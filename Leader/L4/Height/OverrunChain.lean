import Leader.L4.Height.LevelRec
import Leader.L4.Height.ClockMeanAlt
import Leader.L4.Height.PhysicalGen
import Leader.L4.Height.RepairTime

namespace L4.Height

open L4.Compiler.Native
open Classical

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

noncomputable section

/-- A clock-driving chain remembers the lifted word state and the owner
published by its most recent transition. -/
abbrev OverrunState (m : Nat) := WordState m × Option (Fin m)

/-- The abstract publication choice made by one scheduler letter. -/
abbrev OverrunAct (n m : Nat) :=
  OverrunState m → Fin n → Option (Fin m × Bool)

/-- The chain transition: a missing publication stutters the clock state,
while a publication performs exactly one SyncAlt activation. -/
def overrunNext {n m B M : Nat} (hm : 0 < m)
    (act : OverrunAct n m) :
    OverrunState m → Fin n → OverrunState m
  | y, e =>
      match act y e with
      | none => (y.1, none)
      | some p => (activate B M hm y.1 p.1 p.2, some p.1)

/-- The service predicate is the last-publication marker. -/
def overrunServed {m : Nat} (i : Fin m) (y : OverrunState m) : Prop :=
  y.2 = some i

/-- State after the first t scheduler letters. -/
def overrunStateAt {n m B M : Nat} (hm : 0 < m)
    (act : OverrunAct n m) (x : OverrunState m)
    (u : Thru.Word n) (t : Nat) : OverrunState m :=
  Thru.runWord (overrunNext (B := B) (M := M) hm act) x (u.take t)

/-- Least true Boolean at or below a finite bound. If no entry is true,
the bound itself is returned. -/
def overrunLeastTrue (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      let j := overrunLeastTrue p k
      if p j = true then j else k + 1

theorem overrunLeastTrue_le (p : Nat → Bool) :
    ∀ k, overrunLeastTrue p k ≤ k := by
  intro k
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      simp only [overrunLeastTrue]
      split
      · exact Nat.le_trans ih (Nat.le_succ k)
      · exact Nat.le_refl _

/-- Finite hitting time, capped at the word length. Levels are measured
relative to the common initial floor `base`; the caller supplies
`base ≤ x.1.lift i` for every site. -/
def finiteLevelTime {n m B M : Nat} (hm : 0 < m)
    (act : OverrunAct n m) (x : OverrunState m)
    (base : Nat) (u : Thru.Word n) (i : Fin m) (ell : Nat) : Nat :=
  if ell = 0 then 0 else
    overrunLeastTrue
      (fun k => decide
        (base + ell ≤ (overrunStateAt (B := B) (M := M) hm act x u k).1.lift i))
      u.length

theorem finiteLevelTime_le_length {n m B M : Nat} (hm : 0 < m)
    (act : OverrunAct n m) (x : OverrunState m)
    (base : Nat) (u : Thru.Word n) (i : Fin m) (ell : Nat) :
    finiteLevelTime (B := B) (M := M) hm act x base u i ell ≤ u.length := by
  unfold finiteLevelTime
  by_cases h : ell = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    exact overrunLeastTrue_le _ _

/-- The level-zero floor is reached at the empty prefix. -/
theorem finiteLevelTime_floor {n m B M : Nat} (hm : 0 < m)
    (act : OverrunAct n m) (x : OverrunState m)
    (base : Nat) (u : Thru.Word n) (i : Fin m) :
    finiteLevelTime (B := B) (M := M) hm act x base u i 0 = 0 := by
  simp [finiteLevelTime]

/-- Append law for the scheduler executor. -/
private theorem overrun_runWord_append
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (x : α)
    (u v : Thru.Word n) :
    Thru.runWord next x (u ++ v) =
      Thru.runWord next (Thru.runWord next x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (next x e)

/-- Prefix/suffix decomposition, proved locally because the corresponding
ClockMeanAlt helper is private to that module. -/
private theorem overrun_take_add
    {α : Type} (u : List α) (a b : Nat) :
    u.take (a + b) = u.take a ++ (u.drop a).take b := by
  induction a generalizing u with
  | zero => simp
  | succ a ih =>
      cases u with
      | nil => simp
      | cons e u =>
          simp only [Nat.succ_add, List.take_succ_cons,
            List.drop_succ_cons, List.cons_append]
          exact congrArg (List.cons e) (ih u)

/-- A wait shorter than the remaining word certifies a hit at its stopping
prefix. -/
private theorem overrun_wait_hit
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop) :
    ∀ x (u : Thru.Word n),
      Thru.wait next A x u < u.length →
      A (Thru.runWord next x
        (u.take (Thru.wait next A x u))) := by
  intro x u
  induction u generalizing x with
  | nil =>
      intro h
      simp [Thru.wait] at h
  | cons e u ih =>
      intro h
      by_cases hx : A x
      · have hw := Thru.wait_of_hit next A x hx (e :: u)
        simpa [hw, Thru.runWord] using hx
      · rw [Thru.wait_cons_of_not next A x hx e u] at h ⊢
        have ht : Thru.wait next A (next x e) u < u.length := by
          simp only [List.length_cons] at h
          omega
        have htail := ih (next x e) ht
        simpa [Thru.runWord] using htail

/-- Strict service strictly inside the word has a published owner at that prefix. -/
private theorem overrun_service_hit {α : Type} {n m : Nat}
    (next : α → Fin n → α) (x : α) (served : Fin m → α → Prop)
    (u : Thru.Word n) (i : Fin m) (t : Nat)
    (h : serviceTime next x served u i t < u.length) :
    served i (Thru.runWord next x (u.take (serviceTime next x served u i t))) := by
  rw [serviceTime_eq_requested] at h ⊢
  let a := t + 1
  let y := Thru.runWord next x (u.take a)
  let v := u.drop a
  have hw : Thru.wait next (served i) y v < v.length := by
    change a + Thru.wait next (served i) y v < u.length at h
    change Thru.wait next (served i) y v < (u.drop a).length
    rw [List.length_drop]
    omega
  change served i (Thru.runWord next x (u.take (a + Thru.wait next (served i) y v)))
  rw [overrun_take_add, overrun_runWord_append]
  exact overrun_wait_hit next (served i) y v hw

/-- With no service strictly after the request, the word length is a lower
bound for the absolute service time, including on an exhausted suffix. -/
theorem serviceTime_ge_length_of_no_service {α : Type} {n m : Nat}
    (next : α → Fin n → α) (x : α) (served : Fin m → α → Prop)
    (u : Thru.Word n) (i : Fin m) (t : Nat)
    (hno : ∀ k, t < k → k ≤ u.length →
      ¬ served i (Thru.runWord next x (u.take k))) :
    u.length ≤ serviceTime next x served u i t := by
  apply Nat.le_of_not_lt
  intro h
  exact hno _ (serviceTime_after next x served u i t) (Nat.le_of_lt h)
    (overrun_service_hit next x served u i t h)

/-- The cap can signal a miss. Every strictly earlier result is a hit. -/
private theorem overrun_search_hit (p : Nat → Bool) (k : Nat)
    (h : overrunLeastTrue p k < k) : p (overrunLeastTrue p k) = true := by
  cases k with
  | zero => omega
  | succ k =>
    simp only [overrunLeastTrue] at h ⊢
    split at h <;> rename_i hp
    · simp [hp]
    · omega

/-- If the prefix at j hits, the search stops by j and returns a hit. -/
private theorem overrun_search_min (p : Nat → Bool) (k j : Nat)
    (hj : j ≤ k) (hp : p j = true) :
    overrunLeastTrue p k ≤ j ∧ p (overrunLeastTrue p k) = true := by
  induction k with
  | zero =>
    have hz : j = 0 := by omega
    subst j
    exact ⟨Nat.le_refl _, hp⟩
  | succ k ih =>
    simp only [overrunLeastTrue]
    by_cases hjk : j ≤ k
    · obtain ⟨hle, hhit⟩ := ih hjk
      simp [hhit, hle]
    · have he : j = k + 1 := by omega
      split
      next h => exact ⟨by have := overrunLeastTrue_le p k; omega, h⟩
      next _ => exact ⟨by omega, he ▸ hp⟩

private theorem overrun_activate_mono {m B M : Nat} (hm : 0 < m)
    (s : WordState m) (i : Fin m) (b : Bool) (j : Fin m) :
    s.lift j ≤ (activate B M hm s i b).lift j := by
  by_cases he : j = i
  · subst j
    cases h : clockAction M hm s i <;> simp [activate, h, advanceLift]
  · simp [activate, he]

section Prefix

variable {n m B M : Nat} (hm : 0 < m) (act : OverrunAct n m)
    (x : OverrunState m) (u : Thru.Word n)

local notation "state" => overrunStateAt (B := B) (M := M) hm act x u
local notation "step" => overrunNext (B := B) (M := M) hm act

private theorem overrun_prefix_step (q : Nat) (hq : q < u.length) :
    state (q + 1) = step (state q) u[q] := by
  unfold overrunStateAt
  rw [List.take_succ_eq_append_getElem hq, overrun_runWord_append]
  rfl

private theorem overrun_prefix_legit (hM : ClockParams M) (hx : Legit M hm x.1)
    (q : Nat) (hq : q ≤ u.length) : Legit M hm (state q).1 := by
  induction q with
  | zero => exact hx
  | succ q ih =>
    have h := ih (by omega)
    rw [overrun_prefix_step hm act x u q (by omega)]
    have hlt : q < u.length := by omega
    cases hc : act (state q) u[q] with
    | none => simpa only [overrunNext, hc] using h
    | some p =>
      simpa only [overrunNext, hc] using
        (legit_activate (B := B) hM hm (state q).1 h p.1 p.2)

private theorem overrun_prefix_mono (j : Fin m) (a q : Nat)
    (ha : a ≤ q) (hq : q ≤ u.length) : (state a).1.lift j ≤ (state q).1.lift j := by
  induction q with
  | zero =>
    have he : a = 0 := by omega
    subst a
    exact Nat.le_refl _
  | succ q ih =>
    by_cases he : a = q + 1
    · subst a
      exact Nat.le_refl _
    · apply Nat.le_trans (ih (by omega) (by omega))
      rw [overrun_prefix_step hm act x u q (by omega)]
      have hlt : q < u.length := by omega
      cases hc : act (state q) u[q] with
      | none => simp only [overrunNext, hc, Nat.le_refl]
      | some p =>
        simpa only [overrunNext, hc] using
          (overrun_activate_mono (B := B) (M := M) hm (state q).1 p.1 p.2 j)

/-- A publication can be read back as the activation of its marked site,
even when other scheduler letters stutter. -/
private theorem overrun_published_step (q : Nat) (hq : q < u.length) (i : Fin m)
    (hs : overrunServed i (state (q + 1))) :
    ∃ b, (state (q + 1)).1 = activate B M hm (state q).1 i b := by
  rw [overrun_prefix_step hm act x u q hq] at hs ⊢
  cases hc : act (state q) u[q] with
  | none => simp [overrunServed, overrunNext, hc] at hs
  | some p =>
    have he : p.1 = i := by simpa [overrunServed, overrunNext, hc] using hs
    subst i
    exact ⟨p.2, by simp [overrunNext, hc]⟩

end Prefix

private theorem overrun_raise {m B M : Nat} (hm : 0 < m) (hM : ClockParams M)
    (s : WordState m) (hs : Legit M hm s) (i : Fin m) (b : Bool) (d : Nat)
    (hl : d ≤ s.lift (left hm i)) (hc : d ≤ s.lift i) (hr : d ≤ s.lift (right hm i)) :
    d + 1 ≤ (activate B M hm s i b).lift i := by
  by_cases hd : d + 1 ≤ s.lift i
  · exact Nat.le_trans hd (overrun_activate_mono hm s i b i)
  · have hnearL := hs.2.2 (i := i) (j := left hm i) (Or.inl rfl)
    have hnearR := hs.2.2 (i := i) (j := right hm i) (Or.inr rfl)
    unfold Near at hnearL hnearR
    have hfront : CanAdvance hm s.lift i := ⟨by omega, by omega⟩
    have ha := (action_inc_iff hM hm s hs i).2 hfront
    simp [activate, ha, advanceLift, hc]

section FiniteClock

variable {n m B M : Nat} (hm : 0 < m) (act : OverrunAct n m)
    (x : OverrunState m) (base : Nat)

local notation "T" => finiteLevelTime (B := B) (M := M) hm act x base
local notation "prefixAt" => overrunStateAt (B := B) (M := M) hm act x
local notation "next" => overrunNext (B := B) (M := M) hm act

private theorem overrun_level_at (hb : ∀ j, base ≤ x.1.lift j)
    (u : Thru.Word n) (j : Fin m) (ell q : Nat)
    (ht : T u j ell ≤ q) (hq : q < u.length) :
    base + ell ≤ (prefixAt u q).1.lift j := by
  by_cases hz : ell = 0
  · subst ell
    exact Nat.le_trans (hb j)
      (overrun_prefix_mono hm act x u j 0 q (Nat.zero_le _) (Nat.le_of_lt hq))
  · let p := fun k => decide (base + ell ≤ (prefixAt u k).1.lift j)
    have he : T u j ell = overrunLeastTrue p u.length := by simp [finiteLevelTime, hz, p]
    rw [he] at ht
    have hh := of_decide_eq_true (overrun_search_hit p u.length (Nat.lt_of_le_of_lt ht hq))
    exact Nat.le_trans hh (overrun_prefix_mono hm act x u j _ q ht (Nat.le_of_lt hq))

/-- The finite clock on every scheduler word satisfies the three-neighbour recursion. -/
theorem level_rec_finite (hM : ClockParams M) (hx : Legit M hm x.1)
    (hb : ∀ j, base ≤ x.1.lift j) (u : Thru.Word n) (i : Fin m) (ell : Nat) :
    T u i (ell + 1) ≤ serviceTime next x overrunServed u i
      (max (max (T u (left hm i) ell) (T u i ell)) (T u (right hm i) ell)) := by
  let t := max (max (T u (left hm i) ell) (T u i ell)) (T u (right hm i) ell)
  let k := serviceTime next x overrunServed u i t
  change T u i (ell + 1) ≤ k
  by_cases hk : k < u.length
  · have hafter : t < k := serviceTime_after next x overrunServed u i t
    obtain ⟨q, he⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
    have hq : q < u.length := by omega
    have hs : overrunServed i (prefixAt u (q + 1)) := by
      rw [← he]
      exact overrun_service_hit next x overrunServed u i t hk
    obtain ⟨b, hstep⟩ := overrun_published_step hm act x u q hq i hs
    have hleg := overrun_prefix_legit (B := B) hm act x u hM hx q (Nat.le_of_lt hq)
    have hlocal := overrun_level_at (B := B) (M := M) hm act x base hb u
    have hh : base + ell + 1 ≤ (prefixAt u (q + 1)).1.lift i := by
      rw [hstep]
      exact overrun_raise hm hM _ hleg i b (base + ell)
        (hlocal (left hm i) ell q (by dsimp [t] at hafter; omega) hq)
        (hlocal i ell q (by dsimp [t] at hafter; omega) hq)
        (hlocal (right hm i) ell q (by dsimp [t] at hafter; omega) hq)
    rw [he]
    simp only [finiteLevelTime, Nat.succ_ne_zero, ↓reduceIte]
    apply (overrun_search_min _ u.length (q + 1) (by omega) _).1
    exact decide_eq_true (by simpa only [Nat.add_assoc] using hh)
  · exact Nat.le_trans (finiteLevelTime_le_length hm act x base u i (ell + 1)) (by omega)

/-- The concrete finite clock has the depth mean bound for every word length. -/
theorem clock_depth_mean {L : Nat} (hM : ClockParams M) (hx : Legit M hm x.1)
    (hb : ∀ j, base ≤ x.1.lift j) (hL : 1 ≤ L)
    (hMoment : ∀ i y, Thru.MomentAt next (overrunServed i) L y) (h t : Nat) :
    Thru.wordSum (fun u => min (clockMaximum T h u) t) t ≤
      L * (Nat.log2 (m * 3 ^ h) + Nat.log2 (16 ^ h) + 4) * n ^ t :=
  clock_mean hm next x overrunServed L hL hMoment T
    (level_rec_finite hm act x base hM hx hb)
    (fun u j => Nat.le_of_eq (finiteLevelTime_floor hm act x base u j)) h t

/-- The probability of overrunning the physical horizon is at most one quarter. -/
theorem overrun_chain {L h : Nat} (hM : ClockParams M) (hx : Legit M hm x.1)
    (hb : ∀ j, base ≤ x.1.lift j) (hL : 1 ≤ L)
    (hMoment : ∀ i y, Thru.MomentAt next (overrunServed i) L y)
    (hh : h ≤ 2 ^ 25 * m) :
    4 * Thru.wordSum (fun u => if 2 ^ 30 * L * m ≤ clockMaximum T h u then 1 else 0)
      (2 ^ 30 * L * m) ≤ n ^ (2 ^ 30 * L * m) := by
  rw [← repair_wordSum_eq_thru]
  apply overrun_quarter_gen L m h (fun u => clockMaximum T h u) hL hm hh
  intro t
  rw [repair_wordSum_eq_thru]
  exact clock_depth_mean hm act x base hM hx hb hL hMoment h t

end FiniteClock

#print axioms level_rec_finite
#print axioms clock_depth_mean
#print axioms overrun_chain

end
end L4.Height
