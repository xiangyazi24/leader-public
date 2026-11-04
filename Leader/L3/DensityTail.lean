import Leader.L3.ProbRenewal

namespace L3.Density

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree
open LeaderCountDyadicTail
open K2ArbitraryElimination.FiniteAccounting

/-!
Independent coalescing particles on a directed ring.

All bounds use literal
finite scheduler-word counts.
The half-line tail uses stopped linear and quadratic potentials.
The process and its statements do not mention protocol states.
-/

/-! Occupancies and the common graphical map. -/

abbrev Occupancy (n : Nat) := Fin n → Bool

def successor {n : Nat} (e : Fin n) : Fin n :=
  ⟨(e.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt e.isLt)⟩

def full {n : Nat} : Occupancy n := fun _ => true

/-- Destination first also gives the correct identity step when n = 1. -/
def step {n : Nat} (o : Occupancy n) (e : Fin n) : Occupancy n :=
  fun v => if v = successor e then o v || o e
    else if v = e then false else o v

def after {n : Nat} : Occupancy n → List (Fin n) → Occupancy n
  | o, [] => o
  | o, e :: w => after (step o e) w

def bit (b : Bool) : Nat := if b then 1 else 0

def N {n : Nat} (o : Occupancy n) : Nat :=
  (List.ofFn (fun v : Fin n => bit (o v))).sum

def Included {n : Nat} (o p : Occupancy n) : Prop :=
  ∀ v, o v = true → p v = true

theorem step_empty {n : Nat} (o : Occupancy n) (e : Fin n)
    (he : o e = false) : step o e = o := by
  funext v
  by_cases hd : v = successor e
  · simp [step, hd, he]
  · by_cases hv : v = e
    · subst v
      simp [step, hd, he]
    · simp [step, hd, hv]

theorem step_mono {n : Nat} {o p : Occupancy n}
    (h : Included o p) (e : Fin n) : Included (step o e) (step p e) := by
  intro v hv
  by_cases hd : v = successor e
  · have hh : o v = true ∨ o e = true := by
      simpa [step, hd] using hv
    rcases hh with hh | hh
    · have hp : p v = true := h v hh
      subst hd
      simp [step, hp]
    · have hp : p e = true := h e hh
      simpa [step, hd, hp]
  · by_cases he : v = e
    · have hneq : e ≠ successor e := by
        intro hs
        exact hd (he.trans hs)
      have hf : step o e v = false := by
        rw [he]
        simp [step, hneq]
      rw [hf] at hv
      cases hv
    · have hh : o v = true := by simpa [step, hd, he] using hv
      simpa [step, hd, he] using h v hh

theorem after_mono {n : Nat} {o p : Occupancy n}
    (h : Included o p) (w : List (Fin n)) :
    Included (after o w) (after p w) := by
  induction w generalizing o p with
  | nil => exact h
  | cons e w ih => exact ih (step_mono h e)

theorem N_mono {n : Nat} {o p : Occupancy n}
    (h : Included o p) : N o ≤ N p := by
  apply ofFn_sum_le
  intro v
  cases ho : o v with
  | false => simp [bit, ho]
  | true => simp [bit, ho, h v ho]

theorem N_full (n : Nat) : N (full : Occupancy n) = n := by
  simp [N, full, bit, ofFn_sum_const]

theorem N_le {n : Nat} (o : Occupancy n) : N o ≤ n := by
  have h : Included o (full : Occupancy n) := by intro v hv; rfl
  simpa only [N_full] using N_mono h

theorem after_le_full {n : Nat} (o : Occupancy n) (w : List (Fin n)) :
    N (after o w) ≤ N (after (full : Occupancy n) w) := by
  apply N_mono
  apply after_mono
  intro v hv
  rfl

private theorem spike_sum (n : Nat) :
    ∀ (a : Fin n) (v : Nat),
      (List.ofFn (fun e : Fin n => if e = a then v else 0)).sum = v := by
  induction n with
  | zero => intro a; exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n => if i.succ = (0 : Fin (n + 1)) then v else 0)
            (fun _ : Fin n => 0)
            (by
              intro i
              have hn : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hn])
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = a.succ then v else 0)
          (fun i : Fin n => if i = a then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v

private theorem bit_or_le (a b : Bool) : bit (a || b) ≤ bit a + bit b := by
  cases a <;> cases b <;> decide

theorem N_step_le {n : Nat} (o : Occupancy n) (e : Fin n) :
    N (step o e) ≤ N o := by
  have hp (v : Fin n) :
      bit (step o e v) + (if v = e then bit (o e) else 0) ≤
        bit (o v) + (if v = successor e then bit (o e) else 0) := by
    by_cases hd : v = successor e
    · subst v
      simp only [step, if_pos rfl]
      by_cases he : successor e = e
      · rw [he]
        cases o e <;> simp [bit]
      · simp only [if_neg he, Nat.add_zero]
        exact bit_or_le (o (successor e)) (o e)
    · by_cases he : v = e
      · subst v
        simp [step, hd, bit]
      · simp [step, hd, he]
  have hs := ofFn_sum_le
    (fun v : Fin n => bit (step o e v) + (if v = e then bit (o e) else 0))
    (fun v : Fin n => bit (o v) + (if v = successor e then bit (o e) else 0)) hp
  rw [ofFn_sum_add, ofFn_sum_add, spike_sum, spike_sum] at hs
  change N (step o e) + bit (o e) ≤ N o + bit (o e) at hs
  omega

theorem N_after_le {n : Nat} (o : Occupancy n) (w : List (Fin n)) :
    N (after o w) ≤ N o := by
  induction w generalizing o with
  | nil => exact Nat.le_refl _
  | cons e w ih => exact Nat.le_trans (ih (step o e)) (N_step_le o e)

theorem after_append {n : Nat} (o : Occupancy n)
    (u v : List (Fin n)) : after o (u ++ v) = after (after o u) v := by
  induction u generalizing o with
  | nil => rfl
  | cons e u ih => exact ih (step o e)

def lineageStep {n : Nat} (p e : Fin n) : Fin n :=
  if p = e then successor e else p

def lineageAfter {n : Nat} : Fin n → List (Fin n) → Fin n
  | p, [] => p
  | p, e :: w => lineageAfter (lineageStep p e) w

def cover {n : Nat} : List (Fin n) → Occupancy n
  | [] => fun _ => false
  | p :: ps => fun v => if v = p then true else cover ps v

private theorem bool_eq_of_true_iff {a b : Bool}
    (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem cover_true_iff {n : Nat} (ps : List (Fin n)) (v : Fin n) :
    cover ps v = true ↔ v ∈ ps := by
  induction ps with
  | nil => simp [cover]
  | cons p ps ih =>
      by_cases hp : v = p
      · simp [cover, hp]
      · simp [cover, hp, ih]

theorem step_true_iff {n : Nat} (o : Occupancy n) (e v : Fin n) :
    step o e v = true ↔
      (v = successor e ∧ o e = true) ∨ (v ≠ e ∧ o v = true) := by
  by_cases hd : v = successor e
  · by_cases he : v = e
    · have hse : successor e = e := hd.symm.trans he
      cases hb : o e <;> simp [step, hd, he, hse, hb]
    · have hse : successor e ≠ e := by
        intro hs
        exact he (hd.trans hs)
      subst hd
      cases hv : o (successor e) <;> cases hb : o e <;>
        simp [step, hse, hv, hb]
  · by_cases he : v = e <;> simp [step, hd, he]

theorem step_cover {n : Nat} (ps : List (Fin n)) (e : Fin n) :
    step (cover ps) e = cover (ps.map (fun p => lineageStep p e)) := by
  funext v
  apply bool_eq_of_true_iff
  simp only [step_true_iff, cover_true_iff, List.mem_map]
  constructor
  · intro h
    rcases h with ⟨hd, he⟩ | ⟨hne, hv⟩
    · exact ⟨e, he, by simp [lineageStep, hd]⟩
    · exact ⟨v, hv, by simp [lineageStep, hne]⟩
  · intro h
    rcases h with ⟨p, hp, hm⟩
    by_cases he : p = e
    · subst p
      have hd : successor e = v := by simpa [lineageStep] using hm
      exact Or.inl ⟨hd.symm, hp⟩
    · have hv : p = v := by simpa [lineageStep, he] using hm
      have hne : v ≠ e := by
        intro hve
        exact he (hv.trans hve)
      have hmem : v ∈ ps := by
        rw [← hv]
        exact hp
      exact Or.inr ⟨hne, hmem⟩

theorem after_cover {n : Nat} (ps : List (Fin n)) (w : List (Fin n)) :
    after (cover ps) w = cover (ps.map (fun p => lineageAfter p w)) := by
  induction w generalizing ps with
  | nil => simp [after, lineageAfter]
  | cons e w ih =>
      rw [after, step_cover, ih]
      simp only [List.map_map, Function.comp_def, lineageAfter]

theorem cover_full (n : Nat) :
    cover (List.ofFn (fun i : Fin n => i)) = (full : Occupancy n) := by
  funext v
  change cover (List.ofFn (fun i : Fin n => i)) v = true
  exact (cover_true_iff _ _).2 (List.mem_ofFn.mpr ⟨v, rfl⟩)

theorem after_full_lineages {n : Nat} (w : List (Fin n)) :
    after (full : Occupancy n) w =
      cover (List.ofFn (fun i : Fin n => lineageAfter i w)) := by
  rw [← cover_full n, after_cover]
  simp only [List.map_ofFn, Function.comp_def]

private theorem N_cover_nil (n : Nat) : N (cover ([] : List (Fin n))) = 0 := by
  simp [N, cover, bit, ofFn_sum_const]

private theorem N_cover_cons_le {n : Nat} (a : Fin n) (xs : List (Fin n)) :
    N (cover (a :: xs)) ≤ N (cover xs) + 1 := by
  have hp (v : Fin n) :
      bit (cover (a :: xs) v) ≤ bit (cover xs v) + (if v = a then 1 else 0) := by
    by_cases h : v = a
    · rw [show cover (a :: xs) v = true by simp [cover, h], if_pos h]
      change 1 ≤ bit (cover xs v) + 1
      omega
    · simp [cover, h]
  have hs := ofFn_sum_le
    (fun v : Fin n => bit (cover (a :: xs) v))
    (fun v : Fin n => bit (cover xs v) + (if v = a then 1 else 0)) hp
  rw [ofFn_sum_add, spike_sum] at hs
  exact hs

private theorem cover_duplicate {n : Nat} (a : Fin n) (xs : List (Fin n)) :
    cover (a :: a :: xs) = cover (a :: xs) := by
  funext v
  by_cases h : v = a <;> simp [cover, h]

def changesFrom {n : Nat} : Fin n → List (Fin n) → Nat
  | _, [] => 0
  | a, b :: xs => (if a = b then 0 else 1) + changesFrom b xs

private theorem N_cover_changes {n : Nat} (a : Fin n) (xs : List (Fin n)) :
    N (cover (a :: xs)) ≤ 1 + changesFrom a xs := by
  induction xs generalizing a with
  | nil =>
      have h := N_cover_cons_le a []
      simpa only [N_cover_nil, changesFrom, Nat.zero_add, Nat.add_zero] using h
  | cons b xs ih =>
      by_cases h : a = b
      · subst a
        rw [cover_duplicate]
        have hc : changesFrom b (b :: xs) = changesFrom b xs := by
          simp [changesFrom]
        rw [hc]
        exact ih b
      · have hs := N_cover_cons_le a (b :: xs)
        have ht := ih b
        have he : changesFrom a (b :: xs) = 1 + changesFrom b xs := by
          simp only [changesFrom, if_neg h]
        rw [he]
        omega

private theorem changesFrom_ofFn {n m : Nat} (f : Fin (m + 1) → Fin n) :
    changesFrom (f 0) (List.ofFn (fun i : Fin m => f i.succ)) =
      (List.ofFn (fun i : Fin m =>
        if f i.castSucc = f i.succ then 0 else 1)).sum := by
  induction m with
  | zero => simp [changesFrom]
  | succ m ih =>
      rw [List.ofFn_succ, changesFrom, List.ofFn_succ, List.sum_cons]
      exact congrArg
        (fun z : Nat => (if f 0 = f (Fin.succ 0) then 0 else 1) + z)
        (ih (fun i : Fin (m + 1) => f i.succ))

private theorem N_cover_ofFn_le {n m : Nat} (f : Fin (m + 1) → Fin n) :
    N (cover (List.ofFn f)) ≤
      1 + (List.ofFn (fun i : Fin m =>
        if f i.castSucc = f i.succ then 0 else 1)).sum := by
  have h := N_cover_changes (f 0) (List.ofFn (fun i : Fin m => f i.succ))
  rw [changesFrom_ofFn f] at h
  simpa only [List.ofFn_succ] using h

private theorem sum_castSucc_le {m : Nat} (f : Fin (m + 1) → Nat) :
    (List.ofFn (fun i : Fin m => f i.castSucc)).sum ≤ (List.ofFn f).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add_left (ih (fun i : Fin (m + 1) => f i.succ)) _

theorem successor_castSucc {m : Nat} (i : Fin m) :
    successor i.castSucc = i.succ := by
  apply Fin.ext
  change (i.val + 1) % (m + 1) = i.val + 1
  exact Nat.mod_eq_of_lt (by omega)

/-- B.12; a support has at most one plus the number of adjacent changes. -/
theorem particles_boundary_le {n : Nat} (w : List (Fin n)) :
    N (after (full : Occupancy n) w) ≤
      1 + (List.ofFn (fun i : Fin n =>
        if lineageAfter i w = lineageAfter (successor i) w then 0 else 1)).sum := by
  cases n with
  | zero => simp [N]
  | succ m =>
      rw [after_full_lineages]
      have hl := N_cover_ofFn_le (fun i : Fin (m + 1) => lineageAfter i w)
      have ht :
          (List.ofFn (fun i : Fin m =>
            if lineageAfter i.castSucc w = lineageAfter i.succ w then 0 else 1)).sum ≤
          (List.ofFn (fun i : Fin (m + 1) =>
            if lineageAfter i w = lineageAfter (successor i) w then 0 else 1)).sum := by
        calc
          _ = (List.ofFn (fun i : Fin m =>
                if lineageAfter i.castSucc w = lineageAfter (successor i.castSucc) w
                then 0 else 1)).sum := by
            apply ofFn_sum_eq
            intro i
            rw [successor_castSucc]
          _ ≤ _ := sum_castSucc_le (fun i : Fin (m + 1) =>
            if lineageAfter i w = lineageAfter (successor i) w then 0 else 1)
      exact Nat.le_trans hl (Nat.add_le_add_left ht 1)


/-! A stopped-potential bound for the canonical lazy walk. -/

/-- Two moving letters followed by k holding letters. -/
def lazyChoice (k d u h : Nat) (e : Fin (k + 2)) : Nat :=
  Fin.cases d (fun i => Fin.cases u (fun _ => h) i) e

theorem sum_lazyChoice (k d u h : Nat) (f : Nat → Nat) :
    (List.ofFn (fun e : Fin (k + 2) =>
      f (lazyChoice k d u h e))).sum =
      f d + f u + k * f h := by
  simp [lazyChoice, List.ofFn_succ, ofFn_sum_const, Nat.add_assoc]

def lazyStep (k x : Nat) (e : Fin (k + 2)) : Nat :=
  if x = 0 then 0 else lazyChoice k (x - 1) (x + 1) x e

noncomputable def lazyTail (k x m : Nat) : Nat :=
  wordSum (lazyStep k) (miss (fun z => z = 0)) x m

theorem lazyTail_horizon_zero (k x : Nat) :
    lazyTail k x 0 = if x = 0 then 0 else 1 := by
  classical
  simp [lazyTail, wordSum_zero, miss]

theorem lazyTail_zero (k m : Nat) :
    lazyTail k 0 m = 0 := by
  unfold lazyTail
  apply miss_zero (lazyStep k) (fun z => z = 0)
  · intro x e hx
    subst x
    simp [lazyStep]
  · rfl

theorem lazyTail_succ (k x m : Nat) (hx : 0 < x) :
    lazyTail k x (m + 1) =
      lazyTail k (x - 1) m +
      lazyTail k (x + 1) m +
      k * lazyTail k x m := by
  have hxne : x ≠ 0 := by omega
  unfold lazyTail
  rw [wordSum_succ]
  simp only [lazyStep, if_neg hxne]
  exact sum_lazyChoice k (x - 1) (x + 1) x
    (fun y => wordSum (lazyStep k) (miss (fun z => z = 0)) y m)

/-- The same walk, frozen upon reaching zero or the upper cutoff. -/
def capStep (a k x : Nat) (e : Fin (k + 2)) : Nat :=
  if x = 0 ∨ a ≤ x then x
  else lazyChoice k (x - 1) (x + 1) x e

private theorem capStep_sum (a k x : Nat) :
    (List.ofFn (fun e : Fin (k + 2) =>
      capStep a k x e)).sum = (k + 2) * x := by
  by_cases hx : x = 0 ∨ a ≤ x
  · simp only [capStep, if_pos hx, ofFn_sum_const]
  · have hpos : 0 < x := by omega
    have hs :
        (List.ofFn (fun e : Fin (k + 2) =>
          capStep a k x e)).sum =
          (x - 1) + (x + 1) + k * x := by
      simp only [capStep, if_neg hx]
      exact sum_lazyChoice k (x - 1) (x + 1) x (fun y => y)
    rw [hs, Nat.add_mul]
    omega

/-- The stopped linear potential is exactly harmonic. -/
theorem cap_linear (a k x m : Nat) :
    wordSum (capStep a k) (fun y => y) x m =
      (k + 2) ^ m * x := by
  induction m generalizing x with
  | zero => simp [wordSum_zero]
  | succ m ih =>
      rw [wordSum_succ,
        ofFn_sum_eq _ _ (fun e => ih (capStep a k x e)),
        ofFn_sum_mul_left, capStep_sum, Nat.pow_succ]
      ac_rfl

private theorem cutoff_quadratic (a x : Nat)
    (hpos : 0 < x) (hlt : x < a) :
    (x - 1) * (a - (x - 1)) +
        (x + 1) * (a - (x + 1)) + 2 =
      2 * (x * (a - x)) := by
  let u := x - 1
  let v := a - (x + 1)
  have hu : x - 1 = u := rfl
  have hx : x = u + 1 := by dsimp [u]; omega
  have hplus : x + 1 = u + 2 := by omega
  have hlo : a - (x - 1) = v + 2 := by dsimp [v]; omega
  have hhi : a - (x + 1) = v := rfl
  have hmid : a - x = v + 1 := by dsimp [v]; omega
  calc
    (x - 1) * (a - (x - 1)) +
          (x + 1) * (a - (x + 1)) + 2 =
        u * (v + 2) + (u + 2) * v + 2 := by
      rw [hlo, hhi, hu, hplus]
    _ = 2 * ((u + 1) * (v + 1)) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    _ = 2 * (x * (a - x)) := by rw [hmid, hx]

/-- Scaling the quadratic by n gives an integer exit-cost reserve.
    One of the two exact drift units is enough for the desired constants. -/
theorem cap_cost (a k x m : Nat) :
    costNumerator (capStep a k) (fun y => y = 0 ∨ a ≤ y) x m ≤
      (k + 2) ^ m * ((k + 2) * (x * (a - x))) := by
  apply L3.Prob.costNumerator_le_of_potential
    (capStep a k) (fun y => y = 0 ∨ a ≤ y)
    (fun y => (k + 2) * (y * (a - y)))
  intro y hy
  have hpos : 0 < y := by omega
  have hlt : y < a := by omega
  have hquad := cutoff_quadratic a y hpos hlt
  have hs :
      (List.ofFn (fun e : Fin (k + 2) =>
        (k + 2) *
          (capStep a k y e * (a - capStep a k y e)))).sum =
        (k + 2) * ((y - 1) * (a - (y - 1))) +
        (k + 2) * ((y + 1) * (a - (y + 1))) +
        k * ((k + 2) * (y * (a - y))) := by
    simp only [capStep, if_neg hy]
    exact sum_lazyChoice k (y - 1) (y + 1) y
      (fun z => (k + 2) * (z * (a - z)))
  have he :
      (List.ofFn (fun e : Fin (k + 2) =>
        (k + 2) *
          (capStep a k y e * (a - capStep a k y e)))).sum +
          2 * (k + 2) =
        (k + 2) * ((k + 2) * (y * (a - y))) := by
    rw [hs]
    calc
      (k + 2) * ((y - 1) * (a - (y - 1))) +
          (k + 2) * ((y + 1) * (a - (y + 1))) +
          k * ((k + 2) * (y * (a - y))) +
          2 * (k + 2) =
        (k + 2) *
          ((y - 1) * (a - (y - 1)) +
            (y + 1) * (a - (y + 1)) + 2) +
          k * ((k + 2) * (y * (a - y))) := by
            simp only [Nat.mul_add, Nat.add_mul]
            ac_rfl
      _ = (k + 2) * (2 * (y * (a - y))) +
          k * ((k + 2) * (y * (a - y))) := by rw [hquad]
      _ = (k + 2) * ((k + 2) * (y * (a - y))) := by
        simp only [Nat.add_mul, Nat.mul_add]
        ac_rfl
  omega

private theorem survival_eq_endpoint {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop)
    (hc : ∀ x e, P x → P (next x e)) :
    ∀ x m, UniformFirstHit.survivalNumerator next P x m =
      wordSum next (miss P) x m := by
  classical
  intro x m
  induction m generalizing x with
  | zero =>
      simp [UniformFirstHit.survivalNumerator,
        FixedSpanRenewalPayload.wordSum, allSchedules,
        UniformFirstHit.survivalWord, wordSum_zero, miss]
  | succ m ih =>
      by_cases hx : P x
      · rw [UniformFirstHit.survivalNumerator_of_target next P x hx,
          miss_zero next P hc x hx]
      · rw [UniformFirstHit.survivalNumerator_succ_of_not next P x hx,
          wordSum_succ]
        exact ofFn_sum_eq _ _ (fun e => ih (next x e))

/-- The upper-exit count is at most the total word count divided by a. -/
theorem cap_high_le (a k m : Nat) :
    a * wordSum (capStep a k)
        (fun y => if a ≤ y then 1 else 0) 1 m ≤
      (k + 2) ^ m := by
  have hp : ∀ y : Nat, a * (if a ≤ y then 1 else 0) ≤ y := by
    intro y
    by_cases hy : a ≤ y
    · simpa only [if_pos hy, Nat.mul_one] using hy
    · simp only [if_neg hy, Nat.mul_zero]
      exact Nat.zero_le _
  have hs := wordSum_mono (capStep a k)
    (fun y => a * (if a ≤ y then 1 else 0)) (fun y => y) hp 1 m
  rw [wordSum_mul, cap_linear] at hs
  simpa only [Nat.mul_one] using hs

theorem cap_interior_le (a k m : Nat) :
    m * wordSum (capStep a k)
        (miss (fun y => y = 0 ∨ a ≤ y)) 1 m ≤
      (k + 2) ^ m * (k + 2) * (a - 1) := by
  have hc : ∀ y e, (y = 0 ∨ a ≤ y) →
      (capStep a k y e = 0 ∨ a ≤ capStep a k y e) := by
    intro y e hy
    simpa only [capStep, if_pos hy] using hy
  have hs := UniformFirstHit.survival_mul_le_cost
    (capStep a k) (fun y => y = 0 ∨ a ≤ y) 1 m
  rw [survival_eq_endpoint (capStep a k)
    (fun y => y = 0 ∨ a ≤ y) hc] at hs
  have ht := Nat.le_trans hs (cap_cost a k 1 m)
  simpa only [Nat.one_mul, Nat.mul_assoc] using ht

private theorem cap_alive_high (a k x m : Nat)
    (ha : 0 < a) (hax : a ≤ x) :
    wordSum (capStep a k) (miss (fun y => y = 0)) x m =
      (k + 2) ^ m := by
  have hx : x ≠ 0 := by omega
  induction m with
  | zero => simp [wordSum_zero, miss, hx]
  | succ m ih =>
      rw [wordSum_succ]
      have hs :
          (List.ofFn (fun e : Fin (k + 2) =>
            wordSum (capStep a k) (miss (fun y => y = 0))
              (capStep a k x e) m)).sum =
            (List.ofFn (fun _ : Fin (k + 2) =>
              (k + 2) ^ m)).sum :=
        ofFn_sum_eq _ _ (fun e => by
          have hsx : capStep a k x e = x := by simp [capStep, hax]
          rw [hsx]
          exact ih)
      rw [hs, ofFn_sum_const, Nat.pow_succ]
      ac_rfl

theorem lazyTail_le_cap (a k x m : Nat) (ha : 0 < a) :
    lazyTail k x m ≤
      wordSum (capStep a k) (miss (fun y => y = 0)) x m := by
  unfold lazyTail
  induction m generalizing x with
  | zero => exact Nat.le_refl _
  | succ m ih =>
      by_cases hax : a ≤ x
      · rw [cap_alive_high a k x (m + 1) ha hax]
        exact miss_mass_le (lazyStep k) (fun y => y = 0) x (m + 1)
      · rw [wordSum_succ, wordSum_succ]
        apply ofFn_sum_le
        intro e
        have he : capStep a k x e = lazyStep k x e := by
          by_cases hx : x = 0 <;>
            simp [capStep, lazyStep, hx, hax]
        rw [he]
        exact ih (lazyStep k x e)

/-- Division-free cutoff estimate, valid for every positive cutoff. -/
theorem lazyTail_cutoff (k a m : Nat) (ha : 0 < a) :
    a * m * lazyTail k 1 m ≤
      (m + (k + 2) * a * (a - 1)) * (k + 2) ^ m := by
  classical
  let H := wordSum (capStep a k)
    (fun y => if a ≤ y then 1 else 0) 1 m
  let I := wordSum (capStep a k)
    (miss (fun y => y = 0 ∨ a ≤ y)) 1 m
  have hh : a * H ≤ (k + 2) ^ m := cap_high_le a k m
  have hi : m * I ≤ (k + 2) ^ m * (k + 2) * (a - 1) :=
    cap_interior_le a k m
  have hfun :
      miss (fun y : Nat => y = 0) =
        (fun y =>
          (if a ≤ y then 1 else 0) +
            miss (fun z => z = 0 ∨ a ≤ z) y) := by
    funext y
    by_cases hy : y = 0
    · subst y
      have hnot : ¬ a ≤ 0 := by omega
      simp [miss, hnot]
    · by_cases hhigh : a ≤ y <;> simp [miss, hy, hhigh]
  have he :
      wordSum (capStep a k) (miss (fun y => y = 0)) 1 m = H + I := by
    rw [hfun, wordSum_add]
  have hf : lazyTail k 1 m ≤ H + I := by
    have hc := lazyTail_le_cap a k 1 m ha
    rw [he] at hc
    exact hc
  calc
    a * m * lazyTail k 1 m ≤ a * m * (H + I) :=
      Nat.mul_le_mul_left (a * m) hf
    _ = m * (a * H) + a * (m * I) := by
      rw [Nat.mul_add]
      congr 1 <;> ac_rfl
    _ ≤ m * (k + 2) ^ m +
        a * ((k + 2) ^ m * (k + 2) * (a - 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul_left m hh) (Nat.mul_le_mul_left a hi)
    _ = (m + (k + 2) * a * (a - 1)) * (k + 2) ^ m := by
      rw [Nat.add_mul]
      congr 1 <;> ac_rfl


/-! Comparison with the actual two-lineage process on the ring. -/

def ringGap {n : Nat} (x y : Fin n) : Nat :=
  if x.val ≤ y.val then y.val - x.val else n + y.val - x.val

theorem ringGap_self {n : Nat} (x : Fin n) :
    ringGap x x = 0 := by
  simp [ringGap]

theorem ringGap_eq_zero {n : Nat} (x y : Fin n) :
    ringGap x y = 0 ↔ x = y := by
  have hx := x.isLt
  have hy := y.isLt
  constructor
  · intro h
    apply Fin.ext
    unfold ringGap at h
    split at h <;> omega
  · intro h
    subst y
    exact ringGap_self x

private theorem ringSuccessor_cases {n : Nat} (x : Fin n) :
    (x.val + 1 < n ∧ (successor x).val = x.val + 1) ∨
      (x.val + 1 = n ∧ (successor x).val = 0) := by
  by_cases h : x.val + 1 < n
  · left
    constructor
    · exact h
    · change (x.val + 1) % n = x.val + 1
      exact Nat.mod_eq_of_lt h
  · right
    have hx := x.isLt
    have he : x.val + 1 = n := by omega
    constructor
    · exact he
    · change (x.val + 1) % n = 0
      rw [he, Nat.mod_self]

theorem ringGap_successor_left {n : Nat}
    (x y : Fin n) (hxy : x ≠ y) :
    ringGap (successor x) y = ringGap x y - 1 := by
  have hx := x.isLt
  have hy := y.isLt
  have hval : x.val ≠ y.val := by
    intro h
    exact hxy (Fin.ext h)
  rcases ringSuccessor_cases x with ⟨hsmall, hs⟩ | ⟨hlast, hs⟩
  · by_cases hle : x.val ≤ y.val
    · have hnew : x.val + 1 ≤ y.val := by omega
      simp only [ringGap, hs, if_pos hnew, if_pos hle]
      omega
    · have hnew : ¬ x.val + 1 ≤ y.val := by omega
      simp only [ringGap, hs, if_neg hnew, if_neg hle]
      omega
  · have hle : ¬ x.val ≤ y.val := by omega
    simp only [ringGap, hs, if_neg hle, Nat.zero_le, if_true]
    omega

theorem ringGap_successor_right {n : Nat} (x y : Fin n) :
    ringGap x (successor y) =
      if ringGap x y + 1 = n then 0 else ringGap x y + 1 := by
  have hx := x.isLt
  have hy := y.isLt
  rcases ringSuccessor_cases y with ⟨hsmall, hs⟩ | ⟨hlast, hs⟩
  · by_cases hle : x.val ≤ y.val
    · have hnew : x.val ≤ y.val + 1 := by omega
      have hmax : ringGap x y + 1 ≠ n := by
        simp only [ringGap, if_pos hle]
        omega
      rw [if_neg hmax]
      simp only [ringGap, hs, if_pos hnew, if_pos hle]
      omega
    · by_cases hnext : x.val = y.val + 1
      · have hnew : x.val ≤ y.val + 1 := by omega
        have hmax : ringGap x y + 1 = n := by
          simp only [ringGap, if_neg hle]
          omega
        rw [if_pos hmax]
        simp only [ringGap, hs, if_pos hnew]
        omega
      · have hnew : ¬ x.val ≤ y.val + 1 := by omega
        have hmax : ringGap x y + 1 ≠ n := by
          simp only [ringGap, if_neg hle]
          omega
        rw [if_neg hmax]
        simp only [ringGap, hs, if_neg hnew, if_neg hle]
        omega
  · have hle : x.val ≤ y.val := by omega
    by_cases hz : x.val = 0
    · have hnew : x.val ≤ 0 := by omega
      have hmax : ringGap x y + 1 = n := by
        simp only [ringGap, if_pos hle]
        omega
      rw [if_pos hmax]
      simp only [ringGap, hs, if_pos hnew]
      omega
    · have hnew : ¬ x.val ≤ 0 := by omega
      have hmax : ringGap x y + 1 ≠ n := by
        simp only [ringGap, if_pos hle]
        omega
      rw [if_neg hmax]
      simp only [ringGap, hs, if_neg hnew, if_pos hle]
      omega

theorem ringGap_adjacent (k : Nat) (i : Fin (k + 2)) :
    ringGap i (successor i) = 1 := by
  have hn : (1 : Nat) ≠ k + 2 := by omega
  simpa [ringGap_self, hn] using ringGap_successor_right i i

def lineagePairStep {n : Nat}
    (p : Fin n × Fin n) (e : Fin n) : Fin n × Fin n :=
  (lineageStep p.1 e, lineageStep p.2 e)

theorem lineagePair_diagonal {n : Nat}
    (p : Fin n × Fin n) (e : Fin n) (h : p.1 = p.2) :
    (lineagePairStep p e).1 = (lineagePairStep p e).2 := by
  change lineageStep p.1 e = lineageStep p.2 e
  rw [h]

private theorem pair_ofFn_nodup {k : Nat} {X : Type}
    (f : Fin k → X) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
        have h := hf hi
        have hv := congrArg Fin.val h
        change i.val + 1 = 0 at hv
        omega
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

private theorem lineagePair_row_le
    (k m : Nat) (x y : Fin (k + 2)) (hxy : x ≠ y) :
    (List.ofFn (fun e : Fin (k + 2) =>
      lazyTail k
        (ringGap (lineageStep x e) (lineageStep y e)) m)).sum
      ≤ lazyTail k (ringGap x y) (m + 1) := by
  have hpos : 0 < ringGap x y := by
    have hz : ringGap x y ≠ 0 := by
      intro h
      exact hxy ((ringGap_eq_zero x y).1 h)
    omega
  have hsum := FiniteUniformStoppingTree.sum_two_exceptions
    (List.ofFn (fun e : Fin (k + 2) => e))
    x y
    (fun e => lazyTail k
      (ringGap (lineageStep x e) (lineageStep y e)) m)
    (lazyTail k (ringGap x y) m)
    (pair_ofFn_nodup _ (by intro a b h; exact h))
    (List.mem_ofFn.mpr ⟨x, rfl⟩)
    (List.mem_ofFn.mpr ⟨y, rfl⟩)
    hxy
    (by
      intro e he hex hey
      simp [lineageStep, Ne.symm hex, Ne.symm hey])
  have he :
      (List.ofFn (fun e : Fin (k + 2) =>
        lazyTail k
          (ringGap (lineageStep x e) (lineageStep y e)) m)).sum =
        lazyTail k (ringGap x y - 1) m +
          lazyTail k (ringGap x (successor y)) m +
          k * lazyTail k (ringGap x y) m := by
    calc
      (List.ofFn (fun e : Fin (k + 2) =>
          lazyTail k
            (ringGap (lineageStep x e) (lineageStep y e)) m)).sum =
          ((List.ofFn (fun e : Fin (k + 2) => e)).map
            (fun e => lazyTail k
              (ringGap (lineageStep x e) (lineageStep y e)) m)).sum := by
        simp only [List.map_ofFn, Function.comp_def]
      _ = _ := by
        rw [hsum]
        have hlen :
            (List.ofFn (fun e : Fin (k + 2) => e)).length - 2 = k := by
          simp
        have hx : lineageStep x x = successor x := by
          simp [lineageStep]
        have hy : lineageStep y x = y := by
          simp [lineageStep, Ne.symm hxy]
        have hz : lineageStep x y = x := by
          simp [lineageStep, hxy]
        have hw : lineageStep y y = successor y := by
          simp [lineageStep]
        rw [hlen, hx, hy, hz, hw, ringGap_successor_left x y hxy]
  have hup :
      lazyTail k (ringGap x (successor y)) m ≤
        lazyTail k (ringGap x y + 1) m := by
    rw [ringGap_successor_right]
    split
    · rw [lazyTail_zero]
      exact Nat.zero_le _
    · exact Nat.le_refl _
  rw [he, lazyTail_succ k (ringGap x y) m hpos]
  exact Nat.add_le_add_right (Nat.add_le_add_left hup _) _

/-- Comparison is on the original finite scheduler tree. -/
theorem lineagePairTail_le
    (k m : Nat) (x y : Fin (k + 2)) :
    wordSum lineagePairStep
      (miss (fun p : Fin (k + 2) × Fin (k + 2) => p.1 = p.2))
      (x, y) m ≤ lazyTail k (ringGap x y) m := by
  classical
  induction m generalizing x y with
  | zero =>
      simp [wordSum_zero, miss, lazyTail_horizon_zero, ringGap_eq_zero]
      by_cases hxy : x = y <;> simp [hxy]
  | succ m ih =>
      by_cases hxy : x = y
      · subst y
        rw [miss_zero lineagePairStep
          (fun p : Fin (k + 2) × Fin (k + 2) => p.1 = p.2)
          lineagePair_diagonal (x, x) rfl (m + 1)]
        exact Nat.zero_le _
      · rw [wordSum_succ]
        calc
          _ ≤ (List.ofFn (fun e : Fin (k + 2) =>
              lazyTail k
                (ringGap (lineageStep x e) (lineageStep y e)) m)).sum :=
            ofFn_sum_le _ _
              (fun e => ih (lineageStep x e) (lineageStep y e))
          _ ≤ _ := lineagePair_row_le k m x y hxy

theorem adjacentLineageTail_le
    (k m : Nat) (i : Fin (k + 2)) :
    wordSum lineagePairStep
      (miss (fun p : Fin (k + 2) × Fin (k + 2) => p.1 = p.2))
      (i, successor i) m ≤ lazyTail k 1 m := by
  simpa only [ringGap_adjacent] using
    lineagePairTail_le k m i (successor i)


/-! Exact scheduler-word sums and the first moment. -/

theorem schedule_sum_const {n : Nat} (T c : Nat) :
    L3.Prob.scheduleSum n T (fun _ => c) = n ^ T * c := by
  change FixedSpanRenewalPayload.wordSum n T (fun _ => c) = _
  rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun _ => c)]
  exact ofFn_sum_const (n ^ T) c

theorem schedule_sum_add {n : Nat} (T : Nat)
    (f g : List (Fin n) → Nat) :
    L3.Prob.scheduleSum n T (fun w => f w + g w) =
      L3.Prob.scheduleSum n T f + L3.Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T (fun w => f w + g w) =
    FixedSpanRenewalPayload.wordSum n T f + FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun w => f w + g w),
    ← FixedSpanRenewalPayload.rawWord_sum n T f,
    ← FixedSpanRenewalPayload.rawWord_sum n T g]
  exact ofFn_sum_add _ _

theorem schedule_sum_mono {n : Nat} (T : Nat)
    (f g : List (Fin n) → Nat) (h : ∀ w, f w ≤ g w) :
    L3.Prob.scheduleSum n T f ≤ L3.Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T f ≤ FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T f,
    ← FixedSpanRenewalPayload.rawWord_sum n T g]
  exact ofFn_sum_le _ _ (fun i => h _)

theorem schedule_sum_fin {n k : Nat} (T : Nat)
    (f : Fin k → List (Fin n) → Nat) :
    L3.Prob.scheduleSum n T (fun w => (List.ofFn (fun i : Fin k => f i w)).sum) =
      (List.ofFn (fun i : Fin k => L3.Prob.scheduleSum n T (f i))).sum := by
  induction k with
  | zero =>
      change L3.Prob.scheduleSum n T (fun _ => 0) = 0
      rw [schedule_sum_const, Nat.mul_zero]
  | succ k ih =>
      have he :
          (fun w : List (Fin n) => (List.ofFn (fun i : Fin (k + 1) => f i w)).sum) =
          (fun w : List (Fin n) =>
            f 0 w + (List.ofFn (fun i : Fin k => f i.succ w)).sum) := by
        funext w
        rw [List.ofFn_succ, List.sum_cons]
      rw [he, schedule_sum_add, List.ofFn_succ, List.sum_cons]
      exact congrArg (fun z : Nat => L3.Prob.scheduleSum n T (f 0) + z)
        (ih (fun i : Fin k => f i.succ))

theorem scheduleSum_after {n : Nat} (f : Occupancy n → Nat)
    (o : Occupancy n) (T : Nat) :
    L3.Prob.scheduleSum n T (fun w => f (after o w)) =
      wordSum step f o T := by
  induction T generalizing o with
  | zero =>
      change FixedSpanRenewalPayload.wordSum n 0 _ = _
      simp [FixedSpanRenewalPayload.wordSum, allSchedules, after]
  | succ T ih =>
      change FixedSpanRenewalPayload.wordSum n (T + 1) _ = _
      rw [FixedSpanRenewalPayload.wordSum_succ, wordSum_succ]
      exact ofFn_sum_eq _ _ (fun e => ih (step o e))

theorem scheduleSum_lineagePair {n : Nat} (a b : Fin n) (T : Nat) :
    L3.Prob.scheduleSum n T (fun w =>
      if lineageAfter a w = lineageAfter b w then 0 else 1) =
      wordSum lineagePairStep
        (miss (fun p : Fin n × Fin n => p.1 = p.2)) (a, b) T := by
  classical
  induction T generalizing a b with
  | zero =>
      by_cases h : a = b <;>
        simp [L3.Prob.scheduleSum, FixedSpanRenewalPayload.wordSum,
          allSchedules, lineageAfter, miss, h]
  | succ T ih =>
      change FixedSpanRenewalPayload.wordSum n (T + 1) _ = _
      rw [FixedSpanRenewalPayload.wordSum_succ, wordSum_succ]
      apply ofFn_sum_eq
      intro e
      change L3.Prob.scheduleSum n T
          (fun w => if lineageAfter (lineageStep a e) w =
            lineageAfter (lineageStep b e) w then 0 else 1) =
        wordSum lineagePairStep
          (miss (fun p : Fin n × Fin n => p.1 = p.2))
          (lineageStep a e, lineageStep b e) T
      exact ih (lineageStep a e) (lineageStep b e)

theorem particles_full_first_moment_le {n : Nat} (T : Nat) :
    wordSum step N (full : Occupancy n) T ≤
      n ^ T + (List.ofFn (fun i : Fin n =>
        wordSum lineagePairStep
          (miss (fun p : Fin n × Fin n => p.1 = p.2))
          (i, successor i) T)).sum := by
  calc
    wordSum step N (full : Occupancy n) T =
        L3.Prob.scheduleSum n T (fun w => N (after (full : Occupancy n) w)) :=
      (scheduleSum_after N full T).symm
    _ ≤ L3.Prob.scheduleSum n T (fun w =>
        1 + (List.ofFn (fun i : Fin n =>
          if lineageAfter i w = lineageAfter (successor i) w then 0 else 1)).sum) :=
      schedule_sum_mono T _ _ particles_boundary_le
    _ = _ := by
      rw [schedule_sum_add, schedule_sum_const, schedule_sum_fin]
      simp only [Nat.mul_one]
      apply congrArg (fun z : Nat => n ^ T + z)
      apply ofFn_sum_eq
      intro i
      exact scheduleSum_lineagePair i (successor i) T

theorem particles_first_moment_le {n : Nat} (o : Occupancy n) (T : Nat) :
    wordSum step N o T ≤
      n ^ T + (List.ofFn (fun i : Fin n =>
        wordSum lineagePairStep
          (miss (fun p : Fin n × Fin n => p.1 = p.2))
          (i, successor i) T)).sum := by
  calc
    wordSum step N o T =
        L3.Prob.scheduleSum n T (fun w => N (after o w)) :=
      (scheduleSum_after N o T).symm
    _ ≤ L3.Prob.scheduleSum n T (fun w => N (after (full : Occupancy n) w)) :=
      schedule_sum_mono T _ _ (after_le_full o)
    _ = wordSum step N (full : Occupancy n) T := scheduleSum_after N full T
    _ ≤ _ := particles_full_first_moment_le T


/-! Integer estimates: no square roots or division of expectations. -/

private theorem square_le_square {a b : Nat} (h : a ≤ b) :
    a * a ≤ b * b :=
  Nat.mul_le_mul h h

private theorem le_of_square_le {a b : Nat} (h : a * a ≤ b * b) :
    a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · have hba : b + 1 ≤ a := by omega
    have hs := Nat.mul_le_mul hba hba
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hs
    omega

/-- Optimize the cutoff by a quotient of exact word counts. -/
theorem square_tail_of_cutoffs (n m C F : Nat)
    (hcut : ∀ a, 0 < a →
      a * m * F ≤ (m + n * a * (a - 1)) * C) :
    m * (F * F) ≤ 4 * n * (C * C) := by
  by_cases hz : F = 0
  · simp [hz]
  · have hF : 0 < F := by omega
    let a := (2 * C) / F + 1
    have ha : 0 < a := Nat.zero_lt_succ _
    have hdiv : ((2 * C) / F) * F + (2 * C) % F = 2 * C := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod (2 * C) F
    have hmod := Nat.mod_lt (2 * C) hF
    have hlo : 2 * C ≤ a * F := by
      dsimp [a]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hhi : (a - 1) * F ≤ 2 * C := by
      have he : a - 1 = (2 * C) / F := by simp [a]
      rw [he]
      omega
    have hc : a * (m * F) ≤ m * C + a * (n * (a - 1) * C) := by
      calc
        a * (m * F) = a * m * F := by ac_rfl
        _ ≤ (m + n * a * (a - 1)) * C := hcut a ha
        _ = m * C + a * (n * (a - 1) * C) := by
          rw [Nat.add_mul]
          congr 1 <;> ac_rfl
    have hd : 2 * (m * C) ≤ a * (m * F) := by
      calc
        2 * (m * C) = m * (2 * C) := by ac_rfl
        _ ≤ m * (a * F) := Nat.mul_le_mul_left m hlo
        _ = a * (m * F) := by ac_rfl
    have he : a * (m * F) ≤ a * (2 * n * (a - 1) * C) := by
      have hrearr :
          a * (2 * n * (a - 1) * C) =
            2 * (a * (n * (a - 1) * C)) := by ac_rfl
      rw [hrearr]
      omega
    have hcancel : m * F ≤ 2 * n * (a - 1) * C :=
      Nat.le_of_mul_le_mul_left he ha
    calc
      m * (F * F) = (m * F) * F := by ac_rfl
      _ ≤ (2 * n * (a - 1) * C) * F :=
        Nat.mul_le_mul_right F hcancel
      _ = (2 * n * C) * ((a - 1) * F) := by ac_rfl
      _ ≤ (2 * n * C) * (2 * C) :=
        Nat.mul_le_mul_left _ hhi
      _ = (2 * 2) * n * (C * C) := by ac_rfl
      _ = 4 * n * (C * C) := rfl

theorem lazyTail_square (k m : Nat) :
    m * (lazyTail k 1 m * lazyTail k 1 m) ≤
      4 * (k + 2) * ((k + 2) ^ m * (k + 2) ^ m) :=
  square_tail_of_cutoffs (k + 2) m ((k + 2) ^ m)
    (lazyTail k 1 m) (fun a ha => lazyTail_cutoff k a m ha)

/-- Uniform individual square bounds also bound the square of a sum. -/
theorem ofFn_sum_square_bound {r : Nat}
    (f : Fin r → Nat) (a b : Nat)
    (hf : ∀ i, a * (f i * f i) ≤ b) :
    a * ((List.ofFn f).sum * (List.ofFn f).sum) ≤ (r * r) * b := by
  let S := (List.ofFn f).sum
  have hp (i j : Fin r) : a * (f i * f j) ≤ b := by
    rcases Nat.le_total (f i) (f j) with h | h
    · exact Nat.le_trans
        (Nat.mul_le_mul_left a (Nat.mul_le_mul_right (f j) h)) (hf j)
    · exact Nat.le_trans
        (Nat.mul_le_mul_left a (Nat.mul_le_mul_left (f i) h)) (hf i)
  have hr (i : Fin r) : (a * f i) * S ≤ r * b := by
    have hs := ofFn_sum_le
      (fun j : Fin r => (a * f i) * f j)
      (fun _ : Fin r => b)
      (fun j => by simpa only [Nat.mul_assoc] using hp i j)
    rw [ofFn_sum_mul_left, ofFn_sum_const] at hs
    exact hs
  have hs := ofFn_sum_le
    (fun i : Fin r => (a * S) * f i)
    (fun _ : Fin r => r * b)
    (fun i => by
      have he : (a * S) * f i = (a * f i) * S := by ac_rfl
      rw [he]
      exact hr i)
  rw [ofFn_sum_mul_left, ofFn_sum_const] at hs
  calc
    a * ((List.ofFn f).sum * (List.ofFn f).sum) = (a * S) * S := by
      dsimp [S]
      ac_rfl
    _ ≤ r * (r * b) := hs
    _ = (r * r) * b := by ac_rfl

private theorem add_square_le (a b : Nat) :
    (a + b) * (a + b) ≤ 2 * (a * a + b * b) := by
  rcases Nat.le_total a b with h | h
  · let d := b - a
    have he : b = a + d := by dsimp [d]; omega
    rw [he]
    simp only [Nat.add_mul, Nat.mul_add]
    have hc : d * a = a * d := Nat.mul_comm d a
    rw [hc]
    omega
  · let d := a - b
    have he : a = b + d := by dsimp [d]; omega
    rw [he]
    simp only [Nat.add_mul, Nat.mul_add]
    have hc : d * b = b * d := Nat.mul_comm d b
    rw [hc]
    omega

/-- Square form of the first-moment estimate used in B.16. -/
theorem squared_mean_of_excess (n C A S : Nat)
    (hn : 16 ≤ n) (hS : S ≤ C + A)
    (hA : 16 * (A * A) ≤ n * (C * C)) :
    4 * (S * S) ≤ n * (C * C) := by
  have hq := Nat.le_trans (square_le_square hS) (add_square_le C A)
  have hs := Nat.mul_le_mul_left 8 hq
  have he :
      8 * (2 * (C * C + A * A)) =
        16 * (C * C) + 16 * (A * A) := by
    rw [← Nat.mul_assoc]
    change 16 * (C * C + A * A) = _
    rw [Nat.mul_add]
  rw [he] at hs
  have hC : 16 * (C * C) ≤ n * (C * C) :=
    Nat.mul_le_mul_right (C * C) hn
  omega

private theorem product_lower_of_squares (q a b : Nat)
    (ha : q ≤ a * a) (hb : q ≤ b * b) :
    q ≤ a * b := by
  rcases Nat.le_total a b with h | h
  · exact Nat.le_trans ha (Nat.mul_le_mul_left a h)
  · exact Nat.le_trans hb (Nat.mul_le_mul_right b h)

/-- Squared Markov inequality, proved by summing over pairs of words. -/
theorem endpoint_event_square_le {S : Type} {n : Nat}
    (next : S → Fin n → S) (v : S → Nat) (P : S → Prop)
    (q : Nat) (h : ∀ y, ¬ P y → q ≤ v y * v y)
    (x : S) (T : Nat) :
    q * (wordSum next (miss P) x T * wordSum next (miss P) x T) ≤
      wordSum next v x T * wordSum next v x T := by
  classical
  let F := wordSum next (miss P) x T
  let V := wordSum next v x T
  have hr (y : S) (hy : ¬ P y) : q * F ≤ v y * V := by
    have hp (z : S) : q * miss P z ≤ v y * v z := by
      by_cases hz : P z
      · simp [miss, hz]
      · simp only [miss, if_neg hz, Nat.mul_one]
        exact product_lower_of_squares q (v y) (v z) (h y hy) (h z hz)
    have hs := wordSum_mono next _ _ hp x T
    rw [wordSum_mul, wordSum_mul] at hs
    exact hs
  have hp (y : S) : (q * F) * miss P y ≤ V * v y := by
    by_cases hy : P y
    · simp [miss, hy]
    · simp only [miss, if_neg hy, Nat.mul_one]
      simpa only [Nat.mul_comm] using hr y hy
  have hs := wordSum_mono next _ _ hp x T
  rw [wordSum_mul, wordSum_mul] at hs
  change (q * F) * F ≤ V * V at hs
  simpa only [Nat.mul_assoc] using hs

theorem quarter_fail_of_squared_mean {S : Type} {n : Nat}
    (hn : 0 < n) (next : S → Fin n → S) (v : S → Nat)
    (x : S) (T : Nat)
    (hmean : 4 * (wordSum next v x T * wordSum next v x T) ≤
      n * (n ^ T * n ^ T)) :
    4 * wordSum next (miss (fun y => v y * v y ≤ 4 * n)) x T ≤
      n ^ T := by
  let F := wordSum next (miss (fun y => v y * v y ≤ 4 * n)) x T
  let V := wordSum next v x T
  let C := n ^ T
  have ht : (4 * n) * (F * F) ≤ V * V :=
    endpoint_event_square_le next v (fun y => v y * v y ≤ 4 * n)
      (4 * n) (by intro y hy; omega) x T
  have hs : n * ((4 * F) * (4 * F)) ≤ n * (C * C) := by
    calc
      n * ((4 * F) * (4 * F)) = 4 * ((4 * n) * (F * F)) := by
        ac_rfl
      _ ≤ 4 * (V * V) := Nat.mul_le_mul_left 4 ht
      _ ≤ n * (C * C) := hmean
  have hsq : (4 * F) * (4 * F) ≤ C * C :=
    Nat.le_of_mul_le_mul_left hs hn
  exact le_of_square_le hsq


/-! A fixed-block timer supplying the existing retry theorem. -/

open L3.Prob
open PPL.Convergence.LDLocal
  (AttemptNode RetryKernel attemptCostNumerator retryCount)

private noncomputable def blockKernel {S : Type} {n : Nat}
    (next : S → Fin n → S) (Good : S → Prop)
    (B : Nat) : RetryKernel (S × Nat) S n := by
  classical
  exact
    { start := fun x => (x, B - 1)
      step := fun a e =>
        if Good (next a.1 e) then .success
        else
          match a.2 with
          | 0 => .retry (next a.1 e)
          | k + 1 => .active (next a.1 e, k)
      valid := fun _ => True
      retry_valid := by
        intro a e s h
        exact True.intro }

private theorem blockAttemptCost {S : Type} {n : Nat}
    (next : S → Fin n → S) (Good : S → Prop) (B : Nat) :
    ∀ T x k,
      attemptCostNumerator (blockKernel next Good B)
        (.active (x, k)) T ≤ n ^ T * (k + 1) := by
  classical
  intro T
  induction T with
  | zero =>
      intro x k
      simp [attemptCostNumerator]
  | succ T ih =>
      intro x k
      have hchild (e : Fin n) :
          attemptCostNumerator (blockKernel next Good B)
            ((blockKernel next Good B).step (x, k) e) T ≤ n ^ T * k := by
        by_cases hy : Good (next x e)
        · cases T <;> simp [blockKernel, hy, attemptCostNumerator]
        · cases k with
          | zero =>
              cases T <;> simp [blockKernel, hy, attemptCostNumerator]
          | succ k =>
              simpa only [blockKernel, if_neg hy] using ih (next x e) k
      change n ^ (T + 1) +
          (List.ofFn (fun e : Fin n =>
            attemptCostNumerator (blockKernel next Good B)
              ((blockKernel next Good B).step (x, k) e) T)).sum
          ≤ n ^ (T + 1) * (k + 1)
      calc
        _ ≤ n ^ (T + 1) +
            (List.ofFn (fun _ : Fin n => n ^ T * k)).sum :=
          Nat.add_le_add_left (ofFn_sum_le _ _ hchild) _
        _ = _ := by
          simp only [ofFn_sum_const, Nat.pow_succ, Nat.mul_add, Nat.mul_one]
          ac_rfl

private theorem blockRetryEarly {S : Type} {n : Nat}
    (next : S → Fin n → S) (Good : S → Prop) (B : Nat) :
    ∀ T x k, T ≤ k →
      retryCount (blockKernel next Good B) (.active (x, k)) T = 0 := by
  classical
  intro T
  induction T with
  | zero => intro x k h; rfl
  | succ T ih =>
      intro x k h
      cases k with
      | zero => omega
      | succ k =>
          rw [retryCount]
          calc
            _ = (List.ofFn (fun _ : Fin n => 0)).sum := by
              apply ofFn_sum_eq
              intro e
              by_cases hy : Good (next x e)
              · simp [blockKernel, hy, retryCount]
              · simpa only [blockKernel, if_neg hy] using
                  ih (next x e) k (by omega)
            _ = 0 := by simp [ofFn_sum_const]

/-- Exact failure mass after expiration, including all unused suffixes. -/
private theorem blockRetryLate {S : Type} {n : Nat}
    (next : S → Fin n → S) (Good : S → Prop) (B : Nat)
    (hc : ∀ x e, Good x → Good (next x e)) :
    ∀ k x U,
      retryCount (blockKernel next Good B)
        (.active (x, k)) ((k + 1) + U) =
        n ^ U * wordSum next (miss Good) x (k + 1) := by
  classical
  intro k
  induction k with
  | zero =>
      intro x U
      rw [show (0 + 1) + U = U + 1 by omega]
      rw [retryCount, wordSum_succ, ← ofFn_sum_mul_left]
      apply ofFn_sum_eq
      intro e
      by_cases hy : Good (next x e)
      · simp [blockKernel, hy, retryCount, miss]
      · simp [blockKernel, hy, retryCount, miss]
  | succ k ih =>
      intro x U
      rw [show (k + 1 + 1) + U = (k + 1 + U) + 1 by omega]
      rw [retryCount, wordSum_succ, ← ofFn_sum_mul_left]
      apply ofFn_sum_eq
      intro e
      by_cases hy : Good (next x e)
      · rw [miss_zero next Good hc (next x e) hy (k + 1)]
        simp [blockKernel, hy, retryCount]
      · simpa only [blockKernel, if_neg hy] using ih (next x e) U

/-- Derive the nondegenerate retry premises from a uniform block bound. -/
theorem costNumerator_of_block {S : Type} {n : Nat}
    (next : S → Fin n → S) (Good : S → Prop)
    (B num den : Nat)
    (hB : 0 < B) (hrho : num < den)
    (hc : ∀ x e, Good x → Good (next x e))
    (hb : ∀ x, den * wordSum next (miss Good) x B ≤ num * n ^ B) :
    ∀ x T,
      costNumerator next Good x T ≤ n ^ T * renewalCeiling B num den := by
  classical
  let K := blockKernel next Good B
  let Rel : S → S × Nat → Prop := fun x a => x = a.1
  have hpred : B - 1 + 1 = B := by omega
  have hsim : RetrySimulation K next Good Rel := by
    intro x a hrel hx e
    rcases a with ⟨y, k⟩
    change x = y at hrel
    subst y
    by_cases hy : Good (next x e)
    · simp [K, blockKernel, hy]
    · cases k <;> simp [K, blockKernel, hy, Rel]
  have hcost : ∀ s, K.valid s → ∀ T,
      costNumerator (attemptStepper K)
        (fun q => attemptGood q ∨ attemptFail q)
        (.active (K.start s)) T ≤ n ^ T * B := by
    intro s hs T
    rw [attempt_costNumerator_eq]
    change attemptCostNumerator (blockKernel next Good B)
      (.active (s, B - 1)) T ≤ n ^ T * B
    simpa only [hpred] using blockAttemptCost next Good B T s (B - 1)
  have hfail : ∀ s, K.valid s → ∀ T,
      den * retryCount K (.active (K.start s)) T ≤ num * n ^ T := by
    intro s hs T
    change den * retryCount (blockKernel next Good B)
      (.active (s, B - 1)) T ≤ num * n ^ T
    by_cases hsmall : T ≤ B - 1
    · rw [blockRetryEarly next Good B T s (B - 1) hsmall]
      simp
    · let U := T - B
      have hT : T = (B - 1 + 1) + U := by dsimp [U]; omega
      rw [hT, blockRetryLate next Good B hc (B - 1) s U]
      calc
        den * (n ^ U *
            wordSum next (miss Good) s (B - 1 + 1)) =
            n ^ U * (den * wordSum next (miss Good) s B) := by
          rw [hpred]
          ac_rfl
        _ ≤ n ^ U * (num * n ^ B) := Nat.mul_le_mul_left _ (hb s)
        _ = num * n ^ ((B - 1 + 1) + U) := by
          rw [hpred, Nat.pow_add]
          ac_rfl
  intro x T
  exact costNumerator_renewal_le next Good K Rel hsim
    B num den hrho hcost hfail x x True.intro rfl T

theorem densityRenewalCeiling (n : Nat) :
    renewalCeiling (144 * n ^ 2) 1 4 = 192 * n ^ 2 := by
  have he : (144 * n ^ 2) * 4 = (192 * n ^ 2) * 3 := by omega
  simp only [renewalCeiling, ceilNat]
  rw [he]
  simp

theorem costNumerator_of_quarter_block {S : Type} {n : Nat}
    (hn : 16 ≤ n)
    (next : S → Fin n → S) (Good : S → Prop)
    (hc : ∀ x e, Good x → Good (next x e))
    (hb : ∀ x,
      4 * wordSum next (miss Good) x (144 * n ^ 2) ≤ n ^ (144 * n ^ 2)) :
    ∀ x T,
      costNumerator next Good x T ≤ n ^ T * (192 * n ^ 2) := by
  have hnpos : 0 < n := by omega
  have hpow : 0 < n ^ 2 := by
    simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using
      Nat.mul_pos hnpos hnpos
  have hB : 0 < 144 * n ^ 2 := by omega
  intro x T
  have h := costNumerator_of_block next Good (144 * n ^ 2) 1 4
    hB (by decide) hc
    (by intro y; simpa only [Nat.one_mul] using hb y) x T
  simpa only [densityRenewalCeiling] using h


/-! The three requested particle bounds. -/

/-- Exact count of words on which one specified adjacent pair has not met. -/
noncomputable def adjacentPairCount {n : Nat} (i : Fin n) (m : Nat) : Nat :=
  L3.Prob.scheduleSum n m (fun w =>
    if lineageAfter i w = lineageAfter (successor i) w then 0 else 1)

/-- Endpoint inequality is precisely survival of the first meeting time. -/
theorem adjacentPairCount_eq_survival {n : Nat} (i : Fin n) (m : Nat) :
    adjacentPairCount i m =
      UniformFirstHit.survivalNumerator lineagePairStep
        (fun p : Fin n × Fin n => p.1 = p.2) (i, successor i) m := by
  rw [adjacentPairCount, scheduleSum_lineagePair]
  exact (survival_eq_endpoint lineagePairStep
    (fun p : Fin n × Fin n => p.1 = p.2)
    lineagePair_diagonal (i, successor i) m).symm

/-- Squared B.14, with constant 4 in place of the sufficient constant 9. -/
theorem adjacent_pair_tail_square {n : Nat} (hn : 2 ≤ n)
    (i : Fin n) (m : Nat) :
    m * (adjacentPairCount i m) ^ 2 ≤ 4 * n * (n ^ m) ^ 2 := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, n = k + 2 := ⟨n - 2, by omega⟩
  subst n
  have hle := adjacentLineageTail_le k m i
  have hs := Nat.mul_le_mul_left m (square_le_square hle)
  have ht := Nat.le_trans hs (lazyTail_square k m)
  simpa only [adjacentPairCount, scheduleSum_lineagePair,
    Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using ht

/-- The square of the first moment at the selected block length. -/
theorem particles_block_squared_mean {n : Nat} (hn : 16 ≤ n)
    (o : Occupancy n) :
    4 * (wordSum step N o (144 * n ^ 2) *
      wordSum step N o (144 * n ^ 2)) ≤
      n * (n ^ (144 * n ^ 2) * n ^ (144 * n ^ 2)) := by
  let B := 144 * n ^ 2
  let C := n ^ B
  let f : Fin n → Nat := fun i =>
    wordSum lineagePairStep (miss (fun p : Fin n × Fin n => p.1 = p.2))
      (i, successor i) B
  let A := (List.ofFn f).sum
  have hp (i : Fin n) : B * (f i * f i) ≤ 4 * n * (C * C) := by
    have h := adjacent_pair_tail_square (show 2 ≤ n by omega) i B
    simpa only [adjacentPairCount, scheduleSum_lineagePair,
      Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using h
  have hsum := ofFn_sum_square_bound f B (4 * n * (C * C)) hp
  change B * (A * A) ≤ (n * n) * (4 * n * (C * C)) at hsum
  have hscaled :
      (4 * (n * n)) * (36 * (A * A)) ≤
        (4 * (n * n)) * (n * (C * C)) := by
    calc
      (4 * (n * n)) * (36 * (A * A)) =
          (144 * n ^ 2) * (A * A) := by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
        calc
          (4 * (n * n)) * (36 * (A * A)) =
              (4 * 36) * (n * n) * (A * A) := by ac_rfl
          _ = (144 * (n * n)) * (A * A) := rfl
      _ ≤ (n * n) * (4 * n * (C * C)) := hsum
      _ = (4 * (n * n)) * (n * (C * C)) := by ac_rfl
  have hnpos : 0 < n := by omega
  have hfactor : 0 < 4 * (n * n) :=
    Nat.mul_pos (by decide) (Nat.mul_pos hnpos hnpos)
  have hstrong : 36 * (A * A) ≤ n * (C * C) :=
    Nat.le_of_mul_le_mul_left hscaled hfactor
  have hA : 16 * (A * A) ≤ n * (C * C) :=
    Nat.le_trans
      (Nat.mul_le_mul_right (A * A) (by decide : 16 ≤ 36)) hstrong
  have hS : wordSum step N o B ≤ C + A :=
    particles_first_moment_le o B
  exact squared_mean_of_excess n C A (wordSum step N o B) hn hS hA

/-- Scaled B.16, suitable as the exact retry-mass premise. -/
theorem particles_block_fail_scaled {n : Nat} (hn : 16 ≤ n)
    (o : Occupancy n) :
    4 * wordSum step (miss (fun p : Occupancy n => N p * N p ≤ 4 * n))
      o (144 * n ^ 2) ≤ n ^ (144 * n ^ 2) :=
  quarter_fail_of_squared_mean (by omega) step N o (144 * n ^ 2)
    (particles_block_squared_mean hn o)

/-- Literal number of bad complete scheduler words, with denominator n^T. -/
noncomputable def particlesFailureCount {n : Nat} (o : Occupancy n)
    (T : Nat) : Nat :=
  L3.Prob.scheduleSum n T
    (fun w => if 4 * n < (N (after o w)) ^ 2 then 1 else 0)

theorem particlesFailureCount_eq {n : Nat} (o : Occupancy n) (T : Nat) :
    particlesFailureCount o T =
      wordSum step (miss (fun p : Occupancy n => N p * N p ≤ 4 * n)) o T := by
  classical
  unfold particlesFailureCount
  rw [← scheduleSum_after (miss (fun p : Occupancy n => N p * N p ≤ 4 * n)) o T]
  apply congrArg (L3.Prob.scheduleSum n T)
  funext w
  by_cases hg : N (after o w) * N (after o w) ≤ 4 * n
  · have hh : ¬ 4 * n < N (after o w) * N (after o w) := by omega
    simp [miss, hg, hh, Nat.pow_succ]
  · have hh : 4 * n < N (after o w) * N (after o w) := by omega
    simp [miss, hg, hh, Nat.pow_succ]

/-- B.16 for every occupancy, without a reachability hypothesis. -/
theorem particles_block_fail {n : Nat} (hn : 16 ≤ n) (o : Occupancy n) :
    particlesFailureCount o (144 * n ^ 2) ≤ n ^ (144 * n ^ 2) / 4 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < (4 : Nat))).2
  have h := particles_block_fail_scaled hn o
  rw [particlesFailureCount_eq]
  simpa only [Nat.mul_comm] using h

/-- Pathwise closure of the squared density target. -/
theorem density_target_closed {n : Nat} (o : Occupancy n) (e : Fin n)
    (h : N o * N o ≤ 4 * n) :
    N (step o e) * N (step o e) ≤ 4 * n :=
  Nat.le_trans (square_le_square (N_step_le o e)) h

/-- The requested finite-prefix expected density-entrance cost. -/
theorem particles_cost {n : Nat} (hn : 16 ≤ n)
    (o : Occupancy n) (T : Nat) :
    costNumerator step (fun p : Occupancy n => N p * N p ≤ 4 * n) o T ≤
      n ^ T * (192 * n ^ 2) := by
  exact costNumerator_of_quarter_block hn step
    (fun p : Occupancy n => N p * N p ≤ 4 * n)
    density_target_closed (fun p => particles_block_fail_scaled hn p) o T

end L3.Density
