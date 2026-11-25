import Leader.L4.Height.Quiet
import Leader.L4.Height.RepairStrict

/-!
# Strict service cover for the quiet-clock recovery stage

`Thru.wait` tests the source state before consuming a letter.  That convention
cannot certify a publication when the source already has `lastAct = some i`,
because `ClockChain` gives no predecessor witness for an arbitrary source.
Accordingly `ClockChain.waitAfter` ignores the source `lastAct` and waits for a
served state reached after at least one scheduler step.

The one-step shift costs one factor two in the exponential moment.  Thus a
plain per-site `MomentAt` constant `2` gives a strict post-step wait constant
`4`; this is exactly the quiet-stage `Mq = 4` used by `repairTimeBudget`.
-/

namespace L4.Height.Recover.CoverOne

open L4.Compiler.Native
open Classical

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

noncomputable section

/-- A chain whose scheduler letters optionally drive one native-clock
publication.  This is the interface requested by the recovery composition. -/
structure ClockChain (α : Type) (n m : Nat) (B M : Nat) (hm : 0 < m) where
  next : α → Fin n → α
  cfg : α → Fin m → NativeRecord
  act : α → Fin n → Option (Fin m × Bool)
  lastAct : α → Option (Fin m)
  cfg_next : ∀ x e, cfg (next x e) =
    match act x e with
    | none => cfg x
    | some p => StageOne.activate B M hm (cfg x) p.1 p.2
  last_next : ∀ x e, lastAct (next x e) = (act x e).map Prod.fst

/-- Site `i` is the publication recorded by the current state. -/
def ClockChain.served
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (i : Fin m) (x : α) : Prop :=
  C.lastAct x = some i

/-- Actual native-clock activations generated while consuming a scheduler
word, in execution order.  Letters with `act = none` are omitted. -/
def ClockChain.activations
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) :
    α → Thru.Word n → List (Fin m × Bool)
  | _, [] => []
  | x, e :: u =>
      match C.act x e with
      | none => activations C (C.next x e) u
      | some p => p :: activations C (C.next x e) u

/-- First positive service time.  On `e :: u`, the first consumed letter
moves to `C.next x e`, and ordinary `Thru.wait` starts there.  If no served
state is seen, this equals the whole word length. -/
def ClockChain.waitAfter
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (i : Fin m) (x : α) :
    Thru.Word n → Nat
  | [] => 0
  | e :: u =>
      Nat.succ (Thru.wait C.next (C.served i) (C.next x e) u)

/-- One strict post-step wait function for every site. -/
def ClockChain.waitsAfter
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (x : α) :
    List (Thru.Word n → Nat) :=
  (List.finRange m).map (fun i => C.waitAfter i x)

/-- Source predicate used by the quiet stage. -/
def ClockChain.BoundedSource
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (x : α) : Prop :=
  StageOne.TickBound M (C.cfg x)

/-- Target predicate produced by the quiet stage. -/
def ClockChain.AllQuiet
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (x : α) : Prop :=
  ∀ i, StageOne.Quiet M hm (C.cfg x) i

variable {α : Type} {n m B M : Nat} {hm : 0 < m}

/-- Projecting a scheduler execution to native records is exactly execution of
its filtered native activation list. -/
theorem cfg_runWord
    (C : ClockChain α n m B M hm) (x : α) :
    ∀ u : Thru.Word n,
      C.cfg (runWord C.next x u) =
        StageOne.runWord B M hm (C.activations x u) (C.cfg x) := by
  intro u
  induction u generalizing x with
  | nil =>
      rfl
  | cons e u ih =>
      rw [show runWord C.next x (e :: u) =
        runWord C.next (C.next x e) u from rfl]
      rw [ih (x := C.next x e)]
      rw [C.cfg_next x e]
      cases hact : C.act x e with
      | none =>
          simp only [ClockChain.activations, hact]
      | some p =>
          rcases p with ⟨i, delta⟩
          simp only [ClockChain.activations, hact, StageOne.runWord]

/-- A served successor records an actual activation of the served site on the
letter that produced it. -/
private theorem act_of_served_next
    (C : ClockChain α n m B M hm) (i : Fin m)
    (x : α) (e : Fin n)
    (hserved : C.served i (C.next x e)) :
    ∃ delta, C.act x e = some (i, delta) := by
  unfold ClockChain.served at hserved
  rw [C.last_next x e] at hserved
  cases hact : C.act x e with
  | none =>
      simp [hact] at hserved
  | some p =>
      rcases p with ⟨j, delta⟩
      have hji : j = i := by
        simpa [hact] using hserved
      subst j
      exact ⟨delta, rfl⟩

/-- An activation present in a tail remains present after one earlier letter. -/
private theorem activated_of_tail
    (C : ClockChain α n m B M hm) (i : Fin m)
    (x : α) (e : Fin n) (u : Thru.Word n)
    (h : StageOne.Activated (C.activations (C.next x e) u) i) :
    StageOne.Activated (C.activations x (e :: u)) i := by
  rcases h with ⟨delta, hmem⟩
  refine ⟨delta, ?_⟩
  cases hact : C.act x e with
  | none =>
      simpa only [ClockChain.activations, hact] using hmem
  | some p =>
      simp only [ClockChain.activations, hact, List.mem_cons]
      exact Or.inr hmem

/-- Away from a source hit, `waitAfter` and ordinary `wait` agree. -/
private theorem waitAfter_eq_wait_of_not
    (C : ClockChain α n m B M hm) (i : Fin m)
    (x : α) (hnot : ¬ C.served i x) :
    ∀ u : Thru.Word n,
      C.waitAfter i x u = Thru.wait C.next (C.served i) x u := by
  intro u
  cases u with
  | nil =>
      rfl
  | cons e u =>
      simp only [ClockChain.waitAfter]
      rw [Thru.wait_cons_of_not C.next (C.served i) x hnot e u]

/-- Strong form used by the cover: if the positive service time is at most
`k`, and `k` is a strict prefix length, then site `i` occurs in the activation
list of that prefix. -/
theorem served_by_activated
    (C : ClockChain α n m B M hm) (i : Fin m) (x : α) :
    ∀ (u : Thru.Word n) (k : Nat),
      C.waitAfter i x u ≤ k →
      k < u.length →
      StageOne.Activated (C.activations x (u.take k)) i := by
  intro u
  induction u generalizing x with
  | nil =>
      intro k _hwait hk
      simp only [List.length_nil] at hk
      omega
  | cons e u ih =>
      intro k hwait hk
      cases k with
      | zero =>
          simp only [ClockChain.waitAfter] at hwait
          omega
      | succ k =>
          simp only [List.length_cons] at hk
          have hkTail : k < u.length := by omega
          by_cases hserved : C.served i (C.next x e)
          · obtain ⟨delta, hact⟩ :=
              act_of_served_next C i x e hserved
            refine ⟨delta, ?_⟩
            simp only [List.take_succ_cons, ClockChain.activations,
              hact, List.mem_cons]
            exact Or.inl True.intro
          · have heq :
                C.waitAfter i (C.next x e) u =
                  Thru.wait C.next (C.served i) (C.next x e) u :=
              waitAfter_eq_wait_of_not C i (C.next x e) hserved u
            have houter :
                C.waitAfter i x (e :: u) =
                  Nat.succ (C.waitAfter i (C.next x e) u) := by
              calc
                C.waitAfter i x (e :: u) =
                    Nat.succ
                      (Thru.wait C.next (C.served i) (C.next x e) u) := rfl
                _ = Nat.succ (C.waitAfter i (C.next x e) u) :=
                  congrArg Nat.succ heq.symm
            have hinner : C.waitAfter i (C.next x e) u ≤ k := by
              rw [houter] at hwait
              omega
            have htail := ih (x := C.next x e) k hinner hkTail
            have hlift :=
              activated_of_tail C i x e (u.take k) htail
            simpa only [List.take_succ_cons] using hlift

/-- Requested exact-time form. -/
theorem served_wait_activated
    (C : ClockChain α n m B M hm) (i : Fin m)
    (x : α) (u : Thru.Word n)
    (hstrict : C.waitAfter i x u < u.length) :
    StageOne.Activated
      (C.activations x (u.take (C.waitAfter i x u))) i := by
  exact served_by_activated C i x u (C.waitAfter i x u)
    (Nat.le_refl _) hstrict

/-- The positive wait never exceeds the supplied word length. -/
theorem waitAfter_le_length
    (C : ClockChain α n m B M hm) (i : Fin m)
    (x : α) (u : Thru.Word n) :
    C.waitAfter i x u ≤ u.length := by
  cases u with
  | nil =>
      simpa only [ClockChain.waitAfter, List.length_nil] using
        (Nat.le_refl 0)
  | cons e u =>
      simp only [ClockChain.waitAfter, List.length_cons]
      exact Nat.succ_le_succ
        (Thru.wait_le_length C.next (C.served i) (C.next x e) u)

/-- Successor commutes with `Nat.min`. -/
private theorem min_succ_succ (a b : Nat) :
    Nat.min (Nat.succ a) (Nat.succ b) =
      Nat.succ (Nat.min a b) := by
  simpa only [Nat.succ_eq_add_one] using
    (Nat.add_min_add_right a b 1)

/-- Adding one before floor division adds at most one to the quotient. -/
private theorem div_succ_le (a L : Nat) (hL : 1 ≤ L) :
    Nat.succ a / L ≤ a / L + 1 := by
  have _hpos : 0 < L := by omega
  rw [Nat.succ_eq_add_one, Nat.succ_div]
  split <;> omega

/-- Pointwise exponential cost of the one-step positive-wait shift. -/
private theorem shifted_exp_le (a t L : Nat) (hL : 1 ≤ L) :
    2 ^ (Nat.min (Nat.succ a) (Nat.succ t) / L) ≤
      2 * 2 ^ (Nat.min a t / L) := by
  rw [min_succ_succ]
  have hdiv := div_succ_le (Nat.min a t) L hL
  have hpow := Nat.pow_le_pow_right
    (by omega : 0 < (2 : Nat)) hdiv
  calc
    2 ^ (Nat.succ (Nat.min a t) / L)
        ≤ 2 ^ (Nat.min a t / L + 1) := hpow
    _ = 2 * 2 ^ (Nat.min a t / L) := by
      rw [Nat.pow_succ]
      ac_rfl

/-- Sum of a constant over `Fin n`, proved locally because the corresponding
throughput helper is private. -/
private theorem sum_ofFn_const (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero =>
      simp [List.ofFn_zero]
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih]
      simp only [Nat.add_mul, Nat.one_mul]
      omega

/-- A plain `MomentAt` bound of `2` yields a post-step strict-wait bound of
`4`.  The additional factor is exactly the one-step shift. -/
theorem waitAfter_moment_four
    (C : ClockChain α n m B M hm) (i : Fin m)
    (L : Nat) (hL : 1 ≤ L)
    (hMom : ∀ y, Thru.MomentAt C.next (C.served i) L y)
    (x : α) :
    ∀ t,
      Thru.wordSum
          (fun u =>
            2 ^ (Nat.min (C.waitAfter i x u) t / L)) t ≤
        4 * n ^ t := by
  intro t
  cases t with
  | zero =>
      simp [Thru.wordSum, ClockChain.waitAfter]
  | succ t =>
      have hEach : ∀ e : Fin n,
          Thru.wordSum
              (fun v =>
                2 ^ (Nat.min
                  (C.waitAfter i x (e :: v)) (Nat.succ t) / L)) t ≤
            4 * n ^ t := by
        intro e
        have hpoint : ∀ v : Thru.Word n,
            2 ^ (Nat.min
                (C.waitAfter i x (e :: v)) (Nat.succ t) / L) ≤
              2 * 2 ^ (Nat.min
                (Thru.wait C.next (C.served i) (C.next x e) v) t / L) := by
          intro v
          simpa only [ClockChain.waitAfter] using
            (shifted_exp_le
              (Thru.wait C.next (C.served i) (C.next x e) v)
              t L hL)
        have hsum := Thru.wordSum_mono
          (fun v =>
            2 ^ (Nat.min
              (C.waitAfter i x (e :: v)) (Nat.succ t) / L))
          (fun v =>
            2 * 2 ^ (Nat.min
              (Thru.wait C.next (C.served i) (C.next x e) v) t / L))
          hpoint t
        rw [Thru.wordSum_mul_left] at hsum
        calc
          Thru.wordSum
              (fun v =>
                2 ^ (Nat.min
                  (C.waitAfter i x (e :: v)) (Nat.succ t) / L)) t
              ≤ 2 * Thru.wordSum
                  (fun v =>
                    2 ^ (Nat.min
                      (Thru.wait C.next (C.served i)
                        (C.next x e) v) t / L)) t := hsum
          _ ≤ 2 * (2 * n ^ t) :=
            Nat.mul_le_mul_left 2 (hMom (C.next x e) t)
          _ = 4 * n ^ t := by omega
      simp only [Thru.wordSum]
      calc
        (List.ofFn (fun e : Fin n =>
          Thru.wordSum
              (fun v =>
                2 ^ (Nat.min
                  (C.waitAfter i x (e :: v)) (Nat.succ t) / L)) t)).sum
            ≤ (List.ofFn (fun _ : Fin n => 4 * n ^ t)).sum :=
              Thru.ofFn_sum_le _ _ hEach
        _ = n * (4 * n ^ t) := sum_ofFn_const n (4 * n ^ t)
        _ = 4 * n ^ Nat.succ t := by
          rw [Nat.pow_succ]
          ac_rfl

/-- The strict family contains exactly one function for each site. -/
theorem waitsAfter_length
    (C : ClockChain α n m B M hm) (x : α) :
    (C.waitsAfter x).length = m := by
  simp only [ClockChain.waitsAfter, List.length_map,
    List.length_finRange]

/-- Every site's positive wait occurs in the strict wait family. -/
theorem waitAfter_mem_waitsAfter
    (C : ClockChain α n m B M hm) (x : α) (i : Fin m) :
    C.waitAfter i x ∈ C.waitsAfter x := by
  unfold ClockChain.waitsAfter
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- Every member of a wait family is bounded by its pointwise maximum. -/
private theorem le_maxWait_of_mem
    {q : Nat} (Ws : List (Thru.Word q → Nat))
    (W : Thru.Word q → Nat) (hW : W ∈ Ws) (u : Thru.Word q) :
    W u ≤ Thru.maxWait Ws u := by
  induction Ws with
  | nil =>
      simp at hW
  | cons V Vs ih =>
      simp only [List.mem_cons] at hW
      simp only [Thru.maxWait]
      rcases hW with hEq | hTail
      · subst W
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hTail) (Nat.le_max_right _ _)

/-- Concrete strict-cover data at one bounded source state. -/
theorem quiet_cover_data
    (C : ClockChain α n m B M hm) (L : Nat)
    (hM : StageOne.ClockParams M) (hL : 1 ≤ L)
    (hMom : ∀ i y, Thru.MomentAt C.next (C.served i) L y)
    (x : α) (_hbound : StageOne.TickBound M (C.cfg x)) :
    ∃ Ws : List (Thru.Word n → Nat),
      Ws.length = m ∧
      (∀ W, W ∈ Ws → ∀ t,
        Thru.wordSum
            (fun u => 2 ^ (Nat.min (W u) t / L)) t ≤
          4 * n ^ t) ∧
      (∀ u : Thru.Word n, ∀ k,
        Thru.maxWait Ws u ≤ k →
        k < u.length →
        ClockChain.AllQuiet C (runWord C.next x (u.take k))) := by
  refine ⟨C.waitsAfter x, waitsAfter_length C x, ?_, ?_⟩
  · intro W hW t
    unfold ClockChain.waitsAfter at hW
    obtain ⟨i, _hi, hEq⟩ := List.mem_map.mp hW
    subst W
    exact waitAfter_moment_four C i L hL (hMom i) x t
  · intro u k hmax hk
    have hcovered :
        StageOne.Covered (C.activations x (u.take k)) := by
      unfold StageOne.Covered
      intro i
      have hmem : C.waitAfter i x ∈ C.waitsAfter x :=
        waitAfter_mem_waitsAfter C x i
      have hlemax :
          C.waitAfter i x u ≤ Thru.maxWait (C.waitsAfter x) u :=
        le_maxWait_of_mem (C.waitsAfter x) (C.waitAfter i x) hmem u
      have hwk : C.waitAfter i x u ≤ k :=
        Nat.le_trans hlemax hmax
      exact served_by_activated C i x u k hwk hk
    have hquiet :=
      StageOne.quiet_forever (B := B) (M := M)
        hM hm (C.activations x (u.take k)) [] (C.cfg x) hcovered
    unfold ClockChain.AllQuiet
    intro i
    have hcfg := cfg_runWord C x (u.take k)
    rw [hcfg]
    simpa only [StageOne.runWord] using hquiet i

/-- Stage-one native-clock quietness as the accepted strict stage cover. -/
theorem quiet_cover
    (C : ClockChain α n m B M hm) (L : Nat)
    (hM : StageOne.ClockParams M) (hL : 1 ≤ L)
    (hMom : ∀ i y, Thru.MomentAt C.next (C.served i) L y) :
    StageCoverStrict C.next
      (ClockChain.BoundedSource C)
      (ClockChain.AllQuiet C)
      L m 4 := by
  unfold StageCoverStrict
  intro x hx
  exact quiet_cover_data C L hM hL hMom x hx

end

end L4.Height.Recover.CoverOne

