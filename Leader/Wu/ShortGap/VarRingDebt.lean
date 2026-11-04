import Lean
import Init.Data.Fin.Lemmas
import Init.Data.List.OfFn
import Init.Data.List.Nat.Sum

/-!
# Variable-length ring debt for stop-and-wait denial carriers

Self-contained model of `m` independent gaps of variable lengths, using only
imports from the Lean distribution. This file is independent of the project's
`Leader.*` modules.

The progress theorem assumes the invariant `Valid len P`. The strict
child-sum inequality additionally assumes `0 < D len P`; the stopped version
charges one only while the debt is positive. Counterexamples to omitting
these hypotheses are included below.

The sigma-indexed sum enumerates every pair `(g, a)` with `a : Fin (len g)`
exactly once. A supplied two-sided equivalence transports it exactly to a
`Fin n` sum and certifies `n = totalLen len`.
-/

namespace VariableGap

set_option autoImplicit false

/-! ## Elementary finite sums -/

def sumOfFn {k : Nat} (f : Fin k → Nat) : Nat :=
  (List.ofFn f).sum

@[simp] theorem sum_ofFn_zero (f : Fin 0 → Nat) : sumOfFn f = 0 := by
  simp [sumOfFn]

theorem sum_ofFn_succ {k : Nat} (f : Fin (k + 1) → Nat) :
    sumOfFn f = f 0 + sumOfFn (fun i : Fin k => f i.succ) := by
  simp only [sumOfFn, List.ofFn_succ, List.sum_cons]

theorem sum_ofFn_eq {k : Nat} (f g : Fin k → Nat)
    (hfg : ∀ i, f i = g i) : sumOfFn f = sumOfFn g := by
  have h : f = g := funext hfg
  rw [h]

theorem sum_ofFn_le {k : Nat} (f g : Fin k → Nat)
    (hfg : ∀ i, f i ≤ g i) : sumOfFn f ≤ sumOfFn g := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sum_ofFn_succ, sum_ofFn_succ]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

theorem sum_ofFn_const (k c : Nat) :
    sumOfFn (fun _ : Fin k => c) = k * c := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sum_ofFn_succ, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

theorem sum_ofFn_add {k : Nat} (f g : Fin k → Nat) :
    sumOfFn (fun i => f i + g i) = sumOfFn f + sumOfFn g := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sum_ofFn_succ, sum_ofFn_succ, sum_ofFn_succ, ih]
      omega

theorem sum_ofFn_mul {k : Nat} (f : Fin k → Nat) (c : Nat) :
    sumOfFn (fun i => f i * c) = sumOfFn f * c := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sum_ofFn_succ, sum_ofFn_succ, ih, Nat.add_mul]

theorem sum_ofFn_single {k : Nat} (j : Fin k) (c : Nat) :
    sumOfFn (fun i => if i = j then c else 0) = c := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [sum_ofFn_succ, Fin.succ_ne_zero, sum_ofFn_const]
      · have hzero : (0 : Fin (k + 1)) ≠ j.succ := by
          intro he
          exact Fin.succ_ne_zero j he.symm
        simpa [sum_ofFn_succ, hzero] using ih j

theorem sum_ofFn_lt_of_single_lt {k : Nat}
    (f g : Fin k → Nat) (j : Fin k)
    (hle : ∀ i, f i ≤ g i) (hlt : f j < g j) :
    sumOfFn f < sumOfFn g := by
  have hpoint : ∀ i, f i + (if i = j then 1 else 0) ≤ g i := by
    intro i
    by_cases hi : i = j
    · subst i
      have hs : f j + 1 ≤ g j := by omega
      simpa using hs
    · simpa [hi] using hle i
  have hs := sum_ofFn_le
    (fun i => f i + (if i = j then 1 else 0)) g hpoint
  rw [sum_ofFn_add, sum_ofFn_single] at hs
  omega

theorem sum_ofFn_drop_one {k : Nat}
    (f g : Fin k → Nat) (j : Fin k)
    (hj : f j + 1 = g j)
    (hother : ∀ i, i ≠ j → f i = g i) :
    sumOfFn f + 1 = sumOfFn g := by
  have hpoint : ∀ i, f i + (if i = j then 1 else 0) = g i := by
    intro i
    by_cases hi : i = j
    · subst i
      simpa using hj
    · simp [hi, hother i hi]
  have hs := sum_ofFn_eq
    (fun i => f i + (if i = j then 1 else 0)) g hpoint
  rw [sum_ofFn_add, sum_ofFn_single] at hs
  exact hs

theorem sum_ofFn_pos_exists {k : Nat} (f : Fin k → Nat)
    (h : 0 < sumOfFn f) : ∃ i, 0 < f i := by
  induction k with
  | zero => simp at h
  | succ k ih =>
      rw [sum_ofFn_succ] at h
      by_cases hzero : 0 < f 0
      · exact ⟨0, hzero⟩
      · have htail : 0 < sumOfFn (fun i : Fin k => f i.succ) := by
          omega
        obtain ⟨i, hi⟩ := ih (fun i : Fin k => f i.succ) htail
        exact ⟨i.succ, hi⟩

theorem sum_ofFn_comm {k l : Nat} (f : Fin k → Fin l → Nat) :
    sumOfFn (fun i => sumOfFn (fun j => f i j)) =
      sumOfFn (fun j => sumOfFn (fun i => f i j)) := by
  induction k with
  | zero => simp [sum_ofFn_const]
  | succ k ih =>
      rw [sum_ofFn_succ]
      rw [ih (fun i j => f i.succ j)]
      rw [← sum_ofFn_add]
      apply sum_ofFn_eq
      intro j
      exact (sum_ofFn_succ (fun i : Fin (k + 1) => f i j)).symm

/-- The additive form avoids distributing truncated subtraction over a sum. -/
theorem sum_ofFn_twice_sub_one_add_card {m : Nat}
    (len : Fin m → Nat) (hlen : ∀ g, 1 ≤ len g) :
    sumOfFn (fun g => 2 * len g - 1) + m = 2 * sumOfFn len := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_ofFn_succ, sum_ofFn_succ]
      have htail := ih (fun i : Fin m => len i.succ)
        (fun i => hlen i.succ)
      have hhead := hlen 0
      omega

/-! ## One gap -/

inductive Phase where
  | prelaunch
  | declAt (j : Nat)
  | replyAt (j : Nat)
  | delivered
  deriving DecidableEq, Repr

def phaseDebt (h : Nat) : Phase → Nat
  | .prelaunch => 2 * h - 1
  | .declAt j => 2 * h - 1 - j
  | .replyAt j => j
  | .delivered => 0

/-- The literal transition rule, including stuttering on every other edge. -/
def nextPhase (h : Nat) : Phase → Nat → Phase
  | .prelaunch, a =>
      if a = 0 then
        if h = 1 then .delivered else .declAt 1
      else .prelaunch
  | .declAt j, a =>
      if a = j then
        if j = h - 1 then .replyAt (h - 1) else .declAt (j + 1)
      else .declAt j
  | .replyAt j, a =>
      if a = j - 1 then
        if j = 1 then .delivered else .replyAt (j - 1)
      else .replyAt j
  | .delivered, _ => .delivered

/--
The unique candidate edge. The bound on this candidate requires PhaseValid.
In particular, this function does not pretend that declAt 2 is valid at h = 2.
The zero-debt malformed phase replyAt 0 has no advancing edge.
-/
def advancingEdge : Phase → Option Nat
  | .prelaunch => some 0
  | .declAt j => some j
  | .replyAt j => if j = 0 then none else some (j - 1)
  | .delivered => none

/-- A natural invariant satisfied by every phase reachable from prelaunch. -/
def PhaseValid (h : Nat) : Phase → Prop
  | .prelaunch => True
  | .declAt j => 0 < j ∧ j < h
  | .replyAt j => 0 < j ∧ j < h
  | .delivered => True

/-- Monotonicity is unconditional: no validity or edge-range assumption. -/
theorem phaseDebt_next_le (h : Nat) (p : Phase) (a : Nat) :
    phaseDebt h (nextPhase h p a) ≤ phaseDebt h p := by
  cases p with
  | prelaunch =>
      by_cases ha : a = 0
      · by_cases hh : h = 1 <;>
          simp [nextPhase, phaseDebt, ha, hh] <;> omega
      · simp [nextPhase, ha]
  | declAt j =>
      by_cases ha : a = j
      · by_cases hj : j = h - 1 <;>
          simp [nextPhase, phaseDebt, ha, hj] <;> omega
      · simp [nextPhase, ha]
  | replyAt j =>
      by_cases ha : a = j - 1
      · by_cases hj : j = 1 <;>
          simp [nextPhase, phaseDebt, ha, hj] <;> omega
      · simp [nextPhase, ha]
  | delivered => simp [nextPhase]

theorem nextPhase_valid {h : Nat} {p : Phase}
    (hh : 1 ≤ h) (hp : PhaseValid h p) (a : Nat) :
    PhaseValid h (nextPhase h p a) := by
  cases p with
  | prelaunch =>
      by_cases ha : a = 0
      · by_cases h1 : h = 1 <;>
          simp [nextPhase, PhaseValid, ha, h1] <;> omega
      · simp [nextPhase, PhaseValid, ha]
  | declAt j =>
      have hj : 0 < j ∧ j < h := hp
      by_cases ha : a = j
      · by_cases hlast : j = h - 1 <;>
          simp [nextPhase, PhaseValid, ha, hlast] <;> omega
      · simpa [nextPhase, ha] using hp
  | replyAt j =>
      have hj : 0 < j ∧ j < h := hp
      by_cases ha : a = j - 1
      · by_cases h1 : j = 1 <;>
          simp [nextPhase, PhaseValid, ha, h1] <;> omega
      · simpa [nextPhase, ha] using hp
  | delivered => exact hp

theorem advancingEdge_exists {h : Nat} {p : Phase}
    (hh : 1 ≤ h) (hp : PhaseValid h p) (hd : 0 < phaseDebt h p) :
    ∃ a : Fin h, advancingEdge p = some a.val := by
  cases p with
  | prelaunch =>
      exact ⟨⟨0, by omega⟩, rfl⟩
  | declAt j =>
      have hj : 0 < j ∧ j < h := hp
      exact ⟨⟨j, hj.2⟩, rfl⟩
  | replyAt j =>
      have hj : 0 < j ∧ j < h := hp
      have hj0 : j ≠ 0 := by omega
      refine ⟨⟨j - 1, by omega⟩, ?_⟩
      simp [advancingEdge, hj0]
  | delivered => simp [phaseDebt] at hd

/-- A valid candidate edge reduces the debt by exactly one. -/
theorem phaseDebt_advance {h a : Nat} {p : Phase}
    (hh : 1 ≤ h) (hp : PhaseValid h p)
    (ha : advancingEdge p = some a) :
    phaseDebt h (nextPhase h p a) + 1 = phaseDebt h p := by
  cases p with
  | prelaunch =>
      have hzero : 0 = a := by simpa [advancingEdge] using ha
      subst a
      by_cases h1 : h = 1 <;>
        simp [nextPhase, phaseDebt, h1] <;> omega
  | declAt j =>
      have hj : 0 < j ∧ j < h := hp
      have hja : j = a := by simpa [advancingEdge] using ha
      subst a
      by_cases hlast : j = h - 1 <;>
        simp [nextPhase, phaseDebt, hlast] <;> omega
  | replyAt j =>
      have hj : 0 < j ∧ j < h := hp
      have hj0 : j ≠ 0 := by omega
      have hja : j - 1 = a := by simpa [advancingEdge, hj0] using ha
      subst a
      by_cases h1 : j = 1 <;>
        simp [nextPhase, phaseDebt, h1] <;> omega
  | delivered => simp [advancingEdge] at ha

theorem phaseDebt_advance_sub {h a : Nat} {p : Phase}
    (hh : 1 ≤ h) (hp : PhaseValid h p)
    (ha : advancingEdge p = some a) :
    phaseDebt h (nextPhase h p a) = phaseDebt h p - 1 := by
  have hs := phaseDebt_advance hh hp ha
  omega

theorem nextPhase_eq_self_of_not_advancing {h a : Nat} {p : Phase}
    (ha : advancingEdge p ≠ some a) : nextPhase h p a = p := by
  cases p with
  | prelaunch =>
      have hzero : a ≠ 0 := by
        intro hzero
        subst a
        exact ha rfl
      simp [nextPhase, hzero]
  | declAt j =>
      have hj : a ≠ j := by
        intro hj
        subst a
        exact ha rfl
      simp [nextPhase, hj]
  | replyAt j =>
      by_cases hj0 : j = 0
      · subst j
        simp [nextPhase]
      · have hj : a ≠ j - 1 := by
          intro he
          apply ha
          simp [advancingEdge, hj0, he]
        simp [nextPhase, hj]
  | delivered => rfl

theorem phaseDebt_next_lt_iff {h : Nat} {p : Phase}
    (hh : 1 ≤ h) (hp : PhaseValid h p) (a : Fin h) :
    phaseDebt h (nextPhase h p a.val) < phaseDebt h p ↔
      advancingEdge p = some a.val := by
  constructor
  · intro hlt
    by_cases ha : advancingEdge p = some a.val
    · exact ha
    · have hs := nextPhase_eq_self_of_not_advancing (h := h) ha
      rw [hs] at hlt
      omega
  · intro ha
    have hs := phaseDebt_advance hh hp ha
    omega

/-- Existence, exact decrement, and uniqueness among all legal edges. -/
theorem advancingEdge_unique {h : Nat} {p : Phase}
    (hh : 1 ≤ h) (hp : PhaseValid h p) (hd : 0 < phaseDebt h p) :
    ∃ a : Fin h,
      advancingEdge p = some a.val ∧
      phaseDebt h (nextPhase h p a.val) + 1 = phaseDebt h p ∧
      ∀ b : Fin h,
        (phaseDebt h (nextPhase h p b.val) < phaseDebt h p ↔ b = a) := by
  obtain ⟨a, ha⟩ := advancingEdge_exists hh hp hd
  refine ⟨a, ha, phaseDebt_advance hh hp ha, ?_⟩
  intro b
  constructor
  · intro hb
    have hb' := (phaseDebt_next_lt_iff hh hp b).mp hb
    apply Fin.ext
    simpa only [Option.some.injEq] using hb'.symm.trans ha
  · intro hb
    subst b
    exact (phaseDebt_next_lt_iff hh hp a).mpr ha

/-! ## Variable-length systems and sigma-indexed sums -/

abbrev Edge {m : Nat} (len : Fin m → Nat) :=
  Σ g : Fin m, Fin (len g)

def totalLen {m : Nat} (len : Fin m → Nat) : Nat :=
  sumOfFn len

def Valid {m : Nat} (len : Fin m → Nat) (P : Fin m → Phase) : Prop :=
  ∀ g, PhaseValid (len g) (P g)

def step {m : Nat} (len : Fin m → Nat)
    (P : Fin m → Phase) (e : Edge len) (g : Fin m) : Phase :=
  if g = e.1 then nextPhase (len e.1) (P e.1) e.2.val else P g

def D {m : Nat} (len : Fin m → Nat) (P : Fin m → Phase) : Nat :=
  sumOfFn (fun g => phaseDebt (len g) (P g))

/-- Each pair (g,a) occurs once: the inner sum ranges over Fin (len g). -/
def edgeSum {m : Nat} (len : Fin m → Nat) (f : Edge len → Nat) : Nat :=
  sumOfFn (fun g => sumOfFn (fun a : Fin (len g) => f ⟨g, a⟩))

theorem edgeSum_congr {m : Nat} (len : Fin m → Nat)
    (f g : Edge len → Nat) (hfg : ∀ e, f e = g e) :
    edgeSum len f = edgeSum len g := by
  unfold edgeSum
  apply sum_ofFn_eq
  intro i
  apply sum_ofFn_eq
  intro a
  exact hfg ⟨i, a⟩

theorem edgeSum_const {m : Nat} (len : Fin m → Nat) (c : Nat) :
    edgeSum len (fun _ => c) = totalLen len * c := by
  unfold edgeSum totalLen
  calc
    _ = sumOfFn (fun g => len g * c) := by
      apply sum_ofFn_eq
      intro g
      exact sum_ofFn_const (len g) c
    _ = sumOfFn len * c := sum_ofFn_mul len c

theorem edgeSum_le {m : Nat} (len : Fin m → Nat)
    (f g : Edge len → Nat) (hfg : ∀ e, f e ≤ g e) :
    edgeSum len f ≤ edgeSum len g := by
  unfold edgeSum
  apply sum_ofFn_le
  intro i
  apply sum_ofFn_le
  intro a
  exact hfg ⟨i, a⟩

theorem edgeSum_lt {m : Nat} (len : Fin m → Nat)
    (f g : Edge len → Nat) (e : Edge len)
    (hle : ∀ a, f a ≤ g a) (hlt : f e < g e) :
    edgeSum len f < edgeSum len g := by
  unfold edgeSum
  apply sum_ofFn_lt_of_single_lt _ _ e.1
  · intro i
    apply sum_ofFn_le
    intro a
    exact hle ⟨i, a⟩
  · apply sum_ofFn_lt_of_single_lt _ _ e.2
    · intro a
      exact hle ⟨e.1, a⟩
    · exact hlt

theorem valid_start {m : Nat} (len : Fin m → Nat) :
    Valid len (fun _ => .prelaunch) := by
  intro g
  exact True.intro

theorem step_valid {m : Nat} (len : Fin m → Nat)
    (hlen : ∀ g, 1 ≤ len g) (P : Fin m → Phase)
    (hP : Valid len P) (e : Edge len) : Valid len (step len P e) := by
  intro g
  by_cases hg : g = e.1
  · subst g
    simpa [step] using nextPhase_valid (hlen e.1) (hP e.1) e.2.val
  · simpa [step, hg] using hP g

/-- No validity assumption is needed for non-increase. -/
theorem D_step_le {m : Nat} (len : Fin m → Nat)
    (P : Fin m → Phase) (e : Edge len) :
    D len (step len P e) ≤ D len P := by
  unfold D
  apply sum_ofFn_le
  intro g
  by_cases hg : g = e.1
  · subst g
    simpa [step] using phaseDebt_next_le (len e.1) (P e.1) e.2.val
  · simp [step, hg]

/-- The corrected progress theorem: validity supplies the legal useful edge. -/
theorem D_useful_lt {m : Nat} (len : Fin m → Nat)
    (hlen : ∀ g, 1 ≤ len g) (P : Fin m → Phase)
    (hP : Valid len P) (hD : 0 < D len P) :
    ∃ e : Edge len, D len (step len P e) + 1 = D len P := by
  obtain ⟨g, hg⟩ := sum_ofFn_pos_exists
    (fun g : Fin m => phaseDebt (len g) (P g)) hD
  obtain ⟨a, ha⟩ := advancingEdge_exists (hlen g) (hP g) hg
  refine ⟨⟨g, a⟩, ?_⟩
  unfold D
  apply sum_ofFn_drop_one
    (fun i => phaseDebt (len i) (step len P ⟨g, a⟩ i))
    (fun i => phaseDebt (len i) (P i)) g
  · simpa [step] using phaseDebt_advance (hlen g) (hP g) ha
  · intro i hi
    simp [step, hi]

/-- The version without the extra unit is valid even at zero debt. -/
theorem D_childSum_le {m : Nat} (len : Fin m → Nat)
    (P : Fin m → Phase) :
    edgeSum len (fun e => D len (step len P e)) ≤ totalLen len * D len P := by
  calc
    _ ≤ edgeSum len (fun _ => D len P) :=
      edgeSum_le len _ _ (fun e => D_step_le len P e)
    _ = totalLen len * D len P := edgeSum_const len (D len P)

/-- The extra unit is justified only for a valid state with positive debt. -/
theorem D_childSum {m : Nat} (len : Fin m → Nat)
    (hlen : ∀ g, 1 ≤ len g) (P : Fin m → Phase)
    (hP : Valid len P) (hD : 0 < D len P) :
    1 + edgeSum len (fun e => D len (step len P e)) ≤
      totalLen len * D len P := by
  obtain ⟨e, he⟩ := D_useful_lt len hlen P hP hD
  have hs := edgeSum_lt len
    (fun a => D len (step len P a)) (fun _ => D len P) e
    (fun a => D_step_le len P a) (by omega)
  rw [edgeSum_const] at hs
  omega

/-- A stopped-cost formulation for every valid state, including zero debt. -/
theorem D_childSum_stopped {m : Nat} (len : Fin m → Nat)
    (hlen : ∀ g, 1 ≤ len g) (P : Fin m → Phase) (hP : Valid len P) :
    (if 0 < D len P then 1 else 0) +
        edgeSum len (fun e => D len (step len P e)) ≤
      totalLen len * D len P := by
  by_cases hD : 0 < D len P
  · simpa [hD] using D_childSum len hlen P hP hD
  · simpa [hD] using D_childSum_le len P

theorem D_start {m : Nat} (len : Fin m → Nat)
    (hlen : ∀ g, 1 ≤ len g) :
    D len (fun _ => .prelaunch) = 2 * totalLen len - m := by
  change sumOfFn (fun g : Fin m => 2 * len g - 1) = 2 * sumOfFn len - m
  have hs := sum_ofFn_twice_sub_one_add_card len hlen
  omega

/-! ## Exact transport from the sigma sum to Fin n -/

universe u v

/-- A self-contained equivalence record, with both inverse laws. -/
structure Equiv (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

local infix:25 " ≃ " => Equiv

theorem sum_ofFn_equiv_fiber {n : Nat} {α : Type u} [DecidableEq α]
    (e : Fin n ≃ α) (x : α) (c : Nat) :
    sumOfFn (fun i : Fin n => if e.toFun i = x then c else 0) = c := by
  calc
    _ = sumOfFn (fun i : Fin n => if i = e.invFun x then c else 0) := by
      apply sum_ofFn_eq
      intro i
      by_cases hi : i = e.invFun x
      · subst i
        simp [e.right_inv]
      · have hx : e.toFun i ≠ x := by
          intro he
          apply hi
          calc
            i = e.invFun (e.toFun i) := (e.left_inv i).symm
            _ = e.invFun x := congrArg e.invFun he
        simp [hi, hx]
    _ = c := sum_ofFn_single (e.invFun x) c

theorem edgeSum_single {m : Nat} (len : Fin m → Nat)
    (x : Edge len) (c : Nat) :
    edgeSum len (fun y => if y = x then c else 0) = c := by
  obtain ⟨g, a⟩ := x
  unfold edgeSum
  calc
    _ = sumOfFn (fun h : Fin m => if h = g then c else 0) := by
      apply sum_ofFn_eq
      intro h
      by_cases hh : h = g
      · subst h
        rw [if_pos rfl]
        calc
          _ = sumOfFn (fun b : Fin (len g) => if b = a then c else 0) := by
            apply sum_ofFn_eq
            intro b
            by_cases hb : b = a
            · subst b
              simp
            · have hs : (⟨g, b⟩ : Edge len) ≠ ⟨g, a⟩ := by
                intro he
                apply hb
                apply Fin.ext
                exact congrArg (fun z : Edge len => z.2.val) he
              simp [hb, hs]
          _ = c := sum_ofFn_single a c
      · have hs : ∀ b : Fin (len h), (⟨h, b⟩ : Edge len) ≠ ⟨g, a⟩ := by
          intro b he
          exact hh (congrArg (fun z : Edge len => z.1) he)
        calc
          _ = sumOfFn (fun _ : Fin (len h) => 0) := by
            apply sum_ofFn_eq
            intro b
            simp [hs b]
          _ = if h = g then c else 0 := by
            simp [hh, sum_ofFn_const]
    _ = c := sum_ofFn_single g c

theorem edgeSum_single_value {m : Nat} (len : Fin m → Nat)
    (x : Edge len) (f : Edge len → Nat) :
    edgeSum len (fun y => if y = x then f y else 0) = f x := by
  calc
    _ = edgeSum len (fun y => if y = x then f x else 0) := by
      apply edgeSum_congr
      intro y
      by_cases hy : y = x
      · subst y
        simp
      · simp [hy]
    _ = f x := edgeSum_single len x (f x)

theorem sum_ofFn_edgeSum_comm {m n : Nat} (len : Fin m → Nat)
    (f : Fin n → Edge len → Nat) :
    sumOfFn (fun i => edgeSum len (fun x => f i x)) =
      edgeSum len (fun x => sumOfFn (fun i => f i x)) := by
  unfold edgeSum
  calc
    _ = sumOfFn (fun g : Fin m =>
        sumOfFn (fun i : Fin n =>
          sumOfFn (fun a : Fin (len g) => f i ⟨g, a⟩))) :=
      sum_ofFn_comm (fun i g =>
        sumOfFn (fun a : Fin (len g) => f i ⟨g, a⟩))
    _ = _ := by
      apply sum_ofFn_eq
      intro g
      exact sum_ofFn_comm
        (fun (i : Fin n) (a : Fin (len g)) => f i ⟨g, a⟩)

/-- Exact equality of the two sums, not merely a reproof of the inequality. -/
theorem sum_ofFn_equiv_edgeSum {m n : Nat} (len : Fin m → Nat)
    (e : Fin n ≃ Edge len) (f : Edge len → Nat) :
    sumOfFn (fun i : Fin n => f (e.toFun i)) = edgeSum len f := by
  calc
    _ = sumOfFn (fun i : Fin n =>
        edgeSum len (fun x => if x = e.toFun i then f x else 0)) := by
      apply sum_ofFn_eq
      intro i
      exact (edgeSum_single_value len (e.toFun i) f).symm
    _ = edgeSum len (fun x =>
        sumOfFn (fun i : Fin n => if x = e.toFun i then f x else 0)) :=
      sum_ofFn_edgeSum_comm len
        (fun i x => if x = e.toFun i then f x else 0)
    _ = edgeSum len f := by
      apply edgeSum_congr
      intro x
      simpa only [eq_comm] using sum_ofFn_equiv_fiber e x (f x)

/-- A supplied equivalence also certifies the scheduler's edge count. -/
theorem equiv_card {m n : Nat} (len : Fin m → Nat)
    (e : Fin n ≃ Edge len) : n = totalLen len := by
  have hs := sum_ofFn_equiv_edgeSum len e (fun _ => 1)
  rw [sum_ofFn_const, edgeSum_const] at hs
  simpa using hs

/-- The requested literal Fin n / List.ofFn formulation. -/
theorem D_childSum_fin {m n : Nat} (len : Fin m → Nat)
    (hlen : ∀ g, 1 ≤ len g) (P : Fin m → Phase)
    (hP : Valid len P) (hD : 0 < D len P) (e : Fin n ≃ Edge len) :
    1 + (List.ofFn (fun i : Fin n =>
        D len (step len P (e.toFun i)))).sum ≤ n * D len P := by
  change 1 + sumOfFn (fun i : Fin n => D len (step len P (e.toFun i))) ≤
    n * D len P
  rw [sum_ofFn_equiv_edgeSum len e (fun a => D len (step len P a))]
  rw [equiv_card len e]
  exact D_childSum len hlen P hP hD

/-! ## Counterexamples to the two omitted hypotheses -/

def badLen : Fin 1 → Nat := fun _ => 2

def badState : Fin 1 → Phase := fun _ => .declAt 2

theorem badLen_pos : ∀ g : Fin 1, 1 ≤ badLen g := by
  intro g
  simp [badLen]

theorem badState_not_valid : ¬ Valid badLen badState := by
  intro h
  have hh := h (0 : Fin 1)
  change 0 < 2 ∧ 2 < 2 at hh
  omega

theorem bad_D : D badLen badState = 1 := by
  change sumOfFn (fun _ : Fin 1 => 1) = 1
  simpa using sum_ofFn_const 1 1

theorem bad_step (e : Edge badLen) : step badLen badState e = badState := by
  funext g
  have he : e.2.val < 2 := e.2.isLt
  have hne : e.2.val ≠ 2 := by omega
  simp [step, badLen, badState, nextPhase, hne]

theorem D_useful_lt_needs_valid :
    ¬ (0 < D badLen badState →
      ∃ e : Edge badLen,
        D badLen (step badLen badState e) + 1 = D badLen badState) := by
  intro h
  obtain ⟨e, he⟩ := h (by rw [bad_D]; omega)
  rw [bad_step, bad_D] at he
  omega

@[simp] theorem D_delivered {m : Nat} (len : Fin m → Nat) :
    D len (fun _ => .delivered) = 0 := by
  change sumOfFn (fun _ : Fin m => 0) = 0
  simpa using sum_ofFn_const m 0

@[simp] theorem step_delivered {m : Nat} (len : Fin m → Nat)
    (e : Edge len) :
    step len (fun _ => .delivered) e = (fun _ => .delivered) := by
  funext g
  simp [step, nextPhase]

/-- Even a well-formed all-delivered state refutes the unguarded extra unit. -/
theorem D_childSum_needs_positive {m : Nat} (len : Fin m → Nat) :
    ¬ (1 + edgeSum len (fun e =>
        D len (step len (fun _ => .delivered) e)) ≤
      totalLen len * D len (fun _ => .delivered)) := by
  simp [edgeSum_const]

end VariableGap

#print axioms VariableGap.D_useful_lt
#print axioms VariableGap.D_childSum
#print axioms VariableGap.D_childSum_fin
#print axioms VariableGap.D_start
