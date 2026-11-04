import Leader.L3.Top.PortPhase

/-!
For P.3.

The first-tail predicate's present-time purity does not by
itself state permanent future purity. This module gives a
strengthened class, proves the scalar budgets, and proves a
conditional finite-stage composition from the merged P.2.

The real FIFO/rearm count and adapted ledger are OPEN.
-/

namespace L3

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open Classical

set_option autoImplicit false
set_option Elab.async false

def topFreshTailExportAllowance (r : Nat) : Nat :=
  2 * r ^ 2 + 1

def topFreshTailContactAllowance (r : Nat) : Nat :=
  topFreshTailExportAllowance r * (r + 1) +
    2 * r * (r + 1)

/-- Multiplication reorder before the arithmetic decision step. -/
private theorem topFreshTailMulReorder
    (a b u v : Nat) :
    (a * u) * (b * v) = (a * b) * (u * v) := by
  calc
    (a * u) * (b * v) = a * (u * (b * v)) := by
      rw [Nat.mul_assoc]
    _ = a * (b * (u * v)) := by
      rw [Nat.mul_left_comm u b v]
    _ = (a * b) * (u * v) := by
      rw [Nat.mul_assoc]

private theorem topFreshTailSquareProduct (r : Nat) :
    r ^ 2 * r ^ 2 = r ^ 4 := by
  have hp := Nat.pow_add r 2 2
  change r ^ 4 = r ^ 2 * r ^ 2 at hp
  exact hp.symm

private theorem topFreshTailCubicProduct (r : Nat) :
    r ^ 2 * r = r ^ 3 := by
  have hp := Nat.pow_succ r 2
  change r ^ 3 = r ^ 2 * r at hp
  exact hp.symm

/-- Arithmetic only: old r^2+r operands plus the first tail. -/
theorem topFreshTailOperandArithmetic
    (r : Nat) (hr : 1 ≤ r) :
    r ^ 2 + r + 1 ≤ topFreshTailExportAllowance r := by
  have hlinear : r ≤ r ^ 2 := by
    calc
      r = r * 1 := by rw [Nat.mul_one]
      _ ≤ r * r := Nat.mul_le_mul_left r hr
      _ = r ^ 2 := by rw [Nat.pow_two]
  unfold topFreshTailExportAllowance
  omega

/-- Charged materialization/hop/buffer contacts, for r >= 3. -/
theorem topFreshTailContactAllowanceLe
    (r : Nat) (hr : 3 ≤ r) :
    topFreshTailContactAllowance r ≤ 8 * r ^ 3 := by
  have hpositive : 1 ≤ r := by omega
  have hsquare : 1 ≤ r ^ 2 := by
    have hp : 1 * 1 ≤ r * r :=
      Nat.mul_le_mul hpositive hpositive
    simpa only [Nat.one_mul, Nat.pow_two] using hp
  have hlinear : r + 1 ≤ 2 * r := by omega
  have hcoefficient : 2 * r ^ 2 + 1 ≤
      3 * r ^ 2 := by omega
  have hfirst :
      (2 * r ^ 2 + 1) * (r + 1) ≤
        6 * r ^ 3 := by
    calc
      (2 * r ^ 2 + 1) * (r + 1) ≤
          (3 * r ^ 2) * (2 * r) :=
        Nat.mul_le_mul hcoefficient hlinear
      _ = (3 * 2) * (r ^ 2 * r) :=
        topFreshTailMulReorder 3 2 (r ^ 2) r
      _ = 6 * r ^ 3 := by
        rw [topFreshTailCubicProduct]
  have hrr : r + 1 ≤ r * r := by
    calc
      r + 1 ≤ 2 * r := hlinear
      _ = r * 2 := Nat.mul_comm 2 r
      _ ≤ r * r :=
        Nat.mul_le_mul_left r (by omega : 2 ≤ r)
  have hsecond :
      2 * r * (r + 1) ≤ 2 * r ^ 3 := by
    calc
      2 * r * (r + 1) ≤ 2 * r * (r * r) :=
        Nat.mul_le_mul_left (2 * r) hrr
      _ = 2 * ((r * r) * r) := by
        simp only [Nat.mul_assoc]
      _ = 2 * r ^ 3 := by
        rw [← Nat.pow_two, topFreshTailCubicProduct]
  unfold topFreshTailContactAllowance
    topFreshTailExportAllowance
  omega

/-- Exactly F(r) = 6r^4+16r^3+7r^2+4r+2. -/
theorem topFreshTailPolynomial (r : Nat) :
    topClockF r =
      6 * r ^ 4 + 16 * r ^ 3 +
        7 * r ^ 2 + 4 * r + 2 := by
  have hfour :
      (2 * r ^ 2) * (3 * r ^ 2) =
        6 * r ^ 4 := by
    calc
      (2 * r ^ 2) * (3 * r ^ 2) =
          (2 * 3) * (r ^ 2 * r ^ 2) :=
        topFreshTailMulReorder 2 3 (r ^ 2) (r ^ 2)
      _ = 6 * r ^ 4 := by
        rw [topFreshTailSquareProduct]
  have hthree :
      (2 * r ^ 2) * (4 * r) = 8 * r ^ 3 := by
    calc
      (2 * r ^ 2) * (4 * r) =
          (2 * 4) * (r ^ 2 * r) :=
        topFreshTailMulReorder 2 4 (r ^ 2) r
      _ = 8 * r ^ 3 := by
        rw [topFreshTailCubicProduct]
  have htwo : (2 * r ^ 2) * 2 = 4 * r ^ 2 := by
    calc
      (2 * r ^ 2) * 2 = 2 * (r ^ 2 * 2) := by
        rw [Nat.mul_assoc]
      _ = 2 * (2 * r ^ 2) := by
        rw [Nat.mul_comm (r ^ 2) 2]
      _ = 4 * r ^ 2 := by
        rw [← Nat.mul_assoc]
  unfold topClockF topClockB
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul,
    hfour, hthree, htwo]
  omega

/-! ## Current receipt versus permanent source purity -/

/-- Unlike concretePureCohorts' finite recorded prefix, this
uses the same current accepted anchor for ALL continuations.
The FIFO induction needed to reach this cut is OPEN. -/
noncomputable def topFreshTailPermanentCut
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Prop :=
  topClockReached ring C Z ∧
  topClockGenuineTailAccepted C s Z ∧
  ∃ anchor : DigitExport (compileAdvice (ceilLogTwo n)) n,
    topClockConcreteTailAnchor s Z anchor ∧
    anchor.time = Z.1.2.clock ∧
    ∀ word : List (Fin n),
      topClockConcretePureStream s
        (topFixedTraceRun ring C (Z.2 ++ word)) anchor

theorem topFreshTailPermanentCutSpec
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (h : topFreshTailPermanentCut ring C s Z) :
    topClockReached ring C Z ∧
    topClockGenuineTailAccepted C s Z ∧
    topClockConcretePureCohorts s Z := by
  obtain ⟨hreach, hgenuine, anchor, hanchor, _, hfuture⟩ := h
  refine ⟨hreach, hgenuine, ⟨anchor, hanchor, ?_⟩⟩
  have hnow := hfuture []
  simp only [List.append_nil] at hnow
  rw [hreach]
  exact hnow

/-- Corrected cut-class field, leaving all later cuts unchanged.
Its eventual hitting time is NOT proved by this definition. -/
noncomputable def topFreshTailCorrectedClasses
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) :
    TopClockCutClasses ring C s :=
  { topClockConcreteCutClasses ring C s with
    firstTail := topFreshTailPermanentCut ring C s
    firstTailSpec := by
      intro Z h
      exact topFreshTailPermanentCutSpec ring C s Z h }

/-! ## First-hit monotonicity -/

private theorem topFreshTailCostTargetMonotone
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P Q : S → Prop)
    (hinclusion : ∀ x : S, P x → Q x) :
    ∀ (T : Nat) (x : S),
      costNumerator next Q x T ≤
        costNumerator next P x T := by
  intro T
  induction T with
  | zero =>
      intro x
      simp [costNumerator_zero]
  | succ T ih =>
      intro x
      by_cases hq : Q x
      · rw [costNumerator_terminal next Q x hq]
        exact Nat.zero_le _
      · have hp : ¬ P x := by
          intro h
          exact hq (hinclusion x h)
        rw [costNumerator_succ next Q x hq,
          costNumerator_succ next P x hp]
        exact Nat.add_le_add_left
          (ofFn_sum_le
            (fun e : Fin n =>
              costNumerator next Q (next x e) T)
            (fun e : Fin n =>
              costNumerator next P (next x e) T)
            (fun e => ih (next x e))) _

private theorem topFreshTailExpectedTargetMonotone
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P Q : S → Prop)
    (hn : 0 < n) (x : S) (budget : Nat)
    (hinclusion : ∀ y : S, P y → Q y)
    (h : UniformFirstHit.ExpectedHittingTimeAtMost
      next P x (budget : Rat)) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      next Q x (budget : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    next Q hn x budget).2
  have hcost :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      next P hn x budget).1 h
  intro T
  exact Nat.le_trans
    (topFreshTailCostTargetMonotone
      next P Q hinclusion T x) (hcost T)

private theorem topFreshTailExpectedBudgetMonotone
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop)
    (hn : 0 < n) (x : S) (a b : Nat)
    (h : UniformFirstHit.ExpectedHittingTimeAtMost
      next P x (a : Rat)) (hab : a ≤ b) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      next P x (b : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    next P hn x b).2
  have hcost :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      next P hn x a).1 h
  intro T
  exact Nat.le_trans (hcost T)
    (Nat.mul_le_mul_left (n ^ T) hab)

private theorem topFreshTailExpectedAtCut
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop)
    (hn : 0 < n) (x : S) (hp : P x) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      next P x (0 : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    next P hn x 0).2
  intro T
  rw [costNumerator_terminal next P x hp]
  simp

/-- The weighted number of completed adapted stages. -/
def topFreshTailStageBudget (price : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => topFreshTailStageBudget price j + price j

def topFreshTailExportServices (isExport : Nat → Bool) : Nat → Nat
  | 0 => 0
  | j + 1 =>
      topFreshTailExportServices isExport j +
        (if isExport j then 1 else 0)

def topFreshTailContactServices (isExport : Nat → Bool) : Nat → Nat
  | 0 => 0
  | j + 1 =>
      topFreshTailContactServices isExport j +
        (if isExport j then 0 else 1)

/-- Exact cost for any ordering of n*B export stages and
n-cost useful contact stages. No consecutive-edge requirement. -/
theorem topFreshTailStageBudgetCounts
    (isExport : Nat → Bool) (n b j : Nat) :
    topFreshTailStageBudget
        (fun i => if isExport i then n * b else n) j =
      n * (topFreshTailExportServices isExport j * b +
        topFreshTailContactServices isExport j) := by
  induction j with
  | zero =>
      simp [topFreshTailStageBudget, topFreshTailExportServices,
        topFreshTailContactServices]
  | succ j ih =>
      simp only [topFreshTailStageBudget, topFreshTailExportServices,
        topFreshTailContactServices, ih]
      cases isExport j with
      | false =>
          simp only [Bool.false_eq_true, if_false, Nat.add_zero,
            Nat.mul_add, Nat.mul_one]
          omega
      | true =>
          simp only [if_true, Nat.add_zero, Nat.add_mul, Nat.one_mul,
            Nat.mul_add]
          omega

/-- Iterated first-hit composition with its own adapted
predicate and price for each stage. -/
private theorem topFreshTailExpectedStagePrefix
    {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (layers : Nat → S → Prop) (price : Nat → Nat)
    (hn : 0 < n) (x : S)
    (hstart : layers 0 x) (limit : Nat)
    (hnext : ∀ j : Nat, j < limit →
      ∀ y : S, layers j y →
        UniformFirstHit.ExpectedHittingTimeAtMost
          next (layers (j + 1)) y (price j : Rat)) :
    ∀ j : Nat, j ≤ limit →
      UniformFirstHit.ExpectedHittingTimeAtMost
        next (layers j) x
        (topFreshTailStageBudget price j : Rat) := by
  intro j
  induction j with
  | zero =>
      intro _
      exact topFreshTailExpectedAtCut
        next (layers 0) hn x hstart
  | succ j ih =>
      intro hj
      have hprev : j ≤ limit := by omega
      have hthis : j < limit := by omega
      exact topClockExpectedSequential
        next (layers (j + 1)) (layers j)
        hn x (topFreshTailStageBudget price j)
        (price j) (ih hprev) (hnext j hthis)

/-! ## Actual-history count and missing source-row lemma -/

/-- Actual comparison source-port receipts with positive time. -/
noncomputable def topFreshTailPortReceiptCount
    {n : Nat} (s : Fin n)
    (Z : TopFixedTraceState n) : Nat :=
  (topClockConcreteExportsAfter s Z 0).length

/-- Needed from FIFO/border-rearm rows: every reached trace
before its first genuine border tail has <= 2r²+1 exports.
This is a Prop to prove, NOT a theorem. -/
noncomputable def TopFreshTailFIFOReceiptBound
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) : Prop :=
  ∀ Z : TopFixedTraceState n,
    topClockReached ring C Z →
    (∀ (pre suffix : List (Fin n)),
      pre ++ suffix = Z.2 → suffix ≠ [] →
      ¬ topClockGenuineTailAccepted C s
        (topFixedTraceRun ring C pre)) →
    topFreshTailPortReceiptCount s Z ≤
      topFreshTailExportAllowance (topClockSpan n)

/-- Actual adapted first-hit stages, interleaving ready exports
and useful source contacts in arbitrary order. The existence
of this ledger is the remaining physical FIFO/rearm producer.
No arbitrary scheduler contacts are charged as progress. -/
structure TopFreshTailAdaptedLedger
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (cuts : TopClockCutClasses ring C s) where
  steps : Nat
  isExport : Nat → Bool
  layers : Nat → TopFixedTraceState n → Prop
  initial :
    layers 0 ((C, digitAuditInitial (piD C)), [])
  terminal :
    layers steps = topClockStopOr ring C s cuts.firstTail
  absorbed :
    ∀ j : Nat, j ≤ steps → ∀ Z : TopFixedTraceState n,
      topClockStopOr ring C s cuts.firstTail Z → layers j Z
  exportBound :
    topFreshTailExportServices isExport steps ≤
      topFreshTailExportAllowance (topClockSpan n)
  contactBound :
    topFreshTailContactServices isExport steps ≤
      8 * topClockSpan n ^ 3
  exportReady :
    ∀ j : Nat, j < steps → isExport j = true →
      ∀ Z : TopFixedTraceState n, layers j Z →
        topClockStopOr ring C s cuts.firstTail Z ∨
        ∃ atom : Option (DigitAtom n),
          topClockReached ring C Z ∧
          topClockPortReady s atom Z ∧
          (∀ Y : TopFixedTraceState n,
            topClockStopOr ring C s
                (topClockPortAccepted s atom) Y →
              layers (j + 1) Y)
  contactProgress :
    ∀ j : Nat, j < steps → isExport j = false →
      ∀ Z : TopFixedTraceState n, layers j Z →
        UniformFirstHit.ExpectedHittingTimeAtMost
          (topFixedTraceNext ring C)
          (layers (j + 1)) Z (n : Rat)

/-- P.2 plus a genuinely ranked interleaved ledger closes
P.3 at EXACT n*F(r). The ledger is NOT constructed here. -/
theorem topFreshTailPhaseOfAdaptedLedger
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (cuts : TopClockCutClasses ring C s)
    (ledger : TopFreshTailAdaptedLedger ring C s cuts) :
    TopClockFreshTailPhase ring C s cuts := by
  have hn : 0 < n :=
    Nat.lt_of_le_of_lt (Nat.zero_le s.val) s.isLt
  have hport := topClockConcretePortPhase ring C s hbad
  have hstep :
      ∀ j : Nat, j < ledger.steps →
        ∀ Z : TopFixedTraceState n,
          ledger.layers j Z →
          UniformFirstHit.ExpectedHittingTimeAtMost
            (topFixedTraceNext ring C)
            (ledger.layers (j + 1)) Z
            ((if ledger.isExport j then
                n * topClockB (topClockSpan n)
              else n : Nat) : Rat) := by
    intro j hj Z hz
    cases hkind : ledger.isExport j with
    | false =>
        exact ledger.contactProgress j hj hkind Z hz
    | true =>
        rcases ledger.exportReady j hj hkind Z hz with
          hstop | ⟨atom, hreach, hready, hentry⟩
        · have hzero := topFreshTailExpectedAtCut
            (topFixedTraceNext ring C) (ledger.layers (j + 1))
            hn Z
            (ledger.absorbed (j + 1) (by omega) Z hstop)
          exact topFreshTailExpectedBudgetMonotone
            (topFixedTraceNext ring C) (ledger.layers (j + 1))
            hn Z 0 (n * topClockB (topClockSpan n))
            hzero (Nat.zero_le _)
        · exact topFreshTailExpectedTargetMonotone
            (topFixedTraceNext ring C)
            (topClockStopOr ring C s
              (topClockPortAccepted s atom))
            (ledger.layers (j + 1))
            hn Z (n * topClockB (topClockSpan n))
            hentry (hport atom Z hreach hready)
  have hfull :
      UniformFirstHit.ExpectedHittingTimeAtMost
        (topFixedTraceNext ring C)
        (ledger.layers ledger.steps)
        ((C, digitAuditInitial (piD C)), [])
        (topFreshTailStageBudget
          (fun j => if ledger.isExport j then
            n * topClockB (topClockSpan n) else n)
          ledger.steps : Rat) :=
    topFreshTailExpectedStagePrefix
      (topFixedTraceNext ring C)
      ledger.layers
      (fun j => if ledger.isExport j then
        n * topClockB (topClockSpan n) else n)
      hn ((C, digitAuditInitial (piD C)), [])
      ledger.initial ledger.steps hstep
      ledger.steps (Nat.le_refl _)
  have hcharges :
      topFreshTailExportServices
          ledger.isExport ledger.steps *
          topClockB (topClockSpan n) +
        topFreshTailContactServices
          ledger.isExport ledger.steps ≤
      topClockF (topClockSpan n) := by
    change
      topFreshTailExportServices
          ledger.isExport ledger.steps *
          topClockB (topClockSpan n) +
        topFreshTailContactServices
          ledger.isExport ledger.steps ≤
      topFreshTailExportAllowance (topClockSpan n) *
        topClockB (topClockSpan n) +
        8 * topClockSpan n ^ 3
    exact Nat.add_le_add
      (Nat.mul_le_mul_right
        (topClockB (topClockSpan n)) ledger.exportBound)
      ledger.contactBound
  have hbudget :
      topFreshTailStageBudget
          (fun j => if ledger.isExport j then
            n * topClockB (topClockSpan n) else n)
          ledger.steps ≤
        n * topClockF (topClockSpan n) := by
    rw [topFreshTailStageBudgetCounts]
    exact Nat.mul_le_mul_left n hcharges
  have hfinal := topFreshTailExpectedBudgetMonotone
    (topFixedTraceNext ring C)
    (ledger.layers ledger.steps)
    hn ((C, digitAuditInitial (piD C)), [])
    (topFreshTailStageBudget
      (fun j => if ledger.isExport j then
        n * topClockB (topClockSpan n) else n)
      ledger.steps)
    (n * topClockF (topClockSpan n)) hfull hbudget
  rw [ledger.terminal] at hfinal
  exact hfinal

end L3

#print axioms L3.topFreshTailOperandArithmetic
#print axioms L3.topFreshTailContactAllowanceLe
#print axioms L3.topFreshTailPolynomial
#print axioms L3.topFreshTailPermanentCutSpec
#print axioms L3.topFreshTailStageBudgetCounts
#print axioms L3.topFreshTailPhaseOfAdaptedLedger
