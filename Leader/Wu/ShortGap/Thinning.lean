import Std.Tactic

/-!
# Accounting kernel for short-gap thinning

Before geometric-priority sampling, densely spaced leaders may be thinned by
one-sided capture transactions.  A successful transaction crosses a clockwise
gap of length strictly below `h`, deletes the leader at its far endpoint, and
merges that short gap with the endpoint's next gap.

The cyclic list may be reanchored after every deletion.  Accordingly
`MergeStep` is an accounting quotient: it remembers the two merged masses but
forgets their cyclic anchor.  Every literal adjacent cyclic merge has this
shape; the converse is neither asserted nor used.

The theorems prove the deterministic part of the complexity reduction:

* every success preserves total ring mass and removes exactly one gap/leader;
* the total length charged by any success trace is at most `h` times the
  initial leader count; and
* an `h`-separated terminal partition has at most `n / h` leaders.

This file does not prove that a capture succeeds.  The provisional receipt,
preemption, final-grant, target-local leader clear, release, and arbitrary-ring
nonmasking theorem remain the physical `SparseRootEntry` obligation.
-/

namespace ShortGapThinning

/-- One successful short-gap deletion, modulo reanchoring of the cyclic gap
list.  `charge` is the physical length of the captured clockwise gap. -/
structure MergeStep
    (h : Nat) (before : List Nat) (charge : Nat) (after : List Nat) where
  shortGap : Nat
  nextGap : Nat
  rest : List Nat
  before_perm : before.Perm (shortGap :: nextGap :: rest)
  after_perm : after.Perm ((shortGap + nextGap) :: rest)
  charge_eq : charge = shortGap
  short_lt : shortGap < h

theorem MergeStep.charge_lt
    {h before charge after} (step : MergeStep h before charge after) :
    charge < h := by
  rw [step.charge_eq]
  exact step.short_lt

theorem MergeStep.mass_preserved
    {h before charge after} (step : MergeStep h before charge after) :
    before.sum = after.sum := by
  calc
    before.sum = (step.shortGap :: step.nextGap :: step.rest).sum :=
      step.before_perm.sum_nat
    _ = ((step.shortGap + step.nextGap) :: step.rest).sum := by
      simp only [List.sum_cons]
      omega
    _ = after.sum := step.after_perm.sum_nat.symm

theorem MergeStep.length_drop
    {h before charge after} (step : MergeStep h before charge after) :
    after.length + 1 = before.length := by
  have before_length := step.before_perm.length_eq
  have after_length := step.after_perm.length_eq
  simp only [List.length_cons] at before_length after_length
  omega

/-- The directly reanchored physical case: the short gap is listed first and
its clockwise neighbour second. -/
def headMergeStep
    (h shortGap nextGap : Nat) (rest : List Nat)
    (short_lt : shortGap < h) :
    MergeStep h (shortGap :: nextGap :: rest) shortGap
      ((shortGap + nextGap) :: rest) := by
  exact
    { shortGap := shortGap
      nextGap := nextGap
      rest := rest
      before_perm := .refl _
      after_perm := .refl _
      charge_eq := rfl
      short_lt := short_lt }

/-- A finite sequence of successful short-gap deletions. -/
inductive MergeTrace (h : Nat) : List Nat -> Nat -> List Nat -> Prop where
  | refl (gaps : List Nat) : MergeTrace h gaps 0 gaps
  | cons {before middle after charge tailCharge}
      (head : MergeStep h before charge middle)
      (tail : MergeTrace h middle tailCharge after) :
      MergeTrace h before (charge + tailCharge) after

theorem MergeTrace.mass_preserved
    {h before charge after} (trace : MergeTrace h before charge after) :
    before.sum = after.sum := by
  induction trace with
  | refl => rfl
  | cons head _ ih => exact head.mass_preserved.trans ih

theorem MergeTrace.length_nonincreasing
    {h before charge after} (trace : MergeTrace h before charge after) :
    after.length <= before.length := by
  induction trace with
  | refl => exact Nat.le_refl _
  | cons head _ ih =>
      have head_le : _ := head.length_drop
      exact Nat.le_trans ih (by omega)

/-- If the physical compiler resolves one initial choice per leader and
rearms at most the two roots adjacent to each committed deletion, this is its
deterministic nonretry choice-service budget.  The number of commits is the
observed leader-count drop. -/
def localChoiceRearmBudget (before after : List Nat) : Nat :=
  before.length + 2 * (before.length - after.length)

/-- Local rearming costs at most three times the initial leader count.  This
is the accounting reason a topology-changing commit must not trigger a global
choice refresh. -/
theorem MergeTrace.localChoiceRearmBudget_le_three_initial
    {h before charge after} (trace : MergeTrace h before charge after) :
    localChoiceRearmBudget before after <= 3 * before.length := by
  have hlength := trace.length_nonincreasing
  simp only [localChoiceRearmBudget]
  omega

/-- Each success costs less than `h`, and every success removes one list
entry.  Thus even an adversarial successful deletion order has total captured
gap length at most `h` times the initial leader count. -/
theorem MergeTrace.charge_le_height_mul_initial_count
    {h before charge after} (trace : MergeTrace h before charge after) :
    charge <= h * before.length := by
  induction trace with
  | refl => simp
  | @cons before middle after headCharge tailCharge head tail ih =>
      have head_le : headCharge <= h := Nat.le_of_lt head.charge_lt
      calc
        headCharge + tailCharge <= h + h * middle.length :=
          Nat.add_le_add head_le ih
        _ = h * middle.length + h := Nat.add_comm _ _
        _ = h * (middle.length + 1) := by
          simp only [Nat.mul_add, Nat.mul_one]
        _ = h * before.length := by rw [head.length_drop]

/-- Generic physical accounting for a clean committed lifecycle using at most
`tripFactor` complete gap crossings and `overhead` local services per deleted
leader. -/
def linearCarrierCost (tripFactor overhead charge commits : Nat) : Nat :=
  tripFactor * charge + overhead * commits

/-- Any constant-trip implementation of the successful capture macro remains
within the sparse-entry `O(h * initialLeaders)` service envelope. -/
theorem MergeTrace.linearCarrierCost_le
    {h before charge after} (trace : MergeTrace h before charge after)
    (tripFactor overhead : Nat) :
    linearCarrierCost tripFactor overhead charge
        (before.length - after.length) <=
      (tripFactor * h + overhead) * before.length := by
  have crossing := Nat.mul_le_mul_left tripFactor
    trace.charge_le_height_mul_initial_count
  have commits : before.length - after.length <= before.length :=
    Nat.sub_le _ _
  have localCost := Nat.mul_le_mul_left overhead commits
  calc
    linearCarrierCost tripFactor overhead charge
        (before.length - after.length) =
        tripFactor * charge + overhead * (before.length - after.length) := rfl
    _ <= tripFactor * (h * before.length) + overhead * before.length :=
      Nat.add_le_add crossing localCost
    _ = (tripFactor * h + overhead) * before.length := by
      simp only [Nat.add_mul, Nat.mul_assoc]

/-- Specialization to the clean protected lifecycle: proposal, FINAL return,
commit, and committed-receipt return. -/
theorem MergeTrace.fourCrossingCarrierCost_le
    {h before charge after} (trace : MergeTrace h before charge after)
    (overhead : Nat) :
    linearCarrierCost 4 overhead charge
        (before.length - after.length) <=
      (4 * h + overhead) * before.length :=
  trace.linearCarrierCost_le 4 overhead

def Separated (h : Nat) (gaps : List Nat) : Prop :=
  forall gap, gap ∈ gaps -> h <= gap

/-- Disjoint `h`-cell root blocks fit inside the conserved ring mass once all
cyclic gaps are at least `h`. -/
theorem separated_mul_count_le_mass
    {h : Nat} {gaps : List Nat} (separated : Separated h gaps) :
    h * gaps.length <= gaps.sum := by
  induction gaps with
  | nil => simp
  | cons gap rest ih =>
      have gap_ge : h <= gap := separated gap (by simp)
      have rest_separated : Separated h rest := by
        intro value member
        exact separated value (by simp [member])
      calc
        h * (gap :: rest).length = h * rest.length + h := by
          simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        _ <= rest.sum + gap := Nat.add_le_add (ih rest_separated) gap_ge
        _ = (gap :: rest).sum := by
          simp only [List.sum_cons]
          omega

theorem separated_mul_count_le_ring
    {h n : Nat} {gaps : List Nat}
    (separated : Separated h gaps) (mass : gaps.sum = n) :
    h * gaps.length <= n := by
  rw [<- mass]
  exact separated_mul_count_le_mass separated

theorem separated_or_has_short (h : Nat) (gaps : List Nat) :
    Separated h gaps \/ exists gap, gap ∈ gaps /\ gap < h := by
  induction gaps with
  | nil =>
      left
      intro gap member
      simp at member
  | cons first rest ih =>
      by_cases first_large : h <= first
      · rcases ih with rest_large | ⟨gap, member, short⟩
        · left
          intro gap member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact first_large
          · exact rest_large gap member
        · right
          exact ⟨gap, by simp [member], short⟩
      · right
        exact ⟨first, by simp, by omega⟩

end ShortGapThinning

#print axioms ShortGapThinning.MergeStep.mass_preserved
#print axioms ShortGapThinning.MergeStep.length_drop
#print axioms ShortGapThinning.MergeTrace.mass_preserved
#print axioms ShortGapThinning.MergeTrace.localChoiceRearmBudget_le_three_initial
#print axioms ShortGapThinning.MergeTrace.charge_le_height_mul_initial_count
#print axioms ShortGapThinning.MergeTrace.linearCarrierCost_le
#print axioms ShortGapThinning.MergeTrace.fourCrossingCarrierCost_le
#print axioms ShortGapThinning.separated_mul_count_le_ring
#print axioms ShortGapThinning.separated_or_has_short
