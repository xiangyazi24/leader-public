import Std.Tactic

/-!
# Weighted merge-span accounting

The existing priority merge theorem counts deleted boundaries.  Physical
request, receipt, pivot, and cleanup traversals are instead charged by the
number of groups or agents in the two incident gaps and the victim block.

`WeightedMergeTree` decorates every initial gap leaf and every deleted leader
node with an arbitrary natural mass.  A merge charges the whole mass of its
new interval.  The total charge is at most final mass times tree height.

This is the deterministic accounting kernel needed by
`PriorityLeaseContraction`.  A later physical refinement must prove that its
decorated leaves/nodes form a disjoint partition of at most `n` agents and that
one carrier attempt costs a constant times the corresponding interval mass
times `h`.
-/

inductive WeightedMergeTree where
  | leaf (weight : Nat)
  | node (left : WeightedMergeTree) (ownWeight : Nat)
      (right : WeightedMergeTree)
  deriving DecidableEq, Repr

namespace WeightedMergeTree

/-- Maximum number of charged merge nodes on a root-to-leaf path. -/
def height : WeightedMergeTree -> Nat
  | .leaf _ => 0
  | .node left _ right => max (height left) (height right) + 1

/-- Total physical mass represented by the interval. -/
def mass : WeightedMergeTree -> Nat
  | .leaf weight => weight
  | .node left ownWeight right => mass left + ownWeight + mass right

/-- Sum of the full interval mass charged at every successful merge. -/
def accumulatedSpan : WeightedMergeTree -> Nat
  | .leaf _ => 0
  | .node left ownWeight right =>
      accumulatedSpan left + accumulatedSpan right +
        (mass left + ownWeight + mass right)

/-- Every mass atom is charged by at most the number of ancestors above it. -/
theorem accumulatedSpan_le_mass_mul_height (tree : WeightedMergeTree) :
    accumulatedSpan tree <= mass tree * height tree := by
  induction tree with
  | leaf weight => simp [accumulatedSpan, mass, height]
  | node left ownWeight right left_ih right_ih =>
      let commonHeight := max left.height right.height
      have left_height : left.height <= commonHeight :=
        Nat.le_max_left _ _
      have right_height : right.height <= commonHeight :=
        Nat.le_max_right _ _
      have left_work : left.accumulatedSpan <=
          left.mass * commonHeight :=
        Nat.le_trans left_ih (Nat.mul_le_mul_left left.mass left_height)
      have right_work : right.accumulatedSpan <=
          right.mass * commonHeight :=
        Nat.le_trans right_ih (Nat.mul_le_mul_left right.mass right_height)
      simp only [accumulatedSpan, mass, height]
      change left.accumulatedSpan + right.accumulatedSpan +
          (left.mass + ownWeight + right.mass) <=
        (left.mass + ownWeight + right.mass) * (commonHeight + 1)
      calc
        left.accumulatedSpan + right.accumulatedSpan +
            (left.mass + ownWeight + right.mass) <=
          left.mass * commonHeight + right.mass * commonHeight +
            (left.mass + ownWeight + right.mass) := by omega
        _ <= (left.mass + ownWeight + right.mass) *
            (commonHeight + 1) := by
          simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
          omega

/-- A final physical partition of mass at most `n` and height at most `H`
immediately gives the `n*H` successful-span budget. -/
theorem accumulatedSpan_le_ring_budget
    {tree : WeightedMergeTree} {n H : Nat}
    (mass_le : tree.mass <= n)
    (height_le : tree.height <= H) :
    tree.accumulatedSpan <= n * H := by
  exact Nat.le_trans (accumulatedSpan_le_mass_mul_height tree)
    (Nat.mul_le_mul mass_le height_le)

/-- In one contention layer, every active gap can occur in the weights of its
two endpoint actors and every active victim block occurs once.  If those gap
and victim masses are a subpartition of the ring, total attempted actor mass
is at most `2*n`. -/
def activeRoundMass (gapMass victimMass : Nat) : Nat :=
  2 * gapMass + victimMass

theorem activeRoundMass_le_two_mul_ring
    {gapMass victimMass n : Nat}
    (subpartition : gapMass + victimMass <= n) :
    activeRoundMass gapMass victimMass <= 2 * n := by
  simp only [activeRoundMass]
  omega

end WeightedMergeTree

#print axioms WeightedMergeTree.accumulatedSpan_le_mass_mul_height
#print axioms WeightedMergeTree.accumulatedSpan_le_ring_budget
#print axioms WeightedMergeTree.activeRoundMass_le_two_mul_ring
