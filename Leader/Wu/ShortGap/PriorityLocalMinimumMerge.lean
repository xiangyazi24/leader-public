import Leader.Wu.ShortGap.PriorityHeapRecords
import Leader.Wu.ShortGap.SegmentPeakMerge

/-!
# Local-minimum deletion produces a heap-ordered peak merge tree

For two currently adjacent live leaders, a `PriorityGap` stores the merge tree
of boundaries already deleted between them.  Its invariant says that every
deleted priority is at most both live boundary priorities.  Empty initial gaps
have the invariant trivially.

When a live victim is no greater than its two current live neighbours, the two
incident gaps can be joined at that victim.  The new tree is heap ordered and
again bounded by both surviving leaders.  Thus any sequential linearization of
such commits, including arbitrary tie order, produces exactly the heap shape
consumed by `PriorityHeapRecords`.

The last section forgets random priorities and evaluates the same tree shape
with the strict dominating-pivot merge from `SegmentPeakMerge`.  Its peak rank
is exactly the tree height.  No physical comparison, reservation, receipt, or
cleanup transition is asserted here.
-/

namespace PriorityMergeTree

/-- A gap between live boundary priorities.  Every deleted boundary stored in
the gap is bounded by each still-live endpoint. -/
structure PriorityGap (leftBoundary rightBoundary : Nat) where
  tree : PriorityMergeTree
  heap : tree.HeapOrdered
  leftBound : tree.AllLE leftBoundary
  rightBound : tree.AllLE rightBoundary

namespace PriorityGap

/-- Before any deletion, the interval between consecutive live leaders has no
deleted-boundary tree. -/
def empty (leftBoundary rightBoundary : Nat) :
    PriorityGap leftBoundary rightBoundary where
  tree := .empty
  heap := trivial
  leftBound := by simp [AllLE, inorder]
  rightBound := by simp [AllLE, inorder]

private theorem node_allLE
    {left right : PriorityMergeTree} {pivot bound : Nat}
    (left_le : left.AllLE bound)
    (pivot_le : pivot <= bound)
    (right_le : right.AllLE bound) :
    (PriorityMergeTree.node left pivot right).AllLE bound := by
  intro value hvalue
  simp only [inorder] at hvalue ⊢
  simp only [List.mem_append, List.mem_cons] at hvalue
  rcases hvalue with in_left | is_pivot | in_right
  · exact left_le value in_left
  · simpa [is_pivot] using pivot_le
  · exact right_le value in_right

/-- One accepted deletion step.  `victim_le_left/right` are exactly the
semantic local-minimum guard evaluated against the two current live
neighbours. -/
def deleteLocalMinimum
    {leftBoundary victim rightBoundary : Nat}
    (leftGap : PriorityGap leftBoundary victim)
    (rightGap : PriorityGap victim rightBoundary)
    (victim_le_left : victim <= leftBoundary)
    (victim_le_right : victim <= rightBoundary) :
    PriorityGap leftBoundary rightBoundary where
  tree := .node leftGap.tree victim rightGap.tree
  heap := by
    exact ⟨leftGap.heap, rightGap.heap, leftGap.rightBound,
      rightGap.leftBound⟩
  leftBound := by
    apply node_allLE leftGap.leftBound victim_le_left
    intro value hvalue
    exact Nat.le_trans (rightGap.leftBound value hvalue) victim_le_left
  rightBound := by
    apply node_allLE
    · intro value hvalue
      exact Nat.le_trans (leftGap.rightBound value hvalue) victim_le_right
    · exact victim_le_right
    · exact rightGap.rightBound

theorem deleteLocalMinimum_heap
    {leftBoundary victim rightBoundary : Nat}
    (leftGap : PriorityGap leftBoundary victim)
    (rightGap : PriorityGap victim rightBoundary)
    (victim_le_left : victim <= leftBoundary)
    (victim_le_right : victim <= rightBoundary) :
    (deleteLocalMinimum leftGap rightGap victim_le_left victim_le_right).tree.HeapOrdered :=
  (deleteLocalMinimum leftGap rightGap victim_le_left victim_le_right).heap

theorem deleteLocalMinimum_inorder
    {leftBoundary victim rightBoundary : Nat}
    (leftGap : PriorityGap leftBoundary victim)
    (rightGap : PriorityGap victim rightBoundary)
    (victim_le_left : victim <= leftBoundary)
    (victim_le_right : victim <= rightBoundary) :
    (deleteLocalMinimum leftGap rightGap victim_le_left victim_le_right).tree.inorder =
      leftGap.tree.inorder ++ victim :: rightGap.tree.inorder := rfl

theorem deleteLocalMinimum_height
    {leftBoundary victim rightBoundary : Nat}
    (leftGap : PriorityGap leftBoundary victim)
    (rightGap : PriorityGap victim rightBoundary)
    (victim_le_left : victim <= leftBoundary)
    (victim_le_right : victim <= rightBoundary) :
    (deleteLocalMinimum leftGap rightGap victim_le_left victim_le_right).tree.height =
      max leftGap.tree.height rightGap.tree.height + 1 := rfl

end PriorityGap

/-- Evaluate a priority merge-tree shape using the independent peak-label
merge algebra.  Priorities choose the shape; peak pivots remain the strict
`max child cap` values required for comparison suppression. -/
def toRankedPeakSegment : PriorityMergeTree -> RankedPeakSegment
  | .empty => .empty
  | .node left _ right =>
      RankedPeakSegment.merge (toRankedPeakSegment left)
        (toRankedPeakSegment right)

/-- The distributed peak rank required by a deletion history is exactly the
height of its priority heap tree. -/
theorem toRankedPeakSegment_cap (tree : PriorityMergeTree) :
    tree.toRankedPeakSegment.cap = tree.height := by
  induction tree with
  | empty => rfl
  | node left priority right left_ih right_ih =>
      simp only [toRankedPeakSegment, RankedPeakSegment.merge_cap, height,
        left_ih, right_ih]

theorem toRankedPeakSegment_safe (tree : PriorityMergeTree) :
    SegmentPeakWord tree.toRankedPeakSegment.word :=
  tree.toRankedPeakSegment.safe

/-- Number of deleted boundaries represented by a merge tree. -/
def nodeCount : PriorityMergeTree -> Nat
  | .empty => 0
  | .node left _ right => nodeCount left + nodeCount right + 1

/-- Sum of the current interval sizes charged at all merge nodes.  This is the
unweighted core of the comparison/pivot traversal accounting; initial follower
groups can be added as leaf weights by the same depth argument. -/
def accumulatedMergeSpan : PriorityMergeTree -> Nat
  | .empty => 0
  | .node left _ right =>
      accumulatedMergeSpan left + accumulatedMergeSpan right +
        (nodeCount left + nodeCount right + 1)

/-- Every deleted boundary participates in at most one charged interval per
ancestor.  Hence total charged span is bounded by node count times tree
height. -/
theorem accumulatedMergeSpan_le_count_mul_height
    (tree : PriorityMergeTree) :
    tree.accumulatedMergeSpan <= tree.nodeCount * tree.height := by
  induction tree with
  | empty => simp [accumulatedMergeSpan, nodeCount, height]
  | node left priority right left_ih right_ih =>
      let commonHeight := max left.height right.height
      have left_height : left.height <= commonHeight :=
        Nat.le_max_left _ _
      have right_height : right.height <= commonHeight :=
        Nat.le_max_right _ _
      have left_work : left.accumulatedMergeSpan <=
          left.nodeCount * commonHeight :=
        Nat.le_trans left_ih (Nat.mul_le_mul_left left.nodeCount left_height)
      have right_work : right.accumulatedMergeSpan <=
          right.nodeCount * commonHeight :=
        Nat.le_trans right_ih (Nat.mul_le_mul_left right.nodeCount right_height)
      simp only [accumulatedMergeSpan, nodeCount, height]
      change left.accumulatedMergeSpan + right.accumulatedMergeSpan +
          (left.nodeCount + right.nodeCount + 1) <=
        (left.nodeCount + right.nodeCount + 1) * (commonHeight + 1)
      calc
        left.accumulatedMergeSpan + right.accumulatedMergeSpan +
            (left.nodeCount + right.nodeCount + 1) <=
          left.nodeCount * commonHeight + right.nodeCount * commonHeight +
            (left.nodeCount + right.nodeCount + 1) := by omega
        _ <= (left.nodeCount + right.nodeCount + 1) *
            (commonHeight + 1) := by
          simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
          omega

end PriorityMergeTree

#print axioms PriorityMergeTree.PriorityGap.deleteLocalMinimum_heap
#print axioms PriorityMergeTree.PriorityGap.deleteLocalMinimum_inorder
#print axioms PriorityMergeTree.toRankedPeakSegment_cap
#print axioms PriorityMergeTree.toRankedPeakSegment_safe
#print axioms PriorityMergeTree.accumulatedMergeSpan_le_count_mul_height
