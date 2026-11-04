import Std.Tactic

/-!
# Heap paths are controlled by weak priority records

This file isolates the deterministic combinatorial kernel needed by the
asynchronous geometric-priority elimination candidate.  A completed sequence
of local-minimum boundary deletions should produce an inorder merge tree whose
parent priority is at least every priority in either child.  The theorem below
does not assume how equal priorities were scheduled.

For any node of such a heap-ordered tree, ancestors lying to its right are
weak records when the inorder suffix is scanned from the node.  Ancestors on
the left satisfy the symmetric statement after reversing the inorder prefix.
Consequently the node depth is bounded by the sum of two weak-record counts.

This is an abstract tree theorem only.  The physical protocol still has to
prove that accepted local-minimum commits linearize to a heap-ordered inorder
tree and that stale comparisons cannot authorize a deletion.
-/

inductive PriorityMergeTree where
  | empty : PriorityMergeTree
  | node (left : PriorityMergeTree) (priority : Nat)
      (right : PriorityMergeTree) : PriorityMergeTree
  deriving DecidableEq, Repr

namespace PriorityMergeTree

def inorder : PriorityMergeTree -> List Nat
  | .empty => []
  | .node left priority right => inorder left ++ priority :: inorder right

/-- Merge-tree height, with empty initial gaps at height zero. -/
def height : PriorityMergeTree -> Nat
  | .empty => 0
  | .node left _ right => max (height left) (height right) + 1

def AllLE (tree : PriorityMergeTree) (bound : Nat) : Prop :=
  forall value, value ∈ inorder tree -> value <= bound

def HeapOrdered : PriorityMergeTree -> Prop
  | .empty => True
  | .node left priority right =>
      HeapOrdered left ∧ HeapOrdered right ∧
      AllLE left priority ∧ AllLE right priority

/-- A path selects one internal node. -/
inductive NodePath : (tree : PriorityMergeTree) -> Type
  | root (left right : PriorityMergeTree) (priority : Nat) :
      NodePath (.node left priority right)
  | left {left right : PriorityMergeTree} {priority : Nat} :
      NodePath left -> NodePath (.node left priority right)
  | right {left right : PriorityMergeTree} {priority : Nat} :
      NodePath right -> NodePath (.node left priority right)

namespace NodePath

def target : {tree : PriorityMergeTree} -> NodePath tree -> Nat
  | _, .root _ _ priority => priority
  | _, .left path => target path
  | _, .right path => target path

/-- Inorder entries strictly before the selected node. -/
def before : {tree : PriorityMergeTree} -> NodePath tree -> List Nat
  | _, .root lhs _ _ => inorder lhs
  | _, .left path => before path
  | _, .right (left := lhs) (priority := priority) path =>
      inorder lhs ++ priority :: before path

/-- Inorder entries strictly after the selected node. -/
def after : {tree : PriorityMergeTree} -> NodePath tree -> List Nat
  | _, .root _ rhs _ => inorder rhs
  | _, .left (right := rhs) (priority := priority) path =>
      after path ++ priority :: inorder rhs
  | _, .right path => after path

/-- Number of ancestors whose inorder position is left of the target. -/
def leftAncestors : {tree : PriorityMergeTree} -> NodePath tree -> Nat
  | _, .root _ _ _ => 0
  | _, .left path => leftAncestors path
  | _, .right path => leftAncestors path + 1

/-- Number of ancestors whose inorder position is right of the target. -/
def rightAncestors : {tree : PriorityMergeTree} -> NodePath tree -> Nat
  | _, .root _ _ _ => 0
  | _, .left path => rightAncestors path + 1
  | _, .right path => rightAncestors path

def depth {tree : PriorityMergeTree} (path : NodePath tree) : Nat :=
  leftAncestors path + rightAncestors path

theorem inorder_decomposition
    {tree : PriorityMergeTree} (path : NodePath tree) :
    inorder tree = before path ++ target path :: after path := by
  induction path with
  | root left right priority =>
      simp [inorder, before, target, after]
  | @left left right priority path ih =>
      simp only [inorder, before, target, after]
      rw [ih]
      simp only [List.append_assoc, List.cons_append]
  | @right left right priority path ih =>
      simp only [inorder, before, target, after]
      rw [ih]
      simp only [List.append_assoc, List.cons_append]

theorem target_mem_inorder
    {tree : PriorityMergeTree} (path : NodePath tree) :
    target path ∈ inorder tree := by
  rw [inorder_decomposition path]
  simp

theorem before_subset_inorder
    {tree : PriorityMergeTree} (path : NodePath tree) :
    forall value, value ∈ before path -> value ∈ inorder tree := by
  intro value hvalue
  rw [inorder_decomposition path]
  simp [hvalue]

theorem after_subset_inorder
    {tree : PriorityMergeTree} (path : NodePath tree) :
    forall value, value ∈ after path -> value ∈ inorder tree := by
  intro value hvalue
  rw [inorder_decomposition path]
  simp [hvalue]

end NodePath

/-- Scan a word from a current maximum.  The second component counts entries
which weakly exceed the maximum seen so far; ties are deliberately counted. -/
def weakRecordScan : Nat -> List Nat -> Nat × Nat
  | current, [] => (current, 0)
  | current, value :: rest =>
      if current <= value then
        let result := weakRecordScan value rest
        (result.1, result.2 + 1)
      else
        weakRecordScan current rest

def weakRecordCount (current : Nat) (word : List Nat) : Nat :=
  (weakRecordScan current word).2

def weakRecordMaximum (current : Nat) (word : List Nat) : Nat :=
  (weakRecordScan current word).1

theorem weakRecordScan_append (current : Nat) (first second : List Nat) :
    weakRecordScan current (first ++ second) =
      let scanned := weakRecordScan current first
      let continued := weakRecordScan scanned.1 second
      (continued.1, scanned.2 + continued.2) := by
  induction first generalizing current with
  | nil => simp [weakRecordScan]
  | cons value rest ih =>
      simp only [List.cons_append, weakRecordScan]
      split
      · rename_i current_le
        simp only [ih]
        congr 1
        omega
      · exact ih current

theorem weakRecordMaximum_le_of_all_le
    {current bound : Nat} {word : List Nat}
    (current_le : current <= bound)
    (all_le : forall value, value ∈ word -> value <= bound) :
    weakRecordMaximum current word <= bound := by
  induction word generalizing current with
  | nil => simpa [weakRecordMaximum, weakRecordScan] using current_le
  | cons value rest ih =>
      have value_le : value <= bound := all_le value (by simp)
      have rest_le : forall x, x ∈ rest -> x <= bound := by
        intro x hx
        exact all_le x (by simp [hx])
      simp only [weakRecordMaximum, weakRecordScan]
      split
      · exact ih value_le rest_le
      · exact ih current_le rest_le

theorem weakRecordCount_append_ge (current : Nat) (first second : List Nat) :
    weakRecordCount current first <=
      weakRecordCount current (first ++ second) := by
  simp only [weakRecordCount, weakRecordScan_append]
  omega

/-- Raising the initial threshold can only remove weak records. -/
theorem weakRecordCount_anti_current
    {lower upper : Nat} (lower_le : lower <= upper) (word : List Nat) :
    weakRecordCount upper word <= weakRecordCount lower word := by
  induction word generalizing lower upper with
  | nil => simp [weakRecordCount, weakRecordScan]
  | cons value rest ih =>
      simp only [weakRecordCount, weakRecordScan]
      by_cases upper_le : upper <= value
      · have lower_value : lower <= value := Nat.le_trans lower_le upper_le
        simp only [if_pos upper_le, if_pos lower_value]
        exact Nat.le_refl _
      · by_cases lower_value : lower <= value
        · simp only [if_neg upper_le, if_pos lower_value]
          have value_le_upper : value <= upper := by omega
          have tail_bound : (weakRecordScan upper rest).2 <=
              (weakRecordScan value rest).2 := by
            simpa only [weakRecordCount] using ih value_le_upper
          omega
        · simp only [if_neg upper_le, if_neg lower_value]
          exact ih lower_le

/-- If `pivot` dominates the current maximum and an entire prefix, scanning
through that prefix and then the pivot gains at least one weak record. -/
theorem weakRecordCount_append_pivot_ge
    {current pivot : Nat} {head tail : List Nat}
    (current_le : current <= pivot)
    (head_le : forall value, value ∈ head -> value <= pivot) :
    weakRecordCount current head + 1 <=
      weakRecordCount current (head ++ pivot :: tail) := by
  rw [weakRecordCount, weakRecordCount, weakRecordScan_append]
  have maximum_le : weakRecordMaximum current head <= pivot :=
    weakRecordMaximum_le_of_all_le current_le head_le
  simp only [weakRecordMaximum] at maximum_le
  generalize hhead : weakRecordScan current head = headResult
  simp only [hhead] at maximum_le ⊢
  simp only [weakRecordScan]
  split
  · omega
  · omega

private theorem heap_left
    {left right : PriorityMergeTree} {priority : Nat}
    (heap : HeapOrdered (.node left priority right)) : HeapOrdered left :=
  heap.1

private theorem heap_right
    {left right : PriorityMergeTree} {priority : Nat}
    (heap : HeapOrdered (.node left priority right)) : HeapOrdered right :=
  heap.2.1

private theorem heap_left_le
    {left right : PriorityMergeTree} {priority : Nat}
    (heap : HeapOrdered (.node left priority right)) : AllLE left priority :=
  heap.2.2.1

private theorem heap_right_le
    {left right : PriorityMergeTree} {priority : Nat}
    (heap : HeapOrdered (.node left priority right)) : AllLE right priority :=
  heap.2.2.2

/-- Ancestors to the right of a selected node inject into the weak records of
the inorder suffix, uniformly over all equal-priority tie shapes. -/
theorem rightAncestors_le_weakRecords
    {tree : PriorityMergeTree} (heap : HeapOrdered tree)
    (path : NodePath tree) :
    path.rightAncestors <= weakRecordCount path.target path.after := by
  induction path with
  | root left right priority =>
      simp [NodePath.rightAncestors]
  | @left left right priority path ih =>
      have left_heap := heap_left heap
      have previous := ih left_heap
      have left_le := heap_left_le heap
      have target_le : path.target <= priority :=
        left_le path.target path.target_mem_inorder
      have after_le : forall value, value ∈ path.after -> value <= priority := by
        intro value hvalue
        exact left_le value (path.after_subset_inorder value hvalue)
      have gain := weakRecordCount_append_pivot_ge
        (current := path.target) (pivot := priority)
        (head := path.after) (tail := inorder right) target_le after_le
      simp only [NodePath.rightAncestors, NodePath.target, NodePath.after]
      omega
  | @right left right priority path ih =>
      have right_heap := heap_right heap
      simpa [NodePath.rightAncestors, NodePath.target, NodePath.after] using
        ih right_heap

/-- Ancestors to the left satisfy the symmetric weak-record bound after the
inorder prefix is reversed. -/
theorem leftAncestors_le_weakRecords
    {tree : PriorityMergeTree} (heap : HeapOrdered tree)
    (path : NodePath tree) :
    path.leftAncestors <=
      weakRecordCount path.target path.before.reverse := by
  induction path with
  | root left right priority =>
      simp [NodePath.leftAncestors]
  | @left left right priority path ih =>
      have left_heap := heap_left heap
      simpa [NodePath.leftAncestors, NodePath.target, NodePath.before] using
        ih left_heap
  | @right left right priority path ih =>
      have right_heap := heap_right heap
      have previous := ih right_heap
      have right_le := heap_right_le heap
      have target_le : path.target <= priority :=
        right_le path.target path.target_mem_inorder
      have before_le : forall value, value ∈ path.before.reverse ->
          value <= priority := by
        intro value hvalue
        have original_mem : value ∈ path.before := by
          simpa using hvalue
        exact right_le value (path.before_subset_inorder value original_mem)
      have gain := weakRecordCount_append_pivot_ge
        (current := path.target) (pivot := priority)
        (head := path.before.reverse) (tail := (inorder left).reverse)
        target_le before_le
      have normalized_gain :
          weakRecordCount path.target path.before.reverse + 1 <=
            weakRecordCount path.target
              (path.before.reverse ++ [priority] ++ (inorder left).reverse) := by
        simpa only [List.append_assoc, List.singleton_append] using gain
      simp only [NodePath.leftAncestors, NodePath.target, NodePath.before,
        List.reverse_append, List.reverse_cons]
      omega

/-- The full deterministic depth bound.  This is the tie-robust replacement
for importing a Cartesian-tree theorem with a global linear key order. -/
theorem depth_le_two_sided_weakRecords
    {tree : PriorityMergeTree} (heap : HeapOrdered tree)
    (path : NodePath tree) :
    path.depth <=
      weakRecordCount path.target path.before.reverse +
      weakRecordCount path.target path.after := by
  have left_bound := leftAncestors_le_weakRecords heap path
  have right_bound := rightAncestors_le_weakRecords heap path
  simp only [NodePath.depth]
  omega

/-- If every selected-node path has depth below one common cap, then the whole
tree height fits that cap. -/
theorem height_le_of_all_path_depth_lt
    (tree : PriorityMergeTree) (cap : Nat)
    (all_paths : forall path : NodePath tree, path.depth < cap) :
    tree.height <= cap := by
  induction tree generalizing cap with
  | empty => simp [height]
  | node left priority right left_ih right_ih =>
      have cap_pos : 0 < cap := by
        have root_bound := all_paths (.root left right priority)
        simpa [NodePath.depth, NodePath.leftAncestors,
          NodePath.rightAncestors] using root_bound
      cases cap with
      | zero => omega
      | succ smaller =>
          have left_paths : forall path : NodePath left,
              path.depth < smaller := by
            intro path
            change path.leftAncestors + path.rightAncestors < smaller
            have bound := all_paths (NodePath.left (right := right)
              (priority := priority) path)
            simp only [NodePath.depth, NodePath.leftAncestors,
              NodePath.rightAncestors] at bound
            omega
          have right_paths : forall path : NodePath right,
              path.depth < smaller := by
            intro path
            change path.leftAncestors + path.rightAncestors < smaller
            have bound := all_paths (NodePath.right (left := left)
              (priority := priority) path)
            simp only [NodePath.depth, NodePath.leftAncestors,
              NodePath.rightAncestors] at bound
            omega
          have left_height := left_ih smaller left_paths
          have right_height := right_ih smaller right_paths
          simp only [height]
          omega

/-- Uniform two-sided weak-record control yields a uniform merge-height cap. -/
theorem height_le_of_two_sided_weakRecords_lt
    {tree : PriorityMergeTree} (heap : HeapOrdered tree) (cap : Nat)
    (records_lt : forall path : NodePath tree,
      weakRecordCount path.target path.before.reverse +
        weakRecordCount path.target path.after < cap) :
    tree.height <= cap := by
  apply height_le_of_all_path_depth_lt tree cap
  intro path
  exact Nat.lt_of_le_of_lt (depth_le_two_sided_weakRecords heap path)
    (records_lt path)

end PriorityMergeTree

#print axioms PriorityMergeTree.NodePath.inorder_decomposition
#print axioms PriorityMergeTree.rightAncestors_le_weakRecords
#print axioms PriorityMergeTree.leftAncestors_le_weakRecords
#print axioms PriorityMergeTree.depth_le_two_sided_weakRecords
#print axioms PriorityMergeTree.height_le_of_two_sided_weakRecords_lt
