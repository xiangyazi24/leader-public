import Std.Tactic

/-!
# Structural suppression by peak-separated segment words

This file isolates the combinatorial kernel for a clock-free suppression
design.  A leader-delimited segment is represented by a word of group IDs.
`SegmentPeakWord` records a recursive unique-peak decomposition: the pivot is
strictly larger than every ID in both child segments, and both children carry
the same certificate.

The intended protocol use is a staged leader deletion.  While the victim is
still a leader, its group is rewritten to a fresh pivot.  Only after the two
neighbouring certified segments and the pivot form one certified segment may
the leader bit be cleared.  The lemmas below are purely combinatorial; they do
not assume a physical handshake, accepted-work cleanup, or a scheduler bound.
-/

/-- A finite ID word with a recursive strictly-dominating pivot.

This is a certificate form of the paper's `perfect` condition.  In particular,
two equal values lying in different children are separated by the displayed
pivot, while equal values inside one child are handled recursively. -/
inductive SegmentPeakWord : List Nat -> Prop
  | empty : SegmentPeakWord []
  | pivot (left right : List Nat) (value : Nat)
      (left_safe : SegmentPeakWord left)
      (right_safe : SegmentPeakWord right)
      (left_lt : forall x, x ∈ left -> x < value)
      (right_lt : forall x, x ∈ right -> x < value) :
      SegmentPeakWord (left ++ value :: right)

namespace SegmentPeakWord

/-- Operational form of the `perfect` condition: any two equal IDs in linear
order have a strictly larger ID between them. -/
def RepeatPeakSafe (word : List Nat) : Prop :=
  forall (i j : Nat) (hi : i < word.length) (hj : j < word.length),
    i < j -> word.get ⟨i, hi⟩ = word.get ⟨j, hj⟩ ->
      exists (k : Nat) (hk : k < word.length),
        i < k ∧ k < j ∧ word.get ⟨i, hi⟩ < word.get ⟨k, hk⟩

private theorem get_merge_left
    {left right : List Nat} {value i : Nat}
    (hi : i < left.length)
    (hword : i < (left ++ value :: right).length) :
    (left ++ value :: right).get ⟨i, hword⟩ = left.get ⟨i, hi⟩ := by
  simp only [List.get_eq_getElem, List.getElem_append]
  simp [hi]

private theorem get_merge_pivot
    {left right : List Nat} {value : Nat}
    (hword : left.length < (left ++ value :: right).length) :
    (left ++ value :: right).get ⟨left.length, hword⟩ = value := by
  simp only [List.get_eq_getElem, List.getElem_append]
  simp

private theorem get_merge_right
    {left right : List Nat} {value i : Nat}
    (hi : left.length < i)
    (hword : i < (left ++ value :: right).length)
    (hright : i - (left.length + 1) < right.length) :
    (left ++ value :: right).get ⟨i, hword⟩ =
      right.get ⟨i - (left.length + 1), hright⟩ := by
  simp only [List.get_eq_getElem, List.getElem_append]
  have hnot : ¬i < left.length := by omega
  rw [dif_neg hnot]
  have hpos : 1 <= i - left.length := by omega
  have hidx : i - left.length = (i - (left.length + 1)) + 1 := by
    rw [← Nat.sub_sub]
    exact (Nat.sub_add_cancel hpos).symm
  simp only [hidx, List.getElem_cons_succ]

/-- The abstract deletion join: a pivot dominating both certified children
makes their concatenation a certified segment. -/
theorem merge
    {left right : List Nat} {value : Nat}
    (left_safe : SegmentPeakWord left)
    (right_safe : SegmentPeakWord right)
    (left_lt : forall x, x ∈ left -> x < value)
    (right_lt : forall x, x ∈ right -> x < value) :
    SegmentPeakWord (left ++ value :: right) :=
  .pivot left right value left_safe right_safe left_lt right_lt

/-- The recursive certificate implies the exact pairwise peak condition used
by comparison-signal safety. -/
theorem repeat_peak_safe
    {word : List Nat} (safe : SegmentPeakWord word) :
    RepeatPeakSafe word := by
  induction safe with
  | empty =>
      intro i j hi
      simp at hi
  | pivot left right value left_safe right_safe left_lt right_lt ih_left ih_right =>
      intro i j hi hj hij equal
      let split := left.length
      by_cases hj_left : j < split
      · have hi_left : i < split := by omega
        have equal_left :
            left.get ⟨i, hi_left⟩ = left.get ⟨j, hj_left⟩ := by
          rw [← get_merge_left hi_left hi, ← get_merge_left hj_left hj]
          exact equal
        obtain ⟨k, hk, hik, hkj, hpeak⟩ :=
          ih_left i j hi_left hj_left hij equal_left
        have hk_word : k < (left ++ value :: right).length := by
          simp only [List.length_append, List.length_cons]
          omega
        refine ⟨k, hk_word, hik, hkj, ?_⟩
        rw [get_merge_left hi_left hi, get_merge_left hk hk_word]
        exact hpeak
      · by_cases hi_left : i < split
        · by_cases hj_pivot : j = split
          · subst j
            have source_mem : left.get ⟨i, hi_left⟩ ∈ left :=
              List.get_mem left ⟨i, hi_left⟩
            have source_lt := left_lt _ source_mem
            have hpivot : split < (left ++ value :: right).length := by
              simp only [List.length_append, List.length_cons]
              omega
            rw [get_merge_left hi_left hi, get_merge_pivot hpivot] at equal
            omega
          · have hj_after : split < j := by omega
            have hpivot : split < (left ++ value :: right).length := by
              simp only [List.length_append, List.length_cons]
              omega
            have source_mem : left.get ⟨i, hi_left⟩ ∈ left :=
              List.get_mem left ⟨i, hi_left⟩
            have source_lt := left_lt _ source_mem
            refine ⟨split, hpivot, by omega, hj_after, ?_⟩
            rw [get_merge_left hi_left hi, get_merge_pivot hpivot]
            exact source_lt
        · have hi_ge : split <= i := by omega
          by_cases hi_pivot : i = split
          · subst i
            have hj_after : split < j := by omega
            have hj_right : j - (split + 1) < right.length := by
              simp only [List.length_append, List.length_cons] at hj
              omega
            have target_mem : right.get ⟨j - (split + 1), hj_right⟩ ∈ right :=
              List.get_mem right ⟨j - (split + 1), hj_right⟩
            have target_lt := right_lt _ target_mem
            dsimp [split] at target_lt
            have hpivot : split < (left ++ value :: right).length := by
              simp only [List.length_append, List.length_cons]
              omega
            rw [get_merge_pivot hpivot,
              get_merge_right hj_after hj hj_right] at equal
            have impossible : value < value := by
              calc
                value = right.get ⟨j - (left.length + 1), hj_right⟩ := equal
                _ < value := target_lt
            exact (Nat.lt_irrefl value impossible).elim
          · have hi_after : split < i := by omega
            have hj_after : split < j := by omega
            let i' := i - (split + 1)
            let j' := j - (split + 1)
            have hi_right : i' < right.length := by
              simp only [List.length_append, List.length_cons] at hi
              dsimp [i']
              omega
            have hj_right : j' < right.length := by
              simp only [List.length_append, List.length_cons] at hj
              dsimp [j']
              omega
            have hij_right : i' < j' := by
              dsimp [i', j']
              omega
            have equal_right :
                right.get ⟨i', hi_right⟩ = right.get ⟨j', hj_right⟩ := by
              rw [← get_merge_right hi_after hi hi_right,
                ← get_merge_right hj_after hj hj_right]
              exact equal
            obtain ⟨k, hk, hik, hkj, hpeak⟩ :=
              ih_right i' j' hi_right hj_right hij_right equal_right
            let lifted := split + 1 + k
            have hlift_after : split < lifted := by
              dsimp [lifted]
              omega
            have hlift_word : lifted < (left ++ value :: right).length := by
              simp only [List.length_append, List.length_cons]
              dsimp [lifted]
              omega
            have hlift_right : lifted - (split + 1) < right.length := by
              dsimp [lifted]
              simpa using hk
            refine ⟨lifted, hlift_word, ?_, ?_, ?_⟩
            · dsimp [lifted, i'] at hik ⊢
              omega
            · dsimp [lifted, j'] at hkj ⊢
              omega
            · rw [get_merge_right hi_after hi hi_right,
                get_merge_right hlift_after hlift_word hlift_right]
              have hlift_index : lifted - (split + 1) = k := by
                dsimp [lifted]
                omega
              dsimp [i', split] at hpeak
              dsimp [split] at hlift_index
              simp only [List.get_eq_getElem] at hpeak ⊢
              simpa only [hlift_index] using hpeak

/-- Any comparison signal crossing from the left child into the right child
meets the merge pivot, whose value is larger than its source ID. -/
theorem pivot_blocks_cross_child_match
    {left : List Nat} {value source : Nat}
    (source_in_left : source ∈ left)
    (left_lt : forall x, x ∈ left -> x < value) :
    source < value :=
  left_lt source source_in_left

private theorem two_pow_mono {a b : Nat} (hab : a <= b) :
    2 ^ a <= 2 ^ b := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases ha : a = b + 1
      · subst a
        exact Nat.le_refl _
      · have hab' : a <= b := by omega
        have hprev := ih hab'
        rw [Nat.pow_succ]
        omega

private theorem two_pow_pos (exponent : Nat) : 0 < 2 ^ exponent := by
  induction exponent with
  | zero => simp
  | succ exponent ih =>
      rw [Nat.pow_succ]
      omega

/-- A certified word whose IDs all lie below `cap` has fewer than `2^cap`
positions.  Thus logarithmic ID height is both sufficient for balanced merge
trees and necessary for arbitrarily long certified segments. -/
theorem length_lt_two_pow_of_bounded
    {word : List Nat} (safe : SegmentPeakWord word) :
    forall cap : Nat, (forall x, x ∈ word -> x < cap) ->
      word.length < 2 ^ cap := by
  induction safe with
  | empty =>
      intro cap _
      simpa only [List.length_nil] using two_pow_pos cap
  | pivot left right value left_safe right_safe left_lt right_lt ih_left ih_right =>
      intro cap all_lt
      have value_lt : value < cap := by
        apply all_lt value
        simp
      have left_length : left.length < 2 ^ value :=
        ih_left value left_lt
      have right_length : right.length < 2 ^ value :=
        ih_right value right_lt
      have merged_length :
          (left ++ value :: right).length < 2 ^ (value + 1) := by
        rw [List.length_append, List.length_cons, Nat.pow_succ]
        omega
      have cap_power := two_pow_mono (a := value + 1) (b := cap) (by omega)
      omega

end SegmentPeakWord

/-- A segment packages the strict upper bound that its next merge may use as
a pivot.  `cap` is proof data here; a physical protocol would encode it in a
distributed bit word. -/
structure RankedPeakSegment where
  word : List Nat
  cap : Nat
  safe : SegmentPeakWord word
  bounded : forall x, x ∈ word -> x < cap

namespace RankedPeakSegment

/-- Empty leader-to-leader intervals start at rank zero. -/
def empty : RankedPeakSegment where
  word := []
  cap := 0
  safe := .empty
  bounded := by simp

/-- Merge two certified intervals around the group occupied by the leader to
be deleted.  The old leader group receives `max left.cap right.cap`; the merged
rank is one larger. -/
def merge (left right : RankedPeakSegment) : RankedPeakSegment where
  word := left.word ++ max left.cap right.cap :: right.word
  cap := max left.cap right.cap + 1
  safe := by
    apply SegmentPeakWord.merge left.safe right.safe
    · intro x hx
      have hx' := left.bounded x hx
      have hcap : left.cap <= max left.cap right.cap := Nat.le_max_left _ _
      omega
    · intro x hx
      have hx' := right.bounded x hx
      have hcap : right.cap <= max left.cap right.cap := Nat.le_max_right _ _
      omega
  bounded := by
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | hx | hx
    · have hx' := left.bounded x hx
      have hcap : left.cap <= max left.cap right.cap := Nat.le_max_left _ _
      omega
    · subst x
      omega
    · have hx' := right.bounded x hx
      have hcap : right.cap <= max left.cap right.cap := Nat.le_max_right _ _
      omega

/-- Every ranked segment obeys the sharp exponential capacity bound. -/
theorem length_lt_capacity (segment : RankedPeakSegment) :
    segment.word.length < 2 ^ segment.cap :=
  SegmentPeakWord.length_lt_two_pow_of_bounded segment.safe segment.cap
    segment.bounded

/-- The rank recurrence exposed by a certified deletion. -/
theorem merge_cap (left right : RankedPeakSegment) :
    (merge left right).cap = max left.cap right.cap + 1 := rfl

/-- The direct `max + 1` merge rule has linear adversarial height.  Repeatedly
attaching an empty right child is the abstract deletion tree obtained by a
completely unbalanced sequence of boundary removals. -/
def rightComb : Nat -> RankedPeakSegment
  | 0 => empty
  | steps + 1 => merge (rightComb steps) empty

theorem rightComb_cap (steps : Nat) : (rightComb steps).cap = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [rightComb, merge_cap, ih, empty]
      omega

theorem rightComb_length (steps : Nat) :
    (rightComb steps).word.length = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [rightComb, merge, empty, ih]

/-- Hence a finite pivot alphabet of size `cap` cannot simply execute the
direct merge rule on every deletion order: one more unbalanced merge requests
rank `cap + 1`.  A fast-path height tail still needs a total overflow branch. -/
theorem rightComb_overflow (cap : Nat) :
    (rightComb (cap + 1)).cap = cap + 1 :=
  rightComb_cap (cap + 1)

end RankedPeakSegment

#print axioms SegmentPeakWord.length_lt_two_pow_of_bounded
#print axioms SegmentPeakWord.repeat_peak_safe
#print axioms RankedPeakSegment.length_lt_capacity
#print axioms RankedPeakSegment.rightComb_overflow
