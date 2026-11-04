import Leader.Wu.ShortGap.SegmentPeakMerge

/-!
# Scoped obstruction to label-preserving oriented append

An unequal-rank merge cannot in general keep the larger segment unchanged and
append arbitrarily many lower-rank singleton pieces without increasing its
two-label alphabet.  Starting from the safe singleton `[1]`, no two appended
labels below `2` produce a peak-safe three-letter word.

This rules out only the naive label-preserving append rule.  It does not rule
out an oriented certificate with boundary metadata, rotations, or an accepted
relabeling of one side.
-/

namespace SegmentPeakWord

private theorem not_safe_one_zero_zero :
    ¬RepeatPeakSafe [1, 0, 0] := by
  intro safe
  obtain ⟨middle, _, left_lt, right_lt, _⟩ :=
    safe 1 2 (by decide) (by decide) (by decide) (by decide)
  omega

private theorem not_safe_one_zero_one :
    ¬RepeatPeakSafe [1, 0, 1] := by
  intro safe
  obtain ⟨middle, middle_lt, left_lt, right_lt, higher⟩ :=
    safe 0 2 (by decide) (by decide) (by decide) (by decide)
  have middle_eq : middle = 1 := by omega
  subst middle
  simp at higher

private theorem not_safe_one_one_zero :
    ¬RepeatPeakSafe [1, 1, 0] := by
  intro safe
  obtain ⟨middle, _, left_lt, right_lt, _⟩ :=
    safe 0 1 (by decide) (by decide) (by decide) (by decide)
  omega

private theorem not_safe_one_one_one :
    ¬RepeatPeakSafe [1, 1, 1] := by
  intro safe
  obtain ⟨middle, _, left_lt, right_lt, _⟩ :=
    safe 0 1 (by decide) (by decide) (by decide) (by decide)
  omega

/-- No choice of two successive connector labels from the unchanged alphabet
`{0,1}` keeps the initial `[1]` segment peak-safe. -/
theorem no_two_label_preserving_right_appends
    (first second : Nat) (first_lt : first < 2) (second_lt : second < 2) :
    ¬RepeatPeakSafe [1, first, second] := by
  have first_cases : first = 0 ∨ first = 1 := by omega
  have second_cases : second = 0 ∨ second = 1 := by omega
  rcases first_cases with rfl | rfl <;>
    rcases second_cases with rfl | rfl
  · exact not_safe_one_zero_zero
  · exact not_safe_one_zero_one
  · exact not_safe_one_one_zero
  · exact not_safe_one_one_one

end SegmentPeakWord

#print axioms SegmentPeakWord.no_two_label_preserving_right_appends
