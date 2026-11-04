import Std.Tactic

set_option autoImplicit false

namespace ShortGapMergeMonotone

/-- Number of gaps whose lengths are strictly below the threshold `h`. -/
def shortCount (h : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => if x < h then shortCount h xs + 1 else shortCount h xs

/-- Merge the entries at positions `i` and `i+1` by replacing them with their
sum.  The theorems below are for the non-wrap case `i + 1 < l.length`.
For an invalid position, `mergeAt` leaves the remaining list unchanged. -/
def mergeAt : List Nat → Nat → List Nat
  | x :: y :: xs, 0 => (x + y) :: xs
  | x :: xs, Nat.succ i => x :: mergeAt xs i
  | l, _ => l

/-- A valid non-wrap merge removes exactly one gap. -/
theorem length_mergeAt
    (l : List Nat) (i : Nat) (hi : i + 1 < l.length) :
    (mergeAt l i).length + 1 = l.length := by
  induction i generalizing l with
  | zero =>
      cases l with
      | nil => simp at hi
      | cons x xs =>
          cases xs with
          | nil => simp at hi
          | cons y ys =>
              simp [mergeAt]
  | succ i ih =>
      cases l with
      | nil => simp at hi
      | cons x xs =>
          have hi' : i + 1 < xs.length := by
            simp at hi
            omega
          simpa [mergeAt] using
            congrArg (fun k : Nat => k + 1) (ih xs hi')

/-- Every output gap dominates some input gap.  In particular, a merge never
creates a gap shorter than both of its sources, and untouched gaps are equal
to an input gap. -/
theorem mem_ge_of_mergeAt
    (l : List Nat) (i : Nat) (hi : i + 1 < l.length) :
    ∀ y ∈ mergeAt l i, ∃ x ∈ l, x ≤ y := by
  induction i generalizing l with
  | zero =>
      cases l with
      | nil => simp at hi
      | cons x xs =>
          cases xs with
          | nil => simp at hi
          | cons y ys =>
              intro z hz
              simp [mergeAt] at hz
              rcases hz with hz | hz
              · subst z
                exact ⟨x, by simp, by omega⟩
              · exact ⟨z, by simp [hz], Nat.le_refl z⟩
  | succ i ih =>
      cases l with
      | nil => simp at hi
      | cons x xs =>
          have hi' : i + 1 < xs.length := by
            simp at hi
            omega
          intro z hz
          simp [mergeAt] at hz
          rcases hz with hz | hz
          · subst z
            exact ⟨x, by simp, Nat.le_refl x⟩
          · obtain ⟨w, hwmem, hwle⟩ := ih xs hi' z hz
            exact ⟨w, by simp [hwmem], hwle⟩

/-- Positions strictly before the merged pair are untouched. -/
theorem get?_mergeAt_before
    (l : List Nat) (i j : Nat)
    (hi : i + 1 < l.length) (hj : j < i) :
    (mergeAt l i)[j]? = l[j]? := by
  induction i generalizing l j with
  | zero => omega
  | succ i ih =>
      cases l with
      | nil => simp at hi
      | cons x xs =>
          have hi' : i + 1 < xs.length := by
            simp at hi
            omega
          cases j with
          | zero => simp [mergeAt]
          | succ j =>
              have hj' : j < i := by omega
              simpa [mergeAt] using ih xs j hi' hj'

/-- Positions strictly after the merged output entry are shifted left by one.
The extra bound says that the corresponding source position `j+1` exists. -/
theorem get?_mergeAt_after
    (l : List Nat) (i j : Nat)
    (hi : i + 1 < l.length) (hj : i < j)
    (hjlen : j + 1 < l.length) :
    (mergeAt l i)[j]? = l[j + 1]? := by
  induction i generalizing l j with
  | zero =>
      cases l with
      | nil => simp at hi
      | cons x xs =>
          cases xs with
          | nil => simp at hi
          | cons y ys =>
              cases j with
              | zero => omega
              | succ j => simp [mergeAt]
  | succ i ih =>
      cases l with
      | nil => simp at hi
      | cons x xs =>
          have hi' : i + 1 < xs.length := by
            simp at hi
            omega
          cases j with
          | zero => omega
          | succ j =>
              have hj' : i < j := by omega
              have hjlen' : j + 1 < xs.length := by
                simp at hjlen
                omega
              simpa [mergeAt] using ih xs j hi' hj' hjlen'

/-- If the left member of the merged pair is short, the number of short gaps
drops by at least one.  Gap lengths do not count the deleted leader itself. -/
theorem shortCount_mergeAt_of_short
    (h : Nat) (l : List Nat) (i : Nat)
    (hi : i + 1 < l.length)
    (hx : l.get ⟨i, by omega⟩ < h) :
    shortCount h (mergeAt l i) + 1 ≤ shortCount h l := by
  induction i generalizing l with
  | zero =>
      cases l with
      | nil => simp at hi
      | cons x xs =>
          cases xs with
          | nil => simp at hi
          | cons y ys =>
              change x < h at hx
              by_cases hy : y < h
              <;> by_cases hxy : x + y < h
              <;> simp [mergeAt, shortCount, hx, hy, hxy]
              <;> omega
  | succ i ih =>
      cases l with
      | nil => simp at hi
      | cons x xs =>
          have hi' : i + 1 < xs.length := by
            simp at hi
            omega
          change xs.get ⟨i, by omega⟩ < h at hx
          have hind := ih xs hi' hx
          by_cases hhead : x < h
          <;> simp [mergeAt, shortCount, hhead]
          <;> omega

/-- A valid merge can never increase the number of short gaps. -/
theorem shortCount_mergeAt_le
    (h : Nat) (l : List Nat) (i : Nat)
    (hi : i + 1 < l.length) :
    shortCount h (mergeAt l i) ≤ shortCount h l := by
  induction i generalizing l with
  | zero =>
      cases l with
      | nil => simp at hi
      | cons x xs =>
          cases xs with
          | nil => simp at hi
          | cons y ys =>
              by_cases hx : x < h
              <;> by_cases hy : y < h
              <;> by_cases hxy : x + y < h
              <;> simp [mergeAt, shortCount, hx, hy, hxy]
              <;> omega
  | succ i ih =>
      cases l with
      | nil => simp at hi
      | cons x xs =>
          have hi' : i + 1 < xs.length := by
            simp at hi
            omega
          have hind := ih xs hi'
          by_cases hhead : x < h
          <;> simp [mergeAt, shortCount, hhead]
          <;> omega

/-- Merging two adjacent gaps preserves their total length. -/
theorem sum_mergeAt
    (l : List Nat) (i : Nat) (hi : i + 1 < l.length) :
    (mergeAt l i).sum = l.sum := by
  induction i generalizing l with
  | zero =>
      cases l with
      | nil => simp at hi
      | cons x xs =>
          cases xs with
          | nil => simp at hi
          | cons y ys =>
              simp [mergeAt, List.sum_cons, Nat.add_assoc]
  | succ i ih =>
      cases l with
      | nil => simp at hi
      | cons x xs =>
          have hi' : i + 1 < xs.length := by
            simp at hi
            omega
          simpa [mergeAt, List.sum_cons] using
            congrArg (fun k : Nat => x + k) (ih xs hi')

/-- The short-gap count is bounded by the number of gaps. -/
theorem shortCount_le_length (h : Nat) (l : List Nat) :
    shortCount h l ≤ l.length := by
  induction l with
  | nil => simp [shortCount]
  | cons x xs ih =>
      by_cases hx : x < h
      <;> simp [shortCount, hx]
      <;> omega

/-- Every non-short gap has length at least `h`; hence their total minimum
mass is bounded by the sum of all gap lengths. -/
theorem long_count_le (h : Nat) (l : List Nat) :
    h * (l.length - shortCount h l) ≤ l.sum := by
  induction l with
  | nil => simp [shortCount]
  | cons x xs ih =>
      have hsc : shortCount h xs ≤ xs.length := shortCount_le_length h xs
      by_cases hx : x < h
      · have hsub :
            (x :: xs).length - shortCount h (x :: xs) =
              xs.length - shortCount h xs := by
          simp [shortCount, hx] <;> omega
        calc
          h * ((x :: xs).length - shortCount h (x :: xs)) =
              h * (xs.length - shortCount h xs) := by rw [hsub]
          _ ≤ xs.sum := ih
          _ ≤ (x :: xs).sum := by
            simp only [List.sum_cons]
            omega
      · have hxge : h ≤ x := by omega
        have hsub :
            (x :: xs).length - shortCount h (x :: xs) =
              (xs.length - shortCount h xs) + 1 := by
          simp [shortCount, hx] <;> omega
        calc
          h * ((x :: xs).length - shortCount h (x :: xs)) =
              h * ((xs.length - shortCount h xs) + 1) := by rw [hsub]
          _ = h * (xs.length - shortCount h xs) + h := by
            simp [Nat.mul_add]
          _ ≤ xs.sum + x := Nat.add_le_add ih hxge
          _ = (x :: xs).sum := by
            simp only [List.sum_cons]
            exact Nat.add_comm _ _

/-- Quiescent-round arithmetic with constant `c₁ = 4`. -/
theorem round_cost_le_four_nhZ
    (h Z n : Nat) (hZ : 1 ≤ Z) (hh : 1 ≤ h) :
    n * Z * (2 * h + 1) + n * (2 * h - 1) ≤ 4 * n * h * Z := by
  have h1 : n * (2 * h - 1) ≤ n * Z * (2 * h - 1) := by
    apply Nat.mul_le_mul_right
    calc n = n * 1 := (Nat.mul_one _).symm
      _ ≤ n * Z := Nat.mul_le_mul_left _ hZ
  have h2 : n * Z * (2 * h + 1) + n * Z * (2 * h - 1) = 4 * n * h * Z := by
    rw [← Nat.mul_add]
    have he : (2 * h + 1) + (2 * h - 1) = 4 * h := by omega
    rw [he]
    ac_rfl
  omega

#print axioms ShortGapMergeMonotone.length_mergeAt
#print axioms ShortGapMergeMonotone.mem_ge_of_mergeAt
#print axioms ShortGapMergeMonotone.get?_mergeAt_before
#print axioms ShortGapMergeMonotone.get?_mergeAt_after
#print axioms ShortGapMergeMonotone.shortCount_mergeAt_of_short
#print axioms ShortGapMergeMonotone.shortCount_mergeAt_le
#print axioms ShortGapMergeMonotone.sum_mergeAt
#print axioms ShortGapMergeMonotone.shortCount_le_length
#print axioms ShortGapMergeMonotone.long_count_le
#print axioms ShortGapMergeMonotone.round_cost_le_four_nhZ
