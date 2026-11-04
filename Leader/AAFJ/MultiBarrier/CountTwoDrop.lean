import Leader.AAFJ.MultiBarrier.PushIterate

set_option autoImplicit false

namespace AAFJPK.OriginalCountTwoDrop

open BarrierAlgebra
open OriginalNonbarrierWord

abbrev Config (n k : Nat) := Fin n → State k

private theorem list_length_two_shape
    {α : Type} (xs : List α) (h : xs.length = 2) :
    ∃ a b, xs = [a, b] := by
  cases xs with
  | nil => simp at h
  | cons a xs =>
      cases xs with
      | nil => simp at h
      | cons b xs =>
          cases xs with
          | nil => exact ⟨a, b, rfl⟩
          | cons c xs =>
              simp only [List.length_cons] at h
              omega

/-- A charged-barrier count of two yields a fresh oriented exact-support pair. -/
theorem exactTwo_of_barrierCount_eq_two
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Config n k)
    (hcount : barrierCount hk ring (labelsOf C) = 2) :
    ∃ a b, ExactTwoBarrierSupport hk ring C a b := by
  let S := barrierSupport hk ring (labelsOf C)
  have hlen : S.length = 2 := by
    simpa [S, barrierCount] using hcount
  rcases list_length_two_shape S hlen with ⟨a, b, hS⟩
  have hnodup : S.Nodup := by
    simpa [S] using barrierSupport_nodup hk ring (labelsOf C)
  rw [hS] at hnodup
  have hab : a ≠ b := by
    simpa using hnodup
  have hmem :
      ∀ e : Fin n, e ∈ S ↔ BarrierAt hk ring (labelsOf C) e := by
    intro e
    simpa [S] using mem_barrierSupport_iff hk ring (labelsOf C) e
  refine ⟨a, b, ⟨hab, ?_⟩⟩
  intro e
  constructor
  · intro hb
    have hm : e ∈ S := (hmem e).2 hb
    rw [hS] at hm
    simpa using hm
  · intro he
    apply (hmem e).1
    rw [hS]
    simpa using he

/-- From the scalar count-two level alone, a bounded literal word strictly
decreases the original AAFJ charged-barrier count. -/
theorem countTwo_strict_drop_word
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Config n k)
    (hcount : barrierCount hk ring (labelsOf C) = 2) :
    ∃ word : List (Fin n),
      word.length ≤ 4 * (n - 2) + 6 ∧
      barrierCount hk ring (labelsOf (rawRun hk ring C word)) <
        barrierCount hk ring (labelsOf C) := by
  rcases exactTwo_of_barrierCount_eq_two hk ring C hcount with ⟨q, r, hs⟩
  exact AAFJPK.OriginalPushIter.exactTwo_strict_drop_word
    hk ring hn3 C q r hs

#print axioms exactTwo_of_barrierCount_eq_two
#print axioms countTwo_strict_drop_word

end AAFJPK.OriginalCountTwoDrop
