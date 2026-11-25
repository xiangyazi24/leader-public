import Leader.L4.ReportDigitWord

namespace L4.ReportCommitValue
open ReportDigitArithmetic ReportDigitWord ReportStaticSpacing ShortResetChart

/-- If the now-selected file is precisely the preserved staged output, the
physical word decodes to the clipped old-snapshot update. No provenance
or selected-bank frame follows merely from a byte-valid COMMIT guard. -/
theorem value_of_preserved_digits {n : Nat} (p : ReportByteRows.Params)
    (post : Fin n → BitVec p.w) (i : Fin n) (minus : Bool)
    (ix x : Nat) (root : Bool) (B : 2≤p.beta) (R : p.radius < p.beta^p.digits)
    (S : ReportByteRows.publicationSelector p (post i)=ix)
    (D : ∀ j, j<p.digits →
      selectedDigit p ix minus (post (nextAt i j)) =
        digit p.beta j (updateDist p.radius root x)) :
    reportValue p post i minus = updateDist p.radius root x := by
  let y := updateDist p.radius root x
  have Y : y < p.beta^p.digits := by
    cases root with
    | true => simpa [y,updateDist] using (Nat.pow_pos (by omega) : 0 < p.beta^p.digits)
    | false => exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) R
  change reportValue p post i minus = y
  rw [←Nat.mod_eq_of_lt Y, ←word_of_digits]
  unfold reportValue word
  rw [S]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j J
  rw [D j (List.mem_range.mp J)]

/-- Semantic descriptor supplied by the completed directional folds. -/
def descriptor (old radius left right : Nat) : Nat :=
  4*(2*old+(1-old)) + 2*(decide (left<radius)).toNat+(decide (right<radius)).toNat

theorem descriptor_fields (old radius left right : Nat) (O : old≤1) :
    let d := descriptor old radius left right
    d/8=old ∧ (d/4)%2=1-old ∧
      d%4=2*(decide (left<radius)).toNat+(decide (right<radius)).toNat := by
  unfold descriptor
  rcases (show old=0 ∨ old=1 by omega) with H|H <;> rw [H] <;>
    by_cases L : left<radius <;> by_cases R : right<radius <;> simp [L,R]

#print axioms value_of_preserved_digits
#print axioms descriptor_fields
end L4.ReportCommitValue
