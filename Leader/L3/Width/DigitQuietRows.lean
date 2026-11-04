import Leader.L3.CertRows

/-!
# The dirty and report rows of `liveTopPair`

The last lines of `liveTopPair` (CertRows.lean 745-758, "emission-first DIRTY"): a side's new dirty
bit is the change of its digit unless the side was dirty, in which case the bit is cleared and
the step reports; the only other report is the comparison carry reaching its terminal with the
error bit set.

Consumer: `L3.DigitQuiet.qdigitOfQuiet` (WidthDigitQuietSafe).
-/

namespace L3

set_option autoImplicit false

section Rows

variable (c : Compiled) (ox oy : Agent c) (bX bY : Bool)

/-- The new dirty bit of the left side: cleared if it was dirty, else the change of the digit.
Consumer: `WidthDigitQuietSafe`. -/
theorem liveTop_dirty_x :
    (liveTopPair c ox oy bX bY).x.topDirty =
      (if ox.topDirty = true then false else ((liveTopPair c ox oy bX bY).x.d != ox.d)) := by
  cases hx : ox.topDirty <;> simp [liveTopPair, hx]

/-- The new dirty bit of the right side.  Consumer: `WidthDigitQuietSafe`. -/
theorem liveTop_dirty_y :
    (liveTopPair c ox oy bX bY).y.topDirty =
      (if oy.topDirty = true then false else ((liveTopPair c ox oy bX bY).y.d != oy.d)) := by
  cases hy : oy.topDirty <;> simp [liveTopPair, hy]

/-- A report clears an OLD dirty endpoint or is a comparison carry at its terminal with the error
bit set.  Consumer: `WidthDigitQuietSafe`. -/
theorem liveTop_report_source (h : (liveTopPair c ox oy bX bY).topReject = true) :
    ox.topDirty = true ∨ oy.topDirty = true ∨
      (ox.l = false ∧ oy.l = false ∧ ox.qCarry.isL = true ∧ topTerminal ox oy = true ∧
        qcE ox.qCarry = true) := by
  cases hx : ox.topDirty
  · cases hy : oy.topDirty
    · refine Or.inr (Or.inr ?_)
      cases hxl : ox.l
      · cases hyl : oy.l
        · cases hq : ox.qCarry with
          | OFF =>
              simp [liveTopPair, hx, hy, hxl, hyl, hq, QCarry.isL] at h
              split at h <;> simp at h
          | L cc e =>
              cases ht : topTerminal ox oy
              · simp [liveTopPair, hx, hy, hxl, hyl, hq, ht, QCarry.isL] at h
                split at h <;> simp at h
              · cases he : e
                · simp [liveTopPair, hx, hy, hxl, hyl, hq, ht, he, QCarry.isL, qcE] at h
                · simp [QCarry.isL, qcE, hq, ht, he]
        · simp [liveTopPair, hx, hy, hxl, hyl] at h
      · simp [liveTopPair, hx, hy, hxl] at h
    · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

end Rows

end L3

#print axioms L3.liveTop_dirty_x
#print axioms L3.liveTop_dirty_y
#print axioms L3.liveTop_report_source
