import Leader.L3.Width.DigitWriterCurrentOrderStep
import Leader.L3.Width.DigitWriterCurrentEntry

/-!
# Writer currentness: no inherited carry in the target window after the first completion

`OrderInv` collects, for a state of the audit fold, the marker layout, the carry correspondence,
the order of inherited and new carries in the target window (`OrdWin`) and the clause "if a writer
terminal of the last target cell with a non-inherited ledger was recorded, the window holds no
inherited carry" (`NoInhWin`).  One letter preserves it (`orderInvStep`, from `windowShape`), so
it holds along every clean run of a complete pair (`orderInvRun`).  Hence the first recorded
completion of a pair makes the window of its target free of inherited carries
(`windowNoInherited`): a non-inherited carry reached the last cell, so every carry to its left is
non-inherited, and nothing inherited enters afterwards.

Consumer: `writerAgeBodyOfAged` (WidthDigitWriterCurrentAged).
-/

namespace L3.WriterCurrent

set_option autoImplicit false

open L3
open L3.WidthDigit
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.GhostBridge
open L3.Correspondence
open L3.WidthWave

variable {n : Nat} {ring : DirectedRing n}

/-- **The order invariant of a state of the audit fold.**  Consumer: `orderInvStep`. -/
def OrderInv (ref : WidthDigitReference ring) (root : Fin n) (src R : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthCohortLayout ref root src R y.1 ∧ CarryAll (piD (ref.phys y.1)) y.2.current ∧
  OrdWin R (winCarry ring root src y.2.current) ∧
  (∀ (T : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
      (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n),
    DigitRecordedTerminal y.2 T → T.lane = DigitLane.writer →
    T.source = digitSite ring root (src + (2 * R - 1)) → T.ledger = some L →
    L.inherited = none → NoInhWin R (winCarry ring root src y.2.current))

/-- **One letter preserves `OrderInv`.**  Consumer: `orderInvRun`. -/
theorem orderInvStep (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
    (root : Fin n) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : OrderInv ref root src R y) : OrderInv ref root src R (widthDigitAuditNext ref y e) := by
  obtain ⟨hlay, hcar, hord, hterm⟩ := h
  have hlay' := (widthCohortStep ref hfix hn root DigitLane.writer src R hR hsrc hend y.1 hlay
    e).1
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay
  obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref hfix hn root y.1 hL e
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hshape := windowShape ring (by omega) root (piD (ref.phys y.1)) y.2.current
    (y.2.clock + 1) R src hR hsrc hend hbR hb2R hbF hcar j hj hbX hbY
  refine ⟨hlay', ?_, ?_, ?_⟩
  · show CarryAll (piD (ref.phys (ref.next y.1 (digitSite ring root j))))
      (digitGhostStep ring (piD (ref.phys y.1)) y.2.current (y.2.clock + 1)
        (digitSite ring root j))
    rw [heq]
    exact carryAll_step ring _ _ _ _ hcar
  · exact ordWin_step hR hshape hord
  · intro T L hT hlane hsrcT hled hinh
    have hT' : DigitRecordedTerminal (digitAuditStep ring (piD (ref.phys y.1)) y.2
        (digitSite ring root j)) T := hT
    obtain ⟨f, hf, hft, hfe, hfr⟩ := hT'
    simp only [digitAuditStep, List.mem_cons] at hf
    rcases hf with hf | hf
    · subst hf
      have hjv : j = src + (2 * R - 1) :=
        bankRepairDigitSiteInj ring root hj (by omega) (hfe.trans hsrcT)
      rw [hlane] at hfr
      have hterm' := L3.UseRows.termLiveD DigitLane.writer (y.2.clock + 1)
        (digitSite ring root j) (ring.rightNeighbor (digitSite ring root j))
        ((piD (ref.phys y.1)) (digitSite ring root j))
        ((piD (ref.phys y.1)) (ring.rightNeighbor (digitSite ring root j)))
        (y.2.current (digitSite ring root j))
        (y.2.current (ring.rightNeighbor (digitSite ring root j))) T hfr
      have hLold : winCarry ring root src y.2.current (2 * R - 1) = some L := by
        unfold winCarry
        rw [← hjv]
        rw [← hled]
        exact hterm'.2.symm
      subst hjv
      rw [if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at hshape
      exact noInhWin_exit hR hshape (by omega) hord L hLold hinh
    · exact noInhWin_step hR hshape (hterm T L ⟨f, hf, hft, hfe, hfr⟩ hlane hsrcT hled hinh)

/-- **`OrderInv` along a word.**  Consumer: `windowNoInherited`. -/
theorem orderInvRun (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
    (root : Fin n) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (w : List (Fin n)) :
    ∀ y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      OrderInv ref root src R y →
      OrderInv ref root src R (w.foldl (widthDigitAuditNext ref) y) := by
  induction w with
  | nil => intro y h; exact h
  | cons e rest ih =>
    intro y h
    exact ih _ (orderInvStep ref hfix hn root src R hR hsrc hend y e h)

end L3.WriterCurrent

#print axioms L3.WriterCurrent.orderInvStep
#print axioms L3.WriterCurrent.orderInvRun
