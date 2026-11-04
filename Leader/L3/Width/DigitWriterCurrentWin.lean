import Leader.L3.Width.DigitCloseCurrent

/-!
# Writer currentness: the aged window of one pair on the writer lane

`L3.CloseCurrent.PairWin` carries, for the comparison lane, the layout, the ghost correspondence
with the inherited base, the value invariant, the cycle class and the aged window `WinAge … cut`
of one complete pair, and `pairCurrentOfAge` turns it into `DigitPairCurrent`.  All the
ingredients (`widthGhostCorrDistinctStep`, `widthValInvStep`, `widthCohortStep`, `cohortCycStep`,
`winAgeStep`, `pairCurrentOfAge`) are generic in the lane; this module instantiates them at the
writer lane:

* `WriterPairWin`: the window class of a pair on the writer lane at `cut`;
* `writerPairWinStep`, `writerPairWinRun`: it is carried by every audit letter and every word;
* `writerPairCurrentOfWin`: it gives `DigitPairCurrent … .writer … cut clock`.

What it does not give: the *entry* of the window class (see
`Leader/L3/Width/DigitWriterCurrentEntry.lean`).

Consumer: `Leader/L3/Width/DigitWriterCurrentEntry.lean`.
-/

namespace L3.WriterCurrent

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.CohortDomination
open L3.CohortSites
open L3.Rearm
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CurrentWin
open L3.CloseCurrent
open L3.WidthWave

variable {n : Nat} {ring : DirectedRing n}

/-- **The window class of one pair on the writer lane at `cut`**: layout, correspondence with the
inherited base, value invariant, cycle class and aged window, with `cut` no later than the clock.

Consumer: `writerPairWinStep`, `writerPairCurrentOfWin`. -/
def WriterPairWin (ref : WidthDigitReference ring) (root : Fin n) (src R cut : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthCohortLayout ref root src R y.1 ∧
  GhostCorrDistinct ring root DigitLane.writer src R (InheritedOk DigitLane.writer)
    (piD (ref.phys y.1)) y.2 ∧
  WidthValInv ref root DigitLane.writer src R y ∧
  (∃ (j : Nat) (g : (Nat → Nat) × Nat) (o : Nat),
    CohortCycIn R j (cohortProj ring root DigitLane.writer src R (piD (ref.phys y.1))) g o) ∧
  WinAge ring root DigitLane.writer src R cut
    (cohortProj ring root DigitLane.writer src R (piD (ref.phys y.1))) y.2 ∧
  cut ≤ y.2.clock

/-- **`WriterPairWin` is carried by every letter.**

Consumer: `writerPairWinRun`. -/
theorem writerPairWinStep (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
    (root : Fin n) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (cut : Nat) (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : WriterPairWin ref root src R cut y) :
    WriterPairWin ref root src R cut (widthDigitAuditNext ref y e) := by
  obtain ⟨hlay, hgc, hval, ⟨jj, g, o, hcyc⟩, hage, hcut⟩ := h
  obtain ⟨hlay', hgc'⟩ := widthGhostCorrDistinctStep ref hfix hn root DigitLane.writer src R
    hR hsrc hend (InheritedOk DigitLane.writer) y hlay hgc e
  have hval' := widthValInvStep ref hfix hn root DigitLane.writer src R hR hsrc hend y hlay
    hval e
  have hproj := (widthCohortStep ref hfix hn root DigitLane.writer src R hR hsrc hend y.1
    hlay e).2
  refine ⟨hlay', hgc', hval', ?_, ?_, ?_⟩
  · show ∃ (j : Nat) (g : (Nat → Nat) × Nat) (o : Nat), CohortCycIn R j
      (cohortProj ring root DigitLane.writer src R (piD (ref.phys (ref.next y.1 e)))) g o
    rw [hproj]
    rcases cohortCycStep hcyc (cohortEdgeOf root src R e) with ⟨o', -, h', -⟩ | h'
    · exact ⟨jj, _, o', h'⟩
    · exact ⟨jj + 1, _, 0, h'⟩
  · obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay
    obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref hfix hn root y.1 hL e
    show WinAge ring root DigitLane.writer src R cut
      (cohortProj ring root DigitLane.writer src R (piD (ref.phys (ref.next y.1 e))))
      (digitAuditStep ring (piD (ref.phys y.1)) y.2 e)
    rw [heq]
    obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
    exact winAgeStep ring (by omega) root (piD (ref.phys y.1)) R src hR hsrc hend hroot hb0 hbR
      hb2R hbF DigitLane.writer (InheritedOk DigitLane.writer)
      (inheritedNoSample DigitLane.writer) y.2 j hj hbX hbY cut hcut hgc hcyc hage
  · show cut ≤ y.2.clock + 1
    omega

/-- `WriterPairWin` along every word.

Consumer: `writerPairCurrentOfWin` users in `WidthDigitWriterCurrentEntry`. -/
theorem writerPairWinRun (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
    (root : Fin n) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (cut : Nat) (word : List (Fin n)) :
    ∀ y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      WriterPairWin ref root src R cut y →
      WriterPairWin ref root src R cut (word.foldl (widthDigitAuditNext ref) y) := by
  induction word with
  | nil => intro y h; exact h
  | cons e rest ih =>
    intro y h
    exact ih _ (writerPairWinStep ref hfix hn root src R hR hsrc hend cut y e h)

/-- **The window class gives writer currentness of the pair at the clock.**

Consumer: `writersCurrentOfEntry` (WidthDigitWriterCurrentEntry). -/
theorem writerPairCurrentOfWin (ref : WidthDigitReference ring) (root : Fin n) (src cut : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WriterPairWin ref root src (digitSpan (compileAdvice (ceilLogTwo n))) cut y) :
    DigitPairCurrent ring root y.2 (piD (ref.phys y.1)) y.2.current DigitLane.writer src
      (src + digitSpan (compileAdvice (ceilLogTwo n))) cut y.2.clock := by
  obtain ⟨-, hgc, hval, ⟨jj, g, o, hcyc⟩, hage, -⟩ := h
  exact pairCurrentOfAge ring root DigitLane.writer src
    (digitSpan (compileAdvice (ceilLogTwo n))) rfl (InheritedOk DigitLane.writer)
    (inheritedNoSample DigitLane.writer) (piD (ref.phys y.1)) y.2 cut hgc hval.1
    hval.2.2.1 hcyc hage

end L3.WriterCurrent

#print axioms L3.WriterCurrent.writerPairWinRun
#print axioms L3.WriterCurrent.writerPairCurrentOfWin
