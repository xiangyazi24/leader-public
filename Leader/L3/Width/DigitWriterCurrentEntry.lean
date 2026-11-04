import Leader.L3.Width.DigitWriterCurrentWin
import Leader.L3.Width.DigitCloseEntry

/-!
# Writer currentness: the entry of the window class at the fifth writer completion

`L3.WriterCurrent.WriterPairWin` is carried by every audit letter.  This module splits its entry,
at the terminal letter of the fifth next writer completion of a complete pair after `after`
(`DigitFiveCompletions`, the first part of the chain's `DigitFiveCohortCompletions`), into

* a routine part, proved on every clean-run state: the layout, the ghost correspondence with the
  inherited base and the value invariant of the pair on the writer lane (`writerPairBaseRun`,
  the writer copy of `L3.CloseEntry.pairBaseRun`);
* the new content `WriterEntryCore`: at that terminal state the masked writer lane is in the cycle
  class and the aged window `WinAge … after` holds.

Data: `research/lean-l3/wip/r10c-values/run6.py` and `run7.py` check the consequence
`DigitPairCurrent … .writer` at that terminal state, for every complete pair, for chain cuts and for
arbitrary `after`; it holds from the third completion on (the first and second fail:
`run7.py … 1` fails in most tests, `… 2` in 3 of 360).

Consumer: `Leader/L3/Width/DigitWriterCurrentChain.lean`.
-/

namespace L3.WriterCurrent

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.ValueWaveClose
open L3.CohortDomination
open L3.CohortSites
open L3.Rearm
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortLedger
open L3.ValueLedger
open L3.CurrentWin
open L3.CloseCurrent
open L3.CloseEntry
open L3.WidthWave

variable {n : Nat} {ring : DirectedRing n}

/-- **The routine part of the writer window class on every clean-run state** of a complete pair of
the start: layout, ghost correspondence with the inherited base, value invariant.

Consumer: `writerEntryOfCore`. -/
theorem writerPairBaseRun (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (start : ref.State)
    (hL : WidthBoundaryDigitLayoutValues ref root start) (source : Nat)
    (hpair : DigitCompletePair ring root (piD (ref.phys start)) source
      (source + digitSpan (compileAdvice (ceilLogTwo n)))) (u : List (Fin n)) :
    WidthCohortLayout ref.toWidthDigitReference root source
        (digitSpan (compileAdvice (ceilLogTwo n)))
        (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))).1 ∧
      GhostCorrDistinct ring root DigitLane.writer source
        (digitSpan (compileAdvice (ceilLogTwo n))) (InheritedOk DigitLane.writer)
        (piD (ref.phys (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))).1))
        (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))).2 ∧
      WidthValInv ref.toWidthDigitReference root DigitLane.writer source
        (digitSpan (compileAdvice (ceilLogTwo n)))
        (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))) := by
  obtain ⟨hsrc, hend, hlay⟩ := pairLayoutStart ref hn root start hL source hpair
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  have h0 : WidthCohortLayout ref.toWidthDigitReference root source
        (digitSpan (compileAdvice (ceilLogTwo n)))
        (start, digitAuditInitial (piD (ref.phys start))).1 ∧
      GhostCorrDistinct ring root DigitLane.writer source
        (digitSpan (compileAdvice (ceilLogTwo n))) (InheritedOk DigitLane.writer)
        (piD (ref.phys (start, digitAuditInitial (piD (ref.phys start))).1))
        (start, digitAuditInitial (piD (ref.phys start))).2 ∧
      WidthValInv ref.toWidthDigitReference root DigitLane.writer source
        (digitSpan (compileAdvice (ceilLogTwo n)))
        (start, digitAuditInitial (piD (ref.phys start))) :=
    ⟨hlay, ghostCorrDistinctInitial ring root _ _ _ _,
      ⟨valCorrInitial ring root _ _ _ _, exportValInitial ring root _ _ _ _,
        useValInitial ring root _ _ _ _, ledgerOkInitial ring root _ _ _ _⟩⟩
  generalize (start, digitAuditInitial (piD (ref.phys start))) = y at h0
  induction u generalizing y with
  | nil => exact h0
  | cons e rest ih =>
    apply ih
    obtain ⟨hl, hg, hv⟩ := h0
    obtain ⟨hl', hg'⟩ := widthGhostCorrDistinctStep ref.toWidthDigitReference ref.singletonFixed hn
      root DigitLane.writer source _ hR hsrc hend (InheritedOk DigitLane.writer) y hl hg e
    exact ⟨hl', hg', widthValInvStep ref.toWidthDigitReference ref.singletonFixed hn root
      DigitLane.writer source _ hR hsrc hend y hl hv e⟩

/-- A fifth next completion terminates after `after`.

Consumer: `writerEntryOfCore`. -/
theorem fiveAfterTerminal {c : Compiled} (A : DigitAudit c n) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (after : Nat) (T : DigitTerminal c n)
    (h : DigitFiveCompletions ring A root source target lane after T) : after < T.time := by
  obtain ⟨t1, t2, t3, t4, h1, h2, h3, h4, h5⟩ := h
  have a1 := h1.2.1
  have a2 := h2.2.1
  have a3 := h3.2.1
  have a4 := h4.2.1
  have a5 := h5.2.1
  omega

/-- **The new content of the writer entry fact**: at the terminal state of the fifth next writer
completion of a complete pair after `after`, on the clean run, the masked writer lane is in the
cycle class and the aged window holds at `after`.  Data: `run6.py`, `run7.py` (the consequence
`DigitPairCurrent`); the comparison analogue is `L3.CloseEntry.EntryCore` (also not produced).

Consumer: `writerEntryOfCore`. -/
def WriterEntryCore (ref : WidthDigitReference ring) : Prop :=
  ∀ (root : Fin n) (start : ref.State) (u : List (Fin n)) (source after : Nat)
    (T : DigitTerminal (compileAdvice (ceilLogTwo n)) n),
    ref.start start → ref.singleton root start →
    DigitCompletePair ring root (piD (ref.phys start)) source
      (source + digitSpan (compileAdvice (ceilLogTwo n))) →
    DigitFiveCompletions ring
      (u.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2
      root source (source + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.writer after T →
    T.time =
      (u.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2.clock →
    (∃ (j : Nat) (g : (Nat → Nat) × Nat) (o : Nat),
      CohortCycIn (digitSpan (compileAdvice (ceilLogTwo n))) j
        (cohortProj ring root DigitLane.writer source (digitSpan (compileAdvice (ceilLogTwo n)))
          (piD (ref.phys (u.foldl (widthDigitAuditNext ref)
            (start, digitAuditInitial (piD (ref.phys start)))).1))) g o) ∧
    WinAge ring root DigitLane.writer source (digitSpan (compileAdvice (ceilLogTwo n))) after
      (cohortProj ring root DigitLane.writer source (digitSpan (compileAdvice (ceilLogTwo n)))
        (piD (ref.phys (u.foldl (widthDigitAuditNext ref)
          (start, digitAuditInitial (piD (ref.phys start)))).1)))
      (u.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2

/-- **The entry of the writer window class from its new content** (any boundary reference).

Consumer: `writersCurrentOfCore` (WidthDigitWriterCurrentChain). -/
theorem writerEntryOfCore (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hcore : WriterEntryCore ref.toWidthDigitReference)
    (root : Fin n) (start : ref.State) (u : List (Fin n)) (source after : Nat)
    (T : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hst : ref.start start) (hs : ref.singleton root start)
    (hpair : DigitCompletePair ring root (piD (ref.phys start)) source
      (source + digitSpan (compileAdvice (ceilLogTwo n))))
    (hT : DigitFiveCompletions ring
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2
      root source (source + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.writer after T)
    (hTc : T.time =
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2.clock) :
    WriterPairWin ref.toWidthDigitReference root source
      (digitSpan (compileAdvice (ceilLogTwo n))) after
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))) := by
  obtain ⟨root0, hs0, hL⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root0 :=
    (ref.singletonFixed root0 start hs0).2.1 root (ref.singletonFixed root start hs).1
  subst hr
  obtain ⟨hl, hg, hv⟩ := writerPairBaseRun ref hn root start hL source hpair u
  obtain ⟨hcyc, hage⟩ := hcore root start u source after T hst hs hpair hT hTc
  have hlt := fiveAfterTerminal _ root source _ DigitLane.writer after T hT
  exact ⟨hl, hg, hv, hcyc, hage, by rw [← hTc]; exact Nat.le_of_lt hlt⟩

end L3.WriterCurrent

#print axioms L3.WriterCurrent.writerPairBaseRun
#print axioms L3.WriterCurrent.writerEntryOfCore
