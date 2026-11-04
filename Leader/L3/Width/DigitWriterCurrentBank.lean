import Leader.L3.Width.DigitWriterCurrentEntry
import Leader.L3.Width.DigitWriterCurrentChain
import Leader.L3.Bank.RepairDigitEntryBridge
import Leader.L3.Bank.RepairDigitBoundaryClean
import Leader.L3.Width.DigitFirstZero

/-!
# Writer currentness at BANK: the cycle-class half of the entry content is proved

`WriterEntryCore` (`WidthDigitWriterCurrentEntry`) has two conjuncts at the terminal state of the
fifth next writer completion: the masked writer lane is in the cycle class `CohortCycIn`, and the
aged window `WinAge … after` holds.  For the BANK reference the first conjunct is the group 6
bridge `L3.DigitEntryBridge.strictCompletionCyc` (a recorded completion puts the lane in `CohortCyc`
at every later state of the run from a layout state), whose layout hypothesis comes from
`pairLayoutStart` and `widthCohortLayoutBank`.  This module proves that, and leaves exactly the
second conjunct:

* `WriterAgeCore ref`: the aged-window conjunct alone;
* `writerEntryCoreOfAge`: at BANK, `WriterAgeCore ⇒ WriterEntryCore`.

Data for the residual conjunct: `research/lean-l3/wip/r10c-values/run8.py` (adversarial schedulers)
finds, for every recorded writer completion `c_i` of every complete pair, at most one earlier
completion later than the oldest sample in the window of `c_i` (q ≤ 1 in 5 800 completions), so the
fifth completion after any `after` has an aged window (it needs q ≤ 3).

Consumer: `writersCurrentOfCore` (WidthDigitWriterCurrentChain) via `WriterEntryCore`.
-/

namespace L3.WriterCurrent

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.CohortDomination
open L3.CohortSites
open L3.Rearm
open L3.CurrentWin
open L3.CloseEntry
open L3.DigitEntryBridge
open L3.DigitEntryPhase
open L3.ValueWaveClose

variable {n : Nat} {ring : DirectedRing n}

/-- **The aged-window half of the writer entry content**: at the terminal state of the fifth next
writer completion of a complete pair after `after` on the clean run, `WinAge … after` holds.  The
only unproved part of `WriterEntryCore` at BANK.

Consumer: `writerEntryCoreOfAge`. -/
def WriterAgeCore (ref : WidthDigitReference ring) : Prop :=
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
    WinAge ring root DigitLane.writer source (digitSpan (compileAdvice (ceilLogTwo n))) after
      (cohortProj ring root DigitLane.writer source (digitSpan (compileAdvice (ceilLogTwo n)))
        (piD (ref.phys (u.foldl (widthDigitAuditNext ref)
          (start, digitAuditInitial (piD (ref.phys start)))).1)))
      (u.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2

/-- **The cycle-class half at BANK.**  For the BANK reference, at the end of a clean run in which a
complete pair has a recorded writer completion (in particular after five next completions), the
masked writer lane is in the cycle class.

Consumer: `writerEntryCoreOfAge`. -/
theorem writerCycOfBank (hn : 5 ≤ n) (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (start : BankReferenceState ring hbank) (u : List (Fin n)) (source after : Nat)
    (T : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hst : (bankWidthBoundaryReference ring hn hbank).start start)
    (hs : (bankWidthBoundaryReference ring hn hbank).singleton root start)
    (hpair : DigitCompletePair ring root (piD start.val.1) source
      (source + digitSpan (compileAdvice (ceilLogTwo n))))
    (hT : DigitFiveCompletions ring
      (u.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))).2
      root source (source + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.writer after T) :
    ∃ (j : Nat) (g : (Nat → Nat) × Nat) (o : Nat),
      CohortCycIn (digitSpan (compileAdvice (ceilLogTwo n))) j
        (cohortProj ring root DigitLane.writer source (digitSpan (compileAdvice (ceilLogTwo n)))
          (piD (u.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
            (start, digitAuditInitial (piD start.val.1))).1.val.1)) g o := by
  let bref := bankWidthBoundaryReference ring hn hbank
  obtain ⟨root0, hs0, hL⟩ := widthCleanBoundaryRoot bref start hst
  have hr : root = root0 :=
    (bref.singletonFixed root0 start hs0).2.1 root (bref.singletonFixed root start hs).1
  subst hr
  obtain ⟨hsrc, hend, hlay⟩ := pairLayoutStart bref hn root start hL source hpair
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  obtain ⟨t1, t2, t3, t4, -, -, -, -, h5⟩ := hT
  have hcyc := strictCompletionCyc ring hn hbank root DigitLane.writer source
    (digitSpan (compileAdvice (ceilLogTwo n))) hR hsrc hend start hlay u rfl 0 T h5.1
  exact cycClassIn hcyc 0 |>.elim fun g hg => hg.elim fun o ho => ⟨0, g, o, ho⟩

/-- **At BANK the writer entry content is its aged-window half.**

Consumer: `writersCurrentOfCore` (WidthDigitWriterCurrentChain) at the BANK reference. -/
theorem writerEntryCoreOfAge (hn : 5 ≤ n) (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hage : WriterAgeCore (bankWidthDigitReference ring hn hbank)) :
    WriterEntryCore (bankWidthDigitReference ring hn hbank) := by
  intro root start u source after T hst hs hpair hT hTc
  exact ⟨writerCycOfBank hn hbank root start u source after T hst hs hpair hT,
    hage root start u source after T hst hs hpair hT hTc⟩

open L3.WriterValueCuts in
/-- **`DigitWritersCurrent` at the BANK writer comparison cut, from the aged-window half alone.**

Consumer: the BANK case of the writer comparison certificate (second conjunct), through the
physical value step. -/
theorem writersCurrentOfAgeBank (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hage : WriterAgeCore (bankWidthDigitReference ring hn hbank))
    (start : BankReferenceState ring hbank) (word : List (Fin n)) (root : Fin n)
    (z : BankReferenceState ring hbank)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (retired restart : Nat)
    (hst : (bankWidthDigitReference ring hn hbank).start start)
    (hfold : word.foldl (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (start, digitAuditInitial (piD ((bankWidthDigitReference ring hn hbank).phys start))) =
      (z, audit))
    (hW : WFixedRoot ring root (piW ((bankWidthDigitReference ring hn hbank).phys z)))
    (hrec : WidthWriterValueReceipts ring root audit retired restart) :
    ∃ (structural first baseCut last : Nat) (cuts : List (Nat × Nat)),
      DigitValueChain ring root audit structural first baseCut last restart cuts ∧
      DigitWritersCurrent ring root audit
        (piD ((bankWidthDigitReference ring hn hbank).phys z)) audit.current structural
        audit.clock cuts :=
  writersCurrentOfCore (bankWidthBoundaryReference ring hn hbank) hn
    (writerEntryCoreOfAge hn hbank hage) start word root z audit retired restart hst hfold
    hW hrec

end L3.WriterCurrent

#print axioms L3.WriterCurrent.writersCurrentOfAgeBank
#print axioms L3.WriterCurrent.writerCycOfBank
#print axioms L3.WriterCurrent.writerEntryCoreOfAge
