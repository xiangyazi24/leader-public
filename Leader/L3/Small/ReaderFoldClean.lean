import Leader.L3.Width.ReaderFold
import Leader.L3.Small.FinishClean
import Leader.L3.Small.ReaderClean

/-!
# SMALL clean reader fold soundness (E.G22)

`smallCleanReaderFoldSoundProved : SmallCleanReaderFoldSound ring` at
5 ≤ n: at every done cut of a genuine decorated phiR run from a SMALL
W-accepted start (clean word at a fixed root), the reader accepts with the
five-fold validity predicate and the all-future certificate QReader.

Proof: the width-generic clean fold of WidthReaderFold
(`widthCleanRepairCloseFoldAt`, rows from `widthCleanRepairCloseRowsAtOfValues`)
at `2 ≤ n` and `0 < t` (`L3.ClosureFull.adviceWidthPositive`), with the W start
given by the reader projection `piR start.1`; the fixed root and the five
clean-worker word equations come from `SmallCleanWord`.  No SMALL band fact
beyond `5 ≤ n` is used.
-/

namespace L3.SmallFinishClean

open L3
open L3.HeadlineRenewal
open L3.SmallRenewal
open L3.SmallFinishRepair
open L3.SmallRepairStages
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- E.G22 on SMALL: the clean reader fold is sound at every done cut of
a run from a W-accepted SMALL start.  Consumer:
`smallCleanReaderHalfStageOfRetirementAndFold` (with
`smallCleanResidentRetirementClockProved`), hence the SMALL clean R
half-stage. -/
theorem smallCleanReaderFoldSoundProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    SmallCleanReaderFoldSound ring := by
  intro start finish word initial control hw _hactual hinit hrun hdone hnames
  obtain ⟨root, hfix, hvals, _⟩ := hw.2.2
  have hrows := widthCleanRepairCloseRowsAtOfValues ring hn (by omega)
    (L3.ClosureFull.adviceWidthPositive (ceilLogTwo n)) (piR start.1) root hfix hvals
  exact widthCleanRepairCloseFoldAt ring (by omega)
    (L3.ClosureFull.adviceWidthPositive (ceilLogTwo n)) (piR start.1) (piR finish.1)
    hrows word initial control hinit hrun hdone hnames

/-- The SMALL clean R half-stage with no open premise: E.G19 retirement
(`smallCleanResidentRetirementClockProved`) and E.G22 fold soundness
(`smallCleanReaderFoldSoundProved`).  Consumer: the SMALL clean finish
composition (the R stage of the six-stage SMALL clean finish). -/
theorem smallCleanReaderHalfStageProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    BankRepairHalfStage (renewalSmallNext ring)
      (SmallCleanWAcceptedOnGuard ring)
      (SmallCleanReader ring)
      (2 * smallRepairWidth n) :=
  smallCleanReaderHalfStageOfRetirementAndFold ring
    (L3.SmallReaderClean.smallCleanResidentRetirementClockProved ring hn hsmall)
    (smallCleanReaderFoldSoundProved ring hn)

end L3.SmallFinishClean

#print axioms L3.SmallFinishClean.smallCleanReaderFoldSoundProved
#print axioms L3.SmallFinishClean.smallCleanReaderHalfStageProved
