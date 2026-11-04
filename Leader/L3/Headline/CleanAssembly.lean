import Leader.L3.Headline.RenewalCleanSmall
import Leader.L3.Width.DigitFirstZero
import Leader.L3.Width.DigitWriterStage
import Leader.L3.Width.DigitWriterCore
import Leader.L3.Small.ReaderFoldClean
import Leader.L3.Bank.InheritedArmedRows
import Leader.L3.Bank.InheritedProgress
import Leader.L3.Bank.WindowThreshold
import Leader.L3.StageM.Compare
import Leader.L3.StageM.Pair
import Leader.L3.StageM.Entry
import Leader.L3.StageM.EntryCyc
import Leader.L3.Top.ClockEntrance
import Leader.L3.Width.DigitCloseOrder
import Leader.L3.Width.DigitWriterOrderedWave
import Leader.L3.Width.DigitWriterOrderedClose

/-!
The clean headline from the open rows of both branches.

`l3HeadlineOfCleanBranches`: `L3Headline ring` at 5 ≤ n from
* old Q9 (`StageRequestMissingClock`);
* the R10c digit premises on the writer-lane cut family (`L3.WriterValueCuts`:
  the values-stable and comparison cuts carry the first WRITER structural cut,
  not the both-lane one; the comparison lane enters only through the restarted
  comparison-ready cut), stated ONCE at the digit reference of the band
  (`L3.WidthDigit.bandWidthDigitReference`, clean start): the writer
  comparison-entry certificate, at the cut the quiet class
  `L3.DigitQuiet.WidthDigitQuiet` (`QDigit` is false there and is reached only
  at zero dirty count, as in the paper), and for every root and first delimiter
  the one-letter law `L3.DigitQuiet.QuietStepLaw` (the ordered receipt conversion
  `L3.WriterOrdered.WidthWriterOrderedReceiptsClose` is proved,
  `L3.WriterOrderedClose.bandWriterOrderedClose`); the clean core is
  `L3.WriterOrderedWave.writerDigitHalfOfBandOrdered`.  Band
  charges: BANK micro-charges; SMALL the concrete slice tables
  `smallDigitZeroTable`, `smallDigitWaveTable`, `smallDigitCompareTable`,
  fitted by `smallDigitTablesFit`; the first-zero clock is proved on both bands
  (BANK `widthDigitFirstZeroClockBankOfReference`, SMALL `bandWidthFirstZeroClockSmall`);
* the value wave: on BANK the per-pair exponential moment
  `WidthStrictPairMoment` (`E[z^T] ≤ 40`, `z = N/(N-1)`,
  `N = widthPairMomentWidth n = n (2 C_r + 1)`; composed by Lemma e-max
  `widthStructuralClockOfMoments`) and the entry clock
  (`bankWriterValueWaveOfMoments`, total fitted by `momentLedgerFit`); on
  SMALL the writer-lane moment `WidthWriterPairMoment` (Lemma e-max on the
  writer lane with exact Jensen, slice certificate `smallWriterCertificate`,
  slot `smallDigitWriterTable`) and the entry clock from the writer cut to
  `P' 0` at `6 n (5 R + 2 + L)` (slot `smallDigitEntryTable`)
  (`smallWaveClockOfWriter`); on both bands the wave after the entry is
  `L3.WidthWave.widthCleanWaveAfterEntry`;
* the comparison lane: on SMALL Lemma e-max on the comparison lane restarted at
  the digit-stability cut (`smallComparisonClockOfMoments`: per-pair moment
  `WidthComparePairMoment` and `WidthComparisonClose`, slot
  `smallDigitCompareTable` = the certified writer coefficient); on BANK the
  writer comparison clock at the micro-charge;
* the boundary stage is proved on both bands: BANK
  `widthDigitBoundaryStageBank`, SMALL `bandWidthBoundaryStageSmall` (slice
  coefficient `widthBoundarySlice`);
* BANK: the R11 K-head threshold `BankCutGenuineHeadThreshold` is proved
  (`L3.BankWindow.bankCutGenuineHeadThresholdAll`, from the window exactness
  step `bankWindowExactStep`); the R7 progress alternative
  `BankInheritedProgressAlternative` is proved
  (`bankInheritedProgressAlternativeHolds`, BankInheritedProgress);
* SMALL: the fold is `smallCleanReaderFoldSoundProved`.

R7 enters through its merged reduction (A and B rows proved,
`bankInheritedRetirementStageOfProgress`).  The installed stage is stated
on the start class `BankInheritedRootedStart`, which also asks the seed
to avoid the OLD target; its proof discards that conjunct.  The clean R14
quantifies over seeds outside Gclean, so the same proof is restated here on
the start class without that conjunct (`bankCleanInheritedRetirementStage`);
its progress input is `bankInheritedProgressAlternativeHolds`.
-/

namespace L3.HeadlineCleanAssembly

open L3
open L3.HeadlineRenewal
open L3.HeadlineRenewalCleanBank
open L3.HeadlineRenewalCleanSmall
open L3.RenewalReferenceClock
open L3.SmallFinishClean
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Every renewal start of the valid BANK reference, with no condition on
the target.  Consumer: `bankCleanInheritedRetirementStage`. -/
def BankCleanRootedStart {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ seed : RootedSeed ring,
    z = (bankValidRootedReferenceData ring hbank).referenceStart seed

/-- R7 (sigma_B) on every renewal start, from the progress alternative
alone: the proof of `bankInheritedRetirementStageOfEdgeRows` with the
proved A and B rows.  Consumer: `bankCleanDigitStageRootedRenewalCost`. -/
theorem bankCleanInheritedRetirementStage
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hC : BankInheritedProgressAlternative ring hbank) :
    StageInheritedAuthorityExtinction
      (bankValidRootedReferenceData ring hbank).referenceNext
      (BankCleanRootedStart ring hbank)
      (fun z => headlineRooted ring z.val.1 ∧
        InheritedAuthorityExtinct ring hbank z)
      (ceilLogTwo n) := by
  have hA : BankInheritedNonarmedEdgeRows ring hbank :=
    bankInheritedNonarmedEdgeRowsOfLocal ring hn hbank
      (bankInheritedNonarmedLocalRowsHolds ring hn hbank)
  have hB : BankInheritedArmedEdgeRows ring hbank :=
    bankInheritedArmedEdgeRowsHolds ring hn hbank
  intro z hz
  obtain ⟨seed, hstart⟩ := hz
  have hreach : BankInheritedReachable ring hbank z := by
    rw [hstart]
    exact bankInheritedReachableStart ring hbank seed
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (bankValidRootedReferenceData ring hbank).referenceNext
    (fun u => headlineRooted ring u.val.1 ∧
      InheritedAuthorityExtinct ring hbank u)
    ring.hn z
    (headlineInheritedRate (ceilLogTwo n) * n ^ 2)).2
  intro T
  have hcompare :=
    L3.Counter.resetClockCostLeOfStoppedSimulation
      (bankValidRootedReferenceData ring hbank).referenceNext
      (bankValidRootedReferenceData ring hbank).referenceNext
      (fun u => headlineRooted ring u.val.1 ∧
        InheritedAuthorityExtinct ring hbank u)
      (fun u => bankInheritedStateAtomCount ring hbank u = 0)
      (fun u v => u = v ∧ BankInheritedReachable ring hbank u)
      (fun u v huv hzero => by
        rcases huv with ⟨rfl, hu⟩
        obtain ⟨s, pre, hrep⟩ := hu.2
        exact ⟨hu.1,
          bankInheritedZeroExtinct
            ring hn hbank s pre u hrep hzero⟩)
      (fun u v e huv _ _ => by
        rcases huv with ⟨rfl, hu⟩
        exact ⟨rfl, bankInheritedReachableStep
          ring hn hbank u hu e⟩)
      z z ⟨rfl, hreach⟩ T
  have hpotential :=
    L3.Prob.costNumerator_le_of_potential_on
      (bankValidRootedReferenceData ring hbank).referenceNext
      (fun u => bankInheritedStateAtomCount ring hbank u = 0)
      (BankInheritedReachable ring hbank)
      (bankInheritedPotential ring hbank)
      (fun u hu _ e =>
        bankInheritedReachableStep ring hn hbank u hu e)
      (fun u hu hnonzero =>
        bankInheritedBellmanOfEdgeRows
          ring hbank hA hB hC u hu hnonzero)
      z hreach T
  have hstartBound :
      bankInheritedPotential ring hbank z ≤
        (116 * (compileAdvice (ceilLogTwo n)).b + 232) * n ^ 2 := by
    rw [hstart]
    exact bankInheritedPotentialStartLe ring hbank seed
  have hcost :=
    Nat.le_trans hcompare
      (Nat.le_trans hpotential
        (Nat.mul_le_mul_left (n ^ T) hstartBound))
  rw [bankInheritedHeadlineRateBankEq
    (ceilLogTwo n) hbank]
  exact hcost

/-- The BANK clean R14 from the clean digit half and the R11 K-head
threshold; the R7 progress alternative is `bankInheritedProgressAlternativeHolds`.
Consumer: `l3HeadlineOfCleanBranches`. -/
theorem bankCleanDigitStageRootedRenewalCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hdigit : BankCleanDigitHalfOnDrain ring hbank)
    (hthreshold : L3.BankRetryCoverage.BankCutGenuineHeadThreshold ring hbank) :
    StageCleanRootedRenewalCost ring :=
  bankCleanStageRootedRenewalCost ring hn hbank hdigit hthreshold
    (BankCleanRootedStart ring hbank)
    (fun seed _ => ⟨seed, rfl⟩)
    (bankCleanInheritedRetirementStage ring hn hbank
      (bankInheritedProgressAlternativeHolds ring hn hbank))

/-- The SMALL clean R14 from the digit half alone (fold proved).
Consumer: `l3HeadlineOfCleanBranches`. -/
theorem smallCleanDigitStageRootedRenewalCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hdigit : SmallCleanDigitHalf ring) :
    StageCleanRootedRenewalCost ring :=
  smallCleanStageRootedRenewalCost ring hn hsmall
    (smallCleanReaderFoldSoundProved ring hn) hdigit

/-- The top conditional headline.  Premises are exactly the open rows:
old Q9; the R10c digit premises once, at the digit reference of the band
(`bandWidthDigitReference`, clean start) with the band charges; on SMALL
the writer-lane moment, the entry clock after the writer cut, and the
comparison-lane moment after the digit-stability cut (the comparison close is
proved, `L3.CloseOrder.bandWidthComparisonClose`);
the one-letter law `hlaw` of the quiet class; at the band reference the writer certificate
`hcert` (the ordered receipt conversion
`L3.WriterOrdered.WidthWriterOrderedReceiptsClose` is proved,
`L3.WriterOrderedClose.bandWriterOrderedClose`; `WidthWriterReceiptsClose` is false on
reached states, DESIGN-MOTIVATIONS 2026-11-02 "ordered receipts"); on
BANK the Lemma e-max per-pair moment, the entry clock, the writer comparison
clock at the micro-charge and the R11 threshold (R7 is proved; the pin after a strict writer
completion is proved, `L3.StageMEntryCyc.bandPinAfterStrict`).  Consumer: the L3 board (H1); each premise is
replaced by its producer when that lands. -/
theorem l3HeadlineOfCleanBranches {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hlaw : ∀ (root : Fin n) (first : Nat),
      L3.DigitQuiet.QuietStepLaw (c := compileAdvice (ceilLogTwo n)) ring root first)
    (hcert : L3.WriterValueCuts.WidthWriterComparisonCertificate
      (L3.WidthDigit.bandWidthDigitReference ring hn))
    :
    L3Headline ring := by
  have hord : L3.WriterOrdered.WidthWriterOrderedReceiptsClose
      (L3.WidthDigit.bandWidthDigitReference ring hn) :=
    L3.WriterOrderedClose.bandWriterOrderedClose ring hn
  have hcmpClose : L3.CompareStage.WidthComparisonClose
      (L3.WidthDigit.bandWidthDigitReference ring hn) :=
    L3.CloseOrder.bandWidthComparisonClose ring hn
  have hpin : L3.StageMEntry.WidthPinAfterStrict (L3.WidthDigit.bandWidthDigitReference ring hn) :=
    L3.StageMEntryCyc.bandPinAfterStrict ring hn
  have hboundary : (compileAdvice (ceilLogTwo n)).useSmall = true →
      L3.WidthDigit.WidthDigitBoundaryStage (L3.WidthDigit.bandWidthDigitReference ring hn)
        (L3.WidthDigit.widthDigitBandCharge n L3.WidthDigit.widthBoundarySlice
          (bankRepairDigitBoundaryMicroCharge n)) :=
    L3.WidthDigit.bandWidthBoundaryStageSmall ring hn _ (Nat.le_refl _)
  have hcompare : L3.WriterValueCuts.WidthWriterComparisonClock
      (L3.WidthDigit.bandWidthDigitReference ring hn)
      (L3.WidthDigit.widthDigitBandCharge n L3.WidthDigit.smallDigitCompareTable
        (bankRepairDigitComparisonMicroCharge n)) := by
    cases hb : (compileAdvice (ceilLogTwo n)).useSmall with
    | true =>
        exact L3.CompareStage.smallComparisonClockOfMoments ring hn hb
          (L3.StageMCompare.smallCmpMoment ring hn hb) hcmpClose
    | false =>
        rw [L3.WidthDigit.widthDigitBandChargeBank _ _ hb,
          L3.WidthDigit.bandWidthDigitReferenceBank ring hn hb]
        have hcb := hcmpClose
        rw [L3.WidthDigit.bandWidthDigitReferenceBank ring hn hb] at hcb
        exact L3.StageMCompare.bankCompareOfClose ring hn hb hcb
  obtain ⟨hbankDigit, hsmallDigit⟩ :=
    L3.WriterOrderedWave.writerDigitHalfOfBandOrdered ring hn L3.WidthDigit.widthBoundarySlice
      L3.WidthDigit.smallDigitZeroTable L3.WidthDigit.smallDigitWaveTable
      L3.WidthDigit.smallDigitCompareTable (fun hs => L3.WidthDigit.smallDigitTablesFit hn hs)
      hboundary (L3.WidthDigit.bandWidthFirstZeroClockSmall ring hn)
      (fun hs => L3.WriterOrderedWave.smallWaveClockOfWriterOrdered ring hn hs
        (L3.StageMPair.smallWriterPairMoment ring hn hs) hpin hord)
      (L3.StageMPair.bankHPair ring hn) hpin hord hcompare hlaw hcert
  have hcost : StageCleanRootedRenewalCost ring := by
    cases hb : (compileAdvice (ceilLogTwo n)).useSmall with
    | true =>
        exact smallCleanDigitStageRootedRenewalCost ring hn hb
          (hsmallDigit hb)
    | false =>
        exact bankCleanDigitStageRootedRenewalCost ring hn hb
          (hbankDigit hb) (L3.BankWindow.bankCutGenuineHeadThresholdAll ring hn hb)
  exact l3HeadlineOfRequestAndCleanRenewal ring hn
    (L3.stageRequestMissingClockProved ring hn) hcost

end L3.HeadlineCleanAssembly

#print axioms L3.HeadlineCleanAssembly.bankCleanInheritedRetirementStage
#print axioms L3.HeadlineCleanAssembly.bankCleanDigitStageRootedRenewalCost
#print axioms L3.HeadlineCleanAssembly.smallCleanDigitStageRootedRenewalCost
#print axioms L3.HeadlineCleanAssembly.l3HeadlineOfCleanBranches
