import Leader.L3.StageM.Moment
import Leader.L3.Width.PacketMomentTailLab
import Leader.L3.Width.PacketMomentCompare
import Leader.L3.Width.DigitCompareRestart

/-!
# The comparison-lane stage obligation: the tail stage, then Stage M

The pre-attempt stage of a pair is the distinguished-tail stage (`widthTailLabMoment`, to the
labelled aligned source after the cut, `w^{tailBudget R}`, `tailBudget R ≤ C_R`) followed by
Stage M (`L3.StageMMoment.stageMStage`, to the completion or the attempt cut, `w^{R(4R+4)}`,
`R(4R+4) ≤ 2 C_R`). Their composition (`tailStageM`) is the stage premise with `B ≤ 3 C_R`.

* `tailStageM`: from the run invariant at a clock not before the cut.
* `widthCmpPairStageWHolds`: `WidthCmpPairStageW` at every boundary reference (the cut is the
  restart, `restart ≤ clock` by `stableRunRestartLe`; the run invariant by `widthStableRunInv`).
* `smallCmpMoment`: the SMALL headline premise `hcmpMomentSmall` (`smallComparePairMoment`).
* `bankCompareOfClose`: the BANK headline premise `hcompareBank` from `WidthComparisonClose` at
  BANK alone. The existing `hcompareBankOfStage` takes the BANK stage `CmpPairStageW`, whose
  target `LaneCutC` is the mobile-free cut; this goes through `widthComparePairMoment` at
  `bankWidthBoundaryReference` instead (its `stageFactor` needs `C ≥ 20` only).

Consumer: `hcmpMomentSmall` and `hcompareBank` of `l3HeadlineOfCleanBranches`.
-/

namespace L3.StageMCompare

set_option autoImplicit false

open L3
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.WriterValueCuts
open L3.PairMomentPremise
open L3.WidthDigit
open L3.CohortSites
open L3.PacketMomentRelease
open L3.PacketMomentPrep
open L3.PacketMomentGroupLabels
open L3.CompareStage
open L3.WidthPacketMoment
open L3.WidthPacketMomentAudit
open L3.WidthPacketMomentGroupCompletion
open L3.WidthPacketMomentCutLabels
open L3.WidthPacketMomentCutAttempt
open L3.WidthPacketMomentCutEntry
open L3.WidthPacketMomentTail
open L3.WidthPacketMomentTailLab
open L3.WidthPacketMomentCompare
open L3.StageMMoment

/-- **The stage budget**: `tailBudget R + R(4R+4) ≤ 3 C_R`. Consumer:
`widthCmpPairStageWHolds`. -/
theorem stageBudgetLe (R : Nat) :
    tailBudget R + R * (4 * R + 4) ≤ 3 * bankRepairDigitPairClock R := by
  have h1 := tailBudgetLe R
  have h2 := stageMBudget R
  omega

/-- **The tail stage, then Stage M**: from the run invariant of a pair at a clock not before the
cut, the completion or the attempt cut is reached with `E[z^T] ≤ w^{tailBudget R + R(4R+4)}`.
Consumer: `widthCmpPairStageWHolds`. -/
theorem tailStageM {n : Nat} (ring : DirectedRing n) (ref : WidthBoundaryReference ring)
    (hn : 5 ≤ n) (root : Fin n) (lane : DigitLane) (src R cut : Nat) (hR : 2 ≤ R)
    (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat) (hN : n < N)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hI : WidthRunInv ring ref root lane src R x) (hc : cut ≤ x.2.clock) :
    MomentBoundQ (widthDigitAuditNext ref.toWidthDigitReference)
      (fun y => WidthPairDoneC ring ref root lane src R cut y ∨
        WidthLaneCutC ring ref root lane src R cut y) N
      (N ^ (tailBudget R + R * (4 * R + 4)))
      ((N - n) ^ (tailBudget R + R * (4 * R + 4))) x := by
  have hT := widthTailLabMoment ring ref hn root lane src R cut hR hsrc hend N hN x hI.1.1 hc
  have hK := momentKeep (widthDigitAuditNext ref.toWidthDigitReference) _
    (WidthRunInv ring ref root lane src R) N _ _
    (fun y e hy => widthRunInvStep ring ref hn root lane src R hR hsrc hend y hy e) x hI hT
  have hS := momentSeq (widthDigitAuditNext ref.toWidthDigitReference) _ _ N _ _ _ _ x
    (Nat.pow_le_pow_left (Nat.sub_le N n) _)
    (fun y hy => stageMStage ring ref hn root lane src R cut hR hsrc hend N hN y hy.2.1.1
      hy.2.1.2.1 hy.1.1) hK
  rw [Nat.pow_add, Nat.pow_add]
  exact hS

/-- **The comparison-lane stage obligation holds** at every boundary reference, with
`B = tailBudget r + r(4r+4) ≤ 3 C_r`. Consumer: `smallCmpMoment`, `bankCompareOfClose`. -/
theorem widthCmpPairStageWHolds {n : Nat} (ring : DirectedRing n)
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    : WidthCmpPairStageW ring ref := by
  refine ⟨tailBudget (digitSpan (compileAdvice (ceilLogTwo n))) +
      digitSpan (compileAdvice (ceilLogTwo n)) * (4 * digitSpan (compileAdvice (ceilLogTwo n)) + 4),
    stageBudgetLe _, ?_⟩
  intro root restart i first x hx hf hend _
  obtain ⟨h2, hI⟩ := widthStableRunInv ring ref hn root restart x hx first hf i hend
  have h3 := widthSpanThree hn
  exact tailStageM ring ref hn root DigitLane.comparison _ _ restart (by omega) h2 hend _
    (pairWidthGt _ hn) x hI
    (L3.CompareRestart.stableRunRestartLe ref.toWidthDigitReference root restart x hx)

/-- **The SMALL headline premise `hcmpMomentSmall`.** Consumer: `hcmpMomentSmall` of
`l3HeadlineOfCleanBranches`. -/
theorem smallCmpMoment {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hs : (compileAdvice (ceilLogTwo n)).useSmall = true)
    :
    WidthComparePairMoment (bandWidthDigitReference ring hn) (widthPairMomentWidth n) :=
  smallComparePairMoment ring hn hs
    (widthCmpPairStageWHolds ring (smallWidthBoundaryReference ring hn hs) hn)

/-- **The BANK headline premise `hcompareBank`** from the comparison close at BANK alone (the
per-pair moment through `widthComparePairMoment` at `bankWidthBoundaryReference`). Consumer:
`hcompareBank` of `l3HeadlineOfCleanBranches`. -/
theorem bankCompareOfClose {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hclose : WidthComparisonClose (bankWidthDigitReference ring hn hbank)) :
    WidthWriterComparisonClock (bankWidthDigitReference ring hn hbank)
      (bankRepairDigitComparisonMicroCharge n) :=
  bankRepairDigitChargedMono _ _ _ (L3.PacketMomentCompareBank.cmpChargeLe hbank)
    (widthComparisonStageOfMoments (bankWidthDigitReference ring hn hbank) hn
      (widthPairMomentWidth n) (widthPairMomentWidth n * (ceilLogTwo n + 6))
      (widthPairMomentWidthTwo (by omega))
      (widthComparePairMoment ring (bankWidthBoundaryReference ring hn hbank) hn
        (widthCmpPairStageWHolds ring (bankWidthBoundaryReference ring hn hbank) hn))
      hclose (L3.PacketMomentCompareBank.cmpCert hn))

end L3.StageMCompare

#print axioms L3.StageMCompare.stageBudgetLe
#print axioms L3.StageMCompare.tailStageM
#print axioms L3.StageMCompare.widthCmpPairStageWHolds
#print axioms L3.StageMCompare.smallCmpMoment
#print axioms L3.StageMCompare.bankCompareOfClose
