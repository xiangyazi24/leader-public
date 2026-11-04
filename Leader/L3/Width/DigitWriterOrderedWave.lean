import Leader.L3.Width.DigitWriterOrdered
import Leader.L3.Width.DigitWriterCore

/-!
# The writer value-wave clocks and the digit halves from the ordered receipt conversion

`L3.WriterStage.widthWaveClockOfWriter`, `smallWaveClockOfWriter`,
`L3.WriterCore.bankWriterValueWaveOfMoments`, `bankWriterDigitHalfOfMoment` and
`writerDigitHalfOfBand` with the false premise `WidthWriterReceiptsClose` replaced by
`L3.WriterOrdered.WidthWriterOrderedReceiptsClose` (DESIGN-MOTIVATIONS 2026-11-02, "ordered
receipts").  The entry stage into the ordered block cut is an inclusion (the writer cut on SMALL,
the structural cut on BANK, from the pin after a strict writer completion), at the same charge
slot as before; the wave after it is `L3.WriterOrdered.widthOrdWaveAfterEntry`.  Charges and
fits are unchanged.
-/

namespace L3.WriterOrderedWave

set_option autoImplicit false

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.WidthDigit
open L3.DigitCohortScratch
open L3.DigitStructuralClean
open L3.PairMoment
open L3.PairMomentPremise
open L3.WriterValueCuts
open L3.WriterStage
open L3.WriterCore
open L3.WriterOrdered

variable {n : Nat} {ring : DirectedRing n}

/-- The ordered block cut is a continuation of a clean start.  Consumer:
`widthWaveClockOfWriterOrdered`, `bankWriterValueWaveOrdered`. -/
theorem reachedOfOrdEntry (ref : WidthBoundaryReference ring) (z : ref.State)
    (h : WidthOrdEntryCut ref.toWidthDigitReference 0 z) :
    ∃ (start : ref.State) (word : List (Fin n)), ref.start start ∧
      z = word.foldl ref.next start := by
  obtain ⟨root, audit, _, hrun, -⟩ := h
  exact L3.CloseKeep.reachedOfZeroRun ref root z audit hrun

/-- **The writer value-wave clock from the ordered receipts** (any boundary reference): the
writer stage of the moments, the inclusion of the writer cut in `P'' 0` (charged at the entry
slot), and the ordered wave, carrying the leader receipt (`L3.CloseKeep.leaderWave`).  Consumer:
`smallWaveClockOfWriterOrdered`. -/
theorem widthWaveClockOfWriterOrdered (ref : WidthBoundaryReference ring)
    (hn : 5 ≤ n) (N t : Nat) (hN : 2 ≤ N)
    (hmom : WidthWriterPairMoment ref.toWidthDigitReference N)
    (hcert : n / L3.ValueWaveClose.valueSpan n * 40 * (N - 1) ^ t ≤ N ^ t)
    (hpin : L3.StageMEntry.WidthPinAfterStrict ref.toWidthDigitReference)
    (hord : WidthWriterOrderedReceiptsClose ref.toWidthDigitReference) :
    WidthWriterValueWaveClock ref.toWidthDigitReference
      (2 * t + 6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) +
        bankRepairDigitValueWaveMicroCharge n) :=
  bankRepairDigitChargedWeaken ref.next _ _ _ _ _
    (fun z h => ⟨h, L3.CloseKeep.firstZeroLeader ref.toWidthDigitReference z h⟩) (fun _ h => h)
    (L3.CloseKeep.leaderWave ref hn (WidthDigitFirstZeroCut ref.toWidthDigitReference)
      (WidthDigitWriterCut ref.toWidthDigitReference)
      (WidthOrdEntryCut ref.toWidthDigitReference 0)
      (fun z => WidthDigitLeaderReceipt ref.toWidthDigitReference z →
        WidthWriterValuesStableCut ref.toWidthDigitReference z)
      (WidthWriterValuesStableCut ref.toWidthDigitReference) _ _ _
      (L3.CloseKeep.reachedOfFirstZero ref)
      (fun z h => by
        obtain ⟨root, audit, hrun, -⟩ := h
        exact L3.CloseKeep.reachedOfZeroRun ref root z audit hrun)
      (reachedOfOrdEntry ref)
      (widthWriterStageOfMoments ref.toWidthDigitReference hn N t hN hmom hcert)
      (L3.StageMEntry.chargedOfIncl _ _ _
        (writerCutOrdEntry ref.toWidthDigitReference hpin) _)
      (widthOrdWaveAfterEntry ref.toWidthDigitReference ref.singletonFixed hn _
        (fun root z audit aft h1 h2 hL => hord root z audit aft h1 h2 hL))
      (fun _ h hL => h hL))

/-- **The SMALL value-wave clock from the ordered receipts**: `smallWaveClockOfWriter` with the
ordered receipt conversion and the pin after a strict completion in place of the receipt
conversion and the entry clock.  Consumer: the SMALL wave input of
`writerDigitHalfOfBandOrdered` in `l3HeadlineOfCleanBranches`. -/
theorem smallWaveClockOfWriterOrdered (ring : DirectedRing n) (hn : 5 ≤ n)
    (hs : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hmom : WidthWriterPairMoment (bandWidthDigitReference ring hn) (widthPairMomentWidth n))
    (hpin : L3.StageMEntry.WidthPinAfterStrict (bandWidthDigitReference ring hn))
    (hord : WidthWriterOrderedReceiptsClose (bandWidthDigitReference ring hn)) :
    WidthWriterValueWaveClock (bandWidthDigitReference ring hn)
      (widthDigitBandCharge n smallDigitWaveTable (bankRepairDigitValueWaveMicroCharge n)) := by
  rw [widthDigitBandChargeSmall _ _ hs]
  rw [bandWidthDigitReferenceSmall ring hn hs] at hmom hpin hord ⊢
  have hw := widthWaveClockOfWriterOrdered (smallWidthBoundaryReference ring hn hs) hn
    (widthPairMomentWidth n) (smallDigitWriterTable (ceilLogTwo n) * n ^ 2 / 2)
    (widthPairMomentWidthTwo (by omega)) hmom
    (L3.PairMomentCert.smallWriterCertificate hn hs) hpin hord
  refine bankRepairDigitChargedMono _ _ _ ?_ hw
  have h2 := Nat.mul_div_le (smallDigitWriterTable (ceilLogTwo n) * n ^ 2) 2
  have hE := smallEntryChargeLe hn
  unfold smallDigitWaveTable bankRepairDigitValueWaveMicroCharge
  have e : (200 + smallDigitWriterTable (ceilLogTwo n) + smallDigitEntryTable (ceilLogTwo n)) *
      n ^ 2 = 200 * n ^ 2 + smallDigitWriterTable (ceilLogTwo n) * n ^ 2 +
        smallDigitEntryTable (ceilLogTwo n) * n ^ 2 := by rw [Nat.add_mul, Nat.add_mul]
  rw [e]
  omega

/-! ### BANK -/

section Bank

variable (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

include hn in
/-- **The BANK structural cut lies in the ordered entry cut `P'' 0`** (same state and audit,
`aft` the clock): `L3.StageMEntry.structuralCutEntry` with the strict completions recorded by the
structural time and the base covers at the clock.  Consumer: `bankWriterValueWaveOrdered`. -/
theorem structuralCutOrdEntry
    (hpin : L3.StageMEntry.WidthPinAfterStrict (bankWidthDigitReference ring hn hbank))
    (z : BankReferenceState ring hbank)
    (h : WidthDigitStructuralCut (bankWidthDigitReference ring hn hbank) z) :
    WidthOrdEntryCut (bankWidthDigitReference ring hn hbank) 0 z := by
  obtain ⟨start, word, root, audit, structural, ⟨hD, hC⟩, hfold, hW, hrun, hS⟩ :=
    widthStructuralZeroRun (bankWidthDigitReference ring hn hbank) z h
  have hfold' : word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (z, audit) := hfold
  have hsc : structural ≤ audit.clock := hS.1.1
  refine ⟨root, audit, fun _ => audit.clock, hrun, ⟨fun i _ first hf h2 hend => ?_,
    zeroRunCovers (bankWidthDigitReference ring hn hbank) root (z, audit) hrun, fun i hi => absurd hi (Nat.not_lt_zero i),
    Nat.le_refl _⟩, ?_⟩
  · have hpair := L3.DigitPairsClean.cleanPairIn ring hn hbank start hD hC word root
      (by rw [hfold']; exact hW) first (by rw [hfold']; exact hf) i h2 hend
    rw [hfold'] at hpair
    obtain ⟨tm, htm, hle⟩ := hS.1.2 _ _ DigitLane.writer hpair
    exact ⟨tm, htm.1, by show tm.time ≤ audit.clock; omega⟩
  · intro first hf i _ h2 hend
    have hpair := L3.DigitPairsClean.cleanPairIn ring hn hbank start hD hC word root
      (by rw [hfold']; exact hW) first (by rw [hfold']; exact hf) i h2 hend
    rw [hfold'] at hpair
    obtain ⟨tm, htm, -⟩ := hS.1.2 _ _ DigitLane.writer hpair
    exact L3.StageMEntry.pairPinOfCompletion (bankWidthDigitReference ring hn hbank) hpin root
      (z, audit) hrun _ tm h2 hend htm.1

/-- **The BANK writer value wave from the ordered receipts**: `bankWriterValueWaveOfMoments`
with the inclusion `structuralCutOrdEntry` (charged at the entry slot) and the ordered wave.
Consumer: `bankWriterDigitHalfOrdered`. -/
theorem bankWriterValueWaveOrdered
    (hpair : L3.PairMomentPremise.WidthStrictPairMoment (bankWidthDigitReference ring hn hbank)
      (L3.PairMomentPremise.widthPairMomentWidth n))
    (hpin : L3.StageMEntry.WidthPinAfterStrict (bankWidthDigitReference ring hn hbank))
    (hord : WidthWriterOrderedReceiptsClose (bankWidthDigitReference ring hn hbank)) :
    WidthWriterValueWaveClock (bankWidthDigitReference ring hn hbank)
      (2 * (L3.PairMomentPremise.widthPairMomentWidth n * (ceilLogTwo n + 6)) +
        6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) +
        bankRepairDigitValueWaveMicroCharge n) :=
  bankRepairDigitChargedWeaken (bankWidthDigitReference ring hn hbank).next _ _ _ _ _
    (fun z h => ⟨h, L3.CloseKeep.firstZeroLeader (bankWidthDigitReference ring hn hbank) z h⟩)
    (fun _ h => h)
    (L3.CloseKeep.leaderWave (bankWidthBoundaryReference ring hn hbank) hn
      (WidthDigitFirstZeroCut (bankWidthDigitReference ring hn hbank))
      (WidthDigitStructuralCut (bankWidthDigitReference ring hn hbank))
      (WidthOrdEntryCut (bankWidthDigitReference ring hn hbank) 0)
      (fun z => WidthDigitLeaderReceipt (bankWidthDigitReference ring hn hbank) z →
        WidthWriterValuesStableCut (bankWidthDigitReference ring hn hbank) z)
      (WidthWriterValuesStableCut (bankWidthDigitReference ring hn hbank)) _ _ _
      (L3.CloseKeep.reachedOfFirstZero (bankWidthBoundaryReference ring hn hbank))
      (L3.CloseKeep.reachedOfStructural (bankWidthBoundaryReference ring hn hbank))
      (reachedOfOrdEntry (bankWidthBoundaryReference ring hn hbank))
      (L3.PairMomentBank.widthStructuralClockOfMoments ring hn hbank hpair)
      (L3.StageMEntry.chargedOfIncl _ _ _ (structuralCutOrdEntry ring hn hbank hpin)
        (6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n)))
      (widthOrdWaveAfterEntry (bankWidthDigitReference ring hn hbank)
        (bankWidthBoundaryReference ring hn hbank).singletonFixed hn _
        (fun root z audit aft h1 h2 hL => hord root z audit aft h1 h2 hL))
      (fun _ h hL => h hL))

/-- **BANK clean digit half from the ordered receipts**: `bankWriterDigitHalfOfMoment` with
`bankWriterValueWaveOrdered`.  Consumer: `writerDigitHalfOfBandOrdered`. -/
theorem bankWriterDigitHalfOrdered
    (hpair : L3.PairMomentPremise.WidthStrictPairMoment (bankWidthDigitReference ring hn hbank)
      (L3.PairMomentPremise.widthPairMomentWidth n))
    (hpin : L3.StageMEntry.WidthPinAfterStrict (bankWidthDigitReference ring hn hbank))
    (hord : WidthWriterOrderedReceiptsClose (bankWidthDigitReference ring hn hbank))
    (hcompare : WidthWriterComparisonClock (bankWidthDigitReference ring hn hbank)
      (bankRepairDigitComparisonMicroCharge n))
    (hlaw : ∀ (root : Fin n) (first : Nat),
      L3.DigitQuiet.QuietStepLaw (c := compileAdvice (ceilLogTwo n)) ring root first)
    (hcert : WidthWriterComparisonCertificate (bankWidthDigitReference ring hn hbank)) :
    BankCleanDigitHalfOnDrain ring hbank :=
  widthWriterDigitHalfOfPremises (bankWidthDigitReference ring hn hbank) hn _ _ _ _ 201
    (by
      have h := L3.PairMomentBank.momentLedgerFit hn hbank
      simp only [Nat.add_assoc] at h ⊢
      exact h)
    (widthDigitBoundaryStageBank ring hn hbank)
    (widthDigitFirstZeroClockBankOfReference ring hn hbank)
    (bankWriterValueWaveOrdered ring hn hbank hpair hpin hord)
    hcompare hlaw hcert

end Bank

/-! ### Both bands -/

/-- **Both clean digit halves from the ordered receipt conversion**: `writerDigitHalfOfBand`
with `WidthWriterOrderedReceiptsClose` in place of `WidthWriterReceiptsClose` and the pin after a
strict completion in place of the BANK entry clock.  Consumer: `l3HeadlineOfCleanBranches`. -/
theorem writerDigitHalfOfBandOrdered (ring : DirectedRing n) (hn : 5 ≤ n)
    (b z w p : Nat → Nat)
    (hfit : (compileAdvice (ceilLogTwo n)).useSmall = true →
      b (ceilLogTwo n) + z (ceilLogTwo n) + w (ceilLogTwo n) + p (ceilLogTwo n) + 2 ≤
        L3.SmallFinishRepair.smallRepairDigitHalf n)
    (hboundary : (compileAdvice (ceilLogTwo n)).useSmall = true →
      WidthDigitBoundaryStage (bandWidthDigitReference ring hn)
        (widthDigitBandCharge n b (bankRepairDigitBoundaryMicroCharge n)))
    (hzeroSmall : (compileAdvice (ceilLogTwo n)).useSmall = true →
      WidthDigitFirstZeroClock (bandWidthDigitReference ring hn)
        (widthDigitBandCharge n z (bankRepairDigitFirstZeroMicroCharge n)))
    (hwaveSmall : (compileAdvice (ceilLogTwo n)).useSmall = true →
      WidthWriterValueWaveClock (bandWidthDigitReference ring hn)
        (widthDigitBandCharge n w (bankRepairDigitValueWaveMicroCharge n)))
    (hpair : ∀ hb : (compileAdvice (ceilLogTwo n)).useSmall = false,
      L3.PairMomentPremise.WidthStrictPairMoment (bankWidthDigitReference ring hn hb)
        (L3.PairMomentPremise.widthPairMomentWidth n))
    (hpin : L3.StageMEntry.WidthPinAfterStrict (bandWidthDigitReference ring hn))
    (hord : WidthWriterOrderedReceiptsClose (bandWidthDigitReference ring hn))
    (hcompare : WidthWriterComparisonClock (bandWidthDigitReference ring hn)
      (widthDigitBandCharge n p (bankRepairDigitComparisonMicroCharge n)))
    (hlaw : ∀ (root : Fin n) (first : Nat),
      L3.DigitQuiet.QuietStepLaw (c := compileAdvice (ceilLogTwo n)) ring root first)
    (hcert : WidthWriterComparisonCertificate (bandWidthDigitReference ring hn)) :
    (∀ hb : (compileAdvice (ceilLogTwo n)).useSmall = false,
      BankCleanDigitHalfOnDrain ring hb) ∧
    ((compileAdvice (ceilLogTwo n)).useSmall = true →
      L3.SmallFinishClean.SmallCleanDigitHalf ring) := by
  constructor
  · intro hb
    rw [widthDigitBandChargeBank _ _ hb] at hcompare
    rw [bandWidthDigitReferenceBank ring hn hb] at hcompare hcert hpin hord
    exact bankWriterDigitHalfOrdered ring hn hb (hpair hb) hpin hord hcompare hlaw hcert
  · intro hs
    have hB := hboundary hs
    have hwave := hwaveSmall hs
    have hzero := hzeroSmall hs
    rw [widthDigitBandChargeSmall _ _ hs] at hB hzero hwave hcompare
    rw [bandWidthDigitReferenceSmall ring hn hs] at hB hzero hwave hcompare hcert
    exact smallWriterDigitHalfOfSliceCharges ring hn hs b z w p (hfit hs)
      hB hzero hwave hcompare hlaw hcert

end L3.WriterOrderedWave

#print axioms L3.WriterOrderedWave.reachedOfOrdEntry
#print axioms L3.WriterOrderedWave.widthWaveClockOfWriterOrdered
#print axioms L3.WriterOrderedWave.smallWaveClockOfWriterOrdered
#print axioms L3.WriterOrderedWave.structuralCutOrdEntry
#print axioms L3.WriterOrderedWave.bankWriterValueWaveOrdered
#print axioms L3.WriterOrderedWave.bankWriterDigitHalfOrdered
#print axioms L3.WriterOrderedWave.writerDigitHalfOfBandOrdered
