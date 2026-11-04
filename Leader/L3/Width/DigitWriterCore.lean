import Leader.L3.Width.DigitCompareStage
import Leader.L3.Width.DigitFirstZero
import Leader.L3.Width.DigitQuietSafe

/-!
# The clean digit core on the writer-lane cut family

The clean causal core of WidthDigitCleanCore, with the successor-value and comparison cuts
replaced by the writer-lane cut family of `L3.WriterValueCuts` (`WidthWriterValuesStableCut`,
`WidthWriterComparisonCut`).  The core reads these cuts only as stage endpoints and as the
start class of the comparison-entry certificate, so every proof is the old one with the cut
renamed; the generic lemmas of WidthDigitCleanCore that do not mention the cuts (drain through a
word, safe values along a drained word, identity on a safe state, the dirty count, its rows and
its drop) are reused.

* `widthWriterCausalCoreOfPremises`, `widthWriterDigitHalfOfPremises`: the core and the half
  stage from the boundary stage, the first-zero clock, the writer value-wave clock, the writer
  comparison clock, the one-letter law of the quiet class (`L3.DigitQuiet.QuietStepLaw`) and the
  writer comparison-entry certificate.  On the pre-drain the quiet class replaces `QDigit`: the
  identity of digits is the law's identity clause, the dirty drain runs on it, and `QDigit` is
  reached at zero dirty count by `L3.DigitQuiet.qdigitOfQuiet`.
* BANK: `bankWriterValueWaveOfMoments` (structural clock from the per-pair moments, entry
  clock, wave after the entry into the writer values-stable cut) and
  `bankWriterDigitHalfOfMoment`.
* SMALL: `smallWriterDigitHalfOfSliceCharges` at per-slice charges.
* `writerDigitHalfOfBand`: both halves from one premise list.
-/

namespace L3.WriterCore

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.WidthDigit
open L3.WriterValueCuts

set_option autoImplicit false

section Core

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- A writer comparison cut on a drained state followed by zero or more reference steps.
Consumer: `widthWriterCausalCoreOfPremises`. -/
def WidthWriterPreDrain (z : ref.State) : Prop :=
  ∃ (start : ref.State) (word : List (Fin n)),
    ref.drained start ∧ WidthWriterComparisonCut ref start ∧
    z = word.foldl ref.next start

/-- The clean cut family on the writer values-stable cut, with the drain retained.  Consumer:
`widthWriterCausalCoreOfPremises`. -/
def widthWriterCoreCuts : WidthDigitCuts ref.State where
  boundaryRetired := fun z => ref.drained z ∧
    (WidthDigitBoundaryRetiredCut ref z ∧ WidthDigitGoneReachable ref z)
  firstBlockZero := fun z => ref.drained z ∧ WidthDigitFirstZeroCut ref z
  successorValuesStable := fun z => ref.drained z ∧ WidthWriterValuesStableCut ref z

/-- The writer pre-drain is closed.  Consumer: `widthWriterCausalCoreOfPremises`. -/
theorem widthWriterPreDrainClosed :
    ∀ z, WidthWriterPreDrain ref z → ∀ e : Fin n,
      WidthWriterPreDrain ref (ref.next z e) := by
  rintro z ⟨start, word, hD, hC, rfl⟩ e
  refine ⟨start, word ++ [e], hD, hC, ?_⟩
  rw [List.foldl_append]
  rfl

/-- Every writer pre-drain state is drained.  Consumer: `widthWriterIdentityOfCertificate`,
`widthWriterDirtyRank`. -/
theorem widthWriterPreDrainDrain (z : ref.State) (hz : WidthWriterPreDrain ref z) :
    ref.drained z := by
  obtain ⟨start, word, hD, _, rfl⟩ := hz
  exact widthCleanDigitDrainWord ref start word hD

/-- The writer value-wave clock on the drained cuts.  Consumer:
`widthWriterCausalCoreOfPremises`. -/
theorem widthWriterCoreValueWaveClock (charge : Nat)
    (hclock : WidthWriterValueWaveClock ref charge) :
    BankRepairDigitChargedStage ref.next (widthWriterCoreCuts ref).firstBlockZero
      (widthWriterCoreCuts ref).successorValuesStable charge :=
  widthCleanDigitChargedCarryDrain ref _ _ charge (fun _ h => h.1)
    (bankRepairDigitChargedWeaken ref.next _ _ _ _ charge (fun _ h => h.2) (fun _ h => h)
      hclock)

/-- The writer comparison clock into the writer pre-drain.  Consumer:
`widthWriterCausalCoreOfPremises`. -/
theorem widthWriterCoreComparisonClock (charge : Nat)
    (hclock : WidthWriterComparisonClock ref charge) :
    BankRepairDigitChargedStage ref.next (widthWriterCoreCuts ref).successorValuesStable
      (WidthWriterPreDrain ref) charge := by
  have hkeep := widthCleanDigitChargedCarryDrain ref
    (fun z => ref.drained z ∧ WidthWriterValuesStableCut ref z)
    (WidthWriterComparisonCut ref) charge (fun _ h => h.1)
    (bankRepairDigitChargedWeaken ref.next _ _ _ _ charge (fun _ h => h.2) (fun _ h => h)
      hclock)
  exact bankRepairDigitChargedWeaken ref.next _ _ _ _ charge (fun _ h => h)
    (fun z hz => ⟨z, [], hz.1, hz.2, rfl⟩) hkeep

/-- A clean root and the quiet class persist on every drained run, by the one-letter law and
`cleanWordRootPhiStep`.  Consumer: `widthWriterSafeValuesOfCertificate`. -/
theorem widthWriterQuietWord (hn : 5 ≤ n) (root : Fin n) (first : Nat)
    (hlaw : L3.DigitQuiet.QuietStepLaw (c := compileAdvice (ceilLogTwo n)) ring root first)
    (word : List (Fin n)) :
    ∀ z : ref.State, ref.drained z →
      CleanWordAtRoot ring root (piW (ref.phys z)) →
      L3.DigitQuiet.WidthDigitQuiet ring root first (piD (ref.phys z)) →
      CleanWordAtRoot ring root (piW (ref.phys (word.foldl ref.next z))) ∧
      L3.DigitQuiet.WidthDigitQuiet ring root first
        (piD (ref.phys (word.foldl ref.next z))) := by
  induction word with
  | nil =>
      intro z _ hW hQ
      exact ⟨hW, hQ⟩
  | cons e rest ih =>
      intro z hD hW hQ
      have hW' : CleanWordAtRoot ring root (piW (ref.phys (ref.next z e))) := by
        rw [ref.wordStep z hD e]
        exact cleanWordRootPhiStep (by omega : 3 ≤ n) ring root (piW (ref.phys z)) e hW
      have hQ' : L3.DigitQuiet.WidthDigitQuiet ring root first
          (piD (ref.phys (ref.next z e))) := by
        rw [ref.digitStep z hD e]
        exact (hlaw (piD (ref.phys z)) e hQ hW.1 hW.2.2).1
      exact ih (ref.next z e) (ref.drainedClosed z hD e) hW' hQ'

/-- The writer certificate propagates over the writer pre-drain.  Consumer:
`widthWriterIdentityOfCertificate`, `widthWriterZeroOfCertificate`. -/
theorem widthWriterSafeValuesOfCertificate (hn : 5 ≤ n)
    (hlaw : ∀ (root : Fin n) (first : Nat),
      L3.DigitQuiet.QuietStepLaw (c := compileAdvice (ceilLogTwo n)) ring root first)
    (hcert : WidthWriterComparisonCertificate ref)
    (z : ref.State) (hz : WidthWriterPreDrain ref z) :
    ∃ (root : Fin n) (first : Nat),
      CleanWordAtRoot ring root (piW (ref.phys z)) ∧
      L3.DigitQuiet.WidthDigitQuiet ring root first (piD (ref.phys z)) := by
  obtain ⟨start, word, hD, hC, rfl⟩ := hz
  obtain ⟨root, first, hW, hQ⟩ := hcert start hD hC
  exact ⟨root, first, widthWriterQuietWord ref hn root first (hlaw root first) word start hD hW hQ⟩

/-- The identity proposals on the writer pre-drain: the identity clause of the one-letter law.
Consumer: `widthWriterCausalCoreOfPremises`. -/
theorem widthWriterIdentityOfCertificate (hn : 5 ≤ n)
    (hlaw : ∀ (root : Fin n) (first : Nat),
      L3.DigitQuiet.QuietStepLaw (c := compileAdvice (ceilLogTwo n)) ring root first)
    (hcert : WidthWriterComparisonCertificate ref) :
    ∀ z, WidthWriterPreDrain ref z → ∀ e i : Fin n,
      (ref.phys (ref.next z e) i).d = (ref.phys z i).d := by
  intro z hz e i
  obtain ⟨root, first, hW, hQ⟩ := widthWriterSafeValuesOfCertificate ref hn hlaw hcert z hz
  have hpoint := congrArg
    (fun p : Fin n → ProjD (compileAdvice (ceilLogTwo n)) => (p i).top.d)
    (ref.digitStep z (widthWriterPreDrainDrain ref z hz) e)
  change (ref.phys (ref.next z e) i).d = ((phiD ring (piD (ref.phys z)) e) i).top.d at hpoint
  have hvalue := (hlaw root first (piD (ref.phys z)) e hQ hW.1 hW.2.2).2.1 i
  change ((phiD ring (piD (ref.phys z)) e) i).top.d = (ref.phys z i).d at hvalue
  exact hpoint.trans hvalue

/-- Zero dirty count on the writer pre-drain gives the clean digit: `QDigit` there is
`L3.DigitQuiet.qdigitOfQuiet`, the values are the class's `values` field.  Consumer:
`widthWriterCausalCoreOfPremises`. -/
theorem widthWriterZeroOfCertificate (hn : 5 ≤ n)
    (hlaw : ∀ (root : Fin n) (first : Nat),
      L3.DigitQuiet.QuietStepLaw (c := compileAdvice (ceilLogTwo n)) ring root first)
    (hcert : WidthWriterComparisonCertificate ref)
    (z : ref.State) (hz : WidthWriterPreDrain ref z)
    (hzero : widthDigitDirtyCount ref z = 0) :
    WidthCleanDigit ref z := by
  obtain ⟨root, first, hW, hQ⟩ := widthWriterSafeValuesOfCertificate ref hn hlaw hcert z hz
  have hnd : L3.DigitQuiet.NoDirty (piD (ref.phys z)) := widthDigitNoDirtyOfZero ref z hzero
  exact widthCleanDigitZeroOfSafeValues ref z root hW hQ.values
    (L3.DigitQuiet.qdigitOfQuiet (by omega : 3 ≤ n) ring root first (hlaw root first) _ hQ hnd hW)
    hzero

/-- The nominated-edge dirty rank on the writer pre-drain.  Consumer:
`widthWriterCausalCoreOfPremises`. -/
theorem widthWriterDirtyRank (hn : 5 ≤ n)
    (hidentity : ∀ z, WidthWriterPreDrain ref z → ∀ e i : Fin n,
      (ref.phys (ref.next z e) i).d = (ref.phys z i).d)
    (haccept : ∀ z, WidthWriterPreDrain ref z →
      widthDigitDirtyCount ref z = 0 → WidthCleanDigit ref z) :
    ∃ (rank : ref.State → Nat) (chosen : ref.State → Fin n),
      (∀ z, WidthWriterPreDrain ref z → rank z ≤ n) ∧
      (∀ z, WidthWriterPreDrain ref z → rank z = 0 → WidthCleanDigit ref z) ∧
      (∀ z, WidthWriterPreDrain ref z → ¬ WidthCleanDigit ref z →
        rank (ref.next z (chosen z)) + 1 ≤ rank z) ∧
      (∀ z, WidthWriterPreDrain ref z → ¬ WidthCleanDigit ref z →
        ∀ e : Fin n, rank (ref.next z e) ≤ rank z) := by
  classical
  have hrows := widthDigitDirtyRows ref hn (WidthWriterPreDrain ref)
    (widthWriterPreDrainDrain ref) hidentity
  refine ⟨widthDigitDirtyCount ref,
    fun z => ring.leftNeighbor (widthDigitLeftmostDirtySite ref z), ?_, ?_, ?_, ?_⟩
  · intro z _
    exact widthDigitDirtyCountCap ref z
  · intro z hz hzero
    exact haccept z hz hzero
  · intro z hz hnot
    have hex : ∃ i : Fin n, (ref.phys z i).topDirty = true := by
      by_cases hdirty : ∃ i : Fin n, (ref.phys z i).topDirty = true
      · exact hdirty
      · have hclean : ∀ i : Fin n, (ref.phys z i).topDirty = false := by
          intro i
          cases hb : (ref.phys z i).topDirty with
          | false => rfl
          | true => exact False.elim (hdirty ⟨i, hb⟩)
        exact False.elim (hnot (haccept z hz (widthDigitDirtyCountZeroOfClean ref z hclean)))
    exact widthDigitDirtyCountDrop ref (WidthWriterPreDrain ref) hrows z hz
      (widthDigitLeftmostDirtySite ref z) (widthDigitLeftmostDirtySpec ref z hex)
  · intro z hz _ e
    exact widthDigitDirtyCountNonincreasing ref (WidthWriterPreDrain ref) hrows z hz e

/-- **The clean causal core on the writer cut family, once for both bands**: the boundary
stage, the first-zero clock, the writer value-wave and comparison clocks, the one-letter law of
the quiet class and the writer comparison-entry certificate give the generic causal core from the clean start to the clean
digit.  Consumer: `widthWriterDigitHalfOfPremises`, `smallWriterDigitHalfOfSliceCharges`. -/
theorem widthWriterCausalCoreOfPremises (hn : 5 ≤ n) (cb cz cw cc : Nat)
    (hboundary : WidthDigitBoundaryStage ref cb)
    (hzero : WidthDigitFirstZeroClock ref cz)
    (hwave : WidthWriterValueWaveClock ref cw)
    (hcompare : WidthWriterComparisonClock ref cc)
    (hlaw : ∀ (root : Fin n) (first : Nat),
      L3.DigitQuiet.QuietStepLaw (c := compileAdvice (ceilLogTwo n)) ring root first)
    (hcert : WidthWriterComparisonCertificate ref) :
    WidthDigitCausalCore ref.next ref.start (WidthWriterPreDrain ref)
      (WidthCleanDigit ref) (widthWriterCoreCuts ref) cb cz cw cc := by
  obtain ⟨rank, chosen, hcap, hzeroRank, hdrop, hnoninc⟩ :=
    widthWriterDirtyRank ref hn
      (widthWriterIdentityOfCertificate ref hn hlaw hcert)
      (widthWriterZeroOfCertificate ref hn hlaw hcert)
  exact ⟨hboundary,
    widthCleanDigitCoreFirstZeroClock ref cz hzero,
    widthWriterCoreValueWaveClock ref cw hwave,
    widthWriterCoreComparisonClock ref cc hcompare,
    widthWriterPreDrainClosed ref,
    rank, chosen, hcap, hzeroRank, hdrop, hnoninc⟩

/-- The clean digit half-stage at `H + 2` on the writer cut family.  Consumer:
`bankWriterDigitHalfOfMoment`. -/
theorem widthWriterDigitHalfOfPremises (hn : 5 ≤ n) (cb cz cw cc H : Nat)
    (hfit : cb + cz + cw + cc ≤ H * n ^ 2)
    (hboundary : WidthDigitBoundaryStage ref cb)
    (hzero : WidthDigitFirstZeroClock ref cz)
    (hwave : WidthWriterValueWaveClock ref cw)
    (hcompare : WidthWriterComparisonClock ref cc)
    (hlaw : ∀ (root : Fin n) (first : Nat),
      L3.DigitQuiet.QuietStepLaw (c := compileAdvice (ceilLogTwo n)) ring root first)
    (hcert : WidthWriterComparisonCertificate ref) :
    BankRepairHalfStage ref.next ref.start (WidthCleanDigit ref) (H + 2) :=
  widthDigitHalfOfCausalCore ref.next ref.start (WidthWriterPreDrain ref)
    (WidthCleanDigit ref) (widthWriterCoreCuts ref) cb cz cw cc H hfit
    (widthWriterCausalCoreOfPremises ref hn cb cz cw cc hboundary hzero hwave hcompare hlaw hcert)

end Core

/-! ### BANK -/

/-- **The BANK writer value wave from the per-pair moments**: the structural clock
`widthStructuralClockOfMoments` (Lemma e-max, both lanes), the entry clock from the structural
cut to `P' 0`, and the wave after the entry into the writer values-stable cut
(`L3.WidthWave.widthCleanWaveAfterEntry`, from `WidthWriterReceiptsClose`), carrying the boundary
leader receipt of the first-zero cut through the three stages (`L3.CloseKeep.leaderWave`).
Consumer: `bankWriterDigitHalfOfMoment`. -/
theorem bankWriterValueWaveOfMoments {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpair : L3.PairMomentPremise.WidthStrictPairMoment (bankWidthDigitReference ring hn hbank)
      (L3.PairMomentPremise.widthPairMomentWidth n))
    (hentry : L3.DigitStructuralClean.WidthDigitEntryClock
      (bankWidthDigitReference ring hn hbank)
      (6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n)))
    (hclose : WidthWriterReceiptsClose (bankWidthDigitReference ring hn hbank)) :
    WidthWriterValueWaveClock (bankWidthDigitReference ring hn hbank)
      (2 * (L3.PairMomentPremise.widthPairMomentWidth n * (ceilLogTwo n + 6)) +
        6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) +
        bankRepairDigitValueWaveMicroCharge n) :=
  bankRepairDigitChargedWeaken (bankWidthDigitReference ring hn hbank).next _ _ _ _ _
    (fun z h => ⟨h, L3.CloseKeep.firstZeroLeader (bankWidthDigitReference ring hn hbank) z h⟩)
    (fun _ h => h)
    (L3.CloseKeep.leaderWave (bankWidthBoundaryReference ring hn hbank) hn
      (WidthDigitFirstZeroCut (bankWidthDigitReference ring hn hbank))
      (L3.DigitStructuralClean.WidthDigitStructuralCut (bankWidthDigitReference ring hn hbank))
      (L3.DigitStructuralClean.WidthEntryCut (bankWidthDigitReference ring hn hbank) 0)
      (fun z => WidthDigitLeaderReceipt (bankWidthDigitReference ring hn hbank) z →
        WidthWriterValuesStableCut (bankWidthDigitReference ring hn hbank) z)
      (WidthWriterValuesStableCut (bankWidthDigitReference ring hn hbank)) _ _ _
      (L3.CloseKeep.reachedOfFirstZero (bankWidthBoundaryReference ring hn hbank))
      (L3.CloseKeep.reachedOfStructural (bankWidthBoundaryReference ring hn hbank))
      (L3.CloseKeep.reachedOfEntry (bankWidthBoundaryReference ring hn hbank) 0)
      (L3.PairMomentBank.widthStructuralClockOfMoments ring hn hbank hpair) hentry
      (L3.WidthWave.widthCleanWaveAfterEntry (bankWidthDigitReference ring hn hbank)
        (bankWidthBoundaryReference ring hn hbank).singletonFixed hn _
        (fun root z audit h1 h2 hL => hclose root z audit h1 h2 hL))
      (fun _ h hL => h hL))

/-- **BANK clean digit half on the writer cut family**: boundary stage
`widthDigitBoundaryStageBank`, first-zero clock `widthDigitFirstZeroClockBankOfReference`
(the generic first-zero proof at the BANK boundary reference), writer value
wave `bankWriterValueWaveOfMoments`, the writer comparison clock at the micro-charge, the
one-letter law of the quiet class and the writer certificate; the charges fit 201 by `momentLedgerFit`.  Consumer:
`writerDigitHalfOfBand`. -/
theorem bankWriterDigitHalfOfMoment {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpair : L3.PairMomentPremise.WidthStrictPairMoment (bankWidthDigitReference ring hn hbank)
      (L3.PairMomentPremise.widthPairMomentWidth n))
    (hentry : L3.DigitStructuralClean.WidthDigitEntryClock
      (bankWidthDigitReference ring hn hbank)
      (6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n)))
    (hclose : WidthWriterReceiptsClose (bankWidthDigitReference ring hn hbank))
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
    (bankWriterValueWaveOfMoments ring hn hbank hpair hentry hclose)
    hcompare hlaw hcert

/-! ### SMALL -/

/-- **SMALL clean digit half on the writer cut family, from per-slice charges**: stage charges
`b q · n²`, `z q · n²`, `w q · n²`, `p q · n²` per slice `q = ceilLogTwo n`, fitting the SMALL
digit budget with the two dirty-drain half-units.  Consumer: `writerDigitHalfOfBand`. -/
theorem smallWriterDigitHalfOfSliceCharges {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (b z w p : Nat → Nat)
    (htable : b (ceilLogTwo n) + z (ceilLogTwo n) + w (ceilLogTwo n) + p (ceilLogTwo n) + 2 ≤
      L3.SmallFinishRepair.smallRepairDigitHalf n)
    (hboundary : WidthDigitBoundaryStage (smallWidthDigitReference ring hn hsmall)
      (b (ceilLogTwo n) * n ^ 2))
    (hzero : WidthDigitFirstZeroClock (smallWidthDigitReference ring hn hsmall)
      (z (ceilLogTwo n) * n ^ 2))
    (hwave : WidthWriterValueWaveClock (smallWidthDigitReference ring hn hsmall)
      (w (ceilLogTwo n) * n ^ 2))
    (hcompare : WidthWriterComparisonClock (smallWidthDigitReference ring hn hsmall)
      (p (ceilLogTwo n) * n ^ 2))
    (hlaw : ∀ (root : Fin n) (first : Nat),
      L3.DigitQuiet.QuietStepLaw (c := compileAdvice (ceilLogTwo n)) ring root first)
    (hcert : WidthWriterComparisonCertificate (smallWidthDigitReference ring hn hsmall)) :
    L3.SmallFinishClean.SmallCleanDigitHalf ring := by
  have hfit : b (ceilLogTwo n) * n ^ 2 + z (ceilLogTwo n) * n ^ 2 +
      w (ceilLogTwo n) * n ^ 2 + p (ceilLogTwo n) * n ^ 2 ≤
        (L3.SmallFinishRepair.smallRepairDigitHalf n - 2) * n ^ 2 := by
    rw [← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul]
    exact Nat.mul_le_mul_right (n ^ 2) (by omega)
  exact L3.SmallFinishClean.smallCleanDigitHalfOfCausalCore ring hn hsmall
    (WidthWriterPreDrain (smallWidthDigitReference ring hn hsmall))
    (widthWriterCoreCuts (smallWidthDigitReference ring hn hsmall)) _ _ _ _ hfit
    (widthWriterCausalCoreOfPremises (smallWidthDigitReference ring hn hsmall) hn
      _ _ _ _ hboundary hzero hwave hcompare hlaw hcert)

/-! ### Both bands -/

/-- **Both clean digit halves on the writer cut family, from one premise list.**  At the band
reference: the receipt conversion `WidthWriterReceiptsClose`, the writer comparison clock at the
band charge, the one-letter law of the quiet class and the writer certificate.  On BANK: boundary stage and first-zero clock proved,
value wave from the per-pair moments and the entry clock (`bankWriterDigitHalfOfMoment`).  On
SMALL: the slice table `b z w p` fits the digit budget, and the boundary stage, the first-zero
clock and the writer value-wave clock at the slice charges.
Consumer: `l3HeadlineOfCleanBranches`. -/
theorem writerDigitHalfOfBand {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
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
    (hentry : ∀ hb : (compileAdvice (ceilLogTwo n)).useSmall = false,
      L3.DigitStructuralClean.WidthDigitEntryClock (bankWidthDigitReference ring hn hb)
        (6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n)))
    (hclose : WidthWriterReceiptsClose (bandWidthDigitReference ring hn))
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
    rw [bandWidthDigitReferenceBank ring hn hb] at hcompare hcert hclose
    exact bankWriterDigitHalfOfMoment ring hn hb (hpair hb)
      (hentry hb) hclose hcompare hlaw hcert
  · intro hs
    have hB := hboundary hs
    have hwave := hwaveSmall hs
    have hzero := hzeroSmall hs
    rw [widthDigitBandChargeSmall _ _ hs] at hB hzero hwave hcompare
    rw [bandWidthDigitReferenceSmall ring hn hs] at hB hzero hwave hcompare hcert
    exact smallWriterDigitHalfOfSliceCharges ring hn hs b z w p (hfit hs)
      hB hzero hwave hcompare hlaw hcert

end L3.WriterCore

#print axioms L3.WriterCore.widthWriterQuietWord
#print axioms L3.WriterCore.widthWriterSafeValuesOfCertificate
#print axioms L3.WriterCore.widthWriterIdentityOfCertificate
#print axioms L3.WriterCore.widthWriterZeroOfCertificate
#print axioms L3.WriterCore.widthWriterDirtyRank
#print axioms L3.WriterCore.widthWriterCausalCoreOfPremises
#print axioms L3.WriterCore.widthWriterDigitHalfOfPremises
#print axioms L3.WriterCore.bankWriterValueWaveOfMoments
#print axioms L3.WriterCore.bankWriterDigitHalfOfMoment
#print axioms L3.WriterCore.smallWriterDigitHalfOfSliceCharges
#print axioms L3.WriterCore.writerDigitHalfOfBand
