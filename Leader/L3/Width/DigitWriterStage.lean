import Leader.L3.Width.DigitPairMomentCert
import Leader.L3.Width.WaveCore
import Leader.L3.Width.DigitWriterValueCuts
import Leader.L3.Width.DigitCloseKeep

/-!
# The writer-lane e-max stage and the SMALL value wave after it

repair.tex 1712-1717: "First bring every complete writer pair into its post-strict structural
class, using Lemma e-max ... Thereafter" the current-value wave.  The comparison lane is a
separate, later e-max stage with the observer restarted at the digit-stability cut
(1743-1749).  This module states the writer stage once for both bands and proves it from the
per-pair writer moments; on SMALL it composes it with the wave after the writer cut.

* `WidthDigitWriterCut`: a first-zero continuation of the audit restarted at the clean start at
  which every complete writer pair has a strict completion.
* `WidthWriterPairMoment ref N`: the writer-lane restriction of `WidthStrictPairMoment`.
* `widthWriterStageOfMoments` (both bands): writer moments `E[z^T] ≤ 40` and the certificate
  `⌊n/r⌋ · 40 · (N-1)^t ≤ N^t` give the stage from the first-zero cut to the writer cut at
  charge `2 t` (Lemma e-max with exact Jensen, `simultaneousOfMoments`; the `⌊n/r⌋` goals are the
  complete pairs, the others are vacuous).
* `widthWaveClockOfWriter` (both bands): the writer stage, the entry clock from the writer cut
  to `P' 0` and the wave after the entry, into the writer values-stable cut
  (`L3.WriterValueCuts.WidthWriterValuesStableCut`, from `WidthWriterReceiptsClose`).
* `smallWaveClockOfWriter` (SMALL): with `t = ⌊c n² / 2⌋`, `c = smallDigitWriterTable q`
  (certificate `smallWriterCertificate`), the value-wave clock at the slot
  `smallDigitWaveTable q = 200 + c + e`.
-/

namespace L3.WriterStage

open L3
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open L3.WidthDigit
open L3.DigitCohortScratch
open L3.DigitStructuralClean
open L3.PairMoment
open L3.PairMomentPremise
open L3.WriterValueCuts

set_option autoImplicit false

section Generic

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- The writer cut: a first-zero continuation of the audit restarted at the clean start at which
every complete writer pair has a strict completion.  Consumer: `widthWriterStageOfMoments`,
`smallWaveClockOfWriter` and the SMALL wave premise of `l3HeadlineOfCleanBranches`. -/
def WidthDigitWriterCut (z : ref.State) : Prop :=
  ∃ (root : Fin n) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
    WidthZeroRun ref root (z, audit) ∧
      ∀ i, WidthPairDone ref root i DigitLane.writer (z, audit)

/-- **Lemma e-max's per-pair input on the writer lane**: from every first-zero continuation
of the audit restarted at the clean start, the first strict completion of writer pair `i` has
`E[z^T] ≤ 40`, `z = N/(N-1)`.  The writer-lane part of `WidthStrictPairMoment`.  Consumer:
`widthWriterStageOfMoments`, `smallWaveClockOfWriter` and the SMALL writer premise of
`l3HeadlineOfCleanBranches`. -/
def WidthWriterPairMoment (N : Nat) : Prop :=
  ∀ (root : Fin n) (i : Nat) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    WidthZeroRun ref root x → ¬ WidthPairDone ref root i DigitLane.writer x →
      MomentBound (widthDigitAuditNext ref) (WidthPairDone ref root i DigitLane.writer) N 40 x

/-- Pairs `i ≥ ⌊n/r⌋` are not complete, so their obligation holds vacuously.  Consumer:
`widthWriterStageOfMoments`. -/
theorem writerPairVacuous (hn : 5 ≤ n) (root : Fin n) (i : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hi : n / L3.ValueWaveClose.valueSpan n ≤ i) :
    WidthPairDone ref root i DigitLane.writer x := by
  intro first _ hend
  exfalso
  have hR := L3.ValueWaveClose.valueSpanTwo hn
  generalize L3.ValueWaveClose.valueSpan n = R at hR hi hend
  have hdm := Nat.div_add_mod n R
  have hmod := Nat.mod_lt n (by omega : 0 < R)
  have hmul : n / R * R ≤ i * R := Nat.mul_le_mul_right R hi
  have hc : R * (n / R) = n / R * R := Nat.mul_comm _ _
  omega

/-- **The writer-lane e-max stage, both bands**: per-pair writer moments at `N` and the
certificate `⌊n/r⌋ · 40 · (N-1)^t ≤ N^t` give the stage from the first-zero cut to the writer
cut at charge `2 t` (doubled units).  Consumer: `smallWaveClockOfWriter`. -/
theorem widthWriterStageOfMoments (hn : 5 ≤ n) (N t : Nat) (hN : 2 ≤ N)
    (hmom : WidthWriterPairMoment ref N)
    (hcert : n / L3.ValueWaveClose.valueSpan n * 40 * (N - 1) ^ t ≤ N ^ t) :
    BankRepairDigitChargedStage ref.next (WidthDigitFirstZeroCut ref) (WidthDigitWriterCut ref)
      (2 * t) := by
  intro z hz T
  obtain ⟨start, word, root, audit, retired, hst, hfold, hW, hDA, hcov, hBd, -⟩ := hz
  have hx : WidthZeroRun ref root (z, audit) :=
    ⟨start, word, [], (z, audit), retired, hst, hfold, hW, hDA, hcov, hBd, rfl⟩
  have hsim := simultaneousOfMoments (widthDigitAuditNext ref)
    (fun (i : Fin (n / L3.ValueWaveClose.valueSpan n)) y =>
      WidthPairDone ref root i.val DigitLane.writer y) N 40 t hN
    (fun i y e h => widthPairDoneStep ref root _ _ y e h) (z, audit)
    (fun i hng => hmom root i.val (z, audit) hx hng) hcert T
  have hB : ∀ y, (WidthZeroRun ref root y ∧
      ∀ i : Fin (n / L3.ValueWaveClose.valueSpan n),
        WidthPairDone ref root i.val DigitLane.writer y) → WidthDigitWriterCut ref y.1 := by
    rintro y ⟨hy, hgood⟩
    refine ⟨root, y.2, hy, fun i => ?_⟩
    by_cases hi : i < n / L3.ValueWaveClose.valueSpan n
    · exact hgood ⟨i, hi⟩
    · exact writerPairVacuous ref hn root i y (by omega)
  have hstop := costNumeratorTargetOnClosed (widthDigitAuditNext ref)
    (WidthZeroRun ref root)
    (fun y => WidthZeroRun ref root y ∧ ∀ i : Fin (n / L3.ValueWaveClose.valueSpan n),
      WidthPairDone ref root i.val DigitLane.writer y)
    (fun y => ∀ i : Fin (n / L3.ValueWaveClose.valueSpan n),
      WidthPairDone ref root i.val DigitLane.writer y)
    (fun y hy e => widthZeroRunStep ref root y hy e) (fun y hy hq => ⟨hy, hq⟩) T (z, audit) hx
  have hproj := L3.Projection.costProjectLe ref.next (widthDigitAuditNext ref) Prod.fst
    (fun _ _ => rfl) (WidthDigitWriterCut ref)
    (fun y => WidthZeroRun ref root y ∧ ∀ i : Fin (n / L3.ValueWaveClose.valueSpan n),
      WidthPairDone ref root i.val DigitLane.writer y) hB (z, audit) T
  calc 2 * costNumerator ref.next (WidthDigitWriterCut ref) z T
      ≤ 2 * (n ^ T * t) := Nat.mul_le_mul_left 2 (Nat.le_trans hproj (Nat.le_trans hstop hsim))
    _ = n ^ T * (2 * t) := Nat.mul_left_comm _ _ _

end Generic

/-- The SMALL entry charge fits its slot: `6 n (5 R + 2 + L) ≤ smallDigitEntryTable q · n²` on
every ring.  Consumer: `smallWaveClockOfWriter`. -/
theorem smallEntryChargeLe {n : Nat} (hn : 5 ≤ n) :
    6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) ≤
      smallDigitEntryTable (ceilLogTwo n) * n ^ 2 := by
  have hspec := ceilLogTwo_spec n (by omega)
  unfold smallDigitEntryTable
  generalize ceilLogTwo n = q at hspec ⊢
  generalize 5 * digitSpan (compileAdvice q) + 2 + q = y
  have hN : 0 < 2 ^ (q - 1) + 1 := Nat.succ_pos _
  have hdm := Nat.div_add_mod (6 * y + 2 ^ (q - 1)) (2 ^ (q - 1) + 1)
  have hmod := Nat.mod_lt (6 * y + 2 ^ (q - 1)) hN
  generalize (6 * y + 2 ^ (q - 1)) / (2 ^ (q - 1) + 1) = E at hdm ⊢
  have hEx : 6 * y ≤ E * (2 ^ (q - 1) + 1) := by
    have : (2 ^ (q - 1) + 1) * E = E * (2 ^ (q - 1) + 1) := Nat.mul_comm _ _
    omega
  have hEn : E * (2 ^ (q - 1) + 1) ≤ E * n := Nat.mul_le_mul_left E (by omega)
  have h1 : n * (6 * y) ≤ n * (E * n) := Nat.mul_le_mul_left n (Nat.le_trans hEx hEn)
  have e1 : 6 * n * y = n * (6 * y) := by grind
  have e2 : E * n ^ 2 = n * (E * n) := by rw [Nat.pow_two]; grind
  rw [e1, e2]
  exact h1

/-- **The value wave from the writer lane, at a digit reference**: the writer-lane e-max stage
(`widthWriterStageOfMoments`), the entry clock from the writer cut to the pinned block cut
`P' 0`, and the value wave after the entry (`L3.WidthWave.widthCleanWaveAfterEntry`, from
`WidthWriterReceiptsClose`) compose to the writer value-wave clock at
`2 t + 6 n (5 R + 2 + L) + 200 n²`, carrying the boundary leader receipt of the first-zero cut
through the three stages (`L3.CloseKeep.leaderWave`).
Consumer: `smallWaveClockOfWriter`. -/
theorem widthWaveClockOfWriter {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring)
    (hn : 5 ≤ n) (N t : Nat) (hN : 2 ≤ N)
    (hmom : WidthWriterPairMoment ref.toWidthDigitReference N)
    (hcert : n / L3.ValueWaveClose.valueSpan n * 40 * (N - 1) ^ t ≤ N ^ t)
    (hentry : BankRepairDigitChargedStage ref.next (WidthDigitWriterCut ref.toWidthDigitReference)
      (WidthEntryCut ref.toWidthDigitReference 0)
      (6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n)))
    (hclose : WidthWriterReceiptsClose ref.toWidthDigitReference) :
    WidthWriterValueWaveClock ref.toWidthDigitReference
      (2 * t + 6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) +
        bankRepairDigitValueWaveMicroCharge n) :=
  bankRepairDigitChargedWeaken ref.next _ _ _ _ _
    (fun z h => ⟨h, L3.CloseKeep.firstZeroLeader ref.toWidthDigitReference z h⟩) (fun _ h => h)
    (L3.CloseKeep.leaderWave ref hn (WidthDigitFirstZeroCut ref.toWidthDigitReference)
      (WidthDigitWriterCut ref.toWidthDigitReference) (WidthEntryCut ref.toWidthDigitReference 0)
      (fun z => WidthDigitLeaderReceipt ref.toWidthDigitReference z →
        WidthWriterValuesStableCut ref.toWidthDigitReference z)
      (WidthWriterValuesStableCut ref.toWidthDigitReference) _ _ _
      (L3.CloseKeep.reachedOfFirstZero ref)
      (fun z h => by
        obtain ⟨root, audit, hrun, -⟩ := h
        exact L3.CloseKeep.reachedOfZeroRun ref root z audit hrun)
      (L3.CloseKeep.reachedOfEntry ref 0)
      (widthWriterStageOfMoments ref.toWidthDigitReference hn N t hN hmom hcert) hentry
      (L3.WidthWave.widthCleanWaveAfterEntry ref.toWidthDigitReference ref.singletonFixed hn _
        (fun root z audit h1 h2 hL => hclose root z audit h1 h2 hL))
      (fun _ h hL => h hL))

/-- **The SMALL value-wave clock from the writer lane**: `widthWaveClockOfWriter` at the SMALL
reference (`hfix` = `singletonFixed` of `smallWidthBoundaryReference`) with
`N = widthPairMomentWidth n`, `t = ⌊c n² / 2⌋`, `c = smallDigitWriterTable q` (certificate
`smallWriterCertificate`), within the slot `smallDigitWaveTable q = 200 + c + e`
(`smallEntryChargeLe`).  Consumer: `L3.WriterCore.writerDigitHalfOfBand` (its SMALL value-wave
input). -/
theorem smallWaveClockOfWriter {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hs : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hmom : WidthWriterPairMoment (bandWidthDigitReference ring hn) (widthPairMomentWidth n))
    (hentry : BankRepairDigitChargedStage (bandWidthDigitReference ring hn).next
      (WidthDigitWriterCut (bandWidthDigitReference ring hn))
      (WidthEntryCut (bandWidthDigitReference ring hn) 0)
      (6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n)))
    (hclose : WidthWriterReceiptsClose (bandWidthDigitReference ring hn)) :
    WidthWriterValueWaveClock (bandWidthDigitReference ring hn)
      (widthDigitBandCharge n smallDigitWaveTable (bankRepairDigitValueWaveMicroCharge n)) := by
  rw [widthDigitBandChargeSmall _ _ hs]
  rw [bandWidthDigitReferenceSmall ring hn hs] at hmom hentry hclose ⊢
  have hw := widthWaveClockOfWriter (smallWidthBoundaryReference ring hn hs) hn
    (widthPairMomentWidth n) (smallDigitWriterTable (ceilLogTwo n) * n ^ 2 / 2)
    (widthPairMomentWidthTwo (by omega)) hmom
    (L3.PairMomentCert.smallWriterCertificate hn hs) hentry hclose
  refine bankRepairDigitChargedMono _ _ _ ?_ hw
  have h2 := Nat.mul_div_le (smallDigitWriterTable (ceilLogTwo n) * n ^ 2) 2
  have hE := smallEntryChargeLe hn
  unfold smallDigitWaveTable bankRepairDigitValueWaveMicroCharge
  have e : (200 + smallDigitWriterTable (ceilLogTwo n) + smallDigitEntryTable (ceilLogTwo n)) *
      n ^ 2 = 200 * n ^ 2 + smallDigitWriterTable (ceilLogTwo n) * n ^ 2 +
        smallDigitEntryTable (ceilLogTwo n) * n ^ 2 := by rw [Nat.add_mul, Nat.add_mul]
  rw [e]
  omega

end L3.WriterStage

#print axioms L3.WriterStage.writerPairVacuous
#print axioms L3.WriterStage.widthWriterStageOfMoments
#print axioms L3.WriterStage.widthWaveClockOfWriter
#print axioms L3.WriterStage.smallWaveClockOfWriter
