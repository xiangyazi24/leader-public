import Leader.L3.StageM.Compare
import Leader.L3.Width.DigitWriterStage
import Leader.L3.Width.DigitPairMomentPremise

/-!
# The per-pair moment on every lane from a first-zero run: the tail stage, then Stage M

`WidthStrictPairMoment` (`hpair`, BANK) and `WidthWriterPairMoment` (`hwriterSmall`, SMALL) are
per-pair moments from a `WidthZeroRun` state to the completion of pair `i` with the cut `0`. At a
boundary reference they follow as the comparison lane did (`L3.StageMCompare`), with the cut `0`
and the run invariant of a first-zero run:

* `widthZeroRunInv`: on a `WidthZeroRun` state every interior pair of the first delimiter has the
  run invariant, on every lane (the port of `L3.PacketMomentPairEntry.zeroRunInv`).
* `widthPairDoneOfC`: a completion with the cut `0` of the pair of the first delimiter is
  `WidthPairDone`.
* `widthStrictPairMomentHolds`: `WidthStrictPairMoment` at every boundary reference (tail stage then
  Stage M with the cut `0`, `tailStageM`; then `widthPairMomentOfStageC`; `stageFactor`).
* `bankHPair`, `smallWriterPairMoment`: the headline premises `hpair` and `hwriterSmall`.

The BANK route goes through `bankWidthBoundaryReference`, not through `bankHPairOfStage`, whose
`BankPairStageW` targets the mobile-free cut `LaneCut`, which Stage M does not produce.

Consumer: `hpair` and `hwriterSmall` of `l3HeadlineOfCleanBranches`.
-/

namespace L3.StageMPair

set_option autoImplicit false

open L3
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.CohortSites
open L3.PacketMomentPrep
open L3.PacketMomentGroupLabels
open L3.PacketMomentPairDone
open L3.DigitCohortScratch
open L3.PairMomentPremise
open L3.WidthPacketMoment
open L3.WidthPacketMomentAudit
open L3.WidthPacketMomentGroupCompletion
open L3.WidthPacketMomentCutAttempt
open L3.WidthPacketMomentCutEntry
open L3.WidthPacketMomentTail
open L3.WidthPacketMomentCompare
open L3.StageMMoment
open L3.StageMCompare

section Coupled

variable {n : Nat} (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)

include hn in
/-- **The run invariant at a first-zero run** on every lane at a boundary reference. Consumer:
`widthStrictPairMomentHolds`. -/
theorem widthZeroRunInv (root : Fin n)
    (lane : DigitLane) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthZeroRun ref.toWidthDigitReference root x) (first : Nat)
    (hf : DigitFirstDelimiter ring root x.2.start first) (i : Nat)
    (hend : first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
      2 * digitSpan (compileAdvice (ceilLogTwo n)) < n) :
    2 ≤ first + i * digitSpan (compileAdvice (ceilLogTwo n)) ∧
      WidthRunInv ring ref root lane (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
        (digitSpan (compileAdvice (ceilLogTwo n))) x := by
  obtain ⟨start, word0, word, y, _, hs, hy, hW, -, -, -, hxw⟩ := hx
  have hst : x.2.start = piD (ref.phys start) := by
    rw [← hxw, widthFoldStart ring ref word y, ← hy, widthFoldStart ring ref word0]
    rfl
  have hW' : WFixedRoot ring root (piW (ref.phys (word0.foldl ref.next start))) := by
    have h1 := widthAuditFoldFst ref.toWidthDigitReference word0
      (start, digitAuditInitial (piD (ref.phys start)))
    rw [hy] at h1
    rw [← h1]
    exact hW
  rw [hst] at hf
  obtain ⟨h2, hI⟩ := widthCleanRunStart ring ref hn root lane start hs word0 hW' first hf i
    hend
  refine ⟨h2, ?_⟩
  rw [← hxw, ← hy]
  have hR := widthBoundaryDigitSpanTwo hn
  exact widthRunInvFold ring ref hn root lane _ _ (by omega) h2 hend word _
    (widthRunInvFold ring ref hn root lane _ _ (by omega) h2 hend word0 _ hI)

/-- **A completion with the cut `0` of the pair of the first delimiter is `WidthPairDone`** (the
first delimiter is unique). Consumer: `widthStrictPairMomentHolds`. -/
theorem widthPairDoneOfC (root : Fin n) (i first : Nat) (lane : DigitLane)
    (x y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hf : DigitFirstDelimiter ring root x.2.start first) (hy : y.2.start = x.2.start)
    (h : WidthPairDoneC ring ref root lane (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
      (digitSpan (compileAdvice (ceilLogTwo n))) 0 y) :
    WidthPairDone ref.toWidthDigitReference root i lane y := by
  intro f hf' _
  have he := firstDelimUnique ring root _ f first hf' (by rw [hy]; exact hf)
  subst he
  exact h

include hn in
/-- **`WidthStrictPairMoment` at a boundary reference** (`N = widthPairMomentWidth n`), every
lane: the tail stage then Stage M with the cut `0` (`tailStageM`, `B ≤ 3 C_r`), then the attempt
loop (`widthPairMomentOfStageC`). Consumer: `bankHPair`, `smallWriterPairMoment`. -/
theorem widthStrictPairMomentHolds :
    WidthStrictPairMoment ref.toWidthDigitReference (widthPairMomentWidth n) := by
  intro root i lane x hx hnd
  obtain ⟨first, hf, hend, hno⟩ : ∃ first, DigitFirstDelimiter ring root x.2.start first ∧
      first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
        2 * digitSpan (compileAdvice (ceilLogTwo n)) < n ∧
      ¬ WidthPairDoneC ring ref root lane (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
        (digitSpan (compileAdvice (ceilLogTwo n))) 0 x := by
    refine Classical.byContradiction fun hcon => hnd ?_
    intro first hf hend
    exact Classical.byContradiction fun hno => hcon ⟨first, hf, hend, hno⟩
  obtain ⟨h2, hI⟩ := widthZeroRunInv ring ref hn root lane x hx first hf i hend
  have h3 := widthSpanThree hn
  have hstage := tailStageM ring ref hn root lane
    (first + i * digitSpan (compileAdvice (ceilLogTwo n))) (digitSpan (compileAdvice (ceilLogTwo n)))
    0 (by omega) h2 hend
    (n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1))
    (pairWidthGt _ hn) x hI (Nat.zero_le _)
  have hq := widthPairMomentOfStageC ring ref hn root lane _ _ h3 h2 hend 0 x hI _ _ hstage
  have hk := momentKeep (widthDigitAuditNext ref.toWidthDigitReference) _
    (fun y => y.2.start = x.2.start) _ _ _ (fun y e hy => hy) x rfl hq
  have hw := momentWeaken _ _ (WidthPairDone ref.toWidthDigitReference root i lane)
    _ _ _ (fun y hy => widthPairDoneOfC ring ref root i first lane x y hf hy.2 hy.1) x hk
  have hC : 20 ≤ bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) :=
    Nat.le_trans (by decide) (pairClockMid _ (by omega))
  have hB := stageBudgetLe (digitSpan (compileAdvice (ceilLogTwo n)))
  show L3.PairMoment.MomentBound _ _
    (n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1)) 40 x
  have hab := stageFactor (n * (2 * bankRepairDigitPairClock
    (digitSpan (compileAdvice (ceilLogTwo n))) + 1)) n _ _ (by omega) hC (Nat.le_refl _) hB
  generalize bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) = C at hw hC hab ⊢
  have hNn : 0 < n * (2 * C + 1) - n := by
    have : n * 2 ≤ n * (2 * C + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  refine momentBoundOfQ _ _ _ _ _ 40 x (Nat.mul_pos (Nat.pow_pos hNn) (Nat.pow_pos hNn)) ?_ hw
  generalize (n * (2 * C + 1)) ^ (tailBudget (digitSpan (compileAdvice (ceilLogTwo n))) +
    digitSpan (compileAdvice (ceilLogTwo n)) * (4 * digitSpan (compileAdvice (ceilLogTwo n)) + 4))
    = a at hab ⊢
  generalize (n * (2 * C + 1) - n) ^ (tailBudget (digitSpan (compileAdvice (ceilLogTwo n))) +
    digitSpan (compileAdvice (ceilLogTwo n)) * (4 * digitSpan (compileAdvice (ceilLogTwo n)) + 4))
    = b at hab ⊢
  generalize (n * (2 * C + 1) - n) ^ C = p
  have h6 : 6 * a ≤ 40 * b := by omega
  have e1 : a * (6 * p) = 6 * a * p := by ac_rfl
  have e2 : 40 * (b * p) = 40 * b * p := by ac_rfl
  rw [e1, e2]
  exact Nat.mul_le_mul_right p h6

end Coupled

/-- **The headline premise `hpair`** (BANK, every lane). Consumer: `hpair` of
`l3HeadlineOfCleanBranches`. -/
theorem bankHPair {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    :
    ∀ hbank : (compileAdvice (ceilLogTwo n)).useSmall = false,
      WidthStrictPairMoment (bankWidthDigitReference ring hn hbank) (widthPairMomentWidth n) :=
  fun hbank => widthStrictPairMomentHolds ring (bankWidthBoundaryReference ring hn hbank) hn

/-- **The headline premise `hwriterSmall`** (SMALL, the writer lane). Consumer: `hwriterSmall` of
`l3HeadlineOfCleanBranches`. -/
theorem smallWriterPairMoment {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    :
    (compileAdvice (ceilLogTwo n)).useSmall = true →
      L3.WriterStage.WidthWriterPairMoment (bandWidthDigitReference ring hn)
        (widthPairMomentWidth n) := by
  intro hs
  rw [bandWidthDigitReferenceSmall ring hn hs]
  intro root i x hx hnd
  exact widthStrictPairMomentHolds ring (smallWidthBoundaryReference ring hn hs) hn root i
    DigitLane.writer x hx hnd

end L3.StageMPair

#print axioms L3.StageMPair.widthZeroRunInv
#print axioms L3.StageMPair.widthPairDoneOfC
#print axioms L3.StageMPair.widthStrictPairMomentHolds
#print axioms L3.StageMPair.bankHPair
#print axioms L3.StageMPair.smallWriterPairMoment
