import Leader.L3.Bank.RepairDigitPacketMomentCutAttempt
import Leader.L3.Bank.RepairDigitPacketMomentPairEntry

/-!
# Lemma e-packet with a cut: the entry at the mobile-free cut and the stage composition

`L3.PacketMomentPairEntry` with the cut of the completion as a parameter.

* `LaneCutC c`: the labelled aligned source with labels stamped after `c` (`SrcLabAtC c`) at a
  mobile-free target half.
* `attemptOfCutC`: `RunInv` and `LaneCutC c` give `AttemptInvC c`.
* `pairMomentOfStageC`: a stage bound `a/b` to `PairDoneC c ∨ LaneCutC c`, composed with the
  attempt loop with cut (`attemptMomentBankC`): `E[z^τ] ≤ 6 a / b` to `PairDoneC c`.
* The cut-`0` versions are corollaries: `labelCutZero` (recorded samples are stamped after `0`,
  `AuditFrameOrder`), `attemptInvZero` (`AttemptInv → AttemptInvC 0`), `attemptMomentBankZero`
  (the uncut `attemptMomentBank` from `attemptMomentBankC` at `c = 0`).
-/

namespace L3.PacketMomentCutEntry

set_option autoImplicit false

open L3
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Correspondence
open L3.GhostBridge
open L3.WidthDigit
open L3.DigitPacketTransport
open L3.DigitPacketQueue
open L3.PacketMomentPrep
open L3.PacketMomentCells
open L3.PacketMomentLabels
open L3.PacketMomentTrialLabels
open L3.PacketMomentGroupLabels
open L3.PacketMomentGroupCompletion
open L3.PacketMomentAttempt
open L3.PacketMomentPairEntry
open L3.PacketMomentCutLabels
open L3.PacketMomentCutAttempt

section Coupled

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat)

/-- **The mobile-free cut after the cut `c`**: the labelled aligned source, labels stamped after
`c`, at a mobile-free target half. Consumer: `attemptOfCutC`, the comparison stage obligation. -/
def LaneCutC (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  SrcLabAtC ring hbank root lane src R cut x ∧
    MobileFree R (laneOfState ring hbank root lane src R x)

/-- **The entry at the mobile-free cut with the cut `c`.** Consumer: `pairMomentOfStageC`. -/
theorem attemptOfCutC (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hI : RunInv ring hbank root lane src R x) (hc : LaneCutC ring hbank root lane src R cut x) :
    AttemptInvC ring hbank root lane src R (InheritedOk lane) cut x := by
  obtain ⟨⟨σ, hL, hC, hs⟩, hm⟩ := hc
  obtain ⟨a, hA, -⟩ := id hs
  exact ⟨hI.1, winAlignedOfMobileFree R _ ⟨a, hA⟩ hm,
    ⟨σ, hL, hC, winLabOfMobileFree R _ σ hs hm⟩,
    packetQueueMobileFree ring root lane src R (piD x.1.val.1) x.2
      (fun _ => ⟨0, lane, root, root, none, ⟨0, compileAdvice_topA_pos _⟩, false⟩) hm, hI.2⟩

/-- **The stage, then the attempt loop, with the cut `c`.** Consumer: the comparison per-pair
moment (`L3.PacketMomentCompareBank`). -/
theorem pairMomentOfStageC (hR : 7 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (cut : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hI : RunInv ring hbank root lane src R x) (a b : Nat)
    (hstage : MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => PairDoneC ring hbank root lane src R cut y ∨
        LaneCutC ring hbank root lane src R cut y)
      (n * (2 * bankRepairDigitPairClock R + 1)) a b x) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (PairDoneC ring hbank root lane src R cut) (n * (2 * bankRepairDigitPairClock R + 1))
      (a * (6 * (n * (2 * bankRepairDigitPairClock R + 1) - n) ^ bankRepairDigitPairClock R))
      (b * (n * (2 * bankRepairDigitPairClock R + 1) - n) ^ bankRepairDigitPairClock R) x := by
  have hk := momentKeep (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) _
    (RunInv ring hbank root lane src R) _ a b
    (fun y e hy => runInvStep ring hn hbank root lane src R (by omega) hsrc hend y hy e) x hI hstage
  refine momentSeq _ _ _ _ a b _ _ x (Nat.le_mul_of_pos_left _ (by decide)) (fun y hy => ?_) hk
  obtain ⟨hd | hc, hy⟩ := hy
  · exact momentDone _ _ _ _ _ y (Nat.le_mul_of_pos_left _ (by decide)) hd
  · exact attemptMomentBankC ring hn hbank root lane src R hR hsrc hend (InheritedOk lane) cut y
      (attemptOfCutC ring hbank root lane src R cut y hy hc)

/-! ### The cut-`0` versions are corollaries -/

/-- **Recorded samples are stamped after `0`**: on an ordered audit `LabelOk` gives `LabelCut 0`.
Consumer: `attemptInvZero`. -/
theorem labelCutZero (s : CohortLane) (σ : Nat → Option Nat)
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) (hfo : AuditFrameOrder A)
    (hL : LabelOk ring root lane src R s σ A) : LabelCut ring root lane src R 0 s σ A := by
  have key : ∀ (a : Option (DigitAtom n)) v, SampledAt ring root lane src R A a v → AfterCut 0 a := by
    intro a v hs id hid
    obtain ⟨-, smp, ha, -, -, -, f, hf, hft, -⟩ := hs
    rw [ha] at hid
    simp only [Option.some.injEq, DigitAtom.sampled.injEq] at hid
    subst hid
    rw [← hft]
    exact (hfo.2.1 f hf).1
  exact ⟨Nat.zero_le _, fun j hj T v hD hv => key _ _ (hL.1 j hj T v hD hv),
    fun j hj1 hj2 v hp hv => key _ _ (hL.2 j hj1 hj2 v hp hv)⟩

/-- **The attempt class is the attempt class with cut `0`.** Consumer: `attemptMomentBankZero`. -/
theorem attemptInvZero (Base : Bool → DigitAtom n → Prop)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AttemptInv ring hbank root lane src R Base x) :
    AttemptInvC ring hbank root lane src R Base 0 x := by
  obtain ⟨hP, hw, ⟨σ, hL, hs⟩, hq, hp⟩ := h
  exact ⟨hP, hw, ⟨σ, hL, labelCutZero ring root lane src R _ σ x.2 hP.2.1 hL, hs⟩, hq, hp⟩

/-- **The uncut attempt loop as the cut-`0` corollary** of `attemptMomentBankC`. Consumer:
none in the chain; it shows the cut-parametric loop specialises to `attemptMomentBank`. -/
theorem attemptMomentBankZero (hR : 7 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (Base : Bool → DigitAtom n → Prop)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AttemptInv ring hbank root lane src R Base x) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (PairDone ring hbank root lane src R) (n * (2 * bankRepairDigitPairClock R + 1))
      (6 * (n * (2 * bankRepairDigitPairClock R + 1) - n) ^ bankRepairDigitPairClock R)
      ((n * (2 * bankRepairDigitPairClock R + 1) - n) ^ bankRepairDigitPairClock R) x :=
  attemptMomentBankC ring hn hbank root lane src R hR hsrc hend Base 0 x
    (attemptInvZero ring hbank root lane src R Base x h)

end Coupled

end L3.PacketMomentCutEntry

#print axioms L3.PacketMomentCutEntry.attemptOfCutC
#print axioms L3.PacketMomentCutEntry.pairMomentOfStageC
#print axioms L3.PacketMomentCutEntry.labelCutZero
#print axioms L3.PacketMomentCutEntry.attemptInvZero
#print axioms L3.PacketMomentCutEntry.attemptMomentBankZero
