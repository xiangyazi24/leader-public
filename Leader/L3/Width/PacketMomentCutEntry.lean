import Leader.L3.Bank.RepairDigitPacketMomentCutEntry
import Leader.L3.Width.PacketMomentCutAttempt

/-!
# Lemma e-packet with a cut at a boundary reference: the entry into the attempt class at the cut

Generic form of the coupled part of `L3.PacketMomentCutEntry` (BankRepairDigitPacketMomentCutEntry)
at an arbitrary `WidthBoundaryReference`:

* `WidthLaneCutC c`: the attempt class at the paper's cut, without the audit invariants: one
  labelling `σ` stamped after `c` with the labelled aligned source (`SrcLab`) and the labelled
  aligned queue (`WinLab`), the aligned window (`WinAligned`) and the reached-state queue
  (`PacketQueue`) at the lane of `x` (Stage M; the earlier mobile-free target is dropped).
* `WidthRunInv`, `widthRunInvStep`: the audit invariants with the inherited atoms as base and the
  complete pair at the audit start, kept by every coupled letter.
* `widthAttemptOfCutC`: `WidthRunInv` and `WidthLaneCutC c` give `WidthAttemptInvC c`
  (a repackaging).
* `widthPairMomentOfStageC`: a stage bound `a/b` to `WidthPairDoneC c ∨ WidthLaneCutC c`, composed
  with the attempt loop at the pair clock (`widthAttemptMomentPairC`, every `R ≥ 3`):
  `E[z^τ] ≤ 6 a / b` to `WidthPairDoneC c`.
* `widthAttemptInvZero`: the attempt class is the attempt class with cut `0` (`labelCutZero`).

Consumer: the SMALL per-pair moments (`hpair` at cut `0`, `hcmpMomentSmall` at the restart cut).
-/

namespace L3.WidthPacketMomentCutEntry

set_option autoImplicit false
set_option linter.unusedSectionVars false

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
open L3.PacketMomentPairEntry
open L3.PacketMomentCutLabels
open L3.PacketMomentCutEntry
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentAudit
open L3.WidthPacketMomentGroupCompletion
open L3.WidthPacketMomentAttempt
open L3.WidthPacketMomentCutLabels
open L3.WidthPacketMomentCutAttempt

section Coupled

variable {n : Nat} (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat)

/-- **The attempt cut after the cut `c`** at a boundary reference (Stage M): one labelling `σ`
stamped after `c` with the labelled aligned source and the labelled aligned queue, the aligned
window and the reached-state queue, at the lane of `x`. Consumer: `widthAttemptOfCutC`, the
per-pair stage obligation (`WidthCmpPairStageW`). -/
def WidthLaneCutC (cut : Nat) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    Prop :=
  (∃ σ, LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R x)
        σ x.2 ∧
      LabelCut ring root lane src R cut
        (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ x.2 ∧
      SrcLab R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ ∧
      WinLab R (widthLaneOfState ref.toWidthDigitReference root lane src R x) σ) ∧
    WinAligned R (widthLaneOfState ref.toWidthDigitReference root lane src R x) ∧
    PacketQueue ring root lane src R (piD (ref.phys x.1)) x.2

/-- The attempt cut carries the labelled aligned source after the cut. Consumer: the stage
proof from `WidthSrcLabAtC`. -/
theorem widthSrcLabOfCutC (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hc : WidthLaneCutC ring ref root lane src R cut x) :
    WidthSrcLabAtC ring ref root lane src R cut x := by
  obtain ⟨⟨σ, hL, hC, hs, -⟩, -⟩ := hc
  exact ⟨σ, hL, hC, hs⟩

/-- **The run invariant of the pair** at a boundary reference: the audit invariants with the
inherited atoms as base and the complete pair at the audit start. Consumer: `widthAttemptOfCutC`,
`widthPairMomentOfStageC`. -/
def WidthRunInv (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthPairInv ring ref root lane src R (InheritedOk lane) x ∧
    DigitCompletePair ring root x.2.start src (src + R)

include hn in
/-- Every coupled letter keeps the run invariant. Consumer: `widthPairMomentOfStageC`. -/
theorem widthRunInvStep (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthRunInv ring ref root lane src R x) (e : Fin n) :
    WidthRunInv ring ref root lane src R (widthNxt ring ref x e) :=
  ⟨widthPairInvStep ring ref hn root lane src R hR hsrc hend _ x h.1 e, h.2⟩

/-- **The entry into the attempt class at the cut `c`** (a repackaging). Consumer:
`widthPairMomentOfStageC`. -/
theorem widthAttemptOfCutC (cut : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hI : WidthRunInv ring ref root lane src R x)
    (hc : WidthLaneCutC ring ref root lane src R cut x) :
    WidthAttemptInvC ring ref root lane src R (InheritedOk lane) cut x := by
  obtain ⟨⟨σ, hL, hC, -, hW⟩, hA, hQ⟩ := hc
  exact ⟨hI.1, hA, ⟨σ, hL, hC, hW⟩, hQ, hI.2⟩

include hn in
/-- **The stage, then the attempt loop, with the cut `c`**, at a boundary reference and every
`R ≥ 3`. Consumer: the SMALL per-pair moments (`hpair` at cut `0`, `hcmpMomentSmall` at the
restart cut). -/
theorem widthPairMomentOfStageC (hR : 3 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (cut : Nat) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hI : WidthRunInv ring ref root lane src R x) (a b : Nat)
    (hstage : MomentBoundQ (widthDigitAuditNext ref.toWidthDigitReference)
      (fun y => WidthPairDoneC ring ref root lane src R cut y ∨
        WidthLaneCutC ring ref root lane src R cut y)
      (n * (2 * bankRepairDigitPairClock R + 1)) a b x) :
    MomentBoundQ (widthDigitAuditNext ref.toWidthDigitReference)
      (WidthPairDoneC ring ref root lane src R cut) (n * (2 * bankRepairDigitPairClock R + 1))
      (a * (6 * (n * (2 * bankRepairDigitPairClock R + 1) - n) ^ bankRepairDigitPairClock R))
      (b * (n * (2 * bankRepairDigitPairClock R + 1) - n) ^ bankRepairDigitPairClock R) x := by
  have hk := momentKeep (widthDigitAuditNext ref.toWidthDigitReference) _
    (WidthRunInv ring ref root lane src R) _ a b
    (fun y e hy => widthRunInvStep ring ref hn root lane src R (by omega) hsrc hend y hy e)
    x hI hstage
  refine momentSeq _ _ _ _ a b _ _ x (Nat.le_mul_of_pos_left _ (by decide)) (fun y hy => ?_) hk
  obtain ⟨hd | hc, hy⟩ := hy
  · exact momentDone _ _ _ _ _ y (Nat.le_mul_of_pos_left _ (by decide)) hd
  · exact widthAttemptMomentPairC ring ref hn root lane src R hR hsrc hend _ (Nat.le_refl _)
      (InheritedOk lane) cut y (widthAttemptOfCutC ring ref root lane src R cut y hy hc)

/-- **The attempt class is the attempt class with cut `0`** at a boundary reference (recorded
samples are stamped after `0`, `labelCutZero`). Consumer: none in the chain; it shows the
cut-parametric loop specialises to `widthAttemptMomentPair`'s class. -/
theorem widthAttemptInvZero (Base : Bool → DigitAtom n → Prop)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthAttemptInv ring ref root lane src R Base x) :
    WidthAttemptInvC ring ref root lane src R Base 0 x := by
  obtain ⟨hP, hw, ⟨σ, hL, hs⟩, hq, hp⟩ := h
  exact ⟨hP, hw, ⟨σ, hL, labelCutZero ring root lane src R _ σ x.2 hP.2.1 hL, hs⟩, hq, hp⟩

end Coupled

end L3.WidthPacketMomentCutEntry

#print axioms L3.WidthPacketMomentCutEntry.widthRunInvStep
#print axioms L3.WidthPacketMomentCutEntry.widthSrcLabOfCutC
#print axioms L3.WidthPacketMomentCutEntry.widthAttemptOfCutC
#print axioms L3.WidthPacketMomentCutEntry.widthPairMomentOfStageC
#print axioms L3.WidthPacketMomentCutEntry.widthAttemptInvZero
