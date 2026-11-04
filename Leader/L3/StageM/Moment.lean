import Leader.L3.StageM.QueueCoupled
import Leader.L3.Width.PacketMomentCutEntry

/-!
# Stage M (R10c, Lemma e-max, producer M1): from the labelled aligned source to the lane cut

From a layout state with ordered audit frames and the labelled aligned source after the cut
(`WidthSrcLabAtC`), with arbitrary inherited target contents, the coupled chain reaches the
attempt cut `WidthLaneCutC` with `E[z^T] ≤ w^{R(4R+4)}`, and `R(4R+4) = 4R(R+1) ≤ 2 C_R`
(`stageMBudget`).

The proof simulates the coupled chain by the ghost lane chain `gnext` (`L3.StageMGhostLane`):
`StageSim` couples a coupled state with a ghost lane state (the lane of the coupled state, a
ghost window with the run invariant `MaskInv` of `L3.StageMQueueCoupled`, and one labelling with
the labelled aligned source and the labelled aligned queue of the masked lane). The ghost chain
reaches `orank = 0` within the moment `ghostMoment`; there `ghostStop` gives the window invariants
and no old pending packet, so `winLabMaskStop`, `queueMaskStop` and `orderOfWin` give every clause
of `WidthLaneCutC`.

Consumer: the stage premise `hstage` of
`L3.WidthPacketMomentCutEntry.widthPairMomentOfStageC` (with the stages before the cut) and the
per-pair stage obligation `WidthCmpPairStageW`.
-/

namespace L3.StageMMoment

set_option autoImplicit false

open L3
open L3.PacketMoment
open L3.MarkedCells
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.GhostBridge
open L3.WidthDigit
open L3.DigitPacketTransport
open L3.DigitPacketOrder
open L3.DigitPacketQueue
open L3.DigitPacketQueueRows
open L3.PacketMomentRelease
open L3.PacketMomentWindow
open L3.PacketMomentPrep
open L3.PacketMomentLabels
open L3.PacketMomentTrialLabels
open L3.PacketMomentGroupLabels
open L3.PacketMomentCutLabels
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentAudit
open L3.WidthPacketMomentCutLabels
open L3.WidthPacketMomentCutAttempt
open L3.WidthPacketMomentCutEntry
open L3.StageMOldRank
open L3.StageMGhostLane
open L3.StageMMasked
open L3.StageMQueue
open L3.StageMQueueCoupled

/-- **The Stage M budget fits**: `R(4R+4) = 4R(R+1) ≤ 2 C_R`. Consumer: the per-pair stage
budget (`WidthCmpPairStageW`, `B ≤ 3 C_R` with the tail stage). -/
theorem stageMBudget (R : Nat) : R * (4 * R + 4) ≤ 2 * bankRepairDigitPairClock R := by
  unfold bankRepairDigitPairClock
  have h2 : R ^ 2 = R * R := Nat.pow_two R
  have e : R * (4 * R + 4) = 4 * (R * R) + 4 * R := by
    rw [Nat.mul_add, Nat.mul_comm R (4 * R), Nat.mul_assoc, Nat.mul_comm R 4]
  rw [e, h2]
  generalize R * R = t
  generalize R ^ 4 = a
  generalize R ^ 3 = b
  omega

variable {n : Nat}

/-- **The simulation of the coupled chain by the ghost lane chain**: the run invariant, the lane,
and one labelling with the labelled aligned source and the labelled aligned masked queue.
Consumer: `stageMMoment`. -/
def StageSim (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (root : Fin n)
    (lane : DigitLane) (src R cut : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (z : CohortLane × (Nat → OCell)) : Prop :=
  MaskInv ring ref root lane src R y z.2 ∧
    widthLaneOfState ref.toWidthDigitReference root lane src R y = z.1 ∧
    ∃ σ, LabelOk ring root lane src R (widthLaneOfState ref.toWidthDigitReference root lane src R y)
        σ y.2 ∧
      LabelCut ring root lane src R cut
        (widthLaneOfState ref.toWidthDigitReference root lane src R y) σ y.2 ∧
      SrcLab R (widthLaneOfState ref.toWidthDigitReference root lane src R y) σ ∧
      WinLab R (maskL R (widthLaneOfState ref.toWidthDigitReference root lane src R y) z.2) σ

/-- **The simulation is kept by every letter** (both chains read the same letter). Consumer:
`stageMMoment`. -/
theorem stageSimStep (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R cut : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (z : CohortLane × (Nat → OCell)) (e : Fin n)
    (h : StageSim ring ref root lane src R cut y z) :
    StageSim ring ref root lane src R cut (widthDigitAuditNext ref.toWidthDigitReference y e)
      (gnext R (cohortEdgeOf root src R) z e) := by
  obtain ⟨hM, hz, σ, hL, hC, hS, hW⟩ := h
  obtain ⟨hx, -, hg, -, hnb, -⟩ := id hM
  obtain ⟨-, h2⟩ := widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R
    hR hsrc hend y hx e
  refine ⟨?_, ?_, sigNext R (widthLaneOfState ref.toWidthDigitReference root lane src R y) σ
      (cohortEdgeOf root src R e),
    widthLabelOkStep ring ref hn root lane src R hR hsrc hend y hx σ e hL,
    widthLabelCutStep ring ref hn root lane src R hR hsrc hend cut y hx σ e hC, ?_, ?_⟩
  · show MaskInv ring ref root lane src R (widthDigitAuditNext ref.toWidthDigitReference y e)
      (gstep R z.1 z.2 (cohortEdgeOf root src R e))
    rw [← hz]
    exact maskInvStep ring ref hn root lane src R hR hsrc hend y z.2 hM e
  · show widthLaneOfState ref.toWidthDigitReference root lane src R
      (widthDigitAuditNext ref.toWidthDigitReference y e) =
      cohortLaneStep R z.1 (cohortEdgeOf root src R e)
    rw [h2, hz]
  · show SrcLab R (widthLaneOfState ref.toWidthDigitReference root lane src R
      (widthDigitAuditNext ref.toWidthDigitReference y e)) _
    rw [h2]
    revert hS
    cases cohortEdgeOf root src R e with
    | none => exact id
    | some k => exact fun hS => srcLabStep R hR _ σ k hS
  · show WinLab R (maskL R (widthLaneOfState ref.toWidthDigitReference root lane src R
      (widthDigitAuditNext ref.toWidthDigitReference y e))
      (gstep R z.1 z.2 (cohortEdgeOf root src R e))) _
    rw [h2, ← hz]
    have hw := winLabMaskStep R hR (widthLaneOfState ref.toWidthDigitReference root lane src R y)
      z.2 σ hg hnb (cohortEdgeOf root src R e) hW
    revert hw
    cases cohortEdgeOf root src R e with
    | none => exact id
    | some k => exact id

/-- **At ghost rank zero the coupled state is at the attempt cut.** Consumer: `stageMMoment`. -/
theorem stageSimStop (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (root : Fin n)
    (lane : DigitLane) (src R cut : Nat) (hR : 2 ≤ R)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (z : CohortLane × (Nat → OCell)) (h : StageSim ring ref root lane src R cut y z)
    (h0 : orank R z.2 = 0) : WidthLaneCutC ring ref root lane src R cut y := by
  obtain ⟨hM, -, σ, hL, hC, hS, hW⟩ := h
  obtain ⟨-, -, hg, hi, -, χ, hq⟩ := hM
  obtain ⟨hinv, hbar, hold, -⟩ := ghostStop R _ z.2 hg hi h0
  have hWL := winLabMaskStop R (by omega) _ z.2 σ hg hold hinv hW
  obtain ⟨a, hA, -⟩ := id hWL
  exact ⟨⟨σ, hL, hC, hS, hWL⟩, ⟨⟨a, hA⟩, hinv, hbar⟩, orderOfWin R _ hinv hbar, χ,
    (queueAtIff ring root lane src R _ _ χ).2 (queueMaskStop R _ z.2 hg hold hinv _ _ χ hq)⟩

/-- **Stage M (producer M1).** From a layout state with ordered audit frames and the labelled
aligned source after the cut, with arbitrary inherited target contents, the coupled chain reaches
the attempt cut with `E[z^T] ≤ w^{R(4R+4)}` (`w = N / (N - n)`). Consumer: `stageMStage`. -/
theorem stageMMoment (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R cut : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) (N : Nat) (hN : n < N)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1)
    (hfo : AuditFrameOrder x.2) (hs : WidthSrcLabAtC ring ref root lane src R cut x) :
    MomentBoundQ (widthDigitAuditNext ref.toWidthDigitReference)
      (WidthLaneCutC ring ref root lane src R cut) N (N ^ (R * (4 * R + 4)))
      ((N - n) ^ (R * (4 * R + 4))) x := by
  obtain ⟨σ, hL, hC, hS⟩ := hs
  have hsim : StageSim ring ref root lane src R cut x
      (widthLaneOfState ref.toWidthDigitReference root lane src R x,
        ghostInit R (widthLaneOfState ref.toWidthDigitReference root lane src R x)) :=
    ⟨maskInvInit ring ref root lane src R x hx hfo, rfl, σ, hL, hC, hS,
      winLabMaskInit R _ σ hS⟩
  have hgm := ghostMoment R hR (by omega) N (by omega) (fun k => digitSite ring root (src + k))
    (cohortEdgeOf root src R) (fun k hk => cohortEdgeOfSite ring root src R hend k hk)
    (widthLaneOfState ref.toWidthDigitReference root lane src R x,
      ghostInit R (widthLaneOfState ref.toWidthDigitReference root lane src R x))
  have hco := momentSimQ (widthDigitAuditNext ref.toWidthDigitReference)
    (gnext R (cohortEdgeOf root src R)) (StageSim ring ref root lane src R cut)
    (WidthLaneCutC ring ref root lane src R cut) (fun z => orank R z.2 = 0) N _ _
    (fun y z e hyz _ => stageSimStep ring ref hn root lane src R cut hR hsrc hend y z e hyz)
    (fun y z hyz h0 => stageSimStop ring ref root lane src R cut hR y z hyz h0) x _ hsim hgm
  refine momentQCross _ _ N _ _ _ _ x (Nat.pow_pos (by omega)) ?_ hco
  exact powCross N n _ _ (orankLe R _)

/-- **Stage M in the shape of the stage premise** (`hstage` of `widthPairMomentOfStageC`, whose
target is `WidthPairDoneC ∨ WidthLaneCutC`). Consumer: the per-pair stage obligation, after the
stages that reach `WidthSrcLabAtC`. -/
theorem stageMStage (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R cut : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) (N : Nat) (hN : n < N)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1)
    (hfo : AuditFrameOrder x.2) (hs : WidthSrcLabAtC ring ref root lane src R cut x) :
    MomentBoundQ (widthDigitAuditNext ref.toWidthDigitReference)
      (fun y => WidthPairDoneC ring ref root lane src R cut y ∨
        WidthLaneCutC ring ref root lane src R cut y) N (N ^ (R * (4 * R + 4)))
      ((N - n) ^ (R * (4 * R + 4))) x :=
  momentWeaken _ _ _ N _ _ (fun _ h => Or.inr h) x
    (stageMMoment ring ref hn root lane src R cut hR hsrc hend N hN x hx hfo hs)

/-- The pair-moment width exceeds `n`. Consumer: `stageMPairMoment`. -/
theorem pairWidthGt (R : Nat) (hn : 5 ≤ n) : n < n * (2 * bankRepairDigitPairClock R + 1) := by
  have hc : 1 ≤ bankRepairDigitPairClock R := by
    show 1 ≤ 2 * R ^ 4 + 8 * R ^ 3 + 3 * R ^ 2 + 11 * R + 4
    exact Nat.le_trans (by decide : 1 ≤ 4) (Nat.le_add_left 4 _)
  have h3 : n * 3 ≤ n * (2 * bankRepairDigitPairClock R + 1) :=
    Nat.mul_le_mul_left n (by omega)
  omega

/-- **Stage M fed into the per-pair moment**: from the run invariant and the labelled aligned
source after the cut, the pair completes with the Stage M factor `w^{R(4R+4)}` times the attempt
factor of `widthPairMomentOfStageC`. Consumer: the per-pair moment once the stages before the cut
(reaching `WidthSrcLabAtC`) are composed in front. -/
theorem stageMPairMoment (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R cut : Nat) (hR : 3 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hI : WidthRunInv ring ref root lane src R x)
    (hs : WidthSrcLabAtC ring ref root lane src R cut x) :
    MomentBoundQ (widthDigitAuditNext ref.toWidthDigitReference)
      (WidthPairDoneC ring ref root lane src R cut) (n * (2 * bankRepairDigitPairClock R + 1))
      ((n * (2 * bankRepairDigitPairClock R + 1)) ^ (R * (4 * R + 4)) *
        (6 * (n * (2 * bankRepairDigitPairClock R + 1) - n) ^ bankRepairDigitPairClock R))
      ((n * (2 * bankRepairDigitPairClock R + 1) - n) ^ (R * (4 * R + 4)) *
        (n * (2 * bankRepairDigitPairClock R + 1) - n) ^ bankRepairDigitPairClock R) x :=
  widthPairMomentOfStageC ring ref hn root lane src R hR hsrc hend cut x hI _ _
    (stageMStage ring ref hn root lane src R cut (by omega) hsrc hend _ (pairWidthGt R hn) x
      hI.1.1 hI.1.2.1 hs)

end L3.StageMMoment

#print axioms L3.StageMMoment.stageMBudget
#print axioms L3.StageMMoment.stageSimStep
#print axioms L3.StageMMoment.stageSimStop
#print axioms L3.StageMMoment.stageMMoment
#print axioms L3.StageMMoment.stageMStage
#print axioms L3.StageMMoment.stageMPairMoment
