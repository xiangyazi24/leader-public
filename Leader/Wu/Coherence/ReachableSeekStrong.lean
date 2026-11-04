import Leader.Wu.Coherence.ReachableSeek
import Leader.Wu.Coherence.ReachableStrongOwnership

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableSeek2

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableSeek
open R2CoherenceV31ReachableOpenNoHazard3
open R2CoherenceV31Closure

variable {n ψ κ τ : Nat}

private theorem branch_seek_token_seek2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .seek) :
    r.ctl.tok = .seek := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowV3_seek_eq_seek2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .seek) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = seekStageV3 l r := by
  have hs := branch_seek_token_seek2 hψ h2 l r hb
  simp [rowV3, hs]

private theorem seekStage_phys_seek2 (l r : Cell ψ κ τ) :
    (seekStageV3 l r).1.phys = l.phys ∧
    (seekStageV3 l r).2.phys = r.phys := by
  unfold seekStageV3
  repeat' split <;> simp [setControl]

private theorem seek_step_phys_eq_seek2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    ∀ p, (stepV3 hψ h2 ring C e p).phys = (C p).phys := by
  intro p
  have hr := rowV3_seek_eq_seek2 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  have hp := seekStage_phys_seek2 (C e) (C (ring.rightNeighbor e))
  by_cases hpe : p = e
  · subst p
    simpa [stepV3, protocolV3, PopulationProtocol.step, hr] using hp.1
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      simpa [stepV3, protocolV3, PopulationProtocol.step, hr, hpe] using hp.2
    · rw [stepV3_other hψ h2 ring C e p hpe hpr]

private theorem seek_step_ctl_shape_seek2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    (stepV3 hψ h2 ring C e p).ctl = (C p).ctl ∨
      ((stepV3 hψ h2 ring C e p).ctl.mark = .closing ∧
       ((stepV3 hψ h2 ring C e p).ctl.tok = .none ∨
        (stepV3 hψ h2 ring C e p).ctl.tok = .seek ∨
        (stepV3 hψ h2 ring C e p).ctl.tok = .sweep)) := by
  have hr := rowV3_seek_eq_seek2 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  by_cases hpe : p = e
  · subst p
    have hleft :
        stepV3 hψ h2 ring C e e =
          (seekStageV3 (C e) (C (ring.rightNeighbor e))).1 := by
      simp [stepV3, protocolV3, PopulationProtocol.step, hr]
    rw [hleft]
    cases hrr : atRootB (C (ring.rightNeighbor e)) <;>
      cases hl : atRootB (C e) <;>
      simp [seekStageV3, hrr, hl, setControl]
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      have hright :
          stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
            (seekStageV3 (C e) (C (ring.rightNeighbor e))).2 := by
        simp [stepV3, protocolV3, PopulationProtocol.step, hr, hpe]
      rw [hright]
      cases hrr : atRootB (C (ring.rightNeighbor e)) <;>
        cases hl : atRootB (C e) <;>
        simp [seekStageV3, hrr, hl, setControl]
    · left
      rw [stepV3_other hψ h2 ring C e p hpe hpr]


private theorem seek_post_openR_old_seek2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek)
    (ho : (stepV3 hψ h2 ring C e p).ctl.tok = .openR) :
    (stepV3 hψ h2 ring C e p).ctl = (C p).ctl := by
  rcases seek_step_ctl_shape_seek2 hψ h2 ring C e p hb with h | h
  · exact h
  · rcases h.2 with h0 | hs | hw
    · simp [h0] at ho
    · simp [hs] at ho
    · simp [hw] at ho

private theorem mainClear_phys_frame_seek2
    {u v : Cell ψ κ τ} (hp : u.phys = v.phys)
    (hm : MainClearV3 v) : MainClearV3 u := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at hm ⊢
  simpa [eraseCellV3, R2Coherence.raw, hp] using hm

/-- R1 is genuinely frame-only under SEEK. -/
theorem openRForwardMainClear_seek_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hR1 : OpenRForwardMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    OpenRForwardMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  intro owner hOpenR d
  have hCtl := seek_post_openR_old_seek2 hψ h2 ring C e owner hb hOpenR
  have hOld : (C owner).ctl.tok = .openR := by
    rw [hCtl] at hOpenR
    exact hOpenR
  have hRaw :
      raw (stepV3 hψ h2 ring C e owner) = raw (C owner) := by
    change
      (stepV3 hψ h2 ring C e owner).phys.base.core.core =
        (C owner).phys.base.core.core
    exact congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core)
      (seek_step_phys_eq_seek2 hψ h2 ring C e hb owner)
  have hv :
      (raw (stepV3 hψ h2 ring C e owner)).label.val =
        (raw (C owner)).label.val :=
    congrArg (fun x : BoundedAgentState ψ κ => x.label.val) hRaw
  have hdC : d.val < ψ - (raw (C owner)).label.val := by
    simpa only [hv] using d.isLt
  let dC : Fin (ψ - (raw (C owner)).label.val) := ⟨d.val, hdC⟩
  have hm := hR1 owner hOld dC
  exact mainClear_phys_frame_seek2
    (seek_step_phys_eq_seek2 hψ h2 ring C e hb
      (R2Coherence.fwd ring owner d.val))
    (by simpa [dC] using hm)


/-- Exact first residual: already identified in `ReachableSeek`.  It is needed
because the nonroot/nonroot SEEK arm puts `.seek` at the initiator. -/
abbrev SeekSPreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  SeekIncomingSweepOpenROverlapClearWideSeekPreservationV31
    (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring

/-- Exact additional strong-R2 debt: only genuinely new sweeps are charged
here.  Surviving sweeps are covered by the old strong-R2 frame argument. -/
def SeekFreshSweepPendingFootprintOwnedV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e sweep owner p : Fin n),
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek →
    (stepV3 hψ h2 ring C e sweep).ctl.tok = .sweep →
    (C sweep).ctl.tok ≠ .sweep →
    PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner →
    InSweepWideReadV31 ring (stepV3 hψ h2 ring C e) sweep p →
    InOpenRFreshFootprintV31 ring (stepV3 hψ h2 ring C e) owner p →
      PhaseOwnedV31 (stepV3 hψ h2 ring C e p)

/-- Package the remaining R2 transport as a separately auditable obligation.
The old-R2 half and surviving-sweep half are controller/label frames; the only
semantic addition is `SeekFreshSweepPendingFootprintOwnedV31`. -/
def SeekStrongR2PreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek →
    OpenRPhaseOwnershipDisjointStrongV31 ring
      (stepV3 hψ h2 ring C e)

theorem seekStep_reachable_full
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hS : SeekSPreservationV31 (κ := κ) (τ := τ) hψ h2 ring)
    (hR2 : SeekStrongR2PreservationV31 (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    ReachablePhaseFactsPlus4StrongR2V31 ring
      (stepV3 hψ h2 ring C e) := by
  have hP3 := reachablePhaseFactsPlus3_seek_step
    hψ h2 ring C e hGeom hTrace hPlus hb
  have hSD := hS C e hTrace hGeom hPlus hb
  have hR1D := openRForwardMainClear_seek_step
    hψ h2 ring C e hPlus.2.2.1 hb
  have hR2D := hR2 C e hPlus hb
  exact ⟨hP3, hSD, hR1D, hR2D⟩



end R2CoherenceV31ReachableSeek2
