import Leader.Wu.Coherence.ReachableSound
import Leader.Wu.Coherence.ReachableSealed
import Leader.Wu.Coherence.ReachableOpenHazardPrepaid
import Leader.Wu.Coherence.ReachableMixed
import Leader.Wu.Coherence.ReachableCommitOverlap
import Leader.Wu.Coherence.ReachableReleaseWide
import Leader.Wu.Coherence.ReachableSweepStrongTail


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachableSoundInstances


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableSound


variable {n ψ κ τ : Nat}


/-- MIXED's first unexported tail field after its installed S residual. -/
def MixedOpenRForwardMainClearPreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .mixed →
      OpenRForwardMainClearV31 ring (stepV3 hψ h2 ring C e)


/-- MIXED's second unexported tail field. -/
def MixedStrongR2PreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .mixed →
      OpenRPhaseOwnershipDisjointStrongV31 ring
        (stepV3 hψ h2 ring C e)


theorem stepPreservesV31_seek_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hS : R2CoherenceV31ReachableSeek2.SeekSPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hR2 : R2CoherenceV31ReachableSeek2.SeekStrongR2PreservationV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    StepPreservesV31_seek (κ := κ) (τ := τ) hψ h2 ring := by
  exact R2CoherenceV31ReachableSound.stepPreservesV31_seek_of_residuals
    hψ h2 ring hS hR2


theorem stepPreservesV31_sweep_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hP6 : R2CoherenceV31ReachableSweep2.SweepCurrentOpenRFreshPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hTail : R2CoherenceV31ReachableSweep2.SweepStrongTailPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    StepPreservesV31_sweep (κ := κ) (τ := τ) hψ h2 ring := by
  exact R2CoherenceV31ReachableSweep2.stepPreservesV31_sweep_of_residuals
    hψ h2 ring hP6 hTail


theorem stepPreservesV31_commit_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    StepPreservesV31_commit (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace hPlus hb
  exact R2CoherenceV31ReachableThreeBranches4.commitStep_reachable_full
    hψ h2 ring C e hGeom hTrace hPlus hb


theorem stepPreservesV31_sealed_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    StepPreservesV31_sealed (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace hPlus hb
  exact R2CoherenceV31ReachableSealed.sealedStep_reachable_full
    hψ h2 ring C e hGeom hTrace hPlus hb

theorem stepPreservesV31_openHazard_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hFresh : R2CoherenceV31ReachableOpenHazard.OpenHazardFreshSeekPrepaidV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    StepPreservesV31_openHazard (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace hPlus hb
  exact R2CoherenceV31ReachableOpenHazard2.openHazardStep_reachable_full
    hψ h2 ring hFresh C e hGeom hTrace hPlus hb


theorem stepPreservesV31_mixed_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hS : R2CoherenceV31ReachableMixed.MixedSeekIncomingSweepOpenROverlapClearWidePreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hR1 : MixedOpenRForwardMainClearPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hR2 : MixedStrongR2PreservationV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    StepPreservesV31_mixed (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace hPlus hb
  have hP3 := R2CoherenceV31ReachableMixed.reachablePhaseFactsPlus3_mixed_step
    hψ h2 ring C e hGeom hTrace hPlus hb
  have hSD := hS C e hGeom hTrace hPlus hb
  have hR1D := hR1 C e hGeom hTrace hPlus hb
  have hR2D := hR2 C e hGeom hTrace hPlus hb
  exact ⟨hP3, hSD, hR1D, hR2D⟩


theorem stepPreservesV31_release_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hP7 : R2CoherenceV31ReachableRelease.ReleaseScrubLIncomingOpenRFreshPreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hP8 : R2CoherenceV31ReachableRelease2.ReleaseSweepOpenROverlapClearPreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hP9 : R2CoherenceV31ReachableRelease3.ReleaseSweepOpenROverlapClearWidePreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hS : R2CoherenceV31ReachableRelease3.ReleaseSeekIncomingSweepOpenROverlapClearWidePreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hR2 : R2CoherenceV31ReachableRelease3.ReleaseStrongR2PreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring) :
    StepPreservesV31_release (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace hPlus hb
  exact R2CoherenceV31ReachableRelease3.releaseStep_reachable_full
    hψ h2 ring hP7 hP8 hP9 hS hR2 C e hGeom hTrace hPlus hb


/-- SCRUBL: Facts close; P7/P8/P9/S/R1/strong-R2 remain unassembled. -/
theorem stepPreservesV31_scrubL_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (h : StepPreservesV31_scrubL (κ := κ) (τ := τ) hψ h2 ring) :
    StepPreservesV31_scrubL (κ := κ) (τ := τ) hψ h2 ring := h


/-- OPEN-R: P1-P9 close; standard-payload S/R1/strong-R2 remain. -/
theorem stepPreservesV31_openR_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (h : StepPreservesV31_openR (κ := κ) (τ := τ) hψ h2 ring) :
    StepPreservesV31_openR (κ := κ) (τ := τ) hψ h2 ring := h


/-- OPEN-NO-HAZARD: chain seam is needed for Facts/P7; S and R1 remain. -/
theorem stepPreservesV31_openNoHazard_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (h : StepPreservesV31_openNoHazard (κ := κ) (τ := τ) hψ h2 ring) :
    StepPreservesV31_openNoHazard (κ := κ) (τ := τ) hψ h2 ring := h

theorem reachableSound_of_installed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hSeekS : R2CoherenceV31ReachableSeek2.SeekSPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hSeekR2 : R2CoherenceV31ReachableSeek2.SeekStrongR2PreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hSweepP6 : R2CoherenceV31ReachableSweep2.SweepCurrentOpenRFreshPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hSweepTail : R2CoherenceV31ReachableSweep2.SweepStrongTailPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hHaz : R2CoherenceV31ReachableOpenHazard.OpenHazardFreshSeekPrepaidV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hMixedS : R2CoherenceV31ReachableMixed.MixedSeekIncomingSweepOpenROverlapClearWidePreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hMixedR1 : MixedOpenRForwardMainClearPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hMixedR2 : MixedStrongR2PreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hReleaseP7 : R2CoherenceV31ReachableRelease.ReleaseScrubLIncomingOpenRFreshPreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hReleaseP8 : R2CoherenceV31ReachableRelease2.ReleaseSweepOpenROverlapClearPreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hReleaseP9 : R2CoherenceV31ReachableRelease3.ReleaseSweepOpenROverlapClearWidePreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hReleaseS : R2CoherenceV31ReachableRelease3.ReleaseSeekIncomingSweepOpenROverlapClearWidePreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hReleaseR2 : R2CoherenceV31ReachableRelease3.ReleaseStrongR2PreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hScrubL : StepPreservesV31_scrubL (κ := κ) (τ := τ) hψ h2 ring)
    (hOpenR : StepPreservesV31_openR (κ := κ) (τ := τ) hψ h2 ring)
    (hOpenNoHazard : StepPreservesV31_openNoHazard (κ := κ) (τ := τ) hψ h2 ring) :
    ∀ C : FC n ψ κ τ,
      ReachableFromQuarantineV31 hψ h2 ring C →
        ReachablePhaseFactsPlus4StrongR2V31 ring C := by
  have hSeek := stepPreservesV31_seek_of_residuals
    hψ h2 ring hSeekS hSeekR2
  have hSweep := stepPreservesV31_sweep_of_residuals
    hψ h2 ring hSweepP6 hSweepTail
  have hCommit := stepPreservesV31_commit_of_residuals
    (κ := κ) (τ := τ) hψ h2 ring
  have hRelease := stepPreservesV31_release_of_residuals
    hψ h2 ring hReleaseP7 hReleaseP8 hReleaseP9 hReleaseS hReleaseR2
  have hSealed := stepPreservesV31_sealed_of_residuals
    (κ := κ) (τ := τ) hψ h2 ring
  have hOpenHazard := stepPreservesV31_openHazard_of_residuals
    hψ h2 ring hHaz
  have hMixed := stepPreservesV31_mixed_of_residuals
    hψ h2 ring hMixedS hMixedR1 hMixedR2
  exact R2CoherenceV31ReachableSound.reachableSound_of_branchSteps
    hψ h2 ring hSeek hSweep hCommit hRelease
    (stepPreservesV31_scrubL_of_residuals hψ h2 ring hScrubL)
    (stepPreservesV31_openR_of_residuals hψ h2 ring hOpenR)
    hSealed hOpenHazard
    (stepPreservesV31_openNoHazard_of_residuals hψ h2 ring hOpenNoHazard)
    hMixed
    (R2CoherenceV31ReachableSound.birthEntrancePayloadV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (R2CoherenceV31Closure2.electionGeometryStepV31
      (κ := κ) (τ := τ) hψ h2 ring)


end R2CoherenceV31ReachableSoundInstances
