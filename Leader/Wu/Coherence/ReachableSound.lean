import Leader.Wu.Coherence.ReachableOpenRIncomingSeek
import Leader.Wu.Coherence.ReachableSeekStrong
import Leader.Wu.Coherence.ReachableScrubL
import Leader.Wu.Coherence.ReachableRelease
import Leader.Wu.Coherence.ReachableCommitOwnerFresh

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableSound

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableOpenNoHazard4

variable {n ψ κ τ : Nat}

abbrev ReachableSoundPayloadV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ReachablePhaseFactsPlus4StrongR2V31 ring C

private def StepPreservesBranchV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (b : BranchV3) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachableSoundPayloadV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b →
      ReachableSoundPayloadV31 ring (stepV3 hψ h2 ring C e)

def StepPreservesV31_seek
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31 (κ := κ) (τ := τ) hψ h2 ring .seek

def StepPreservesV31_sweep
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31 (κ := κ) (τ := τ) hψ h2 ring .sweep

def StepPreservesV31_commit
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31 (κ := κ) (τ := τ) hψ h2 ring .commit

def StepPreservesV31_release
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31 (κ := κ) (τ := τ) hψ h2 ring .release

def StepPreservesV31_scrubL
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31 (κ := κ) (τ := τ) hψ h2 ring .scrubL

def StepPreservesV31_openR
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31 (κ := κ) (τ := τ) hψ h2 ring .openR

def StepPreservesV31_sealed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31 (κ := κ) (τ := τ) hψ h2 ring .sealed

def StepPreservesV31_openHazard
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31 (κ := κ) (τ := τ) hψ h2 ring .openHazard

def StepPreservesV31_openNoHazard
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31 (κ := κ) (τ := τ) hψ h2 ring .openNoHazard

def StepPreservesV31_mixed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31 (κ := κ) (τ := τ) hψ h2 ring .mixed

def BirthEntrancePayloadV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C0 : FC n ψ κ τ,
    BirthEntranceV1 hψ h2 ring C0 → ReachableSoundPayloadV31 ring C0


private theorem reachable_step_sound
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C) :
    ReachableFromQuarantineV31 hψ h2 ring (stepV3 hψ h2 ring C e) := by
  rcases hTrace with ⟨C0, w, hBirth, hC⟩
  refine ⟨C0, w ++ [e], hBirth, ?_⟩
  rw [List.foldl_append, ← hC]
  rfl

theorem birthEntrancePayloadV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    BirthEntrancePayloadV31 (κ := κ) (τ := τ) hψ h2 ring := by
  intro C0 hBirth
  exact R2CoherenceV31ReachableOpenNoHazard4.reachablePhaseFactsPlus4StrongR2_entrance hψ h2 ring C0 hBirth

theorem reachableSound_of_branchSteps
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hSeek : StepPreservesV31_seek (κ := κ) (τ := τ) hψ h2 ring)
    (hSweep : StepPreservesV31_sweep (κ := κ) (τ := τ) hψ h2 ring)
    (hCommit : StepPreservesV31_commit (κ := κ) (τ := τ) hψ h2 ring)
    (hRelease : StepPreservesV31_release (κ := κ) (τ := τ) hψ h2 ring)
    (hScrubL : StepPreservesV31_scrubL (κ := κ) (τ := τ) hψ h2 ring)
    (hOpenR : StepPreservesV31_openR (κ := κ) (τ := τ) hψ h2 ring)
    (hSealed : StepPreservesV31_sealed (κ := κ) (τ := τ) hψ h2 ring)
    (hOpenHazard : StepPreservesV31_openHazard (κ := κ) (τ := τ) hψ h2 ring)
    (hOpenNoHazard : StepPreservesV31_openNoHazard (κ := κ) (τ := τ) hψ h2 ring)
    (hMixed : StepPreservesV31_mixed (κ := κ) (τ := τ) hψ h2 ring)
    (hBase : BirthEntrancePayloadV31 (κ := κ) (τ := τ) hψ h2 ring)
    (hGeomStep : ElectionGeometryStepV31 (κ := κ) (τ := τ) hψ h2 ring) :
    ∀ C : FC n ψ κ τ,
      ReachableFromQuarantineV31 hψ h2 ring C →
        ReachableSoundPayloadV31 ring C := by
  intro C hTrace
  rcases hTrace with ⟨C0, w, hBirth, hC⟩
  have carry :
      ∀ (v : List (Fin n)) (D : FC n ψ κ τ),
        ReachableFromQuarantineV31 hψ h2 ring D →
        ElectionGeometryV31 ring D →
        ReachableSoundPayloadV31 ring D →
          ReachableSoundPayloadV31 ring
            (v.foldl (stepV3 hψ h2 ring) D) := by
    intro v
    induction v with
    | nil =>
        intro D _ _ hP
        simpa using hP
    | cons e v ih =>
        intro D hTraceD hGeomD hPD
        simp only [List.foldl_cons]
        have hNext :
            ReachableSoundPayloadV31 ring (stepV3 hψ h2 ring D e) := by
          cases hbr : branchAtV3 hψ h2 (D e) (D (ring.rightNeighbor e)) with
          | seek => exact hSeek D e hGeomD hTraceD hPD hbr
          | sweep => exact hSweep D e hGeomD hTraceD hPD hbr
          | commit => exact hCommit D e hGeomD hTraceD hPD hbr
          | release => exact hRelease D e hGeomD hTraceD hPD hbr
          | scrubL => exact hScrubL D e hGeomD hTraceD hPD hbr
          | openR => exact hOpenR D e hGeomD hTraceD hPD hbr
          | sealed => exact hSealed D e hGeomD hTraceD hPD hbr
          | openHazard => exact hOpenHazard D e hGeomD hTraceD hPD hbr
          | openNoHazard => exact hOpenNoHazard D e hGeomD hTraceD hPD hbr
          | mixed => exact hMixed D e hGeomD hTraceD hPD hbr
        exact ih _
          (reachable_step_sound hψ h2 ring D e hTraceD)
          (hGeomStep D e hGeomD) hNext
  rw [hC]
  exact carry w C0 ⟨C0, [], hBirth, rfl⟩ hBirth.2 (hBase C0 hBirth)

theorem stepPreservesV31_seek_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hS : R2CoherenceV31ReachableSeek2.SeekSPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hR2 : R2CoherenceV31ReachableSeek2.SeekStrongR2PreservationV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    StepPreservesV31_seek (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace hPlus hb
  exact R2CoherenceV31ReachableSeek2.seekStep_reachable_full
    hψ h2 ring hS hR2 C e hGeom hTrace hPlus hb

end R2CoherenceV31ReachableSound
