import Leader.Wu.Coherence.ReachableSoundInstances
import Leader.Wu.Coherence.CarrierSimulationComponents

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableSoundParametric

open R2CoherenceV31
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableSound
open R2CoherenceV31FinalSimulation
open R2CoherenceV31FinalSimulation4
open R2CoherenceV31FinalSimulation5
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C

variable {n ψ κ τ : Nat}

def ReachableFromV31
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n ψ κ τ) : Prop :=
  ∃ (C0 : R2CoherenceV31.FC n ψ κ τ) (w : List (Fin n)),
    Entrance C0 ∧ C = w.foldl (stepV3 hψ h2 ring) C0

theorem reachableFromV31_birth_iff
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n ψ κ τ) :
    ReachableFromV31
        (BirthEntranceV1 hψ h2 ring) hψ h2 ring C ↔
      ReachableFromQuarantineV31 hψ h2 ring C := by
  rfl

def StepPreservesBranchV31Parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (b : BranchV3) : Prop :=
  ∀ (C : R2CoherenceV31.FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromV31 Entrance hψ h2 ring C →
    ReachableSoundPayloadV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b →
      ReachableSoundPayloadV31 ring (stepV3 hψ h2 ring C e)

abbrev StepPreservesV31_seek_parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31Parametric
    (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ) Entrance hψ h2 ring .seek
abbrev StepPreservesV31_sweep_parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31Parametric
    (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ) Entrance hψ h2 ring .sweep
abbrev StepPreservesV31_commit_parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31Parametric
    (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ) Entrance hψ h2 ring .commit
abbrev StepPreservesV31_release_parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31Parametric
    (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ) Entrance hψ h2 ring .release
abbrev StepPreservesV31_scrubL_parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31Parametric
    (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ) Entrance hψ h2 ring .scrubL
abbrev StepPreservesV31_openR_parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31Parametric
    (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ) Entrance hψ h2 ring .openR
abbrev StepPreservesV31_sealed_parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31Parametric
    (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ) Entrance hψ h2 ring .sealed
abbrev StepPreservesV31_openHazard_parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31Parametric
    (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ) Entrance hψ h2 ring .openHazard
abbrev StepPreservesV31_openNoHazard_parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31Parametric
    (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ) Entrance hψ h2 ring .openNoHazard
abbrev StepPreservesV31_mixed_parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  StepPreservesBranchV31Parametric
    (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ) Entrance hψ h2 ring .mixed

def EntrancePayloadV31Parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (ring : DirectedRing n) : Prop :=
  ∀ C0, Entrance C0 → ReachableSoundPayloadV31 ring C0

def EntranceGeometryV31Parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (ring : DirectedRing n) : Prop :=
  ∀ C0, Entrance C0 → ElectionGeometryV31 ring C0

private theorem reachable_step_parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : R2CoherenceV31.FC n ψ κ τ) (e : Fin n)
    (h : ReachableFromV31 Entrance hψ h2 ring C) :
    ReachableFromV31 Entrance hψ h2 ring (stepV3 hψ h2 ring C e) := by
  rcases h with ⟨C0, w, hEnt, hC⟩
  refine ⟨C0, w ++ [e], hEnt, ?_⟩
  rw [List.foldl_append, ← hC]
  rfl

theorem electionGeometry_of_reachableFromV31
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hBase : EntranceGeometryV31Parametric Entrance ring)
    (hStep : ElectionGeometryStepV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : R2CoherenceV31.FC n ψ κ τ)
    (hReach : ReachableFromV31 Entrance hψ h2 ring C) :
    ElectionGeometryV31 ring C := by
  rcases hReach with ⟨C0, w, hEnt, rfl⟩
  have carry : ∀ (v : List (Fin n)) (D : R2CoherenceV31.FC n ψ κ τ),
      ElectionGeometryV31 ring D →
      ElectionGeometryV31 ring (v.foldl (stepV3 hψ h2 ring) D) := by
    intro v
    induction v with
    | nil => intro D h; simpa using h
    | cons e v ih =>
        intro D h
        simp only [List.foldl_cons]
        exact ih _ (hStep D e h)
  exact carry w C0 (hBase C0 hEnt)

theorem reachableSound_parametric
    (Entrance : R2CoherenceV31.FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hSeek : StepPreservesV31_seek_parametric Entrance hψ h2 ring)
    (hSweep : StepPreservesV31_sweep_parametric Entrance hψ h2 ring)
    (hCommit : StepPreservesV31_commit_parametric Entrance hψ h2 ring)
    (hRelease : StepPreservesV31_release_parametric Entrance hψ h2 ring)
    (hScrubL : StepPreservesV31_scrubL_parametric Entrance hψ h2 ring)
    (hOpenR : StepPreservesV31_openR_parametric Entrance hψ h2 ring)
    (hSealed : StepPreservesV31_sealed_parametric Entrance hψ h2 ring)
    (hOpenHazard : StepPreservesV31_openHazard_parametric Entrance hψ h2 ring)
    (hOpenNoHazard : StepPreservesV31_openNoHazard_parametric Entrance hψ h2 ring)
    (hMixed : StepPreservesV31_mixed_parametric Entrance hψ h2 ring)
    (hBase : EntrancePayloadV31Parametric Entrance ring)
    (hGeomBase : EntranceGeometryV31Parametric Entrance ring)
    (hGeomStep : ElectionGeometryStepV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    ∀ C : R2CoherenceV31.FC n ψ κ τ,
      ReachableFromV31 Entrance hψ h2 ring C →
        ReachableSoundPayloadV31 ring C := by
  intro C hTrace
  rcases hTrace with ⟨C0, w, hEnt, hC⟩
  have carry : ∀ (v : List (Fin n)) (D : R2CoherenceV31.FC n ψ κ τ),
      ReachableFromV31 Entrance hψ h2 ring D →
      ElectionGeometryV31 ring D →
      ReachableSoundPayloadV31 ring D →
      ReachableSoundPayloadV31 ring (v.foldl (stepV3 hψ h2 ring) D) := by
    intro v
    induction v with
    | nil => intro D _ _ hP; simpa using hP
    | cons e v ih =>
        intro D hTraceD hGeomD hPD
        simp only [List.foldl_cons]
        have hNext : ReachableSoundPayloadV31 ring
            (stepV3 hψ h2 ring D e) := by
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
          (reachable_step_parametric Entrance hψ h2 ring D e hTraceD)
          (hGeomStep D e hGeomD) hNext
  rw [hC]
  exact carry w C0 ⟨C0, [], hEnt, rfl⟩
    (hGeomBase C0 hEnt) (hBase C0 hEnt)

private theorem liftFinalV31_tok_none
    (C : FinalCandidateR2C.Config n ψ κ τ) (i : Fin n) :
    (liftFinalV31 C i).ctl.tok = .none := by
  rfl

/-- Strong payload, not merely the basic Facts payload, is free at the admitted
lift because every extra conjunct is guarded by seek/sweep/scrubL/openR. -/
theorem reachableSoundPayload_liftFinalV31
    (ring : DirectedRing n)
    (C : FinalCandidateR2C.Config n ψ κ τ) :
    ReachableSoundPayloadV31 ring (liftFinalV31 C) := by
  have hFacts := reachablePhaseFacts_liftFinalV31 ring C
  refine ⟨⟨⟨⟨hFacts, ?_⟩, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · intro e hs
    rw [liftFinalV31_tok_none C (ring.rightNeighbor e)] at hs
    cases hs
  · intro e owner hs
    rw [liftFinalV31_tok_none C e] at hs
    cases hs
  · intro e owner hs
    rw [liftFinalV31_tok_none C e] at hs
    cases hs
  · intro e owner hs
    rw [liftFinalV31_tok_none C (ring.rightNeighbor e)] at hs
    cases hs
  · intro e hs
    rw [liftFinalV31_tok_none C e] at hs
    cases hs
  · constructor
    · intro e owner hs
      rw [liftFinalV31_tok_none C e] at hs
      cases hs
    · intro sweep owner p hs
      rw [liftFinalV31_tok_none C sweep] at hs
      cases hs

theorem c1FinalV31AdmittedReachablePhaseResidual_of_parametricBranchSteps
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hGeom : C1FinalV31AdmittedElectionGeometryResidual
      (kappa := κ) (tau := τ) hψ h2 ring)
    (hSeek : StepPreservesV31_seek_parametric
      (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
      (C1FinalV31AdmittedEntrance
        (n:=n) (psi:=ψ) (kappa:=κ) (tau:=τ) hψ h2 ring)
      hψ h2 ring)
    (hSweep : StepPreservesV31_sweep_parametric
      (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
      (C1FinalV31AdmittedEntrance
        (n:=n) (psi:=ψ) (kappa:=κ) (tau:=τ) hψ h2 ring)
      hψ h2 ring)
    (hCommit : StepPreservesV31_commit_parametric
      (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
      (C1FinalV31AdmittedEntrance
        (n:=n) (psi:=ψ) (kappa:=κ) (tau:=τ) hψ h2 ring)
      hψ h2 ring)
    (hRelease : StepPreservesV31_release_parametric
      (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
      (C1FinalV31AdmittedEntrance
        (n:=n) (psi:=ψ) (kappa:=κ) (tau:=τ) hψ h2 ring)
      hψ h2 ring)
    (hScrubL : StepPreservesV31_scrubL_parametric
      (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
      (C1FinalV31AdmittedEntrance
        (n:=n) (psi:=ψ) (kappa:=κ) (tau:=τ) hψ h2 ring)
      hψ h2 ring)
    (hOpenR : StepPreservesV31_openR_parametric
      (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
      (C1FinalV31AdmittedEntrance
        (n:=n) (psi:=ψ) (kappa:=κ) (tau:=τ) hψ h2 ring)
      hψ h2 ring)
    (hSealed : StepPreservesV31_sealed_parametric
      (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
      (C1FinalV31AdmittedEntrance
        (n:=n) (psi:=ψ) (kappa:=κ) (tau:=τ) hψ h2 ring)
      hψ h2 ring)
    (hOpenHazard : StepPreservesV31_openHazard_parametric
      (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
      (C1FinalV31AdmittedEntrance
        (n:=n) (psi:=ψ) (kappa:=κ) (tau:=τ) hψ h2 ring)
      hψ h2 ring)
    (hOpenNoHazard : StepPreservesV31_openNoHazard_parametric
      (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
      (C1FinalV31AdmittedEntrance
        (n:=n) (psi:=ψ) (kappa:=κ) (tau:=τ) hψ h2 ring)
      hψ h2 ring)
    (hMixed : StepPreservesV31_mixed_parametric
      (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
      (C1FinalV31AdmittedEntrance
        (n:=n) (psi:=ψ) (kappa:=κ) (tau:=τ) hψ h2 ring)
      hψ h2 ring) :
    C1FinalV31AdmittedReachablePhaseResidual
      (kappa := κ) (tau := τ) hψ h2 ring := by
  let Entrance : R2CoherenceV31.FC n ψ κ τ → Prop :=
    C1FinalV31AdmittedEntrance
      (n:=n) (psi:=ψ) (kappa:=κ) (tau:=τ) hψ h2 ring
  have hBase : EntrancePayloadV31Parametric
      (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ) Entrance ring := by
    intro Q hQ
    rcases hQ with ⟨C, _, _, _, rfl⟩
    exact reachableSoundPayload_liftFinalV31 ring C
  have hGeomBase : EntranceGeometryV31Parametric
      (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ) Entrance ring := by
    intro Q hQ
    rcases hQ with ⟨C, hA, hL, hOpen, rfl⟩
    exact hGeom C hA hL hOpen
  have hSound := reachableSound_parametric
    (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
    Entrance hψ h2 ring hSeek hSweep hCommit hRelease hScrubL hOpenR
    hSealed hOpenHazard hOpenNoHazard hMixed hBase hGeomBase
    (R2CoherenceV31Closure2.electionGeometryStepV31
      (κ := κ) (τ := τ) hψ h2 ring)
  intro C hA hL hOpen w
  have hReach : ReachableFromV31
      (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
      Entrance hψ h2 ring
      (w.foldl (stepV3 hψ h2 ring) (liftFinalV31 C)) :=
    ⟨liftFinalV31 C, w, ⟨C, hA, hL, hOpen, rfl⟩, rfl⟩
  exact (hSound _ hReach).1.1.1.1

end R2CoherenceV31ReachableSoundParametric
