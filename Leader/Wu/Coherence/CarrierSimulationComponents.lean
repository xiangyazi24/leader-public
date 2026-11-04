import Leader.Wu.Coherence.CarrierSimulationLeaderless
import Leader.Wu.Coherence.CarrierViewGate
import Leader.Wu.Coherence.ReachableFacts
import Leader.Wu.Coherence.ReachableBirthLabelProfile

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace R2CoherenceV31FinalSimulation5

open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open R2CoherenceV31FinalSimulation
open R2CoherenceV31FinalSimulation3
open R2CoherenceV31FinalSimulation4

variable {n psi kappa tau : Nat}

/-- Exact label clause of the admitted closed-domain residual. -/
def C1FinalV31AdmittedElectionGeometryResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ C : FinalCandidateR2C.Config n psi kappa tau,
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C → FinalAllOpen C →
      R2CoherenceV31Closure.ElectionGeometryV31 ring (liftFinalV31 C)

/-- Stronger producer-side label profile shared with the root-spacing route. -/
def C1FinalV31AdmittedLabelProfileResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ C : FinalCandidateR2C.Config n psi kappa tau,
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C → FinalAllOpen C →
      R2CoherenceV31ReachableRootSpacing.RootSpacingV31 ring
        (liftFinalV31 C)

/-- Current CHECK/ID coherence is not implied by writer passivity. -/
def C1FinalV31AdmittedCoherentPrefixesResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ C : FinalCandidateR2C.Config n psi kappa tau,
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C → FinalAllOpen C →
      R2CoherenceV31.CoherentPrefixesV3 ring (liftFinalV31 C)

/-- Future causal payload needed to obtain the future-quantified controller
soundness field of `CoherenceClosedV31`. -/
def C1FinalV31AdmittedReachablePhaseResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ C : FinalCandidateR2C.Config n psi kappa tau,
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C → FinalAllOpen C →
    ∀ w : List (Fin n),
      R2CoherenceV31ReachableFacts.ReachablePhaseFactsV31 ring
        (w.foldl (R2CoherenceV31.stepV3 hpsi h2 ring) (liftFinalV31 C))

/-- At word zero the admitted lift has open/none controls, so every phase
payload implication is vacuous. -/
theorem reachablePhaseFacts_liftFinalV31
    (ring : DirectedRing n)
    (C : FinalCandidateR2C.Config n psi kappa tau) :
    R2CoherenceV31ReachableFacts.ReachablePhaseFactsV31 ring
      (liftFinalV31 C) := by
  simp [R2CoherenceV31ReachableFacts.ReachablePhaseFactsV31,
    liftFinalV31, R2CoherenceV31MissionGate.finalV31View,
    R2CoherenceV31Entrance.openInitV31]

/-- The future reachable-phase residual is exactly strong enough for the
`ControllerSoundV3` field. -/
theorem controllerSoundV3_of_admittedReachablePhase
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hPhase : C1FinalV31AdmittedReachablePhaseResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    ∀ C : FinalCandidateR2C.Config n psi kappa tau,
      ConcreteB7AdmittedPassive hpsi h2 ring C →
      FinalLeaderless C → FinalAllOpen C →
        R2CoherenceV31.ControllerSoundV3 hpsi h2 ring (liftFinalV31 C) := by
  intro C hA hL hOpen
  unfold R2CoherenceV31.ControllerSoundV3
  intro w
  exact R2CoherenceV31ReachableFacts.reachablePhaseFacts_implies_shape
    ring _ (hPhase C hA hL hOpen w)

/-- Exact decomposition of the state-only residual. -/
theorem c1FinalV31AdmittedClosedResidual_of_components
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hGeom : C1FinalV31AdmittedElectionGeometryResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hCoh : C1FinalV31AdmittedCoherentPrefixesResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hPhase : C1FinalV31AdmittedReachablePhaseResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    C1FinalV31AdmittedClosedResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  intro C hA hL hOpen
  refine ⟨hGeom C hA hL hOpen, hCoh C hA hL hOpen, ?_⟩
  exact controllerSoundV3_of_admittedReachablePhase
    (kappa := kappa) (tau := tau) hpsi h2 ring hPhase
    C hA hL hOpen

/-- The generic mission needs no adjustment: only its entrance predicate is
instantiated with the admitted final-view image. -/
theorem c1FinalV31Mission_of_components
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hOpenNoHazard : R2CoherenceV31Step.OpenNoHazardCoherenceV31
      (κ := kappa) (τ := tau) hpsi h2 ring)
    (hGeom : C1FinalV31AdmittedElectionGeometryResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hCoh : C1FinalV31AdmittedCoherentPrefixesResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hPhase : C1FinalV31AdmittedReachablePhaseResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    R2CoherenceV31Mission.PostBirthCheckIdCoherenceMissionV1
      (κ := kappa) (τ := tau)
      (C1FinalV31AdmittedEntrance
        (kappa := kappa) (tau := tau) hpsi h2 ring)
      hpsi h2 ring := by
  exact c1FinalV31Mission_of_admittedClosed
    (kappa := kappa) (tau := tau) hpsi h2 ring hOpenNoHazard
    (c1FinalV31AdmittedClosedResidual_of_components
      (kappa := kappa) (tau := tau) hpsi h2 ring hGeom hCoh hPhase)

/-- Full C1 reduction.  The existing mission-gate consumer is used verbatim;
The two one-step admission strengthenings remain explicit. -/
theorem c1CoherenceGate_of_admitted_components
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (hOpenNoHazard : R2CoherenceV31Step.OpenNoHazardCoherenceV31
      (κ := kappa) (τ := tau) hpsi h2 ring)
    (hGeom : C1FinalV31AdmittedElectionGeometryResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hCoh : C1FinalV31AdmittedCoherentPrefixesResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hPhase : C1FinalV31AdmittedReachablePhaseResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hPassiveClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := kappa) (τ := tau) hpsi h2 ring)
    (hReady : C1FinalV31ReadyAlignedAdmission
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hFrame : C1FinalV31MainPathFrameAdmission
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    R2CoherenceV31MissionGate.C1CoherenceGate
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  apply R2CoherenceV31MissionGate.c1CoherenceGate_of_mission_and_simulation
    (BirthEntrance := C1FinalV31AdmittedEntrance
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    hpsi h2 ring
  · exact c1FinalV31Mission_of_components
      (kappa := kappa) (tau := tau) hpsi h2 ring
      hOpenNoHazard hGeom hCoh hPhase
  · exact c1FinalV31SimulationObligation_of_admittedEntrance
      (kappa := kappa) (tau := tau) hpsi h2 ring hn
      hPassiveClosed hReady hFrame

end R2CoherenceV31FinalSimulation5
