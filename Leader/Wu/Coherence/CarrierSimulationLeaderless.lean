import Leader.Wu.Coherence.CarrierSimulationAdmission
import Leader.Wu.Coherence.BirthQuarantine

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace R2CoherenceV31FinalSimulation4

open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open R2CoherenceV31FinalSimulation
open R2CoherenceV31FinalSimulation2
open R2CoherenceV31FinalSimulation3
open R2CoherenceV31Mission R2CoherenceV31Step
open R2CoherenceV31Closure
open R2CoherenceV31BirthQuarantine

variable {n psi kappa tau : Nat}

/-- Every current concrete birth entrance still has a physical leader:
`quarantineInitV31` changes only the V3.1 controller. -/
theorem birthEntranceV1_hasLeader
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (Q : R2CoherenceV31.FC n psi kappa tau)
    (hB : BirthEntranceV1 hpsi h2 ring Q) :
    R2CoherenceV31Entrance.HasLeaderV31 Q := by
  rcases hB.1 with ⟨C0, C, hEnt, hQ⟩
  rcases hEnt with ⟨s, hReady, hRun, hOpen, hLeader⟩
  rcases hLeader with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rw [hQ]
  simpa [quarantineInitV31, R2CoherenceV31.setControl,
    R2CoherenceV31.raw] using hi

/-- The C1 source view is physically leaderless whenever the final source is. -/
theorem liftFinalV31_noLeader_of_finalLeaderless
    (C : FinalCandidateR2C.Config n psi kappa tau)
    (hL : FinalLeaderless C) :
    ¬ R2CoherenceV31Entrance.HasLeaderV31 (liftFinalV31 C) := by
  rintro ⟨i, hi⟩
  have hz : (C i).phys.phys.base.core.core.leader = false := by
    simpa [outputFinal] using hL i
  have ht : (C i).phys.phys.base.core.core.leader = true := by
    simpa [liftFinalV31, R2CoherenceV31MissionGate.finalV31View,
      R2CoherenceV31Entrance.openInitV31, R2Coherence.project,
      physicalConfig, R2CoherenceV31.raw] using hi
  rw [hz] at ht
  cases ht

/-- In particular, the tempting `pre = []` use of the old birth entrance is
impossible on the leaderless C1 source class. -/
theorem liftFinalV31_not_birthEntranceV1_of_finalLeaderless
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FinalCandidateR2C.Config n psi kappa tau)
    (hL : FinalLeaderless C) :
    ¬ BirthEntranceV1 hpsi h2 ring (liftFinalV31 C) := by
  intro hB
  exact (liftFinalV31_noLeader_of_finalLeaderless C hL)
    (birthEntranceV1_hasLeader hpsi h2 ring (liftFinalV31 C) hB)

/-- The C-final mission should start at the current admitted leaderless view,
not reconstruct an R1 birth history from an extensional admission predicate. -/
def C1FinalV31AdmittedEntrance
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (Q : R2CoherenceV31.FC n psi kappa tau) : Prop :=
  ∃ C : FinalCandidateR2C.Config n psi kappa tau,
    ConcreteB7AdmittedPassive hpsi h2 ring C ∧
      FinalLeaderless C ∧ FinalAllOpen C ∧
      Q = liftFinalV31 C

/-- Honest replacement for historical birth provenance: the admitted current
state itself must lie in the V3.1 closed domain. -/
def C1FinalV31AdmittedClosedResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  ∀ C : FinalCandidateR2C.Config n psi kappa tau,
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C → FinalAllOpen C →
    CoherenceClosedV31 hpsi h2 ring (liftFinalV31 C)

/-- For the admitted entrance, the old third residual is definitionally an
empty-prefix fact. -/
theorem c1FinalV31EntranceReachabilityResidual_of_admittedEntrance
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    C1FinalV31EntranceReachabilityResidual
      (kappa := kappa) (tau := tau)
      (C1FinalV31AdmittedEntrance
        (kappa := kappa) (tau := tau) hpsi h2 ring)
      hpsi h2 ring := by
  intro C hA hL hOpen
  refine ⟨liftFinalV31 C, [], ?_, rfl⟩
  exact ⟨C, hA, hL, hOpen, rfl⟩

/-- The state-only residual is exactly the generic mission's entrance bridge. -/
theorem c1FinalV31AdmittedEntranceClosedBridge
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hClosed : C1FinalV31AdmittedClosedResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    EntranceClosedBridgeV31V1
      (κ := kappa) (τ := tau)
      (C1FinalV31AdmittedEntrance
        (kappa := kappa) (tau := tau) hpsi h2 ring)
      hpsi h2 ring := by
  intro Q hQ
  rcases hQ with ⟨C, hA, hL, hOpen, rfl⟩
  exact hClosed C hA hL hOpen

/-- No mission definition change is needed: instantiate its generic entrance
parameter with the admitted final-view image. -/
theorem c1FinalV31Mission_of_admittedClosed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hOpenNoHazard : OpenNoHazardCoherenceV31
      (κ := kappa) (τ := tau) hpsi h2 ring)
    (hClosed : C1FinalV31AdmittedClosedResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    PostBirthCheckIdCoherenceMissionV1
      (κ := kappa) (τ := tau)
      (C1FinalV31AdmittedEntrance
        (kappa := kappa) (tau := tau) hpsi h2 ring)
      hpsi h2 ring := by
  exact mission_of_bridge_and_openNoHazard
    (κ := kappa) (τ := tau)
    (C1FinalV31AdmittedEntrance
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    hpsi h2 ring hOpenNoHazard
    (c1FinalV31AdmittedEntranceClosedBridge
      (kappa := kappa) (tau := tau) hpsi h2 ring hClosed)

/-- The two admission strengthenings now compose with the trivial
admitted-entrance reachability and the installed word-simulation assembler. -/
theorem c1FinalV31SimulationObligation_of_admittedEntrance
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (hPassiveClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := kappa) (τ := tau) hpsi h2 ring)
    (hReady : C1FinalV31ReadyAlignedAdmission
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hFrame : C1FinalV31MainPathFrameAdmission
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    R2CoherenceV31MissionGate.C1FinalV31SimulationObligation
      (C1FinalV31AdmittedEntrance
        (kappa := kappa) (tau := tau) hpsi h2 ring)
      hpsi h2 ring := by
  apply R2CoherenceV31FinalSimulation.c1FinalV31SimulationObligation_of_stepSimulation
    (BirthEntrance := C1FinalV31AdmittedEntrance
      (kappa := kappa) (tau := tau) hpsi h2 ring)
    hpsi h2 ring
  · exact c1FinalV31EntranceReachabilityResidual_of_admittedEntrance
      (kappa := kappa) (tau := tau) hpsi h2 ring
  · exact hPassiveClosed
  · exact c1FinalV31OneStepSimulationResidual_of_admission
      (kappa := kappa) (tau := tau)
      hpsi h2 ring hn hReady hFrame

/-- Final reduction: the existing mission gate consumes the admitted entrance
without any historical birth-preimage theorem. -/
theorem c1CoherenceGate_of_admittedEntrance
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (hOpenNoHazard : OpenNoHazardCoherenceV31
      (κ := kappa) (τ := tau) hpsi h2 ring)
    (hAdmittedClosed : C1FinalV31AdmittedClosedResidual
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
  · exact c1FinalV31Mission_of_admittedClosed
      (kappa := kappa) (tau := tau)
      hpsi h2 ring hOpenNoHazard hAdmittedClosed
  · exact c1FinalV31SimulationObligation_of_admittedEntrance
      (kappa := kappa) (tau := tau)
      hpsi h2 ring hn hPassiveClosed hReady hFrame

end R2CoherenceV31FinalSimulation4
