import Leader.Wu.Coherence.PostBirthStatement
import Leader.Wu.Entrance.ComposedRow
import Leader.Wu.Entrance.PassiveProjection

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace R2CoherenceV31MissionGate

open BirthLeaderlessBirthMassRenewal
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C

variable {n psi kappa tau : Nat}
variable {ring : DirectedRing n}

/-!
SOURCE — Leader/Wu/Coherence/PostBirthStatement.lean:22-33:

  def PostBirthCheckIdCoherenceMissionV1
      (BirthEntranceV1 : R2CoherenceV31.FC n psi kappa tau -> Prop)
      (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
    forall C0, BirthEntranceV1 C0 -> forall w,
      R2CoherenceV31.ElectionGeometryV31 ring
          (w.foldl (R2CoherenceV31.stepV3 hpsi h2 ring) C0) /\
      R2CoherenceV31.CoherentPrefixesV3 ring
          (w.foldl (R2CoherenceV31.stepV3 hpsi h2 ring) C0).

FINAL-CARRIER ADMISSION SURFACE:
* Leader/Wu/Entrance/PassiveAdmission.lean:85-94:
  `ConcreteB7AdmittedPassive` is FinalNoProducer + FinalWriterPassive +
  FinalAllOpen + every-edge no-garbage/HOST/ProposalNoWrite.
* Leader/Wu/Entrance/ComposedRow.lean:636-637:
  `FinalLeaderless C := forall i, outputFinal (C i) = false`.
* Leader/Wu/Entrance/ComposedRow.lean:663-664:
  `FinalAllOpen C := forall i, R2Coherence.OpenControl (C i).phys`.

PROJECTION CENSUS:
* Leader/Wu/Entrance/ComposedRow.lean:583-585 exports
  `physicalConfig : Config -> R2Coherence.FC`.
* Leader/Wu/Coherence/SixTokenController.lean:388-389 exports
  `project : R2Coherence.FC -> R2.FC`, retaining the complete R2 cell/fuel.
* Leader/Wu/Coherence/OpenEntrance.lean:23-27 exports
  `openInitV31 : R2.FC -> R2CoherenceV31.FC`, installing open/none V3.1
  control.
* Leader/Wu/Entrance/Admission.lean:69-71 `finalBase` erases farther to bare R1,
  so it is too lossy to reconstruct the V3.1 carrier.

There is no current final `stepConcrete` -> V3.1 `stepV3` same-word theorem.
The branch files only expose V3.1 -> R2Coherence erasures.  The existing
Leader/Wu/Entrance/PassiveProjection.lean:130-169 theorem transports `finalBase` to R1
`step1`, which is also below the R2/V3.1 information required here.
-/

/-- Canonical final-state observation at the V3.1 type boundary.
It forgets the outer B9 controller and old R2C controller, keeps the complete
R2 physical cell, then installs V3.1 open/none control. -/
def finalV31View
    (C : Config n psi kappa tau) : R2CoherenceV31.FC n psi kappa tau :=
  R2CoherenceV31Entrance.openInitV31
    (R2Coherence.project (physicalConfig C))

def C1FinalV31SimulationObligation
    (BirthEntrance : R2CoherenceV31.FC n psi kappa tau -> Prop)
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  forall (C : Config n psi kappa tau) (w : List (Fin n)),
    ConcreteB7AdmittedPassive hpsi h2 ring C ->
    FinalLeaderless C ->
    FinalAllOpen C ->
    AliveAlong
        (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
        FinalLeaderless C w ->
    exists Q : R2CoherenceV31.FC n psi kappa tau,
      exists pre : List (Fin n),
        BirthEntrance Q /\
        finalV31View C =
          pre.foldl (R2CoherenceV31.stepV3 hpsi h2 ring) Q /\
        finalV31View
            (w.foldl
              (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring) C) =
          w.foldl (R2CoherenceV31.stepV3 hpsi h2 ring)
            (finalV31View C)


def C1CoherenceGate
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  forall (C : Config n psi kappa tau) (w : List (Fin n)),
    ConcreteB7AdmittedPassive hpsi h2 ring C ->
    FinalLeaderless C ->
    FinalAllOpen C ->
    AliveAlong
        (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
        FinalLeaderless C w ->
    R2CoherenceV31Closure.ElectionGeometryV31 ring
        (finalV31View
          (w.foldl
            (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring) C)) /\
      R2CoherenceV31.CoherentPrefixesV3 ring
        (finalV31View
          (w.foldl
            (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring) C))


theorem c1CoherenceGate_of_mission_and_simulation
    (BirthEntrance : R2CoherenceV31.FC n psi kappa tau -> Prop)
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (hMission :
      R2CoherenceV31Mission.PostBirthCheckIdCoherenceMissionV1
        BirthEntrance hpsi h2 ring)
    (hSim :
      C1FinalV31SimulationObligation BirthEntrance hpsi h2 ring) :
    C1CoherenceGate (kappa := kappa) (tau := tau) hpsi h2 ring := by
  intro C w hA hLeaderless hOpen hAlive
  rcases hSim C w hA hLeaderless hOpen hAlive with
    ⟨Q, pre, hBirth, hStart, hWord⟩
  have hm := hMission Q hBirth (pre ++ w)
  rw [List.foldl_append, ← hStart] at hm
  rw [hWord]
  exact hm


end R2CoherenceV31MissionGate
