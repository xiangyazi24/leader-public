import Leader.Wu.Entrance.JoinObligations
import Leader.Wu.Entrance.PassiveWriterPost
import Leader.Wu.Entrance.PassiveOuterNeutralFrame
import Leader.Wu.Entrance.PassiveInputNeutralProjection

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace CFinalJ2Landing

open BirthLeaderlessBirthMassRenewal
open CFinalAssembly
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C

variable {n psi : Nat}

/-- What C1 + the B4 passive post interfaces still do not prove.
The C1 observations and outer-neutral post are explicit premises so this is
exactly the remaining edge-admission bridge, not a stronger hidden assumption. -/
def J2C1AdmissionEdgeResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n psi psi (16 * psi)) (e : Fin n),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C →
    let D := stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e
    FinalLeaderless D →
    R2CoherenceV31Closure.ElectionGeometryV31 ring
      (R2CoherenceV31MissionGate.finalV31View D) →
    R2CoherenceV31.CoherentPrefixesV3 ring
      (R2CoherenceV31MissionGate.finalV31View D) →
    (∀ i : Fin n, NeutralController (D i)) →
    ∀ a : Fin n,
      ¬ FinalGarbage hpsi (D a) (D (ring.rightNeighbor a)) ∧
      (concretePortLocal (κ := psi) (τ := 16 * psi) hpsi h2).action
          (D a) (D (ring.rightNeighbor a)) = .host ∧
      R2Coherence.ProposalNoWrite hpsi (by decide : 0 < 2) h2
        (D a).phys (D (ring.rightNeighbor a)).phys


/-- Strongest source-supported J2 landing: the J1 equality is wiring; C1
supplies the one-step V3.1 observations; B4 supplies writer/all-open/neutrality;
only `J2C1AdmissionEdgeResidual` remains semantic. -/
theorem j2C1AdmissionLanding_of_b4_posts_and_edge_residual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hWriter : ConcreteB7PassiveWriterPostObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (hSelector : ConcretePortHostSelectorResidual
      (κ := psi) (τ := 16 * psi) hpsi h2)
    (hFaith : ConcretePortControllerFaithfulObligation
      (κ := psi) (τ := 16 * psi) hpsi h2)
    (hEdge : J2C1AdmissionEdgeResidual hpsi h2 ring) :
    J2C1AdmissionLanding hpsi h2 ring := by
  intro _hJ1 hC1
  intro C e hA hL
  let D := stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e
  by_cases hLead : HasLeader D
  · left
    simpa [D] using hLead
  · right
    have hDL : FinalLeaderless D :=
      (finalLeaderless_iff_not_hasLeader D).2 hLead
    have hAlive :
        AliveAlong
          (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
          FinalLeaderless C [e] := by
      change FinalLeaderless C ∧ FinalLeaderless D
      exact ⟨hL, hDL⟩
    have hCoh := hC1 C [e] hA hL hA.2.2.1 hAlive
    have hGeom :
        R2CoherenceV31Closure.ElectionGeometryV31 ring
          (R2CoherenceV31MissionGate.finalV31View D) := by
      simpa [D] using hCoh.1
    have hPrefix :
        R2CoherenceV31.CoherentPrefixesV3 ring
          (R2CoherenceV31MissionGate.finalV31View D) := by
      simpa [D] using hCoh.2
    have hInput : ConcreteB7PassiveInputOuterNeutralObligation
        (κ := psi) (τ := 16 * psi) hpsi h2 ring :=
      concreteB7PassiveInputOuterNeutral_of_selector
        hpsi h2 ring hSelector
    have hOuter : ConcreteB7PassiveOuterNeutralPostObligation
        (κ := psi) (τ := 16 * psi) hpsi h2 ring :=
      concreteB7PassiveOuterNeutralPost_of_input_outer_neutral
        hpsi h2 ring hInput hFaith
    have hNeutral : ∀ i : Fin n, NeutralController (D i) := by
      intro i
      unfold NeutralController
      simpa [D] using (hOuter C e hA hL hDL i)
    have hWriterD : FinalWriterPassive D := by
      simpa [D] using (hWriter C e hA hL hDL)
    have hNoProducerD : FinalNoProducer D :=
      finalNoProducer_of_finalWriterPassive D hWriterD
    have hAllOpenD : FinalAllOpen D := by
      simpa [D] using
        (concreteB7PassiveAllOpenPost
          (κ := psi) (τ := 16 * psi) hpsi h2 ring C e hA)
    have hEdges :=
      hEdge C e hA hL hDL hGeom hPrefix hNeutral
    change ConcreteB7AdmittedPassive hpsi h2 ring D
    exact ⟨hNoProducerD, hWriterD, hAllOpenD, hEdges⟩

end CFinalJ2Landing
