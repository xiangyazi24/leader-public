import Leader.Wu.Entrance.AdmissionLanding
import Leader.Wu.Entrance.AdmissionCyclicRuler
import Leader.Wu.Coherence.FreshCoverSoundness
import Leader.Wu.Entrance.AdmittedCyclicRuler

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace CFinalJ2EdgeResidual

open CFinalJ2Landing CFinalJ2Edge CFinalJ2Edge2 CFinalJ2Ruler
open BarrierDischargeTruth2
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C

variable {n psi : Nat}

/-- The no-garbage projection of J2's edge residual. -/
def J2C1AdmissionNoGarbageResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
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
      ¬ FinalGarbage hpsi (D a) (D (ring.rightNeighbor a))

/-- Current admission already gives the full cyclic ruler, not merely the
root-or-successor `ElectionGeometryV31` view. -/
theorem cyclicRulerEntrance_closed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hS : ConcretePortHostSelectorResidual
      (κ := psi) (τ := 16 * psi) hpsi h2) :
    ConcreteB7PassiveCyclicRulerEntranceObligation hpsi h2 ring := by
  intro C hA hL
  apply (finalCyclicRuler_iff_view hpsi ring C).2
  have h := admittedCyclicRuler_of_noGarbage
    (kappa := psi) (tau := 16 * psi) hpsi h2 ring hS C hA hL
  simpa [CyclicRulerV31, AdmittedCyclicRulerV31] using h

/-- Hence the geometric-hole sub-residual is completely closed. -/
theorem j2C1AdmissionHoleResidual_closed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hS : ConcretePortHostSelectorResidual
      (κ := psi) (τ := 16 * psi) hpsi h2) :
    J2C1AdmissionHoleResidual hpsi h2 ring :=
  j2Hole_of_cyclicRulerEntrance hpsi h2 ring
    (cyclicRulerEntrance_closed hpsi h2 ring hS)

/-- Neutrality removes scrub garbage; the transported cyclic ruler removes
`FinalHole`.  The two C1 hypotheses are accepted but not needed. -/
theorem j2C1AdmissionNoGarbageResidual_closed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hS : ConcretePortHostSelectorResidual
      (κ := psi) (τ := 16 * psi) hpsi h2) :
    J2C1AdmissionNoGarbageResidual hpsi h2 ring := by
  intro C e hA hL
  dsimp only
  intro hDL hGeom hPrefix hNeutral a
  have hh := (j2C1AdmissionHoleResidual_closed hpsi h2 ring hS)
    C e hA hL hDL hGeom hPrefix hNeutral a
  exact no_finalGarbage_of_neutral_noHole hpsi
    (hNeutral a) (hNeutral (ring.rightNeighbor a)) hh

/-- Edge2 already closes the concrete HOST-selector conjunct. -/
theorem j2C1AdmissionHostActionResidual_closed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    J2C1AdmissionHostActionResidual hpsi h2 ring :=
  CFinalJ2Edge2.j2C1AdmissionHostActionResidual_closed hpsi h2 ring



/-- Exact remainder after no-garbage and HOST selection are discharged. -/
def J2C1AdmissionProposalNoWriteResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
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
      R2Coherence.ProposalNoWrite hpsi (by decide : 0 < 2) h2
        (D a).phys (D (ring.rightNeighbor a)).phys

/-- The older global B4 post obligation is stronger than the exact J2-shaped
remainder. -/
theorem proposalNoWriteResidual_of_post
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hPost : ConcreteB7PassiveProposalNoWritePostObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring) :
    J2C1AdmissionProposalNoWriteResidual hpsi h2 ring := by
  intro C e hA hL
  dsimp only
  intro hDL _hGeom _hPrefix _hNeutral a
  exact hPost C e hA hL hDL a

/-- With the preceding two closed conjuncts, this is all that J2 needs. -/
theorem j2C1AdmissionEdgeResidual_of_proposalNoWrite
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hS : ConcretePortHostSelectorResidual
      (κ := psi) (τ := 16 * psi) hpsi h2)
    (hNoWrite : J2C1AdmissionProposalNoWriteResidual hpsi h2 ring) :
    J2C1AdmissionEdgeResidual hpsi h2 ring := by
  intro C e hA hL
  dsimp only
  intro hDL hGeom hPrefix hNeutral a
  have hg := (j2C1AdmissionNoGarbageResidual_closed hpsi h2 ring hS)
    C e hA hL hDL hGeom hPrefix hNeutral a
  have ha := (j2C1AdmissionHostActionResidual_closed hpsi h2 ring)
    C e hA hL hDL hGeom hPrefix hNeutral a
  have hn := hNoWrite C e hA hL hDL hGeom hPrefix hNeutral a
  exact ⟨hg, ha, hn⟩

/-- Conversely, J2's full edge residual contains exactly this final conjunct. -/
theorem proposalNoWrite_of_j2C1AdmissionEdgeResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hEdge : J2C1AdmissionEdgeResidual hpsi h2 ring) :
    J2C1AdmissionProposalNoWriteResidual hpsi h2 ring := by
  intro C e hA hL
  dsimp only
  intro hDL hGeom hPrefix hNeutral a
  exact (hEdge C e hA hL hDL hGeom hPrefix hNeutral a).2.2

/-- Architectural endpoint: the full edge residual is equivalent to the
single second-step R2 no-write residual. -/
theorem j2C1AdmissionEdgeResidual_iff_proposalNoWrite
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hS : ConcretePortHostSelectorResidual
      (κ := psi) (τ := 16 * psi) hpsi h2) :
    J2C1AdmissionEdgeResidual hpsi h2 ring ↔
      J2C1AdmissionProposalNoWriteResidual hpsi h2 ring := by
  constructor
  · exact proposalNoWrite_of_j2C1AdmissionEdgeResidual hpsi h2 ring
  · exact j2C1AdmissionEdgeResidual_of_proposalNoWrite hpsi h2 ring hS

/-- Compatibility with the old B4 name: proving that global post obligation
immediately closes J2. -/
theorem j2C1AdmissionEdgeResidual_of_proposalNoWritePost
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hS : ConcretePortHostSelectorResidual
      (κ := psi) (τ := 16 * psi) hpsi h2)
    (hPost : ConcreteB7PassiveProposalNoWritePostObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring) :
    J2C1AdmissionEdgeResidual hpsi h2 ring :=
  j2C1AdmissionEdgeResidual_of_proposalNoWrite hpsi h2 ring hS
    (proposalNoWriteResidual_of_post hpsi h2 ring hPost)

end CFinalJ2EdgeResidual
