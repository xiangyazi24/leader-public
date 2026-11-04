import Leader.Wu.Entrance.ElectionGeometryGlobalCensus


set_option autoImplicit false
set_option Elab.async false


namespace BarrierDischargeCensus


open R2CoherenceV31 R2CoherenceV31Closure
open BirthLeaderlessBirthMassRenewal
open R2CoherenceV31FinalSimulation
open R2CoherenceV31FinalSimulation5
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open ElectionGeometryGlobalCensus


variable {n psi kappa tau : Nat}


/-- The real local missing lemma.  If this is true, C1 geometry is already
latent in the existing concrete admission predicate. -/
def ConcreteAdmissionBadEdgeForcesRelabelV31
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : FinalCandidateR2C.Config n psi kappa tau) (e : Fin n),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C →
    passiveEdgeOKV3
      (liftFinalV31 C e)
      (liftFinalV31 C (ring.rightNeighbor e)) = false →
    ¬ R2Coherence.ProposalNoWrite hpsi (by decide : 0 < 2) h2
      (C e).phys (C (ring.rightNeighbor e)).phys


theorem c1Geometry_of_badEdgeForcesRelabel
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hLocal : ConcreteAdmissionBadEdgeForcesRelabelV31
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    C1FinalV31AdmittedElectionGeometryResidual
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  intro C hA hL _hOpen e
  cases hgood : passiveEdgeOKV3
      (liftFinalV31 C e)
      (liftFinalV31 C (ring.rightNeighbor e)) with
  | true => rfl
  | false =>
      have hNo := hA.2.2.2 e |>.2.2
      exact (hLocal C e hA hL hgood hNo).elim





open ElectionGeometryGlobalCensus


variable {n psi kappa tau : Nat}


/-- Exact class on which the V3.1 mission is allowed to start. -/
def ConcreteB7AdmittedGeometryV31
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : FinalCandidateR2C.Config n psi kappa tau) : Prop :=
  ConcreteB7AdmittedPassive hpsi h2 ring C ∧
    R2CoherenceV31Closure.ElectionGeometryV31 ring (liftFinalV31 C)


/-- Physical prefix target: either birth already succeeded or the configuration
has reached the actual V3.1 entrance class. -/
def BarrierDischargeOrBirthV31
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : FinalCandidateR2C.Config n psi kappa tau) : Prop :=
  HasLeader C ∨ ConcreteB7AdmittedGeometryV31 hpsi h2 ring C


/-- Mass leaf to add only if the direct admission⇒geometry lemma is refuted. -/
def C0BarrierDischargeOrBirthMassV31
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (L Q : Nat) : Prop :=
  UniformEscapeMass
    (stepConcrete (κ := kappa) (τ := tau) hpsi h2 ring)
    (fun C => FinalLeaderless C ∧
      ¬ ConcreteB7AdmittedGeometryV31 hpsi h2 ring C)
    L Q


/-- Restricted C1 geometry is projection, not an assumption. -/
theorem geometry_of_restrictedAdmission
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FinalCandidateR2C.Config n psi kappa tau)
    (h : ConcreteB7AdmittedGeometryV31 hpsi h2 ring C) :
    R2CoherenceV31Closure.ElectionGeometryV31 ring (liftFinalV31 C) :=
  h.2



end BarrierDischargeCensus
