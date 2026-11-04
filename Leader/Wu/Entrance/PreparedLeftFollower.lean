import Leader.Wu.Entrance.WriterPremiseLeftFollower
import Leader.Wu.Birth.CapToFirstBirth


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B6MicroLeftFollower


open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthSigMoveDisposalRepair


variable {n psi kappa tau : Nat}


/-- Disposal preparation preserves the physical leader bit. -/
theorem prepared_leader_eq
    (hpsi : 0 < psi) (u : ExpiringAgentState psi kappa tau) :
    (prepareExpiringDisposal hpsi u).core.erase.core.leader =
      u.core.core.leader := by
  have h := congrArg AgentState.leader
    (K2BirthDispatcher.prepareExpiring_signal hpsi u)
  change (prepareExpiringDisposal hpsi u).core.erase.core.leader =
    u.core.core.leader at h
  exact h


/-- Before the first birth, every served edge has a prepared left follower. -/
theorem missingLeftFollower_of_leaderless
    (hpsi : 0 < psi)
    (C : BirthPhaseCapToFirstBirth.FC n psi kappa tau)
    (e : Fin n)
    (hzero : BirthShortDoneTerminalFirstHit.Leaderless C) :
    B6WriterPremiseStage2.MissingLeftFollowerConjunct
      ((prepareExpiringDisposal hpsi (C e)).core.erase) := by
  unfold B6WriterPremiseStage2.MissingLeftFollowerConjunct
  exact (prepared_leader_eq hpsi (C e)).trans (hzero e)


/-- In particular, the fact is available from the B6 carrier itself. -/
theorem b6Carrier_missingLeftFollower
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : BirthPhaseCapToFirstBirth.FC n psi kappa tau)
    (hC : BirthPhaseCapToFirstBirth.B6Carrier hpsi h2 ring C)
    (e : Fin n) :
    B6WriterPremiseStage2.MissingLeftFollowerConjunct
      ((prepareExpiringDisposal hpsi (C e)).core.erase) := by
  exact missingLeftFollower_of_leaderless hpsi C e hC.1


end B6MicroLeftFollower


#print axioms B6MicroLeftFollower.prepared_leader_eq
#print axioms B6MicroLeftFollower.missingLeftFollower_of_leaderless
#print axioms B6MicroLeftFollower.b6Carrier_missingLeftFollower
