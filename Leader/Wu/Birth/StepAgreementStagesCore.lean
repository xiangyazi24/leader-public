import Leader.Wu.Birth.ResetStepAgreementCounterexample


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace BirthB1ResetStepAgreementStages


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepPreCheckResetRepair
open BirthWaitPassive BirthGenerationControlRepair BirthGenerationDone
  BirthArrivalCaptureRepair BirthSingleUseReleaseRepair
  BirthShortWait BirthShortWaitTerminalEntryRepair
  BirthShortDoneTerminalEntryCut BirthSigMoveDisposalRepair
open BirthB1ResetFreeControlled BirthB1ResetCorridorBridge
  BirthB1ResetStepAgreement


variable {n psi kappa tau : Nat}


structure StepView (psi : Nat) where
  leader : Bool
  reset : Bool
  echo : Bool
  deriving DecidableEq


def stepView (u : AgentState psi) : StepView psi :=
  ⟨u.leader, u.reset_cmd, u.echo⟩


def stepPair (q : AgentState psi × AgentState psi) :=
  (stepView q.1, stepView q.2)


def authStepPair
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :=
  stepPair (q.1.core, q.2.core)


/-- The strengthened entrance makes the B1 disposal preparation a literal
identity on both served endpoints. -/
theorem preparation_stage
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthB1ResetCorridorBridge.FC n psi kappa tau) (e : Fin n)
    (hp : NoPendingTerminalDisposalOnEdge hpsi ring C e) :
    prepareExpiringDisposal hpsi (C e) = C e ∧
      prepareExpiringDisposal hpsi (C (ring.rightNeighbor e)) =
        C (ring.rightNeighbor e) := by
  unfold NoPendingTerminalDisposalOnEdge
    BirthB1ResetFreeControlled.rawAt at hp
  constructor
  · unfold prepareExpiringDisposal
    rw [prepareBoundedDisposal_eq_of_clear hpsi (C e).core hp.1]
  · unfold prepareExpiringDisposal
    rw [prepareBoundedDisposal_eq_of_clear hpsi
      (C (ring.rightNeighbor e)).core hp.2]


/-- After the identity preparation, the established no-active-deletion
entrance opens exactly the deletion-priority gate used by the wall row. -/
theorem deletion_gate_stage
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthB1ResetCorridorBridge.FC n psi kappa tau) (e : Fin n)
    (hp : NoPendingTerminalDisposalOnEdge hpsi ring C e)
    (hno : B1NoActiveDeletion C) :
    WallPriorityOpen
      (prepareExpiringDisposal hpsi (C e))
      (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e))) := by
  rcases preparation_stage hpsi ring C e hp with ⟨hl, hr⟩
  rw [hl, hr]
  exact noActiveDeletion_opens_edge ring C hno e


/-- The shared pre-CHECK deletion reset changes none of the observed fields. -/
theorem precheck_reset_stage (l r : AuthorizedAgentState psi) :
    authStepPair (preCheckResetWall l r) = authStepPair (l, r) := by
  unfold authStepPair stepPair stepView preCheckResetWall
    clearAuthorizedComparison clearComparisonSignal
  dsimp only
  repeat (first | rfl | split <;> try dsimp only)


end BirthB1ResetStepAgreementStages


#print axioms BirthB1ResetStepAgreementStages.preparation_stage
#print axioms BirthB1ResetStepAgreementStages.deletion_gate_stage
#print axioms BirthB1ResetStepAgreementStages.precheck_reset_stage
