import Leader.Wu.Birth.StepAgreementStagesCore
import Leader.Wu.Birth.StepAgreementWaitStage
import Leader.Wu.Birth.StepAgreementGenStage
import Leader.Wu.Birth.StepAgreementSuppressStage
import Leader.Wu.Birth.StepAgreementDoneStage


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


/-- Complete prepared-entrance certificate at the three-field abstraction used
by the B1 step-agreement decomposition.  The only unproved component is supplied
as the explicit `done_agreement` field by the capstone theorem below. -/
structure B1PreparedEntranceStepAgreement
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : BirthB1ResetCorridorBridge.FC n psi kappa tau) (e : Fin n) : Prop where
  left_follower :
    (BirthB1ResetFreeControlled.rawAt C e).leader = false
  left_reset :
    (BirthB1ResetFreeControlled.rawAt C e).reset_cmd = true
  right_follower :
    (BirthB1ResetFreeControlled.rawAt C (ring.rightNeighbor e)).leader = false
  prepared_left :
    prepareExpiringDisposal hpsi (C e) = C e
  prepared_right :
    prepareExpiringDisposal hpsi (C (ring.rightNeighbor e)) =
      C (ring.rightNeighbor e)
  priority_open :
    WallPriorityOpen
      (prepareExpiringDisposal hpsi (C e))
      (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e)))
  wait_agreement :
    forall l r : AgentState psi,
      stepPair (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r) =
        stepPair (waitSaturated hpsi kappa l r)
  gen_agreement :
    forall l r : AgentState psi,
      stepPair (genCleanAfterWait hpsi l r) =
        stepPair (genSigSaturatedAfterWait hpsi l r)
  done_agreement :
    forall l r : AgentState psi,
      stepPair (doneCaptureSigMove hpsi l r) =
        stepPair (sigMoveLeaderWall hpsi l r)
  precheck_reset_agreement :
    forall l r : AuthorizedAgentState psi,
      authStepPair (preCheckResetWall l r) = authStepPair (l, r)
  suppress_agreement :
    forall l r : AgentState psi,
      stepPair
          (suppressSigResetKillWidth hpsi (by decide : 0 < 2) h2 l r) =
        stepPair (suppressSigResetKill hpsi l r)


/-- Capstone for the strengthened B1 entrance.  All seven stages are now proved,
so this is unconditional: `done_agreement` is discharged from `done_stage` in
`Leader.Wu.Birth.StepAgreementDoneStage` rather than taken as a hypothesis. -/
theorem b1_prepared_entrance_step_agreement
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : BirthB1ResetCorridorBridge.FC n psi kappa tau) (e : Fin n)
    (hp : NoPendingTerminalDisposalOnEdge hpsi ring C e)
    (hno : B1NoActiveDeletion C)
    (hlFollower :
      (BirthB1ResetFreeControlled.rawAt C e).leader = false)
    (hlReset :
      (BirthB1ResetFreeControlled.rawAt C e).reset_cmd = true)
    (hrFollower :
      (BirthB1ResetFreeControlled.rawAt C (ring.rightNeighbor e)).leader = false) :
    B1PreparedEntranceStepAgreement hpsi h2 ring C e := by
  have hprep := preparation_stage hpsi ring C e hp
  exact {
    left_follower := hlFollower
    left_reset := hlReset
    right_follower := hrFollower
    prepared_left := hprep.1
    prepared_right := hprep.2
    priority_open := deletion_gate_stage hpsi ring C e hp hno
    wait_agreement := fun l r => shortened_wait_stage hpsi h2 kappa l r
    gen_agreement := fun l r => gen_stage hpsi l r
    done_agreement := fun l r => done_stage hpsi l r
    precheck_reset_agreement := fun l r => precheck_reset_stage l r
    suppress_agreement := fun l r => suppress_stage hpsi h2 l r
  }


end BirthB1ResetStepAgreementStages


#print axioms BirthB1ResetStepAgreementStages.b1_prepared_entrance_step_agreement
