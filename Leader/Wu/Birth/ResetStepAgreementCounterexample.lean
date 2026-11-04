import Leader.Wu.Birth.ResetCorridorBridge
import Leader.Wu.WallSweep.PreCheckResetContractsNormalized


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace BirthB1ResetStepAgreement


open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol
open PPLLWallSweepFiniteCleanup PPLLWallSweepClockwiseAttempt
open PPLLWallSweepPreCheckResetRepair
open BirthSigMoveDisposalRepair
open BirthB1ResetFreeControlled BirthB1ResetCorridorBridge


private theorem hpsi2 : 0 < 2 := by decide
private theorem h2 : 2 <= 2 := by decide
private def ring2 : DirectedRing 2 := ⟨by decide⟩
private def edge0 : Fin 2 := 0


private theorem right0 :
    ring2.rightNeighbor edge0 = (1 : Fin 2) := by decide


private def peace2 (j : Fin 2) : PeaceView 2 :=
  { leader := false
    label := j
    shield := false
    bullet := 0
    signal_B := 0 }


private def rawBase (j : Fin 2) : AgentState 2 :=
  PeaceView.toState (peace2 j)


/-- Initially deletion-inactive, but already pending at the terminal. -/
private def sourceRaw : AgentState 2 :=
  { rawBase (1 : Fin 2) with
      reset_cmd := true
      path := .some 1 0
      path2 := some ⟨0, 0, 0, 4⟩ }


private def receiverRaw : AgentState 2 :=
  rawBase (0 : Fin 2)


private theorem sourceRaw_domain : sourceRaw.inProtocolDomain 0 := by
  simp [sourceRaw, rawBase, peace2, PeaceView.toState,
    AgentState.inProtocolDomain]


private theorem receiverRaw_domain : receiverRaw.inProtocolDomain 0 := by
  simp [receiverRaw, rawBase, peace2, PeaceView.toState,
    AgentState.inProtocolDomain]


private def source : ExpiringAgentState 2 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain sourceRaw sourceRaw_domain, false⟩, 0⟩


private def receiver : ExpiringAgentState 2 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain receiverRaw receiverRaw_domain, false⟩, 0⟩


private def badC : BirthB1ResetCorridorBridge.FC 2 2 0 0 := fun i =>
  if i = 0 then source else receiver


private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  omega


private theorem bad_no_active : B1NoActiveDeletion badC := by
  intro i
  rcases fin2_cases i with rfl | rfl <;> decide


private theorem bad_left_follower :
    (BirthB1ResetFreeControlled.rawAt badC edge0).leader = false := by
  decide


private theorem bad_left_reset :
    (BirthB1ResetFreeControlled.rawAt badC edge0).reset_cmd = true := by
  decide


private theorem bad_right_follower :
    (BirthB1ResetFreeControlled.rawAt badC
      (ring2.rightNeighbor edge0)).leader = false := by
  rw [right0]
  decide


/-- This is the first divergent stage.  `NoActiveDeletion` is true before
preparation, but the pending terminal action-4 carrier becomes active. -/
theorem prepareExpiringDisposal_is_first_break :
    deletionActive source.core.erase = false ∧
      pendingTerminalDisposal hpsi2 sourceRaw = true ∧
      deletionActive
        (prepareExpiringDisposal hpsi2 source).core.erase = true := by
  decide


private theorem bad_wall_open : WallPriorityOpen source receiver := by
  have h := noActiveDeletion_opens_edge ring2 badC bad_no_active edge0
  rw [right0] at h
  simpa [badC, edge0] using h


/-- The wall transition is genuinely on its reset-moving ordinary branch. -/
theorem wall_step_consumes_left_reset :
    (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi2 0 0 source receiver).1.core.erase.core.reset_cmd = false := by
  rcases
      PPLLWallSweepPreCheckResetContracts.wallSweepResetProbePreCheckResetLeaderSinkPathStall_exists_reset_follower_normalization
        hpsi2 source receiver bad_wall_open
        (by decide) (by decide) (by decide)
      with ⟨out, hout, hnorm⟩
  rw [hout] at hnorm
  exact hnorm.control.left_reset_false


private def badD : BirthB1ResetCorridorBridge.FC 2 2 0 0 :=
  BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 ring2 badC edge0


/-- B1 has already taken the prepared-deletion branch, so Algorithm 14 never
gets the chance to move/consume this reset. -/
theorem currentStep2_keeps_left_reset :
    (BirthB1ResetFreeControlled.rawAt badD edge0).reset_cmd = true := by
  decide


/-- In fact the prepared deletion itself also survives the B1 row. -/
theorem currentStep2_keeps_active_deletion :
    deletionActive (badD edge0).core.erase = true := by
  decide


theorem currentStep2_not_resetAwareFollowerFrame :
    ¬ ResetAwareFollowerGlobalStepFrame hpsi2 ring2 badC badD edge0 := by
  intro hframe
  have hfalse := hframe.normalized.control.left_reset_false
  change
    (BirthB1ResetFreeControlled.rawAt badD edge0).reset_cmd = false
      at hfalse
  rw [currentStep2_keeps_left_reset] at hfalse
  cases hfalse


/-- The exact seam is therefore false as currently stated. -/
theorem not_B1ResetFollowerStepAgreement :
    ¬ B1ResetFollowerStepAgreement
      (n := 2) (psi := 2) (kappa := 0) (tau := 0)
      hpsi2 h2 ring2 := by
  intro hagree
  have hframe := hagree badC edge0 bad_no_active
    bad_left_follower bad_left_reset bad_right_follower
  change ResetAwareFollowerGlobalStepFrame
    hpsi2 ring2 badC badD edge0 at hframe
  exact currentStep2_not_resetAwareFollowerFrame hframe


variable {n psi kappa tau : Nat}

/-- Exact strengthening needed merely to get past the first B1 stage. -/
def NoPendingTerminalDisposalOnEdge
    (hpsi : 0 < psi)
    (ring : DirectedRing n)
    (C : BirthB1ResetCorridorBridge.FC n psi kappa tau)
    (e : Fin n) : Prop :=
  pendingTerminalDisposal hpsi
      (BirthB1ResetFreeControlled.rawAt C e) = false ∧
    pendingTerminalDisposal hpsi
      (BirthB1ResetFreeControlled.rawAt C (ring.rightNeighbor e)) = false


end BirthB1ResetStepAgreement


#print axioms BirthB1ResetStepAgreement.prepareExpiringDisposal_is_first_break
#print axioms BirthB1ResetStepAgreement.wall_step_consumes_left_reset
#print axioms BirthB1ResetStepAgreement.currentStep2_keeps_left_reset
#print axioms BirthB1ResetStepAgreement.currentStep2_keeps_active_deletion
#print axioms BirthB1ResetStepAgreement.currentStep2_not_resetAwareFollowerFrame
#print axioms BirthB1ResetStepAgreement.not_B1ResetFollowerStepAgreement
