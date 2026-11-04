import Leader.Wu.Splice.FenceHandoffWholeRow


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceV10bDeleteBranch


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b B9SpliceV10bWholeRow


variable {n psi width kappa tau : Nat}


def BranchSafeV10b
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (write : R1AgentStateV6 psi kappa tau -> R1AgentStateV6 psi kappa tau ->
      R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) : Prop :=
  ∀ (C : R1ConfigV6 n psi kappa tau) (e : Fin n),
    SpliceSafeV7 hpsi ring C ->
    rowV10b hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
      write (C e) (C (ring.rightNeighbor e)) ->
    SpliceSafeV7 hpsi ring (stepV10b hpsi hwidth hle ring C e)


private instance instDecidablePreparedDanger
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring (projectV6 C) e) := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6
  dsimp only
  unfold isBarrier
  infer_instance


private instance instDecidableProtected
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (ProtectedSpliceEdgeV7 ring C e) := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3
    HostFenceShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only
  infer_instance


private instance instDecidableTicketShape
    (u : R1AgentStateV6 psi kappa tau) : Decidable (TicketShapeV7 u) := by
  unfold TicketShapeV7 HostFenceShapeV7 ReservedFrontHoldGuard
  infer_instance


private instance instDecidableProvenance
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) :
    Decidable (ProvenanceSafeV7 ring C) := by
  unfold ProvenanceSafeV7
  infer_instance


private instance instDecidableSpliceSafe
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) : Decidable (SpliceSafeV7 hpsi ring C) := by
  unfold SpliceSafeV7
  infer_instance


private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private def ring3 : DirectedRing 3 := ⟨hThree⟩


private def leftView : PeaceView 2 :=
  { leader := true, label := 1, shield := false, bullet := 0, signal_B := 0 }
private def rightView : PeaceView 2 :=
  { leader := false, label := 0, shield := false, bullet := 2, signal_B := 0 }
private def tailView : PeaceView 2 :=
  { leader := false, label := 1, shield := false, bullet := 0, signal_B := 0 }
private def leftRaw : AgentState 2 := PeaceView.toState leftView
private def rightRaw : AgentState 2 := PeaceView.toState rightView
private def tailRaw : AgentState 2 := PeaceView.toState tailView
private theorem leftDomain : leftRaw.inProtocolDomain 1 := by
  simp [leftRaw, leftView, PeaceView.toState, AgentState.inProtocolDomain]
private theorem rightDomain : rightRaw.inProtocolDomain 1 := by
  simp [rightRaw, rightView, PeaceView.toState, AgentState.inProtocolDomain]
private theorem tailDomain : tailRaw.inProtocolDomain 1 := by
  simp [tailRaw, tailView, PeaceView.toState, AgentState.inProtocolDomain]
private def topStall : Fin 2 := ⟨1, by decide⟩
private def pack (u : AgentState 2) (hu : u.inProtocolDomain 1) :
    ExpiringAgentState 2 1 1 :=
  ⟨⟨BoundedAgentState.ofDomain u hu, false⟩, topStall⟩
private def carrier (b : ExpiringAgentState 2 1 1) (r : SpliceRole) :
    R1AgentStateV4 2 1 1 :=
  { splice := { base := b, spliceRole := r }, repairPending := false }
private def start : R1ConfigV6 3 2 1 1 := fun i =>
  if i = 0 then liftAgentV6 (carrier (pack leftRaw leftDomain) .front)
  else if i = 1 then liftAgentV6 (carrier (pack rightRaw rightDomain) .front)
  else liftAgentV6 (carrier (pack tailRaw tailDomain) .none)
private def after : R1ConfigV6 3 2 1 1 :=
  stepV10b hTwo hOne hOneTwo ring3 start (0 : Fin 3)


theorem start_safe : SpliceSafeV7 hTwo ring3 start := by
  decide


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem selected_delete :
    rowV10b hTwo hOne hOneTwo
      (start 0) (start (ring3.rightNeighbor 0)) =
    deleteWriteV6 hTwo hOne hOneTwo
      (start 0) (start (ring3.rightNeighbor 0)) := by
  decide


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem delete_physical_census :
    (start 0).carrier.splice.base.core.core.leader = true ∧
    (start 0).carrier.splice.base.core.core.label = (1 : Fin 2) ∧
    (after 0).carrier.splice.base.core.core.leader = false ∧
    (after 0).carrier.splice.base.core.core.label = (0 : Fin 2) ∧
    (after 1).carrier.splice.base.core.core.leader = false ∧
    (after 1).carrier.splice.base.core.core.label = (0 : Fin 2) := by
  decide


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- Requested lemma 1 is false: DELETE creates a new unprotected danger. -/
theorem delete_dangerCoverage_fails :
    PreparedDangerAt hTwo ring3 (projectV6 after) (0 : Fin 3) ∧
    ¬ ProtectedSpliceEdgeV7 ring3 after (0 : Fin 3) := by
  decide


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- Controller sublemma 2 survives: DELETE clears both tickets. -/
theorem delete_ticketShape_holds : ∀ i, TicketShapeV7 (after i) := by
  decide


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- Controller sublemma 3 survives: the pending predecessor has its front backing. -/
theorem delete_pending_backing_holds :
    ∀ i, role (after i).carrier = .predecessorArmed ->
      (after i).carrier.repairPending = true ->
      ReservedFrontHoldGuard (after (ring3.rightNeighbor i)).carrier ∧
      (after (ring3.rightNeighbor i)).acquireTicket = false := by
  decide


theorem delete_after_not_safe : ¬ SpliceSafeV7 hTwo ring3 after := by
  intro hs
  exact delete_dangerCoverage_fails.2
    (hs.1 (0 : Fin 3) delete_dangerCoverage_fails.1)


theorem not_deleteBranch_v10b :
    ¬ BranchSafeV10b (kappa := 1) (tau := 1) hTwo hOne hOneTwo ring3
      (deleteWriteV6 (kappa := 1) (tau := 1) hTwo hOne hOneTwo) := by
  intro h
  exact delete_after_not_safe
    (h start (0 : Fin 3) start_safe selected_delete)


end B9SpliceV10bDeleteBranch


#print axioms B9SpliceV10bDeleteBranch.start_safe
#print axioms B9SpliceV10bDeleteBranch.selected_delete
#print axioms B9SpliceV10bDeleteBranch.delete_dangerCoverage_fails
#print axioms B9SpliceV10bDeleteBranch.delete_ticketShape_holds
#print axioms B9SpliceV10bDeleteBranch.delete_pending_backing_holds
#print axioms B9SpliceV10bDeleteBranch.not_deleteBranch_v10b
