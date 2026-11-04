import Leader.Wu.Splice.FenceHandoffDeleteCounterexample
import Leader.Wu.Birth.ShortDoneTerminalDeletionPpsiFrame

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV10bLeaderLabelInvariant

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open Q11593SpliceControllerDesign
open BirthShortDoneTerminalDeletionPpsiFrame
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b

variable {n psi width kappa tau : Nat}

def LeadersLabelReadyV10b (hpsi : 0 < psi)
    (C : R1ConfigV6 n psi kappa tau) : Prop :=
  forall i, LeaderLabelReady hpsi (C i).carrier.splice.base

def DeleteSafeWithLeaderLabels
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : Prop :=
  forall (C : R1ConfigV6 n psi kappa tau) (e : Fin n),
    SpliceSafeV7 hpsi ring C -> LeadersLabelReadyV10b hpsi C ->
    rowV10b hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
      deleteWriteV6 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) ->
    SpliceSafeV7 hpsi ring (stepV10b hpsi hwidth hle ring C e)

private instance instDanger (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring (projectV6 C) e) := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6
  dsimp only
  unfold isBarrier
  infer_instance

private instance instProtected (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (ProtectedSpliceEdgeV7 ring C e) := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3
    HostFenceShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only
  infer_instance

private instance instTicket (u : R1AgentStateV6 psi kappa tau) :
    Decidable (TicketShapeV7 u) := by
  unfold TicketShapeV7 HostFenceShapeV7 ReservedFrontHoldGuard
  infer_instance

private instance instProv (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) : Decidable (ProvenanceSafeV7 ring C) := by
  unfold ProvenanceSafeV7
  infer_instance

private instance instSafe (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) : Decidable (SpliceSafeV7 hpsi ring C) := by
  unfold SpliceSafeV7
  infer_instance

private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private def ring3 : DirectedRing 3 := ⟨hThree⟩

private def leftRaw : AgentState 2 :=
  { counterexampleLeftRaw with label := 0 }
private def rightRaw : AgentState 2 :=
  { counterexampleRightRaw with bullet := 2 }
private def tailRaw : AgentState 2 :=
  { counterexampleLeftRaw with leader := false, label := 1 }

private theorem leftDomain : leftRaw.inProtocolDomain 0 := by
  simp [leftRaw, counterexampleLeftRaw, AgentState.inProtocolDomain]
private theorem rightDomain : rightRaw.inProtocolDomain 0 := by
  simp [rightRaw, counterexampleRightRaw, AgentState.inProtocolDomain]
private theorem tailDomain : tailRaw.inProtocolDomain 0 := by
  simp [tailRaw, counterexampleLeftRaw, AgentState.inProtocolDomain]

private def pack (u : AgentState 2) (hu : u.inProtocolDomain 0) :
    ExpiringAgentState 2 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain u hu, false⟩, 0⟩

private def carrier (b : ExpiringAgentState 2 0 0) (r : SpliceRole) :
    R1AgentStateV4 2 0 0 :=
  { splice := { base := b, spliceRole := r }, repairPending := false }

private def start : R1ConfigV6 3 2 0 0 := fun i =>
  if i = 0 then liftAgentV6 (carrier (pack leftRaw leftDomain) .front)
  else if i = 1 then liftAgentV6 (carrier (pack rightRaw rightDomain) .front)
  else liftAgentV6 (carrier (pack tailRaw tailDomain) .none)

private def after : R1ConfigV6 3 2 0 0 :=
  stepV10b hTwo hOne hOneTwo ring3 start (0 : Fin 3)

theorem start_safe : SpliceSafeV7 hTwo ring3 start := by decide

theorem start_leaders_ready : LeadersLabelReadyV10b hTwo start := by
  intro i hi
  revert hi
  revert i
  decide

theorem selected_delete :
    rowV10b hTwo hOne hOneTwo (start 0) (start (ring3.rightNeighbor 0)) =
      deleteWriteV6 hTwo hOne hOneTwo
        (start 0) (start (ring3.rightNeighbor 0)) := by
  decide

theorem after_left_follower_zero :
    (after 0).carrier.splice.base.core.core.leader = false /\
      (after 0).carrier.splice.base.core.core.label = (0 : Fin 2) := by
  decide

theorem after_right_follower_zero :
    (after 1).carrier.splice.base.core.core.leader = false /\
      (after 1).carrier.splice.base.core.core.label = (0 : Fin 2) := by
  decide

theorem after_leaders_ready : LeadersLabelReadyV10b hTwo after := by
  intro i hi
  revert hi
  revert i
  decide

theorem after_served_danger :
    PreparedDangerAt hTwo ring3 (projectV6 after) (0 : Fin 3) := by decide

theorem after_served_not_protected :
    ¬ ProtectedSpliceEdgeV7 ring3 after (0 : Fin 3) := by decide

theorem after_not_safe : ¬ SpliceSafeV7 hTwo ring3 after := by
  intro hs
  exact after_served_not_protected (hs.1 0 after_served_danger)

theorem delete_with_global_leader_labels_still_fails :
    ¬ DeleteSafeWithLeaderLabels (kappa := 0) (tau := 0)
      hTwo hOne hOneTwo ring3 := by
  intro h
  exact after_not_safe
    (h start 0 start_safe start_leaders_ready selected_delete)

end B9SpliceV10bLeaderLabelInvariant

#print axioms B9SpliceV10bLeaderLabelInvariant.start_safe
#print axioms B9SpliceV10bLeaderLabelInvariant.start_leaders_ready
#print axioms B9SpliceV10bLeaderLabelInvariant.selected_delete
#print axioms B9SpliceV10bLeaderLabelInvariant.after_leaders_ready
#print axioms B9SpliceV10bLeaderLabelInvariant.after_served_danger
#print axioms B9SpliceV10bLeaderLabelInvariant.after_served_not_protected
#print axioms B9SpliceV10bLeaderLabelInvariant.delete_with_global_leader_labels_still_fails
