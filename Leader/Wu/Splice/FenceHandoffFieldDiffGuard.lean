import Leader.Wu.Splice.FenceHandoffWindowNoGo
set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false
namespace B9SpliceV10dFieldDiff
open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open BirthSigMoveDisposalRepair BirthShortDoneTerminalBirthSources
  Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b
variable {n psi width kappa tau : Nat}
private theorem hOne : 0 < 1 := by decide
private theorem hLe : 1 <= 1 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩
private def ring4 : DirectedRing 4 := ⟨by decide⟩
private def peace1 : PeaceView 1 :=
  { leader := false, label := 0, shield := false, bullet := 0, signal_B := 0 }
private def rawL : AgentState 1 := PeaceView.toState peace1
private def rawR : AgentState 1 := { PeaceView.toState peace1 with write_state := .depart }
private theorem rawLDomain : rawL.inProtocolDomain 1 := by
  simp [rawL, peace1, PeaceView.toState, AgentState.inProtocolDomain]
private theorem rawRDomain : rawR.inProtocolDomain 1 := by
  simp [rawR, peace1, PeaceView.toState, AgentState.inProtocolDomain]
private def topStall : Fin 2 := ⟨1, by decide⟩
private def expL : ExpiringAgentState 1 1 1 :=
  ⟨⟨BoundedAgentState.ofDomain rawL rawLDomain, false⟩, topStall⟩
private def expR : ExpiringAgentState 1 1 1 :=
  ⟨⟨BoundedAgentState.ofDomain rawR rawRDomain, false⟩, topStall⟩
private def neutralCarrier (b : ExpiringAgentState 1 1 1) : R1AgentStateV4 1 1 1 :=
  { splice := { base := b, spliceRole := .none }, repairPending := false }
private def neutralL := liftAgentV6 (neutralCarrier expL)
private def neutralR := liftAgentV6 (neutralCarrier expR)
private def blocker : R1AgentStateV6 1 1 1 :=
  setControlV6 (liftAgentV6 (neutralCarrier expL)) .predecessorArmed false
private def fixture (m : Nat) : R1ConfigV6 m 1 1 1 := fun i =>
  if i.val = 0 then neutralL else if i.val = 1 then neutralR else blocker


def RequestedSame (u v : R1AgentStateV6 psi kappa tau) : Prop :=
  u.carrier.splice.base.core.core.state = v.carrier.splice.base.core.core.state ∧
  u.carrier.splice.base.core.core.path = v.carrier.splice.base.core.core.path ∧
  u.carrier.splice.base.core.core.path2 = v.carrier.splice.base.core.core.path2 ∧
  u.carrier.splice.base.core.core.path3 = v.carrier.splice.base.core.core.path3 ∧
  u.carrier.splice.base.core.core.path4 = v.carrier.splice.base.core.core.path4 ∧
  u.carrier.splice.base.core.core.path5 = v.carrier.splice.base.core.core.path5 ∧
  u.carrier.splice.base.core.core.p = v.carrier.splice.base.core.core.p ∧
  u.carrier.splice.base.core.core.p_carry = v.carrier.splice.base.core.core.p_carry ∧
  u.carrier.splice.base.core.path0Crossed = v.carrier.splice.base.core.path0Crossed ∧
  u.carrier.splice.base.core.core.count = v.carrier.splice.base.core.core.count ∧
  u.carrier.splice.base.core.core.label = v.carrier.splice.base.core.core.label ∧
  u.carrier.splice.base.core.core.reset = v.carrier.splice.base.core.core.reset ∧
  u.carrier.splice.base.core.core.reset_cmd = v.carrier.splice.base.core.core.reset_cmd ∧
  u.carrier.splice.base.core.core.carry = v.carrier.splice.base.core.core.carry ∧
  u.carrier.splice.base.core.core.echo = v.carrier.splice.base.core.core.echo ∧
  u.carrier.splice.base.core.core.leader = v.carrier.splice.base.core.core.leader ∧
  role u.carrier = role v.carrier ∧
  u.carrier.repairPending = v.carrier.repairPending ∧
  u.acquireTicket = v.acquireTicket


private def A0 := fixture 3
private def A1 := stepV10b hOne hOne hLe ring3 A0 0
private def W1 := rowV10b hOne hOne hLe (A1 0) (A1 1)
private def A2 := stepV10b hOne hOne hLe ring3 A1 0
private def W2 := rowV10b hOne hOne hLe (A2 0) (A2 1)


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem first_left_requested_same : RequestedSame (A1 0) W1.1 := by unfold RequestedSame; decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem first_right_requested_same : RequestedSame (A1 1) W1.2 := by unfold RequestedSame; decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem first_left_stall_change :
    (A1 0).carrier.splice.base.stall.val = 0 ∧ W1.1.carrier.splice.base.stall.val = 1 := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem first_right_stall_change :
    (A1 1).carrier.splice.base.stall.val = 0 ∧ W1.2.carrier.splice.base.stall.val = 1 := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem first_left_hField_change :
    (A1 0).carrier.splice.base.core.core.h_field = true ∧
      W1.1.carrier.splice.base.core.core.h_field = false := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem first_right_hField_change :
    (A1 1).carrier.splice.base.core.core.h_field = false ∧
      W1.2.carrier.splice.base.core.core.h_field = true := by decide


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem second_left_requested_same : RequestedSame (A2 0) W2.1 := by unfold RequestedSame; decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem second_right_requested_same : RequestedSame (A2 1) W2.2 := by unfold RequestedSame; decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem second_left_stall_change :
    (A2 0).carrier.splice.base.stall.val = 1 ∧ W2.1.carrier.splice.base.stall.val = 0 := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem second_right_stall_change :
    (A2 1).carrier.splice.base.stall.val = 1 ∧ W2.2.carrier.splice.base.stall.val = 0 := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem second_left_hField_change :
    (A2 0).carrier.splice.base.core.core.h_field = false ∧
      W2.1.carrier.splice.base.core.core.h_field = true := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem second_right_hField_change :
    (A2 1).carrier.splice.base.core.core.h_field = true ∧
      W2.2.carrier.splice.base.core.core.h_field = false := by decide


def FieldDiffGuardV10d
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  let q := rowV10b hpsi hwidth hle l r
  l.carrier.splice.base.stall.val = 0 ∧ r.carrier.splice.base.stall.val = 0 ∧
  RequestedSame l q.1 ∧ RequestedSame r q.2 ∧
  l.carrier.splice.base.core.core.h_field = q.1.carrier.splice.base.core.core.h_field ∧
  r.carrier.splice.base.core.core.h_field = q.2.carrier.splice.base.core.core.h_field ∧
  q.1.carrier.splice.base.stall = freshStall tau ∧
  q.2.carrier.splice.base.stall = freshStall tau
private instance instDecidableFieldDiffGuard
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (FieldDiffGuardV10d hpsi hwidth hle l r) := by
  unfold FieldDiffGuardV10d RequestedSame
  dsimp only
  infer_instance


def rowV10dField (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :=
  if FieldDiffGuardV10d hpsi hwidth hle l r then (l, r)
  else rowV10b hpsi hwidth hle l r


def stepV10dField (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :=
  let j := ring.rightNeighbor e
  if j = e then C else
    let q := rowV10dField hpsi hwidth hle (C e) (C j)
    fun i => if i = e then q.1 else if i = j then q.2 else C i


def Same3 (C D : R1ConfigV6 3 1 1 1) : Prop := C 0 = D 0 ∧ C 1 = D 1 ∧ C 2 = D 2
def Same4 (C D : R1ConfigV6 4 1 1 1) : Prop :=
  C 0 = D 0 ∧ C 1 = D 1 ∧ C 2 = D 2 ∧ C 3 = D 3
private def B0 := fixture 4
private def B1 := stepV10b hOne hOne hLe ring4 B0 0


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem guard_recheck :
    ¬ FieldDiffGuardV10d hOne hOne hLe (A1 0) (A1 1) ∧
    ¬ Same3 (stepV10dField hOne hOne hLe ring3 A1 0) A1 ∧
    ¬ FieldDiffGuardV10d hOne hOne hLe (B1 0) (B1 1) ∧
    ¬ Same4 (stepV10dField hOne hOne hLe ring4 B1 0) B1 := by
  exact ⟨by unfold FieldDiffGuardV10d RequestedSame; decide, by unfold Same3; decide,
    by unfold FieldDiffGuardV10d RequestedSame; decide, by unfold Same4; decide⟩


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem n4_failure_values :
    (B1 0).carrier.splice.base.stall.val = 0 ∧
    (B1 1).carrier.splice.base.stall.val = 0 ∧
    (B1 0).carrier.splice.base.core.core.h_field = true ∧
    (B1 1).carrier.splice.base.core.core.h_field = false ∧
    (let q := rowV10b hOne hOne hLe (B1 0) (B1 1)
     q.1.carrier.splice.base.stall.val = 1 ∧ q.2.carrier.splice.base.stall.val = 1 ∧
     q.1.carrier.splice.base.core.core.h_field = false ∧
     q.2.carrier.splice.base.core.core.h_field = true) := by decide


end B9SpliceV10dFieldDiff
#print axioms B9SpliceV10dFieldDiff.first_left_stall_change
#print axioms B9SpliceV10dFieldDiff.first_left_hField_change
#print axioms B9SpliceV10dFieldDiff.second_left_hField_change
#print axioms B9SpliceV10dFieldDiff.guard_recheck
