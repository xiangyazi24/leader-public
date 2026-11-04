import Leader.Wu.Splice.ZeroRefreshTable


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SplicePotentialEscape


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
  B9SpliceControllerR1TableV10b B9SpliceV10cLiveness


variable {n psi kappa tau : Nat}


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


def physical (u : R1AgentStateV6 psi kappa tau) : AgentState psi :=
  u.carrier.splice.base.core.erase.core
def hBit (u : R1AgentStateV6 psi kappa tau) : Nat :=
  match (physical u).h_field with | false => 0 | true => 1
def remainingStall (u : R1AgentStateV6 psi kappa tau) : Nat :=
  tau - u.carrier.splice.base.stall.val
def edgeHCount (C : R1ConfigV6 n psi kappa tau) (e j : Fin n) : Nat :=
  hBit (C e) + hBit (C j)
def edgeRemaining (C : R1ConfigV6 n psi kappa tau) (e j : Fin n) : Nat :=
  remainingStall (C e) + remainingStall (C j)
def escapePotentialAt (C : R1ConfigV6 n psi kappa tau) (e : Fin n) : Nat :=
  2 * controllerPotentialV6 C + hBit (C e)


theorem escapePotentialAt_le (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    escapePotentialAt C e <= 16 * n + 1 := by
  have hc := controllerPotentialV6_le_eight_mul C
  cases hh : (physical (C e)).h_field <;>
    simp [escapePotentialAt, hBit, hh] <;> omega


private def C30 := fixture 3
private def C31 := stepV10c hOne hOne hLe ring3 C30 0
private def C32 := stepV10c hOne hOne hLe ring3 C31 0
private def C33 := stepV10c hOne hOne hLe ring3 C32 0
private def D40 := fixture 4
private def D41 := stepV10c hOne hOne hLe ring4 D40 0
private def D42 := stepV10c hOne hOne hLe ring4 D41 0


def Same4 (C D : R1ConfigV6 4 1 1 1) : Prop :=
  C 0 = D 0 ∧ C 1 = D 1 ∧ C 2 = D 2 ∧ C 3 = D 3


set_option maxHeartbeats 20000000 in
set_option maxRecDepth 65536 in
theorem n3_left_physical_exact :
    physical (C32 0) = { physical (C31 0) with h_field := false } := by decide
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 65536 in
theorem n3_right_physical_exact :
    physical (C32 1) = { physical (C31 1) with h_field := true } := by decide
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 65536 in
theorem n3_stall_exact :
    (C31 0).carrier.splice.base.stall.val = 0 ∧
    (C31 1).carrier.splice.base.stall.val = 0 ∧
    (C32 0).carrier.splice.base.stall.val = 1 ∧
    (C32 1).carrier.splice.base.stall.val = 1 := by decide
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 65536 in
theorem n3_nonstall_frame :
    (C32 0).carrier.splice.base.core.path0Crossed =
      (C31 0).carrier.splice.base.core.path0Crossed ∧
    (C32 1).carrier.splice.base.core.path0Crossed =
      (C31 1).carrier.splice.base.core.path0Crossed ∧
    role (C32 0).carrier = role (C31 0).carrier ∧
    role (C32 1).carrier = role (C31 1).carrier ∧
    (C32 0).carrier.repairPending = (C31 0).carrier.repairPending ∧
    (C32 1).carrier.repairPending = (C31 1).carrier.repairPending ∧
    (C32 0).acquireTicket = (C31 0).acquireTicket ∧
    (C32 1).acquireTicket = (C31 1).acquireTicket ∧ C32 2 = C31 2 := by decide
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 65536 in
theorem n3_return_exact :
    physical (C33 0) = { physical (C32 0) with h_field := true } ∧
    physical (C33 1) = { physical (C32 1) with h_field := false } ∧
    (C33 0).carrier.splice.base.stall.val = 0 ∧
    (C33 1).carrier.splice.base.stall.val = 0 := by decide


set_option maxHeartbeats 20000000 in
set_option maxRecDepth 65536 in
theorem n3_underlying_v10b :
    Same3 (stepV10b hOne hOne hLe ring3 C31 0) C32 ∧
    Same3 (stepV10b hOne hOne hLe ring3 C32 0) C33 := by unfold Same3; decide
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 65536 in
theorem n3_measure_census :
    edgeHCount C31 0 1 = 1 ∧ edgeHCount C32 0 1 = 1 ∧
    edgeHCount C33 0 1 = 1 ∧ edgeRemaining C31 0 1 = 2 ∧
    edgeRemaining C32 0 1 = 0 ∧ edgeRemaining C33 0 1 = 2 ∧
    controllerPotentialV6 C32 = controllerPotentialV6 C31 ∧
    controllerPotentialV6 C33 = controllerPotentialV6 C32 ∧
    escapePotentialAt C31 0 = escapePotentialAt C32 0 + 1 ∧
    escapePotentialAt C33 0 = escapePotentialAt C32 0 + 1 := by decide
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 65536 in
theorem n3_cycle : Same3 C33 C31 := by unfold Same3; decide


set_option maxHeartbeats 20000000 in
set_option maxRecDepth 65536 in
theorem n4_measure_census :
    edgeHCount D41 0 1 = 1 ∧ edgeHCount D42 0 1 = 1 ∧
    edgeRemaining D41 0 1 = 2 ∧ edgeRemaining D42 0 1 = 0 ∧
    controllerPotentialV6 D42 = controllerPotentialV6 D41 ∧
    escapePotentialAt D41 0 = escapePotentialAt D42 0 + 1 := by decide


private theorem c33_eq_c31 : C33 = C31 := by
  have h := n3_cycle
  funext i
  rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 by omega) with h0 | h1 | h2
  · have hi : i = (0 : Fin 3) := Fin.ext h0
    subst i
    exact h.1
  · have hi : i = (1 : Fin 3) := Fin.ext h1
    subst i
    exact h.2.1
  · have hi : i = (2 : Fin 3) := Fin.ext h2
    subst i
    exact h.2.2


theorem state_potential_escape_impossible
    (P : R1ConfigV6 3 1 1 1 -> Nat) :
    ¬ (P C32 < P C31 ∧ P C33 <= P C32) := by
  intro h
  rw [c33_eq_c31] at h
  omega


end B9SplicePotentialEscape


#print axioms B9SplicePotentialEscape.n3_left_physical_exact
#print axioms B9SplicePotentialEscape.n3_stall_exact
#print axioms B9SplicePotentialEscape.n3_measure_census
#print axioms B9SplicePotentialEscape.n4_measure_census
#print axioms B9SplicePotentialEscape.state_potential_escape_impossible
