import Leader.Wu.Splice.ZeroRefreshTable


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceWaitFieldNecessity


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open BirthSigMoveDisposalRepair BirthShortDoneTerminalBirthSources
  BirthShortWait Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b B9SpliceV10cLiveness


private theorem hOne : 0 < 1 := by decide
private theorem hLe : 1 <= 1 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩
private def ring4 : DirectedRing 4 := ⟨by decide⟩


private def peace1 : PeaceView 1 :=
  { leader := false, label := 0, shield := false, bullet := 0, signal_B := 0 }
private def raw0 : AgentState 1 := PeaceView.toState peace1
private def raw1 : AgentState 1 := { raw0 with h_field := true }
private def carry0 : AgentState 1 := { raw0 with carry := true }


/-- Prepare uses the label-zero h bit as the low WAIT bit: 0 -> 1 stops,
while 1 -> 0 launches the ripple carry. -/
theorem prepare_reads_left_h_field :
    let q0 := waitSaturatedPrepare hOne raw0 raw0
    let q1 := waitSaturatedPrepare hOne raw1 raw0
    q0.1.h_field = true ∧ q0.1.carry = false ∧
      q1.1.h_field = false ∧ q1.1.carry = true := by
  decide


/-- Carry then reads the responder h bit.  A zero bit is set and stops the
ripple; a one terminal bit is cleared and increments the saturated count. -/
theorem carry_reads_right_h_field :
    let q0 := waitWidthCarry hOne hLe 1 carry0 raw0
    let q1 := waitWidthCarry hOne hLe 1 carry0 raw1
    q0.2.h_field = true ∧ q0.2.count = 0 ∧
      q1.2.h_field = false ∧ q1.2.count = 1 := by
  decide


private def rawR : AgentState 1 := { raw0 with write_state := .depart }
private theorem raw0Domain : raw0.inProtocolDomain 1 := by
  simp [raw0, peace1, PeaceView.toState, AgentState.inProtocolDomain]
private theorem rawRDomain : rawR.inProtocolDomain 1 := by
  simp [rawR, raw0, peace1, PeaceView.toState, AgentState.inProtocolDomain]
private def topStall : Fin 2 := ⟨1, by decide⟩
private def expL : ExpiringAgentState 1 1 1 :=
  ⟨⟨BoundedAgentState.ofDomain raw0 raw0Domain, false⟩, topStall⟩
private def expR : ExpiringAgentState 1 1 1 :=
  ⟨⟨BoundedAgentState.ofDomain rawR rawRDomain, false⟩, topStall⟩
private def neutralCarrier (b : ExpiringAgentState 1 1 1) :
    R1AgentStateV4 1 1 1 :=
  { splice := { base := b, spliceRole := .none }, repairPending := false }
private def neutralL := liftAgentV6 (neutralCarrier expL)
private def neutralR := liftAgentV6 (neutralCarrier expR)
private def blocker : R1AgentStateV6 1 1 1 :=
  setControlV6 (liftAgentV6 (neutralCarrier expL)) .predecessorArmed false
private def fixture (m : Nat) : R1ConfigV6 m 1 1 1 := fun i =>
  if i.val = 0 then neutralL else if i.val = 1 then neutralR else blocker


private def A0 := fixture 3
private def A1 := stepV10c hOne hOne hLe ring3 A0 0
private def A2 := stepV10c hOne hOne hLe ring3 A1 0
private def A3 := stepV10c hOne hOne hLe ring3 A2 0
private def B0 := fixture 4
private def B1 := stepV10c hOne hOne hLe ring4 B0 0
private def B2 := stepV10c hOne hOne hLe ring4 B1 0
private def B3 := stepV10c hOne hOne hLe ring4 B2 0


private def rawV6 (u : R1AgentStateV6 1 1 1) : AgentState 1 :=
  u.carrier.splice.base.core.core.erase


private def n3PreparePhase1 : AgentState 1 × AgentState 1 :=
  waitSaturatedPrepare hOne (rawV6 (A1 0)) (rawV6 (A1 1))
private def n3PreparePhase2 : AgentState 1 × AgentState 1 :=
  waitSaturatedPrepare hOne (rawV6 (A2 0)) (rawV6 (A2 1))


def Same3 (C D : R1ConfigV6 3 1 1 1) : Prop :=
  C 0 = D 0 ∧ C 1 = D 1 ∧ C 2 = D 2


def Same4 (C D : R1ConfigV6 4 1 1 1) : Prop :=
  C 0 = D 0 ∧ C 1 = D 1 ∧ C 2 = D 2 ∧ C 3 = D 3


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- The actual V10c edge-0 orbit alternates the two WAIT phases on n=3. -/
theorem n3_wait_phase_cycle :
    (rawV6 (A1 0)).h_field = true ∧ (rawV6 (A1 1)).h_field = false ∧
    (rawV6 (A2 0)).h_field = false ∧ (rawV6 (A2 1)).h_field = true ∧
    (rawV6 (A3 0)).h_field = true ∧ (rawV6 (A3 1)).h_field = false ∧
    Same3 A3 A1 := by
  unfold Same3 rawV6
  decide


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- The same phase alternation is present on the n=4 lift. -/
theorem n4_wait_phase_cycle :
    (rawV6 (B1 0)).h_field = true ∧ (rawV6 (B1 1)).h_field = false ∧
    (rawV6 (B2 0)).h_field = false ∧ (rawV6 (B2 1)).h_field = true ∧
    (rawV6 (B3 0)).h_field = true ∧ (rawV6 (B3 1)).h_field = false ∧
    Same4 B3 B1 := by
  unfold Same4 rawV6
  decide


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- The next Prepare call distinguishes the two n=3 phases by carry launch. -/
theorem n3_next_prepare_distinguishes_phases :
    let p1 := waitSaturatedPrepare hOne (rawV6 (A1 0)) (rawV6 (A1 1))
    let p2 := waitSaturatedPrepare hOne (rawV6 (A2 0)) (rawV6 (A2 1))
    p1.1.carry = true ∧ p2.1.carry = false := by
  change (n3PreparePhase1).1.carry = true ∧
    (n3PreparePhase2).1.carry = false
  decide


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- Replacing one of two repeated services by a stutter changes the state
seen after the second scheduled service, on both finite fixtures. -/
theorem stutter_substitution_is_wrong :
    ¬ Same3 A3 A2 ∧ ¬ Same4 B3 B2 := by
  unfold Same3 Same4
  decide


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- Controller-only V6 potential is blind to this genuine WAIT phase step. -/
theorem controller_potential_is_flat_across_wait_phase :
    controllerPotentialV6 A2 = controllerPotentialV6 A1 ∧
      controllerPotentialV6 B2 = controllerPotentialV6 B1 := by
  decide


#print axioms prepare_reads_left_h_field
#print axioms carry_reads_right_h_field
#print axioms n3_wait_phase_cycle
#print axioms n4_wait_phase_cycle
#print axioms n3_next_prepare_distinguishes_phases
#print axioms stutter_substitution_is_wrong
#print axioms controller_potential_is_flat_across_wait_phase


end B9SpliceWaitFieldNecessity
