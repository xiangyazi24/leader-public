import Leader.Wu.Birth.PPrimeProbeRearm
import Leader.Wu.Comparison.HistoryDoneMove



set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace Q11581DoneJoinCensus


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLComparisonHistory
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalEntryCut


private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private theorem hFour : 0 < 4 := by decide


def ring4 : DirectedRing 4 := ⟨hFour⟩


def p0 : Fin 4 := 0
def p1 : Fin 4 := 1
def p2 : Fin 4 := 2
def p3 : Fin 4 := 3


private theorem fin4_cases (i : Fin 4) :
    i = p0 ∨ i = p1 ∨ i = p2 ∨ i = p3 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  simpa [p0, p1, p2, p3] using hi


/-! ## Staged physical input -/


def remoteLeaderRaw : AgentState 2 :=
  { PPLLCounterexample.state2 1 with leader := true }


def readyRaw : AgentState 2 :=
  { PPLLCounterexample.state2 0 with state := .CHECK_ready }


def genLeftRaw : AgentState 2 :=
  { PPLLCounterexample.state2 0 with wait := false }


def genRightRaw : AgentState 2 :=
  PPLLCounterexample.state2 1


private theorem remoteLeaderRaw_domain :
    remoteLeaderRaw.inProtocolDomain 10 := by
  simp [remoteLeaderRaw, PPLLCounterexample.state2,
    AgentState.inProtocolDomain]


private theorem readyRaw_domain :
    readyRaw.inProtocolDomain 10 := by
  simp [readyRaw, PPLLCounterexample.state2,
    AgentState.inProtocolDomain]


private theorem genLeftRaw_domain :
    genLeftRaw.inProtocolDomain 10 := by
  simp [genLeftRaw, PPLLCounterexample.state2,
    AgentState.inProtocolDomain]


private theorem genRightRaw_domain :
    genRightRaw.inProtocolDomain 10 := by
  simp [genRightRaw, PPLLCounterexample.state2,
    AgentState.inProtocolDomain]


def remoteLeaderEndpoint : ExpiringAgentState 2 10 1 :=
  ⟨⟨BoundedAgentState.ofDomain remoteLeaderRaw remoteLeaderRaw_domain,
      false⟩, 1⟩


def readyEndpoint : ExpiringAgentState 2 10 1 :=
  ⟨⟨BoundedAgentState.ofDomain readyRaw readyRaw_domain, false⟩, 1⟩


def genLeftEndpoint : ExpiringAgentState 2 10 1 :=
  ⟨⟨BoundedAgentState.ofDomain genLeftRaw genLeftRaw_domain, false⟩, 1⟩


def genRightEndpoint : ExpiringAgentState 2 10 1 :=
  ⟨⟨BoundedAgentState.ofDomain genRightRaw genRightRaw_domain, false⟩, 1⟩


def initialConfig : Fin 4 -> ExpiringAgentState 2 10 1 := fun i =>
  if i = p0 then remoteLeaderEndpoint
  else if i = p1 then readyEndpoint
  else if i = p2 then genLeftEndpoint
  else genRightEndpoint


/-! ## Four-field histories -/


def idleHistory : LocalComparisonHistory 4 where
  state := .absent
  path := .absent
  path2 := .absent
  pCarry := .absent


def readyHistory : LocalComparisonHistory 4 where
  state := .trusted p1
  path := .absent
  path2 := .absent
  pCarry := .absent


def source2History : LocalComparisonHistory 4 where
  state := .trusted p2
  path := .trusted p2
  path2 := .absent
  pCarry := .absent


def initialHistory : Fin 4 -> LocalComparisonHistory 4 := fun i =>
  if i = p1 then readyHistory else idleHistory


/-- Every initial physical endpoint satisfies the full four-field trust
relation.  This is deliberately stronger than a pair-local premise. -/
theorem initial_full_history_trusted :
    forall i : Fin 4,
      FullLocalHistoryTrusted
        (initialConfig i).core.core.erase (initialHistory i) := by
  intro i
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    simp [initialConfig, initialHistory, p0, p1, p2, p3,
      remoteLeaderEndpoint, readyEndpoint, genLeftEndpoint,
      genRightEndpoint, remoteLeaderRaw, readyRaw, genLeftRaw,
      genRightRaw, BoundedAgentState.erase_ofDomain,
      FullLocalHistoryTrusted, AuditLocalHistoryTrusted,
      PCarryHistoryTrusted, MarkMatches, idleHistory, readyHistory,
      PPLLCounterexample.state2]


/-! ## First actual current-consumer row: edge 2 -> 3 -/


def afterGen : Fin 4 -> ExpiringAgentState 2 10 1 :=
  BirthShortDoneTerminalConsumer.step hTwo hTwo hTwoLe
    ring4 initialConfig p2


private theorem ring4_right_p2 :
    ring4.rightNeighbor p2 = p3 := by
  decide

private theorem initialConfig_p2 :
    initialConfig p2 = genLeftEndpoint := by
  decide

private theorem initialConfig_p3 :
    initialConfig p3 = genRightEndpoint := by
  decide

private theorem afterGen_p0_unchanged :
    afterGen p0 = initialConfig p0 := by
  simpa only [afterGen] using
    (BirthShortDoneTerminalConsumer.step_other
      hTwo hTwo hTwoLe ring4 initialConfig p2 p0
      (by decide)
      (by
        rw [ring4_right_p2]
        decide))

private theorem afterGen_p1_unchanged :
    afterGen p1 = initialConfig p1 := by
  simpa only [afterGen] using
    (BirthShortDoneTerminalConsumer.step_other
      hTwo hTwo hTwoLe ring4 initialConfig p2 p1
      (by decide)
      (by
        rw [ring4_right_p2]
        decide))

private def firstRow :
    ExpiringAgentState 2 10 1 × ExpiringAgentState 2 10 1 :=
  BirthShortDoneTerminalHost.row
    hTwo hTwo hTwoLe genLeftEndpoint genRightEndpoint

private theorem afterGen_p2_eq_firstRow :
    afterGen p2 = firstRow.1 := by
  unfold afterGen
  simp only [BirthShortDoneTerminalConsumer.step,
    PopulationProtocol.step, BirthShortDoneTerminalConsumer.protocol,
    updatePair, if_true]
  rw [ring4_right_p2, initialConfig_p2, initialConfig_p3]
  rfl

private theorem afterGen_p0_leader :
    (afterGen p0).core.core.leader = true := by
  rw [afterGen_p0_unchanged]
  decide

private theorem afterGen_p1_state :
    (afterGen p1).core.core.state = .CHECK_ready := by
  rw [afterGen_p1_unchanged]
  decide

private theorem afterGen_p1_label :
    (afterGen p1).core.core.label = (0 : Fin 2) := by
  rw [afterGen_p1_unchanged]
  decide

set_option maxRecDepth 20000 in
private theorem firstRow_left_state :
    firstRow.1.core.core.state = .depart := by
  decide

set_option maxRecDepth 20000 in
private theorem firstRow_left_path :
    firstRow.1.core.core.path = .some 0 0 := by
  decide

set_option maxRecDepth 20000 in
private theorem firstRow_left_path2 :
    firstRow.1.core.core.path2 = none := by
  decide

set_option maxRecDepth 20000 in
private theorem firstRow_left_pcarry :
    firstRow.1.core.core.p_carry = false := by
  decide

private theorem afterGen_p2_state :
    (afterGen p2).core.core.state = .depart := by
  rw [afterGen_p2_eq_firstRow]
  exact firstRow_left_state

private theorem afterGen_p2_path :
    (afterGen p2).core.core.path = .some 0 0 := by
  rw [afterGen_p2_eq_firstRow]
  exact firstRow_left_path

private theorem afterGen_p2_path2 :
    (afterGen p2).core.core.path2 = none := by
  rw [afterGen_p2_eq_firstRow]
  exact firstRow_left_path2

private theorem afterGen_p2_pcarry :
    (afterGen p2).core.core.p_carry = false := by
  rw [afterGen_p2_eq_firstRow]
  exact firstRow_left_pcarry

theorem first_current_row_boundary_fields :
    (afterGen p0).core.core.leader = true ∧
    (afterGen p1).core.core.state = .CHECK_ready ∧
    (afterGen p1).core.core.label = (0 : Fin 2) ∧
    (afterGen p2).core.core.state = .depart ∧
    (afterGen p2).core.core.path = .some 0 0 ∧
    (afterGen p2).core.core.path2 = none ∧
    (afterGen p2).core.core.p_carry = false := by
  exact ⟨afterGen_p0_leader, afterGen_p1_state, afterGen_p1_label,
    afterGen_p2_state, afterGen_p2_path, afterGen_p2_path2,
    afterGen_p2_pcarry⟩


set_option maxRecDepth 20000 in
theorem first_current_row_boundary_trusted :
    FullLocalHistoryTrusted
        (afterGen p1).core.core.erase readyHistory ∧
      FullLocalHistoryTrusted
        (afterGen p2).core.core.erase source2History := by
  constructor
  · have h := initial_full_history_trusted p1
    rw [afterGen_p1_unchanged]
    simpa [initialHistory] using h
  · have hpathErase :
        (afterGen p2).core.core.erase.path = .some 0 0 := by
      change
        (match (afterGen p2).core.core.path with
          | .bot => PathInfo.bot
          | .some label bit => PathInfo.some label.val bit.val) =
            PathInfo.some 0 0
      rw [afterGen_p2_path]
      rfl
    unfold FullLocalHistoryTrusted AuditLocalHistoryTrusted
      PCarryHistoryTrusted
    rw [hpathErase]
    simp [MarkMatches, source2History, BoundedAgentState.erase,
      afterGen_p2_state, afterGen_p2_path2, afterGen_p2_pcarry]


private def secondPreparedL : AuthorizedAgentState 2 :=
  normalizeDeletion
    (prepareExpiringDisposal hTwo (afterGen p1)).core.erase


private def secondPreparedR : AuthorizedAgentState 2 :=
  normalizeDeletion
    (prepareExpiringDisposal hTwo (afterGen p2)).core.erase


private def secondBeforeDone :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  generationBeforeMoveEntryWidth
    hTwo hTwo hTwoLe 10 secondPreparedL secondPreparedR


private def secondMarkedL : MarkedAgentState 4 2 :=
  ⟨secondBeforeDone.1.core, readyHistory⟩


private def secondMarkedR : MarkedAgentState 4 2 :=
  ⟨secondBeforeDone.2.core, source2History⟩


set_option maxRecDepth 20000 in
private theorem secondMarkedL_state :
    secondMarkedL.concrete.state = .CHECK_ready := by
  decide

set_option maxRecDepth 20000 in
private theorem secondMarkedL_label_lt :
    secondMarkedL.concrete.label.val < 2 - 1 := by
  decide

set_option maxRecDepth 20000 in
private theorem secondMarkedR_state :
    secondMarkedR.concrete.state = .depart := by
  decide

private theorem secondMarkedL_history_state :
    secondMarkedL.history.state = .trusted p1 := by
  rfl

private theorem secondMarkedR_history_state :
    secondMarkedR.history.state = .trusted p2 := by
  rfl

set_option maxRecDepth 20000 in
private theorem secondMarkedL_path :
    secondMarkedL.concrete.path = .bot := by
  decide

set_option maxRecDepth 20000 in
private theorem secondMarkedL_path2 :
    secondMarkedL.concrete.path2 = none := by
  decide

set_option maxRecDepth 20000 in
private theorem secondMarkedL_pcarry :
    secondMarkedL.concrete.p_carry = false := by
  decide

set_option maxRecDepth 20000 in
private theorem secondMarkedR_path_active :
    secondMarkedR.concrete.path ≠ .bot := by
  decide

set_option maxRecDepth 20000 in
private theorem secondMarkedR_path2 :
    secondMarkedR.concrete.path2 = none := by
  decide

set_option maxRecDepth 20000 in
private theorem secondMarkedR_pcarry :
    secondMarkedR.concrete.p_carry = false := by
  decide

theorem second_done_cut_fields :
    secondMarkedL.concrete.state = .CHECK_ready ∧
      secondMarkedL.concrete.label.val < 2 - 1 ∧
      secondMarkedR.concrete.state = .depart ∧
      secondMarkedL.history.state = .trusted p1 ∧
      secondMarkedR.history.state = .trusted p2 := by
  exact ⟨secondMarkedL_state, secondMarkedL_label_lt,
    secondMarkedR_state, secondMarkedL_history_state,
    secondMarkedR_history_state⟩


theorem second_done_cut_full_history_trusted :
    FullLocalHistoryTrusted
        secondMarkedL.concrete secondMarkedL.history ∧
      FullLocalHistoryTrusted
        secondMarkedR.concrete secondMarkedR.history := by
  change
    FullLocalHistoryTrusted secondMarkedL.concrete readyHistory ∧
      FullLocalHistoryTrusted secondMarkedR.concrete source2History
  constructor
  · simp [FullLocalHistoryTrusted, AuditLocalHistoryTrusted,
      PCarryHistoryTrusted, MarkMatches, readyHistory,
      secondMarkedL_state, secondMarkedL_path,
      secondMarkedL_path2, secondMarkedL_pcarry]
  · simp [FullLocalHistoryTrusted, AuditLocalHistoryTrusted,
      PCarryHistoryTrusted, MarkMatches, source2History,
      secondMarkedR_state, secondMarkedR_path_active,
      secondMarkedR_path2, secondMarkedR_pcarry]


private def secondDonePreclear :
    MarkedAgentState 4 2 × MarkedAgentState 4 2 :=
  markedSigMoveLeaderPreclear hTwo secondMarkedL secondMarkedR

private def secondDoneMoved :
    MarkedAgentState 4 2 × MarkedAgentState 4 2 :=
  markedDoneTransfers secondDonePreclear.1 secondDonePreclear.2

private def secondDoneWall :
    MarkedAgentState 4 2 × MarkedAgentState 4 2 :=
  PPLLWallSweepHistory.markedComparisonLeaderWall
    secondDoneMoved.1 secondDoneMoved.2

private def secondDoneL6 : MarkedAgentState 4 2 :=
  markedSingleUseApplyControl hTwo secondDoneWall.1

private def secondDoneR6 : MarkedAgentState 4 2 :=
  markedSingleUseApplyControl hTwo secondDoneWall.2

private theorem second_currentDoneMoveCompatible_iff :
    CurrentDoneMoveCompatible hTwo secondMarkedL secondMarkedR ↔
      SigMoveDepartCompatible hTwo secondDoneL6 secondDoneR6 := by
  rfl

set_option maxRecDepth 20000 in
private theorem secondDoneL6_state :
    secondDoneL6.concrete.state = .CHECK_ready := by
  decide

set_option maxRecDepth 20000 in
private theorem secondDoneL6_label_lt :
    secondDoneL6.concrete.label.val < 2 - 1 := by
  decide

set_option maxRecDepth 20000 in
private theorem secondDoneR6_state :
    secondDoneR6.concrete.state = .depart := by
  decide

set_option maxRecDepth 20000 in
private theorem secondDoneL6_history_state :
    secondDoneL6.history.state = .trusted p1 := by
  decide

set_option maxRecDepth 20000 in
private theorem secondDoneR6_history_state :
    secondDoneR6.history.state = .trusted p2 := by
  decide

theorem second_done_cut_not_compatible :
    ¬ CurrentDoneMoveCompatible hTwo secondMarkedL secondMarkedR := by
  intro hcurrent
  have hcompat :
      SigMoveDepartCompatible hTwo secondDoneL6 secondDoneR6 :=
    second_currentDoneMoveCompatible_iff.mp hcurrent
  obtain ⟨source, hleft, hright⟩ :=
    hcompat ⟨secondDoneR6_state, secondDoneL6_label_lt,
      secondDoneL6_state⟩
  rw [secondDoneL6_history_state] at hleft
  rw [secondDoneR6_history_state] at hright
  have hp1 : p1 = source := by
    injection hleft
  have hp2 : p2 = source := by
    injection hright
  exact (by decide : p1 ≠ p2) (hp1.trans hp2.symm)


def DoneDepartureSourceAgrees {n psi : Nat} (hpsi : psi > 0)
    (l r : MarkedAgentState n psi) : Prop :=
  let p := markedSigMoveLeaderPreclear hpsi l r
  let moved := markedDoneTransfers p.1 p.2
  let wall := PPLLWallSweepHistory.markedComparisonLeaderWall
    moved.1 moved.2
  let l6 := markedSingleUseApplyControl hpsi wall.1
  let r6 := markedSingleUseApplyControl hpsi wall.2
  (r6.concrete.state = .depart ∧
      l6.concrete.label.val < psi - 1 ∧
      l6.concrete.state = .CHECK_ready) ->
    ∃ source,
      l6.history.state = .trusted source ∧
      r6.history.state = .trusted source


/-- This is not a stronger hidden invariant: it is exactly the already exposed
current-DONE compatibility contract. -/
theorem doneDepartureSourceAgrees_iff_currentDoneMoveCompatible
    {n psi : Nat} (hpsi : psi > 0)
    (l r : MarkedAgentState n psi) :
    DoneDepartureSourceAgrees hpsi l r ↔
      CurrentDoneMoveCompatible hpsi l r := by
  rfl


/-- Immediate consumer theorem: local fieldwise trust plus same-source
agreement at the actual backward-depart join is exactly enough for the
existing current DONE lift. -/
theorem done_preserves_audit_history_of_departure_source_agrees
    {n psi : Nat} (hpsi : psi > 0)
    (l r : MarkedAgentState n psi)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history)
    (hjoin : DoneDepartureSourceAgrees hpsi l r) :
    let q := markedDoneCaptureSigMove hpsi l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  apply markedDoneCaptureSigMove_preserves_auditLocalHistoryTrusted
  · exact hl.1
  · exact hr.1
  · exact
      (doneDepartureSourceAgrees_iff_currentDoneMoveCompatible
        hpsi l r).mp hjoin


#print axioms Q11581DoneJoinCensus.initial_full_history_trusted
#print axioms Q11581DoneJoinCensus.first_current_row_boundary_fields
#print axioms Q11581DoneJoinCensus.first_current_row_boundary_trusted
#print axioms Q11581DoneJoinCensus.second_done_cut_fields
#print axioms Q11581DoneJoinCensus.second_done_cut_full_history_trusted
#print axioms Q11581DoneJoinCensus.second_done_cut_not_compatible
#print axioms Q11581DoneJoinCensus.doneDepartureSourceAgrees_iff_currentDoneMoveCompatible
#print axioms Q11581DoneJoinCensus.done_preserves_audit_history_of_departure_source_agrees


end Q11581DoneJoinCensus
