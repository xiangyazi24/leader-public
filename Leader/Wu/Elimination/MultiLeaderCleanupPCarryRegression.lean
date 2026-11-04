import Leader.Wu.Elimination.MultiLeaderCleanupResetFreeBridge
import Leader.Wu.Elimination.MultiLeaderCleanupSegmentPlan

namespace PPLLCompleteMultiLeaderCleanup
namespace PhysicalBridge

open PPLL PPLLRepair PPLLResearchFormulation PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWriteIncrementGate PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepPreCheckResetRepair
  PPLLPpsiLeaderCreationRepair

set_option autoImplicit false

/-! ## Raw DISAPPEAR carry creation -/

private def pCarryQuietState {psi : Nat}
    (label : Fin psi) : AgentState psi where
  leader := false
  probe := false
  phase := false
  bit := false
  wait := false
  state := .none
  path := .bot
  reset := false
  carry := false
  count := 0
  label := label
  h_field := false
  path2 := none
  path3 := none
  path4 := none
  path5 := none
  p := false
  p_carry := false
  reset_cmd := false
  echo := false
  signal_B := ⟨0, by omega⟩
  bullet := ⟨0, by omega⟩
  shield := false
  write_state := .none
  write := .none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

private theorem pCarry_h2 : 2 > 0 := by omega
private theorem pCarry_h3 : 3 > 0 := by omega

private def pCarryTossLeft2 : AgentState 2 :=
  { pCarryQuietState (⟨0, by omega⟩ : Fin 2) with
    state := .toss
    p := true }

private def pCarryTossRight2 : AgentState 2 :=
  { pCarryQuietState (⟨1, by omega⟩ : Fin 2) with
    p := true }

private def pCarryTossLeft3 : AgentState 3 :=
  { pCarryQuietState (⟨0, by omega⟩ : Fin 3) with
    state := .toss
    p := true }

private def pCarryTossRight3 : AgentState 3 :=
  { pCarryQuietState (⟨1, by omega⟩ : Fin 3) with
    p := true }

/-- At `psi = 2`, the stable label-one responder is terminal, so DISAPPEAR
consumes the carry into `eliminate_signal`. -/
theorem disappear_psi2_terminal_consumes_pCarry :
    let q := disappear pCarry_h2 pCarryTossLeft2 pCarryTossRight2
    q.1.p_carry = false ∧
      q.2.p_carry = false ∧
      q.2.state = .eliminate_signal := by
  decide

/-- At `psi = 3`, DISAPPEAR can create a responder carry although both input
carry bits are false. -/
theorem disappear_psi3_creates_responder_pCarry :
    let q := disappear pCarry_h3 pCarryTossLeft3 pCarryTossRight3
    pCarryTossLeft3.p_carry = false ∧
      pCarryTossRight3.p_carry = false ∧
      q.1.p = false ∧
      q.1.p_carry = false ∧
      q.2.p = false ∧
      q.2.p_carry = true := by
  decide

/-! ## Complete ready-shaped edge preserving an admitted carry -/

private def pCarryLeftRaw : AgentState 2 :=
  { pCarryQuietState (⟨0, by omega⟩ : Fin 2) with
    wait := true }

private def pCarryRightRaw : AgentState 2 :=
  { pCarryQuietState (⟨1, by omega⟩ : Fin 2) with
    wait := true
    p_carry := true }

private def pCarryLeft : AuthorizedAgentState 2 :=
  ⟨pCarryLeftRaw, false⟩

private def pCarryRight : AuthorizedAgentState 2 :=
  ⟨pCarryRightRaw, false⟩

/-- These are exactly the asymmetric idle hypotheses in the current bridge. -/
theorem pCarry_entry_idle_projection :
    CleanupLeftTailIdle pCarryLeft ∧
      CleanupRightTailIdle pCarryRight ∧
      pCarryRight.core.p_carry = true := by
  constructor
  · exact
      { state_none := rfl
        path_bot := rfl
        p_carry_false := rfl
        permit_false := rfl }
  constructor
  · exact
      { state_none := rfl
        path_bot := rfl
        permit_false := rfl }
  · rfl

/-- The normal deletion-priority branch is selected. -/
theorem pCarry_entry_priority_open :
    deletionActive (normalizeDeletion pCarryLeft) = false ∧
      deletionActive (normalizeDeletion pCarryRight) = false := by
  decide

/-- The ready-shaped pair is follower/follower and reset-free. -/
theorem pCarry_entry_reset_free_followers :
    pCarryLeft.core.leader = false ∧
      pCarryRight.core.leader = false ∧
      pCarryLeft.core.reset_cmd = false ∧
      pCarryRight.core.reset_cmd = false ∧
      pCarryLeft.core.echo = false ∧
      pCarryRight.core.echo = false := by
  decide

private def pCarryBeforeCheck :=
  wallSweepResetProbePreCheckResetBeforeCheck
    pCarry_h2 1 pCarryLeft pCarryRight

private def pCarryAfterCheck :=
  wallSweepResetProbePreCheckResetAfterCheck
    pCarry_h2 1 pCarryLeft pCarryRight

private def pCarryAfterDisappear :=
  authorizedDisappear pCarry_h2
    pCarryAfterCheck.1 pCarryAfterCheck.2

private def pCarryAfterCompare :=
  authorizedCompareSigActionOne pCarry_h2
    pCarryAfterDisappear.1 pCarryAfterDisappear.2

private def pCarryAfterSuppress :=
  authorizedReconcile (suppressSigResetKill pCarry_h2)
    pCarryAfterCompare.1 pCarryAfterCompare.2

private def pCarryAfterEgress :=
  authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink pCarry_h2)
    pCarryAfterSuppress.1 pCarryAfterSuppress.2

private def pCarryAfterWrite :=
  authorizedReconcile (writeSeqIncrementGate pCarry_h2)
    pCarryAfterEgress.1 pCarryAfterEgress.2

private def pCarryBorn : Bool :=
  leaderBirthBeforeOrAtCheck
    pCarryLeft pCarryRight pCarryBeforeCheck pCarryAfterCheck

private def pCarryAfterMark :=
  markLeaderBirth pCarryBorn pCarryAfterWrite

private def pCarryAuthorizedOut :=
  multiLeaderCleanupAuthorizedTransition
    pCarry_h2 1 pCarryLeft pCarryRight

/-- Every authorized stage preserves the responder carry admitted at entry. -/
theorem authorized_stage_trace_preserves_admitted_pCarry :
    pCarryRight.core.p_carry = true ∧
      pCarryBeforeCheck.2.core.p_carry = true ∧
      pCarryAfterCheck.2.core.p_carry = true ∧
      pCarryAfterDisappear.2.core.p_carry = true ∧
      pCarryAfterCompare.2.core.p_carry = true ∧
      pCarryAfterSuppress.2.core.p_carry = true ∧
      pCarryAfterEgress.2.core.p_carry = true ∧
      pCarryAfterWrite.2.core.p_carry = true ∧
      pCarryAfterMark.2.core.p_carry = true ∧
      pCarryAuthorizedOut.2.core.p_carry = true := by
  decide

private theorem pCarryLeftDomain :
    pCarryLeftRaw.inProtocolDomain 1 := by
  simp [pCarryLeftRaw, pCarryQuietState, AgentState.inProtocolDomain]

private theorem pCarryRightDomain :
    pCarryRightRaw.inProtocolDomain 1 := by
  simp [pCarryRightRaw, pCarryQuietState, AgentState.inProtocolDomain]

private def pCarryLeftBounded : AuthorizedBoundedAgentState 2 1 :=
  ⟨BoundedAgentState.ofDomain pCarryLeftRaw pCarryLeftDomain, false⟩

private def pCarryRightBounded : AuthorizedBoundedAgentState 2 1 :=
  ⟨BoundedAgentState.ofDomain pCarryRightRaw pCarryRightDomain, false⟩

private def pCarryLeftExpiring : ExpiringAgentState 2 1 1 :=
  ⟨pCarryLeftBounded, ⟨1, by omega⟩⟩

private def pCarryRightExpiring : ExpiringAgentState 2 1 1 :=
  ⟨pCarryRightBounded, ⟨1, by omega⟩⟩

private def pCarryBoundedOut :=
  multiLeaderCleanupBoundedTransition
    pCarry_h2 1 pCarryLeftBounded pCarryRightBounded

private def pCarryExpiringOut :=
  multiLeaderCleanupTransition
    pCarry_h2 1 1 pCarryLeftExpiring pCarryRightExpiring

/-- Bounded reification and positive-static expiry preserve the admitted
responder carry. -/
theorem complete_transition_preserves_admitted_pCarry :
    pCarryBoundedOut.2.erase.core.p_carry = true ∧
      pCarryExpiringOut.2.core.erase.core.p_carry = true ∧
      pCarryExpiringOut.2.stall.val = 0 := by
  decide

/-- Complete-transition counterexample to a handoff producer derived from the
current asymmetric idle premises alone. -/
theorem complete_transition_not_left_idle_from_current_entry :
    ¬ CleanupLeftTailIdle pCarryExpiringOut.2.core.erase := by
  intro hleft
  have hout : pCarryExpiringOut.2.core.erase.core.p_carry = true :=
    complete_transition_preserves_admitted_pCarry.2.1
  have hbad : true = false :=
    hout.symm.trans hleft.p_carry_false
  simp at hbad

end PhysicalBridge
end PPLLCompleteMultiLeaderCleanup
