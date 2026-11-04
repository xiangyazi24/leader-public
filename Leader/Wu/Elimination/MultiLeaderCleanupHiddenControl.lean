import Leader.Wu.Safety.Counterexamples
import Leader.Wu.Elimination.MultiLeaderCleanupResetFreeSweep

/-!
# Hidden-control audit for multi-leader cleanup

This module does four deliberately separate things.

1. It reconstructs the exact six-agent fixture of the rejected assertion and records the actual
   pre-CHECK fields after prefix `[0, 1, 2]`.  The reported producer is absent:
   the responder is still a leader, so the SIGMOVE leader wall clears both
   comparison endpoints before the named pre-CHECK boundary.
2. It gives a smaller genuine reset/WAIT trace on three agents.  A reset is
   seeded, handed through a label-zero follower, and then that follower is
   scheduled again after the reset has moved onward.  With `psi = 3`, the next
   responder is nonterminal and remains a follower, so GENSIG leaves a
   path-free `.produce` initiator at the actual pre-CHECK boundary.
3. It integrates the reset-host assignments only at the two existing
   Algorithm-14 reset-kill sites and proves a closed before/after regression on
   that trace.
4. It composes those assignments with the unconditional responder
   `p_carry := false` boundary immediately after DISAPPEAR.  A final reset-free
   fixture proves the remaining obstruction: neither repair supplies
   pre-CHECK WAIT/GENSIG readiness for a reset-free label-zero initiator.

The reset-host assignments are a new protocol-repair candidate, not a transcription
of printed Algorithm 14.  The responder assignment is scoped to this separately
named cleanup suffix and does not change literal `PPLL.disappear`.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PhysicalBridge
namespace Q5577HiddenControlAudit

open PPLL PPLLRepair PPLLResearchFormulation PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWriteIncrementGate PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepPreCheckResetRepair
  PPLLPpsiLeaderCreationRepair

set_option autoImplicit false

variable {psi : Nat}

/-! ## A compact exact view of the audited fields -/

structure HiddenControlAuditView (psi : Nat) where
  state : MainState
  wait : Bool
  h_field : Bool
  carry : Bool
  path : PathInfo
  p_carry : Bool
  reset_cmd : Bool
  path0Crossed : Bool
  deriving DecidableEq, Repr

namespace HiddenControlAuditView

def ofAuthorized (u : AuthorizedAgentState psi) :
    HiddenControlAuditView psi where
  state := u.core.state
  wait := u.core.wait
  h_field := u.core.h_field
  carry := u.core.carry
  path := u.core.path
  p_carry := u.core.p_carry
  reset_cmd := u.core.reset_cmd
  path0Crossed := u.path0Crossed

end HiddenControlAuditView

/-! ## 1. Exact reconstruction and correction of the rejected fixture -/

abbrev Q5539Psi : Nat := 2
abbrev Q5539Kappa : Nat := 0
abbrev Q5539Tau : Nat := 16

private def q5539HPsi : Q5539Psi > 0 := by decide

private def q5539Ring6 : DirectedRing 6 :=
  ⟨by decide⟩

/-- Exact physical input of the rejected fixture: leaders at 0 and 3, labels
`[0, 1, 0, 0, 1, 0]`, and only position 2 starts with `wait = false`. -/
def q5539Raw (i : Fin 6) : AgentState Q5539Psi :=
  match i.val with
  | 0 => PPLLCounterexample.state2 0 true
  | 1 => PPLLCounterexample.state2 1
  | 2 => { PPLLCounterexample.state2 0 with wait := false }
  | 3 => PPLLCounterexample.state2 0 true
  | 4 => PPLLCounterexample.state2 1
  | _ => PPLLCounterexample.state2 0

theorem q5539_raw_domain (i : Fin 6) :
    (q5539Raw i).inProtocolDomain Q5539Kappa := by
  have hlt : i.val < 6 := i.isLt
  have hi :
      i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨
        i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by
    omega
  rcases hi with h0 | h1 | h2 | h3 | h4 | h5
  · simp [q5539Raw, h0, AgentState.inProtocolDomain,
      PPLLCounterexample.state2]
  · simp [q5539Raw, h1, AgentState.inProtocolDomain,
      PPLLCounterexample.state2]
  · simp [q5539Raw, h2, AgentState.inProtocolDomain,
      PPLLCounterexample.state2]
  · simp [q5539Raw, h3, AgentState.inProtocolDomain,
      PPLLCounterexample.state2]
  · simp [q5539Raw, h4, AgentState.inProtocolDomain,
      PPLLCounterexample.state2]
  · simp [q5539Raw, h5, AgentState.inProtocolDomain,
      PPLLCounterexample.state2]

def q5539Bounded (i : Fin 6) :
    BoundedAgentState Q5539Psi Q5539Kappa :=
  BoundedAgentState.ofDomain (q5539Raw i) (q5539_raw_domain i)

def q5539Authorized (i : Fin 6) :
    AuthorizedBoundedAgentState Q5539Psi Q5539Kappa :=
  ⟨q5539Bounded i, false⟩

def q5539Input (i : Fin 6) :
    ExpiringAgentState Q5539Psi Q5539Kappa Q5539Tau :=
  ⟨q5539Authorized i, freshStall Q5539Tau⟩

/-- Exact prefix used by the rejected assertion. -/
def q5539Prefix : DetSchedule 6 := [0, 1, 2]

/-- Exact physical leader-kill word stated by the rejected assertion. -/
def q5539CoreWord : DetSchedule 6 :=
  [0, 1, 2, 2, 3, 4, 5, 0, 5, 4, 3]

def q5539CriticalConfig :
    Fin 6 → ExpiringAgentState Q5539Psi Q5539Kappa Q5539Tau :=
  runLocalSchedule q5539Ring6
    (multiLeaderCleanupTransition q5539HPsi Q5539Kappa Q5539Tau)
    q5539Input q5539Prefix

def q5539CriticalLeft :
    ExpiringAgentState Q5539Psi Q5539Kappa Q5539Tau :=
  q5539CriticalConfig 2

def q5539CriticalRight :
    ExpiringAgentState Q5539Psi Q5539Kappa Q5539Tau :=
  q5539CriticalConfig 3

def q5539CriticalLeft0 : AuthorizedAgentState Q5539Psi :=
  normalizeDeletion q5539CriticalLeft.core.erase

def q5539CriticalRight0 : AuthorizedAgentState Q5539Psi :=
  normalizeDeletion q5539CriticalRight.core.erase

/-- Prefix output just after the reset-aware GENSIG/CLEAN/ELIMINATE/SIGMOVE
stages and before the explicit pre-CHECK reset wall. -/
def q5539BeforeResetWall :
    AuthorizedAgentState Q5539Psi × AuthorizedAgentState Q5539Psi :=
  wallSweepResetProbeAuthorizedBeforeCheck
    q5539HPsi Q5539Kappa q5539CriticalLeft0 q5539CriticalRight0

/-- The actual named boundary used by the cleanup pair-readiness record. -/
def q5539BeforeCheck :
    AuthorizedAgentState Q5539Psi × AuthorizedAgentState Q5539Psi :=
  wallSweepResetProbePreCheckResetBeforeCheck
    q5539HPsi Q5539Kappa q5539CriticalLeft0 q5539CriticalRight0

theorem q5539_fixture_shape :
    List.ofFn (fun i : Fin 6 =>
      (q5539Input i).core.erase.core.label.val) =
        [0, 1, 0, 0, 1, 0] ∧
    List.ofFn (fun i : Fin 6 =>
      (q5539Input i).core.erase.core.leader) =
        [true, false, false, true, false, false] ∧
    (q5539Input 2).core.erase.core.wait = false := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 200000 in
/-- The input to the repeated `2 -> 3` boundary is the part the rejected assertion got right:
the reset has moved to the still-leading responder. -/
theorem q5539_prefix_input_actual :
    q5539CriticalLeft0.core.leader = false ∧
      q5539CriticalLeft0.core.label = (0 : Fin Q5539Psi) ∧
      q5539CriticalLeft0.core.wait = false ∧
      q5539CriticalLeft0.core.state = .none ∧
      q5539CriticalLeft0.core.path = .bot ∧
      q5539CriticalLeft0.core.reset_cmd = false ∧
      q5539CriticalRight0.core.leader = true ∧
      q5539CriticalRight0.core.label = (0 : Fin Q5539Psi) ∧
      q5539CriticalRight0.core.reset_cmd = true := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 200000 in
/-- The missed stage in the rejected assertion: because the responder is a leader, the actual
SIGMOVE wall has already neutralized both comparison carriers. -/
theorem q5539_right_leader_sigmove_wall_actual :
    q5539CriticalRight0.core.leader = true ∧
      q5539BeforeResetWall.1.core.state = .none ∧
      q5539BeforeResetWall.1.core.path = .bot ∧
      q5539BeforeResetWall.1.core.p_carry = false ∧
      q5539BeforeResetWall.1.path0Crossed = false ∧
      q5539BeforeResetWall.2.core.state = .none ∧
      q5539BeforeResetWall.2.core.path = .bot ∧
      q5539BeforeResetWall.2.core.p_carry = false ∧
      q5539BeforeResetWall.2.path0Crossed = false := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 200000 in
/-- Exact audited pre-CHECK view.  WAIT remains false, but no producer remains:
SIGMOVE's right-leader wall has changed the initiator state back to `.none`.
The second WAIT interaction also leaves `h_field = false` and `carry = false`. -/
theorem q5539_precheck_actual_view :
    HiddenControlAuditView.ofAuthorized q5539BeforeCheck.1 =
      { state := .none
        wait := false
        h_field := false
        carry := false
        path := .bot
        p_carry := false
        reset_cmd := false
        path0Crossed := false } := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 200000 in
/-- All four fields of the real left-idle contract hold. -/
theorem q5539_precheck_is_cleanupLeftTailIdle :
    CleanupLeftTailIdle q5539BeforeCheck.1 := by
  exact
    { state_none := by decide
      path_bot := by decide
      p_carry_false := by decide
      permit_false := by decide }

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 200000 in
/-- Closed refutation of the first failed kernel-decision proposition. -/
theorem q5539_false_produce_claim :
    ¬(
      q5539BeforeCheck.1.core.state = .produce ∧
      q5539BeforeCheck.1.core.wait = false ∧
      q5539BeforeCheck.1.core.path = .bot ∧
      q5539BeforeCheck.1.core.p_carry = false ∧
      q5539BeforeCheck.1.path0Crossed = false) := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 200000 in
/-- Closed refutation of the corresponding `state != none` proposition. -/
theorem q5539_false_not_none_claim :
    ¬(
      q5539BeforeCheck.1.core.state ≠ .none ∧
      q5539BeforeCheck.1.core.path = .bot ∧
      q5539BeforeCheck.1.core.p_carry = false ∧
      q5539BeforeCheck.1.path0Crossed = false) := by
  decide

/-! ## 2. Exact reset-host and responder-carry candidate kernels -/

/-- The new reset-host candidate.  This is deliberately separate from the
printed Algorithm 14 lane. -/
def resetHostSanitizerQ5577 (u : AgentState psi) : AgentState psi :=
  if u.reset_cmd then
    { clearComparisonSignal u with
      wait := true
      h_field := false
      carry := false }
  else u

theorem resetHostSanitizerQ5577_exact
    (u : AgentState psi) (hreset : u.reset_cmd = true) :
    let v := resetHostSanitizerQ5577 u
    ComparisonNeutral v ∧
      v.wait = true ∧
      v.h_field = false ∧
      v.carry = false ∧
      v.reset_cmd = true := by
  simp [resetHostSanitizerQ5577, hreset,
    ComparisonNeutral, clearComparisonSignal]

theorem resetHostSanitizerQ5577_eq_self_of_false
    (u : AgentState psi) (hreset : u.reset_cmd = false) :
    resetHostSanitizerQ5577 u = u := by
  simp [resetHostSanitizerQ5577, hreset]

/-- Algorithm 14 with the reset-host transformer substituted at exactly the two
current reset-kill sites.  All stage ordering is otherwise unchanged. -/
def suppressSigHiddenControlQ5577
    (hpsi : psi > 0) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let q0 := suppressSigStart l r
  let q0 :=
    (resetHostSanitizerQ5577 q0.1,
      resetHostSanitizerQ5577 q0.2)
  let q1 := suppressSigMoveReset q0.1 q0.2
  let q1 :=
    (resetHostSanitizerQ5577 q1.1,
      resetHostSanitizerQ5577 q1.2)
  let q2 := suppressSigTerminal hpsi q1.1 q1.2
  let q3 := suppressSigEcho q2.1 q2.2
  suppressSigFinish q3.1 q3.2

/-- The cleanup-local one-field responder postprocessor. -/
def clearAuthorizedResponderPCarryQ5577
    (u : AuthorizedAgentState psi) : AuthorizedAgentState psi :=
  ⟨{ u.core with p_carry := false }, u.path0Crossed⟩

def authorizedDisappearResponderPCarryOffQ5577
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q := authorizedDisappear hpsi l r
  (q.1, clearAuthorizedResponderPCarryQ5577 q.2)

theorem authorizedDisappearResponderPCarryOffQ5577_exact
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    let q := authorizedDisappear hpsi l r
    let out := authorizedDisappearResponderPCarryOffQ5577 hpsi l r
    out.1 = q.1 ∧
      out.2.core.state = q.2.core.state ∧
      out.2.core.path = q.2.core.path ∧
      out.2.path0Crossed = q.2.path0Crossed ∧
      out.2.core.p_carry = false := by
  dsimp only [authorizedDisappearResponderPCarryOffQ5577,
    clearAuthorizedResponderPCarryQ5577]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Candidate authorized suffixes and dispatchers -/

/-- Current cleanup suffix with only Algorithm 14 replaced by the reset-host candidate. -/
def multiLeaderAfterCheckSuffixSuppressedQ5577
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigHiddenControlQ5577 hpsi) q1.1 q1.2
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  authorizedReconcile
    (writeSeqIncrementGate hpsi) q3.1 q3.2

/-- Current cleanup suffix with both candidates: the responder postprocessor immediately after
DISAPPEAR, then the reset-host sanitizer at the two Algorithm-14 reset hosts. -/
def multiLeaderAfterCheckSuffixCombinedQ5577
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q0 := authorizedDisappearResponderPCarryOffQ5577 hpsi l r
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigHiddenControlQ5577 hpsi) q1.1 q1.2
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  authorizedReconcile
    (writeSeqIncrementGate hpsi) q3.1 q3.2

/-- The current deletion-priority dispatcher parameterized only by its ordinary
post-CHECK suffix.  This avoids changing either priority branch or any prefix
stage. -/
def multiLeaderCleanupAuthorizedTransitionWithSuffixQ5577
    (hpsi : psi > 0) (kappa : Nat)
    (suffix : AuthorizedAgentState psi → AuthorizedAgentState psi →
      AuthorizedAgentState psi × AuthorizedAgentState psi)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then
    authorizedEliminateSig hpsi l0 r0
  else if deletionActive l0 then
    (l0, r0)
  else
    let beforeCheck :=
      wallSweepResetProbePreCheckResetBeforeCheck
        hpsi kappa l0 r0
    let afterCheck :=
      wallSweepResetProbePreCheckResetAfterCheck
        hpsi kappa l0 r0
    let born :=
      leaderBirthBeforeOrAtCheck
        l0 r0 beforeCheck afterCheck
    markLeaderBirth born (suffix afterCheck.1 afterCheck.2)

def multiLeaderCleanupAuthorizedTransitionSuppressedQ5577
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  multiLeaderCleanupAuthorizedTransitionWithSuffixQ5577
    hpsi kappa (multiLeaderAfterCheckSuffixSuppressedQ5577 hpsi) l r

def multiLeaderCleanupAuthorizedTransitionCombinedQ5577
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  multiLeaderCleanupAuthorizedTransitionWithSuffixQ5577
    hpsi kappa (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi) l r

/-! ## 3. Smallest explicit real reset/WAIT trace -/

/-- A generic quiet raw state used only by the fixed finite controls below. -/
private def quietState
    {psi : Nat} (label : Fin psi) (leader : Bool := false) :
    AgentState psi where
  leader := leader
  probe := false
  phase := false
  bit := false
  wait := true
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
  signal_B := 0
  bullet := 0
  shield := true
  write_state := .none
  write := .none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

abbrev TracePsi : Nat := 3
abbrev TraceKappa : Nat := 0

private def traceHPsi : TracePsi > 0 := by decide
private def traceRing3 : DirectedRing 3 := ⟨by decide⟩

/-- Stable labels `[2, 0, 1]`.  Position 0 is the reset-seeding leader;
position 1 is the label-zero follower whose stale `wait = false` is audited;
position 2 is a nonterminal follower, which is exactly what the false
fixture lacked at its repeated edge. -/
def hiddenTraceRaw (i : Fin 3) : AgentState TracePsi :=
  match i.val with
  | 0 => quietState (2 : Fin TracePsi) true
  | 1 => { quietState (0 : Fin TracePsi) with wait := false }
  | _ => quietState (1 : Fin TracePsi)

def hiddenTraceInput (i : Fin 3) : AuthorizedAgentState TracePsi :=
  ⟨hiddenTraceRaw i, false⟩

def hiddenSeedWord : DetSchedule 3 := [0]
def hiddenTransferWord : DetSchedule 3 := [0, 1]

/-- After the source edge only: position 1 still carries reset. -/
def hiddenAfterSeed : Fin 3 → AuthorizedAgentState TracePsi :=
  runLocalSchedule traceRing3
    (multiLeaderCleanupAuthorizedTransition traceHPsi TraceKappa)
    hiddenTraceInput hiddenSeedWord

/-- The first `1 -> 2` pre-CHECK boundary is reset-covered and therefore
neutral. -/
def hiddenCoveredBeforeCheck :
    AuthorizedAgentState TracePsi × AuthorizedAgentState TracePsi :=
  wallSweepResetProbePreCheckResetBeforeCheck
    traceHPsi TraceKappa (hiddenAfterSeed 1) (hiddenAfterSeed 2)

/-- Current execution after the source edge and the first `1 -> 2` handoff. -/
def hiddenCurrentAfterTransfer :
    Fin 3 → AuthorizedAgentState TracePsi :=
  runLocalSchedule traceRing3
    (multiLeaderCleanupAuthorizedTransition traceHPsi TraceKappa)
    hiddenTraceInput hiddenTransferWord

/-- The repeated `1 -> 2` pre-CHECK boundary under the current transition. -/
def hiddenCurrentRepeatedBeforeCheck :
    AuthorizedAgentState TracePsi × AuthorizedAgentState TracePsi :=
  wallSweepResetProbePreCheckResetBeforeCheck
    traceHPsi TraceKappa
    (hiddenCurrentAfterTransfer 1) (hiddenCurrentAfterTransfer 2)

/-- Same two-edge prefix with only the reset-host sanitizer substituted at Algorithm 14. -/
def hiddenSuppressedAfterTransfer :
    Fin 3 → AuthorizedAgentState TracePsi :=
  runLocalSchedule traceRing3
    (multiLeaderCleanupAuthorizedTransitionSuppressedQ5577
      traceHPsi TraceKappa)
    hiddenTraceInput hiddenTransferWord

/-- Repeated boundary after the reset-host candidate has processed both reset hosts. -/
def hiddenSuppressedRepeatedBeforeCheck :
    AuthorizedAgentState TracePsi × AuthorizedAgentState TracePsi :=
  wallSweepResetProbePreCheckResetBeforeCheck
    traceHPsi TraceKappa
    (hiddenSuppressedAfterTransfer 1)
    (hiddenSuppressedAfterTransfer 2)

theorem hidden_trace_fixture_shape :
    List.ofFn (fun i : Fin 3 =>
      (hiddenTraceInput i).core.label.val) = [2, 0, 1] ∧
    List.ofFn (fun i : Fin 3 =>
      (hiddenTraceInput i).core.leader) = [true, false, false] ∧
    (hiddenTraceInput 1).core.wait = false := by
  decide

/-- One edge is not yet a counterexample: the initiator still carries reset,
so the actual pre-CHECK wall clears its transient GENSIG state. -/
theorem hidden_after_seed_is_reset_covered :
    (hiddenAfterSeed 1).core.reset_cmd = true ∧
      HiddenControlAuditView.ofAuthorized hiddenCoveredBeforeCheck.1 =
        { state := .none
          wait := false
          h_field := true
          carry := false
          path := .bot
          p_carry := false
          reset_cmd := true
          path0Crossed := false } := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 200000 in
theorem hidden_after_seed_is_cleanupLeftTailIdle :
    CleanupLeftTailIdle hiddenCoveredBeforeCheck.1 := by
  exact
    { state_none := by decide
      path_bot := by decide
      p_carry_false := by decide
      permit_false := by decide }

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 200000 in
/-- After two interactions the reset has moved onward, but current Algorithm 14
has left the old host's waiting control false.  On the next real pre-CHECK
boundary, GENSIG leaves a path-free producer. -/
theorem hidden_current_repeated_boundary_actual :
    HiddenControlAuditView.ofAuthorized
        hiddenCurrentRepeatedBeforeCheck.1 =
      { state := .produce
        wait := false
        h_field := false
        carry := false
        path := .bot
        p_carry := false
        reset_cmd := false
        path0Crossed := false } := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 200000 in
theorem hidden_current_repeated_boundary_not_left_idle :
    ¬ CleanupLeftTailIdle hiddenCurrentRepeatedBeforeCheck.1 := by
  intro h
  have hproduce :
      hiddenCurrentRepeatedBeforeCheck.1.core.state = .produce := by
    decide
  have hbad : MainState.produce = MainState.none :=
    hproduce.symm.trans h.state_none
  exact MainState.noConfusion hbad

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 200000 in
/-- The reset-host sanitizer sets `wait = true` when the reset reaches position 1 and again when
position 1 sends it onward.  The subsequent WAIT stage may toggle `h_field`,
but it cannot start GENSIG because the waiting control remains true. -/
theorem hidden_suppressed_repeated_boundary_actual :
    HiddenControlAuditView.ofAuthorized
        hiddenSuppressedRepeatedBeforeCheck.1 =
      { state := .none
        wait := true
        h_field := true
        carry := false
        path := .bot
        p_carry := false
        reset_cmd := false
        path0Crossed := false } := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 200000 in
theorem hidden_suppressed_repeated_boundary_left_idle :
    CleanupLeftTailIdle hiddenSuppressedRepeatedBeforeCheck.1 := by
  exact
    { state_none := by decide
      path_bot := by decide
      p_carry_false := by decide
      permit_false := by decide }

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 200000 in
/-- Closed before/after regression for the exact reset-host candidate on a genuine
full authorized-prefix trace. -/
theorem q5531_sanitizer_real_trace_regression :
    hiddenCurrentRepeatedBeforeCheck.1.core.state = .produce ∧
      hiddenCurrentRepeatedBeforeCheck.1.core.wait = false ∧
      hiddenSuppressedRepeatedBeforeCheck.1.core.state = .none ∧
      hiddenSuppressedRepeatedBeforeCheck.1.core.wait = true := by
  decide

/-- The explicit trace uses the shortest source/handoff prefix in this fixture:
after one edge reset still covers the initiator; after the second edge it has
moved onward and the repeated edge exposes stale WAIT. -/
theorem hidden_trace_prefix_lengths :
    hiddenSeedWord.length = 1 ∧ hiddenTransferWord.length = 2 := by
  decide

/-! ## 4. Exact obstruction remaining after both repairs -/

/-- Reset-free, priority-open, stable `0 -> 1` pair.  The responder deliberately
starts with the carry obstruction, while the initiator deliberately starts
with the independent WAIT/GENSIG obstruction. -/
def remainingResetFreeLeft : AuthorizedAgentState TracePsi :=
  ⟨{ quietState (0 : Fin TracePsi) with wait := false }, false⟩

def remainingResetFreeRight : AuthorizedAgentState TracePsi :=
  ⟨{ quietState (1 : Fin TracePsi) with p_carry := true }, false⟩

def remainingResetFreeBeforeCheck :
    AuthorizedAgentState TracePsi × AuthorizedAgentState TracePsi :=
  wallSweepResetProbePreCheckResetBeforeCheck
    traceHPsi TraceKappa remainingResetFreeLeft remainingResetFreeRight

def remainingCombinedOutput :
    AuthorizedAgentState TracePsi × AuthorizedAgentState TracePsi :=
  multiLeaderCleanupAuthorizedTransitionCombinedQ5577
    traceHPsi TraceKappa remainingResetFreeLeft remainingResetFreeRight

/-- Exact residual boundary.  Both reset guards are false, so the reset-host sanitizer is inert.
GENSIG therefore produces at the initiator before either post-CHECK candidate
can run.  The responder carry is still present at this early boundary. -/
theorem combined_remaining_reset_free_boundary_actual :
    deletionActive (normalizeDeletion remainingResetFreeLeft) = false ∧
      deletionActive (normalizeDeletion remainingResetFreeRight) = false ∧
      remainingResetFreeLeft.core.reset_cmd = false ∧
      remainingResetFreeRight.core.reset_cmd = false ∧
      remainingResetFreeBeforeCheck.1.core.state = .produce ∧
      remainingResetFreeBeforeCheck.1.core.wait = false ∧
      remainingResetFreeBeforeCheck.1.core.path = .bot ∧
      remainingResetFreeBeforeCheck.1.core.p_carry = false ∧
      remainingResetFreeBeforeCheck.1.path0Crossed = false ∧
      remainingResetFreeBeforeCheck.2.core.p_carry = true := by
  decide

theorem combined_remaining_reset_free_not_left_idle :
    ¬ CleanupLeftTailIdle remainingResetFreeBeforeCheck.1 := by
  intro h
  have hproduce :
      remainingResetFreeBeforeCheck.1.core.state = .produce := by
    decide
  have hbad : MainState.produce = MainState.none :=
    hproduce.symm.trans h.state_none
  exact MainState.noConfusion hbad

/-- The responder postprocessor does remove the responder carry at its post-DISAPPEAR boundary, but
that later one-field success cannot repair the already-false pre-CHECK
`state_none` obligation.  This is the exact obstruction remaining after the two
candidates are combined. -/
theorem combined_repairs_clear_carry_but_leave_wait_obstruction :
    remainingCombinedOutput.2.core.p_carry = false ∧
      remainingResetFreeBeforeCheck.1.core.state = .produce ∧
      remainingResetFreeBeforeCheck.1.core.wait = false ∧
      ¬ CleanupLeftTailIdle remainingResetFreeBeforeCheck.1 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  exact combined_remaining_reset_free_not_left_idle

end Q5577HiddenControlAudit
end PhysicalBridge
end PPLLCompleteMultiLeaderCleanup
