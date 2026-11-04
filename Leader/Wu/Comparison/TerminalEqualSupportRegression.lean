import Leader.Wu.Comparison.TerminalEqualSupportRepair
import Leader.Wu.Safety.Counterexamples

/-!
# Regressions for terminal-equality support

The negative fixture is a pathless terminal `.equal`: current CHECK creates a
leader and WRITE_SEQ migrates it.  The support sanitizer blocks exactly that
malformed local state.  Positive checks retain a locally supported equality
prefix, while T1 remains executable because its forged carrier is locally
consistent.  These are transition-level facts, not provenance or global safety.
-/

namespace PPLLTerminalEqualSupportRegression

open PPLL PPLLRepair PPLLCounterexample PPLLAuthorizedComparisonRepair
  PPLLTerminalEqualSupportRepair

/-- Pathless stable-edge initiator. -/
def pathlessEqualLeft : AgentState 2 :=
  state2 0 false .none

/-- Terminal pathless equality accepted by the current CHECK assignment. -/
def pathlessEqualRight : AgentState 2 :=
  state2 1 false .equal

private def pathlessAuthLeft : AuthorizedAgentState 2 :=
  ⟨pathlessEqualLeft, false⟩

private def pathlessAuthRight : AuthorizedAgentState 2 :=
  ⟨pathlessEqualRight, false⟩

private def pathlessBeforeCheck :=
  authorizedBeforeCheck (by omega : 2 > 0) 10
    pathlessAuthLeft pathlessAuthRight

private def pathlessAfterCheck :=
  authorizedCheckSig (by omega : 2 > 0)
    pathlessBeforeCheck.1 pathlessBeforeCheck.2

private def pathlessLiteralBeforeCheck :=
  ppllBeforeCheck (by omega : 2 > 0) 10
    pathlessEqualLeft pathlessEqualRight

private def pathlessLiteralAfterCheck :=
  ppllAfterCheck (by omega : 2 > 0) 10
    pathlessEqualLeft pathlessEqualRight

private def pathlessLiteralBeforeWrite :=
  ppllBeforeWriteSeq (by omega : 2 > 0) 10
    pathlessEqualLeft pathlessEqualRight

private def pathlessOldOut :=
  ppllAuthorizedRepair (by omega : 2 > 0) 10
    pathlessAuthLeft pathlessAuthRight

/-- The current authorized transition leaves the unsupported equality intact
until CHECK, creates the responder leader, and migrates it left. -/
theorem current_pathless_equal_creates_and_migrates :
    pathlessBeforeCheck.2.core.path = .bot ∧
      pathlessBeforeCheck.2.core.state = .equal ∧
      pathlessAfterCheck.2.core.leader = true ∧
      pathlessOldOut.1.core.leader = true ∧
      pathlessOldOut.2.core.leader = false := by
  decide

/-- Literal staged execution pins CHECK as creation and WRITE_SEQ as
migration, conditional on the audited no-op interpretation of earlier bottom
reads. -/
theorem literal_pathless_equal_staged_creation_and_migration :
    pathlessLiteralBeforeCheck.2.path = .bot ∧
      pathlessLiteralBeforeCheck.2.state = .equal ∧
      pathlessLiteralAfterCheck.2.leader = true ∧
      pathlessLiteralBeforeWrite.1.leader = false ∧
      pathlessLiteralBeforeWrite.2.leader = true ∧
      (ppll (by omega : 2 > 0) 10
        pathlessEqualLeft pathlessEqualRight).1.leader = true ∧
      (ppll (by omega : 2 > 0) 10
        pathlessEqualLeft pathlessEqualRight).2.leader = false := by
  decide

/-- Literal audited P_PLL has the same local creation/migration behavior. -/
theorem literal_pathless_equal_creates_and_migrates :
    let q := ppll (by omega : 2 > 0) 10 pathlessEqualLeft pathlessEqualRight
    q.1.leader = true ∧ q.2.leader = false := by
  exact ⟨literal_pathless_equal_staged_creation_and_migration.2.2.2.2.2.1,
    literal_pathless_equal_staged_creation_and_migration.2.2.2.2.2.2⟩

private def pathlessSupportOut :=
  terminalEqualSupportAuthorizedTransition (by omega : 2 > 0) 10
    pathlessAuthLeft pathlessAuthRight

/-- Sanitization demotes the pathless equality before CHECK, so neither endpoint
becomes a leader. -/
theorem terminal_equal_support_blocks_pathless_hole :
    let clean := sanitizeAuthorizedPair (by omega : 2 > 0) pathlessBeforeCheck
    clean.2.core.state = .none ∧ clean.2.core.path = .bot ∧
      pathlessSupportOut.1.core.leader = false ∧
      pathlessSupportOut.2.core.leader = false := by
  decide

/-! ## Positive local support and T1 scope boundary -/

private def supportedEqualLeft : AuthorizedAgentState 2 :=
  ⟨{ state2 0 false .equal with path := .some 0 0 }, false⟩

private def supportedReadyRight : AuthorizedAgentState 2 :=
  ⟨{ state2 1 false .CHECK_ready with path := .some 1 0 }, false⟩

/-- A real locally supported equality prefix is unchanged and CHECK may still
finish equality and create its responder leader. -/
theorem sanitizer_preserves_supported_check_prefix :
    let l := sanitizeAuthorizedTerminalEqual (by omega : 2 > 0)
      supportedEqualLeft
    let r := sanitizeAuthorizedTerminalEqual (by omega : 2 > 0)
      supportedReadyRight
    let q := authorizedCheckSig (by omega : 2 > 0) l r
    l = supportedEqualLeft ∧ r = supportedReadyRight ∧
      q.1.core.state = .equal ∧ q.2.core.state = .equal ∧
      q.2.core.leader = true := by
  decide

/-- A pre-existing terminal `.equal` with matching local path data exercises
the sanitizer's positive branch directly and remains unchanged. -/
theorem sanitizer_keeps_supported_terminal_equal :
    sanitizeAuthorizedTerminalEqual (by omega : 2 > 0)
      ⟨{ state2 1 false .equal with path := .some 1 0 }, false⟩ =
        ⟨{ state2 1 false .equal with path := .some 1 0 }, false⟩ := by
  decide

/-- T1's terminal component is locally label/bit consistent, so the sanitizer
is intentionally identity on it. -/
theorem sanitizer_does_not_claim_to_fix_t1 :
    sanitizeTerminalEqual (by omega : 2 > 0) a3 = a3 := by
  decide

set_option maxRecDepth 4096 in
/-- Consequently the support repair does not solve T1 provenance: the complete
forged carrier still creates and migrates a leader. -/
theorem terminal_equal_support_preserves_t1_counterexample :
    let q := terminalEqualSupportAuthorizedTransition (by omega : 2 > 0) 10
      ⟨a2, false⟩ ⟨a3, false⟩
    q.1.core.leader = true ∧ q.2.core.leader = false := by
  decide

/-! ## Source-level five-condition counterexample -/

/-- Four-agent pathless-equality configuration with the old leader at zero. -/
def pathlessEqualConfig : Fin 4 → AgentState 2
  | ⟨0, _⟩ => a0
  | ⟨1, _⟩ => a1
  | ⟨2, _⟩ => pathlessEqualLeft
  | ⟨3, _⟩ => pathlessEqualRight

private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hi := i.isLt
  omega

private theorem pathless_unique : hasUniqueLeader 4 pathlessEqualConfig := by
  refine ⟨0, by decide, ?_⟩
  intro j hj
  rcases fin4_cases j with h | h | h | h <;> subst j
  · rfl
  · simp [pathlessEqualConfig, a1, state2, AgentState.isLeader] at hj
  · simp [pathlessEqualConfig, pathlessEqualLeft, state2,
      AgentState.isLeader] at hj
  · simp [pathlessEqualConfig, pathlessEqualRight, state2,
      AgentState.isLeader] at hj

private theorem pathless_no_bad_bullet :
    noNonPeacefulBullet (by omega : 2 > 0) ring4 pathlessEqualConfig := by
  intro i hi
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [pathlessEqualConfig, pathlessEqualLeft, pathlessEqualRight,
      a0, a1, state2] at hi

private theorem pathless_no_free_barrier :
    noFreeBarrier (by omega : 2 > 0) ring4 pathlessEqualConfig := by
  intro i
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [DirectedRing.rightNeighbor, isBarrier, pathlessEqualConfig,
      pathlessEqualLeft, pathlessEqualRight, a0, a1, state2]

private theorem pathless_no_free_ow :
    noFreeOverwritingSignal (by omega : 2 > 0) ring4 pathlessEqualConfig := by
  refine ⟨0, by decide, by decide, ?_⟩
  intro i hi hbound hfree
  obtain ⟨_, haligned⟩ := hfree.1
  obtain ⟨p, hpath, _⟩ := haligned 0 (by omega)
  have hnone : ∀ k : Fin 4, (pathlessEqualConfig k).path3 = none := by
    intro k
    rcases fin4_cases k with h | h | h | h <;> subst k <;> decide
  rw [hnone] at hpath
  contradiction

private theorem pathless_stable_id :
    isStableIDSequence (by omega : 2 > 0) ring4 pathlessEqualConfig := by
  refine ⟨0, by decide, by decide, ?_, ?_⟩
  · intro k hk
    have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases h with h | h | h | h <;> subst k <;> decide
  · intro i hi hlt
    have : i = 1 := by omega
    subst i
    unfold groupID
    simp [List.range_succ, pathlessEqualConfig, pathlessEqualLeft,
      pathlessEqualRight, a0, a1, state2, trailingZeros]

/-- The pathless equality state satisfies all five printed Definition-2 fields;
those fields do not constrain comparison state/path support. -/
theorem pathlessEqualConfig_paper_safe :
    PaperSafeConfig (by omega : 2 > 0) ring4 pathlessEqualConfig where
  unique_leader := pathless_unique
  no_nonpeaceful_bullet := pathless_no_bad_bullet
  no_free_barrier := pathless_no_free_barrier
  no_free_overwriting_signal := pathless_no_free_ow
  stable_id_sequence := pathless_stable_id

/-- Every pathless counterexample state also lies in the κ=10 value domain. -/
theorem pathlessEqualConfig_inProtocolDomain :
    ∀ i, (pathlessEqualConfig i).inProtocolDomain 10 := by
  intro i
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [AgentState.inProtocolDomain, pathlessEqualConfig,
      pathlessEqualLeft, pathlessEqualRight, a0, a1, state2]

/-- Literal one-step successor on the unsupported terminal equality. -/
def pathlessEqualSuccessor : Fin 4 → AgentState 2 :=
  PopulationProtocol.step (PPLL.protocol (by omega) 10)
    ring4 pathlessEqualConfig 2

/-- The literal successor has leaders at both positions zero and two. -/
theorem pathlessEqualSuccessor_not_unique :
    ¬hasUniqueLeader 4 pathlessEqualSuccessor := by
  intro ⟨i, _, huniq⟩
  have h0 : (pathlessEqualSuccessor 0).isLeader := by decide
  have h2 : (pathlessEqualSuccessor 2).isLeader := by decide
  have h02 : (0 : Fin 4) = 2 := (huniq 0 h0).trans (huniq 2 h2).symm
  have := congrArg Fin.val h02
  omega

/-- Literal five-condition closedness already fails with no comparison path at
all; a pre-existing terminal `.equal` is sufficient. -/
theorem paperSafe_not_closed_by_pathless_equal :
    ¬PopulationProtocol.ClosedPred (PPLL.protocol (by omega) 10) ring4
      (PaperSafeConfig (by omega : 2 > 0) ring4) := by
  intro hclosed
  have hnext := hclosed pathlessEqualConfig pathlessEqualConfig_paper_safe
    pathlessEqualSuccessor ⟨2, rfl⟩
  exact pathlessEqualSuccessor_not_unique hnext.unique_leader

private def pathlessLeaderTest (C : Fin 4 → AgentState 2) : Bool :=
  (C 2).leader

/-- Exactly one of four one-edge schedules selects the pathless bad pair. -/
theorem pathless_equal_bad_schedule_count :
    hitCount ring4 (ppll (by omega) 10) pathlessLeaderTest
      pathlessEqualConfig 1 = 1 := by
  decide

/-- The pathless one-step output violation has exact probability `1/4`. -/
theorem pathless_equal_bad_event_probability :
    hitProbability ring4 (ppll (by omega) 10) pathlessLeaderTest
      pathlessEqualConfig 1 = (1 : Rat) / 4 := by
  unfold hitProbability
  rw [pathless_equal_bad_schedule_count, allSchedules_length]
  rfl

/-! ## Exact finite pathless regression -/

private theorem pathlessDomain :
    pathlessEqualLeft.inProtocolDomain 10 ∧
      pathlessEqualRight.inProtocolDomain 10 := by
  simp [pathlessEqualLeft, pathlessEqualRight,
    AgentState.inProtocolDomain, state2]

private def pathlessFiniteLeft : AuthorizedBoundedAgentState 2 10 :=
  ⟨BoundedAgentState.ofDomain pathlessEqualLeft pathlessDomain.1, false⟩

private def pathlessFiniteRight : AuthorizedBoundedAgentState 2 10 :=
  ⟨BoundedAgentState.ofDomain pathlessEqualRight pathlessDomain.2, false⟩

set_option maxRecDepth 4096 in
/-- The actual finite carrier executes the same repair and keeps both outputs
followers. -/
theorem finite_terminal_equal_support_blocks_pathless_hole :
    let q := terminalEqualSupportBoundedTransition (by omega : 2 > 0) 10
      pathlessFiniteLeft pathlessFiniteRight
    q.1.core.leader = false ∧ q.2.core.leader = false := by
  decide

end PPLLTerminalEqualSupportRegression
