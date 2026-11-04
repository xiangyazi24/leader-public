import Leader.Wu.Comparison.LeaderCreationCleanupRepair
import Leader.Wu.Protocol.RepairRegression
import Leader.Wu.Comparison.HostAlignedRepairCounterexample

/-!
# Hostile regressions for leader-source comparison cleanup

The priority-deletion repair solves the exact T19 replay only after a local
leader birth.  Self-stabilization, however, permits a complete armed
carrier elsewhere in the initial configuration.  This file records both sides
of that distinction: the finite repair still suffers T1's first output-changing
edge, while it preserves the existing T9 cleanup, breaks both seven-state
leaderless classes through path-stall expiration, and leaves a genuine
comparison alive when supplied the proved ψ=2 timer budget.
-/

namespace PPLLLeaderCreationCleanupRegression

open PPLL PPLLCounterexample PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLAuthorizedRepairCounterexample
  PPLLHostAlignedRepairCounterexample PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLTraceConvergence

/-- Reify an audit state into the zero-budget cleanup carrier without changing
its physical core or authorization bit. -/
private def reifyZero {ψ κ : Nat} (u : AuthorizedAgentState ψ)
    (hu : u.core.inProtocolDomain κ) : ExpiringAgentState ψ κ 0 :=
  ⟨⟨BoundedAgentState.ofDomain u.core hu, u.path0Crossed⟩, 0⟩

/-- Reify an audit state with the six-opportunity budget used by the checked
ψ=2 comparison lifecycle. -/
private def reifySix {ψ κ : Nat} (u : AuthorizedAgentState ψ)
    (hu : u.core.inProtocolDomain κ) : ExpiringAgentState ψ κ 6 :=
  ⟨⟨BoundedAgentState.ofDomain u.core hu, u.path0Crossed⟩, freshStall 6⟩

/-! ## Negative control: remote T1 material is already armed -/

/-- T1's source configuration lies in the finite κ=10 cleanup carrier.  All
new authorization values start false; CHECK does not consult them. -/
def cleanupT1Config : Fin 4 → ExpiringAgentState 2 10 0 := fun i =>
  reifyZero ⟨counterConfig i, false⟩ (counterConfig_inProtocolDomain i)

/-- Select the remote complete carrier at positions two and three. -/
def cleanupT1After : Fin 4 → ExpiringAgentState 2 10 0 :=
  PopulationProtocol.step
    (leaderCleanupPathStallProtocol (by omega) 10 0)
    ring4 cleanupT1Config 2

/-- Post-birth deletion acts after T1's output violation: the old leader at
zero and new leader at two coexist while both local carrier components enter
the protected deletion phase. -/
theorem cleanup_t1_still_creates_second_leader :
    (cleanupT1After 0).core.core.leader = true ∧
      (cleanupT1After 2).core.core.leader = true ∧
      (cleanupT1After 3).core.core.leader = false ∧
      (cleanupT1After 2).core.core.path = .some 0 0 ∧
      (cleanupT1After 2).core.core.state = .eliminate_signal ∧
      (cleanupT1After 3).core.core.path = .some 1 0 ∧
      (cleanupT1After 3).core.core.state = .eliminate_signal := by
  decide

/-- Boolean test for T1's remote second leader. -/
private def cleanupT1LeaderTest
    (C : Fin 4 → ExpiringAgentState 2 10 0) : Bool :=
  (C 2).core.core.leader

/-- Exactly one of the four one-edge schedules selects T1's armed carrier. -/
theorem cleanup_t1_bad_schedule_count :
    localHitCount ring4
      (leaderCleanupPathStallTransition (by omega) 10 0)
      cleanupT1LeaderTest cleanupT1Config 1 = 1 := by
  decide

/-- The remote-carrier output violation retains exact probability `1/4` under
one uniform interaction.  This is a scoped counterexample to immediate safety,
not to eventual self-stabilization. -/
theorem cleanup_t1_bad_event_probability :
    localHitProbability ring4
      (leaderCleanupPathStallTransition (by omega) 10 0)
      cleanupT1LeaderTest cleanupT1Config 1 = (1 : Rat) / 4 := by
  unfold localHitProbability
  rw [cleanup_t1_bad_schedule_count, allSchedules_length]
  rfl

/-- The finite cleanup candidate does not classify the arbitrary T1 input as
Definition-1 safe: its one-step future changes position two's output. -/
theorem cleanup_t1_not_semantically_safe :
    ¬PopulationProtocol.IsSafe
      (leaderCleanupPathStallProtocol (by omega) 10 0)
      ring4 cleanupT1Config isLeaderOutput := by
  intro hsafe
  have hreach : PopulationProtocol.Reachable
      (leaderCleanupPathStallProtocol (by omega) 10 0)
      ring4 cleanupT1Config cleanupT1After :=
    PopulationProtocol.OneStep.to_reachable ⟨2, rfl⟩
  have hout := hsafe.2 cleanupT1After hreach 2
  have hafter : (cleanupT1After 2).core.core.leader = true := by decide
  have hbefore : (cleanupT1Config 2).core.core.leader = false := by decide
  change (if (cleanupT1After 2).core.core.leader then LeaderOutput.leader
      else LeaderOutput.follower) =
    (if (cleanupT1Config 2).core.core.leader then LeaderOutput.leader
      else LeaderOutput.follower) at hout
  simp [hafter, hbefore] at hout

/-! ## Deletion-priority timer composition -/

private def cleanupDeleteLeft : AuthorizedAgentState 2 :=
  ⟨{ state2 0 false .depart with path := .some 0 0 }, false⟩

private def cleanupDeleteRight : AuthorizedAgentState 2 :=
  ⟨{ state2 1 false .eliminate_signal with path := .some 1 0 }, false⟩

private def cleanupDeleteTerminalPredecessor : AuthorizedAgentState 2 :=
  ⟨state2 1, false⟩

private theorem cleanupDeleteDomain :
    cleanupDeleteLeft.core.inProtocolDomain 0 ∧
      cleanupDeleteRight.core.inProtocolDomain 0 ∧
      cleanupDeleteTerminalPredecessor.core.inProtocolDomain 0 := by
  simp [cleanupDeleteLeft, cleanupDeleteRight,
    cleanupDeleteTerminalPredecessor, AgentState.inProtocolDomain, state2]

private def cleanupDeleteLeftFinite : ExpiringAgentState 2 0 0 :=
  reifyZero cleanupDeleteLeft cleanupDeleteDomain.1

private def cleanupDeleteRightFinite : ExpiringAgentState 2 0 0 :=
  reifyZero cleanupDeleteRight cleanupDeleteDomain.2.1

private def cleanupDeleteTerminalFinite : ExpiringAgentState 2 0 0 :=
  reifyZero cleanupDeleteTerminalPredecessor cleanupDeleteDomain.2.2

private def cleanupDeleteAfterPropagation :=
  leaderCleanupPathStallTransition (by omega : 2 > 0) 0 0
    cleanupDeleteLeftFinite cleanupDeleteRightFinite

private def cleanupDeleteAfterTerminal :=
  leaderCleanupPathStallTransition (by omega : 2 > 0) 0 0
    cleanupDeleteTerminalFinite cleanupDeleteAfterPropagation.1

/-- A newly propagated deletion marker survives even zero path-stall budget,
then a terminal predecessor interaction clears that final source component. -/
theorem cleanup_deletion_priority_survives_timer_and_terminates :
    cleanupDeleteAfterPropagation.1.core.core.state = .eliminate_signal ∧
      cleanupDeleteAfterPropagation.1.core.core.path = .some 0 0 ∧
      cleanupDeleteAfterPropagation.2.core.core.state = .none ∧
      cleanupDeleteAfterPropagation.2.core.core.path = .bot ∧
      cleanupDeleteAfterTerminal.2.core.core.state = .none ∧
      cleanupDeleteAfterTerminal.2.core.core.path = .bot := by
  decide

/-! ## Existing source-self and leaderless-trap regressions -/

/-- The generated T9 starting configuration lies in the bounded domain. -/
private theorem selfSourceConfig_inProtocolDomain (i : Fin 4) :
    (selfSourceConfig i).inProtocolDomain 10 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · simp [selfSourceConfig, AgentState.inProtocolDomain, a0, state2]
  · simp [selfSourceConfig, AgentState.inProtocolDomain, a1, state2]
  · change ({ state2 0 with wait := false } : AgentState 2).inProtocolDomain 10
    simp [AgentState.inProtocolDomain, state2]
  · change (state2 1).inProtocolDomain 10
    simp [AgentState.inProtocolDomain, state2]

/-- Finite form of T9 with initially empty authorization metadata. -/
def cleanupSelfSourceConfig : Fin 4 → ExpiringAgentState 2 10 0 := fun i =>
  reifyZero ⟨selfSourceConfig i, false⟩
    (selfSourceConfig_inProtocolDomain i)

/-- First interaction generates the complete source carrier. -/
def cleanupSelfSourceAfterOne : Fin 4 → ExpiringAgentState 2 10 0 :=
  PopulationProtocol.step
    (leaderCleanupPathStallProtocol (by omega) 10 0)
    ring4 cleanupSelfSourceConfig 2

/-- The second source interaction spends the zero-budget static opportunity. -/
def cleanupSelfSourceAfterTwo : Fin 4 → ExpiringAgentState 2 10 0 :=
  PopulationProtocol.step
    (leaderCleanupPathStallProtocol (by omega) 10 0)
    ring4 cleanupSelfSourceAfterOne 2

/-- The old T9 two-interaction witness creates no second leader.  Its departing
carrier is physically absent after the second static interaction. -/
theorem cleanup_preserves_t9_regression :
    (cleanupSelfSourceAfterTwo 0).core.core.leader = true ∧
      (cleanupSelfSourceAfterTwo 2).core.core.leader = false ∧
      (cleanupSelfSourceAfterTwo 3).core.core.leader = false ∧
      (cleanupSelfSourceAfterTwo 2).core.core.path = .bot ∧
      (cleanupSelfSourceAfterTwo 3).core.core.path = .bot := by
  decide

private theorem authorizedTrapPairDomain :
    trapInitial.1.core.inProtocolDomain 0 ∧
      trapInitial.2.core.inProtocolDomain 0 :=
  trap_inProtocolDomain trapInitial_mem

private def cleanupTrapLeft : ExpiringAgentState 2 0 0 :=
  reifyZero trapInitial.1 authorizedTrapPairDomain.1

private def cleanupTrapRight : ExpiringAgentState 2 0 0 :=
  reifyZero trapInitial.2 authorizedTrapPairDomain.2

/-- Zero-budget path-stall still destroys the original forged-authorization
seven-state class in one interaction. -/
theorem cleanup_breaks_authorized_trap :
    let q := leaderCleanupPathStallTransition (by omega : 2 > 0) 0 0
      cleanupTrapLeft cleanupTrapRight
    q.1.core.core.path = .bot ∧ q.2.core.core.path = .bot ∧
      q.1.core.path0Crossed = false ∧ q.2.core.path0Crossed = false := by
  decide

private theorem hostTrapPairDomain :
    hostTrapState0.1.core.inProtocolDomain 0 ∧
      hostTrapState0.2.core.inProtocolDomain 0 := by
  simpa [hostTrapState0, clearPairAuthorization, clearAuthorization, trapState0]
    using authorizedTrapPairDomain

private def cleanupHostTrapLeft : ExpiringAgentState 2 0 0 :=
  reifyZero hostTrapState0.1 hostTrapPairDomain.1

private def cleanupHostTrapRight : ExpiringAgentState 2 0 0 :=
  reifyZero hostTrapState0.2 hostTrapPairDomain.2

/-- The same timer also destroys the host-aligned clean-marker class; endpoint
retirement is not being substituted for stale-carrier expiration. -/
theorem cleanup_breaks_host_aligned_trap :
    let q := leaderCleanupPathStallTransition (by omega : 2 > 0) 0 0
      cleanupHostTrapLeft cleanupHostTrapRight
    q.1.core.core.path = .bot ∧ q.2.core.core.path = .bot ∧
      q.1.core.path0Crossed = false ∧ q.2.core.path0Crossed = false := by
  decide

/-! ## Migration and positive-comparison regressions -/

/-- Follower initiator beside an existing nonzero-label leader.  WRITE_SEQ
moves that leader left without increasing the pair's leader count. -/
private def cleanupMigrationLeft : AuthorizedAgentState 2 :=
  ⟨{ state2 0 false .depart with path := .some 0 0 }, false⟩

private def cleanupMigrationRight : AuthorizedAgentState 2 :=
  ⟨{ state2 1 true .depart with path := .some 1 0 }, false⟩

private def cleanupMigrationBeforeCheck :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedBeforeCheck (by omega) 0
    cleanupMigrationLeft cleanupMigrationRight

private def cleanupMigrationAfterCheck :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedCheckSig (by omega)
    cleanupMigrationBeforeCheck.1 cleanupMigrationBeforeCheck.2

private def cleanupMigrationBase :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  ppllAuthorizedRepair (by omega) 0
    cleanupMigrationLeft cleanupMigrationRight

/-- The birth trigger excludes ordinary WRITE_SEQ migration: the leader moves
from right to left, but cleanup is exactly the base transition and neither
present path is marked for deletion. -/
theorem cleanup_does_not_mark_ordinary_leader_migration :
    cleanupMigrationBase.1.core.leader = true ∧
      cleanupMigrationBase.2.core.leader = false ∧
      leaderBirthBeforeOrAtCheck cleanupMigrationLeft cleanupMigrationRight
        cleanupMigrationBeforeCheck cleanupMigrationAfterCheck = false ∧
      leaderCleanupAuthorizedTransition (by omega) 0
        cleanupMigrationLeft cleanupMigrationRight = cleanupMigrationBase ∧
      cleanupMigrationBase.1.core.state = .depart ∧
      cleanupMigrationBase.2.core.state = .depart := by
  decide

/-- CHECK-ready carrier whose initiator is already the local leader.  Final
leader bits alone hide the responder birth because WRITE_SEQ merges it back. -/
private def cleanupMaskedBirthLeft : AuthorizedAgentState 2 :=
  ⟨{ a2 with leader := true }, false⟩

private def cleanupMaskedBirthRight : AuthorizedAgentState 2 :=
  ⟨a3, false⟩

private def cleanupMaskedBeforeCheck :=
  authorizedBeforeCheck (by omega : 2 > 0) 10
    cleanupMaskedBirthLeft cleanupMaskedBirthRight

private def cleanupMaskedAfterCheck :=
  authorizedCheckSig (by omega : 2 > 0)
    cleanupMaskedBeforeCheck.1 cleanupMaskedBeforeCheck.2

private def cleanupMaskedBase :=
  ppllAuthorizedRepair (by omega : 2 > 0) 10
    cleanupMaskedBirthLeft cleanupMaskedBirthRight

private def cleanupMaskedOut :=
  leaderCleanupAuthorizedTransition (by omega : 2 > 0) 10
    cleanupMaskedBirthLeft cleanupMaskedBirthRight

/-- The transition-local event sees a CHECK birth that final net leader bits
would miss.  Ordinary WRITE_SEQ merges the newborn into the existing initiator,
but both surviving path components are nevertheless placed in deletion. -/
theorem cleanup_detects_check_birth_masked_by_leader_merge :
    cleanupMaskedAfterCheck.2.core.leader = true ∧
      cleanupMaskedBase.1.core.leader = true ∧
      cleanupMaskedBase.2.core.leader = false ∧
      leaderBirthBeforeOrAtCheck cleanupMaskedBirthLeft cleanupMaskedBirthRight
        cleanupMaskedBeforeCheck cleanupMaskedAfterCheck = true ∧
      cleanupMaskedOut.1.core.state = .eliminate_signal ∧
      cleanupMaskedOut.2.core.state = .eliminate_signal := by
  decide

/-- Complete ψ=2 comparison with an already-earned stable-wrap permission. -/
private def cleanupProgressLeft : AuthorizedAgentState 2 :=
  ⟨{ state2 0 false .depart with path := .some 0 0 }, true⟩

private def cleanupProgressRight : AuthorizedAgentState 2 :=
  ⟨{ state2 1 false .depart with path := .some 1 0 }, false⟩

private theorem cleanupProgressDomain :
    cleanupProgressLeft.core.inProtocolDomain 0 ∧
      cleanupProgressRight.core.inProtocolDomain 0 := by
  simp [cleanupProgressLeft, cleanupProgressRight,
    AgentState.inProtocolDomain, state2]

private def cleanupProgressLeftFinite : ExpiringAgentState 2 0 6 :=
  reifySix cleanupProgressLeft cleanupProgressDomain.1

private def cleanupProgressRightFinite : ExpiringAgentState 2 0 6 :=
  reifySix cleanupProgressRight cleanupProgressDomain.2

/-- The first genuine authorized comparison step is unchanged by deletion.
Permission consumption refreshes the left timer, while the static right path
spends one of its six opportunities; both components remain physically live. -/
theorem cleanup_preserves_authorized_comparison_step :
    let q := leaderCleanupPathStallTransition (by omega : 2 > 0) 0 6
      cleanupProgressLeftFinite cleanupProgressRightFinite
    q.1.core.core.state = .congest ∧
      q.2.core.core.state = .congest ∧
      q.1.core.core.path ≠ .bot ∧ q.2.core.core.path ≠ .bot ∧
      q.1.stall.val = 6 ∧ q.2.stall.val = 5 := by
  decide

end PPLLLeaderCreationCleanupRegression
