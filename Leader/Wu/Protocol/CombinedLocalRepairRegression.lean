import Leader.Wu.Protocol.CombinedLocalRepair
import Leader.Wu.Comparison.LeaderCreationCleanupRegression
import Leader.Wu.Comparison.TerminalEqualSupportRegression
import Leader.Wu.WriteSeq.IncrementGateRegression

/-!
# Hostile matrix for the combined local repair stack

These executable checks pin the intended composition order.  The stack blocks
T8, preserves the T9 source-self repair, retains T19 source retirement, and
blocks T20 before CHECK.  T1 deliberately remains live: local support and
post-birth cleanup cannot protect an arbitrary remote leader before the output
violation occurs.
-/

namespace PPLLCombinedLocalRepairRegression

open PPLL PPLLCounterexample PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLLeaderCreationCleanupRegression
  PPLLTerminalEqualSupportRegression PPLLWriteIncrementGateRegression
  PPLLCombinedLocalRepair

/-! ## T1 remains the global negative control -/

/-- One combined interaction on the existing finite T1 fixture. -/
def combinedT1After : Fin 4 → ExpiringAgentState 2 10 0 :=
  localStep ring4 (combinedLocalPathStallTransition (by omega) 10 0)
    cleanupT1Config 2

/-- The combined stack still creates a second leader from T1 before birth
cleanup can retire the carrier. -/
theorem combined_t1_still_creates_second_leader :
    (combinedT1After 0).core.core.leader = true ∧
      (combinedT1After 2).core.core.leader = true := by
  decide

private def combinedT1LeaderTest
    (C : Fin 4 → ExpiringAgentState 2 10 0) : Bool :=
  (C 2).core.core.leader

/-- T1 remains exactly one bad edge among the four one-step scheduler
outcomes for the combined finite transition. -/
theorem combined_t1_bad_schedule_count :
    PPLLTraceConvergence.localHitCount ring4
      (combinedLocalPathStallTransition (by omega) 10 0)
      combinedT1LeaderTest cleanupT1Config 1 = 1 := by
  decide

/-- The surviving combined T1 event has exact probability `1/4`. -/
theorem combined_t1_bad_event_probability :
    PPLLTraceConvergence.localHitProbability ring4
      (combinedLocalPathStallTransition (by omega) 10 0)
      combinedT1LeaderTest cleanupT1Config 1 = (1 : Rat) / 4 := by
  unfold PPLLTraceConvergence.localHitProbability
  rw [combined_t1_bad_schedule_count, allSchedules_length]
  rfl

/-- The combined T1 start is not Definition-1 safe because its reachable edge
changes position two from follower to leader. -/
theorem combined_t1_not_semantically_safe :
    ¬PopulationProtocol.IsSafe
      (combinedLocalProtocol (by omega) 10 0) ring4
      cleanupT1Config isLeaderOutput := by
  intro hsafe
  have hreach : PopulationProtocol.Reachable
      (combinedLocalProtocol (by omega) 10 0) ring4
      cleanupT1Config combinedT1After :=
    PopulationProtocol.OneStep.to_reachable ⟨2, rfl⟩
  have hout := hsafe.2 combinedT1After hreach 2
  have hbefore : (cleanupT1Config 2).core.core.leader = false := by decide
  have hafter : (combinedT1After 2).core.core.leader = true := by decide
  change (if (combinedT1After 2).core.core.leader then LeaderOutput.leader
      else LeaderOutput.follower) =
    (if (cleanupT1Config 2).core.core.leader then LeaderOutput.leader
      else LeaderOutput.follower) at hout
  rw [hbefore, hafter] at hout
  contradiction

/-! ## T8 prepared-write gate -/

/-- Reify the finite T8 cores into the unchanged authorization-plus-stall
carrier used by the combined stack. -/
def combinedT8Config : Fin 4 → ExpiringAgentState 2 10 0 := fun i =>
  ⟨⟨finiteT8WriteConfig i, false⟩, freshStall 0⟩

/-- One combined interaction on T8's orphan increment edge. -/
def combinedT8After : Fin 4 → ExpiringAgentState 2 10 0 :=
  localStep ring4 (combinedLocalPathStallTransition (by omega) 10 0)
    combinedT8Config 2

/-- The prepared gate blocks T8 inside the combined pipeline. -/
theorem combined_t8_blocks_orphan_increment :
    (combinedT8After 3).core.core.bit = false := by
  decide

/-! ## T9 source-self authorization -/

/-- First combined interaction on the generated source-self fixture. -/
def combinedSelfSourceAfterOne : Fin 4 → ExpiringAgentState 2 10 0 :=
  localStep ring4 (combinedLocalPathStallTransition (by omega) 10 0)
    cleanupSelfSourceConfig 2

/-- Second same-edge interaction. -/
def combinedSelfSourceAfterTwo : Fin 4 → ExpiringAgentState 2 10 0 :=
  localStep ring4 (combinedLocalPathStallTransition (by omega) 10 0)
    combinedSelfSourceAfterOne 2

/-- Source-aligned comparison material remains unable to create another
leader, and zero-budget path-stall removes both components. -/
theorem combined_t9_preserves_source_self_repair :
    (combinedSelfSourceAfterOne 0).core.core.leader = true ∧
      (combinedSelfSourceAfterTwo 2).core.core.leader = false ∧
      (combinedSelfSourceAfterTwo 3).core.core.leader = false ∧
      (combinedSelfSourceAfterTwo 2).core.core.path = .bot ∧
      (combinedSelfSourceAfterTwo 3).core.core.path = .bot := by
  decide

/-! ## T19 source-zero retirement -/

/-- Recovery schedule under the complete combined stack. -/
def combinedRecoveryAfter : Fin 4 → ExpiringAgentState 2 0 0 :=
  runLocalSchedule recoveryRing
    (combinedLocalPathStallTransition (by omega) 0 0)
    recoveryConfig [1, 0, 3, 0]

/-- Replay the old five-edge T19 continuation under the combined stack. -/
def combinedOldBadFuture : Fin 4 → ExpiringAgentState 2 0 0 :=
  runLocalSchedule recoveryRing
    (combinedLocalPathStallTransition (by omega) 0 0)
    combinedRecoveryAfter [1, 0, 2, 1, 2]

/-- The recovery event still creates one leader and marks its residual source;
the formerly bad continuation preserves the unique output. -/
theorem combined_t19_recovery_marks_and_replay_preserves_outputs :
    (combinedRecoveryAfter 0).core.core.leader = true ∧
      (combinedRecoveryAfter 0).core.core.state = .eliminate_signal ∧
      (combinedRecoveryAfter 1).core.core.state = .eliminate_signal ∧
      (combinedOldBadFuture 0).core.core.leader = true ∧
      (combinedOldBadFuture 1).core.core.leader = false ∧
      (combinedOldBadFuture 2).core.core.leader = false ∧
      (combinedOldBadFuture 3).core.core.leader = false := by
  decide

/-! ## T20 terminal equality support -/

/-- Combined audit result on the pathless terminal-equality pair. -/
def combinedT20Pair : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  combinedLocalAuthorizedTransition (by omega) 10
    ⟨pathlessEqualLeft, false⟩ ⟨pathlessEqualRight, false⟩

/-- The terminal support sanitizer blocks pathless equality before CHECK inside
the combined transition. -/
theorem combined_t20_blocks_pathless_terminal_equal :
    combinedT20Pair.1.core.leader = false ∧
      combinedT20Pair.2.core.leader = false := by
  decide

end PPLLCombinedLocalRepairRegression
