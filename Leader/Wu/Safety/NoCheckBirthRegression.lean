import Leader.Wu.Safety.NoCheckBirthRepair
import Leader.Wu.Protocol.CombinedLocalRepairRegression

/-!
# Hostile matrix for the source-shaped no-CHECK-birth repair

Removing CHECK's output writer must eliminate all four comparison/CHECK
counterexamples without disabling P'_ψ's barrier/probe recovery writer.  The
prepared-write and source-self repairs remain composed unchanged.
-/

namespace PPLLNoCheckBirthRegression

open PPLL PPLLCounterexample PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRegression PPLLCombinedLocalRepairRegression
  PPLLNoCheckBirthRepair

/-! ## Comparison/CHECK negative controls -/

/-- T1 after one no-CHECK-birth interaction. -/
def noCheckT1After : Fin 4 → ExpiringAgentState 2 10 0 :=
  localStep ring4 (noCheckBirthPathStallTransition (by omega) 10 0)
    cleanupT1Config 2

/-- T1 can no longer create the remote second leader. -/
theorem no_check_birth_blocks_t1 :
    (noCheckT1After 0).core.core.leader = true ∧
      (noCheckT1After 2).core.core.leader = false ∧
      (noCheckT1After 3).core.core.leader = false := by
  decide

/-- T8 under the no-CHECK-birth stack. -/
def noCheckT8After : Fin 4 → ExpiringAgentState 2 10 0 :=
  localStep ring4 (noCheckBirthPathStallTransition (by omega) 10 0)
    combinedT8Config 2

/-- Prepared write gating continues to block T8. -/
theorem no_check_birth_preserves_t8_gate :
    (noCheckT8After 3).core.core.bit = false := by
  decide

/-- Two source-self interactions under the no-CHECK-birth stack. -/
def noCheckSelfSourceAfter : Fin 4 → ExpiringAgentState 2 10 0 :=
  runLocalSchedule ring4
    (noCheckBirthPathStallTransition (by omega) 10 0)
    cleanupSelfSourceConfig [2, 2]

/-- T9 remains leader-safe and its zero-budget source carrier is removed. -/
theorem no_check_birth_preserves_t9 :
    (noCheckSelfSourceAfter 0).core.core.leader = true ∧
      (noCheckSelfSourceAfter 2).core.core.leader = false ∧
      (noCheckSelfSourceAfter 3).core.core.leader = false ∧
      (noCheckSelfSourceAfter 2).core.core.path = .bot ∧
      (noCheckSelfSourceAfter 3).core.core.path = .bot := by
  decide

/-- T20 pathless equality under no-CHECK-birth semantics. -/
def noCheckT20Pair : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  noCheckBirthAuthorizedTransition (by omega) 10
    ⟨PPLLTerminalEqualSupportRegression.pathlessEqualLeft, false⟩
    ⟨PPLLTerminalEqualSupportRegression.pathlessEqualRight, false⟩

/-- T20 remains blocked independently by support sanitation and by the removed
CHECK writer. -/
theorem no_check_birth_blocks_t20 :
    noCheckT20Pair.1.core.leader = false ∧
      noCheckT20Pair.2.core.leader = false := by
  decide

/-! ## P'_ψ remains a leader-creation writer -/

/-- Follower initiator and probed follower responder on a label barrier. -/
def barrierBirthLeft : AuthorizedAgentState 2 :=
  ⟨PPLLCounterexample.state2 0 false, false⟩

def barrierBirthRight : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false with probe := true }, false⟩

/-- Full source-shaped transition on the barrier/probe birth pair. -/
def barrierBirthPair : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  noCheckBirthAuthorizedTransition (by omega) 10
    barrierBirthLeft barrierBirthRight

/-- Removing CHECK birth does not ban every follower-pair birth: P'_ψ still
creates a leader on its explicit barrier/probe event. -/
theorem no_check_birth_preserves_barrier_recovery_writer :
    barrierBirthLeft.core.leader = false ∧
      barrierBirthRight.core.leader = false ∧
      (barrierBirthPair.1.core.leader = true ∨
        barrierBirthPair.2.core.leader = true) := by
  decide

end PPLLNoCheckBirthRegression
