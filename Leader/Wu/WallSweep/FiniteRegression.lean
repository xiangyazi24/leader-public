import Leader.Wu.WallSweep.FiniteIntegration
import Leader.Wu.WallSweep.PreCheckResetRepair
import Leader.Wu.Protocol.CombinedLocalRepairRegression
import Leader.Wu.Safety.NoCheckBirthOutputLegitimacy

/-!
# Finite hostile matrix for the wall-sweep transition

These executable traces replay the established T1/T8/T9/T19/T20 fixtures and
the exact divisible-ring CHECK-birth schedule on the integrated wall carrier.
-/

namespace PPLLWallSweepFiniteRegression

open PPLL PPLLCounterexample PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLLeaderCreationCleanupRegression
  PPLLTerminalEqualSupportRepair PPLLTerminalEqualSupportRegression
  PPLLWriteIncrementGateRegression PPLLCombinedLocalRepairRegression
  PPLLNoCheckBirthOutputLegitimacy PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLWallSweepRepair

/-! ## T1 remains the provenance negative control -/

def wallT1After : Fin 4 → ExpiringAgentState 2 10 0 :=
  localStep ring4 (wallSweepPathStallTransition (by omega) 10 0)
    cleanupT1Config 2

/-- A remote existing leader is still invisible to T1's forged local carrier;
the wall sweep is an entry mechanism, not an immediate pair-local guard. -/
theorem wall_t1_remains_provenance_obstruction :
    (wallT1After 0).core.core.leader = true ∧
      (wallT1After 2).core.core.leader = true := by
  decide

/-! ## T8/T9/T19/T20 composition matrix -/

def wallT8After : Fin 4 → ExpiringAgentState 2 10 0 :=
  localStep ring4 (wallSweepPathStallTransition (by omega) 10 0)
    combinedT8Config 2

theorem wall_t8_blocks_orphan_increment :
    (wallT8After 3).core.core.bit = false := by
  decide

def wallSelfSourceAfterOne : Fin 4 → ExpiringAgentState 2 10 0 :=
  localStep ring4 (wallSweepPathStallTransition (by omega) 10 0)
    cleanupSelfSourceConfig 2

def wallSelfSourceAfterTwo : Fin 4 → ExpiringAgentState 2 10 0 :=
  localStep ring4 (wallSweepPathStallTransition (by omega) 10 0)
    wallSelfSourceAfterOne 2

theorem wall_t9_preserves_source_self_repair :
    (wallSelfSourceAfterOne 0).core.core.leader = true ∧
      (wallSelfSourceAfterTwo 2).core.core.leader = false ∧
      (wallSelfSourceAfterTwo 3).core.core.leader = false ∧
      (wallSelfSourceAfterTwo 2).core.core.path = .bot ∧
      (wallSelfSourceAfterTwo 3).core.core.path = .bot := by
  decide

def wallRecoveryAfter : Fin 4 → ExpiringAgentState 2 0 0 :=
  runLocalSchedule recoveryRing
    (wallSweepPathStallTransition (by omega) 0 0)
    recoveryConfig [1, 0, 3, 0]

def wallOldBadFuture : Fin 4 → ExpiringAgentState 2 0 0 :=
  runLocalSchedule recoveryRing
    (wallSweepPathStallTransition (by omega) 0 0)
    wallRecoveryAfter [1, 0, 2, 1, 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem wall_t19_recovery_marks_and_replay_preserves_outputs :
    (wallRecoveryAfter 0).core.core.leader = true ∧
      (wallRecoveryAfter 0).core.core.state = .eliminate_signal ∧
      (wallRecoveryAfter 1).core.core.state = .eliminate_signal ∧
      (wallOldBadFuture 0).core.core.leader = true ∧
      (wallOldBadFuture 1).core.core.leader = false ∧
      (wallOldBadFuture 2).core.core.leader = false ∧
      (wallOldBadFuture 3).core.core.leader = false := by
  decide

def wallT20Pair : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  wallSweepAuthorizedTransition (by omega) 10
    ⟨pathlessEqualLeft, false⟩ ⟨pathlessEqualRight, false⟩

theorem wall_t20_blocks_pathless_terminal_equal :
    wallT20Pair.1.core.leader = false ∧
      wallT20Pair.2.core.leader = false := by
  decide

/-! ## Exact divisible-ring CHECK birth -/

private abbrev wallTwoGroupRing : DirectedRing 4 := ⟨by omega⟩

def wallTwoGroupTrapAfter : Fin 4 → ExpiringAgentState 2 0 6 :=
  runLocalSchedule wallTwoGroupRing
    (wallSweepPathStallTransition (by omega) 0 6)
    twoGroupTrap twoGroupTrapEscapeSchedule

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The same six edges escape the divisible leaderless trap and leave exactly
one leader at position two. -/
theorem wallSweep_trap_escape :
    (wallTwoGroupTrapAfter 0).core.core.leader = false ∧
      (wallTwoGroupTrapAfter 1).core.core.leader = false ∧
      (wallTwoGroupTrapAfter 2).core.core.leader = true ∧
      (wallTwoGroupTrapAfter 3).core.core.leader = false := by
  decide

def wallTwoGroupBeforeFinal : Fin 4 → ExpiringAgentState 2 0 6 :=
  runLocalSchedule wallTwoGroupRing
    (wallSweepPathStallTransition (by omega) 0 6)
    twoGroupTrap [0, 1, 0, 2, 1]

private def wallTwoGroupFinalInput :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  ((wallTwoGroupBeforeFinal 2).core.erase,
    (wallTwoGroupBeforeFinal 3).core.erase)

private def wallTwoGroupFinalBeforeCheck :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let q := wallSweepAuthorizedBeforeCheck (by omega) 0
    wallTwoGroupFinalInput.1 wallTwoGroupFinalInput.2
  sanitizeAuthorizedPair (by omega) q

private def wallTwoGroupFinalAfterCheck :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedCheckSig (by omega)
    wallTwoGroupFinalBeforeCheck.1 wallTwoGroupFinalBeforeCheck.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The unique leader in the endpoint trace is born in unchanged CHECK, after
the leader wall and before the T19/write suffix. -/
theorem wallSweep_birth_occurs_at_check :
    wallTwoGroupFinalBeforeCheck.1.core.leader = false ∧
      wallTwoGroupFinalBeforeCheck.2.core.leader = false ∧
      wallTwoGroupFinalBeforeCheck.1.core.state = .CHECK_ready ∧
      wallTwoGroupFinalBeforeCheck.2.core.state = .CHECK_ready ∧
      wallTwoGroupFinalAfterCheck.1.core.state = .equal ∧
      wallTwoGroupFinalAfterCheck.2.core.state = .equal ∧
      wallTwoGroupFinalAfterCheck.1.core.leader = false ∧
      wallTwoGroupFinalAfterCheck.2.core.leader = true ∧
      (wallSweepAuthorizedTransition (by omega) 0
        wallTwoGroupFinalInput.1 wallTwoGroupFinalInput.2).1.core.leader = true ∧
      (wallSweepAuthorizedTransition (by omega) 0
        wallTwoGroupFinalInput.1 wallTwoGroupFinalInput.2).2.core.leader = false := by
  decide

/-! ## Reset/CHECK ordering witness -/

/-- The same final comparison input, but with an already-present reset command
at the initiator.  Algorithm 1 schedules CHECK before SUPPRESS_SIG, so the
current wall repair does not inspect this token before the birth boundary. -/
private def wallTwoGroupResetFinalInput :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  (⟨{ wallTwoGroupFinalInput.1.core with reset_cmd := true },
      wallTwoGroupFinalInput.1.path0Crossed⟩,
    wallTwoGroupFinalInput.2)

private def wallTwoGroupResetFinalBeforeCheck :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let q := wallSweepAuthorizedBeforeCheck (by omega) 0
    wallTwoGroupResetFinalInput.1 wallTwoGroupResetFinalInput.2
  sanitizeAuthorizedPair (by omega) q

private def wallTwoGroupResetFinalAfterCheck :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedCheckSig (by omega)
    wallTwoGroupResetFinalBeforeCheck.1 wallTwoGroupResetFinalBeforeCheck.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- **Sequential ordering witness.**  An initiator reset token is present, yet
the unchanged pre-CHECK prefix still reaches two CHECK-ready components and
CHECK creates the responder leader.  Thus the prose reset wall cannot justify
same-interaction no-birth under Algorithm 1's printed order without an earlier
deletion boundary. -/
theorem wallSweep_existing_reset_does_not_preempt_check_birth :
    wallTwoGroupResetFinalInput.1.core.reset_cmd = true ∧
      wallTwoGroupResetFinalBeforeCheck.1.core.state = .CHECK_ready ∧
      wallTwoGroupResetFinalBeforeCheck.2.core.state = .CHECK_ready ∧
      wallTwoGroupResetFinalBeforeCheck.1.core.leader = false ∧
      wallTwoGroupResetFinalBeforeCheck.2.core.leader = false ∧
      wallTwoGroupResetFinalAfterCheck.2.core.leader = true := by
  decide

private def wallTwoGroupResetRepairedAfter :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  wallSweepPreCheckResetAuthorizedTransition (by omega) 0
    wallTwoGroupResetFinalInput.1 wallTwoGroupResetFinalInput.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The pre-CHECK deletion repair makes the existing reset effective in the
same interaction: both endpoints remain followers. -/
theorem preCheckResetWall_blocks_reset_covered_birth :
    wallTwoGroupResetRepairedAfter.1.core.leader = false ∧
      wallTwoGroupResetRepairedAfter.2.core.leader = false ∧
      ComparisonNeutral wallTwoGroupResetRepairedAfter.1.core ∧
      ComparisonNeutral wallTwoGroupResetRepairedAfter.2.core := by
  unfold ComparisonNeutral
  decide

private def wallTwoGroupNoResetRepairedAfter :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  wallSweepPreCheckResetAuthorizedTransition (by omega) 0
    wallTwoGroupFinalInput.1 wallTwoGroupFinalInput.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- With no leader/reset at the boundary, the repair retains the required
divisible-regime CHECK birth and its label-zero migration. -/
theorem preCheckResetWall_preserves_uncovered_check_birth :
    wallTwoGroupNoResetRepairedAfter.1.core.leader = true ∧
      wallTwoGroupNoResetRepairedAfter.2.core.leader = false ∧
      wallTwoGroupNoResetRepairedAfter.1.core.label = (0 : Fin 2) := by
  decide

end PPLLWallSweepFiniteRegression
