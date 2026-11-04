import Leader.Wu.WallSweep.Repair
import Leader.Wu.Safety.NoCheckBirthOutputLegitimacy

/-!
# Regressions for the source-backed wall sweep

The local deletion assignments must consume their named carriers while leaving
the verified divisible-ring CHECK-birth execution available.  These fixtures
exercise both requirements on the raw repaired transition.
-/

namespace PPLLWallSweepRegression

open PPLL PPLLWallSweepRepair PPLLNoCheckBirthOutputLegitimacy
  PPLLResearchFormulation

/-- A non-barrier probe immediately to the right of a leader. -/
def probeWallLeft : AgentState 2 :=
  { PPLLCounterexample.state2 0 with leader := true }

def probeWallRight : AgentState 2 :=
  { PPLLCounterexample.state2 1 with probe := true }

theorem probe_wall_consumes_without_copy :
    let q := pPsiLeaderProbeWall (by omega : 2 > 0)
      probeWallLeft probeWallRight
    q.1.probe = false ∧ q.2.probe = false ∧ q.1.leader = true := by
  decide

/-- Follower/follower barrier return remains the intended P'_psi birth. -/
def probeBirthLeft : AgentState 2 :=
  PPLLCounterexample.state2 0

def probeBirthRight : AgentState 2 :=
  { PPLLCounterexample.state2 0 with probe := true }

theorem probe_wall_preserves_barrier_birth :
    (pPsiLeaderProbeWall (by omega : 2 > 0)
      probeBirthLeft probeBirthRight).2.leader = true := by
  decide

/-- A reset token crossing onto a maximally populated comparison carrier. -/
def resetWallLeft : AgentState 2 :=
  { PPLLCounterexample.state2 0 with reset_cmd := true }

def resetWallRight : AgentState 2 :=
  { PPLLCounterexample.state2 1 with
    state := .compare1
    path := .some 1 1
    path2 := some ⟨1, 1, 1, 2⟩
    path4 := some (1, 1)
    path5 := some (0, 1)
    p := true
    p_carry := true }

theorem reset_wall_clears_complete_comparison_carrier :
    let q := suppressSigResetKill (by omega : 2 > 0)
      resetWallLeft resetWallRight
    q.2.state = .none ∧ q.2.path = .bot ∧ q.2.path2 = none ∧
      q.2.path4 = none ∧ q.2.path5 = none ∧
      q.2.p = false ∧ q.2.p_carry = false := by
  decide

/-- Deletion occurs before Algorithm 14's echo/reset cancellation. -/
theorem reset_wall_echo_collision_still_clears :
    let q := suppressSigResetKill (by omega : 2 > 0)
      resetWallLeft { resetWallRight with echo := true }
    q.2.state = .none ∧ q.2.path = .bot ∧ q.2.path2 = none ∧
      q.2.p_carry = false ∧ q.2.reset_cmd = false ∧ q.2.echo = false := by
  decide

/-- The comparison carrier on the incoming side of a leader boundary. -/
def leaderWallLeft : AgentState 2 :=
  { resetWallRight with leader := false }

def leaderWallRight : AgentState 2 :=
  { PPLLCounterexample.state2 0 with leader := true }

theorem leader_wall_clears_incoming_and_resident_carriers :
    let q := sigMoveLeaderWall (by omega : 2 > 0) leaderWallLeft
      { leaderWallRight with state := .equal, path := .some 0 0 }
    q.1.state = .none ∧ q.1.path = .bot ∧ q.1.path2 = none ∧
      q.2.state = .none ∧ q.2.path = .bot ∧ q.2.leader = true := by
  decide

/-! ## Exact Algorithm-10 timing cuts -/

/-- An action-5 control that would reach the terminal leader and propagate
`.depart` if it were interpreted before the wall. -/
def leaderControlLeakLeft : AgentState 2 :=
  { PPLLCounterexample.state2 0 with
    state := .CHECK_ready
    path2 := some ⟨0, 0, 0, 5⟩ }

def leaderControlLeakRight : AgentState 2 :=
  { PPLLCounterexample.state2 1 with leader := true }

/-- Audit snapshot of the superseded late-wall staging, immediately after its
full literal SIGMOVE and before its final erasure. -/
def leaderControlLeakLateSnapshot : AgentState 2 × AgentState 2 :=
  let q0 := sigMoveLeaderPreclear (by omega : 2 > 0)
    leaderControlLeakLeft leaderControlLeakRight
  sigMove (by omega) q0.1 q0.2

def leaderControlLeakBeforeControl : AgentState 2 × AgentState 2 :=
  sigMoveLeaderBeforeControl (by omega)
    leaderControlLeakLeft leaderControlLeakRight

def leaderControlLeakCorrected : AgentState 2 × AgentState 2 :=
  sigMoveLeaderWall (by omega) leaderControlLeakLeft leaderControlLeakRight

/-- The old late staging executes action 5 and cross-endpoint departure.  The
repaired boundary has already erased the arrived command before control, and
the final corrected SIGMOVE therefore stays neutral. -/
theorem leader_wall_action5_is_killed_before_control :
    leaderControlLeakLateSnapshot.1.state = .depart ∧
      leaderControlLeakLateSnapshot.2.state = .depart ∧
      leaderControlLeakLateSnapshot.2.path2 = some ⟨0, 0, 0, 5⟩ ∧
      leaderControlLeakBeforeControl.1.state = .none ∧
      leaderControlLeakBeforeControl.2.state = .none ∧
      leaderControlLeakBeforeControl.2.path2 = none ∧
      leaderControlLeakCorrected.1.state = .none ∧
      leaderControlLeakCorrected.2.state = .none := by
  decide

/-- A barrier immediately left of a leader triggers resident deletion before
the first transfer, rather than relying on the later right-leader clear. -/
def incompletePreclearLeft : AgentState 2 :=
  { resetWallRight with leader := false, label := ⟨0, by omega⟩ }

def incompletePreclearRight : AgentState 2 :=
  { PPLLCounterexample.state2 0 with leader := true }

theorem incomplete_left_wall_clears_before_transfer :
    ComparisonNeutral
      (sigMoveLeaderPreclear (by omega : 2 > 0)
        incompletePreclearLeft incompletePreclearRight).1 := by
  apply sigMoveLeaderPreclear_incomplete_left
  decide

/-! ## Positive divisible-ring CHECK birth -/

private abbrev wallTwoGroupRing : DirectedRing 4 := ⟨by omega⟩

def wallTwoGroupTrap : Fin 4 → AgentState 2 :=
  trapCore (n := 4) (by omega)

def wallTwoGroupAfter : Fin 4 → AgentState 2 :=
  runLocalSchedule wallTwoGroupRing
    (wallSweepTransition (by omega) 0) wallTwoGroupTrap
    [0, 1, 0, 2, 1, 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The new deletion walls are inert on the leaderless genuine-comparison
prefix, so the source-backed raw transition retains the six-edge CHECK birth. -/
theorem wallSweep_twoGroup_trap_escape :
    (wallTwoGroupAfter 0).leader = false ∧
      (wallTwoGroupAfter 1).leader = false ∧
      (wallTwoGroupAfter 2).leader = true ∧
      (wallTwoGroupAfter 3).leader = false := by
  decide

end PPLLWallSweepRegression
