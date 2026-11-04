import Leader.Wu.WallSweep.FiniteIntegration
import Leader.Wu.WallSweep.EchoDrain
import Leader.Wu.WallSweep.FiniteCleanup
import Leader.Wu.WallSweep.RestartableProtected
import Leader.Wu.Safety.Counterexamples
import Leader.Wu.WallSweep.FiniteRegression

/-!
# Full-transition cleanup regression

The arbitrary-echo theorem is proved for the isolated repaired Algorithm-14
kernel.  This fixture is the first positive guard for the next join: on a
stable, bullet-free, writer-idle phase frame, the same `2n-1` edge word also
clears arbitrary lottery residue under the complete finite wall transition and
preserves the designated leader.
-/

namespace PPLLWallSweepFullCleanupRegression

open PPLL PPLLCounterexample PPLLResearchFormulation
  PPLLExpiringComparisonRepair PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepEchoDrain PPLLWallSweepFiniteCleanup
  PPLLWallSweepFiniteRegression PPLLWallSweepNormalResetContract
  PPLLWallSweepRestartableProtected PPLLNoCheckBirthOutputLegitimacy

private abbrev cleanupRing : DirectedRing 4 := ⟨by omega⟩
private def cleanupLeader : Fin 4 := ⟨0, by omega⟩

/-- Stable modulo labels, one shielded label-zero leader, a mixed old echo/
reset assignment, and active lottery residue but no path/CHECK or writer carrier. -/
def fullCleanupBase (label : Fin 2) (oldEcho oldReset : Bool) : AgentState 2 :=
  let s := { state2 label with wait := true }
  let s := { s with p := true }
  let s := { s with p_carry := true }
  let s := { s with echo := oldEcho }
  { s with reset_cmd := oldReset }

def fullCleanupCore : Fin 4 → AgentState 2
  | ⟨0, _⟩ =>
      let s := { fullCleanupBase 0 true false with leader := true }
      { s with shield := true }
  | ⟨1, _⟩ => fullCleanupBase 1 false true
  | ⟨2, _⟩ => fullCleanupBase 0 true false
  | ⟨3, _⟩ => fullCleanupBase 1 true true

private theorem fullCleanupCore_domain (i : Fin 4) :
    (fullCleanupCore i).inProtocolDomain 10 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [fullCleanupCore, fullCleanupBase, AgentState.inProtocolDomain, state2]

def fullCleanupConfig : Fin 4 → ExpiringAgentState 2 10 8 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain (fullCleanupCore i)
      (fullCleanupCore_domain i), false⟩, freshStall 8⟩

def fullCleanupAfter : Fin 4 → ExpiringAgentState 2 10 8 :=
  runLocalSchedule cleanupRing
    (wallSweepPathStallTransition (by omega) 10 8)
    fullCleanupConfig
    (leaderDrainReseedResetSweep cleanupRing cleanupLeader)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The complete finite transition realizes the isolated cleanup word on this
nontrivial protected phase fixture. -/
theorem full_wall_cleanup_word_clears_lottery_residue :
    wallPriorityOpenAlongBool (by omega : 2 > 0) 10 8 cleanupRing
      fullCleanupConfig
      (leaderDrainReseedResetSweep cleanupRing cleanupLeader) = true ∧
    (∀ i,
      (fullCleanupAfter i).core.core.state = .none ∧
      (fullCleanupAfter i).core.core.path = .bot ∧
      (fullCleanupAfter i).core.core.path2 = none ∧
      (fullCleanupAfter i).core.core.p = false ∧
      (fullCleanupAfter i).core.core.p_carry = false) ∧
    (fullCleanupAfter 0).core.core.leader = true ∧
    (fullCleanupAfter 1).core.core.leader = false ∧
    (fullCleanupAfter 2).core.core.leader = false ∧
    (fullCleanupAfter 3).core.core.leader = false ∧
    (fullCleanupAfter 3).core.core.signal_ws = true := by
  decide

/-! ## T19 interrupt guard -/

/-- The same final predecessor edge used by the isolated T19 proof consumes
the residual deletion wave through the complete finite wall transition. -/
def wallAfterFinalDeletion : Fin 4 → ExpiringAgentState 2 0 0 :=
  runLocalSchedule recoveryRing
    (wallSweepPathStallTransition (by omega) 0 0)
    wallOldBadFuture [3]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem wall_t19_final_deletion_clears_paths :
    (wallAfterFinalDeletion 0).core.core.path = .bot ∧
    (wallAfterFinalDeletion 1).core.core.path = .bot ∧
    (wallAfterFinalDeletion 2).core.core.path = .bot ∧
    (wallAfterFinalDeletion 3).core.core.path = .bot := by
  decide

/-! ## Divisible-trap entry into the protected cleanup anchor -/

private theorem wallTwoPos : 2 > 0 := by omega

/-- The six-edge CHECK-birth trace is followed by two T19 deletion edges and
one clockwise absence-signal circuit.  The last edge fires the leader bullet
and establishes the shield required by protected cleanup. -/
def wallTwoGroupBirthDrainSchedule : DetSchedule 4 :=
  twoGroupTrapEscapeSchedule ++ [2, 1]

def wallTwoGroupAfterBirthDrain : Fin 4 → ExpiringAgentState 2 0 6 :=
  runLocalSchedule cleanupRing
    (wallSweepPathStallTransition wallTwoPos 0 6)
    twoGroupTrap wallTwoGroupBirthDrainSchedule

def wallTwoGroupProtectedAnchorSchedule : DetSchedule 4 :=
  wallTwoGroupBirthDrainSchedule ++ [2, 3, 0, 1, 2]

def wallTwoGroupProtectedAnchor : Fin 4 → ExpiringAgentState 2 0 6 :=
  runLocalSchedule cleanupRing
    (wallSweepPathStallTransition wallTwoPos 0 6)
    twoGroupTrap wallTwoGroupProtectedAnchorSchedule

private theorem wallSweepRun_reachable
    (C : Fin 4 → ExpiringAgentState 2 0 6) (s : DetSchedule 4) :
    PopulationProtocol.Reachable (wallSweepProtocol wallTwoPos 0 6)
      cleanupRing C
      (runLocalSchedule cleanupRing
        (wallSweepPathStallTransition wallTwoPos 0 6) C s) := by
  induction s generalizing C with
  | nil =>
      exact @PopulationProtocol.Reachable.refl 4
        (wallSweepProtocol wallTwoPos 0 6) cleanupRing C
  | cons e rest ih =>
      exact (PopulationProtocol.OneStep.to_reachable ⟨e, rfl⟩).trans
        (ih (localStep cleanupRing
          (wallSweepPathStallTransition wallTwoPos 0 6) C e))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The two edges after CHECK birth consume both residual deletion markers
before the absence-signal circuit begins. -/
theorem wallSweep_twoGroup_birth_drain_noActive :
    NoActiveDeletion wallTwoGroupAfterBirthDrain ∧
      (wallTwoGroupAfterBirthDrain 2).core.core.leader = true ∧
      (wallTwoGroupAfterBirthDrain 2).core.core.label = (0 : Fin 2) ∧
      (wallTwoGroupAfterBirthDrain 2).core.core.shield = false := by
  unfold NoActiveDeletion
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The canonical divisible-ring trap reaches the actual shielded label-zero
leader premise of the restartable cleanup theorem. -/
theorem wallSweep_twoGroup_trap_reaches_protected_anchor :
    ProtectedLeaderAt wallTwoPos
      wallTwoGroupProtectedAnchor 2 := by
  unfold ProtectedLeaderAt InitiatorAnchor
  decide

/-- The explicit thirteen-edge prefix is a real execution of the finite wall
protocol, not only a computation-level endpoint definition. -/
theorem wallSweep_twoGroup_protected_anchor_reachable :
    PopulationProtocol.Reachable (wallSweepProtocol wallTwoPos 0 6)
      cleanupRing twoGroupTrap wallTwoGroupProtectedAnchor := by
  change PopulationProtocol.Reachable (wallSweepProtocol wallTwoPos 0 6)
    cleanupRing twoGroupTrap
      (runLocalSchedule cleanupRing
        (wallSweepPathStallTransition wallTwoPos 0 6) twoGroupTrap
        wallTwoGroupProtectedAnchorSchedule)
  exact wallSweepRun_reachable twoGroupTrap
    wallTwoGroupProtectedAnchorSchedule

/-- **Positive birth-to-cleanup bridge.**  From the canonical barrier-free
leaderless divisible trap, the complete finite wall protocol reaches a state
with the CHECK-born leader still alive and every comparison carrier neutral.
The theorem claims neither arbitrary-state entry nor write-carrier cleanup. -/
theorem wallSweep_twoGroup_trap_reaches_restartable_comparison_cleanup :
    ∃ (actual : DetSchedule 4)
      (D : Fin 4 → ExpiringAgentState 2 0 6),
      PopulationProtocol.Reachable (wallSweepProtocol wallTwoPos 0 6)
        cleanupRing twoGroupTrap D ∧
      RestartableWallExecution wallTwoPos 0 6 cleanupRing
        wallTwoGroupProtectedAnchor
        (leaderDrainReseedResetSweep cleanupRing 2) actual D ∧
      D = runLocalSchedule cleanupRing
        (wallSweepPathStallTransition wallTwoPos 0 6)
        wallTwoGroupProtectedAnchor actual ∧
      actual.length ≤
        (2 * 4 - 1) * (4 + 1) +
          comparisonPathCount wallTwoGroupProtectedAnchor ∧
      (D 2).core.erase.core.leader = true ∧
      ∀ i, ComparisonNeutral (D i).core.erase.core := by
  obtain ⟨actual, D, hrestart, hlength, hleader, hclean⟩ :=
    exists_restartableLeaderDrainReseedResetSweep_clears_all
      wallTwoPos cleanupRing (by omega) 2
      wallTwoGroupProtectedAnchor
      wallSweep_twoGroup_trap_reaches_protected_anchor
  have hrun := RestartableWallExecution.runLocalSchedule_eq
    wallTwoPos cleanupRing wallTwoGroupProtectedAnchor
    (leaderDrainReseedResetSweep cleanupRing 2) actual D hrestart
  have hsuffix := wallSweepRun_reachable wallTwoGroupProtectedAnchor actual
  have hsuffix' : PopulationProtocol.Reachable
      (wallSweepProtocol wallTwoPos 0 6) cleanupRing
      wallTwoGroupProtectedAnchor D := by
    rw [hrun]
    exact hsuffix
  exact ⟨actual, D,
    wallSweep_twoGroup_protected_anchor_reachable.trans hsuffix',
    hrestart, hrun, hlength, hleader, hclean⟩

end PPLLWallSweepFullCleanupRegression
