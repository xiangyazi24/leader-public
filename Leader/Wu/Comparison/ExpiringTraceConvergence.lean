import Leader.Wu.Comparison.ExpiringRepair
import Leader.Wu.Scheduler.TraceConvergence

/-!
# Exact finite phase for the expiration-repair recovery witness

The nondegenerate n=4 regression has one explicit favorable four-edge schedule.
This module turns that fact into an honest `UniformFinitePhase`: among the
`4^4=256` uniform schedules, at least one visits the stated unique-leader
snapshot, so the exact allowed-failure budget is 255. The postcondition is not
Definition-1 safety. A separate checked five-edge continuation creates a second
leader, and therefore persistence is explicitly false.
-/

namespace PPLLExpiringTraceConvergence

open PPLL PPLLResearchFormulation
open PPLLTraceConvergence PPLLExpiringComparisonRepair

/-- Exact input surface for the concrete recovery phase. -/
def ExpiringRecoveryPre (C : Fin 4 → ExpiringAgentState 2 0 0) : Prop :=
  C = recoveryConfig

/-- Snapshot target: position zero is the sole leader. -/
def ExpiringRecoveryPost (C : Fin 4 → ExpiringAgentState 2 0 0) : Prop :=
  (C 0).core.core.leader = true ∧
    (C 1).core.core.leader = false ∧
    (C 2).core.core.leader = false ∧
    (C 3).core.core.leader = false

/-- Boolean decision procedure for the concrete unique-leader snapshot. -/
def expiringRecoveryPostTest
    (C : Fin 4 → ExpiringAgentState 2 0 0) : Bool :=
  (C 0).core.core.leader && !(C 1).core.core.leader &&
    !(C 2).core.core.leader && !(C 3).core.core.leader

/-- The Boolean target exactly decides the snapshot proposition. -/
theorem expiringRecoveryPostTest_decides
    (C : Fin 4 → ExpiringAgentState 2 0 0) :
    expiringRecoveryPostTest C = true ↔ ExpiringRecoveryPost C := by
  simp [expiringRecoveryPostTest, ExpiringRecoveryPost, and_assoc]

/-- The explicit schedule is one outcome in the exact length-four sample space. -/
theorem expiringRecoverySchedule_mem :
    ([1, 0, 3, 0] : DetSchedule 4) ∈ allSchedules 4 4 :=
  mem_allSchedules_of_length 4 4 _ rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The explicit schedule visits the unique-leader snapshot. -/
theorem expiringRecoverySchedule_hits :
    hitsWithinLocal recoveryRing (expiringTransition (by omega) 0 0)
      expiringRecoveryPostTest recoveryConfig [1, 0, 3, 0] = true := by
  decide

/-- At least one of the 256 schedules is favorable. -/
theorem expiringRecovery_hitCount_pos :
    0 < localHitCount recoveryRing (expiringTransition (by omega) 0 0)
      expiringRecoveryPostTest recoveryConfig 4 := by
  unfold localHitCount
  exact List.countP_pos_iff.mpr
    ⟨[1, 0, 3, 0], expiringRecoverySchedule_mem,
      expiringRecoverySchedule_hits⟩

/-- Honest exact finite phase with success probability at least `1/256`. -/
theorem expiringRecoveryPhase :
    UniformFinitePhase recoveryRing (expiringTransition (by omega) 0 0)
      ExpiringRecoveryPre ExpiringRecoveryPost expiringRecoveryPostTest
      4 255 := by
  constructor
  · exact expiringRecoveryPostTest_decides
  · intro C hC
    subst C
    rw [allSchedules_length]
    have hpos := expiringRecovery_hitCount_pos
    have hpow : 4 ^ 4 = 256 := by decide
    rw [hpow]
    omega

set_option maxRecDepth 8192 in
/-- The phase postcondition is not persistent: the checked continuation from
`ExpiringComparisonRepair` creates a second leader. -/
theorem expiringRecoveryPost_not_persistent :
    ExpiringRecoveryPost recoveryAfter ∧
      ¬ExpiringRecoveryPost
        (runLocalSchedule recoveryRing (expiringTransition (by omega) 0 0)
          recoveryAfter [1, 0, 2, 1, 2]) := by
  constructor
  · unfold ExpiringRecoveryPost
    exact expiring_n4_recovery_schedule_outputs
  · intro h
    have hbad := expiring_n4_recovery_not_output_stable
    have hfalse := h.2.2.1
    have hcontra : true = false := hbad.2.symm.trans hfalse
    exact Bool.noConfusion hcontra

end PPLLExpiringTraceConvergence
