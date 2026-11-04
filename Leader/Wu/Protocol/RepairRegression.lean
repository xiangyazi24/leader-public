import Leader.Wu.Safety.Counterexamples
import Leader.Wu.Safety.CorrectedFormulation

/-!
# Regression matrix for the integrated P_PLL research candidate

The integrated candidate changes only WAIT overflow, the Algorithm-15
bullet/signal collision, and CMP_UPDATE source re-arming.  Self-stabilization
permits arbitrary initial garbage, so a transient T1/T8 action is not by itself
a convergence counterexample.  Nevertheless these exact checks prevent the
candidate from being described as a transition-level repair of defects it does
not address.
-/

namespace PPLLRepairRegression

open PPLL PPLLCounterexample PPLLResearchFormulation

/-! ## T2: WAIT overflow is clamped -/

private def t2OverflowL : AgentState 2 :=
  { state2 0 with carry := true, h_field := false }

private def t2OverflowR : AgentState 2 :=
  { state2 1 with count := 1, h_field := true }

/-- The integrated candidate maps T2's cap-overflow input back to the cap
`κ=1`, rather than producing the out-of-domain value two. -/
theorem t2_integrated_clamps_count :
    (PPLLRepair.ppllIntegratedRepair (by omega : 2 > 0) 1
      t2OverflowL t2OverflowR).2.count = 1 := by
  decide

/-! ## T1: forged complete comparison state remains executable -/

/-- Integrated local step on the original T1 interacting pair. -/
def t1IntegratedPair : AgentState 2 × AgentState 2 :=
  PPLLRepair.ppllIntegratedRepair (by omega) 10
    (counterConfig 2) (counterConfig 3)

/-- The integrated candidate still creates and migrates a leader from T1's
forged complete comparison carrier; its three local repairs are inactive at the
CHECK creation boundary. -/
theorem t1_integrated_still_creates_leader :
    t1IntegratedPair.1.leader = true := by
  decide

/-- Integrated audit-protocol successor for T1. -/
def t1IntegratedSuccessor : Fin 4 → AgentState 2 :=
  PopulationProtocol.step (PPLLRepair.integratedProtocol (by omega) 10)
    ring4 counterConfig 2

/-- The corrected Definition-1 target rejects T1 directly: one reachable
integrated successor changes position 2's output from follower to leader. -/
theorem t1_not_semantically_safe_for_integrated :
    ¬PopulationProtocol.IsSafe
      (PPLLRepair.integratedProtocol (by omega) 10) ring4
      counterConfig isLeaderOutput := by
  intro hsafe
  have hreach : PopulationProtocol.Reachable
      (PPLLRepair.integratedProtocol (by omega) 10) ring4
      counterConfig t1IntegratedSuccessor :=
    PopulationProtocol.OneStep.to_reachable ⟨2, rfl⟩
  have hout := hsafe.2 t1IntegratedSuccessor hreach 2
  change AgentState.outputFn (t1IntegratedSuccessor 2) =
    AgentState.outputFn (counterConfig 2) at hout
  have hne : AgentState.outputFn (t1IntegratedSuccessor 2) ≠
      AgentState.outputFn (counterConfig 2) := by
    decide
  exact hne hout

private def t1LeaderTest (C : Fin 4 → AgentState 2) : Bool :=
  (C 2).leader

/-- Under one uniform integrated interaction, the still-live T1 bad edge has
exact count one among four schedules. -/
theorem t1_integrated_bad_schedule_count :
    hitCount ring4 (PPLLRepair.ppllIntegratedRepair (by omega) 10)
      t1LeaderTest counterConfig 1 = 1 := by
  decide

/-- T1's one-step output change therefore still has exact probability `1/4`
for the integrated audit candidate. -/
theorem t1_integrated_bad_event_probability :
    hitProbability ring4 (PPLLRepair.ppllIntegratedRepair (by omega) 10)
      t1LeaderTest counterConfig 1 = (1 : Rat) / 4 := by
  unfold hitProbability
  rw [t1_integrated_bad_schedule_count, allSchedules_length]
  rfl

/-! ### T1 on the actual finite physical carrier -/

/-- Reification of T1 into the bounded physical state, justified by its proved
Algorithm-1 domain membership. -/
def t1FiniteConfig : Fin 4 → BoundedAgentState 2 10 := fun i =>
  BoundedAgentState.ofDomain (counterConfig i)
    (counterConfig_inProtocolDomain i)

/-- One T1 interaction in the actual finite integrated protocol. -/
def t1FiniteSuccessor : Fin 4 → BoundedAgentState 2 10 :=
  PopulationProtocol.step
    (PPLLRepair.integratedBoundedProtocol (by omega) 10)
    ring4 t1FiniteConfig 2

theorem erase_t1FiniteConfig :
    PPLLRepair.eraseConfig t1FiniteConfig = counterConfig := by
  funext i
  simp [t1FiniteConfig, PPLLRepair.eraseConfig,
    BoundedAgentState.erase_ofDomain]

/-- Exact finite-to-audit simulation identifies the bounded successor with the
integrated T1 successor above. -/
theorem erase_t1FiniteSuccessor :
    PPLLRepair.eraseConfig t1FiniteSuccessor = t1IntegratedSuccessor := by
  unfold t1FiniteSuccessor
  rw [PPLLRepair.erase_integrated_step]
  rw [erase_t1FiniteConfig]
  rfl

/-- The finite T1 interaction changes position 2's physical output from
follower to leader. -/
theorem t1_finite_output_changes :
    (PPLLRepair.integratedBoundedProtocol (by omega) 10).output
        (t1FiniteSuccessor 2) ≠
      (PPLLRepair.integratedBoundedProtocol (by omega) 10).output
        (t1FiniteConfig 2) := by
  change AgentState.outputFn
      (BoundedAgentState.erase (t1FiniteSuccessor 2)) ≠
    AgentState.outputFn (BoundedAgentState.erase (t1FiniteConfig 2))
  have hs := congrFun erase_t1FiniteSuccessor 2
  have hc := congrFun erase_t1FiniteConfig 2
  change BoundedAgentState.erase (t1FiniteSuccessor 2) =
    t1IntegratedSuccessor 2 at hs
  change BoundedAgentState.erase (t1FiniteConfig 2) = counterConfig 2 at hc
  rw [hs, hc]
  decide

/-- T1 is not semantically safe even on the finite physical carrier.  This is
not a failure of eventual self-stabilization; it says the arbitrary T1 input is
not already in the Definition-1 terminal set. -/
theorem t1_finite_not_semantically_safe :
    ¬PopulationProtocol.IsSafe
      (PPLLRepair.integratedBoundedProtocol (by omega) 10) ring4
      t1FiniteConfig isLeaderOutput := by
  intro hsafe
  have hreach : PopulationProtocol.Reachable
      (PPLLRepair.integratedBoundedProtocol (by omega) 10) ring4
      t1FiniteConfig t1FiniteSuccessor :=
    PopulationProtocol.OneStep.to_reachable ⟨2, rfl⟩
  have hout := hsafe.2 t1FiniteSuccessor hreach 2
  exact t1_finite_output_changes hout

/-! ## T7: the exact bullet/signal collision is removed -/

/-- Integrated local transition on T7's interacting pair. -/
def t7IntegratedPair : AgentState 2 × AgentState 2 :=
  PPLLRepair.ppllIntegratedRepair (by omega) 10
    (bulletCounterConfig 0) (bulletCounterConfig 1)

/-- The integrated candidate agrees with the earlier no-collision candidate on
this exact pair, so the proved peacefulness regression transfers unchanged. -/
theorem t7_integrated_pair_eq_repaired :
    t7IntegratedPair = bulletRepairedPair := by
  decide

/-- T7's collocated live bullet no longer carries `signal_B=1`. -/
theorem t7_integrated_removes_collision :
    t7IntegratedPair.2.bullet = 2 ∧ t7IntegratedPair.2.signal_B = 0 := by
  rw [t7_integrated_pair_eq_repaired]
  exact bullet_repair_removes_collision

/-- Full integrated successor of T7's configuration. -/
def t7IntegratedSuccessor : Fin 4 → AgentState 2 :=
  PopulationProtocol.step (PPLLRepair.integratedProtocol (by omega) 10)
    ring4 bulletCounterConfig 0

/-- On the exact T7 witness, the integrated full successor agrees pointwise
with the earlier no-collision successor. -/
theorem t7_integrated_successor_eq_repaired :
    t7IntegratedSuccessor = bulletRepairedSuccessor := by
  funext k
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
    have hv := k.isLt
    omega
  rcases hk with hk | hk | hk | hk <;> subst k <;> decide

/-- Consequently the integrated transition preserves peacefulness for this
specific T7 live bullet. -/
theorem t7_integrated_witness_peaceful :
    isPeacefulBullet (by omega : 2 > 0) ring4 t7IntegratedSuccessor 1 := by
  rw [t7_integrated_successor_eq_repaired]
  exact bullet_repair_witness_remains_peaceful

/-! ## T8: orphan write action remains executable -/

/-- Integrated local step on T8's orphan-write pair. -/
def t8IntegratedPair : AgentState 2 × AgentState 2 :=
  PPLLRepair.ppllIntegratedRepair (by omega) 10
    (writeCounterConfig 2) (writeCounterConfig 3)

/-- Integrated audit successor for the orphan-write witness. -/
def t8IntegratedSuccessor : Fin 4 → AgentState 2 := fun k =>
  if k = (2 : Fin 4) then t8IntegratedPair.1
  else if k = (3 : Fin 4) then t8IntegratedPair.2
  else writeCounterConfig k

/-- None of the three integrated transition changes constrain an orphan
`increment_group`, so T8 still changes the stable follower-group ID. -/
theorem t8_integrated_still_changes_groupID :
    groupID ring4.hn t8IntegratedSuccessor 2 = 1 := by
  decide

private def t8BitTest (C : Fin 4 → AgentState 2) : Bool :=
  (C 3).bit

/-- T8 also remains an exact one-edge event under the integrated candidate. -/
theorem t8_integrated_bad_schedule_count :
    hitCount ring4 (PPLLRepair.ppllIntegratedRepair (by omega) 10)
      t8BitTest writeCounterConfig 1 = 1 := by
  decide

/-- The unchanged orphan-write event has exact probability `1/4`. -/
theorem t8_integrated_bad_event_probability :
    hitProbability ring4 (PPLLRepair.ppllIntegratedRepair (by omega) 10)
      t8BitTest writeCounterConfig 1 = (1 : Rat) / 4 := by
  unfold hitProbability
  rw [t8_integrated_bad_schedule_count, allSchedules_length]
  rfl

/-! ### T8 on the actual finite physical carrier -/

/-- Reification of T8 into the finite physical carrier. -/
def t8FiniteConfig : Fin 4 → BoundedAgentState 2 10 := fun i =>
  BoundedAgentState.ofDomain (writeCounterConfig i)
    (writeCounterConfig_inProtocolDomain i)

/-- One orphan-write interaction in the finite integrated protocol. -/
def t8FiniteSuccessor : Fin 4 → BoundedAgentState 2 10 :=
  PopulationProtocol.step
    (PPLLRepair.integratedBoundedProtocol (by omega) 10)
    ring4 t8FiniteConfig 2

theorem erase_t8FiniteConfig :
    PPLLRepair.eraseConfig t8FiniteConfig = writeCounterConfig := by
  funext i
  simp [t8FiniteConfig, PPLLRepair.eraseConfig,
    BoundedAgentState.erase_ofDomain]

/-- Exact simulation also identifies the finite T8 successor. -/
theorem erase_t8FiniteSuccessor :
    PPLLRepair.eraseConfig t8FiniteSuccessor = t8IntegratedSuccessor := by
  unfold t8FiniteSuccessor
  rw [PPLLRepair.erase_integrated_step]
  rw [erase_t8FiniteConfig]
  rfl

/-- T8's group-ID mutation therefore occurs on the actual finite carrier, not
only in the unbounded audit representation. -/
theorem t8_finite_still_changes_groupID :
    groupID ring4.hn (PPLLRepair.eraseConfig t8FiniteSuccessor) 2 = 1 := by
  rw [erase_t8FiniteSuccessor]
  exact t8_integrated_still_changes_groupID

/-! ## T9/T10/L11 terminal classifications -/

/-- Existing T9 regression: source-departing components stay departing and the
second same-edge interaction creates no leader. -/
theorem t9_exact_witness_removed :
    integratedSelfSourceRound2.1.leader = false ∧
    integratedSelfSourceRound2.2.leader = false := by
  exact ⟨integrated_repair_removes_source_self_witness.1,
    integrated_repair_removes_source_self_witness.2.1⟩

/-- T10 is excluded at the statement layer rather than silently assigned a
same-agent two-output transition interpretation. -/
theorem t10_one_agent_outside_regime :
    PPLLRepair.IntegratedRepairRegime 2 1 → False :=
  PPLLRepair.no_integrated_regime_on_one 2

/-- L11's replacement history is monotone under the finite proof refinement. -/
theorem l11_historical_receipt_preserved
    {n ψ : Nat} (regime : OperationalRegime n ψ) (κ : Nat)
    (C : Fin n → PPLLSuppressionHistory.BoundedReceiptAgentState ψ κ)
    (hC : AllReceivedReset C) (e : Fin n) :
    AllReceivedReset ((receiptProtocol regime κ).step regime.ring C e) :=
  allReceivedReset_preserved_step regime κ C hC e

end PPLLRepairRegression
