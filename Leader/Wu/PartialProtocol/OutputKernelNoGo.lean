import Leader.Wu.PartialProtocol.MinimalTheoremRepair
import Leader.Wu.Safety.Counterexamples

/-!
# Exact output-kernel obstruction for `P_partial`

The four-field `PPartialOutputLegit` predicate is inhabited, but the current
`P_partial` transition still contains the source CHECK writer.  The forged
comparison carrier from T1 already satisfies the stronger printed five-field
safe predicate.  This file reifies that source configuration in the exact
finite `P_partial` carrier and tests the current compiled transition directly.

No semantic-safety or producer hypothesis is used.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialOutputKernelNoGoSol

open PPLL PPLLResearchFormulation PPLLCounterexample
open PPLLExpiringComparisonRepair
open PPLLPathStallComparisonRepair
open PPLLNoCheckBirthPhysicalConditionOne

set_option autoImplicit false

private theorem hpsi : (2 : Nat) > 0 := by omega

private abbrev domain :
    PPartialAuthorizedDomainClosure hpsi 10 :=
  PPartialAuthorizedDomainClosure_q5776 hpsi 10

private abbrev protocol : PopulationProtocol :=
  P_partialProtocol hpsi 10 0 domain

/-- T1 reified in the exact bounded authorization-plus-expiry carrier. -/
def t1FiniteConfig : PPartialConfig 4 2 10 0 :=
  fun i =>
    ⟨⟨BoundedAgentState.ofDomain (counterConfig i)
        (counterConfig_inProtocolDomain i), false⟩,
      freshStall 0⟩

private theorem erase_t1FiniteConfig :
    eraseExpiringConfig t1FiniteConfig = counterConfig := by
  funext i
  change BoundedAgentState.erase
      (BoundedAgentState.ofDomain (counterConfig i)
        (counterConfig_inProtocolDomain i)) = counterConfig i
  exact BoundedAgentState.erase_ofDomain _ _

/-- The finite T1 start belongs to the concrete four-field output kernel. -/
theorem t1FiniteConfig_outputLegit :
    PPartialOutputLegit hpsi ring4 t1FiniteConfig := by
  unfold PPartialOutputLegit
  rw [erase_t1FiniteConfig]
  exact counterConfig_paper_safe.toOutputSafe

/-- The selected exact successor on T1's armed comparison edge. -/
def t1FiniteAfter : PPartialConfig 4 2 10 0 :=
  localStep ring4 (P_partial hpsi 10 0 domain) t1FiniteConfig 2

/-- The old leader remains at zero and the exact current transition creates a
second leader at position two. -/
theorem t1FiniteAfter_two_leaders :
    (t1FiniteAfter 0).core.core.leader = true ∧
      (t1FiniteAfter 2).core.core.leader = true := by
  decide

/-- Two distinct physical leaders refute the current-state output kernel. -/
theorem t1FiniteAfter_not_outputLegit :
    ¬ PPartialOutputLegit hpsi ring4 t1FiniteAfter := by
  intro hafter
  obtain ⟨leader, _hleader, honly⟩ := hafter.unique_leader
  have h0 : (eraseExpiringConfig t1FiniteAfter 0).isLeader := by
    change (t1FiniteAfter 0).core.core.leader = true
    exact t1FiniteAfter_two_leaders.1
  have h2 : (eraseExpiringConfig t1FiniteAfter 2).isLeader := by
    change (t1FiniteAfter 2).core.core.leader = true
    exact t1FiniteAfter_two_leaders.2
  have h02 : (0 : Fin 4) = 2 :=
    (honly 0 h0).trans (honly 2 h2).symm
  have hv := congrArg Fin.val h02
  omega

/-- The selected exact step changes position two from follower to leader. -/
theorem t1FiniteAfter_output_changed :
    protocol.output (t1FiniteAfter 2) ≠
      protocol.output (t1FiniteConfig 2) := by
  have hafter := t1FiniteAfter_two_leaders.2
  have hbefore : (t1FiniteConfig 2).core.core.leader = false := by
    rfl
  change (if (t1FiniteAfter 2).core.core.leader then
      LeaderOutput.leader else LeaderOutput.follower) ≠
    (if (t1FiniteConfig 2).core.core.leader then
      LeaderOutput.leader else LeaderOutput.follower)
  simp [hafter, hbefore]

/-- Thus the inhabited four-field predicate is not a closed predicate for the
exact current `P_partial` protocol. -/
theorem PPartialOutputLegit_not_closed_t1 :
    ¬ PopulationProtocol.ClosedPred protocol ring4
      (PPartialOutputLegit hpsi ring4) := by
  intro hclosed
  have hnext := hclosed t1FiniteConfig t1FiniteConfig_outputLegit
    t1FiniteAfter ⟨2, rfl⟩
  exact t1FiniteAfter_not_outputLegit hnext

/-- The concrete T1 member of the operational kernel is not output-stable. -/
theorem t1FiniteConfig_not_outputStable :
    ¬ OutputStableFrom protocol ring4 t1FiniteConfig := by
  intro hstable
  have hreach : PopulationProtocol.Reachable protocol ring4
      t1FiniteConfig t1FiniteAfter :=
    PopulationProtocol.OneStep.to_reachable ⟨2, rfl⟩
  exact t1FiniteAfter_output_changed
    (hstable t1FiniteAfter hreach 2)

/-- Consequently the concrete output-kernel member is not Definition-1 safe. -/
theorem t1FiniteConfig_not_isSafe :
    ¬ PopulationProtocol.IsSafe protocol ring4
      t1FiniteConfig isLeaderOutput := by
  intro hsafe
  exact t1FiniteConfig_not_outputStable hsafe.2

/-- In the terminology of the minimal theorem repair, T1 is an inhabited
member of the proposed operational kernel but not a member of the exact
semantic stable predicate. -/
theorem t1FiniteConfig_not_stableLegit :
    ¬ PPartialStableLegit hpsi 10 0 ring4 t1FiniteConfig := by
  intro hstable
  exact t1FiniteConfig_not_outputStable hstable.2

/-- Nonvacuous headline: the exact current protocol's four-field kernel
contains a concrete Definition-1-unsafe configuration. -/
theorem PPartialOutputLegit_contains_unsafe_t1 :
    ∃ C : PPartialConfig 4 2 10 0,
      PPartialOutputLegit hpsi ring4 C ∧
        ¬ PopulationProtocol.IsSafe protocol ring4 C isLeaderOutput := by
  exact ⟨t1FiniteConfig, t1FiniteConfig_outputLegit,
    t1FiniteConfig_not_isSafe⟩

/-- The exact local obligation left in the minimal theorem repair is false,
not merely unproved: T1 starts inside its state predicate and exits it in one
real interaction. -/
theorem PPartialOutputLegitimacyStepObligation_false_t1 :
    ¬ PPartialOutputLegitimacyStepObligation hpsi 10 0 ring4 := by
  intro hstep
  have hnext := (hstep t1FiniteConfig
    t1FiniteConfig_outputLegit 2).1
  exact t1FiniteAfter_not_outputLegit hnext

end PPartialOutputKernelNoGoSol
end PPLLCompleteMultiLeaderCleanup
