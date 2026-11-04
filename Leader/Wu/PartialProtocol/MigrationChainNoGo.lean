import Leader.Wu.PartialProtocol.MigrationGadgetNoRepeat

/-!
# No infinite execution made by chaining the exact migration witness

The accepted unbounded family has one exact output-changing transition, but
the edge at which its critical input pair occurs is itself forced: the right
endpoint is the unique initial leader, so injectivity of the ring successor
identifies the edge as `1 -> 2`.

Combining that uniqueness with the proved absence of the critical pair in the
successor rules out an infinite execution in which every next interaction is
another application of the same exact gadget.  This remains false even after
adding edge fairness, since such a chain cannot supply its second transition.

The result is intentionally narrower than a no-return theorem with arbitrary
intervening transitions.  It does not exclude a different protocol path that
first reconstructs the complete critical endpoint states.
-/

namespace PPLLCompleteMultiLeaderCleanup

open PPLL PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open PPLLNoCheckBirthConditionTwoGeometry
open PPartialErratumLocalLegitimacyCounterfamilySol
open PPartialErratumFairMigrationSol

namespace PPartialErratumExactMigrationNoReturnSol

private theorem chainHPsi : (3 : Nat) > 0 := by
  decide

private abbrev chainProtocol : PopulationProtocol :=
  P_partialProtocolUnconditional chainHPsi 1 1

private theorem initial_leader_true_only_at_responder
    {n : Nat} (hn : 6 ≤ n) (i : Fin n)
    (hi : (familyConfig hn i).core.core.leader = true) :
    i = familyResponder hn := by
  by_cases h : i = familyResponder hn
  · exact h
  · rw [familyConfig, if_neg h] at hi
    contradiction

/-- The named edge is not a choice: it is the only edge of the initial family
member carrying the exact ordered critical pair. -/
theorem initial_exact_pair_edge_eq_initiator
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) (e : Fin n)
    (hpair : ExactCriticalPairAt hn ring (familyConfig hn) e) :
    e = familyInitiator hn := by
  have hrightLeader :
      (familyConfig hn (ring.rightNeighbor e)).core.core.leader = true := by
    rw [hpair.2]
    rfl
  have hright :
      ring.rightNeighbor e = familyResponder hn :=
    initial_leader_true_only_at_responder hn
      (ring.rightNeighbor e) hrightLeader
  apply rightNeighbor_injective ring
  exact hright.trans (family_rightNeighbor_initiator hn ring).symm

/-- An infinite schedule and configuration stream which tries to use the same
exact critical pair at every step of the exact current `P_partial`. -/
def ExactMigrationChain
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n)
    (C : Nat → Fin n → ExpiringAgentState 3 1 1)
    (schedule : Nat → Fin n) : Prop :=
  C 0 = familyConfig hn ∧
    ∀ t : Nat,
      ExactCriticalPairAt hn ring (C t) (schedule t) ∧
        C (t + 1) =
          chainProtocol.step ring (C t) (schedule t)

/-- No infinite exact-gadget chain starts from any member of the unbounded
family.  The contradiction occurs at time one. -/
theorem no_exact_migration_chain
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    ¬ ∃ C : Nat → Fin n → ExpiringAgentState 3 1 1,
      ∃ schedule : Nat → Fin n,
        ExactMigrationChain hn ring C schedule := by
  rintro ⟨C, schedule, hinitial, hsteps⟩
  have hpairZero :
      ExactCriticalPairAt hn ring
        (familyConfig hn) (schedule 0) := by
    simpa [hinitial] using (hsteps 0).1
  have hedgeZero : schedule 0 = familyInitiator hn :=
    initial_exact_pair_edge_eq_initiator
      hn ring (schedule 0) hpairZero
  have hstepZero :
      C 1 = chainProtocol.step ring (C 0) (schedule 0) := by
    simpa using (hsteps 0).2
  rw [hinitial, hedgeZero] at hstepZero
  have htimeOne : C 1 = familyAfter hn ring := by
    exact hstepZero.trans
      (familyAfter_eq_protocol_step hn ring).symm
  have hpairOne :
      ExactCriticalPairAt hn ring
        (familyAfter hn ring) (schedule 1) := by
    simpa [htimeOne] using (hsteps 1).1
  exact successor_has_no_exact_critical_pair hn ring
    ⟨schedule 1, hpairOne⟩

/-- Standard strong edge fairness for an infinite edge schedule. -/
def EdgeFair {n : Nat} (schedule : Nat → Fin n) : Prop :=
  ∀ e : Fin n, ∀ t : Nat,
    ∃ u : Nat, t ≤ u ∧ schedule u = e

/-- Adding fairness cannot rescue direct gadget chaining: there is no such
exact execution even before fairness is considered. -/
theorem no_edge_fair_exact_migration_chain
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    ¬ ∃ C : Nat → Fin n → ExpiringAgentState 3 1 1,
      ∃ schedule : Nat → Fin n,
        EdgeFair schedule ∧ ExactMigrationChain hn ring C schedule := by
  rintro ⟨C, schedule, _, hchain⟩
  exact no_exact_migration_chain hn ring ⟨C, schedule, hchain⟩

end PPartialErratumExactMigrationNoReturnSol
end PPLLCompleteMultiLeaderCleanup
