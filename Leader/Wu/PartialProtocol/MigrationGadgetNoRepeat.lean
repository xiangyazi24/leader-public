import Leader.Wu.PartialProtocol.LocalLegitimacyCounterfamily

/-!
# The accepted migration gadget is not self-reproducing

The unbounded counterfamily proves one exact output-changing step, but a
finite bad prefix is not by itself a fair non-stabilizing execution.  This file
isolates the first obstruction to iterating that same gadget.

An exact reuse requires the ordered critical pair again: the neutral
label-one follower on the left and the neutral label-two leader on the right.
After the accepted step, the unique leader is at site one.  Consequently, any
putative next copy must end at site one and hence start at its unique
predecessor, site zero.  Site zero was untouched and has label zero, so it is
not the required label-one left endpoint.  Thus no edge of the immediate
successor contains another exact copy of the accepted pair.

This is deliberately scoped.  It rules out direct tiling/iteration of the
one-step witness; it does not rule out a different recurrent mechanism that
first rebuilds the hidden control state, nor any fair non-stabilizing execution
of the full protocol.  Such a result would require an independently proved
return path or recurrent output-changing set.
-/

namespace PPLLCompleteMultiLeaderCleanup

open PPLL PPLLResearchFormulation PPLLDomain
open PPLLNoCheckBirthConditionTwoGeometry
open PPLLExpiringComparisonRepair
open PPartialErratumLocalLegitimacyCounterfamilySol

set_option autoImplicit false

namespace PPartialErratumFairMigrationSol

private theorem fairHPsi : (3 : Nat) > 0 := by
  decide

private abbrev fairProtocol : PopulationProtocol :=
  P_partialProtocolUnconditional fairHPsi 1 1

/-- Site zero, the unique predecessor of the migrated leader at site one. -/
def familyPredecessor {n : Nat} (hn : 6 ≤ n) : Fin n :=
  ⟨0, by omega⟩

private theorem predecessor_ne_initiator
    {n : Nat} (hn : 6 ≤ n) :
    familyPredecessor hn ≠ familyInitiator hn := by
  intro h
  have hv := congrArg Fin.val h
  simp [familyPredecessor, familyInitiator] at hv

private theorem predecessor_ne_responder
    {n : Nat} (hn : 6 ≤ n) :
    familyPredecessor hn ≠ familyResponder hn := by
  intro h
  have hv := congrArg Fin.val h
  simp [familyPredecessor, familyResponder] at hv

private theorem initiator_ne_responder
    {n : Nat} (hn : 6 ≤ n) :
    familyInitiator hn ≠ familyResponder hn := by
  intro h
  have hv := congrArg Fin.val h
  simp [familyInitiator, familyResponder] at hv

/-- The predecessor edge is exactly `0 -> 1`. -/
theorem rightNeighbor_predecessor
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    ring.rightNeighbor (familyPredecessor hn) = familyInitiator hn := by
  apply Fin.ext
  change 1 % n = 1
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem config_responder_leader
    {n : Nat} (hn : 6 ≤ n) :
    (familyConfig hn (familyResponder hn)).core.core.leader = true := by
  rfl

private theorem config_leader_false_of_ne_responder
    {n : Nat} (hn : 6 ≤ n) (i : Fin n)
    (hi : i ≠ familyResponder hn) :
    (familyConfig hn i).core.core.leader = false := by
  rw [familyConfig, if_neg hi]
  rfl

/-- Before the accepted step, the initiator emits the follower output. -/
private theorem config_initiator_output_follower
    {n : Nat} (hn : 6 ≤ n) :
    fairProtocol.output (familyConfig hn (familyInitiator hn)) =
      .follower := by
  change
    (if (familyConfig hn (familyInitiator hn)).core.core.leader then
      LeaderOutput.leader else LeaderOutput.follower) = .follower
  rw [config_leader_false_of_ne_responder hn
    (familyInitiator hn) (initiator_ne_responder hn)]
  rfl

/-- The already accepted output-change theorem, together with the preceding
follower output, identifies the successor output at site one without unfolding
the transition again. -/
private theorem after_initiator_output_leader
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    fairProtocol.output (familyAfter hn ring (familyInitiator hn)) =
      .leader := by
  have hchanged :
      fairProtocol.output (familyAfter hn ring (familyInitiator hn)) ≠
        fairProtocol.output (familyConfig hn (familyInitiator hn)) := by
    exact family_output_changed_at_initiator hn ring
  rw [config_initiator_output_follower hn] at hchanged
  cases houtput :
      fairProtocol.output (familyAfter hn ring (familyInitiator hn)) with
  | leader =>
      rfl
  | follower =>
      exact (hchanged houtput).elim

/-- In the immediate successor, only site one carries a true leader bit. -/
theorem after_leader_true_only_at_initiator
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) (i : Fin n)
    (hi : (familyAfter hn ring i).core.core.leader = true) :
    i = familyInitiator hn := by
  have hlegit := family_successor_still_legit hn ring
  change
    UniqueLeaderOutput fairProtocol n (familyAfter hn ring)
      isLeaderOutput at hlegit
  rcases hlegit with ⟨leaderPos, _, hunique⟩
  have hiOutput :
      fairProtocol.output (familyAfter hn ring i) = .leader := by
    change
      (if (familyAfter hn ring i).core.core.leader then
        LeaderOutput.leader else LeaderOutput.follower) = .leader
    rw [hi]
    rfl
  have hiLeader :
      isLeaderOutput
        (fairProtocol.output (familyAfter hn ring i)) = true := by
    rw [hiOutput]
    rfl
  have hinitLeader :
      isLeaderOutput
        (fairProtocol.output
          (familyAfter hn ring (familyInitiator hn))) = true := by
    rw [after_initiator_output_leader hn ring]
    rfl
  exact (hunique i hiLeader).trans
    (hunique (familyInitiator hn) hinitLeader).symm

/-- The untouched predecessor state (label zero) is not the critical left
state at site one (label one). -/
theorem predecessor_state_ne_critical_left
    {n : Nat} (hn : 6 ≤ n) :
    familyConfig hn (familyPredecessor hn) ≠
      familyConfig hn (familyInitiator hn) := by
  intro h
  have hlabel := congrArg
    (fun s : ExpiringAgentState 3 1 1 => s.core.core.label.val) h
  change (0 : Nat) = 1 at hlabel
  omega

/-- An edge carries the exact ordered critical pair, with the endpoint states
taken from the initial padded member. -/
def ExactCriticalPairAt
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState 3 1 1) (e : Fin n) : Prop :=
  C e = familyConfig hn (familyInitiator hn) ∧
    C (ring.rightNeighbor e) =
      familyConfig hn (familyResponder hn)

/-- The initial family member contains the exact pair at edge one. -/
theorem initial_has_exact_critical_pair
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    ExactCriticalPairAt hn ring (familyConfig hn) (familyInitiator hn) := by
  constructor
  · rfl
  · rw [family_rightNeighbor_initiator]

/-- Terminal obstruction to direct iteration: after the accepted migration,
no edge contains another exact copy of its input pair. -/
theorem successor_has_no_exact_critical_pair
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    ¬∃ e : Fin n, ExactCriticalPairAt hn ring (familyAfter hn ring) e := by
  rintro ⟨e, hleft, hright⟩
  have hrightLeader :
      (familyAfter hn ring (ring.rightNeighbor e)).core.core.leader = true := by
    rw [hright]
    exact config_responder_leader hn
  have htarget :
      ring.rightNeighbor e = familyInitiator hn :=
    after_leader_true_only_at_initiator hn ring
      (ring.rightNeighbor e) hrightLeader
  have hedge : e = familyPredecessor hn := by
    apply rightNeighbor_injective ring
    exact htarget.trans (rightNeighbor_predecessor hn ring).symm
  subst e
  have hframe := familyAfter_eq_config_of_off_edge
    hn ring (familyPredecessor hn)
      (predecessor_ne_initiator hn) (predecessor_ne_responder hn)
  apply predecessor_state_ne_critical_left hn
  exact hframe.symm.trans hleft

/-- Therefore the accepted exact gadget cannot supply even the second link of
a chain made solely by reapplying that gadget. -/
theorem no_two_link_exact_migration_chain
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    ExactCriticalPairAt hn ring (familyConfig hn) (familyInitiator hn) ∧
      ¬∃ e : Fin n,
        ExactCriticalPairAt hn ring (familyAfter hn ring) e :=
  ⟨initial_has_exact_critical_pair hn ring,
    successor_has_no_exact_critical_pair hn ring⟩

#print axioms after_leader_true_only_at_initiator
#print axioms predecessor_state_ne_critical_left
#print axioms successor_has_no_exact_critical_pair
#print axioms no_two_link_exact_migration_chain

end PPartialErratumFairMigrationSol

end PPLLCompleteMultiLeaderCleanup
