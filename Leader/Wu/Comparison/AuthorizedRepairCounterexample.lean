import Leader.Wu.Comparison.AuthorizedRepair

/-!
# Closed leaderless class for the first authorization repair

The one-bit moved-carrier repair is finite and repairs the local T9/T18 control
flow, but arbitrary initialization can place `path0Crossed=true` on a payload-
zero component hosted at physical label one. If the other agent carries the
other path component, neither path can move; the label-zero fresh-start guard
never consumes the bit. Starting from one exact ψ=2, κ=0 pair, exhaustive
*reachable-set* expansion stabilizes after four rounds at seven states. This is
a small terminal certificate, not a search over the protocol state space: the
certificate checks only the two outgoing edges of seven explicitly computed
reachable states.

Every certified state keeps the forged marker and has no leader. The set is
closed under both directed-ring edges, so no scheduler can reach Definition-1
safety from this input. This gives avenue (e) a concrete proof-of-failure and
prevents the first physical authorization design from being mistaken for a
self-stabilizing repair.
-/

namespace PPLLAuthorizedRepairCounterexample

open PPLL PPLLRepair PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair

abbrev AuthorizedPair := AuthorizedAgentState 2 × AuthorizedAgentState 2

/-- Label-zero half of the reversed complete carrier. Only WAIT's `h_field`
varies in the small recurrent class. -/
def trapLeft (h : Bool) : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false .depart with wait := false, h_field := h, path := .some 1 0, path4 := some (1, 1), path5 := none }, false⟩

/-- Label-one half carries a forged true marker on payload zero. -/
def trapRight (h : Bool) : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 false .depart with wait := true, h_field := h, path := .some 0 0, path4 := none, path5 := some (0, 1) }, true⟩

/-- Initial reversed carrier used to generate the finite trap certificate. -/
def trapInitial : AuthorizedPair := (trapLeft false, trapRight false)

/-- The nontrivial two-agent directed ring. -/
abbrev trapRing : DirectedRing 2 := ⟨by omega⟩

/-- Decode a pair as positions zero and one. -/
def pairConfig (p : AuthorizedPair) : Fin 2 → AuthorizedAgentState 2
  | ⟨0, _⟩ => p.1
  | ⟨1, _⟩ => p.2

/-- Recover the ordered pair from a two-agent configuration. -/
def configPair (C : Fin 2 → AuthorizedAgentState 2) : AuthorizedPair :=
  (C 0, C 1)

/-- Exact full authorized interaction on either of the two ring edges. -/
def trapStep (p : AuthorizedPair) (e : Fin 2) : AuthorizedPair :=
  configPair (localStep trapRing
    (ppllAuthorizedRepair (by omega : 2 > 0) 0) (pairConfig p) e)

/-! ## Explicit seven-state terminal certificate

A separate executable BFS found seven reachable states. We record those states
by shortest transition paths, then kernel-check only their fourteen outgoing
edges. This avoids replaying list deduplication inside the proof kernel. -/

private def trapRightDepart (h : Bool) : AuthorizedAgentState 2 :=
  let u := trapRight h
  ⟨{ u.core with write_state := .depart }, u.path0Crossed⟩

private def trapResetLeft : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false .depart with wait := false, reset := true, path := .some 1 0, write_state := .depart }, false⟩

private def trapBareRight (h : Bool) : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 false .depart with wait := true, h_field := h, path := .some 0 0 }, true⟩

def trapState0 : AuthorizedPair := trapInitial
def trapState1 : AuthorizedPair := (trapLeft true, trapRightDepart false)
def trapState2 : AuthorizedPair := (trapResetLeft, trapBareRight false)
def trapState3 : AuthorizedPair := (trapLeft false, trapRightDepart true)
def trapState4 : AuthorizedPair := (trapLeft true, trapRightDepart true)
def trapState5 : AuthorizedPair := (trapResetLeft, trapBareRight true)
def trapState6 : AuthorizedPair := (trapLeft false, trapRightDepart false)

/-- The reduced closed class, in shortest-path discovery order. -/
def trapStates : List AuthorizedPair :=
  [trapState0, trapState1, trapState2, trapState3,
    trapState4, trapState5, trapState6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem trapState0_edges :
    trapStep trapState0 0 = trapState1 ∧
      trapStep trapState0 1 = trapState2 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem trapState1_edges :
    trapStep trapState1 0 = trapState3 ∧
      trapStep trapState1 1 = trapState2 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem trapState2_edges :
    trapStep trapState2 0 = trapState1 ∧
      trapStep trapState2 1 = trapState2 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem trapState3_edges :
    trapStep trapState3 0 = trapState4 ∧
      trapStep trapState3 1 = trapState5 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem trapState4_edges :
    trapStep trapState4 0 = trapState6 ∧
      trapStep trapState4 1 = trapState5 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem trapState5_edges :
    trapStep trapState5 0 = trapState1 ∧
      trapStep trapState5 1 = trapState5 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem trapState6_edges :
    trapStep trapState6 0 = trapState1 ∧
      trapStep trapState6 1 = trapState2 := by decide

/-- The explicit reduced class has seven states. -/
theorem trapStates_length : trapStates.length = 7 := by rfl

/-- The initial witness belongs to the certified class. -/
theorem trapInitial_mem : trapInitial ∈ trapStates := by
  simp [trapStates, trapState0]

private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi with hi | hi
  · exact .inl (Fin.ext hi)
  · exact .inr (Fin.ext hi)

private theorem mem_trapState0 : trapState0 ∈ trapStates := by simp [trapStates]
private theorem mem_trapState1 : trapState1 ∈ trapStates := by simp [trapStates]
private theorem mem_trapState2 : trapState2 ∈ trapStates := by simp [trapStates]
private theorem mem_trapState3 : trapState3 ∈ trapStates := by simp [trapStates]
private theorem mem_trapState4 : trapState4 ∈ trapStates := by simp [trapStates]
private theorem mem_trapState5 : trapState5 ∈ trapStates := by simp [trapStates]
private theorem mem_trapState6 : trapState6 ∈ trapStates := by simp [trapStates]

/-- The fourteen checked edges give a normal Prop-level closure theorem. -/
theorem trap_closed {p : AuthorizedPair} (hp : p ∈ trapStates)
    (e : Fin 2) : trapStep p e ∈ trapStates := by
  have hp' : p = trapState0 ∨ p = trapState1 ∨ p = trapState2 ∨
      p = trapState3 ∨ p = trapState4 ∨ p = trapState5 ∨
      p = trapState6 := by simpa [trapStates] using hp
  rcases hp' with hp' | hp' | hp' | hp' | hp' | hp' | hp' <;> subst p
  all_goals rcases fin2_cases e with rfl | rfl
  · rw [trapState0_edges.1]; exact mem_trapState1
  · rw [trapState0_edges.2]; exact mem_trapState2
  · rw [trapState1_edges.1]; exact mem_trapState3
  · rw [trapState1_edges.2]; exact mem_trapState2
  · rw [trapState2_edges.1]; exact mem_trapState1
  · rw [trapState2_edges.2]; exact mem_trapState2
  · rw [trapState3_edges.1]; exact mem_trapState4
  · rw [trapState3_edges.2]; exact mem_trapState5
  · rw [trapState4_edges.1]; exact mem_trapState6
  · rw [trapState4_edges.2]; exact mem_trapState5
  · rw [trapState5_edges.1]; exact mem_trapState1
  · rw [trapState5_edges.2]; exact mem_trapState5
  · rw [trapState6_edges.1]; exact mem_trapState1
  · rw [trapState6_edges.2]; exact mem_trapState2

private theorem trapState_properties :
    (trapState0.2.path0Crossed = true ∧
      trapState0.1.core.leader = false ∧ trapState0.2.core.leader = false) ∧
    (trapState1.2.path0Crossed = true ∧
      trapState1.1.core.leader = false ∧ trapState1.2.core.leader = false) ∧
    (trapState2.2.path0Crossed = true ∧
      trapState2.1.core.leader = false ∧ trapState2.2.core.leader = false) ∧
    (trapState3.2.path0Crossed = true ∧
      trapState3.1.core.leader = false ∧ trapState3.2.core.leader = false) ∧
    (trapState4.2.path0Crossed = true ∧
      trapState4.1.core.leader = false ∧ trapState4.2.core.leader = false) ∧
    (trapState5.2.path0Crossed = true ∧
      trapState5.1.core.leader = false ∧ trapState5.2.core.leader = false) ∧
    (trapState6.2.path0Crossed = true ∧
      trapState6.1.core.leader = false ∧ trapState6.2.core.leader = false) := by
  decide

/-- The forged marker persists in every certified state. -/
theorem trap_marker_persists {p : AuthorizedPair} (hp : p ∈ trapStates) :
    p.2.path0Crossed = true := by
  have hp' : p = trapState0 ∨ p = trapState1 ∨ p = trapState2 ∨
      p = trapState3 ∨ p = trapState4 ∨ p = trapState5 ∨
      p = trapState6 := by simpa [trapStates] using hp
  rcases hp' with hp' | hp' | hp' | hp' | hp' | hp' | hp' <;> subst p
  · exact trapState_properties.1.1
  · exact trapState_properties.2.1.1
  · exact trapState_properties.2.2.1.1
  · exact trapState_properties.2.2.2.1.1
  · exact trapState_properties.2.2.2.2.1.1
  · exact trapState_properties.2.2.2.2.2.1.1
  · exact trapState_properties.2.2.2.2.2.2.1

private theorem trapState_domains :
    (trapState0.1.core.inProtocolDomain 0 ∧
      trapState0.2.core.inProtocolDomain 0) ∧
    (trapState1.1.core.inProtocolDomain 0 ∧
      trapState1.2.core.inProtocolDomain 0) ∧
    (trapState2.1.core.inProtocolDomain 0 ∧
      trapState2.2.core.inProtocolDomain 0) ∧
    (trapState3.1.core.inProtocolDomain 0 ∧
      trapState3.2.core.inProtocolDomain 0) ∧
    (trapState4.1.core.inProtocolDomain 0 ∧
      trapState4.2.core.inProtocolDomain 0) ∧
    (trapState5.1.core.inProtocolDomain 0 ∧
      trapState5.2.core.inProtocolDomain 0) ∧
    (trapState6.1.core.inProtocolDomain 0 ∧
      trapState6.2.core.inProtocolDomain 0) := by
  simp [AgentState.inProtocolDomain, trapState0, trapState1, trapState2,
    trapState3, trapState4, trapState5, trapState6, trapInitial,
    trapLeft, trapRight, trapRightDepart, trapResetLeft, trapBareRight,
    PPLLCounterexample.state2]

/-- Both cores of every trap pair lie in the κ=0 finite value domain. -/
theorem trap_inProtocolDomain {p : AuthorizedPair} (hp : p ∈ trapStates) :
    p.1.core.inProtocolDomain 0 ∧ p.2.core.inProtocolDomain 0 := by
  have hp' : p = trapState0 ∨ p = trapState1 ∨ p = trapState2 ∨
      p = trapState3 ∨ p = trapState4 ∨ p = trapState5 ∨
      p = trapState6 := by simpa [trapStates] using hp
  rcases hp' with hp' | hp' | hp' | hp' | hp' | hp' | hp' <;> subst p
  · exact trapState_domains.1
  · exact trapState_domains.2.1
  · exact trapState_domains.2.2.1
  · exact trapState_domains.2.2.2.1
  · exact trapState_domains.2.2.2.2.1
  · exact trapState_domains.2.2.2.2.2.1
  · exact trapState_domains.2.2.2.2.2.2

/-- Every audit trap pair has an exact representative in the finite authorized
carrier. -/
theorem trap_reifies_finitely {p : AuthorizedPair} (hp : p ∈ trapStates) :
    ∃ l r : AuthorizedBoundedAgentState 2 0,
      l.erase = p.1 ∧ r.erase = p.2 := by
  have hd := trap_inProtocolDomain hp
  let l : AuthorizedBoundedAgentState 2 0 :=
    ⟨BoundedAgentState.ofDomain p.1.core hd.1, p.1.path0Crossed⟩
  let r : AuthorizedBoundedAgentState 2 0 :=
    ⟨BoundedAgentState.ofDomain p.2.core hd.2, p.2.path0Crossed⟩
  refine ⟨l, r, ?_, ?_⟩
  · change AuthorizedAgentState.mk
      (BoundedAgentState.erase (BoundedAgentState.ofDomain p.1.core hd.1))
      p.1.path0Crossed = p.1
    rw [BoundedAgentState.erase_ofDomain]
  · change AuthorizedAgentState.mk
      (BoundedAgentState.erase (BoundedAgentState.ofDomain p.2.core hd.2))
      p.2.path0Crossed = p.2
    rw [BoundedAgentState.erase_ofDomain]

/-- Both outputs are followers in every certified state. -/
theorem trap_no_leaders {p : AuthorizedPair} (hp : p ∈ trapStates) :
    p.1.core.leader = false ∧ p.2.core.leader = false := by
  have hp' : p = trapState0 ∨ p = trapState1 ∨ p = trapState2 ∨
      p = trapState3 ∨ p = trapState4 ∨ p = trapState5 ∨
      p = trapState6 := by simpa [trapStates] using hp
  rcases hp' with hp' | hp' | hp' | hp' | hp' | hp' | hp' <;> subst p
  · exact trapState_properties.1.2
  · exact trapState_properties.2.1.2
  · exact trapState_properties.2.2.1.2
  · exact trapState_properties.2.2.2.1.2
  · exact trapState_properties.2.2.2.2.1.2
  · exact trapState_properties.2.2.2.2.2.1.2
  · exact trapState_properties.2.2.2.2.2.2.2

/-- Packaged audit protocol for semantic reachability. -/
def authorizedAuditProtocol : PopulationProtocol where
  Q := AuthorizedAgentState 2
  Y := LeaderOutput
  transition := ppllAuthorizedRepair (by omega) 0
  output := fun s => if s.core.leader then .leader else .follower

/-- Configurations represented by a pair in the seven-state trap. -/
def InAuthorizedTrap (C : Fin 2 → AuthorizedAgentState 2) : Prop :=
  ∃ p, p ∈ trapStates ∧ C = pairConfig p

/-- Pair stepping agrees exactly with the packaged protocol step. -/
theorem protocolStep_pairConfig (p : AuthorizedPair) (e : Fin 2) :
    PopulationProtocol.step authorizedAuditProtocol trapRing (pairConfig p) e =
      pairConfig (trapStep p e) := by
  funext i
  rcases fin2_cases e with rfl | rfl <;>
    rcases fin2_cases i with rfl | rfl <;> rfl

/-- The seven-state trap is a closed configuration predicate. -/
theorem authorizedTrap_closed :
    PopulationProtocol.ClosedPred authorizedAuditProtocol trapRing
      InAuthorizedTrap := by
  intro C hC C' hstep
  obtain ⟨p, hp, rfl⟩ := hC
  obtain ⟨e, rfl⟩ := hstep
  refine ⟨trapStep p e, trap_closed hp e, ?_⟩
  exact protocolStep_pairConfig p e

/-- The concrete initial configuration belongs to the trap. -/
theorem trapInitial_config_mem : InAuthorizedTrap (pairConfig trapInitial) :=
  ⟨trapInitial, trapInitial_mem, rfl⟩

/-- Every trap configuration has no leader output. -/
theorem authorizedTrap_no_leader {C : Fin 2 → AuthorizedAgentState 2}
    (hC : InAuthorizedTrap C) :
    ∀ i, (C i).core.leader = false := by
  obtain ⟨p, hp, rfl⟩ := hC
  have hn := trap_no_leaders hp
  intro i
  rcases fin2_cases i with rfl | rfl
  · exact hn.1
  · exact hn.2

/-- Every configuration reachable from the witness remains leaderless. -/
theorem trap_reachable_no_leader
    {C : PopulationProtocol.Configuration authorizedAuditProtocol 2}
    (hreach : PopulationProtocol.Reachable authorizedAuditProtocol trapRing
      (pairConfig trapInitial) C) :
    ∀ i, (C i).core.leader = false := by
  have htrap := PopulationProtocol.ClosedPred.reachable authorizedTrap_closed
    trapInitial_config_mem hreach
  exact authorizedTrap_no_leader htrap

/-- No reachable future from the witness satisfies Definition-1 safety: its
unique-leader existence clause already fails. -/
theorem trap_no_semantically_safe_reachable
    {C : PopulationProtocol.Configuration authorizedAuditProtocol 2}
    (hreach : PopulationProtocol.Reachable authorizedAuditProtocol trapRing
      (pairConfig trapInitial) C) :
    ¬PopulationProtocol.IsSafe authorizedAuditProtocol trapRing C
      (fun y => match y with | .leader => true | .follower => false) := by
  intro hsafe
  obtain ⟨i, hi, _⟩ := hsafe.1
  have hn := trap_reachable_no_leader hreach i
  change (match (if (C i).core.leader then LeaderOutput.leader
    else LeaderOutput.follower) with
    | .leader => true | .follower => false) = true at hi
  rw [hn] at hi
  contradiction

end PPLLAuthorizedRepairCounterexample
