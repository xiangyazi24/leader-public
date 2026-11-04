import Leader.Wu.Comparison.HostAlignedRepair

/-!
# Leaderless class survives host-aligned authorization

Host alignment removes the forged marker from the first repair's seven-state
trap, but it does not clean the reversed complete physical carrier itself. Clear
both permission bits in each of the seven old core states: the host-aligned full
transition has exactly the same closed transition graph, and every state remains
leaderless. Thus stronger authorization normalization succeeds at its narrow
marker-cleanup goal but still cannot establish self-stabilizing leader election
from arbitrary path fields.
-/

namespace PPLLHostAlignedRepairCounterexample

open PPLL PPLLRepair PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLHostAlignedComparisonRepair
open PPLLAuthorizedRepairCounterexample

/-- Erase both authorization values while retaining the exact physical core. -/
def clearAuthorization (u : AuthorizedAgentState 2) : AuthorizedAgentState 2 :=
  ⟨u.core, false⟩

/-- Pairwise authorization erasure. -/
def clearPairAuthorization (p : AuthorizedPair) : AuthorizedPair :=
  (clearAuthorization p.1, clearAuthorization p.2)

/-- Host-aligned full interaction on the two-agent ring. -/
def hostTrapStep (p : AuthorizedPair) (e : Fin 2) : AuthorizedPair :=
  configPair (localStep trapRing
    (ppllHostAlignedRepair (by omega : 2 > 0) 0) (pairConfig p) e)

/-- The seven old physical cores with both authorization bits already clean. -/
def hostTrapState0 := clearPairAuthorization trapState0
def hostTrapState1 := clearPairAuthorization trapState1
def hostTrapState2 := clearPairAuthorization trapState2
def hostTrapState3 := clearPairAuthorization trapState3
def hostTrapState4 := clearPairAuthorization trapState4
def hostTrapState5 := clearPairAuthorization trapState5
def hostTrapState6 := clearPairAuthorization trapState6

/-- Explicit clean-marker leaderless class. -/
def hostTrapStates : List AuthorizedPair :=
  [hostTrapState0, hostTrapState1, hostTrapState2, hostTrapState3,
    hostTrapState4, hostTrapState5, hostTrapState6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem hostTrapState0_edges :
    hostTrapStep hostTrapState0 0 = hostTrapState1 ∧
      hostTrapStep hostTrapState0 1 = hostTrapState2 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem hostTrapState1_edges :
    hostTrapStep hostTrapState1 0 = hostTrapState3 ∧
      hostTrapStep hostTrapState1 1 = hostTrapState2 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem hostTrapState2_edges :
    hostTrapStep hostTrapState2 0 = hostTrapState1 ∧
      hostTrapStep hostTrapState2 1 = hostTrapState2 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem hostTrapState3_edges :
    hostTrapStep hostTrapState3 0 = hostTrapState4 ∧
      hostTrapStep hostTrapState3 1 = hostTrapState5 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem hostTrapState4_edges :
    hostTrapStep hostTrapState4 0 = hostTrapState6 ∧
      hostTrapStep hostTrapState4 1 = hostTrapState5 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem hostTrapState5_edges :
    hostTrapStep hostTrapState5 0 = hostTrapState1 ∧
      hostTrapStep hostTrapState5 1 = hostTrapState5 := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem hostTrapState6_edges :
    hostTrapStep hostTrapState6 0 = hostTrapState1 ∧
      hostTrapStep hostTrapState6 1 = hostTrapState2 := by decide

private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi with hi | hi
  · exact .inl (Fin.ext hi)
  · exact .inr (Fin.ext hi)

private theorem mem_hostTrapState0 : hostTrapState0 ∈ hostTrapStates := by simp [hostTrapStates]
private theorem mem_hostTrapState1 : hostTrapState1 ∈ hostTrapStates := by simp [hostTrapStates]
private theorem mem_hostTrapState2 : hostTrapState2 ∈ hostTrapStates := by simp [hostTrapStates]
private theorem mem_hostTrapState3 : hostTrapState3 ∈ hostTrapStates := by simp [hostTrapStates]
private theorem mem_hostTrapState4 : hostTrapState4 ∈ hostTrapStates := by simp [hostTrapStates]
private theorem mem_hostTrapState5 : hostTrapState5 ∈ hostTrapStates := by simp [hostTrapStates]
private theorem mem_hostTrapState6 : hostTrapState6 ∈ hostTrapStates := by simp [hostTrapStates]

/-- The clean-marker class is closed under both edges. -/
theorem hostTrap_closed {p : AuthorizedPair} (hp : p ∈ hostTrapStates)
    (e : Fin 2) : hostTrapStep p e ∈ hostTrapStates := by
  have hp' : p = hostTrapState0 ∨ p = hostTrapState1 ∨
      p = hostTrapState2 ∨ p = hostTrapState3 ∨ p = hostTrapState4 ∨
      p = hostTrapState5 ∨ p = hostTrapState6 := by
    simpa [hostTrapStates] using hp
  rcases hp' with hp' | hp' | hp' | hp' | hp' | hp' | hp' <;> subst p
  all_goals rcases fin2_cases e with rfl | rfl
  · rw [hostTrapState0_edges.1]; exact mem_hostTrapState1
  · rw [hostTrapState0_edges.2]; exact mem_hostTrapState2
  · rw [hostTrapState1_edges.1]; exact mem_hostTrapState3
  · rw [hostTrapState1_edges.2]; exact mem_hostTrapState2
  · rw [hostTrapState2_edges.1]; exact mem_hostTrapState1
  · rw [hostTrapState2_edges.2]; exact mem_hostTrapState2
  · rw [hostTrapState3_edges.1]; exact mem_hostTrapState4
  · rw [hostTrapState3_edges.2]; exact mem_hostTrapState5
  · rw [hostTrapState4_edges.1]; exact mem_hostTrapState6
  · rw [hostTrapState4_edges.2]; exact mem_hostTrapState5
  · rw [hostTrapState5_edges.1]; exact mem_hostTrapState1
  · rw [hostTrapState5_edges.2]; exact mem_hostTrapState5
  · rw [hostTrapState6_edges.1]; exact mem_hostTrapState1
  · rw [hostTrapState6_edges.2]; exact mem_hostTrapState2

/-- Every class member has both permissions false. -/
theorem hostTrap_authorization_clean {p : AuthorizedPair}
    (hp : p ∈ hostTrapStates) :
    p.1.path0Crossed = false ∧ p.2.path0Crossed = false := by
  have hp' : p = hostTrapState0 ∨ p = hostTrapState1 ∨
      p = hostTrapState2 ∨ p = hostTrapState3 ∨ p = hostTrapState4 ∨
      p = hostTrapState5 ∨ p = hostTrapState6 := by
    simpa [hostTrapStates] using hp
  rcases hp' with hp' | hp' | hp' | hp' | hp' | hp' | hp' <;>
    subst p <;> exact ⟨rfl, rfl⟩

/-- Clearing authorization does not repair the old leaderless cores. -/
theorem hostTrap_no_leaders {p : AuthorizedPair} (hp : p ∈ hostTrapStates) :
    p.1.core.leader = false ∧ p.2.core.leader = false := by
  have hp' : p = hostTrapState0 ∨ p = hostTrapState1 ∨
      p = hostTrapState2 ∨ p = hostTrapState3 ∨ p = hostTrapState4 ∨
      p = hostTrapState5 ∨ p = hostTrapState6 := by
    simpa [hostTrapStates] using hp
  rcases hp' with hp' | hp' | hp' | hp' | hp' | hp' | hp' <;>
    subst p <;> decide

/-- Packaged host-aligned protocol for semantic reachability. -/
def hostAlignedAuditProtocol : PopulationProtocol where
  Q := AuthorizedAgentState 2
  Y := LeaderOutput
  transition := ppllHostAlignedRepair (by omega) 0
  output := fun s => if s.core.leader then .leader else .follower

/-- Configurations represented by the clean-marker trap. -/
def InHostTrap (C : Fin 2 → AuthorizedAgentState 2) : Prop :=
  ∃ p, p ∈ hostTrapStates ∧ C = pairConfig p

/-- Pair stepping agrees with the packaged host-aligned protocol. -/
theorem hostProtocolStep_pairConfig (p : AuthorizedPair) (e : Fin 2) :
    PopulationProtocol.step hostAlignedAuditProtocol trapRing (pairConfig p) e =
      pairConfig (hostTrapStep p e) := by
  funext i
  rcases fin2_cases e with rfl | rfl <;>
    rcases fin2_cases i with rfl | rfl <;> rfl

/-- The host-aligned clean-marker trap is closed. -/
theorem hostAlignedTrap_closed :
    PopulationProtocol.ClosedPred hostAlignedAuditProtocol trapRing
      InHostTrap := by
  intro C hC C' hstep
  obtain ⟨p, hp, rfl⟩ := hC
  obtain ⟨e, rfl⟩ := hstep
  refine ⟨hostTrapStep p e, hostTrap_closed hp e, ?_⟩
  exact hostProtocolStep_pairConfig p e

/-- The first clean-marker state belongs to the trap. -/
theorem hostTrapInitial_mem : InHostTrap (pairConfig hostTrapState0) := by
  exact ⟨hostTrapState0, mem_hostTrapState0, rfl⟩

/-- Every host-trap configuration remains leaderless. -/
theorem hostTrap_config_no_leader {C : Fin 2 → AuthorizedAgentState 2}
    (hC : InHostTrap C) : ∀ i, (C i).core.leader = false := by
  obtain ⟨p, hp, rfl⟩ := hC
  have hn := hostTrap_no_leaders hp
  intro i
  rcases fin2_cases i with rfl | rfl
  · exact hn.1
  · exact hn.2

/-- Every reachable future from the clean-marker witness is leaderless. -/
theorem hostTrap_reachable_no_leader
    {C : PopulationProtocol.Configuration hostAlignedAuditProtocol 2}
    (hreach : PopulationProtocol.Reachable hostAlignedAuditProtocol trapRing
      (pairConfig hostTrapState0) C) :
    ∀ i, (C i).core.leader = false := by
  have htrap := PopulationProtocol.ClosedPred.reachable hostAlignedTrap_closed
    hostTrapInitial_mem hreach
  exact hostTrap_config_no_leader htrap

/-- Host alignment cleans authorization but no reachable future is Definition-1
safe, because the reversed physical carrier remains in a closed leaderless class. -/
theorem hostTrap_no_semantically_safe_reachable
    {C : PopulationProtocol.Configuration hostAlignedAuditProtocol 2}
    (hreach : PopulationProtocol.Reachable hostAlignedAuditProtocol trapRing
      (pairConfig hostTrapState0) C) :
    ¬PopulationProtocol.IsSafe hostAlignedAuditProtocol trapRing C
      (fun y => match y with | .leader => true | .follower => false) := by
  intro hsafe
  obtain ⟨i, hi, _⟩ := hsafe.1
  have hn := hostTrap_reachable_no_leader hreach i
  change (match (if (C i).core.leader then LeaderOutput.leader
    else LeaderOutput.follower) with
    | .leader => true | .follower => false) = true at hi
  rw [hn] at hi
  contradiction

end PPLLHostAlignedRepairCounterexample
