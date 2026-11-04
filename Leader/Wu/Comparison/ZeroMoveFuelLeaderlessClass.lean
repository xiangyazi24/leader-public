import Leader.Wu.Comparison.MoveFuelPotential
import Leader.Wu.Comparison.AuthorizedRepairCounterexample

/-!
# Closed leaderless class for zero-initialized move fuel

The non-refreshing fuel layer does not repair the predecessor authorization
trap when all fuel values are zero.  On each of the seven certified authorized
cores and both two-agent edges, the complete fuel-aware interaction has exactly
the old authorized core successor and keeps both fuel values zero.

Thus the seven-state leaderless class lifts unchanged to the move-fuel protocol.
This is a terminal arbitrary-initialization counterexample for the current fuel
design: canonical positive birth fuel is not merely an omitted proof, while an
unaccounted refill would invalidate the global nonincreasing potential.
-/

namespace PPLLMoveFuelCounterexample

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLAuthorizedRepairCounterexample PPLLMoveFuelComparisonRepair
  PPLLMoveFuelPotential

abbrev ZeroFuelPair :=
  MoveFuelAuthorizedAgentState 2 0 × MoveFuelAuthorizedAgentState 2 0

/-- Attach the only `Fin 1` fuel value to both cores of an authorized trap
state. -/
def liftAuthorizedTrapPair (p : AuthorizedPair) : ZeroFuelPair :=
  (⟨p.1, zeroMoveFuel 0⟩, ⟨p.2, zeroMoveFuel 0⟩)

/-- Decode a zero-fuel pair as a two-agent configuration. -/
def zeroFuelPairConfig (p : AuthorizedPair) :
    Fin 2 → MoveFuelAuthorizedAgentState 2 0
  | ⟨0, _⟩ => (liftAuthorizedTrapPair p).1
  | ⟨1, _⟩ => (liftAuthorizedTrapPair p).2

/-- Recover authorized cores from a two-agent move-fuel configuration. -/
def zeroFuelConfigCorePair
    (C : Fin 2 → MoveFuelAuthorizedAgentState 2 0) : AuthorizedPair :=
  ((C 0).core, (C 1).core)

/-- One full move-fuel interaction, projected back to its authorized core pair. -/
def zeroFuelTrapStep (p : AuthorizedPair) (e : Fin 2) : AuthorizedPair :=
  zeroFuelConfigCorePair
    (localStep trapRing
      (moveFuelAuthorizedRepair (by omega : 2 > 0) 0)
      (zeroFuelPairConfig p) e)

private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have hi : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi with hi | hi
  · exact .inl (Fin.ext hi)
  · exact .inr (Fin.ext hi)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- On all fourteen outgoing certified edges, zero-fuel execution has exactly
the old authorized core transition. -/
theorem zeroFuelTrapStep_eq_authorized
    {p : AuthorizedPair} (hp : p ∈ trapStates) (e : Fin 2) :
    zeroFuelTrapStep p e = trapStep p e := by
  have hp' : p = trapState0 ∨ p = trapState1 ∨ p = trapState2 ∨
      p = trapState3 ∨ p = trapState4 ∨ p = trapState5 ∨
      p = trapState6 := by
    simpa [trapStates] using hp
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin2_cases e with rfl | rfl <;> decide

/-- Both output fuels remain zero on every lifted trap edge. -/
theorem zeroFuelTrapStep_fuels_zero
    (p : AuthorizedPair) (e : Fin 2) :
    AllMoveFuelZero
      (localStep trapRing
        (moveFuelAuthorizedRepair (by omega : 2 > 0) 0)
        (zeroFuelPairConfig p) e) := by
  apply allMoveFuelZero_localStep
  intro i
  rcases fin2_cases i with rfl | rfl <;> rfl

/-- Packaged audit protocol for the zero-fuel counterexample. -/
def zeroFuelAuditProtocol : PopulationProtocol where
  Q := MoveFuelAuthorizedAgentState 2 0
  Y := LeaderOutput
  transition := moveFuelAuthorizedRepair (by omega) 0
  output := fun s => if s.core.core.leader then .leader else .follower

/-- Configurations represented by one of the seven authorized trap cores with
zero fuel attached at both positions. -/
def InZeroFuelTrap
    (C : Fin 2 → MoveFuelAuthorizedAgentState 2 0) : Prop :=
  ∃ p, p ∈ trapStates ∧ C = zeroFuelPairConfig p

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- One packaged protocol step agrees with lifting the old authorized trap
successor. -/
theorem zeroFuelProtocolStep_pairConfig
    (p : AuthorizedPair) (hp : p ∈ trapStates) (e : Fin 2) :
    PopulationProtocol.step zeroFuelAuditProtocol trapRing
        (zeroFuelPairConfig p) e =
      zeroFuelPairConfig (trapStep p e) := by
  change localStep trapRing
    (moveFuelAuthorizedRepair (by omega : 2 > 0) 0)
      (zeroFuelPairConfig p) e = zeroFuelPairConfig (trapStep p e)
  have hp' : p = trapState0 ∨ p = trapState1 ∨ p = trapState2 ∨
      p = trapState3 ∨ p = trapState4 ∨ p = trapState5 ∨
      p = trapState6 := by
    simpa [trapStates] using hp
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin2_cases e with rfl | rfl <;>
    funext i <;> rcases fin2_cases i with rfl | rfl <;> decide

/-- The lifted seven-state class is closed under the full move-fuel protocol. -/
theorem zeroFuelTrap_closed :
    PopulationProtocol.ClosedPred zeroFuelAuditProtocol trapRing
      InZeroFuelTrap := by
  intro C hC C' hstep
  obtain ⟨p, hp, rfl⟩ := hC
  obtain ⟨e, rfl⟩ := hstep
  refine ⟨trapStep p e, trap_closed hp e, ?_⟩
  exact zeroFuelProtocolStep_pairConfig p hp e

/-- The lifted initial authorized trap belongs to the zero-fuel class. -/
theorem zeroFuelTrapInitial_mem :
    InZeroFuelTrap (zeroFuelPairConfig trapInitial) :=
  ⟨trapInitial, trapInitial_mem, rfl⟩

/-- Every lifted trap state remains leaderless. -/
theorem zeroFuelTrap_no_leader
    {C : Fin 2 → MoveFuelAuthorizedAgentState 2 0}
    (hC : InZeroFuelTrap C) :
    ∀ i, (C i).core.core.leader = false := by
  obtain ⟨p, hp, rfl⟩ := hC
  have hn := trap_no_leaders hp
  intro i
  rcases fin2_cases i with rfl | rfl
  · exact hn.1
  · exact hn.2

/-- Every configuration reachable from the lifted witness is leaderless. -/
theorem zeroFuelTrap_reachable_no_leader
    {C : PopulationProtocol.Configuration zeroFuelAuditProtocol 2}
    (hreach : PopulationProtocol.Reachable zeroFuelAuditProtocol trapRing
      (zeroFuelPairConfig trapInitial) C) :
    ∀ i, (C i).core.core.leader = false := by
  have htrap := PopulationProtocol.ClosedPred.reachable zeroFuelTrap_closed
    zeroFuelTrapInitial_mem hreach
  exact zeroFuelTrap_no_leader htrap

/-- No reachable future from the zero-fuel witness is Definition-1 safe. -/
theorem zeroFuelTrap_no_semantically_safe_reachable
    {C : PopulationProtocol.Configuration zeroFuelAuditProtocol 2}
    (hreach : PopulationProtocol.Reachable zeroFuelAuditProtocol trapRing
      (zeroFuelPairConfig trapInitial) C) :
    ¬PopulationProtocol.IsSafe zeroFuelAuditProtocol trapRing C
      isLeaderOutput := by
  intro hsafe
  obtain ⟨i, hi, _⟩ := hsafe.1
  have hn := zeroFuelTrap_reachable_no_leader hreach i
  change isLeaderOutput
    (if (C i).core.core.leader then LeaderOutput.leader
      else LeaderOutput.follower) = true at hi
  rw [hn] at hi
  contradiction

end PPLLMoveFuelCounterexample
