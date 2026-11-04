import Leader.Wu.Comparison.MoveFuelRepair

/-!
# Regressions for non-refreshing path fuel

A stage-only four-edge SIGMOVE schedule cycles one path around a `ψ=2,n=4`
ring.  With initial fuel three, the move-fuel repair permits the first three
transfers and clears the fourth attempted wrap, while plain authorized SIGMOVE
returns the path to its start.  A positive stable-wrap fixture shows that useful
movement and the subsequent comparison start remain live and that comparison
state/permission changes do not recharge fuel.
-/

namespace PPLLMoveFuelComparisonRegression

open PPLL PPLLCounterexample PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLMoveFuelComparisonRepair

abbrev fuelRing : DirectedRing 4 := ⟨by omega⟩

private def rawWander0 : AuthorizedAgentState 2 :=
  ⟨{ state2 0 false .depart with path := .some 0 0 }, false⟩
private def rawWander1 : AuthorizedAgentState 2 := ⟨state2 1, false⟩
private def rawWander2 : AuthorizedAgentState 2 := ⟨state2 0, false⟩
private def rawWander3 : AuthorizedAgentState 2 := ⟨state2 1, false⟩

/-- One incomplete comparison component and three empty hosts. -/
def rawWanderConfig : Fin 4 → AuthorizedAgentState 2
  | ⟨0, _⟩ => rawWander0
  | ⟨1, _⟩ => rawWander1
  | ⟨2, _⟩ => rawWander2
  | ⟨3, _⟩ => rawWander3

/-- Four directed transfers complete one physical lap. -/
def rawWanderAfter4 : Fin 4 → AuthorizedAgentState 2 :=
  runLocalSchedule fuelRing (authorizedSigMove (by omega))
    rawWanderConfig [0, 1, 2, 3]

/-- Without non-refreshing fuel, the same physical path returns to position
zero after one lap. -/
theorem raw_sigmove_four_edge_cycle_returns_path :
    (rawWanderAfter4 0).core.path = .some 0 0 ∧
      (rawWanderAfter4 1).core.path = .bot ∧
      (rawWanderAfter4 2).core.path = .bot ∧
      (rawWanderAfter4 3).core.path = .bot := by
  decide

private def fuelState (u : AuthorizedAgentState 2) (f : Fin 4) :
    MoveFuelAuthorizedAgentState 2 3 :=
  ⟨u, f⟩

/-- The moving component starts with three units; arbitrary empty hosts also
start high, but arrival overwrites rather than imports host fuel. -/
def fuelWanderConfig : Fin 4 → MoveFuelAuthorizedAgentState 2 3
  | ⟨0, _⟩ => fuelState rawWander0 3
  | ⟨1, _⟩ => fuelState rawWander1 3
  | ⟨2, _⟩ => fuelState rawWander2 3
  | ⟨3, _⟩ => fuelState rawWander3 3

/-- The same four transfer attempts under move-fuel SIGMOVE. -/
def fuelWanderAfter4 : Fin 4 → MoveFuelAuthorizedAgentState 2 3 :=
  runLocalSchedule fuelRing (moveFuelAuthorizedSigMove (by omega))
    fuelWanderConfig [0, 1, 2, 3]

/-- The fourth attempted transfer sees lineage fuel zero and clears both local
post-SIGMOVE bundles, so no component completes the cycle. -/
theorem moveFuel_blocks_fourth_cycle_edge :
    (fuelWanderAfter4 0).core.core.path = .bot ∧
      (fuelWanderAfter4 1).core.core.path = .bot ∧
      (fuelWanderAfter4 2).core.core.path = .bot ∧
      (fuelWanderAfter4 3).core.core.path = .bot ∧
      (fuelWanderAfter4 0).moveFuel.val = 0 := by
  decide

/-! ## Positive stable wrap and comparison -/

private def positiveMoveLeft : MoveFuelAuthorizedAgentState 2 2 :=
  ⟨⟨{ state2 1 false .depart with path := .some 0 0 }, false⟩, 2⟩

private def positiveMoveRight : MoveFuelAuthorizedAgentState 2 2 :=
  ⟨⟨state2 0 false .depart, false⟩, 2⟩

private def positiveComparisonRight : MoveFuelAuthorizedAgentState 2 2 :=
  ⟨⟨{ state2 1 false .depart with path := .some 1 0 }, false⟩, 0⟩

private def positiveMoved :=
  moveFuelAuthorizedSigMove (by omega : 2 > 0)
    positiveMoveLeft positiveMoveRight

private def positiveCompared :=
  keepFuel (authorizedCompareSig (by omega : 2 > 0))
    positiveMoved.2 positiveComparisonRight

/-- Stable terminal-to-zero movement earns permission with decremented fuel;
COMPARE consumes permission and starts the state wave without changing fuel. -/
theorem moveFuel_wrap_then_starts_comparison :
    positiveMoved.1.core.core.path = .bot ∧
      positiveMoved.1.moveFuel.val = 0 ∧
      positiveMoved.2.core.core.path = .some 0 0 ∧
      positiveMoved.2.core.path0Crossed = true ∧
      positiveMoved.2.moveFuel.val = 1 ∧
      positiveCompared.1.core.core.state = .congest ∧
      positiveCompared.2.core.core.state = .congest ∧
      positiveCompared.1.core.path0Crossed = false ∧
      positiveCompared.1.moveFuel.val = 1 := by
  decide

end PPLLMoveFuelComparisonRegression
