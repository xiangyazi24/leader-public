import Leader.Wu.Comparison.PathStallRepair

/-!
# A circulating carrier defeats path-only stall progress

Path-stall expiration refreshes whenever either the physical path or its
one-shot permission changes.  That criterion excludes state/path2 oscillation,
but physical SIGMOVE itself can cycle.  This file gives an exact `ψ=2,n=4`
cycle under the six-edge period `[0,0,1,2,2,3]`.

The proof is structurally reduced rather than a global state-space search.  One
period from the simple start reaches an explicit literal cycle configuration;
one period from that literal returns exactly to itself.  Induction then proves
persistence for arbitrarily many periods.  The cycle always has one incomplete
path component, so its refreshes are not progress toward a complete comparison.
-/

namespace PPLLPathStallCycleCounterexample

open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair

/-- Initial path holder: CHECK-ready with one earned payload-zero permission. -/
private def wanderAudit0 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false .CHECK_ready with
       path := .some 0 0 }, true⟩

private def wanderAudit1 : AuthorizedAgentState 2 :=
  ⟨PPLLCounterexample.state2 1, false⟩

private def wanderAudit2 : AuthorizedAgentState 2 :=
  ⟨PPLLCounterexample.state2 0, false⟩

private def wanderAudit3 : AuthorizedAgentState 2 :=
  ⟨PPLLCounterexample.state2 1, false⟩

private theorem wanderDomains :
    wanderAudit0.core.inProtocolDomain 0 ∧
      wanderAudit1.core.inProtocolDomain 0 ∧
      wanderAudit2.core.inProtocolDomain 0 ∧
      wanderAudit3.core.inProtocolDomain 0 := by
  simp [wanderAudit0, wanderAudit1, wanderAudit2, wanderAudit3,
    AgentState.inProtocolDomain, PPLLCounterexample.state2]

/-- Reify one audit state with the single static-opportunity budget. -/
private def liftWander (u : AuthorizedAgentState 2)
    (hu : u.core.inProtocolDomain 0) : ExpiringAgentState 2 0 1 :=
  ⟨⟨BoundedAgentState.ofDomain u.core hu, u.path0Crossed⟩,
    freshStall 1⟩

abbrev wanderRing : DirectedRing 4 := ⟨by omega⟩

/-- Four-agent start with exactly one comparison path component. -/
def wanderConfig : Fin 4 → ExpiringAgentState 2 0 1
  | ⟨0, _⟩ => liftWander wanderAudit0 wanderDomains.1
  | ⟨1, _⟩ => liftWander wanderAudit1 wanderDomains.2.1
  | ⟨2, _⟩ => liftWander wanderAudit2 wanderDomains.2.2.1
  | ⟨3, _⟩ => liftWander wanderAudit3 wanderDomains.2.2.2

/-- Two static CHECK pauses interleaved with four rightward path transfers. -/
def wanderPeriod : DetSchedule 4 := [0, 0, 1, 2, 2, 3]

/-- Deterministic action of one circulating period. -/
def wanderPeriodMap
    (C : Fin 4 → ExpiringAgentState 2 0 1) :
    Fin 4 → ExpiringAgentState 2 0 1 :=
  runLocalSchedule wanderRing
    (pathStallTransition (by omega) 0 1) C wanderPeriod

/-- First period from the neutral start. -/
def wanderAfterPeriod : Fin 4 → ExpiringAgentState 2 0 1 :=
  wanderPeriodMap wanderConfig

/-! ## Explicit recurrent state

Only WAIT/cleaning/write bookkeeping changes during the first period.  Naming
its settled values makes the recurrent certificate small: subsequent checking
compares one six-edge period from a literal state, not nested iteration terms.
-/

private def cycleAudit0 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false .CHECK_ready with
       wait := false, path := .some 0 0, reset := true,
       path5 := some (0, 1), write_state := .depart }, true⟩

private def cycleAudit1 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 with h_field := true }, false⟩

private def cycleAudit2 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 with wait := false }, false⟩

private def cycleAudit3 : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 with h_field := true }, false⟩

private theorem cycleDomains :
    cycleAudit0.core.inProtocolDomain 0 ∧
      cycleAudit1.core.inProtocolDomain 0 ∧
      cycleAudit2.core.inProtocolDomain 0 ∧
      cycleAudit3.core.inProtocolDomain 0 := by
  simp [cycleAudit0, cycleAudit1, cycleAudit2, cycleAudit3,
    AgentState.inProtocolDomain, PPLLCounterexample.state2]

/-- Literal full configuration reached after the one-period prelude. -/
def wanderCycleConfig : Fin 4 → ExpiringAgentState 2 0 1
  | ⟨0, _⟩ => liftWander cycleAudit0 cycleDomains.1
  | ⟨1, _⟩ => liftWander cycleAudit1 cycleDomains.2.1
  | ⟨2, _⟩ => liftWander cycleAudit2 cycleDomains.2.2.1
  | ⟨3, _⟩ => liftWander cycleAudit3 cycleDomains.2.2.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The simple start reaches the explicit recurrent state in one period. -/
theorem wander_first_period_reaches_cycle :
    wanderAfterPeriod = wanderCycleConfig := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- One full period returns the complete finite physical configuration—not just
its comparison projection—to itself. -/
theorem wander_cycle_period_fixed :
    wanderPeriodMap wanderCycleConfig = wanderCycleConfig := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;> decide

/-- Repeat the fixed six-edge period a specified number of times. -/
def wanderPeriods : Nat → (Fin 4 → ExpiringAgentState 2 0 1)
  | 0 => wanderConfig
  | k + 1 => wanderPeriodMap (wanderPeriods k)

/-- After the first period, every later period endpoint is the same exact
physical cycle state.  The proof is induction from the two reduced certificates
above, not finite-state enumeration. -/
theorem wander_periods_succ_eq_cycle (k : Nat) :
    wanderPeriods (k + 1) = wanderCycleConfig := by
  induction k with
  | zero => exact wander_first_period_reaches_cycle
  | succ k ih =>
      change wanderPeriodMap (wanderPeriods (k + 1)) = wanderCycleConfig
      rw [ih, wander_cycle_period_fixed]

/-- Every positive number of periods leaves exactly one incomplete comparison
component at position zero with a freshly restored budget and permission. -/
theorem wander_incomplete_carrier_persists (k : Nat) :
    let C := wanderPeriods (k + 1)
    (C 0).core.core.path = .some 0 0 ∧
      (C 0).core.core.state = .CHECK_ready ∧
      (C 0).core.path0Crossed = true ∧
      (C 0).stall.val = 1 ∧
      (C 1).core.core.path = .bot ∧
      (C 2).core.core.path = .bot ∧
      (C 3).core.core.path = .bot := by
  rw [wander_periods_succ_eq_cycle]
  decide

end PPLLPathStallCycleCounterexample
