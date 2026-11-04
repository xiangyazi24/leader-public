import Leader.Wu.Safety.OperationalLegitimacy

/-!
# Trace-level convergence phases for finite proof refinements

Historical events such as “received a reset command” are properties of an
execution prefix, not snapshots of Algorithm 14's moving `reset_cmd` token.
This module gives exact finite-uniform semantics for arbitrary finite local
transitions and certifies the first nontrivial historical-receipt phase on the
smallest non-self ring.

The concrete certificate is intentionally tiny: it is a semantic regression
for the corrected formulation, not a scalable version of Lemma 4.1.7 or
Theorem 4.1.13.
-/

namespace PPLLTraceConvergence

open PPLL PPLLRepair PPLLCounterexample PPLLResearchFormulation

/-! ## Generic exact finite phase semantics -/

/-- Whether an arbitrary finite-state local transition visits a Boolean target
initially or along a fixed edge schedule. -/
def hitsWithinLocal {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q) (post : (Fin n → Q) → Bool) :
    (Fin n → Q) → DetSchedule n → Bool
  | C, [] => post C
  | C, e :: rest =>
      post C || hitsWithinLocal ring T post (localStep ring T C e) rest

/-- Number of length-`t` uniform edge schedules that visit a finite-state phase
target. -/
def localHitCount {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q) (post : (Fin n → Q) → Bool)
    (C : Fin n → Q) (t : Nat) : Nat :=
  (allSchedules n t).countP (hitsWithinLocal ring T post C)

/-- Exact rational phase-hit probability under independent uniform edge
choices. -/
def localHitProbability {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q) (post : (Fin n → Q) → Bool)
    (C : Fin n → Q) (t : Nat) : Rat :=
  (localHitCount ring T post C t : Rat) /
    ((allSchedules n t).length : Nat)

/-- Semantic finite phase certificate.  The Boolean test must decide the stated
postcondition, and every pre-state must have enough favorable schedules to
fit the explicit failure-outcome budget. -/
def UniformFinitePhase {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q)
    (Pre Post : (Fin n → Q) → Prop)
    (postTest : (Fin n → Q) → Bool) (t allowedFailures : Nat) : Prop :=
  (∀ C, postTest C = true ↔ Post C) ∧
  ∀ C, Pre C →
    (allSchedules n t).length ≤
      localHitCount ring T postTest C t + allowedFailures

/-! ## Concrete two-agent historical reset receipt -/

/-- Smallest non-self operational regime, with two agents and two labels. -/
theorem regimeTwoTwo : OperationalRegime 2 2 :=
  operationalRegime_of (by omega) (by omega)

private theorem suppressionCounterConfig_inDomain :
    ∀ i, (suppressionCounterConfig i).inProtocolDomain 10 := by
  intro i
  have hi : i = 0 ∨ i = 1 := by
    have := i.isLt
    omega
  rcases hi with hi | hi <;> subst i <;>
    simp [AgentState.inProtocolDomain, suppressionCounterConfig, state2]

/-- Reification of the concrete leader/follower start into the physical finite
carrier. -/
def receiptPhysicalStart : Fin 2 → BoundedAgentState 2 10 := fun i =>
  BoundedAgentState.ofDomain (suppressionCounterConfig i)
    (suppressionCounterConfig_inDomain i)

/-- Canonical phase-origin lift: physical state is unchanged and no receipt is
credited before the phase begins. -/
def receiptRefinedStart :
    Fin 2 → PPLLSuppressionHistory.BoundedReceiptAgentState 2 10 :=
  freshReceiptConfig receiptPhysicalStart

/-- Historical-receipt state after selecting the leader's outgoing edge. -/
def receiptAfterLeaderEdge :
    Fin 2 → PPLLSuppressionHistory.BoundedReceiptAgentState 2 10 :=
  localStep regimeTwoTwo.ring
    (PPLLSuppressionHistory.boundedTransition regimeTwoTwo.hψ 10)
    receiptRefinedStart 0

/-- The integrated prefix preserves the initiator leader on the concrete start,
so Algorithm 14's reset passes through both endpoints. -/
private theorem receiptStart_preSuppress_leader :
    (ppllIntegratedBeforeSuppress regimeTwoTwo.hψ 10
      (BoundedAgentState.erase (receiptRefinedStart 0).concrete)
      (BoundedAgentState.erase (receiptRefinedStart 1).concrete)).1.leader =
      true := by
  decide

/-- One selection of edge `0→1` records historical receipt at both agents. -/
theorem receiptAfterLeaderEdge_allReceived :
    AllReceivedReset receiptAfterLeaderEdge := by
  intro i
  have hi : i = 0 ∨ i = 1 := by
    have := i.isLt
    omega
  rcases hi with hi | hi <;> subst i <;> decide

/-- Boolean decision procedure for historical receipt on the two-agent ring. -/
def allReceivedResetTest
    (C : Fin 2 → PPLLSuppressionHistory.BoundedReceiptAgentState 2 10) : Bool :=
  (C 0).receivedReset && (C 1).receivedReset

/-- The concrete Boolean test exactly decides the trace-history predicate. -/
theorem allReceivedResetTest_decides
    (C : Fin 2 → PPLLSuppressionHistory.BoundedReceiptAgentState 2 10) :
    allReceivedResetTest C = true ↔ AllReceivedReset C := by
  constructor
  · intro h i
    have hi : i = 0 ∨ i = 1 := by
      have := i.isLt
      omega
    rcases hi with hi | hi <;> subst i
    · simpa [allReceivedResetTest] using Bool.and_eq_true_iff.mp h |>.1
    · simpa [allReceivedResetTest] using Bool.and_eq_true_iff.mp h |>.2
  · intro h
    simp [allReceivedResetTest, h 0, h 1]

/-- Exactly one of the two one-edge schedules selects the leader's outgoing
edge and reaches historical suppression. -/
theorem receiptPhase_hitCount :
    localHitCount regimeTwoTwo.ring
      (PPLLSuppressionHistory.boundedTransition regimeTwoTwo.hψ 10)
      allReceivedResetTest receiptRefinedStart 1 = 1 := by
  decide

/-- The corrected concrete phase has exact one-step success probability
`1/2`, unlike the old zero-probability transient-token target. -/
theorem receiptPhase_hitProbability :
    localHitProbability regimeTwoTwo.ring
      (PPLLSuppressionHistory.boundedTransition regimeTwoTwo.hψ 10)
      allReceivedResetTest receiptRefinedStart 1 = (1 : Rat) / 2 := by
  unfold localHitProbability
  rw [receiptPhase_hitCount, allSchedules_length]
  rfl

/-- Singleton initial predicate for the concrete phase regression. -/
def ReceiptPhasePre
    (C : Fin 2 → PPLLSuppressionHistory.BoundedReceiptAgentState 2 10) : Prop :=
  C = receiptRefinedStart

/-- The first genuinely semantic historical-receipt phase certificate. Its
failure budget is one of the two uniform one-edge outcomes. -/
theorem receiptPhase_semantically_valid :
    UniformFinitePhase regimeTwoTwo.ring
      (PPLLSuppressionHistory.boundedTransition regimeTwoTwo.hψ 10)
      ReceiptPhasePre AllReceivedReset allReceivedResetTest 1 1 := by
  constructor
  · exact allReceivedResetTest_decides
  · intro C hC
    subst C
    rw [allSchedules_length, receiptPhase_hitCount]
    decide

/-- Once historical suppression is reached, every subsequent refined protocol
step preserves it. -/
theorem receiptPhase_post_preserved
    (C : Fin 2 → PPLLSuppressionHistory.BoundedReceiptAgentState 2 10)
    (hC : AllReceivedReset C) (e : Fin 2) :
    AllReceivedReset
      ((receiptProtocol regimeTwoTwo 10).step regimeTwoTwo.ring C e) :=
  allReceivedReset_preserved_step regimeTwoTwo 10 C hC e

end PPLLTraceConvergence
