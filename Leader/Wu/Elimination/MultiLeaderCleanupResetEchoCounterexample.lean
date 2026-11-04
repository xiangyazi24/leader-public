import Leader.Wu.Elimination.MultiLeaderCleanupResetFreeBridge
import Leader.Wu.Safety.NoCheckBirthConditionTwoProtocol

/-!
# Reset/echo obstruction for the corrected multi-leader repair tail

The pointwise directional predicate `reset_cmd = false ∨ echo = true` is not
preserved by the literal cleanup word.  This file records the exact Algorithm
14 recurrence and a smallest closed schedule-level counterexample.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace ResetEchoCounterexample

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  PPLLWallSweepRepair
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol
  PPLLNoCheckBirthConditionTwoGeometry

set_option autoImplicit false

variable {psi : Nat}

/-- The complete reset/echo truth table of repaired Algorithm 14 when the
initiator is a follower. -/
theorem suppressSigResetKill_follower_resetEcho_exact
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) :
    let q := suppressSigResetKill hpsi l r
    q.1.reset_cmd = false ∧
      q.2.echo = false ∧
      q.2.reset_cmd =
        (!r.echo && (l.reset_cmd || r.reset_cmd)) ∧
      q.1.echo =
        (l.echo ||
          (decide (r.label = ⟨psi - 1, by omega⟩) &&
            (l.reset_cmd || r.reset_cmd)) ||
          (r.echo && !(l.reset_cmd || r.reset_cmd))) := by
  dsimp only
  cases hlr : l.reset_cmd <;>
  cases hrr : r.reset_cmd <;>
  cases hre : r.echo <;>
  by_cases hlast : r.label = ⟨psi - 1, by omega⟩ <;>
    simp [suppressSigResetKill, suppressSigStart,
      suppressSigMoveReset, resetKillComparison,
      clearComparisonSignal, suppressSigTerminal,
      suppressSigEcho, suppressSigFinish,
      hl, hlr, hrr, hre, hlast]

/-- The tempting but false directional predicate. -/
def ResetEchoDirectional (u : AgentState psi) : Prop :=
  u.reset_cmd = false ∨ u.echo = true

/-- A follower initiator always satisfies the directional predicate after
Algorithm 14. -/
theorem suppressSigResetKill_follower_left_directional
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) :
    ResetEchoDirectional (suppressSigResetKill hpsi l r).1 := by
  left
  exact (suppressSigResetKill_follower_resetEcho_exact
    hpsi l r hl).1

/-- The responder satisfies the predicate exactly when its incoming echo
cancels every reset or neither endpoint supplied a reset. -/
theorem suppressSigResetKill_follower_right_directional_iff
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) :
    ResetEchoDirectional (suppressSigResetKill hpsi l r).2 ↔
      r.echo = true ∨
        (l.reset_cmd = false ∧ r.reset_cmd = false) := by
  cases hlr : l.reset_cmd <;>
  cases hrr : r.reset_cmd <;>
  cases hre : r.echo <;>
    simp [ResetEchoDirectional, suppressSigResetKill,
      suppressSigStart, suppressSigMoveReset,
      resetKillComparison, clearComparisonSignal,
      suppressSigTerminal, suppressSigEcho,
      suppressSigFinish, hl, hlr, hrr, hre]

/-- Exact input-side branch whose responder output satisfies the directional
predicate after a follower interaction. -/
def RepairTailResetBranch (l r : AgentState psi) : Prop :=
  r.echo = true ∨
    (l.reset_cmd = false ∧ r.reset_cmd = false)

/-- The exact reset branch is closed from one follower edge to the next once
it has been seeded on both adjacent input pairs. -/
theorem RepairTailResetBranch.next_of_follower
    (hpsi : psi > 0) (l r s : AgentState psi)
    (hl : l.leader = false)
    (hcurrent : RepairTailResetBranch l r)
    (hnext : RepairTailResetBranch r s) :
    RepairTailResetBranch
      (suppressSigResetKill hpsi l r).2 s := by
  have hexact :=
    suppressSigResetKill_follower_resetEcho_exact
      hpsi l r hl
  have hrReset :
      (suppressSigResetKill hpsi l r).2.reset_cmd = false := by
    rcases hcurrent with hrEcho | ⟨hlReset, hrReset⟩
    · simpa [hrEcho] using hexact.2.2.1
    · simpa [hlReset, hrReset] using hexact.2.2.1
  rcases hnext with hsEcho | ⟨_, hsReset⟩
  · exact Or.inl hsEcho
  · exact Or.inr ⟨hrReset, hsReset⟩

private theorem hTwo : 2 > 0 := by omega

private def ring4 : DirectedRing 4 := ⟨by omega⟩

private def leaders4 (i : Fin 4) : Bool :=
  decide (i.val = 0 ∨ i.val = 2)

/-- Stable labels 0,1,0,1; shielded leaders at 0 and 2; every other raw
field is the canonical `PeaceView.toState` default. -/
private def baseView4 (i : Fin 4) : PeaceView 2 :=
  { leader := leaders4 i
    label := ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩
    shield := leaders4 i
    bullet := 0
    signal_B := 0 }

private def baseCore4 (i : Fin 4) : AgentState 2 :=
  PeaceView.toState (baseView4 i)

private theorem baseCore4_domain (i : Fin 4) :
    (baseCore4 i).inProtocolDomain 0 := by
  simp [baseCore4, baseView4, PeaceView.toState,
    AgentState.inProtocolDomain]

private def input4 (i : Fin 4) : ExpiringAgentState 2 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain
      (baseCore4 i) (baseCore4_domain i), false⟩,
    ⟨0, by omega⟩⟩

private def plan4 : SegmentCleanupPlan ring4 where
  pred := 0
  victim := 2
  source := 0
  pred_ne_victim := by decide
  victim_ne_source := by decide
  dPV := 2
  dVS := 2
  dPV_eq := by decide
  dVS_eq := by decide
  dPV_pos := by omega
  dVS_pos := by omega
  dPV_lt := by omega
  dVS_lt := by omega
  dPV_nonadjacent := by omega
  dVS_nonadjacent := by omega

private abbrev T4 :
    ExpiringAgentState 2 0 0 →
    ExpiringAgentState 2 0 0 →
    ExpiringAgentState 2 0 0 × ExpiringAgentState 2 0 0 :=
  multiLeaderCleanupTransition hTwo 0 0

private def wordOut4 : Fin 4 → ExpiringAgentState 2 0 0 :=
  runLocalSchedule ring4 T4 input4 plan4.word

/-- State after the first repair-tail edge, `1 -> 2`. Position 3 has not yet
been visited by the tail. -/
private def afterFirstRepair4 :
    Fin 4 → ExpiringAgentState 2 0 0 :=
  localStep ring4 T4 wordOut4 (1 : Fin 4)

/-- The two-edge repair tail is `[1,2]`; its second edge `2 -> 3` is position
3's first repair-tail visit. -/
private def afterFirstVisitOf3 :
    Fin 4 → ExpiringAgentState 2 0 0 :=
  runLocalSchedule ring4 T4 wordOut4 plan4.repairTail

theorem plan4_literal_words :
    plan4.word =
        ([0, 1, 1, 2, 3, 0, 3, 2] : List (Fin 4)) ∧
      plan4.repairTail =
        ([1, 2] : List (Fin 4)) := by
  decide

/-- The literal physical word leaves the first clockwise victim follower in
the forbidden reset/echo state. -/
theorem plan4_word_output_refutes_directional :
    (wordOut4 3).core.erase.core.reset_cmd = true ∧
      (wordOut4 3).core.erase.core.echo = false ∧
      ¬ ((wordOut4 3).core.erase.core.reset_cmd = false ∨
         (wordOut4 3).core.erase.core.echo = true) := by
  set_option maxRecDepth 100000 in
    decide

/-- The first repair edge does not touch position 3, so the obstruction is
still present immediately before its first repair-tail visit. -/
theorem plan4_bad_until_first_visit :
    (afterFirstRepair4 3).core.erase.core.reset_cmd = true ∧
      (afterFirstRepair4 3).core.erase.core.echo = false ∧
      ¬ ((afterFirstRepair4 3).core.erase.core.reset_cmd = false ∨
         (afterFirstRepair4 3).core.erase.core.echo = true) ∧
      ring4.rightNeighbor (2 : Fin 4) = 3 := by
  set_option maxRecDepth 100000 in
    decide

/-- The first visit itself does not repair the disjunction: reset is handed
from position 2 into the already reset, echo-free responder at position 3. -/
theorem plan4_bad_after_first_visit :
    (afterFirstVisitOf3 3).core.erase.core.reset_cmd = true ∧
      (afterFirstVisitOf3 3).core.erase.core.echo = false ∧
      ¬ ((afterFirstVisitOf3 3).core.erase.core.reset_cmd = false ∨
         (afterFirstVisitOf3 3).core.erase.core.echo = true) := by
  set_option maxRecDepth 100000 in
    decide

end ResetEchoCounterexample
end PPLLCompleteMultiLeaderCleanup
