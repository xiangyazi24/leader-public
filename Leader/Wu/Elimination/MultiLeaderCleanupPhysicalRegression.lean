import Leader.Wu.Elimination.MultiLeaderCleanupFullWordDescent
import Leader.Wu.Elimination.MultiLeaderCleanupResetFreeSweep

/-!
# Three-leader physical cleanup regression

The four-agent regression exercises only the exact-two base case.  This file
checks a genuine three-leader selected segment through the complete finite
expiring transition.  It guards both the general raw trace and the hidden
prefix-readiness bridge on one nontrivial instance.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PhysicalRegression

open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol
  PPLLNoCheckBirthConditionTwoGeometry
  PPLLWallSweepFiniteCleanup
  PPLLWallSweepClockwiseScheduler
open PhysicalBridge

private theorem hThree : 3 > 0 := by omega

private theorem ring6 : DirectedRing 6 := ⟨by omega⟩

private def leaders024 (i : Fin 6) : Bool :=
  decide (i.val = 0 ∨ i.val = 2 ∨ i.val = 4)

private def inputView (i : Fin 6) : PeaceView 3 :=
  { leader := leaders024 i
    label := ⟨i.val % 2, by omega⟩
    shield := leaders024 i
    bullet := 0
    signal_B := 0 }

private def rawInput (i : Fin 6) : AgentState 3 :=
  PeaceView.toState (inputView i)

private def plan024 : SegmentCleanupPlan ring6 where
  pred := 0
  victim := 2
  source := 4
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

private theorem rawInput_inProtocolDomain (i : Fin 6) :
    (rawInput i).inProtocolDomain 0 := by
  simp [rawInput, inputView, PeaceView.toState,
    AgentState.inProtocolDomain]

private def physicalInput : EConfig 6 3 0 16 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain (rawInput i)
      (rawInput_inProtocolDomain i), false⟩,
    freshStall 16⟩

private theorem smallOffsetCases {k : Nat} (hk : k ≤ 2) :
    k = 0 ∨ k = 1 ∨ k = 2 := by omega

private theorem fin6Cases (i : Fin 6) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  omega

private theorem plan024_word :
    plan024.word = [0, 1, 1, 2, 3, 4, 3, 2] := by
  decide

theorem rawInput_segmentReady :
    SegmentCleanupReady hThree ring6 plan024 rawInput := by
  refine
    { pred_leader := by decide
      victim_leader := by decide
      source_leader := by decide
      source_outgoing_follower := by decide
      pred_zero := by decide
      victim_zero := by decide
      source_zero := by decide
      pred_shielded := by decide
      victim_shielded := by decide
      source_shielded := by decide
      bullets_zero := by intro i; rfl
      arcPV_signals_zero := ?_
      arcVS_signals_zero := ?_
      arcPV_followers := ?_
      arcVS_followers := ?_
      arcPV_aligned := ?_
      arcVS_aligned := ?_ }
  · intro k hk
    rcases smallOffsetCases hk with rfl | rfl | rfl <;> decide
  · intro k hk
    rcases smallOffsetCases hk with rfl | rfl | rfl <;> decide
  · intro k hk0 hk2
    change k < 2 at hk2
    have : k = 1 := by omega
    subst k
    decide
  · intro k hk0 hk2
    change k < 2 at hk2
    have : k = 1 := by omega
    subst k
    decide
  · intro k hk
    change k + 1 < 2 at hk
    have : k = 0 := by omega
    subst k
    decide
  · intro k hk
    change k + 1 < 2 at hk
    have : k = 0 := by omega
    subst k
    decide

/-- The complete transition satisfies its hidden readiness contract at every
prefix of a genuine three-leader kill word. -/
theorem physicalInput_readyAlong :
    MultiLeaderCleanupPhysicalReadyAlong
      hThree 0 16 ring6 physicalInput plan024.word := by
  rw [plan024_word]
  simp only [MultiLeaderCleanupPhysicalReadyAlong]
  repeat' apply And.intro
  all_goals
    first
    | exact True.intro
    | refine
        { priority_open := by decide +kernel
          reset_ppsi_route := by decide +kernel
          left_idle := by constructor <;> decide +kernel
          right_idle := by constructor <;> decide +kernel
          responder_zero := by decide +kernel }

/-- The actual finite expiring transition deletes one of three leaders. -/
theorem physicalInput_word_count_lt :
    let D := runLocalSchedule ring6
      (multiLeaderCleanupTransition hThree 0 16)
      physicalInput plan024.word
    rawPhysicalLeaderCount (eraseExpiringCleanupConfig D) <
      rawPhysicalLeaderCount (eraseExpiringCleanupConfig physicalInput) := by
  exact PPLLCompleteMultiLeaderCleanup.PhysicalBridge.SegmentCleanupReady.expiringPhysicalLeaderCount_lt_of_readyAlong
    hThree 0 16 ring6 plan024 physicalInput
    rawInput_segmentReady physicalInput_readyAlong

private def physicalFullOutput : EConfig 6 3 0 16 :=
  plan024.physicalFullOutput hThree 0 16 physicalInput

/-- The successful three-leader kill word does not leave the incoming follower
as a reset source.  Hence the existing reset-token repair-tail theorem cannot
be the general producer for this canonical execution; the literal tail repairs
the barrier through a different reset-free/P-prime branch. -/
theorem physicalWord_predIncoming_reset_false :
    ((plan024.physicalWordOutput hThree 0 16 physicalInput)
      plan024.predIncoming).core.erase.core.reset_cmd = false := by
  decide +kernel

/-- The corrected kill-and-repair word retains the same strict count descent
on the complete finite transition. -/
theorem physicalInput_fullWord_count_lt :
    rawPhysicalLeaderCount
        (eraseExpiringCleanupConfig physicalFullOutput) <
      rawPhysicalLeaderCount
        (eraseExpiringCleanupConfig physicalInput) := by
  decide +kernel

/-- The full merged-follower repair tail restores `noFreeBarrier` in the
three-leader complete-transition fixture. -/
theorem physicalInput_fullWord_noFreeBarrier :
    noFreeBarrier hThree ring6
      (eraseExpiringCleanupConfig physicalFullOutput) := by
  intro i
  rcases fin6Cases i with h | h | h | h | h | h <;> subst i
  all_goals dsimp only
  all_goals intro hbarrier
  all_goals
    simp only [isBarrier, AgentState.isLeader] at hbarrier ⊢
  all_goals
    first
    | exact (by decide +kernel)
    | exfalso
      revert hbarrier
      decide +kernel

private def physicalTailOne : EConfig 6 3 0 16 :=
  runLocalSchedule ring6
    (multiLeaderCleanupTransition hThree 0 16)
    (plan024.physicalWordOutput hThree 0 16 physicalInput)
    [plan024.predIncoming]

-- The statement's `by omega` bound elaborates against the concrete trace;
-- that elaboration needs a deeper recursion budget than the default.
set_option maxRecDepth 2048 in
/-- The first literal repair interaction is genuinely reset-free and installs
the missing successor label while preserving both follower bits. -/
theorem physicalInput_firstRepairEdge_resetFree_alignment :
    let B := plan024.physicalWordOutput hThree 0 16 physicalInput
    let D := physicalTailOne
    (B plan024.predIncoming).core.erase.core.reset_cmd = false ∧
      (D plan024.predIncoming).core.erase.core.leader = false ∧
      (D (ring6.rightNeighbor plan024.predIncoming)).core.erase.core.leader =
        false ∧
      (D (ring6.rightNeighbor plan024.predIncoming)).core.erase.core.label =
        ⟨((D plan024.predIncoming).core.erase.core.label.val + 1) % 3,
          by omega⟩ := by
  decide +kernel

-- The statement's `by omega` bound elaborates against the concrete trace;
-- that elaboration needs a deeper recursion budget than the default.
set_option maxRecDepth 2048 in
/-- The second literal repair interaction repeats the same successor-label
installation, even though the next responder still carries an unrelated reset
bit from the kill trace. -/
theorem physicalInput_secondRepairEdge_alignment :
    let D := physicalTailOne
    let E := physicalFullOutput
    (D 2).core.erase.core.reset_cmd = false ∧
      (D 3).core.erase.core.reset_cmd = true ∧
      (E 2).core.erase.core.leader = false ∧
      (E 3).core.erase.core.leader = false ∧
      (E 3).core.erase.core.label =
        ⟨((E 2).core.erase.core.label.val + 1) % 3, by omega⟩ := by
  decide +kernel

private def rawProbeInput (mask : Nat) (i : Fin 6) : AgentState 3 :=
  { rawInput i with probe := mask.testBit i.val }

private theorem rawProbeInput_inProtocolDomain (mask : Nat) (i : Fin 6) :
    (rawProbeInput mask i).inProtocolDomain 0 := by
  simp [rawProbeInput, rawInput, inputView, PeaceView.toState,
    AgentState.inProtocolDomain]

private def physicalProbeInput (mask : Nat) : EConfig 6 3 0 16 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain (rawProbeInput mask i)
      (rawProbeInput_inProtocolDomain mask i), false⟩,
    freshStall 16⟩

private def physicalProbeWordOutput (mask : Nat) : EConfig 6 3 0 16 :=
  plan024.physicalWordOutput hThree 0 16 (physicalProbeInput mask)

/-- Exhaustive old-probe audit for the canonical three-leader fixture.  The
64 masks cover every Boolean probe assignment on the six input agents.  After
the genuine kill word, literal P-prime cannot create a responder leader on the
first reset-free repair edge.  Symbolic evaluation keeps the mask arbitrary
and produces a kernel-checked proof for the complete transition trace. -/
theorem physicalProbeWord_firstRepairEdge_ppsi_nonbirth_all :
    ∀ mask : Fin 64,
      let B := physicalProbeWordOutput mask.val
      let l0 := normalizeDeletion
        (B plan024.predIncoming).core.erase
      let r0 := normalizeDeletion
        (B (ring6.rightNeighbor plan024.predIncoming)).core.erase
      (pPsi hThree l0.core r0.core).2.leader = false := by
  decide +kernel

/-- Exhaustive old-probe audit of the second concrete repair prefix.  Together
with the first-edge theorem above, this shows that varying all six input probe
bits cannot trigger P-prime birth on either actual tail edge.  The proof again
evaluates the full trace symbolically, including the first repair interaction. -/
theorem physicalProbeWord_secondRepairEdge_ppsi_nonbirth_all :
    ∀ mask : Fin 64,
      let B := physicalProbeWordOutput mask.val
      let D := localStep ring6
        (multiLeaderCleanupTransition hThree 0 16) B plan024.predIncoming
      let l0 := normalizeDeletion (D 2).core.erase
      let r0 := normalizeDeletion (D (ring6.rightNeighbor 2)).core.erase
      (pPsi hThree l0.core r0.core).2.leader = false := by
  decide +kernel

/-- The actual canonical post-kill pair satisfies every hidden-field premise
of the complete reset-free edge theorem. -/
theorem physicalInput_firstRepairEdge_resetFree_ready :
    let B := plan024.physicalWordOutput hThree 0 16 physicalInput
    MultiLeaderCleanupResetFreePairReady hThree 0
      (B plan024.predIncoming).core.erase
      (B (ring6.rightNeighbor plan024.predIncoming)).core.erase := by
  apply multiLeaderCleanupResetFreePairReady_of_responder_probe_false
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel

private theorem plan024_repairTail :
    plan024.repairTail = [1, 2] := by
  decide +kernel

/-- Both prefixes of the literal repair tail satisfy the reset-free contract,
including the hidden priority, P-prime, CHECK, and COMPARE fields. -/
theorem physicalInput_repairTail_resetFree_readyAlong :
    MultiLeaderCleanupResetFreeReadyAlong hThree 0 16 ring6
      (plan024.physicalWordOutput hThree 0 16 physicalInput)
      plan024.repairTail := by
  rw [plan024_repairTail]
  simp only [MultiLeaderCleanupResetFreeReadyAlong]
  constructor
  · apply multiLeaderCleanupResetFreePairReady_of_responder_probe_false
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · constructor <;> decide +kernel
    · constructor <;> decide +kernel
  constructor
  · apply multiLeaderCleanupResetFreePairReady_of_responder_probe_false
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · constructor <;> decide +kernel
    · constructor <;> decide +kernel
  · trivial

end PhysicalRegression
end PPLLCompleteMultiLeaderCleanup
