import Leader.Wu.Birth.ReleaseTerminalInvariant
import Leader.Wu.Birth.SingleUseReleaseWitnesses

set_option autoImplicit false

namespace BirthSpatialSourceSpliceCounterexample

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLPpsiLeaderCreationRepair PPLLLeaderCreationCleanupRepair
  PPLLNoCheckBirthOutputLegitimacy PPLLWallSweepFinite
  PPLLWallSweepRepair PPLLWallSweepPreCheckResetRepair
  BirthCheckCongestGuardRepair BirthMismatchDisposalProducer
  BirthGenerationControlRepair BirthTossCheckPreservationRepair
  BirthSingleUseReleaseRepair BirthReleaseTerminalInvariant

/-! A sixty-step execution of the frozen single-use full host from an empty
comparison layer on the literal thirty-two-site ruler. Real GEN writes ID
one at source ten and ID two at source six. Servicing edge nine expires the
zero bit from each of those words, while their two one bits remain. The
survivors meet and ultimately compare equal to the ruler peak ID three.

This is mixing of distinct spatial source IDs, not multiple GEN episodes
of a single unchanged source word. All current CHECK-ready and terminal
five guards remain in force. Parameters are n=32, psi=2, kappa=2, tau=16;
no final-paper parameter function or different host is asserted here. -/

theorem twoPositive : 2 > 0 := by decide
theorem ringThirtyTwo : DirectedRing 32 := ⟨by decide⟩

def initialCore (i : Fin 32) : AgentState 2 :=
  { trapCore twoPositive i with
    wait := true
    leader := decide (i = 30)
    bit := decide (i = 3 ∨ i = 6 ∨ i = 11 ∨ i = 14 ∨ i = 15 ∨
      i = 19 ∨ i = 22 ∨ i = 27) }

theorem initialCore_domain (i : Fin 32) : (initialCore i).inProtocolDomain 2 := by
  simpa [initialCore, AgentState.inProtocolDomain] using
    (trapCore_domain (κ := 2) twoPositive i)

def initial (i : Fin 32) : ExpiringAgentState 2 2 16 :=
  ⟨⟨BoundedAgentState.ofDomain (initialCore i) (initialCore_domain i), false⟩, freshStall 16⟩

theorem initial_erase : eraseExpiringConfig initial = initialCore := by
  funext i
  exact BoundedAgentState.erase_ofDomain _ (initialCore_domain i)

theorem initial_ruler : isStableIDSequence twoPositive ringThirtyTwo initialCore := by
  refine ⟨30, by decide, by decide, ?_, ?_⟩
  · have h : ∀ k : Fin 32,
        (initialCore ⟨(30 + k.val) % 32, by omega⟩).label = ⟨k.val % 2, by omega⟩ := by decide
    intro k hk
    exact h ⟨k, hk⟩
  · intro i hi hb
    have hc : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
        i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp [groupID, List.range_succ, initialCore, trailingZeros] <;> decide

private theorem initial_no_bad_bullet :
    noNonPeacefulBullet twoPositive ringThirtyTwo initialCore := by
  have h : ∀ i : Fin 32, (initialCore i).bullet ≠ (⟨2, by omega⟩ : Fin 3) := by decide
  intro i hi
  exact False.elim (h i hi)

private theorem initial_no_free_writer :
    noFreeOverwritingSignal twoPositive ringThirtyTwo initialCore := by
  have h : ∀ i : Fin 32, (initialCore i).path3 = none := by decide
  refine ⟨30, by decide, by decide, ?_⟩
  intro i _ _ hf
  obtain ⟨p, hp, _⟩ := hf.1.2 0 (by decide)
  rw [h] at hp
  cases hp

/-- The actual initial state satisfies all five literal paper safety fields. -/
theorem initial_paperSafe :
    PaperSafeConfig twoPositive ringThirtyTwo (eraseExpiringConfig initial) := by
  rw [initial_erase]
  exact {
    unique_leader := by unfold hasUniqueLeader; decide
    no_nonpeaceful_bullet := initial_no_bad_bullet
    no_free_barrier := noFreeBarrier_of_stableID _ _ _ initial_ruler
    no_free_overwriting_signal := initial_no_free_writer
    stable_id_sequence := initial_ruler }

/-- There is no initial comparison payload, control, phase, or permission.
The two real source groups and the target peak have different numeric IDs. -/
theorem initial_empty_with_distinct_source_ids :
    (∀ i : Fin 32,
      (initial i).core.core.path = .bot ∧
        (initial i).core.core.path2 = none ∧
        (initial i).core.core.path3 = none ∧
        (initial i).core.core.state = .none ∧
        (initial i).core.path0Crossed = false ∧
        (initial i).core.core.wait = true ∧ (initial i).core.core.count = 0) ∧
      groupID ringThirtyTwo.hn initialCore 6 = 2 ∧
      groupID ringThirtyTwo.hn initialCore 10 = 1 ∧
      groupID ringThirtyTwo.hn initialCore 14 = 3 := by
  decide

def schedule : DetSchedule 32 := List.replicate 8 10 ++ List.replicate 8 6 ++
  [7, 6, 8, 7, 8, 8, 7, 8] ++ List.replicate 17 9 ++
  [8, 9, 10, 10, 9, 10, 11, 10, 12, 11, 12, 12, 11, 12, 13, 12, 14, 13, 14]

def runPrefix (t : Nat) : Fin 32 → ExpiringAgentState 2 2 16 :=
  runLocalSchedule ringThirtyTwo (singleUseFullTransition twoPositive 2 16)
    initial (schedule.take t)

/-- Observe GEN only when the real current dispatch executes its ordinary
branch. This observer is external to the protocol state. -/
def observedWrites (t : Nat) (e : Fin 32) : Bool × Bool :=
  let l := preparedInput twoPositive (runPrefix t e).core.erase
  let r := preparedInput twoPositive (runPrefix t (ringThirtyTwo.rightNeighbor e)).core.erase
  if deletionActive r then (false, false)
  else if deletionActive l then (false, false)
  else
    let q := authorizedPPsiLeaderResetProbeWall twoPositive l r
    generationWrites twoPositive 2 q.1.core q.2.core

def beforeMovement (t : Nat) (e : Fin 32) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  generationBeforeMove twoPositive 2
    (preparedInput twoPositive (runPrefix t e).core.erase)
    (preparedInput twoPositive (runPrefix t (ringThirtyTwo.rightNeighbor e)).core.erase)

def beforeCheck (t : Nat) (e : Fin 32) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  singleUseBeforeCheck twoPositive 2
    (preparedInput twoPositive (runPrefix t e).core.erase)
    (preparedInput twoPositive (runPrefix t (ringThirtyTwo.rightNeighbor e)).core.erase)

def afterCheck (t : Nat) (e : Fin 32) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let q := beforeCheck t e
  preserveTossCheck twoPositive q.1 q.2

end BirthSpatialSourceSpliceCounterexample
