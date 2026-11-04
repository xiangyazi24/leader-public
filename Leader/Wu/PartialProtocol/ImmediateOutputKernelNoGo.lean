import Leader.Wu.PartialProtocol.OutputKernelNoGo

/-!
# The exact one-step output guard is not an inductive kernel

`PPartialOutputLegit` does not exclude T1's immediate CHECK writer.  The
logically weakest operational repair of that specific omission is to require
the complete output vector to be framed by every next interaction.  This is a
concrete one-step computation on `P_partial`; it is neither `IsSafe` nor
`OutputStableFrom`.

The guard is inhabited and rejects T1.  Nevertheless a concrete
`produce/larger` predecessor passes it: one interaction turns the initiator
into terminal equality, and the next interaction creates a second leader.
Thus one-step lookahead is not closed and cannot replace a preserved
comparison-lifecycle invariant.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialImmediateOutputKernelNoGoSol

open PPLL PPLLResearchFormulation PPLLCounterexample
open PPLLExpiringComparisonRepair
open PPLLPathStallComparisonRepair
open PPLLNoCheckBirthPhysicalConditionOne

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-- Exact one-step pointwise output framing for every enabled ring edge. -/
def PPartialImmediateOutputFrame
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : PPartialConfig n psi kappa tau) : Prop :=
  ∀ e i : Fin n,
    (((P_partialProtocolUnconditional hpsi kappa tau).step
      ring C e) i).core.core.leader = (C i).core.core.leader

/-- Because the packaged output is exactly the leader bit, the concrete frame
is equivalent to the literal one-step pointwise output equation. -/
theorem PPartialImmediateOutputFrame_iff_step_output_eq
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : PPartialConfig n psi kappa tau) :
    PPartialImmediateOutputFrame hpsi kappa tau ring C ↔
      ∀ e i : Fin n,
        (P_partialProtocolUnconditional hpsi kappa tau).output
            (((P_partialProtocolUnconditional hpsi kappa tau).step
              ring C e) i) =
          (P_partialProtocolUnconditional hpsi kappa tau).output (C i) := by
  constructor
  · intro hframe e i
    change
      (if (((P_partialProtocolUnconditional hpsi kappa tau).step
          ring C e) i).core.core.leader then
        LeaderOutput.leader else LeaderOutput.follower) =
      (if (C i).core.core.leader then
        LeaderOutput.leader else LeaderOutput.follower)
    rw [hframe e i]
  · intro hout e i
    have h := hout e i
    change
      (if (((P_partialProtocolUnconditional hpsi kappa tau).step
          ring C e) i).core.core.leader then
        LeaderOutput.leader else LeaderOutput.follower) =
      (if (C i).core.core.leader then
        LeaderOutput.leader else LeaderOutput.follower) at h
    cases hnew :
        (((P_partialProtocolUnconditional hpsi kappa tau).step
          ring C e) i).core.core.leader <;>
      cases hold : (C i).core.core.leader <;>
      simp [hnew, hold] at h ⊢

/-- The pointwise-smallest strengthening of `PPartialOutputLegit` that
supplies its missing immediate output-frame conjunct directly. -/
def PPartialImmediateOutputLegit
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : PPartialConfig n psi kappa tau) : Prop :=
  PPartialOutputLegit hpsi ring C ∧
    PPartialImmediateOutputFrame hpsi kappa tau ring C

/-- The strengthening really implies the exact output frame for one step; no
closure assumption is hidden in this projection. -/
theorem PPartialImmediateOutputLegit.step_output_eq
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : PPartialConfig n psi kappa tau)
    (hC : PPartialImmediateOutputLegit hpsi kappa tau ring C)
    (e i : Fin n) :
    (P_partialProtocolUnconditional hpsi kappa tau).output
        (((P_partialProtocolUnconditional hpsi kappa tau).step
          ring C e) i) =
      (P_partialProtocolUnconditional hpsi kappa tau).output (C i) :=
  by
    change
      (if (((P_partialProtocolUnconditional hpsi kappa tau).step
          ring C e) i).core.core.leader then
        LeaderOutput.leader else LeaderOutput.follower) =
      (if (C i).core.core.leader then
        LeaderOutput.leader else LeaderOutput.follower)
    rw [hC.2 e i]

private theorem hpsi : (2 : Nat) > 0 := by omega

/-! ## Immediate T1 rejection -/

/-- The exact T1 member of `PPartialOutputLegit` fails the new conjunct on its
armed comparison edge. -/
theorem t1FiniteConfig_not_immediateOutputLegit :
    ¬ PPartialImmediateOutputLegit hpsi 10 0 ring4
      PPartialOutputKernelNoGoSol.t1FiniteConfig := by
  intro hT1
  have hchange :
      (((P_partialProtocolUnconditional hpsi 10 0).step ring4
        PPartialOutputKernelNoGoSol.t1FiniteConfig 2) 2).core.core.leader ≠
        (PPartialOutputKernelNoGoSol.t1FiniteConfig 2).core.core.leader := by
    decide
  exact hchange (hT1.2 (2 : Fin 4) (2 : Fin 4))

/-! ## A concrete guarded predecessor -/

/-- A two-group predecessor of T1.  Its carrier data are already complete,
but the initiator is only `.produce` and the responder is `.larger`; the first
interaction has no leader write. -/
def delayedRawConfig : Fin 4 → AgentState 2
  | ⟨0, _⟩ => counterConfig 0
  | ⟨1, _⟩ => counterConfig 1
  | ⟨2, _⟩ => { counterConfig 2 with state := .produce }
  | ⟨3, _⟩ => { counterConfig 3 with state := .larger }

private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hi := i.isLt
  omega

/-- Every field of the predecessor lies in the declared finite domain. -/
theorem delayedRawConfig_inProtocolDomain :
    ∀ i, (delayedRawConfig i).inProtocolDomain 10 := by
  intro i
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [delayedRawConfig, counterConfig, a0, a1, a2, a3, state2,
      AgentState.inProtocolDomain]

/-- The raw predecessor has exactly the same four output-relevant fields as
T1 and therefore belongs to the existing output kernel. -/
theorem delayedRawConfig_outputSafe :
    OutputSafeConfig hpsi ring4 delayedRawConfig where
  unique_leader := by
    refine ⟨0, by decide, ?_⟩
    intro i hi
    rcases fin4_cases i with h | h | h | h <;> subst i
    · rfl
    all_goals simp [delayedRawConfig, counterConfig, a1, a2, a3,
      state2, AgentState.isLeader] at hi
  leader_label_zero := by
    intro i hi
    rcases fin4_cases i with h | h | h | h <;> subst i
    · rfl
    all_goals simp [delayedRawConfig, counterConfig, a1, a2, a3,
      state2, AgentState.isLeader] at hi
  no_nonpeaceful_bullet := by
    intro i hi
    rcases fin4_cases i with h | h | h | h <;> subst i <;>
      simp [delayedRawConfig, counterConfig, a0, a1, a2, a3, state2] at hi
  no_free_barrier := by
    intro i
    rcases fin4_cases i with h | h | h | h <;> subst i <;>
      simp [DirectedRing.rightNeighbor, isBarrier, delayedRawConfig,
        counterConfig, a0, a1, a2, a3, state2]

/-- Reification uses a positive path-stall budget so that the first genuine
comparison-progress step is not erased by the outer wrapper. -/
def delayedFiniteConfig : PPartialConfig 4 2 10 2 :=
  fun i =>
    ⟨⟨BoundedAgentState.ofDomain (delayedRawConfig i)
        (delayedRawConfig_inProtocolDomain i), false⟩,
      freshStall 2⟩

private theorem erase_delayedFiniteConfig :
    eraseExpiringConfig delayedFiniteConfig = delayedRawConfig := by
  funext i
  change BoundedAgentState.erase
      (BoundedAgentState.ofDomain (delayedRawConfig i)
        (delayedRawConfig_inProtocolDomain i)) = delayedRawConfig i
  exact BoundedAgentState.erase_ofDomain _ _

private abbrev delayedProtocol : PopulationProtocol :=
  P_partialProtocolUnconditional hpsi 10 2

/-- The finite predecessor satisfies the existing four-field output kernel. -/
theorem delayedFiniteConfig_outputLegit :
    PPartialOutputLegit hpsi ring4 delayedFiniteConfig := by
  unfold PPartialOutputLegit
  rw [erase_delayedFiniteConfig]
  exact delayedRawConfig_outputSafe

/-- The predecessor frames the complete output vector under every possible
first exact interaction. -/
theorem delayedFiniteConfig_immediateOutputFrame :
    PPartialImmediateOutputFrame hpsi 10 2 ring4
      delayedFiniteConfig := by
  intro e i
  rcases fin4_cases e with h | h | h | h <;> subst e <;>
    rcases fin4_cases i with h | h | h | h <;> subst i <;> decide

/-- Hence the strengthened operational predicate is genuinely inhabited. -/
theorem PPartialImmediateOutputLegit_inhabited_q6328 :
    ∃ C : PPartialConfig 4 2 10 2,
      PPartialImmediateOutputLegit hpsi 10 2 ring4 C := by
  exact ⟨delayedFiniteConfig, delayedFiniteConfig_outputLegit,
    delayedFiniteConfig_immediateOutputFrame⟩

/-! ## Exact delayed writer -/

/-- The first interaction arms terminal equality at position two. -/
def delayedFiniteAfterOne : PPartialConfig 4 2 10 2 :=
  delayedProtocol.step ring4 delayedFiniteConfig 2

/-- Repeating the same exact edge executes the delayed writer. -/
def delayedFiniteAfterTwo : PPartialConfig 4 2 10 2 :=
  delayedProtocol.step ring4 delayedFiniteAfterOne 2

/-- The first step really reaches terminal equality without changing the
leader bit. -/
theorem delayedFiniteAfterOne_armed_shape :
    (delayedFiniteAfterOne 2).core.core.state = .equal ∧
      (delayedFiniteAfterOne 2).core.core.leader = false := by
  decide

/-- The delayed second interaction changes the leader bit at position two. -/
theorem delayedFiniteAfterTwo_leader_changed :
    (delayedFiniteAfterTwo 2).core.core.leader ≠
      (delayedFiniteAfterOne 2).core.core.leader := by
  decide

/-- The old leader at zero remains while the delayed writer creates the new
leader at position two. -/
theorem delayedFiniteAfterTwo_two_leaders :
    (delayedFiniteAfterTwo 0).core.core.leader = true ∧
      (delayedFiniteAfterTwo 2).core.core.leader = true := by
  decide

/-- Since `P_partial` outputs exactly the leader bit, the same interaction
changes the protocol output. -/
theorem delayedFiniteAfterTwo_output_changed :
    delayedProtocol.output (delayedFiniteAfterTwo 2) ≠
      delayedProtocol.output (delayedFiniteAfterOne 2) := by
  intro hout
  apply delayedFiniteAfterTwo_leader_changed
  cases htwo : (delayedFiniteAfterTwo 2).core.core.leader <;>
    cases hone : (delayedFiniteAfterOne 2).core.core.leader <;>
    simp [delayedProtocol, P_partialProtocolUnconditional,
      P_partialProtocol, htwo, hone] at hout ⊢

/-- The armed first successor therefore fails the exact immediate frame. -/
theorem delayedFiniteAfterOne_not_immediateOutputFrame :
    ¬ PPartialImmediateOutputFrame hpsi 10 2 ring4
      delayedFiniteAfterOne := by
  intro hframe
  exact delayedFiniteAfterTwo_leader_changed
    (by simpa [delayedFiniteAfterTwo, delayedProtocol] using
      hframe (2 : Fin 4) (2 : Fin 4))

/-- In particular the first successor leaves the strengthened predicate. -/
theorem delayedFiniteAfterOne_not_immediateOutputLegit :
    ¬ PPartialImmediateOutputLegit hpsi 10 2 ring4
      delayedFiniteAfterOne := by
  intro hlegit
  exact delayedFiniteAfterOne_not_immediateOutputFrame hlegit.2

/-- Main no-go: the inhabited exact one-step-output strengthening is not
closed under the current `P_partial` transition. -/
theorem PPartialImmediateOutputLegit_not_closed_q6328 :
    ¬ PopulationProtocol.ClosedPred delayedProtocol ring4
      (PPartialImmediateOutputLegit hpsi 10 2 ring4) := by
  intro hclosed
  have hnext := hclosed delayedFiniteConfig
    ⟨delayedFiniteConfig_outputLegit,
      delayedFiniteConfig_immediateOutputFrame⟩
    delayedFiniteAfterOne ⟨2, rfl⟩
  exact delayedFiniteAfterOne_not_immediateOutputLegit hnext

/-- The counterexample is semantic as well as inductive: the guarded
predecessor itself is not Definition-1 safe, because the two-step reachable
state changes an output. -/
theorem delayedFiniteConfig_not_isSafe :
    ¬ PopulationProtocol.IsSafe delayedProtocol ring4 delayedFiniteConfig
      isLeaderOutput := by
  intro hsafe
  have hreachOne : PopulationProtocol.Reachable delayedProtocol ring4
      delayedFiniteConfig delayedFiniteAfterOne :=
    PopulationProtocol.OneStep.to_reachable ⟨2, rfl⟩
  have hreachTwo : PopulationProtocol.Reachable delayedProtocol ring4
      delayedFiniteAfterOne delayedFiniteAfterTwo :=
    PopulationProtocol.OneStep.to_reachable ⟨2, rfl⟩
  have hfromStart := hsafe.2 delayedFiniteAfterTwo
    (hreachOne.trans hreachTwo) (2 : Fin 4)
  have hfirst :=
    PPartialImmediateOutputLegit.step_output_eq hpsi 10 2 ring4
      delayedFiniteConfig
      ⟨delayedFiniteConfig_outputLegit,
        delayedFiniteConfig_immediateOutputFrame⟩
      (2 : Fin 4) (2 : Fin 4)
  exact delayedFiniteAfterTwo_output_changed
    (hfromStart.trans hfirst.symm)

/-- Nonvacuous endpoint: even the minimally one-step-guarded kernel contains
a concrete configuration that is not Definition-1 safe. -/
theorem PPartialImmediateOutputLegit_contains_not_isSafe_q6328 :
    ∃ C : PPartialConfig 4 2 10 2,
      PPartialImmediateOutputLegit hpsi 10 2 ring4 C ∧
        ¬ PopulationProtocol.IsSafe delayedProtocol ring4 C
          isLeaderOutput := by
  exact ⟨delayedFiniteConfig,
    ⟨delayedFiniteConfig_outputLegit,
      delayedFiniteConfig_immediateOutputFrame⟩,
    delayedFiniteConfig_not_isSafe⟩

end PPartialImmediateOutputKernelNoGoSol
end PPLLCompleteMultiLeaderCleanup
