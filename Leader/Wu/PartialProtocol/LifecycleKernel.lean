import Leader.Wu.PartialProtocol.ImmediateOutputKernelNoGo

/-!
# The first concrete comparison-lifecycle kernel for `P_partial`

The exact T1 writer and its delayed predecessor violate two different local
lifecycle facts.  T1 presents a payload-zero CHECK result without the
protocol's executable crossing permit.  The delayed predecessor splices an
already present path into the path-free `.produce` phase.

This file adds exactly those two current-state checks to
`PPartialOutputLegit`.  The resulting predicate is computable from the finite
carrier, is nonempty for every parameter choice, and rejects both accepted
counterexamples.  It is nevertheless not inductive: changing only T1's
arbitrary-initialized permit bit makes the forged carrier pass both checks,
and the exact `P_partial` step still creates a second leader.  Thus the
existing bit records a transition event but cannot authenticate arbitrary
initial provenance.  A genuine closed kernel needs a source-history invariant
or additional executable authentication; no semantic future predicate is
used below.

The transition is always the imported exact unconditional `P_partial`.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialLifecycleKernelSol

open PPLL PPLLResearchFormulation PPLLCounterexample
open PPLLAuthorizedComparisonRepair
open PPLLExpiringComparisonRepair
open PPLLPathStallComparisonRepair
open PPLLNoCheckBirthPhysicalConditionOne
open PPLLNoCheckBirthOutputLegitimacy
open PPLLNoCheckBirthConditionTwoProtocol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Two independent current-state lifecycle checks -/

/-- The four physical states written by CHECK before later comparison stages
consume or transform the result. -/
def PPartialCheckResultState (s : MainState) : Prop :=
  s = .CHECK_ready ∨ s = .equal ∨ s = .larger ∨ s = .less

/-- Generation has no path while it is producing.  Once generation reaches
`.done` or `.depart`, a path must already exist.  This is the physical part of
`GenerationPhaseCoherent`, without pretending that current fields contain a
source identifier. -/
def PPartialGenerationLifecycleOK
    (u : ExpiringAgentState psi kappa tau) : Prop :=
  let raw := eraseExpiringState u
  (raw.state = .produce → raw.path = .bot) ∧
    ((raw.state = .done ∨ raw.state = .depart) → raw.path ≠ .bot)

/-- A CHECK state must still have its comparison path.  For payload zero, the
existing executable `path0Crossed` bit must certify that the carrier crossed
the stable wrap before CHECK.  Nonzero components have no corresponding bit
in the current carrier, so this predicate makes no unsupported claim about
their provenance. -/
def PPartialZeroCheckPermitOK
    (u : ExpiringAgentState psi kappa tau) : Prop :=
  let raw := eraseExpiringState u
  PPartialCheckResultState raw.state →
    raw.path ≠ .bot ∧
      match raw.path with
      | .some 0 _ => u.core.path0Crossed = true
      | _ => True

/-- The conjunction of the two field-level lifecycle checks. -/
def PPartialAgentLifecycleOK
    (u : ExpiringAgentState psi kappa tau) : Prop :=
  PPartialGenerationLifecycleOK u ∧ PPartialZeroCheckPermitOK u

/-- First concrete lifecycle strengthening of the four-field output kernel.
Every conjunct is a predicate of the present finite configuration. -/
def PPartialLifecycleLegit
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : PPartialConfig n psi kappa tau) : Prop :=
  PPartialOutputLegit hpsi ring C ∧
    ∀ i : Fin n, PPartialAgentLifecycleOK (C i)

/-- The lifecycle candidate really strengthens the existing operational
kernel; no closure or safety premise is hidden in the projection. -/
theorem PPartialLifecycleLegit.toOutputLegit
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : PPartialConfig n psi kappa tau)
    (hC : PPartialLifecycleLegit hpsi ring C) :
    PPartialOutputLegit hpsi ring C :=
  hC.1

/-! ## Exact pointwise erasure bridges -/

/-- The canonical witness's finite wrappers erase at one named position. -/
private theorem erase_outputFinite_point
    (hpsi : psi > 0) (kappa tau : Nat) (i : Fin n) :
    eraseExpiringState (outputFinite (n := n) hpsi kappa tau i) =
      outputCore hpsi i := by
  change BoundedAgentState.erase
      (BoundedAgentState.ofDomain (outputCore hpsi i)
        (outputCore_domain hpsi i)) = outputCore hpsi i
  exact BoundedAgentState.erase_ofDomain _ _

/-- Pointwise erasure bridge for the accepted T1 reification. -/
private theorem erase_t1FiniteConfig_point (i : Fin 4) :
    eraseExpiringState
        (PPartialOutputKernelNoGoSol.t1FiniteConfig i) =
      counterConfig i := by
  change BoundedAgentState.erase
      (BoundedAgentState.ofDomain (counterConfig i)
        (counterConfig_inProtocolDomain i)) = counterConfig i
  exact BoundedAgentState.erase_ofDomain _ _

/-- Pointwise erasure bridge for the accepted delayed reification. -/
private theorem erase_delayedFiniteConfig_point (i : Fin 4) :
    eraseExpiringState
        (PPartialImmediateOutputKernelNoGoSol.delayedFiniteConfig i) =
      PPartialImmediateOutputKernelNoGoSol.delayedRawConfig i := by
  change BoundedAgentState.erase
      (BoundedAgentState.ofDomain
        (PPartialImmediateOutputKernelNoGoSol.delayedRawConfig i)
        (PPartialImmediateOutputKernelNoGoSol.delayedRawConfig_inProtocolDomain i)) =
      PPartialImmediateOutputKernelNoGoSol.delayedRawConfig i
  exact BoundedAgentState.erase_ofDomain _ _

/-! ## Nonemptiness -/

/-- The canonical quiet output configuration satisfies both lifecycle checks.
This witnesses the candidate for every finite parameter choice and every
nonempty directed ring. -/
theorem PPartialLifecycleLegit_inhabited
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    ∃ C : PPartialConfig n psi kappa tau,
      PPartialLifecycleLegit hpsi ring C := by
  refine ⟨outputFinite (n := n) hpsi kappa tau,
    outputLegit_inhabited hpsi kappa tau ring, ?_⟩
  intro i
  simp [PPartialAgentLifecycleOK,
    PPartialGenerationLifecycleOK, PPartialZeroCheckPermitOK,
    PPartialCheckResultState, erase_outputFinite_point,
    outputCore, PeaceView.toState]

/-! ## Exact rejection of the two accepted witnesses -/

private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hi := i.isLt
  omega

private theorem two_pos : (2 : Nat) > 0 := by omega

/-- T1 already satisfies generation-phase coherence; its failure is precisely
the missing payload-zero CHECK permit at position two. -/
theorem t1_generationLifecycleOK :
    ∀ i : Fin 4,
      PPartialGenerationLifecycleOK
        (PPartialOutputKernelNoGoSol.t1FiniteConfig i) := by
  intro i
  rcases fin4_cases i with h | h | h | h <;> subst i
  all_goals
    unfold PPartialGenerationLifecycleOK
    rw [erase_t1FiniteConfig_point]
    simp [counterConfig, a0, a1, a2, a3, state2]

/-- The exact T1 configuration is rejected by the permit half of the new
kernel. -/
theorem t1_not_zeroCheckPermitOK :
    ¬ PPartialZeroCheckPermitOK
      (PPartialOutputKernelNoGoSol.t1FiniteConfig 2) := by
  unfold PPartialZeroCheckPermitOK
  rw [erase_t1FiniteConfig_point]
  simp [PPartialCheckResultState, counterConfig, a2, state2,
    PPartialOutputKernelNoGoSol.t1FiniteConfig]

theorem t1FiniteConfig_not_lifecycleLegit :
    ¬ PPartialLifecycleLegit two_pos ring4
      PPartialOutputKernelNoGoSol.t1FiniteConfig := by
  intro h
  exact t1_not_zeroCheckPermitOK (h.2 2).2

/-- R73's delayed configuration does not yet violate the payload-zero CHECK
rule; its independent defect is a `.produce` state that already has a path. -/
theorem delayed_zeroCheckPermitOK :
    ∀ i : Fin 4,
      PPartialZeroCheckPermitOK
        (PPartialImmediateOutputKernelNoGoSol.delayedFiniteConfig i) := by
  intro i
  rcases fin4_cases i with h | h | h | h <;> subst i
  all_goals
    unfold PPartialZeroCheckPermitOK
    rw [erase_delayedFiniteConfig_point]
    simp [PPartialCheckResultState,
      PPartialImmediateOutputKernelNoGoSol.delayedRawConfig,
      counterConfig, a0, a1, a2, a3, state2,
      PPartialImmediateOutputKernelNoGoSol.delayedFiniteConfig]

/-- The exact delayed writer is rejected before its first arming step. -/
theorem delayed_not_generationLifecycleOK :
    ¬ PPartialGenerationLifecycleOK
      (PPartialImmediateOutputKernelNoGoSol.delayedFiniteConfig 2) := by
  unfold PPartialGenerationLifecycleOK
  rw [erase_delayedFiniteConfig_point]
  simp [
    PPartialImmediateOutputKernelNoGoSol.delayedRawConfig,
    counterConfig, a2, state2]

theorem delayedFiniteConfig_not_lifecycleLegit :
    ¬ PPartialLifecycleLegit two_pos ring4
      PPartialImmediateOutputKernelNoGoSol.delayedFiniteConfig := by
  intro h
  exact delayed_not_generationLifecycleOK (h.2 2).1

/-! ## The next exact obstruction: the permit is forgeable -/

/-- T1 with exactly one changed executable field: position two's
`path0Crossed` bit is set.  The raw `AgentState`, timer, and every other
authorized field are unchanged. -/
def forgedPermitT1Config : PPartialConfig 4 2 10 0 :=
  fun i =>
    ⟨⟨BoundedAgentState.ofDomain (counterConfig i)
          (counterConfig_inProtocolDomain i),
        decide (i = (2 : Fin 4))⟩,
      freshStall 0⟩

/-- Pointwise erasure bridge for the one-bit forged reification. -/
private theorem erase_forgedPermitT1Config_point (i : Fin 4) :
    eraseExpiringState (forgedPermitT1Config i) = counterConfig i := by
  change BoundedAgentState.erase
      (BoundedAgentState.ofDomain (counterConfig i)
        (counterConfig_inProtocolDomain i)) = counterConfig i
  exact BoundedAgentState.erase_ofDomain _ _

/-- Forgetting the executable permit gives exactly T1's raw configuration. -/
theorem erase_forgedPermitT1Config :
    eraseExpiringConfig forgedPermitT1Config = counterConfig := by
  funext i
  exact erase_forgedPermitT1Config_point i

/-- The new witness differs from the accepted T1 finite witness at the named
permit and agrees on the complete raw erasure. -/
theorem forgedPermitT1_exact_delta :
    (forgedPermitT1Config 2).core.path0Crossed = true ∧
      (PPartialOutputKernelNoGoSol.t1FiniteConfig 2).core.path0Crossed =
        false ∧
      eraseExpiringConfig forgedPermitT1Config =
        eraseExpiringConfig
          PPartialOutputKernelNoGoSol.t1FiniteConfig := by
  refine ⟨by decide, by decide, ?_⟩
  rw [erase_forgedPermitT1Config]
  funext i
  change counterConfig i = BoundedAgentState.erase
      (BoundedAgentState.ofDomain (counterConfig i)
        (counterConfig_inProtocolDomain i))
  exact (BoundedAgentState.erase_ofDomain _ _).symm

/-- The forged permit makes all present-state lifecycle clauses pass.  This is
the exact reason an arbitrary-initialized transition-event bit is not an
authenticated provenance certificate. -/
theorem forgedPermitT1_lifecycleLegit :
    PPartialLifecycleLegit two_pos ring4 forgedPermitT1Config := by
  constructor
  · unfold PPartialOutputLegit
    rw [erase_forgedPermitT1Config]
    exact counterConfig_paper_safe.toOutputSafe
  · intro i
    rcases fin4_cases i with h | h | h | h <;> subst i
    all_goals
      unfold PPartialAgentLifecycleOK PPartialGenerationLifecycleOK
        PPartialZeroCheckPermitOK
      rw [erase_forgedPermitT1Config_point]
      simp [PPartialCheckResultState,
        forgedPermitT1Config, counterConfig, a0, a1, a2, a3, state2]

private abbrev forgedProtocol : PopulationProtocol :=
  P_partialProtocolUnconditional two_pos 10 0

/-- The exact successor on the same armed edge. -/
def forgedPermitT1After : PPartialConfig 4 2 10 0 :=
  forgedProtocol.step ring4 forgedPermitT1Config 2

/-- Even with the forged permit, the old leader remains and the exact current
transition creates another leader at position two. -/
theorem forgedPermitT1After_two_leaders :
    (forgedPermitT1After 0).core.core.leader = true ∧
      (forgedPermitT1After 2).core.core.leader = true := by
  decide

/-- Hence the exact successor has already left the four-field output kernel. -/
theorem forgedPermitT1After_not_outputLegit :
    ¬ PPartialOutputLegit two_pos ring4 forgedPermitT1After := by
  intro hafter
  obtain ⟨leader, _hleader, honly⟩ := hafter.unique_leader
  have h0 : (eraseExpiringConfig forgedPermitT1After 0).isLeader := by
    change (forgedPermitT1After 0).core.core.leader = true
    exact forgedPermitT1After_two_leaders.1
  have h2 : (eraseExpiringConfig forgedPermitT1After 2).isLeader := by
    change (forgedPermitT1After 2).core.core.leader = true
    exact forgedPermitT1After_two_leaders.2
  have h02 : (0 : Fin 4) = 2 :=
    (honly 0 h0).trans (honly 2 h2).symm
  have hv := congrArg Fin.val h02
  omega

/-- Main closure verdict: the nonempty two-clause lifecycle candidate is not
an inductive predicate for exact `P_partial`. -/
theorem PPartialLifecycleLegit_not_closed_forgedPermit :
    ¬ PopulationProtocol.ClosedPred forgedProtocol ring4
      (PPartialLifecycleLegit two_pos ring4) := by
  intro hclosed
  have hnext := hclosed forgedPermitT1Config
    forgedPermitT1_lifecycleLegit forgedPermitT1After ⟨2, rfl⟩
  exact forgedPermitT1After_not_outputLegit hnext.1

/-- The forged member changes the actual leader output at position two in one
reachable exact step. -/
theorem forgedPermitT1After_output_changed :
    forgedProtocol.output (forgedPermitT1After 2) ≠
      forgedProtocol.output (forgedPermitT1Config 2) := by
  have hafter := forgedPermitT1After_two_leaders.2
  have hbefore : (forgedPermitT1Config 2).core.core.leader = false := by
    rfl
  change (if (forgedPermitT1After 2).core.core.leader then
      LeaderOutput.leader else LeaderOutput.follower) ≠
    (if (forgedPermitT1Config 2).core.core.leader then
      LeaderOutput.leader else LeaderOutput.follower)
  simp [hafter, hbefore]

/-- The closure failure is semantic, not merely a failure to preserve an
auxiliary clause. -/
theorem forgedPermitT1Config_not_isSafe :
    ¬ PopulationProtocol.IsSafe forgedProtocol ring4
      forgedPermitT1Config isLeaderOutput := by
  intro hsafe
  have hreach : PopulationProtocol.Reachable forgedProtocol ring4
      forgedPermitT1Config forgedPermitT1After :=
    PopulationProtocol.OneStep.to_reachable ⟨2, rfl⟩
  exact forgedPermitT1After_output_changed
    (hsafe.2 forgedPermitT1After hreach 2)

/-- Nonvacuous endpoint: the concrete lifecycle kernel itself contains a
Definition-1-unsafe configuration. -/
theorem PPartialLifecycleLegit_contains_unsafe_forgedPermit :
    ∃ C : PPartialConfig 4 2 10 0,
      PPartialLifecycleLegit two_pos ring4 C ∧
        ¬ PopulationProtocol.IsSafe forgedProtocol ring4 C
          isLeaderOutput := by
  exact ⟨forgedPermitT1Config, forgedPermitT1_lifecycleLegit,
    forgedPermitT1Config_not_isSafe⟩

end PPartialLifecycleKernelSol
end PPLLCompleteMultiLeaderCleanup
