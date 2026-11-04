import Leader.Wu.ShortGap.PipelinedOverlap

/-!
# A rearm-service interface for the partial-exit composition

Every short-gap budget in this development so far has been routed through
`ShortGapChoiceStopping.CandidateRearmSpec`, whose composition
(`BalancedFailureRestart.restartStep`) hard-codes two things: the service is
entered at one **fixed** `start`, and service completion returns to one
**fixed** round base.  The partial-exit machinery of
`Leader/Core/PartialExitRestart.lean` and
`Leader/Core/PartialExitEntryRestart.lean` removed both
restrictions, but had no interface consumer: the pipelined files instantiated
`partialExitEntry_natBellmanSuperSolution` directly, one composition at a
time.  Audit item **C2**.

This file supplies the missing interface.

* `PipelinedRoundSpec n` bundles the round side: its step, its potential, its
  scale-one Bellman certificate and its immediate good/bad balance.
* `PipelinedRearmSpec round A R` bundles the service side in the *general*
  shape the partial-exit theorem accepts: an interaction-dependent entry
  `entry : round.Round → Fin n → State`, a service step into
  `ServiceOutcome State round.Round` (so completion may return to an arbitrary
  round state, and a sidecar success may stop the whole process from inside
  the service), a `ServiceBellman` certificate, and the two numeric side
  conditions `entry_le`/`exit_le` that the composition needs.
* `PipelinedRearmSpec.restartStep` / `restartPotential` /
  `restart_natBellmanSuperSolution` / `restartStep_ne_failure` /
  `base_truncatedCost_le` / `base_failureCount_eq_zero` /
  `base_factor_mul_activeCount_le_pow` / `base_success_one_minus_inv_factor`
  mirror the `CandidateRearmSpec.*` API one for one.

Two inhabitants pin the interface down at both ends.

1. `CandidateRearmSpec.toPipelined` — the old interface is the special case
   with constant entry, exit to the fixed all-`Race` base, and no sidecar.
   `toPipelined_restartStep_eq` proves the two composed processes are the
   *same function* (using `noFailure` to discharge the one branch where the
   two lifts would differ), and
   `toPipelined_allRace_truncatedCost_le` re-derives the existing
   `CandidateRearmSpec.allRace_truncatedCost_le` statement verbatim through
   the new interface.  So a downstream file can switch interfaces by renaming.
2. `overlapRearmSpec` — the overlapped pipelined service of
   `Leader/Wu/ShortGap/PipelinedOverlap.lean`, which is a genuinely non-constant
   exit (the service returns the *partially played* next-round word) and does
   use the sidecar port.  `overlapRearmSpec_restartStep_eq` shows the
   interface reproduces `overlapComposedStep` on the nose, and
   `overlapRearmSpec_truncatedCost_le` restates the `2 * (n * m) * (1 + h)`
   capstone through the interface.

**Scope.**  Interface unification only.  No new protocol content: every
inequality here is either the imported partial-exit arithmetic or an
instantiation of a theorem proved in the imported files.  The quotient caveats
of `Leader/Wu/ShortGap/PipelinedRearm.lean` and
`Leader/Wu/ShortGap/PipelinedOverlap.lean` are unchanged and still in force —
abstract one-token-per-gap stop-and-wait carriers with no forgery, staleness
or authentication, uniform gap length `h`, per-gap debt `2 * h`, the
round-`k` word a ghost object whose literal projection (**P1**) and
round-current candidate persistence (**P2**) remain open.  Nothing here claims
stabilization or a final leader-election bound.
-/

namespace ShortGapPipelinedRearmSpec

open FiniteUniformStoppingTree
open PeriodHIncidenceChoice
open ShortGapChoiceStopping
open ShortGapDenialTransport
open ShortGapPipelinedRearm
open ShortGapPipelinedOverlap
open BalancedFailureRestart
open BalancedFailureRestartPartialExit
open BalancedFailureRestartPartialExitEntry

set_option autoImplicit false

/-! ## The two halves of a pipelined restart composition -/

/-- The round side: a stopped round process with a scale-one Bellman
certificate and the immediate good/bad balance that pays the restart
insurance. -/
structure PipelinedRoundSpec (n : Nat) where
  Round : Type
  step : Round → Fin n → StopNode Round
  potential : StopNode Round → Nat
  bellman : NatBellmanSuperSolution step 1 potential
  balance : ∀ state,
    (List.ofFn (fun edge : Fin n => failureWeight (step state edge))).sum ≤
      (List.ofFn (fun edge : Fin n => successWeight (step state edge))).sum

/-- The service side, in the general partial-exit shape.

* `entry` may depend on the failing interaction, not only on the round;
* `step` lands in `ServiceOutcome`, so completion returns to an **arbitrary**
  round state and a sidecar success may stop the whole process from inside the
  service;
* `entry_le` and `exit_le` are the two numeric side conditions of the
  composition: `R` bounds the service potential wherever the round enters it,
  `A` bounds the round potential wherever the service exits into it. -/
structure PipelinedRearmSpec {n : Nat} (round : PipelinedRoundSpec n)
    (A R : Nat) where
  State : Type
  step : State → Fin n → ServiceOutcome State round.Round
  entry : round.Round → Fin n → State
  potential : State → Nat
  bellman : ServiceBellman step 1 potential
  entry_le : ∀ r e, potential (entry r e) ≤ R
  exit_le : ∀ s e r, step s e = .exit r → round.potential (.active r) ≤ A

/-! ## The composed process -/

/-- Active states of a round interleaved with its rearm service. -/
abbrev PipelinedRearmSpec.RestartState {n : Nat}
    {round : PipelinedRoundSpec n} {A R : Nat}
    (spec : PipelinedRearmSpec round A R) :=
  BalancedFailureRestart.RestartState round.Round spec.State

/-- One scheduler interaction of the composed round-with-rearm process. -/
def PipelinedRearmSpec.restartStep {n : Nat}
    {round : PipelinedRoundSpec n} {A R : Nat}
    (spec : PipelinedRearmSpec round A R) :
    spec.RestartState → Fin n → StopNode spec.RestartState :=
  partialExitEntryStep round.step spec.entry spec.step

/-- Combined round-plus-rearm potential. -/
def PipelinedRearmSpec.restartPotential {n : Nat}
    {round : PipelinedRoundSpec n} {A R : Nat}
    (spec : PipelinedRearmSpec round A R) :
    StopNode spec.RestartState → Nat :=
  partialExitPotential round.potential spec.potential A R

/-- **The interface Bellman theorem.**  Local round balance pays the
insurance needed to enter the rearm service; the service pays its own residual
debt; completion may return anywhere with round potential at most `A`. -/
theorem PipelinedRearmSpec.restart_natBellmanSuperSolution {n : Nat}
    {round : PipelinedRoundSpec n} {A R : Nat}
    (spec : PipelinedRearmSpec round A R) :
    NatBellmanSuperSolution spec.restartStep 1 spec.restartPotential :=
  partialExitEntry_natBellmanSuperSolution round.step spec.entry spec.step
    round.potential spec.potential round.bellman spec.bellman round.balance
    spec.exit_le (fun r e _ => spec.entry_le r e)

/-- No scheduler edge of the composed process exposes a bad terminal. -/
theorem PipelinedRearmSpec.restartStep_ne_failure {n : Nat}
    {round : PipelinedRoundSpec n} {A R : Nat}
    (spec : PipelinedRearmSpec round A R) :
    ∀ state edge, spec.restartStep state edge ≠ .failure :=
  partialExitEntryStep_ne_failure round.step spec.entry spec.step

/-- The composed potential at a round base is the `2 * A + R` shape. -/
@[simp] theorem PipelinedRearmSpec.restartPotential_round {n : Nat}
    {round : PipelinedRoundSpec n} {A R : Nat}
    (spec : PipelinedRearmSpec round A R) (base : round.Round) :
    spec.restartPotential (.active (.round base)) =
      round.potential (.active base) + (A + R) := rfl

/-- Exact expected-work numerator from a round base. -/
theorem PipelinedRearmSpec.base_truncatedCost_le {n : Nat}
    {round : PipelinedRoundSpec n} {A R : Nat}
    (spec : PipelinedRearmSpec round A R) (base : round.Round) (T : Nat) :
    truncatedActiveCostNumerator spec.restartStep
        (.active (.round base)) T ≤
      n ^ T * (round.potential (.active base) + (A + R)) := by
  have hcost := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    spec.restartStep 1 spec.restartPotential
    spec.restart_natBellmanSuperSolution (.active (.round base)) T
  have hshape : spec.restartPotential (.active (.round base)) =
      round.potential (.active base) + (A + R) := rfl
  rw [hshape] at hcost
  omega

/-- At every finite horizon the composed tree has zero bad-terminal mass. -/
theorem PipelinedRearmSpec.base_failureCount_eq_zero {n : Nat}
    {round : PipelinedRoundSpec n} {A R : Nat}
    (spec : PipelinedRearmSpec round A R) (base : round.Round) :
    ∀ T, failureCount spec.restartStep (.active (.round base)) T = 0 :=
  BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
    spec.restartStep spec.restartStep_ne_failure (.round base)

/-- Reciprocal finite-horizon tail for the composed process. -/
theorem PipelinedRearmSpec.base_factor_mul_activeCount_le_pow {n factor : Nat}
    {round : PipelinedRoundSpec n} {A R : Nat}
    (spec : PipelinedRearmSpec round A R) (base : round.Round)
    (hpositive : 0 < round.potential (.active base) + (A + R)) :
    factor * activeCount spec.restartStep (.active (.round base))
        (factor * (round.potential (.active base) + (A + R))) ≤
      n ^ (factor * (round.potential (.active base) + (A + R))) := by
  have hpos : 0 < spec.restartPotential (.active (.round base)) := hpositive
  exact BalancedFailureRestart.factor_mul_activeCount_le_pow_of_natSuperSolution
    spec.restartStep spec.restartPotential
    spec.restart_natBellmanSuperSolution (.active (.round base)) hpos
    (factor := factor)

/-- Division-free success form of the same tail bound. -/
theorem PipelinedRearmSpec.base_success_one_minus_inv_factor {n factor : Nat}
    {round : PipelinedRoundSpec n} {A R : Nat}
    (spec : PipelinedRearmSpec round A R) (base : round.Round)
    (hpositive : 0 < round.potential (.active base) + (A + R)) :
    (factor - 1) *
        n ^ (factor * (round.potential (.active base) + (A + R))) ≤
      factor * successCount spec.restartStep (.active (.round base))
        (factor * (round.potential (.active base) + (A + R))) :=
  pred_mul_pow_le_factor_mul_successCount_partialExitEntry_roundBase
    round.step spec.entry spec.step base round.potential spec.potential
    round.bellman spec.bellman round.balance spec.exit_le
    (fun r e _ => spec.entry_le r e) hpositive

/-! ## The bare candidate round as a `PipelinedRoundSpec` -/

/-- The candidate-classifying incidence round of `ShortGapChoiceStopping`,
packaged for the interface. -/
noncomputable def candidateRoundSpec {n m : Nat} (ring : DirectedRing m)
    (hm : 1 < m) (P : Placement n m) (hn : 1 < n) : PipelinedRoundSpec n where
  Round := CandidateDrainState ring
  step := candidateDrainStep ring P
  potential := candidateDrainPotential (n := n) ring
  bellman := candidateDrain_natBellmanSuperSolution ring P
  balance := fun state => candidateDrain_localBalance ring hm P hn state

@[simp] theorem candidateRoundSpec_potential_allRace {n m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n) :
    (candidateRoundSpec ring hm P hn).potential
        (.active (allRaceCandidateDrainState ring (by omega))) = n * m := by
  simp [candidateRoundSpec, candidateDrainPotential,
    allRaceCandidateDrainState, choiceRaceReserve_allRace]

/-- Budget of the interface at the all-`Race` candidate base:
`2 * (n * m) + R`, exactly the shape of
`CandidateRearmSpec.allRace_truncatedCost_le`. -/
theorem candidateRound_allRace_truncatedCost_le {n m R : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (spec : PipelinedRearmSpec (candidateRoundSpec ring hm P hn) (n * m) R)
    (T : Nat) :
    truncatedActiveCostNumerator spec.restartStep
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) + R) := by
  have hcost := spec.base_truncatedCost_le
    (allRaceCandidateDrainState ring (by omega)) T
  rw [candidateRoundSpec_potential_allRace ring hm P hn] at hcost
  have hshape : n * m + (n * m + R) = 2 * (n * m) + R := by omega
  rw [hshape] at hcost
  exact hcost

/-- Reciprocal success tail of the interface at the all-`Race` candidate
base. -/
theorem candidateRound_allRace_success_one_minus_inv_factor
    {n m R factor : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n)
    (spec : PipelinedRearmSpec (candidateRoundSpec ring hm P hn) (n * m) R) :
    (factor - 1) * n ^ (factor * (2 * (n * m) + R)) ≤
      factor * successCount spec.restartStep
        (.active (.round (allRaceCandidateDrainState ring (by omega))))
        (factor * (2 * (n * m) + R)) := by
  have hpositive :
      0 < (candidateRoundSpec ring hm P hn).potential
        (.active (allRaceCandidateDrainState ring (by omega))) +
          (n * m + R) := by
    rw [candidateRoundSpec_potential_allRace ring hm P hn]
    have : 0 < n * m := Nat.mul_pos (by omega) (by omega)
    omega
  have htail := spec.base_success_one_minus_inv_factor
    (allRaceCandidateDrainState ring (by omega)) hpositive (factor := factor)
  rw [candidateRoundSpec_potential_allRace ring hm P hn] at htail
  have hshape : n * m + (n * m + R) = 2 * (n * m) + R := by omega
  rw [hshape] at htail
  exact htail

/-! ## The old interface is the constant-entry, constant-exit special case -/

/-- Read a `CandidateRearmSpec` step as a service step with constant exit and
no sidecar.  The `.failure` branch is unreachable by `noFailure`; it is sent to
the same exit as `.success` so that no bad terminal is invented. -/
def candidateServiceStep {n m : Nat} {ring : DirectedRing m}
    (spec : CandidateRearmSpec n) (roundBase : CandidateDrainState ring)
    (state : spec.State) (edge : Fin n) :
    ServiceOutcome spec.State (CandidateDrainState ring) :=
  match spec.step state edge with
  | .active next => .cont next
  | .success => .exit roundBase
  | .failure => .exit roundBase

private theorem candidateServiceStep_potential {n m : Nat}
    {ring : DirectedRing m} (spec : CandidateRearmSpec n)
    (roundBase : CandidateDrainState ring) (state : spec.State)
    (edge : Fin n) :
    serviceOutcomePotential (fun s => spec.potential (.active s))
        (candidateServiceStep spec roundBase state edge) =
      spec.potential (spec.step state edge) := by
  cases hstep : spec.step state edge with
  | active next =>
      simp [candidateServiceStep, hstep, serviceOutcomePotential]
  | success =>
      simp [candidateServiceStep, hstep, serviceOutcomePotential,
        spec.bellman.1]
  | failure =>
      simp [candidateServiceStep, hstep, serviceOutcomePotential,
        spec.bellman.2.1]

private theorem candidateServiceStep_exit {n m : Nat}
    {ring : DirectedRing m} (spec : CandidateRearmSpec n)
    (roundBase : CandidateDrainState ring) (state : spec.State)
    (edge : Fin n) (r : CandidateDrainState ring)
    (hexit : candidateServiceStep spec roundBase state edge = .exit r) :
    r = roundBase := by
  cases hstep : spec.step state edge with
  | active next =>
      have hval : candidateServiceStep spec roundBase state edge = .cont next := by
        simp [candidateServiceStep, hstep]
      rw [hval] at hexit
      exact absurd hexit (by simp)
  | success =>
      have hval : candidateServiceStep spec roundBase state edge =
          .exit roundBase := by simp [candidateServiceStep, hstep]
      rw [hval] at hexit
      injection hexit with heq
      exact heq.symm
  | failure =>
      have hval : candidateServiceStep spec roundBase state edge =
          .exit roundBase := by simp [candidateServiceStep, hstep]
      rw [hval] at hexit
      injection hexit with heq
      exact heq.symm

private theorem candidateService_bellman {n m : Nat}
    {ring : DirectedRing m} (spec : CandidateRearmSpec n)
    (roundBase : CandidateDrainState ring) :
    ServiceBellman (candidateServiceStep spec roundBase) 1
      (fun state => spec.potential (.active state)) := by
  intro state
  have hmain := spec.bellman.2.2 state
  have hpoint := ofFn_sum_eq
    (fun edge : Fin n =>
      serviceOutcomePotential (fun s => spec.potential (.active s))
        (candidateServiceStep spec roundBase state edge))
    (fun edge : Fin n => spec.potential (spec.step state edge))
    (fun edge => candidateServiceStep_potential spec roundBase state edge)
  show 1 * n + (List.ofFn (fun edge : Fin n =>
      serviceOutcomePotential (fun s => spec.potential (.active s))
        (candidateServiceStep spec roundBase state edge))).sum ≤
    n * spec.potential (.active state)
  rw [hpoint]
  exact hmain

private theorem candidateService_exit_le {n m : Nat}
    (spec : CandidateRearmSpec n) (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) :
    ∀ s e r,
      candidateServiceStep spec (allRaceCandidateDrainState ring (by omega))
          s e = .exit r →
        (candidateRoundSpec ring hm P hn).potential (.active r) ≤ n * m := by
  intro s e r hexit
  have hbase := candidateServiceStep_exit spec _ s e r hexit
  subst hbase
  exact Nat.le_of_eq (candidateRoundSpec_potential_allRace ring hm P hn)

/-- **The old interface, read through the new one.**  Constant entry at
`spec.start`, constant exit to the all-`Race` base, no sidecar success. -/
noncomputable def CandidateRearmSpec.toPipelined {n m : Nat}
    (spec : CandidateRearmSpec n) (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) :
    PipelinedRearmSpec (candidateRoundSpec ring hm P hn) (n * m)
      (spec.potential (.active spec.start)) where
  State := spec.State
  step := candidateServiceStep spec (allRaceCandidateDrainState ring (by omega))
  entry := fun _ _ => spec.start
  potential := fun state => spec.potential (.active state)
  bellman :=
    candidateService_bellman spec (allRaceCandidateDrainState ring (by omega))
  entry_le := fun _ _ => Nat.le_refl _
  exit_le := candidateService_exit_le spec ring hm P hn

/-- **The two composed processes are literally the same function.**  The round
branches agree by definition; the reset branches agree on `.active` and
`.success`, and the branch where `liftResetOutcome` and `liftServiceOutcome`
would differ is exactly the reset `.failure` that `noFailure` excludes. -/
theorem toPipelined_restartStep_eq {n m : Nat} (spec : CandidateRearmSpec n)
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n) :
    (CandidateRearmSpec.toPipelined spec ring hm P hn).restartStep =
      spec.restartStep ring P (by omega) := by
  funext state edge
  cases state with
  | round s => rfl
  | reset s =>
      show liftServiceOutcome
          (candidateServiceStep spec
            (allRaceCandidateDrainState ring (by omega)) s edge) =
        liftResetOutcome (allRaceCandidateDrainState ring (by omega))
          (spec.step s edge)
      cases hstep : spec.step s edge with
      | active next =>
          simp [candidateServiceStep, hstep, liftServiceOutcome,
            liftResetOutcome]
      | success =>
          simp [candidateServiceStep, hstep, liftServiceOutcome,
            liftResetOutcome]
      | failure => exact absurd hstep (spec.noFailure s edge)

/-- **The specialization theorem.**  The interface budget at the all-`Race`
base, transported along `toPipelined_restartStep_eq`, is verbatim the existing
`CandidateRearmSpec.allRace_truncatedCost_le` statement. -/
theorem toPipelined_allRace_truncatedCost_le {n m : Nat}
    (spec : CandidateRearmSpec n) (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (T : Nat) :
    truncatedActiveCostNumerator (spec.restartStep ring P (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) + spec.potential (.active spec.start)) := by
  have hcost := candidateRound_allRace_truncatedCost_le ring hm P hn
    (CandidateRearmSpec.toPipelined spec ring hm P hn) T
  rw [toPipelined_restartStep_eq spec ring hm P hn] at hcost
  exact hcost

/-- Interchangeability check.  This is character-for-character the statement
of `toPipelined_allRace_truncatedCost_le` above, here proved by the *landed*
`CandidateRearmSpec.allRace_truncatedCost_le` instead.  Two proofs of one
proposition: a downstream consumer can switch between the old and the new
interface by renaming and nothing else. -/
theorem landed_allRace_truncatedCost_le {n m : Nat}
    (spec : CandidateRearmSpec n) (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (T : Nat) :
    truncatedActiveCostNumerator (spec.restartStep ring P (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) + spec.potential (.active spec.start)) :=
  spec.allRace_truncatedCost_le ring hm P hn T

/-- The same for the reciprocal success tail. -/
theorem toPipelined_allRace_success_one_minus_inv_factor {n m factor : Nat}
    (spec : CandidateRearmSpec n) (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) :
    (factor - 1) *
        n ^ (factor * (2 * (n * m) + spec.potential (.active spec.start))) ≤
      factor * successCount (spec.restartStep ring P (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega))))
        (factor * (2 * (n * m) +
          spec.potential (.active spec.start))) := by
  have htail := candidateRound_allRace_success_one_minus_inv_factor ring hm P hn
    (CandidateRearmSpec.toPipelined spec ring hm P hn) (factor := factor)
  rw [toPipelined_restartStep_eq spec ring hm P hn] at htail
  exact htail

/-! ## The overlapped pipelined service as a non-constant-exit inhabitant -/

/-- The pipelined ghost round of `Leader/Wu/ShortGap/PipelinedRearm.lean`,
packaged for the interface. -/
noncomputable def pipelinedRoundSpecOf {n h m : Nat} (ring : DirectedRing m)
    (hm : 1 < m) (P : Placement n m) (hn : 1 < n) (L : GapLayout n h m) :
    PipelinedRoundSpec n where
  Round := PipelinedRoundState ring h
  step := pipelinedRoundStep ring P L
  potential := pipelinedRoundPotential (n := n) ring
  bellman := pipelined_natBellmanSuperSolution ring P L
  balance := fun state => pipelined_localBalance ring hm P hn L state

@[simp] theorem pipelinedRoundSpecOf_potential_entry {n h m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (L : GapLayout n h m) :
    (pipelinedRoundSpecOf ring hm P hn L).potential
        (.active (entryRoundState (h := h) ring (by omega))) = n * m := by
  simp [pipelinedRoundSpecOf]

/-- **The overlapped rearm service as a `PipelinedRearmSpec`.**  Its exit is
genuinely non-constant — the service returns the *partially played*
round-`(k+1)` word — and its sidecar port is genuinely used: a candidate found
by the overlapped play stops the whole process before the service finishes.
Neither is expressible in `CandidateRearmSpec`. -/
noncomputable def overlapRearmSpec {n h m : Nat} (ring : DirectedRing m)
    (hm : 1 < m) (P : Placement n m) (hn : 1 < n) (L : GapLayout n h m) :
    PipelinedRearmSpec (pipelinedRoundSpecOf ring hm P hn L) (n * m)
      (n * (m * (2 * h))) where
  State := OverlapServiceState ring h
  step := overlapServiceStep ring P L
  entry := fun _ _ => overlapServiceEntry ring L (by omega)
  potential := overlapServicePotential (n := n)
  bellman := overlapService_bellman ring P L
  entry_le := fun _ _ =>
    Nat.le_of_eq (overlapServicePotential_entry ring L (by omega))
  exit_le := fun s e r hstep => overlapService_exit_le ring P L s e r hstep

/-- The interface reproduces the composed overlapped process on the nose. -/
theorem overlapRearmSpec_restartStep_eq {n h m : Nat} (ring : DirectedRing m)
    (hm : 1 < m) (P : Placement n m) (hn : 1 < n) (L : GapLayout n h m) :
    (overlapRearmSpec ring hm P hn L).restartStep =
      overlapComposedStep ring P L (by omega) := rfl

private theorem budget_eq (n h m : Nat) :
    2 * (n * m) * (1 + h) = 2 * (n * m) + n * (m * (2 * h)) := by
  rw [Nat.mul_add, Nat.mul_one]
  have hswap : n * (m * (2 * h)) = 2 * (n * m) * h := by ac_rfl
  rw [hswap]

/-- **The overlapped capstone through the interface.**  Budget
`2 * (n * m) * (1 + h)`, identical to the direct instantiation of
`Leader/Wu/ShortGap/PipelinedOverlap.lean`. -/
theorem overlapRearmSpec_truncatedCost_le {n h m : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (L : GapLayout n h m) (T : Nat) :
    truncatedActiveCostNumerator (overlapRearmSpec ring hm P hn L).restartStep
        (.active (.round (entryRoundState (h := h) ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) * (1 + h)) := by
  have hcost := (overlapRearmSpec ring hm P hn L).base_truncatedCost_le
    (entryRoundState (h := h) ring (by omega)) T
  rw [pipelinedRoundSpecOf_potential_entry ring hm P hn L] at hcost
  rw [budget_eq]
  have hshape : n * m + (n * m + n * (m * (2 * h))) =
      2 * (n * m) + n * (m * (2 * h)) := by omega
  rw [hshape] at hcost
  exact hcost

/-- Reciprocal success tail of the overlapped capstone through the
interface. -/
theorem overlapRearmSpec_success_one_minus_inv_factor {n h m factor : Nat}
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m) (hn : 1 < n)
    (L : GapLayout n h m) :
    (factor - 1) * n ^ (factor * (2 * (n * m) * (1 + h))) ≤
      factor * successCount (overlapRearmSpec ring hm P hn L).restartStep
        (.active (.round (entryRoundState (h := h) ring (by omega))))
        (factor * (2 * (n * m) * (1 + h))) := by
  have hpositive :
      0 < (pipelinedRoundSpecOf ring hm P hn L).potential
        (.active (entryRoundState (h := h) ring (by omega))) +
          (n * m + n * (m * (2 * h))) := by
    rw [pipelinedRoundSpecOf_potential_entry ring hm P hn L]
    have : 0 < n * m := Nat.mul_pos (by omega) (by omega)
    omega
  have htail :=
    (overlapRearmSpec ring hm P hn L).base_success_one_minus_inv_factor
      (entryRoundState (h := h) ring (by omega)) hpositive (factor := factor)
  rw [pipelinedRoundSpecOf_potential_entry ring hm P hn L] at htail
  rw [budget_eq]
  have hshape : n * m + (n * m + n * (m * (2 * h))) =
      2 * (n * m) + n * (m * (2 * h)) := by omega
  rw [hshape] at htail
  exact htail

#print axioms PipelinedRearmSpec.restart_natBellmanSuperSolution
#print axioms PipelinedRearmSpec.base_truncatedCost_le
#print axioms PipelinedRearmSpec.base_success_one_minus_inv_factor
#print axioms candidateRound_allRace_truncatedCost_le
#print axioms toPipelined_restartStep_eq
#print axioms toPipelined_allRace_truncatedCost_le
#print axioms landed_allRace_truncatedCost_le
#print axioms toPipelined_allRace_success_one_minus_inv_factor
#print axioms overlapRearmSpec_restartStep_eq
#print axioms overlapRearmSpec_truncatedCost_le
#print axioms overlapRearmSpec_success_one_minus_inv_factor

end ShortGapPipelinedRearmSpec
