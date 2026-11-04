import Leader.PPL.Elim.Attempt
import Leader.Core.PredictableTwoTargetFiniteTree

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-!
# Long-attempt retry mass: finite-horizon accounting layer

The physical long-attempt monitor has three success factors:

* the progress race: 1/2, with unresolved active mass retained;
* the incident-orientation race: 1/2, again retaining active mass;
* the retained vulnerable trial: 1/4.

This file proves all protocol-independent finite-tree accounting needed to
multiply those factors without throwing away active residual mass.  The only
remaining physical fact is packaged at the end as
`LongAttemptRetryStageFactorSpec`: it identifies the two serial predictable
races and the retained trial inside the concrete `longAttemptKernel`.
-/

/-! ## Retry trees as ordinary stopped trees -/

/-- Forget the retry payload and regard a completed retry as a failure leaf. -/
def retryAsStopNode {A S : Type} :
    AttemptNode A S -> StopNode A
  | .active a => .active a
  | .success => .success
  | .retry _ => .failure

/-- Ordinary stopped-tree step obtained by forgetting the retry payload. -/
def retryAsStopStep {A S : Type} {n : Nat}
    (K : RetryKernel A S n) :
    A -> Fin n -> StopNode A :=
  fun a e => retryAsStopNode (K.step a e)

/-- The exact retry numerator is the exact failure-leaf numerator of the
payload-forgotten stopped tree, at every finite horizon. -/
theorem retryCount_eq_failureCount
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n) :
    forall x T,
      retryCount K x T =
        failureCount (retryAsStopStep K) (retryAsStopNode x) T := by
  intro x T
  induction T generalizing x with
  | zero =>
      cases x <;> rfl
  | succ T ih =>
      cases x with
      | success =>
          simp [retryCount, failureCount, retryAsStopNode,
            treeWeight_success, failureWeight]
      | retry s =>
          simp [retryCount, failureCount, retryAsStopNode,
            treeWeight_failure, failureWeight]
      | active a =>
          simp only [retryCount, failureCount, retryAsStopNode,
            treeWeight, stepNode, retryAsStopStep]
          apply ofFn_sum_eq
          intro e
          exact ih (K.step a e)

/-- Active plus successful leaves are exactly the finite-horizon mass which
has not completed a retry.  Active residual is intentionally retained. -/
def attemptNonRetryCount
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n) (a : A) (T : Nat) : Nat :=
  activeCount (retryAsStopStep K) (.active a) T +
    successCount (retryAsStopStep K) (.active a) T

/-- Exact finite-horizon partition for one attempt. -/
theorem retryCount_add_attemptNonRetryCount_eq_pow
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n) (a : A) (T : Nat) :
    retryCount K (.active a) T +
        attemptNonRetryCount K a T =
      n ^ T := by
  have hr :=
    retryCount_eq_failureCount K (.active a) T
  have hp :=
    node_count_partition
      (retryAsStopStep K) (.active a) T
  unfold attemptNonRetryCount
  rw [hr]
  simp only [retryAsStopNode] at *
  omega

/-! ## Exact predictable two-target halves -/

/-- If the first predictable target is called the good exit, then
good-or-still-active mass is at least one half of every finite scheduler tree.
No fixed stopping horizon is used. -/
theorem twoTarget_first_or_active_half
    {X : Type} {n : Nat}
    (first second : X -> Fin n)
    (next : X -> Fin n -> X)
    (hdistinct : forall x, first x ≠ second x)
    (x : X) (T : Nat) :
    n ^ T <=
      2 *
        (activeCount
            (PredictableTwoTargetFiniteTree.twoTargetStep
              first second next)
            (.active x) T +
          successCount
            (PredictableTwoTargetFiniteTree.twoTargetStep
              first second next)
            (.active x) T) := by
  have heq :=
    PredictableTwoTargetFiniteTree.twoTarget_successCount_eq_failureCount
      first second next hdistinct x T
  have hp :=
    node_count_partition
      (PredictableTwoTargetFiniteTree.twoTargetStep
        first second next)
      (.active x) T
  omega

/-- Symmetric form when the second predictable target is the good exit.
Again the unresolved active mass is retained. -/
theorem twoTarget_second_or_active_half
    {X : Type} {n : Nat}
    (first second : X -> Fin n)
    (next : X -> Fin n -> X)
    (hdistinct : forall x, first x ≠ second x)
    (x : X) (T : Nat) :
    n ^ T <=
      2 *
        (activeCount
            (PredictableTwoTargetFiniteTree.twoTargetStep
              first second next)
            (.active x) T +
          failureCount
            (PredictableTwoTargetFiniteTree.twoTargetStep
              first second next)
            (.active x) T) := by
  have heq :=
    PredictableTwoTargetFiniteTree.twoTarget_successCount_eq_failureCount
      first second next hdistinct x T
  have hp :=
    node_count_partition
      (PredictableTwoTargetFiniteTree.twoTargetStep
        first second next)
      (.active x) T
  omega

/-! ## Serial 1/2, 1/2, 1/4 arithmetic -/

/-- Division-free multiplication of the three nonretry factors.  `N` is the
actual final nonretry mass, so the exact partition `R + N = M` retains every
active leaf at the horizon rather than silently treating it as a failure. -/
theorem retryMass_fifteen_sixteenths_of_three_factors
    (M R N raceMass incidentMass : Nat)
    (hpartition : R + N = M)
    (hrace : M <= 2 * raceMass)
    (hincident : raceMass <= 2 * incidentMass)
    (hretained : incidentMass <= 4 * N) :
    16 * R <= 15 * M := by
  omega

/-- Generic one-attempt consequence of the three serial factors. -/
theorem retryCount_fifteen_sixteenths_of_three_factors
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n) (a : A) (T : Nat)
    (hfactor :
      exists raceMass incidentMass : Nat,
        n ^ T <= 2 * raceMass /\
        raceMass <= 2 * incidentMass /\
        incidentMass <= 4 * attemptNonRetryCount K a T) :
    16 * retryCount K (.active a) T <=
      15 * n ^ T := by
  obtain ⟨raceMass, incidentMass, hrace, hincident, hretained⟩ :=
    hfactor
  exact
    retryMass_fifteen_sixteenths_of_three_factors
      (n ^ T)
      (retryCount K (.active a) T)
      (attemptNonRetryCount K a T)
      raceMass incidentMass
      (retryCount_add_attemptNonRetryCount_eq_pow K a T)
      hrace hincident hretained

/-! ## Junk starts -/

private theorem longRetry_sum_ofFn_zero :
    forall m : Nat, (List.ofFn (fun _ : Fin m => (0 : Nat))).sum = 0
  | 0 => rfl
  | m + 1 => by
      rw [List.ofFn_succ, List.sum_cons, longRetry_sum_ofFn_zero m]

/-- If every first edge stops in success, no retry has completed at any
finite horizon. -/
theorem retryCount_active_zero_of_step_success
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n) (a : A)
    (hstep : forall e : Fin n, K.step a e = .success) :
    forall T, retryCount K (.active a) T = 0 := by
  intro T
  cases T with
  | zero =>
      rfl
  | succ T =>
      simp only [retryCount]
      calc
        (List.ofFn (fun e : Fin n =>
            retryCount K (K.step a e) T)).sum =
            (List.ofFn (fun _ : Fin n => 0)).sum := by
              apply ofFn_sum_eq
              intro e
              rw [hstep e]
              cases T <;> rfl
        _ = 0 := longRetry_sum_ofFn_zero n

theorem longAttempt_junk_step_success
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) :
    forall e : Fin n,
      (longAttemptKernel ring F).step
          (.junk s) e = .success := by
  intro e
  rfl

theorem longAttempt_junk_retryCount_zero
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) :
    forall T,
      retryCount
          (longAttemptKernel ring F)
          (.active (.junk s)) T = 0 := by
  exact
    retryCount_active_zero_of_step_success
      (longAttemptKernel ring F) (.junk s)
      (longAttempt_junk_step_success ring F s)

theorem longAttempt_start_junk_of_not_good
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n)
    (hbad : ¬ (AttemptGood ring F s)) :
    (longAttemptKernel ring F).start s = .junk s := by
  classical
  change longStart ring F s = .junk s
  simp [longStart, hbad]

/-! ## Single remaining physical serial-composition fact

For a good concrete start, `raceMass` is the target-win-or-active mass after
the progress race, `incidentMass` is the retained-or-active mass after the
incident-orientation race, and `attemptNonRetryCount` is the actual
active-plus-success mass of the full long attempt.

The intended discharge is:
1. `twoTarget_first_or_active_half` (or its symmetric form) for the progress
   race, using `twoTarget_successCount_eq_failureCount`;
2. the same exact theorem for incident orientation;
3. the retained denominator-4 estimate from `target_cycle_pathwise`,
   `retainedTrial_cost_nr`, `compensator_cleared`,
   `retained_collapse_moment`, `W2_scaled`,
   `weighted_changeOfMeasure_nonretry`, and
   `weighted_changeOfMeasure_success`.

What remains physical is the serial identification: reconstruct the
`PhaseHolds` / `VulnerableState` / `RetainedState` witnesses carried only
implicitly by the present `LongAttemptState` stage labels, and show that the
three finite-horizon masses above nest in that order.
-/
def LongAttemptRetryStageFactorSpec : Prop :=
  forall (hSealed : SealedStepSpec),
    forall {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 <= F.b ->
      2 * F.b + 1 <= F.a ->
      forall s, AttemptGood ring F s ->
      forall T,
        exists raceMass incidentMass : Nat,
          n ^ T <= 2 * raceMass /\
          raceMass <= 2 * incidentMass /\
          incidentMass <=
            4 *
              attemptNonRetryCount
                (longAttemptKernel ring F)
                ((longAttemptKernel ring F).start s) T

/-- The requested retry-mass theorem is now reduced to exactly the one physical
serial-composition fact above.  Junk starts are discharged unconditionally. -/
theorem longAttemptRetryMassSpec_of_stageFactors
    (hstage : LongAttemptRetryStageFactorSpec) :
    LongAttemptRetryMassSpec := by
  unfold LongAttemptRetryMassSpec
  intro hSealed n ring C0 F hb hab s T
  classical
  by_cases hgood : AttemptGood ring F s
  · exact
      retryCount_fifteen_sixteenths_of_three_factors
        (longAttemptKernel ring F)
        ((longAttemptKernel ring F).start s) T
        (hstage hSealed ring F hb hab s hgood T)
  · have hstart :
        (longAttemptKernel ring F).start s = .junk s :=
      longAttempt_start_junk_of_not_good ring F s hgood
    rw [hstart]
    rw [longAttempt_junk_retryCount_zero ring F s T]
    omega

end PPL.Convergence.LDLocal
