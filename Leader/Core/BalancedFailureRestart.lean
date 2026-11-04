import Leader.Core.FiniteUniformStoppingTree

/-!
# Restart composition from locally balanced failures

This file isolates the exact interface needed to compose a stopped random
round with a physical restart service.  A round may stop in `success` or
`failure`; every round failure starts the reset service, and reset completion
returns to one fixed round base state.

The key hypothesis is local rather than probabilistic: at every active round
state, the number of immediate failure ports is at most the number of
immediate success ports.  If `A` is a Bellman potential for one round and `R`
is a Bellman potential for a reset service with no failure port, then the
composed process has initial potential

`2 * A(roundBase) + R(resetBase)`.

Thus restart debt is charged explicitly.  It is neither created for free at a
failed leaf nor multiplied by an assumed independent retry coin.
-/

namespace BalancedFailureRestart

open FiniteUniformStoppingTree

set_option autoImplicit false

/-- Active states of a round interleaved with its reset service. -/
inductive RestartState (Round Reset : Type) where
  | round : Round → RestartState Round Reset
  | reset : Reset → RestartState Round Reset

/-- A round failure enters reset; a round success remains terminal. -/
def liftRoundOutcome {Round Reset : Type} (resetBase : Reset) :
    StopNode Round → StopNode (RestartState Round Reset)
  | .active state => .active (.round state)
  | .success => .success
  | .failure => .active (.reset resetBase)

/-- Reset success returns to the fixed round base.  Reset failure is retained
as a bad terminal, but the composition theorem requires that it is absent. -/
def liftResetOutcome {Round Reset : Type} (roundBase : Round) :
    StopNode Reset → StopNode (RestartState Round Reset)
  | .active state => .active (.reset state)
  | .success => .active (.round roundBase)
  | .failure => .failure

/-- One scheduler interaction of the round-with-restart process. -/
def restartStep {Round Reset : Type} {n : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetStep : Reset → Fin n → StopNode Reset)
    (roundBase : Round) (resetBase : Reset) :
    RestartState Round Reset → Fin n →
      StopNode (RestartState Round Reset)
  | .round state, edge => liftRoundOutcome resetBase (roundStep state edge)
  | .reset state, edge => liftResetOutcome roundBase (resetStep state edge)

/-- Insurance held by every active round state.  It is the sum of the cost of
one fresh round and one reset from their respective base states. -/
def insurance {Round Reset : Type}
    (roundPotential : StopNode Round → Nat)
    (resetPotential : StopNode Reset → Nat)
    (roundBase : Round) (resetBase : Reset) : Nat :=
  roundPotential (.active roundBase) +
    resetPotential (.active resetBase)

/-- Bellman potential for the composed process.  During reset, the potential
also reserves the complete cost of returning to and running the base round. -/
def restartPotential {Round Reset : Type}
    (roundPotential : StopNode Round → Nat)
    (resetPotential : StopNode Reset → Nat)
    (roundBase : Round) (resetBase : Reset) :
    StopNode (RestartState Round Reset) → Nat
  | .success => 0
  | .failure => 0
  | .active (.round state) =>
      roundPotential (.active state) +
        insurance roundPotential resetPotential roundBase resetBase
  | .active (.reset state) =>
      resetPotential (.active state) +
        roundPotential (.active roundBase) +
        insurance roundPotential resetPotential roundBase resetBase

private theorem immediate_count_partition
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S) (state : S) :
    (List.ofFn (fun edge : Fin n =>
        activeWeight (step state edge))).sum +
      (List.ofFn (fun edge : Fin n =>
        successWeight (step state edge))).sum +
      (List.ofFn (fun edge : Fin n =>
        failureWeight (step state edge))).sum = n := by
  calc
    (List.ofFn (fun edge : Fin n =>
        activeWeight (step state edge))).sum +
        (List.ofFn (fun edge : Fin n =>
          successWeight (step state edge))).sum +
        (List.ofFn (fun edge : Fin n =>
          failureWeight (step state edge))).sum =
      (List.ofFn (fun edge : Fin n =>
        (activeWeight (step state edge) +
          successWeight (step state edge)) +
          failureWeight (step state edge))).sum := by
            rw [ofFn_sum_add, ofFn_sum_add]
    _ = (List.ofFn (fun _ : Fin n => 1)).sum := by
      apply ofFn_sum_eq
      intro edge
      cases step state edge <;>
        rfl
    _ = n := by simp [ofFn_sum_const]

/-- Main restart theorem.  Both components use the same uniformly scheduled
port set and the same cost scale. -/
theorem restart_natBellmanSuperSolution
    {Round Reset : Type} {n scale : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetStep : Reset → Fin n → StopNode Reset)
    (roundBase : Round) (resetBase : Reset)
    (roundPotential : StopNode Round → Nat)
    (resetPotential : StopNode Reset → Nat)
    (hround : NatBellmanSuperSolution roundStep scale roundPotential)
    (hreset : NatBellmanSuperSolution resetStep scale resetPotential)
    (hbalance : ∀ state,
      (List.ofFn (fun edge : Fin n =>
        failureWeight (roundStep state edge))).sum ≤
      (List.ofFn (fun edge : Fin n =>
        successWeight (roundStep state edge))).sum)
    (hresetNoFailure : ∀ state edge,
      resetStep state edge ≠ .failure) :
    NatBellmanSuperSolution
      (restartStep roundStep resetStep roundBase resetBase) scale
      (restartPotential roundPotential resetPotential roundBase resetBase) := by
  rcases hround with ⟨hroundSuccess, hroundFailure, hroundBellman⟩
  rcases hreset with ⟨hresetSuccess, hresetFailure, hresetBellman⟩
  refine ⟨rfl, rfl, ?_⟩
  intro state
  let credit := insurance roundPotential resetPotential roundBase resetBase
  cases state with
  | round state =>
      let activeMass := (List.ofFn (fun edge : Fin n =>
        activeWeight (roundStep state edge))).sum
      let successMass := (List.ofFn (fun edge : Fin n =>
        successWeight (roundStep state edge))).sum
      let failureMass := (List.ofFn (fun edge : Fin n =>
        failureWeight (roundStep state edge))).sum
      have hpartition : activeMass + successMass + failureMass = n := by
        exact immediate_count_partition roundStep state
      have hmass : activeMass + 2 * failureMass ≤ n := by
        have hbalanced : failureMass ≤ successMass := hbalance state
        omega
      have hextra :
          credit * activeMass + (2 * credit) * failureMass ≤ n * credit := by
        calc
          credit * activeMass + (2 * credit) * failureMass =
              credit * (activeMass + 2 * failureMass) := by
                simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]
          _ ≤ credit * n := Nat.mul_le_mul_left credit hmass
          _ = n * credit := Nat.mul_comm credit n
      have hchild (edge : Fin n) :
          restartPotential roundPotential resetPotential roundBase resetBase
              (liftRoundOutcome resetBase (roundStep state edge)) =
            roundPotential (roundStep state edge) +
              credit * activeWeight (roundStep state edge) +
              (2 * credit) * failureWeight (roundStep state edge) := by
        cases hstep : roundStep state edge with
        | active next =>
            simp [liftRoundOutcome, restartPotential, credit, insurance,
              activeWeight, failureWeight]
        | success =>
            simp [liftRoundOutcome, restartPotential, credit,
              activeWeight, failureWeight, hroundSuccess]
        | failure =>
            simp [liftRoundOutcome, restartPotential, credit, insurance,
              activeWeight, failureWeight, hroundFailure]
            omega
      have hchildren :
          (List.ofFn (fun edge : Fin n =>
            restartPotential roundPotential resetPotential roundBase resetBase
              (liftRoundOutcome resetBase (roundStep state edge)))).sum =
            (List.ofFn (fun edge : Fin n =>
              roundPotential (roundStep state edge))).sum +
              credit * activeMass + (2 * credit) * failureMass := by
        calc
          (List.ofFn (fun edge : Fin n =>
              restartPotential roundPotential resetPotential roundBase resetBase
                (liftRoundOutcome resetBase (roundStep state edge)))).sum =
            (List.ofFn (fun edge : Fin n =>
              (roundPotential (roundStep state edge) +
                credit * activeWeight (roundStep state edge)) +
                (2 * credit) * failureWeight
                  (roundStep state edge))).sum := by
                    apply ofFn_sum_eq
                    exact hchild
          _ = (List.ofFn (fun edge : Fin n =>
                roundPotential (roundStep state edge))).sum +
              credit * activeMass + (2 * credit) * failureMass := by
                rw [ofFn_sum_add, ofFn_sum_add, ofFn_sum_mul_left,
                  ofFn_sum_mul_left]
      change scale * n +
          (List.ofFn (fun edge : Fin n =>
            restartPotential roundPotential resetPotential roundBase resetBase
              (liftRoundOutcome resetBase (roundStep state edge)))).sum ≤
        n * (roundPotential (.active state) + credit)
      rw [hchildren]
      have hmain := hroundBellman state
      have hcombined := Nat.add_le_add hmain hextra
      simpa [Nat.mul_add, Nat.add_assoc] using hcombined
  | reset state =>
      let baseCredit := roundPotential (.active roundBase) + credit
      have hchild (edge : Fin n) :
          restartPotential roundPotential resetPotential roundBase resetBase
              (liftResetOutcome roundBase (resetStep state edge)) =
            resetPotential (resetStep state edge) + baseCredit := by
        cases hstep : resetStep state edge with
        | active next =>
            simp [liftResetOutcome, restartPotential, baseCredit, credit,
              Nat.add_assoc]
        | success =>
            simp [liftResetOutcome, restartPotential, baseCredit, credit,
              hresetSuccess]
        | failure =>
            exact False.elim (hresetNoFailure state edge hstep)
      have hchildren :
          (List.ofFn (fun edge : Fin n =>
            restartPotential roundPotential resetPotential roundBase resetBase
              (liftResetOutcome roundBase (resetStep state edge)))).sum =
            (List.ofFn (fun edge : Fin n =>
              resetPotential (resetStep state edge))).sum + n * baseCredit := by
        calc
          (List.ofFn (fun edge : Fin n =>
              restartPotential roundPotential resetPotential roundBase resetBase
                (liftResetOutcome roundBase (resetStep state edge)))).sum =
            (List.ofFn (fun edge : Fin n =>
              resetPotential (resetStep state edge) + baseCredit)).sum := by
                apply ofFn_sum_eq
                exact hchild
          _ = (List.ofFn (fun edge : Fin n =>
                resetPotential (resetStep state edge))).sum +
              (List.ofFn (fun _ : Fin n => baseCredit)).sum :=
                ofFn_sum_add _ _
          _ = (List.ofFn (fun edge : Fin n =>
                resetPotential (resetStep state edge))).sum +
              n * baseCredit := by rw [ofFn_sum_const]
      simp only [restartStep, restartPotential]
      change scale * n +
          (List.ofFn (fun edge : Fin n =>
            restartPotential roundPotential resetPotential roundBase resetBase
              (liftResetOutcome roundBase (resetStep state edge)))).sum ≤
        n * (resetPotential (.active state) +
          roundPotential (.active roundBase) + credit)
      rw [hchildren]
      have hmain := hresetBellman state
      have hcombined := Nat.add_le_add_right hmain (n * baseCredit)
      simpa [baseCredit, Nat.mul_add, Nat.add_assoc] using hcombined

@[simp] theorem restartPotential_roundBase
    {Round Reset : Type}
    (roundPotential : StopNode Round → Nat)
    (resetPotential : StopNode Reset → Nat)
    (roundBase : Round) (resetBase : Reset) :
    restartPotential roundPotential resetPotential roundBase resetBase
        (.active (.round roundBase)) =
      2 * roundPotential (.active roundBase) +
        resetPotential (.active resetBase) := by
  simp [restartPotential, insurance]
  omega

/-- The composed process has no immediate bad terminal. -/
theorem restartStep_ne_failure
    {Round Reset : Type} {n : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetStep : Reset → Fin n → StopNode Reset)
    (roundBase : Round) (resetBase : Reset)
    (hresetNoFailure : ∀ state edge,
      resetStep state edge ≠ .failure) :
    ∀ state edge,
      restartStep roundStep resetStep roundBase resetBase state edge ≠
        .failure := by
  intro state edge
  cases state with
  | round state =>
      cases hstep : roundStep state edge <;>
        simp [restartStep, liftRoundOutcome, hstep]
  | reset state =>
      cases hstep : resetStep state edge with
      | active next => simp [restartStep, liftResetOutcome, hstep]
      | success => simp [restartStep, liftResetOutcome, hstep]
      | failure => exact False.elim (hresetNoFailure state edge hstep)

/-- If no active state has a bad terminal child, the complete stopped tree
has zero failure leaves at every finite horizon. -/
theorem failureCount_eq_zero_of_step_ne_failure
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S)
    (hnoFailure : ∀ state edge, step state edge ≠ .failure) :
    ∀ state T, failureCount step (.active state) T = 0 := by
  intro state T
  induction T generalizing state with
  | zero => rfl
  | succ T ih =>
      simp only [failureCount, treeWeight, stepNode]
      calc
        (List.ofFn (fun edge : Fin n =>
            treeWeight step failureWeight (step state edge) T)).sum =
          (List.ofFn (fun _ : Fin n => 0)).sum := by
            apply ofFn_sum_eq
            intro edge
            cases hchild : step state edge with
            | active next => simpa [failureCount] using ih next
            | success => simp [treeWeight_success, failureWeight]
            | failure => exact False.elim (hnoFailure state edge hchild)
        _ = 0 := by rw [ofFn_sum_const]; simp

/-! ## A finite-horizon tail bound -/

/-- A finite natural Bellman potential gives the elementary reciprocal tail
bound at a horizon equal to `factor * potential`. -/
theorem factor_mul_activeCount_le_pow_of_natSuperSolution
    {S : Type} {n factor : Nat}
    (step : S → Fin n → StopNode S) (potential : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step 1 potential)
    (state : StopNode S) (hpositive : 0 < potential state) :
    factor * activeCount step state (factor * potential state) ≤
      n ^ (factor * potential state) := by
  let horizon := factor * potential state
  have hdelay := horizon_mul_activeCount_le_truncatedActiveCostNumerator
    step state horizon
  have hcost := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    step 1 potential hsuper state horizon
  have hscaled :
      potential state * (factor * activeCount step state horizon) ≤
        potential state * n ^ horizon := by
    calc
      potential state * (factor * activeCount step state horizon) =
          horizon * activeCount step state horizon := by
            simp [horizon, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ truncatedActiveCostNumerator step state horizon := hdelay
      _ ≤ n ^ horizon * potential state := by simpa using hcost
      _ = potential state * n ^ horizon := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_left hscaled hpositive

/-- When the process has no bad terminal, the reciprocal active tail is an
exact lower bound on success mass.  For `factor > 0`, the left side is the
`(1 - 1/factor)` numerator, stated without division. -/
theorem pred_mul_pow_le_factor_mul_successCount
    {S : Type} {n factor : Nat}
    (step : S → Fin n → StopNode S) (potential : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step 1 potential)
    (hnoFailure : ∀ state edge, step state edge ≠ .failure)
    (state : S) (hpositive : 0 < potential (.active state)) :
    (factor - 1) * n ^ (factor * potential (.active state)) ≤
      factor * successCount step (.active state)
        (factor * potential (.active state)) := by
  let horizon := factor * potential (.active state)
  have hactive := factor_mul_activeCount_le_pow_of_natSuperSolution
    step potential hsuper (.active state) hpositive (factor := factor)
  have hfailure := failureCount_eq_zero_of_step_ne_failure
    step hnoFailure state horizon
  have hpartition := node_count_partition step (.active state) horizon
  have hsum :
      activeCount step (.active state) horizon +
        successCount step (.active state) horizon = n ^ horizon := by
    omega
  dsimp [horizon] at hactive hfailure hpartition hsum ⊢
  by_cases hfactor : factor = 0
  · simp [hfactor]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hfactor
    simp only [Nat.add_sub_cancel, Nat.succ_eq_add_one] at hactive hsum ⊢
    rw [← hsum] at hactive ⊢
    rw [Nat.mul_add]
    simp only [Nat.add_mul, Nat.one_mul] at hactive ⊢
    omega

#print axioms restart_natBellmanSuperSolution
#print axioms restartStep_ne_failure
#print axioms failureCount_eq_zero_of_step_ne_failure
#print axioms factor_mul_activeCount_le_pow_of_natSuperSolution
#print axioms pred_mul_pow_le_factor_mul_successCount

end BalancedFailureRestart
