import Leader.Core.BalancedFailureRestart

/-!
# Restart composition with a partial-exit reset service

This file generalizes `BalancedFailureRestart` in exactly one place: the reset
service is no longer required to complete into one fixed round base state.

In `BalancedFailureRestart.liftResetOutcome`, a reset `success` teleports the
composed process to `.active (.round roundBase)`.  That models a service whose
completion is a global barrier, after which the next round has not been played
at all.  A pipelined service does not have that shape: by the time the service
is declared complete, some parts of the next round may already be resolved.

Here the reset service therefore steps into `ResetOutcome`:

* `cont` — the service continues in a reset state;
* `exit` — the service completes into an *arbitrary* round state.

There is no reset failure port at all, so the composed process has no bad
terminal by construction.

The single new hypothesis is `hexit`: every round state the service can exit
into has round potential at most the declared bound `A`.  Combined with the
service-entry bound `hentry` (`resetPotential resetBase ≤ R`), the composed
potential is

```
V (round state r) = roundPotential (.active r) + (A + R)
V (reset state s) = resetPotential s + A + (A + R)
```

so the budget at a round base with `roundPotential (.active roundBase) ≤ A` is
still `2 * A + R`: the same insurance as the fixed-exit composition survives
the partial exit.

Nothing about any literal protocol carrier is proved here.  In particular this
file makes no claim that any concrete round/service pair satisfies `hexit`, no
claim about stabilization, and no claim about a final complexity bound.  It is
a purely arithmetic composition statement about stopped uniform trees.
-/

namespace BalancedFailureRestartPartialExit

open FiniteUniformStoppingTree
open BalancedFailureRestart

set_option autoImplicit false

/-! ## The partial-exit reset service -/

/-- Outcome of one scheduler interaction of a reset service.  `cont` is the
"continue" port: the service is still running.  `exit` is the completion port:
the service hands control back to the round layer at an arbitrary round state,
not at a fixed base.  There is deliberately no failure port.

(The constructor is named `cont` rather than `continue` because `continue` is a
Lean keyword and cannot be used as a `cases` alternative name.) -/
inductive ResetOutcome (Reset Round : Type) where
  | cont : Reset → ResetOutcome Reset Round
  | exit : Round → ResetOutcome Reset Round

/-- Potential of a reset outcome.  Completion carries no residual service
debt; the cost of the round it exits into is charged by the insurance term of
the composed potential, not here. -/
def resetOutcomePotential {Reset Round : Type} (resetPotential : Reset → Nat) :
    ResetOutcome Reset Round → Nat
  | .cont state => resetPotential state
  | .exit _ => 0

/-- Division-free Bellman supersolution for a partial-exit reset service.  It
is the `NatBellmanSuperSolution` inequality with `resetOutcomePotential` in
place of the stopped-node potential; the two terminal side conditions are
absent because the service has no terminal node of its own. -/
def PartialExitBellman {Reset Round : Type} {n : Nat}
    (resetStep : Reset → Fin n → ResetOutcome Reset Round) (scale : Nat)
    (resetPotential : Reset → Nat) : Prop :=
  ∀ state, scale * n +
    (List.ofFn (fun edge : Fin n =>
      resetOutcomePotential resetPotential (resetStep state edge))).sum ≤
      n * resetPotential state

/-- Embed a reset outcome into the composed state space.  Completion becomes
an active round node at the round state carried by `exit`. -/
def liftPartialExitOutcome {Round Reset : Type} :
    ResetOutcome Reset Round → StopNode (RestartState Round Reset)
  | .cont state => .active (.reset state)
  | .exit state => .active (.round state)

/-- One scheduler interaction of the round-with-partial-exit-restart process.
Round failure still enters the service at the fixed `resetBase`; service
completion may leave at any round state. -/
def partialExitStep {Round Reset : Type} {n : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetStep : Reset → Fin n → ResetOutcome Reset Round)
    (resetBase : Reset) :
    RestartState Round Reset → Fin n →
      StopNode (RestartState Round Reset)
  | .round state, edge => liftRoundOutcome resetBase (roundStep state edge)
  | .reset state, edge => liftPartialExitOutcome (resetStep state edge)

/-- Bellman potential for the composed process.  `A` bounds the round
potential at every admissible service exit, `R` bounds the service potential at
service entry.  Every active round state carries the insurance `A + R`, and
every active reset state additionally reserves one full round of cost `A`. -/
def partialExitPotential {Round Reset : Type}
    (roundPotential : StopNode Round → Nat)
    (resetPotential : Reset → Nat) (A R : Nat) :
    StopNode (RestartState Round Reset) → Nat
  | .success => 0
  | .failure => 0
  | .active (.round state) => roundPotential (.active state) + (A + R)
  | .active (.reset state) => resetPotential state + A + (A + R)

/-! ## Immediate port partition -/

private theorem immediate_count_partition'
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

/-! ## The composition theorem -/

/-- Generalized restart theorem.  Both components use the same uniformly
scheduled port set and the same cost scale.  The reset service returns to an
arbitrary round state whose round potential is at most `A`. -/
theorem partialExit_natBellmanSuperSolution
    {Round Reset : Type} {n scale A R : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetStep : Reset → Fin n → ResetOutcome Reset Round)
    (resetBase : Reset)
    (roundPotential : StopNode Round → Nat)
    (resetPotential : Reset → Nat)
    (hround : NatBellmanSuperSolution roundStep scale roundPotential)
    (hreset : PartialExitBellman resetStep scale resetPotential)
    (hbalance : ∀ state,
      (List.ofFn (fun edge : Fin n =>
        failureWeight (roundStep state edge))).sum ≤
      (List.ofFn (fun edge : Fin n =>
        successWeight (roundStep state edge))).sum)
    (hexit : ∀ state edge r, resetStep state edge = .exit r →
      roundPotential (.active r) ≤ A)
    (hentry : resetPotential resetBase ≤ R) :
    NatBellmanSuperSolution
      (partialExitStep roundStep resetStep resetBase) scale
      (partialExitPotential roundPotential resetPotential A R) := by
  obtain ⟨hroundSuccess, hroundFailure, hroundBellman⟩ := hround
  refine ⟨rfl, rfl, ?_⟩
  intro state
  let credit := A + R
  cases state with
  | round state =>
      let activeMass := (List.ofFn (fun edge : Fin n =>
        activeWeight (roundStep state edge))).sum
      let successMass := (List.ofFn (fun edge : Fin n =>
        successWeight (roundStep state edge))).sum
      let failureMass := (List.ofFn (fun edge : Fin n =>
        failureWeight (roundStep state edge))).sum
      have hpartition : activeMass + successMass + failureMass = n :=
        immediate_count_partition' roundStep state
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
          partialExitPotential roundPotential resetPotential A R
              (liftRoundOutcome resetBase (roundStep state edge)) ≤
            roundPotential (roundStep state edge) +
              credit * activeWeight (roundStep state edge) +
              (2 * credit) * failureWeight (roundStep state edge) := by
        cases hstep : roundStep state edge with
        | active next =>
            simp [liftRoundOutcome, partialExitPotential, credit,
              activeWeight, failureWeight]
        | success =>
            simp [liftRoundOutcome, partialExitPotential, credit,
              activeWeight, failureWeight, hroundSuccess]
        | failure =>
            simp [liftRoundOutcome, partialExitPotential, credit,
              activeWeight, failureWeight, hroundFailure]
            omega
      have hchildren :
          (List.ofFn (fun edge : Fin n =>
            partialExitPotential roundPotential resetPotential A R
              (liftRoundOutcome resetBase (roundStep state edge)))).sum ≤
            (List.ofFn (fun edge : Fin n =>
              roundPotential (roundStep state edge))).sum +
              credit * activeMass + (2 * credit) * failureMass := by
        calc
          (List.ofFn (fun edge : Fin n =>
              partialExitPotential roundPotential resetPotential A R
                (liftRoundOutcome resetBase (roundStep state edge)))).sum ≤
            (List.ofFn (fun edge : Fin n =>
              (roundPotential (roundStep state edge) +
                credit * activeWeight (roundStep state edge)) +
                (2 * credit) * failureWeight
                  (roundStep state edge))).sum :=
                    ofFn_sum_le _ _ hchild
          _ = (List.ofFn (fun edge : Fin n =>
                roundPotential (roundStep state edge))).sum +
              credit * activeMass + (2 * credit) * failureMass := by
                rw [ofFn_sum_add, ofFn_sum_add, ofFn_sum_mul_left,
                  ofFn_sum_mul_left]
      change scale * n +
          (List.ofFn (fun edge : Fin n =>
            partialExitPotential roundPotential resetPotential A R
              (liftRoundOutcome resetBase (roundStep state edge)))).sum ≤
        n * (roundPotential (.active state) + credit)
      refine Nat.le_trans (Nat.add_le_add_left hchildren _) ?_
      have hmain := hroundBellman state
      have hcombined := Nat.add_le_add hmain hextra
      simpa [Nat.mul_add, Nat.add_assoc] using hcombined
  | reset state =>
      let baseCredit := A + credit
      have hchild (edge : Fin n) :
          partialExitPotential roundPotential resetPotential A R
              (liftPartialExitOutcome (resetStep state edge)) ≤
            resetOutcomePotential resetPotential (resetStep state edge) +
              baseCredit := by
        cases hstep : resetStep state edge with
        | cont next =>
            simp [liftPartialExitOutcome, partialExitPotential,
              resetOutcomePotential, baseCredit, credit, Nat.add_assoc]
        | exit next =>
            have hbound : roundPotential (.active next) ≤ A :=
              hexit state edge next hstep
            simp [liftPartialExitOutcome, partialExitPotential,
              resetOutcomePotential, baseCredit, credit]
            omega
      have hchildren :
          (List.ofFn (fun edge : Fin n =>
            partialExitPotential roundPotential resetPotential A R
              (liftPartialExitOutcome (resetStep state edge)))).sum ≤
            (List.ofFn (fun edge : Fin n =>
              resetOutcomePotential resetPotential
                (resetStep state edge))).sum + n * baseCredit := by
        calc
          (List.ofFn (fun edge : Fin n =>
              partialExitPotential roundPotential resetPotential A R
                (liftPartialExitOutcome (resetStep state edge)))).sum ≤
            (List.ofFn (fun edge : Fin n =>
              resetOutcomePotential resetPotential (resetStep state edge) +
                baseCredit)).sum := ofFn_sum_le _ _ hchild
          _ = (List.ofFn (fun edge : Fin n =>
                resetOutcomePotential resetPotential
                  (resetStep state edge))).sum +
              (List.ofFn (fun _ : Fin n => baseCredit)).sum :=
                ofFn_sum_add _ _
          _ = (List.ofFn (fun edge : Fin n =>
                resetOutcomePotential resetPotential
                  (resetStep state edge))).sum +
              n * baseCredit := by rw [ofFn_sum_const]
      change scale * n +
          (List.ofFn (fun edge : Fin n =>
            partialExitPotential roundPotential resetPotential A R
              (liftPartialExitOutcome (resetStep state edge)))).sum ≤
        n * (resetPotential state + A + credit)
      refine Nat.le_trans (Nat.add_le_add_left hchildren _) ?_
      have hmain := hreset state
      have hcombined := Nat.add_le_add_right hmain (n * baseCredit)
      simpa [baseCredit, Nat.mul_add, Nat.add_assoc] using hcombined

/-! ## The composed budget -/

/-- Potential at an arbitrary active round state. -/
@[simp] theorem partialExitPotential_round
    {Round Reset : Type}
    (roundPotential : StopNode Round → Nat)
    (resetPotential : Reset → Nat) (A R : Nat) (state : Round) :
    partialExitPotential (Reset := Reset) roundPotential resetPotential A R
        (.active (.round state)) =
      roundPotential (.active state) + (A + R) := rfl

/-- Potential at an arbitrary active reset state. -/
@[simp] theorem partialExitPotential_reset
    {Round Reset : Type}
    (roundPotential : StopNode Round → Nat)
    (resetPotential : Reset → Nat) (A R : Nat) (state : Reset) :
    partialExitPotential (Round := Round) roundPotential resetPotential A R
        (.active (.reset state)) =
      resetPotential state + A + (A + R) := rfl

/-- The initial budget at a round base whose round potential respects the same
bound `A` used at service exits is `2 * A + R`. -/
theorem partialExitPotential_roundBase_le
    {Round Reset : Type}
    (roundPotential : StopNode Round → Nat)
    (resetPotential : Reset → Nat) (A R : Nat) (roundBase : Round)
    (hbase : roundPotential (.active roundBase) ≤ A) :
    partialExitPotential (Reset := Reset) roundPotential resetPotential A R
        (.active (.round roundBase)) ≤ 2 * A + R := by
  simp [partialExitPotential]
  omega

/-- The composed process has no immediate bad terminal.  Unlike the fixed-exit
composition this needs no hypothesis: the service has no failure port. -/
theorem partialExitStep_ne_failure
    {Round Reset : Type} {n : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetStep : Reset → Fin n → ResetOutcome Reset Round)
    (resetBase : Reset) :
    ∀ state edge,
      partialExitStep roundStep resetStep resetBase state edge ≠ .failure := by
  intro state edge
  cases state with
  | round state =>
      cases hstep : roundStep state edge <;>
        simp [partialExitStep, liftRoundOutcome, hstep]
  | reset state =>
      cases hstep : resetStep state edge <;>
        simp [partialExitStep, liftPartialExitOutcome, hstep]

/-! ## Finite-horizon tail bound -/

/-- Reciprocal tail bound for the partial-exit composition at any active
composed state.  For `factor > 0` the left side is the `(1 - 1/factor)`
numerator, stated without division.  Everything generic is reused from
`FiniteUniformStoppingTree` and `BalancedFailureRestart`. -/
theorem pred_mul_pow_le_factor_mul_successCount_partialExit
    {Round Reset : Type} {n factor A R : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetStep : Reset → Fin n → ResetOutcome Reset Round)
    (resetBase : Reset)
    (roundPotential : StopNode Round → Nat)
    (resetPotential : Reset → Nat)
    (hround : NatBellmanSuperSolution roundStep 1 roundPotential)
    (hreset : PartialExitBellman resetStep 1 resetPotential)
    (hbalance : ∀ state,
      (List.ofFn (fun edge : Fin n =>
        failureWeight (roundStep state edge))).sum ≤
      (List.ofFn (fun edge : Fin n =>
        successWeight (roundStep state edge))).sum)
    (hexit : ∀ state edge r, resetStep state edge = .exit r →
      roundPotential (.active r) ≤ A)
    (hentry : resetPotential resetBase ≤ R)
    (state : RestartState Round Reset)
    (hpositive : 0 <
      partialExitPotential roundPotential resetPotential A R (.active state)) :
    (factor - 1) *
        n ^ (factor *
          partialExitPotential roundPotential resetPotential A R
            (.active state)) ≤
      factor *
        successCount (partialExitStep roundStep resetStep resetBase)
          (.active state)
          (factor *
            partialExitPotential roundPotential resetPotential A R
              (.active state)) :=
  BalancedFailureRestart.pred_mul_pow_le_factor_mul_successCount
    (partialExitStep roundStep resetStep resetBase)
    (partialExitPotential roundPotential resetPotential A R)
    (partialExit_natBellmanSuperSolution roundStep resetStep resetBase
      roundPotential resetPotential hround hreset hbalance hexit hentry)
    (partialExitStep_ne_failure roundStep resetStep resetBase)
    state hpositive

/-- The same tail bound started at a round base, with the budget written
explicitly as `roundPotential (.active roundBase) + (A + R)`.  Together with
`partialExitPotential_roundBase_le` this is the `2 * A + R` budget. -/
theorem pred_mul_pow_le_factor_mul_successCount_partialExit_roundBase
    {Round Reset : Type} {n factor A R : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetStep : Reset → Fin n → ResetOutcome Reset Round)
    (roundBase : Round) (resetBase : Reset)
    (roundPotential : StopNode Round → Nat)
    (resetPotential : Reset → Nat)
    (hround : NatBellmanSuperSolution roundStep 1 roundPotential)
    (hreset : PartialExitBellman resetStep 1 resetPotential)
    (hbalance : ∀ state,
      (List.ofFn (fun edge : Fin n =>
        failureWeight (roundStep state edge))).sum ≤
      (List.ofFn (fun edge : Fin n =>
        successWeight (roundStep state edge))).sum)
    (hexit : ∀ state edge r, resetStep state edge = .exit r →
      roundPotential (.active r) ≤ A)
    (hentry : resetPotential resetBase ≤ R)
    (hpositive : 0 < roundPotential (.active roundBase) + (A + R)) :
    (factor - 1) *
        n ^ (factor * (roundPotential (.active roundBase) + (A + R))) ≤
      factor *
        successCount (partialExitStep roundStep resetStep resetBase)
          (.active (.round roundBase))
          (factor * (roundPotential (.active roundBase) + (A + R))) :=
  pred_mul_pow_le_factor_mul_successCount_partialExit roundStep resetStep
    resetBase roundPotential resetPotential hround hreset hbalance hexit hentry
    (.round roundBase) hpositive

/-! ## The fixed-exit composition is the special case -/

/-- Read a fixed-exit reset outcome as a partial-exit outcome that always
leaves at `roundBase`.  The failure port is mapped to the same exit; it is
never taken under the fixed-exit no-failure hypothesis. -/
def fixedExitOutcome {Round Reset : Type} (roundBase : Round) :
    StopNode Reset → ResetOutcome Reset Round
  | .active state => .cont state
  | .success => .exit roundBase
  | .failure => .exit roundBase

/-- The fixed-exit reset service read as a partial-exit service. -/
def fixedExitStep {Round Reset : Type} {n : Nat}
    (roundBase : Round) (resetStep : Reset → Fin n → StopNode Reset) :
    Reset → Fin n → ResetOutcome Reset Round :=
  fun state edge => fixedExitOutcome roundBase (resetStep state edge)

/-- On non-failure reset outcomes the two liftings agree. -/
theorem liftPartialExitOutcome_fixedExitOutcome
    {Round Reset : Type} (roundBase : Round) (x : StopNode Reset)
    (hx : x ≠ .failure) :
    liftPartialExitOutcome (Round := Round) (fixedExitOutcome roundBase x) =
      liftResetOutcome roundBase x := by
  cases x with
  | active state => rfl
  | success => rfl
  | failure => exact absurd rfl hx

/-- The partial-exit composition over `fixedExitStep` is literally the
fixed-exit composition of `BalancedFailureRestart`. -/
theorem partialExitStep_of_fixed
    {Round Reset : Type} {n : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetStep : Reset → Fin n → StopNode Reset)
    (roundBase : Round) (resetBase : Reset)
    (hresetNoFailure : ∀ state edge, resetStep state edge ≠ .failure) :
    partialExitStep roundStep (fixedExitStep roundBase resetStep) resetBase =
      restartStep roundStep resetStep roundBase resetBase := by
  funext state edge
  cases state with
  | round state => rfl
  | reset state =>
      exact liftPartialExitOutcome_fixedExitOutcome roundBase
        (resetStep state edge) (hresetNoFailure state edge)

/-- With `A` and `R` instantiated at the two base potentials, the generalized
potential is literally `BalancedFailureRestart.restartPotential`. -/
theorem partialExitPotential_of_fixed
    {Round Reset : Type}
    (roundPotential : StopNode Round → Nat)
    (resetPotential : StopNode Reset → Nat)
    (roundBase : Round) (resetBase : Reset) :
    partialExitPotential roundPotential
        (fun state => resetPotential (.active state))
        (roundPotential (.active roundBase))
        (resetPotential (.active resetBase)) =
      restartPotential roundPotential resetPotential roundBase resetBase := by
  funext x
  cases x with
  | success => rfl
  | failure => rfl
  | active state =>
      cases state with
      | round state => rfl
      | reset state => rfl

/-- The fixed-exit service is a partial-exit service with the same Bellman
certificate. -/
theorem partialExitBellman_of_fixed
    {Round Reset : Type} {n scale : Nat}
    (resetStep : Reset → Fin n → StopNode Reset)
    (resetPotential : StopNode Reset → Nat) (roundBase : Round)
    (hreset : NatBellmanSuperSolution resetStep scale resetPotential) :
    PartialExitBellman (Round := Round) (fixedExitStep roundBase resetStep)
      scale (fun state => resetPotential (.active state)) := by
  obtain ⟨hresetSuccess, hresetFailure, hresetBellman⟩ := hreset
  intro state
  have hpoint : ∀ edge : Fin n,
      resetOutcomePotential (fun s => resetPotential (.active s))
          (fixedExitStep (Round := Round) roundBase resetStep state edge) =
        resetPotential (resetStep state edge) := by
    intro edge
    cases hstep : resetStep state edge with
    | active next =>
        simp [fixedExitStep, fixedExitOutcome, resetOutcomePotential, hstep]
    | success =>
        simp [fixedExitStep, fixedExitOutcome, resetOutcomePotential, hstep,
          hresetSuccess]
    | failure =>
        simp [fixedExitStep, fixedExitOutcome, resetOutcomePotential, hstep,
          hresetFailure]
  rw [ofFn_sum_eq _ (fun edge => resetPotential (resetStep state edge)) hpoint]
  exact hresetBellman state

/-- Every fixed exit respects the exit bound with `A` the base round
potential. -/
theorem hexit_of_fixed
    {Round Reset : Type} {n : Nat}
    (resetStep : Reset → Fin n → StopNode Reset)
    (roundPotential : StopNode Round → Nat) (roundBase : Round) :
    ∀ state edge r,
      fixedExitStep (Round := Round) roundBase resetStep state edge =
          .exit r →
        roundPotential (.active r) ≤ roundPotential (.active roundBase) := by
  intro state edge r hstep
  cases hcase : resetStep state edge with
  | active next =>
      rw [fixedExitStep, hcase] at hstep
      exact absurd hstep (by simp [fixedExitOutcome])
  | success =>
      rw [fixedExitStep, hcase] at hstep
      have : r = roundBase := by
        simpa [fixedExitOutcome] using hstep.symm
      subst this
      exact Nat.le_refl _
  | failure =>
      rw [fixedExitStep, hcase] at hstep
      have : r = roundBase := by
        simpa [fixedExitOutcome] using hstep.symm
      subst this
      exact Nat.le_refl _

/-- The fixed-exit restart theorem of `BalancedFailureRestart` recovered as
the special case of the partial-exit theorem where every exit is at
`roundBase`. -/
theorem restart_natBellmanSuperSolution_of_partialExit
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
    (hresetNoFailure : ∀ state edge, resetStep state edge ≠ .failure) :
    NatBellmanSuperSolution
      (restartStep roundStep resetStep roundBase resetBase) scale
      (restartPotential roundPotential resetPotential roundBase resetBase) := by
  rw [← partialExitStep_of_fixed roundStep resetStep roundBase resetBase
      hresetNoFailure,
    ← partialExitPotential_of_fixed roundPotential resetPotential roundBase
      resetBase]
  exact partialExit_natBellmanSuperSolution roundStep
    (fixedExitStep roundBase resetStep) resetBase roundPotential
    (fun state => resetPotential (.active state)) hround
    (partialExitBellman_of_fixed resetStep resetPotential roundBase hreset)
    hbalance
    (hexit_of_fixed resetStep roundPotential roundBase)
    (Nat.le_refl _)

#print axioms partialExit_natBellmanSuperSolution
#print axioms partialExitStep_ne_failure
#print axioms pred_mul_pow_le_factor_mul_successCount_partialExit
#print axioms pred_mul_pow_le_factor_mul_successCount_partialExit_roundBase
#print axioms restart_natBellmanSuperSolution_of_partialExit

end BalancedFailureRestartPartialExit
