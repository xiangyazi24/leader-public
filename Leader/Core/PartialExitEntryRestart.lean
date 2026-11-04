import Leader.Core.PartialExitRestart

/-!
# Partial-exit restart with state-dependent entry and sidecar success

This file adds the two remaining degrees of freedom to the partial-exit
restart composition of `Leader.Core.PartialExitRestart`.

1. **State-dependent service entry.**  In the previous interface a round
   failure always entered the service at one fixed `resetBase`, so the
   interface discarded *which* failure occurred.  The literal protocol has two
   uniform failure words, and the residual service started at a failure
   depends on that word.  Here the composition carries an entry map
   `resetEntry : Round → Fin n → Reset`, read at the failing interaction.

   The round interface is deliberately left exactly as it was landed: the
   round still steps into `StopNode Round`, so `NatBellmanSuperSolution` round
   certificates and the immediate-balance hypothesis `hbalance` (failure ports
   at most success ports) plug in verbatim.  Replacing `StopNode` by a
   payload-carrying `RoundOutcome` would have forced every existing round
   certificate to be restated, for no additional generality: the failure
   payload is exactly `resetEntry state edge`.

2. **Sidecar success during service.**  In the pipelined protocol a candidate
   can appear while the service of an earlier round is still running.  The
   service outcome therefore gains a `succeed` port, which is charged `0`: it
   is a terminal success of the whole composed process.

The potential is unchanged — it is literally
`BalancedFailureRestartPartialExit.partialExitPotential` — and so is the
budget `2 * A + R` at a round base, where

* `A` bounds the round potential at every state the service can exit into;
* `R` bounds the service potential at every state the round can enter at.

The service still has no failure port, so the composed process has no bad
terminal, with no hypothesis at all.

As in the imported file, nothing about any literal protocol carrier is proved
here: there is no claim that any concrete round/service pair satisfies `hexit`
or `hentry`, no claim about stabilization, and no claim about a final
complexity bound.  This is only the arithmetic composition statement about
stopped uniform trees.
-/

namespace BalancedFailureRestartPartialExitEntry

open FiniteUniformStoppingTree
open BalancedFailureRestart
open BalancedFailureRestartPartialExit

set_option autoImplicit false

/-! ## The service interface -/

/-- Outcome of one scheduler interaction of a restart service.

* `cont` — the service is still running;
* `exit` — the service completes into an arbitrary round state;
* `succeed` — a sidecar success of the whole composed process occurs while
  the service is still running.

There is deliberately no failure port.  (`cont` rather than `continue`:
`continue` is a Lean keyword and cannot be used as a `cases` alternative
name.) -/
inductive ServiceOutcome (Reset Round : Type) where
  | cont : Reset → ServiceOutcome Reset Round
  | exit : Round → ServiceOutcome Reset Round
  | succeed : ServiceOutcome Reset Round

/-- Potential of a service outcome.  Completion and sidecar success both carry
no residual service debt; the cost of the round an `exit` lands in is charged
by the insurance term of the composed potential, not here. -/
def serviceOutcomePotential {Reset Round : Type}
    (resetPotential : Reset → Nat) : ServiceOutcome Reset Round → Nat
  | .cont state => resetPotential state
  | .exit _ => 0
  | .succeed => 0

/-- Division-free Bellman supersolution for a restart service with partial
exit and sidecar success. -/
def ServiceBellman {Reset Round : Type} {n : Nat}
    (serviceStep : Reset → Fin n → ServiceOutcome Reset Round) (scale : Nat)
    (resetPotential : Reset → Nat) : Prop :=
  ∀ state, scale * n +
    (List.ofFn (fun edge : Fin n =>
      serviceOutcomePotential resetPotential (serviceStep state edge))).sum ≤
      n * resetPotential state

/-- Embed a service outcome into the composed state space. -/
def liftServiceOutcome {Round Reset : Type} :
    ServiceOutcome Reset Round → StopNode (RestartState Round Reset)
  | .cont state => .active (.reset state)
  | .exit state => .active (.round state)
  | .succeed => .success

/-- One scheduler interaction of the round-with-restart process, with
state-dependent service entry and sidecar success.  The round layer reuses the
landed `liftRoundOutcome`, now applied at the entry state read off the failing
interaction. -/
def partialExitEntryStep {Round Reset : Type} {n : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetEntry : Round → Fin n → Reset)
    (serviceStep : Reset → Fin n → ServiceOutcome Reset Round) :
    RestartState Round Reset → Fin n →
      StopNode (RestartState Round Reset)
  | .round state, edge =>
      liftRoundOutcome (resetEntry state edge) (roundStep state edge)
  | .reset state, edge => liftServiceOutcome (serviceStep state edge)

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

/-- Most general restart composition theorem of this development.  The round
enters the service at a state that may depend on the failing interaction, the
service may exit into an arbitrary round state, and the service may also stop
the whole process in success. -/
theorem partialExitEntry_natBellmanSuperSolution
    {Round Reset : Type} {n scale A R : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetEntry : Round → Fin n → Reset)
    (serviceStep : Reset → Fin n → ServiceOutcome Reset Round)
    (roundPotential : StopNode Round → Nat)
    (resetPotential : Reset → Nat)
    (hround : NatBellmanSuperSolution roundStep scale roundPotential)
    (hservice : ServiceBellman serviceStep scale resetPotential)
    (hbalance : ∀ state,
      (List.ofFn (fun edge : Fin n =>
        failureWeight (roundStep state edge))).sum ≤
      (List.ofFn (fun edge : Fin n =>
        successWeight (roundStep state edge))).sum)
    (hexit : ∀ state edge r, serviceStep state edge = .exit r →
      roundPotential (.active r) ≤ A)
    (hentry : ∀ state edge, roundStep state edge = .failure →
      resetPotential (resetEntry state edge) ≤ R) :
    NatBellmanSuperSolution
      (partialExitEntryStep roundStep resetEntry serviceStep) scale
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
              (liftRoundOutcome (resetEntry state edge)
                (roundStep state edge)) ≤
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
            have hbound : resetPotential (resetEntry state edge) ≤ R :=
              hentry state edge hstep
            simp [liftRoundOutcome, partialExitPotential, credit,
              activeWeight, failureWeight, hroundFailure]
            omega
      have hchildren :
          (List.ofFn (fun edge : Fin n =>
            partialExitPotential roundPotential resetPotential A R
              (liftRoundOutcome (resetEntry state edge)
                (roundStep state edge)))).sum ≤
            (List.ofFn (fun edge : Fin n =>
              roundPotential (roundStep state edge))).sum +
              credit * activeMass + (2 * credit) * failureMass := by
        calc
          (List.ofFn (fun edge : Fin n =>
              partialExitPotential roundPotential resetPotential A R
                (liftRoundOutcome (resetEntry state edge)
                  (roundStep state edge)))).sum ≤
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
              (liftRoundOutcome (resetEntry state edge)
                (roundStep state edge)))).sum ≤
        n * (roundPotential (.active state) + credit)
      refine Nat.le_trans (Nat.add_le_add_left hchildren _) ?_
      have hmain := hroundBellman state
      have hcombined := Nat.add_le_add hmain hextra
      simpa [Nat.mul_add, Nat.add_assoc] using hcombined
  | reset state =>
      let baseCredit := A + credit
      have hchild (edge : Fin n) :
          partialExitPotential roundPotential resetPotential A R
              (liftServiceOutcome (serviceStep state edge)) ≤
            serviceOutcomePotential resetPotential (serviceStep state edge) +
              baseCredit := by
        cases hstep : serviceStep state edge with
        | cont next =>
            simp [liftServiceOutcome, partialExitPotential,
              serviceOutcomePotential, baseCredit, credit, Nat.add_assoc]
        | exit next =>
            have hbound : roundPotential (.active next) ≤ A :=
              hexit state edge next hstep
            simp [liftServiceOutcome, partialExitPotential,
              serviceOutcomePotential, baseCredit, credit]
            omega
        | succeed =>
            simp [liftServiceOutcome, partialExitPotential,
              serviceOutcomePotential]
      have hchildren :
          (List.ofFn (fun edge : Fin n =>
            partialExitPotential roundPotential resetPotential A R
              (liftServiceOutcome (serviceStep state edge)))).sum ≤
            (List.ofFn (fun edge : Fin n =>
              serviceOutcomePotential resetPotential
                (serviceStep state edge))).sum + n * baseCredit := by
        calc
          (List.ofFn (fun edge : Fin n =>
              partialExitPotential roundPotential resetPotential A R
                (liftServiceOutcome (serviceStep state edge)))).sum ≤
            (List.ofFn (fun edge : Fin n =>
              serviceOutcomePotential resetPotential (serviceStep state edge) +
                baseCredit)).sum := ofFn_sum_le _ _ hchild
          _ = (List.ofFn (fun edge : Fin n =>
                serviceOutcomePotential resetPotential
                  (serviceStep state edge))).sum +
              (List.ofFn (fun _ : Fin n => baseCredit)).sum :=
                ofFn_sum_add _ _
          _ = (List.ofFn (fun edge : Fin n =>
                serviceOutcomePotential resetPotential
                  (serviceStep state edge))).sum +
              n * baseCredit := by rw [ofFn_sum_const]
      change scale * n +
          (List.ofFn (fun edge : Fin n =>
            partialExitPotential roundPotential resetPotential A R
              (liftServiceOutcome (serviceStep state edge)))).sum ≤
        n * (resetPotential state + A + credit)
      refine Nat.le_trans (Nat.add_le_add_left hchildren _) ?_
      have hmain := hservice state
      have hcombined := Nat.add_le_add_right hmain (n * baseCredit)
      simpa [baseCredit, Nat.mul_add, Nat.add_assoc] using hcombined

/-- The composed process has no immediate bad terminal.  As in the imported
file this needs no hypothesis: the service has no failure port, and sidecar
success is a good terminal. -/
theorem partialExitEntryStep_ne_failure
    {Round Reset : Type} {n : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetEntry : Round → Fin n → Reset)
    (serviceStep : Reset → Fin n → ServiceOutcome Reset Round) :
    ∀ state edge,
      partialExitEntryStep roundStep resetEntry serviceStep state edge ≠
        .failure := by
  intro state edge
  cases state with
  | round state =>
      cases hstep : roundStep state edge <;>
        simp [partialExitEntryStep, liftRoundOutcome, hstep]
  | reset state =>
      cases hstep : serviceStep state edge <;>
        simp [partialExitEntryStep, liftServiceOutcome, hstep]

/-! ## Finite-horizon tail bound -/

/-- Reciprocal tail bound at any active composed state.  Everything generic is
reused from `FiniteUniformStoppingTree` and `BalancedFailureRestart`. -/
theorem pred_mul_pow_le_factor_mul_successCount_partialExitEntry
    {Round Reset : Type} {n factor A R : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetEntry : Round → Fin n → Reset)
    (serviceStep : Reset → Fin n → ServiceOutcome Reset Round)
    (roundPotential : StopNode Round → Nat)
    (resetPotential : Reset → Nat)
    (hround : NatBellmanSuperSolution roundStep 1 roundPotential)
    (hservice : ServiceBellman serviceStep 1 resetPotential)
    (hbalance : ∀ state,
      (List.ofFn (fun edge : Fin n =>
        failureWeight (roundStep state edge))).sum ≤
      (List.ofFn (fun edge : Fin n =>
        successWeight (roundStep state edge))).sum)
    (hexit : ∀ state edge r, serviceStep state edge = .exit r →
      roundPotential (.active r) ≤ A)
    (hentry : ∀ state edge, roundStep state edge = .failure →
      resetPotential (resetEntry state edge) ≤ R)
    (state : RestartState Round Reset)
    (hpositive : 0 <
      partialExitPotential roundPotential resetPotential A R (.active state)) :
    (factor - 1) *
        n ^ (factor *
          partialExitPotential roundPotential resetPotential A R
            (.active state)) ≤
      factor *
        successCount (partialExitEntryStep roundStep resetEntry serviceStep)
          (.active state)
          (factor *
            partialExitPotential roundPotential resetPotential A R
              (.active state)) :=
  BalancedFailureRestart.pred_mul_pow_le_factor_mul_successCount
    (partialExitEntryStep roundStep resetEntry serviceStep)
    (partialExitPotential roundPotential resetPotential A R)
    (partialExitEntry_natBellmanSuperSolution roundStep resetEntry serviceStep
      roundPotential resetPotential hround hservice hbalance hexit hentry)
    (partialExitEntryStep_ne_failure roundStep resetEntry serviceStep)
    state hpositive

/-- The reciprocal tail started at a round base.  With
`BalancedFailureRestartPartialExit.partialExitPotential_roundBase_le` this is
the `2 * A + R` budget. -/
theorem pred_mul_pow_le_factor_mul_successCount_partialExitEntry_roundBase
    {Round Reset : Type} {n factor A R : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetEntry : Round → Fin n → Reset)
    (serviceStep : Reset → Fin n → ServiceOutcome Reset Round)
    (roundBase : Round)
    (roundPotential : StopNode Round → Nat)
    (resetPotential : Reset → Nat)
    (hround : NatBellmanSuperSolution roundStep 1 roundPotential)
    (hservice : ServiceBellman serviceStep 1 resetPotential)
    (hbalance : ∀ state,
      (List.ofFn (fun edge : Fin n =>
        failureWeight (roundStep state edge))).sum ≤
      (List.ofFn (fun edge : Fin n =>
        successWeight (roundStep state edge))).sum)
    (hexit : ∀ state edge r, serviceStep state edge = .exit r →
      roundPotential (.active r) ≤ A)
    (hentry : ∀ state edge, roundStep state edge = .failure →
      resetPotential (resetEntry state edge) ≤ R)
    (hpositive : 0 < roundPotential (.active roundBase) + (A + R)) :
    (factor - 1) *
        n ^ (factor * (roundPotential (.active roundBase) + (A + R))) ≤
      factor *
        successCount (partialExitEntryStep roundStep resetEntry serviceStep)
          (.active (.round roundBase))
          (factor * (roundPotential (.active roundBase) + (A + R))) :=
  pred_mul_pow_le_factor_mul_successCount_partialExitEntry roundStep resetEntry
    serviceStep roundPotential resetPotential hround hservice hbalance hexit
    hentry (.round roundBase) hpositive

/-! ## The constant-entry, sidecar-free composition is the special case -/

/-- Read a sidecar-free service outcome as a service outcome. -/
def noSidecar {Reset Round : Type} :
    ResetOutcome Reset Round → ServiceOutcome Reset Round
  | .cont state => .cont state
  | .exit state => .exit state

/-- The sidecar-free service read as a service with a sidecar port. -/
def noSidecarStep {Reset Round : Type} {n : Nat}
    (resetStep : Reset → Fin n → ResetOutcome Reset Round) :
    Reset → Fin n → ServiceOutcome Reset Round :=
  fun state edge => noSidecar (resetStep state edge)

/-- The two liftings agree on sidecar-free outcomes. -/
theorem liftServiceOutcome_noSidecar {Round Reset : Type}
    (x : ResetOutcome Reset Round) :
    liftServiceOutcome (Round := Round) (noSidecar x) =
      liftPartialExitOutcome x := by
  cases x with
  | cont state => rfl
  | exit state => rfl

/-- Only an `exit` can come from a sidecar-free `exit`. -/
theorem eq_exit_of_noSidecar_eq_exit {Reset Round : Type}
    (x : ResetOutcome Reset Round) (r : Round)
    (hx : noSidecar (Round := Round) x = .exit r) : x = .exit r := by
  cases x with
  | cont state => exact absurd hx (by simp [noSidecar])
  | exit state =>
      have : state = r := by simpa [noSidecar] using hx
      subst this
      rfl

/-- With constant entry and no sidecar port, this composition is literally the
composition of the imported file. -/
theorem partialExitEntryStep_of_constant
    {Round Reset : Type} {n : Nat}
    (roundStep : Round → Fin n → StopNode Round)
    (resetStep : Reset → Fin n → ResetOutcome Reset Round)
    (resetBase : Reset) :
    partialExitEntryStep roundStep (fun _ _ => resetBase)
        (noSidecarStep resetStep) =
      partialExitStep roundStep resetStep resetBase := by
  funext state edge
  cases state with
  | round state => rfl
  | reset state => exact liftServiceOutcome_noSidecar (resetStep state edge)

/-- A sidecar-free Bellman certificate is a service Bellman certificate. -/
theorem serviceBellman_of_partialExitBellman
    {Round Reset : Type} {n scale : Nat}
    (resetStep : Reset → Fin n → ResetOutcome Reset Round)
    (resetPotential : Reset → Nat)
    (hreset : PartialExitBellman resetStep scale resetPotential) :
    ServiceBellman (noSidecarStep resetStep) scale resetPotential := by
  intro state
  have hpoint : ∀ edge : Fin n,
      serviceOutcomePotential resetPotential
          (noSidecarStep resetStep state edge) =
        resetOutcomePotential resetPotential (resetStep state edge) := by
    intro edge
    cases hstep : resetStep state edge with
    | cont next =>
        simp [noSidecarStep, noSidecar, serviceOutcomePotential,
          resetOutcomePotential, hstep]
    | exit next =>
        simp [noSidecarStep, noSidecar, serviceOutcomePotential,
          resetOutcomePotential, hstep]
  rw [ofFn_sum_eq _
    (fun edge => resetOutcomePotential resetPotential (resetStep state edge))
    hpoint]
  exact hreset state

/-- The partial-exit theorem of the imported file recovered as the special
case of constant entry and no sidecar success. -/
theorem partialExit_natBellmanSuperSolution_of_entry
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
  rw [← partialExitEntryStep_of_constant roundStep resetStep resetBase]
  exact partialExitEntry_natBellmanSuperSolution roundStep
    (fun _ _ => resetBase) (noSidecarStep resetStep) roundPotential
    resetPotential hround
    (serviceBellman_of_partialExitBellman resetStep resetPotential hreset)
    hbalance
    (fun state edge r hstep =>
      hexit state edge r
        (eq_exit_of_noSidecar_eq_exit (resetStep state edge) r hstep))
    (fun _ _ _ => hentry)

#print axioms partialExitEntry_natBellmanSuperSolution
#print axioms partialExitEntryStep_ne_failure
#print axioms pred_mul_pow_le_factor_mul_successCount_partialExitEntry
#print axioms pred_mul_pow_le_factor_mul_successCount_partialExitEntry_roundBase
#print axioms partialExit_natBellmanSuperSolution_of_entry

end BalancedFailureRestartPartialExitEntry
