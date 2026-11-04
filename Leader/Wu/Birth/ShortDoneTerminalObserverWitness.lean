import Leader.Wu.Birth.ShortDoneTerminalObserver
import Leader.Wu.Elimination.BirthDispatcherWitnesses

/-!
# Type and finite-witness audit for the terminal DONE observer

This file produces no no-birth invariant.  It only checks the exact consumer
successor occurring in `NoBirthAlong`, exhibits a finite nonempty word satisfying
that premise, checks the concrete alias semantics, and pins the full-width birth
event target.  The published positive birth fixture is recorded under its real
baseline event type and is intentionally not promoted to a terminal-host event.
-/

namespace BirthShortDoneTerminalObserverAudit

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
  K2OutputSafety
open ExpiringK2Projection LDSinkBoundedKernel

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ width κ τ n : Nat}

/-- Exact consumer type: no older row is hidden in `protocol`. -/
theorem transition_is_terminal_row (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) :
    (BirthShortDoneTerminalConsumer.protocol hψ hwidth hle κ τ).transition =
      BirthShortDoneTerminalHost.row hψ hwidth hle := rfl

/-- The recursive premise is definitionally on the actual newly computed
consumer successor. -/
theorem no_birth_cons_exact (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (es : List (Fin n)) :
    BirthShortDoneTerminalObserver.NoBirthAlong
        hψ hwidth hle ring C (e :: es) ↔
      BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle
          (C e) (C (ring.rightNeighbor e)) = false ∧
      BirthShortDoneTerminalObserver.NoBirthAlong hψ hwidth hle ring
        (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e) es :=
  Iff.rfl

private theorem hTwo : 0 < 2 := by decide
private def ringFour : DirectedRing 4 := ⟨by decide⟩

/-- An existing checked finite carrier value, used only as a state value.
Both old endpoint leader bits are true, so `newborn` is false independently of
what terminal metadata computes. -/
private def leadersFour : Fin 4 → ExpiringAgentState 2 2 3 :=
  fun _ => ExpiringK2Projection.Example.hostLeft

private theorem local_no_birth (e : Fin 4) :
    BirthShortDoneTerminalObserver.birthEvent hTwo hTwo (Nat.le_refl 2)
      (leadersFour e) (leadersFour (ringFour.rightNeighbor e)) = false := by
  simp [BirthShortDoneTerminalObserver.birthEvent,
    K2BirthDispatcher.newborn, leadersFour,
    ExpiringK2Projection.Example.hostLeft]

/-- This is the actual successor after the first scheduled terminal-consumer
step, not an observed or shadow configuration. -/
private def afterZero : Fin 4 → ExpiringAgentState 2 2 3 :=
  BirthShortDoneTerminalConsumer.step hTwo hTwo (Nat.le_refl 2)
    ringFour leadersFour 0

private theorem afterZero_two : afterZero 2 = leadersFour 2 := by
  unfold afterZero
  exact BirthShortDoneTerminalConsumer.step_other
    hTwo hTwo (Nat.le_refl 2) ringFour leadersFour 0 2
    (by decide) (by decide)

private theorem afterZero_right_two :
    afterZero (ringFour.rightNeighbor 2) =
      leadersFour (ringFour.rightNeighbor 2) := by
  unfold afterZero
  exact BirthShortDoneTerminalConsumer.step_other
    hTwo hTwo (Nat.le_refl 2) ringFour leadersFour 0
      (ringFour.rightNeighbor 2) (by decide) (by decide)

/-- The second event is checked on the actual successor.  No global closure
premise is assumed: it follows only because edge 2->3 is disjoint from 0->1. -/
private theorem second_no_birth_on_actual_successor :
    BirthShortDoneTerminalObserver.birthEvent hTwo hTwo (Nat.le_refl 2)
      (afterZero 2) (afterZero (ringFour.rightNeighbor 2)) = false := by
  rw [afterZero_two, afterZero_right_two]
  exact local_no_birth 2

/-- Nonvacuous two-edge witness for the exact recursive premise. -/
theorem two_step_no_birth :
    BirthShortDoneTerminalObserver.NoBirthAlong
      hTwo hTwo (Nat.le_refl 2) ringFour leadersFour
      ([0, 2] : List (Fin 4)) := by
  refine ⟨local_no_birth 0, ?_⟩
  refine ⟨?_, trivial⟩
  simpa [afterZero] using second_no_birth_on_actual_successor

/-- The all-prefix theorem consumes that exact finite witness and exactly the
same `take` word on the terminal consumer and shadow runs. -/
theorem two_step_all_prefixes (t : Nat) :
    ExpiringK2Projection.observe
        (run (BirthShortDoneTerminalConsumer.step
          hTwo hTwo (Nat.le_refl 2) ringFour)
          leadersFour (([0, 2] : List (Fin 4)).take t)) =
      run (K2BirthDispatcher.shadowStep ringFour)
        (ExpiringK2Projection.observe leadersFour)
        (([0, 2] : List (Fin 4)).take t) :=
  BirthShortDoneTerminalObserver.observe_all_prefixes_of_no_birth
    hTwo hTwo (Nat.le_refl 2) ringFour leadersFour
      ([0, 2] : List (Fin 4)) two_step_no_birth t

private def ringOneAudit : DirectedRing 1 := ⟨by decide⟩
private def leaderOne : Fin 1 → ExpiringAgentState 2 2 3 :=
  fun _ => ExpiringK2Projection.Example.hostLeft

private theorem ringOne_alias :
    ringOneAudit.rightNeighbor (0 : Fin 1) = 0 := by decide

private theorem alias_no_birth :
    BirthShortDoneTerminalObserver.birthEvent hTwo hTwo (Nat.le_refl 2)
      (leaderOne 0) (leaderOne 0) = false := by
  simp [BirthShortDoneTerminalObserver.birthEvent,
    K2BirthDispatcher.newborn, leaderOne,
    ExpiringK2Projection.Example.hostLeft]

/-- Concrete self-edge consumer equality: the left host-row output wins. -/
theorem actual_alias_left_output :
    BirthShortDoneTerminalConsumer.step hTwo hTwo (Nat.le_refl 2)
        ringOneAudit leaderOne 0 0 =
      (BirthShortDoneTerminalHost.row hTwo hTwo (Nat.le_refl 2)
        (leaderOne 0) (leaderOne 0)).1 :=
  BirthShortDoneTerminalConsumer.step_alias
    hTwo hTwo (Nat.le_refl 2) ringOneAudit leaderOne 0 ringOne_alias

/-- And the observer's alias theorem is typed on that same actual consumer. -/
theorem actual_alias_observation :
    observeCell
        (BirthShortDoneTerminalConsumer.step hTwo hTwo (Nat.le_refl 2)
          ringOneAudit leaderOne 0 0) =
      (K2BirthDispatcher.shadowRow
        (observeCell (leaderOne 0)) (observeCell (leaderOne 0))).1 :=
  BirthShortDoneTerminalObserver.observe_step_alias_of_no_birth
    hTwo hTwo (Nat.le_refl 2) ringOneAudit leaderOne 0
      ringOne_alias alias_no_birth

/-- At full width, the terminal event targets the published DONE-normalized
metadata host -- not the older baseline `K2BirthDispatcher.birthEvent`. -/
theorem full_width_birth_target (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    BirthShortDoneTerminalObserver.birthEvent hψ hψ (Nat.le_refl ψ) l r =
      K2BirthDoneNormalize.birthEvent hψ l r := by
  unfold BirthShortDoneTerminalObserver.birthEvent
    K2BirthDoneNormalize.birthEvent
  rw [BirthShortDoneTerminalHost.metadata_full hψ l r]

/-- This is the existing checked positive fixture under its exact published
baseline type.  It is deliberately NOT stated as a terminal-host birth. -/
theorem checked_positive_is_baseline :
    K2BirthDispatcher.birthEvent hTwo
      (K2BirthDispatcher.Witnesses.positiveRun 12 2)
      (K2BirthDispatcher.Witnesses.positiveRun 12 3) = true :=
  K2BirthDispatcher.Witnesses.positive_last_event

end BirthShortDoneTerminalObserverAudit

#print axioms BirthShortDoneTerminalObserverAudit.transition_is_terminal_row

#print axioms BirthShortDoneTerminalObserverAudit.no_birth_cons_exact

#print axioms BirthShortDoneTerminalObserverAudit.two_step_no_birth

#print axioms BirthShortDoneTerminalObserverAudit.two_step_all_prefixes

#print axioms BirthShortDoneTerminalObserverAudit.actual_alias_left_output

#print axioms BirthShortDoneTerminalObserverAudit.actual_alias_observation

#print axioms BirthShortDoneTerminalObserverAudit.full_width_birth_target

#print axioms BirthShortDoneTerminalObserverAudit.checked_positive_is_baseline
