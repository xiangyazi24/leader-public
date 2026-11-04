import Leader.Core.Basic
import Leader.Wu.Protocol.FiniteState

set_option autoImplicit false

/-!
# Global fairness for finite transition systems

This module formalizes the deterministic fairness argument used by Angluin,
Aspnes, Fischer, and Jiang, *Self-stabilizing population protocols*,
Definition 2.1 and Theorem 2.2 (in the input-free specialization).

Global fairness is stated in terms of result states: if a state occurs
infinitely often, then every possible one-step successor also occurs
infinitely often.  It is not edge fairness and carries no probability,
runtime, or scheduler-distribution assumptions.

The abstract layer first proves the finite-state theorem for an arbitrary
transition relation.  The final namespace adapts that theorem to the existing
`PopulationProtocol.OneStep`, `PopulationProtocol.Reachable`, and
`PopulationProtocol.ClosedPred` definitions in `Leader.Core.Basic`.
-/

universe u

namespace ExhaustiveList

/-- Enumerate all functions on `Fin n` from an exhaustive list of values.
No duplicate-freedom or decidable equality is required. -/
def finFunctions {Q : Type u} (e : ExhaustiveList Q) :
    (n : Nat) → ExhaustiveList (Fin n → Q)
  | 0 =>
      { values := [fun i : Fin 0 => (Fin.elim0 i : Q)]
        complete := by
          intro f
          apply List.mem_singleton.mpr
          funext i
          exact Fin.elim0 i }
  | n + 1 =>
      ExhaustiveList.mapSurjective
        (ExhaustiveList.prod e (finFunctions e n))
        (fun p : Q × (Fin n → Q) =>
          fun i : Fin (n + 1) => Fin.cases p.1 p.2 i)
        (by
          intro f
          refine ⟨(f 0, fun j => f j.succ), ?_⟩
          funext i
          refine Fin.cases ?_ ?_ i
          · rfl
          · intro j
            rfl)

end ExhaustiveList

namespace FiniteTransitionSystem

/-- A state occurs infinitely often along `execution` when it occurs after
every finite cutoff. -/
def OccursInfinitelyOften {State : Type u}
    (execution : Nat → State) (state : State) : Prop :=
  ∀ cutoff : Nat, ∃ time : Nat, cutoff ≤ time ∧ execution time = state

/-- A target is reached at some point of an execution. -/
def Eventually {State : Type u}
    (execution : Nat → State) (Target : State → Prop) : Prop :=
  ∃ time : Nat, Target (execution time)

/-- From some point onward every state of the execution lies in `Target`. -/
def EventuallyAlways {State : Type u}
    (execution : Nat → State) (Target : State → Prop) : Prop :=
  ∃ start : Nat, ∀ time : Nat, start ≤ time → Target (execution time)

/-- Reflexive-transitive reachability for an abstract transition relation. -/
inductive Reachable {State : Type u} (Step : State → State → Prop) :
    State → State → Prop where
  | refl (state : State) : Reachable Step state state
  | step {start middle finish : State} :
      Reachable Step start middle → Step middle finish →
        Reachable Step start finish

/-- A state predicate is closed under every permitted one-step transition. -/
def ClosedPred {State : Type u} (Step : State → State → Prop)
    (Target : State → Prop) : Prop :=
  ∀ {state next}, Target state → Step state next → Target next

/-- A closed predicate is preserved along every finite reachable fragment. -/
theorem ClosedPred.reachable {State : Type u} {Step : State → State → Prop}
    {Target : State → Prop} (hclosed : ClosedPred Step Target)
    {start finish : State} (hstart : Target start)
    (hreach : Reachable Step start finish) : Target finish := by
  induction hreach with
  | refl => exact hstart
  | step _ hstep ih => exact hclosed ih hstep

/-- An infinite execution is legal when each consecutive pair is a permitted
transition. -/
def LegalExecution {State : Type u} (Step : State → State → Prop)
    (execution : Nat → State) : Prop :=
  ∀ time : Nat, Step (execution time) (execution (time + 1))

/-- AAFJ global fairness, specialized to a transition system with no inputs:
every possible successor of an infinitely recurring state also recurs
infinitely often. -/
def GlobalFair {State : Type u} (Step : State → State → Prop)
    (execution : Nat → State) : Prop :=
  ∀ {state next}, Step state next →
    OccursInfinitelyOften execution state →
    OccursInfinitelyOften execution next

/-- A legal execution together with AAFJ global fairness. -/
structure GloballyFairExecution {State : Type u}
    (Step : State → State → Prop) (execution : Nat → State) : Prop where
  legal : LegalExecution Step execution
  fair : GlobalFair Step execution

/-- AAFJ Theorem 2.2 in the input-free setting: global fairness propagates
infinite recurrence along every finite possible execution fragment. -/
theorem occursInfinitelyOften_of_reachable
    {State : Type u} {Step : State → State → Prop}
    {execution : Nat → State} (hfair : GlobalFair Step execution)
    {start finish : State}
    (hstart : OccursInfinitelyOften execution start)
    (hreach : Reachable Step start finish) :
    OccursInfinitelyOften execution finish := by
  induction hreach with
  | refl => exact hstart
  | step _ hstep ih => exact hfair hstep ih

/-- A later point of a legal execution is reachable from every earlier point. -/
theorem reachable_of_time_le
    {State : Type u} {Step : State → State → Prop}
    {execution : Nat → State} (hlegal : LegalExecution Step execution)
    {start finish : Nat} (horder : start ≤ finish) :
    Reachable Step (execution start) (execution finish) := by
  induction horder with
  | refl => exact .refl _
  | @step time _ ih => exact .step ih (hlegal time)

private theorem list_has_infinite_recurrence
    {State : Type u} (states : List State) (execution : Nat → State)
    (hcover : ∀ time, execution time ∈ states) :
    ∃ state, state ∈ states ∧ OccursInfinitelyOften execution state := by
  classical
  induction states generalizing execution with
  | nil =>
      exact False.elim (by simpa using hcover 0)
  | cons head tail ih =>
      by_cases hhead : OccursInfinitelyOften execution head
      · exact ⟨head, by simp, hhead⟩
      · obtain ⟨cutoff, hcutoff⟩ := Classical.not_forall.mp hhead
        have htail : ∀ time, execution (cutoff + time) ∈ tail := by
          intro time
          rcases List.mem_cons.mp (hcover (cutoff + time)) with heq | hmem
          · exact False.elim (hcutoff ⟨cutoff + time, by omega, heq⟩)
          · exact hmem
        obtain ⟨state, hmem, hinfinite⟩ :=
          ih (fun time => execution (cutoff + time)) htail
        refine ⟨state, List.Mem.tail head hmem, ?_⟩
        intro lower
        obtain ⟨time, htime, heq⟩ := hinfinite lower
        exact ⟨cutoff + time, by omega, heq⟩

/-- Every infinite sequence over an explicitly finite state space has an
infinitely recurring state. -/
theorem exists_occursInfinitelyOften_of_exhaustive
    {State : Type u} (states : ExhaustiveList State)
    (execution : Nat → State) :
    ∃ state, OccursInfinitelyOften execution state := by
  obtain ⟨state, _, hinfinite⟩ :=
    list_has_infinite_recurrence states.values execution
      (fun time => states.complete (execution time))
  exact ⟨state, hinfinite⟩

/-- In a finite system, if every state has a finite path to `Target`, every
globally fair execution eventually reaches `Target`.  This is the qualitative
entrance implication used in AAFJ Theorem 9.3. -/
theorem eventually_of_finite_globalFair_reachable
    {State : Type u} {Step : State → State → Prop}
    (states : ExhaustiveList State) {execution : Nat → State}
    (hfair : GlobalFair Step execution)
    {Target : State → Prop}
    (hreaches : ∀ state, ∃ target,
      Reachable Step state target ∧ Target target) :
    Eventually execution Target := by
  obtain ⟨state, hinfinite⟩ :=
    exists_occursInfinitelyOften_of_exhaustive states execution
  obtain ⟨target, hreach, htarget⟩ := hreaches state
  have htargetInfinite :=
    occursInfinitelyOften_of_reachable hfair hinfinite hreach
  obtain ⟨time, _, heq⟩ := htargetInfinite 0
  exact ⟨time, heq.symm ▸ htarget⟩

/-- If the target is also closed, a legal globally fair execution reaches it
once and remains there forever. -/
theorem eventuallyAlways_of_finite_globalFair_reachable_closed
    {State : Type u} {Step : State → State → Prop}
    (states : ExhaustiveList State) {execution : Nat → State}
    (hlegal : LegalExecution Step execution)
    (hfair : GlobalFair Step execution)
    {Target : State → Prop}
    (hreaches : ∀ state, ∃ target,
      Reachable Step state target ∧ Target target)
    (hclosed : ClosedPred Step Target) :
    EventuallyAlways execution Target := by
  obtain ⟨start, hstart⟩ :=
    eventually_of_finite_globalFair_reachable states hfair hreaches
  refine ⟨start, ?_⟩
  intro time horder
  exact hclosed.reachable hstart (reachable_of_time_le hlegal horder)

end FiniteTransitionSystem

namespace PopulationProtocol.GlobalFairness

abbrev OccursInfinitelyOften {State : Type u} :=
  @FiniteTransitionSystem.OccursInfinitelyOften State

abbrev Eventually {State : Type u} :=
  @FiniteTransitionSystem.Eventually State

abbrev EventuallyAlways {State : Type u} :=
  @FiniteTransitionSystem.EventuallyAlways State

/-- A legal infinite execution of a population protocol. -/
def InfiniteExecution {n : Nat} (P : PopulationProtocol) (ring : DirectedRing n)
    (execution : Nat → P.Configuration n) : Prop :=
  FiniteTransitionSystem.LegalExecution (P.OneStep ring) execution

/-- AAFJ configuration-result global fairness for a population protocol. -/
def GlobalFair {n : Nat} (P : PopulationProtocol) (ring : DirectedRing n)
    (execution : Nat → P.Configuration n) : Prop :=
  FiniteTransitionSystem.GlobalFair (P.OneStep ring) execution

/-- A legal globally fair population-protocol execution. -/
structure GloballyFairExecution {n : Nat} (P : PopulationProtocol)
    (ring : DirectedRing n) (execution : Nat → P.Configuration n) : Prop where
  legal : InfiniteExecution P ring execution
  fair : GlobalFair P ring execution

/-- Existing population-protocol reachability embeds into the abstract finite
transition-system reachability relation. -/
theorem reachable_to_abstract
    {n : Nat} {P : PopulationProtocol} {ring : DirectedRing n}
    {start finish : P.Configuration n}
    (hreach : PopulationProtocol.Reachable P ring start finish) :
    FiniteTransitionSystem.Reachable (P.OneStep ring) start finish := by
  induction hreach with
  | refl => exact .refl _
  | step _ _ _ hstep ih => exact .step ih hstep

/-- Abstract reachability for the one-step protocol relation is exactly the
repository's existing population-protocol reachability. -/
theorem reachable_of_abstract
    {n : Nat} {P : PopulationProtocol} {ring : DirectedRing n}
    {start finish : P.Configuration n}
    (hreach : FiniteTransitionSystem.Reachable (P.OneStep ring) start finish) :
    PopulationProtocol.Reachable P ring start finish := by
  induction hreach with
  | refl => exact .refl _
  | step hreach hstep ih => exact .step _ _ _ ih hstep

/-- Population-protocol closure is the abstract closure condition for its
one-step transition relation. -/
theorem closedPred_to_abstract
    {n : Nat} {P : PopulationProtocol} {ring : DirectedRing n}
    {Target : P.Configuration n → Prop}
    (hclosed : PopulationProtocol.ClosedPred P ring Target) :
    FiniteTransitionSystem.ClosedPred (P.OneStep ring) Target := by
  intro state next hstate hstep
  exact hclosed state hstate next hstep

/-- A finite local-state certificate induces a finite global-configuration
certificate for every fixed population size. -/
def configurationCertificate (P : PopulationProtocol)
    (states : ExhaustiveList P.Q) (n : Nat) :
    ExhaustiveList (P.Configuration n) :=
  states.finFunctions n

/-- AAFJ Theorem 2.2 specialized to the repository's population-protocol
reachability relation. -/
theorem occursInfinitelyOften_of_reachable
    {n : Nat} {P : PopulationProtocol} {ring : DirectedRing n}
    {execution : Nat → P.Configuration n}
    (hfair : GlobalFair P ring execution)
    {start finish : P.Configuration n}
    (hstart : OccursInfinitelyOften execution start)
    (hreach : PopulationProtocol.Reachable P ring start finish) :
    OccursInfinitelyOften execution finish :=
  FiniteTransitionSystem.occursInfinitelyOften_of_reachable
    hfair hstart (reachable_to_abstract hreach)

/-- Statewise finite reachability of a target implies eventual entrance along
every globally fair population-protocol execution on a finite configuration
space. -/
theorem eventually_of_finite_globalFair_reachable
    {n : Nat} {P : PopulationProtocol} {ring : DirectedRing n}
    (configurations : ExhaustiveList (P.Configuration n))
    {execution : Nat → P.Configuration n}
    (hfair : GlobalFair P ring execution)
    {Target : P.Configuration n → Prop}
    (hreaches : ∀ state, ∃ target,
      PopulationProtocol.Reachable P ring state target ∧ Target target) :
    Eventually execution Target := by
  apply FiniteTransitionSystem.eventually_of_finite_globalFair_reachable
    configurations hfair
  intro state
  obtain ⟨target, hreach, htarget⟩ := hreaches state
  exact ⟨target, reachable_to_abstract hreach, htarget⟩

/-- Statewise reachability plus closure gives permanent stabilization along
every legal globally fair execution on a finite configuration space. -/
theorem eventuallyAlways_of_finite_globalFair_reachable_closed
    {n : Nat} {P : PopulationProtocol} {ring : DirectedRing n}
    (configurations : ExhaustiveList (P.Configuration n))
    {execution : Nat → P.Configuration n}
    (hlegal : InfiniteExecution P ring execution)
    (hfair : GlobalFair P ring execution)
    {Target : P.Configuration n → Prop}
    (hreaches : ∀ state, ∃ target,
      PopulationProtocol.Reachable P ring state target ∧ Target target)
    (hclosed : PopulationProtocol.ClosedPred P ring Target) :
    EventuallyAlways execution Target := by
  apply FiniteTransitionSystem.eventuallyAlways_of_finite_globalFair_reachable_closed
    configurations hlegal hfair
  · intro state
    obtain ⟨target, hreach, htarget⟩ := hreaches state
    exact ⟨target, reachable_to_abstract hreach, htarget⟩
  · exact closedPred_to_abstract hclosed

/-- Source-shaped capstone: on a finite configuration space, statewise finite
reachability of a closed target makes every legal globally fair execution
eventually enter that target. -/
theorem eventually_of_globallyFair_reachable_closed
    {n : Nat} {P : PopulationProtocol} {ring : DirectedRing n}
    (configurations : ExhaustiveList (P.Configuration n))
    {execution : Nat → P.Configuration n}
    (hexecution : GloballyFairExecution P ring execution)
    {Target : P.Configuration n → Prop}
    (hreaches : ∀ state, ∃ target,
      PopulationProtocol.Reachable P ring state target ∧ Target target)
    (hclosed : PopulationProtocol.ClosedPred P ring Target) :
    Eventually execution Target := by
  obtain ⟨start, hstable⟩ :=
    eventuallyAlways_of_finite_globalFair_reachable_closed
      configurations hexecution.legal hexecution.fair hreaches hclosed
  exact ⟨start, hstable start (Nat.le_refl start)⟩

/-- The stronger stabilization form of the source-shaped capstone: after the
first target entry, closure keeps every later execution state in the target. -/
theorem eventuallyAlways_of_globallyFair_reachable_closed
    {n : Nat} {P : PopulationProtocol} {ring : DirectedRing n}
    (configurations : ExhaustiveList (P.Configuration n))
    {execution : Nat → P.Configuration n}
    (hexecution : GloballyFairExecution P ring execution)
    {Target : P.Configuration n → Prop}
    (hreaches : ∀ state, ∃ target,
      PopulationProtocol.Reachable P ring state target ∧ Target target)
    (hclosed : PopulationProtocol.ClosedPred P ring Target) :
    EventuallyAlways execution Target :=
  eventuallyAlways_of_finite_globalFair_reachable_closed
    configurations hexecution.legal hexecution.fair hreaches hclosed

end PopulationProtocol.GlobalFairness

#print axioms FiniteTransitionSystem.occursInfinitelyOften_of_reachable
#print axioms FiniteTransitionSystem.eventually_of_finite_globalFair_reachable
#print axioms FiniteTransitionSystem.eventuallyAlways_of_finite_globalFair_reachable_closed
#print axioms PopulationProtocol.GlobalFairness.eventually_of_finite_globalFair_reachable
#print axioms PopulationProtocol.GlobalFairness.eventuallyAlways_of_finite_globalFair_reachable_closed
#print axioms PopulationProtocol.GlobalFairness.eventually_of_globallyFair_reachable_closed
#print axioms PopulationProtocol.GlobalFairness.eventuallyAlways_of_globallyFair_reachable_closed
