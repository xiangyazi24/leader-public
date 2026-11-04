import Leader.Wu.Comparison.ExpiringRepair
import Leader.Wu.Elimination.NearestPeaceful

/-!
# A K2-only replacement row on the existing expiring carrier

The physical carrier is unchanged. In particular no UNode controller is
manufactured, and the observation at modulus one is not a stored component.
The row below invokes the existing K2 kernel, then writes exactly its four
physical fields back to the two original endpoints. It is a new stage, not
an equivalence claim for the complete generation/birth host.
-/

namespace ExpiringK2Projection

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  LDSinkBoundedKernel LDSinkKernelC K2OutputSafety
  PPLLNoCheckBirthConditionTwoProtocol

set_option autoImplicit false

variable {ψ κ τ n : Nat}

/-- Full legacy erasure, retaining the real physical labels and controls. -/
def physicalConfig (C : Fin n → ExpiringAgentState ψ κ τ) :
    Fin n → AgentState ψ := fun i => (C i).core.core.erase

/-- The actual existing four-field observation; its label is the sole Fin 1. -/
def observeCell (q : ExpiringAgentState ψ κ τ) : AgentState 1 :=
  signalView q.core.core.erase

def observe (C : Fin n → ExpiringAgentState ψ κ τ) : Fin n → AgentState 1 :=
  fun i => observeCell (C i)

/-- A lens into the original endpoint. Every field other than these four
comes from q, including the permit and its possibly zero stall counter. -/
def putSignals (q : ExpiringAgentState ψ κ τ) (v : AgentState 1) :
    ExpiringAgentState ψ κ τ :=
  { q with core := { q.core with core := { q.core.core with
    leader := v.leader, shield := v.shield, bullet := v.bullet,
    signal_B := v.signal_B } } }

@[simp] theorem observe_putSignals (q : ExpiringAgentState ψ κ τ)
    (v : AgentState 1) : observeCell (putSignals q v) = signalView v := rfl

@[simp] theorem putSignals_twice (q : ExpiringAgentState ψ κ τ)
    (u v : AgentState 1) : putSignals (putSignals q u) v = putSignals q v := rfl

@[simp] theorem putSignals_self (q : ExpiringAgentState ψ κ τ) :
    putSignals q (observeCell q) = q := by
  cases q with
  | mk auth stall =>
    cases auth with
    | mk legacy permit => cases legacy <;> rfl

/-- Restoring only the four input signal fields recovers the entire input,
so this equality frames all remaining fields, not merely selected controls. -/
theorem putSignals_restore (q : ExpiringAgentState ψ κ τ) (v : AgentState 1) :
    putSignals (putSignals q v) (observeCell q) = q := by
  rw [putSignals_twice, putSignals_self]

/-- Only a proof-side comparison key: all non-K2 fields remain present. -/
def nonK2 (q : ExpiringAgentState ψ κ τ) : ExpiringAgentState ψ κ τ :=
  putSignals q (PeaceView.toState ⟨false, 0, false, 0, 0⟩)

@[simp] theorem nonK2_putSignals (q : ExpiringAgentState ψ κ τ)
    (v : AgentState 1) : nonK2 (putSignals q v) = nonK2 q := rfl

/-- Actual FIRE/MOVE/SIGNAL/dummy-sink execution on the four real fields. -/
def row (_hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := sinkKernelC (by decide) (observeCell l) (observeCell r)
  (putSignals l q.1, putSignals r q.2)

theorem observe_row (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    (observeCell (row hψ l r).1, observeCell (row hψ l r).2) =
      sinkKernelC (by decide) (observeCell l) (observeCell r) := by
  have h := signal_kernel (by decide : 0 < 1) (observeCell l) (observeCell r)
    (Or.inl (Subsingleton.elim _ _))
  exact h

theorem row_frame (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    putSignals (row hψ l r).1 (observeCell l) = l ∧
      putSignals (row hψ l r).2 (observeCell r) = r :=
  ⟨putSignals_restore l _, putSignals_restore r _⟩

theorem row_nonK2 (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    nonK2 (row hψ l r).1 = nonK2 l ∧
      nonK2 (row hψ l r).2 = nonK2 r := ⟨rfl, rfl⟩

/-- These controls in particular are not sanitized or reinitialized by K2. -/
theorem row_controls (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    (row hψ l r).1.core.core.state = l.core.core.state ∧
    (row hψ l r).1.core.core.path2 = l.core.core.path2 ∧
    (row hψ l r).1.core.core.wait = l.core.core.wait ∧
    (row hψ l r).1.core.core.count = l.core.core.count ∧
    (row hψ l r).1.core.path0Crossed = l.core.path0Crossed ∧
    (row hψ l r).1.stall = l.stall ∧
    (row hψ l r).2.core.core.state = r.core.core.state ∧
    (row hψ l r).2.core.core.path2 = r.core.core.path2 ∧
    (row hψ l r).2.core.core.wait = r.core.core.wait ∧
    (row hψ l r).2.core.core.count = r.core.core.count ∧
    (row hψ l r).2.core.path0Crossed = r.core.path0Crossed ∧
    (row hψ l r).2.stall = r.stall := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def protocol (hψ : 0 < ψ) (κ τ : Nat) : PopulationProtocol where
  Q := ExpiringAgentState ψ κ τ
  Y := Bool
  transition := row hψ
  output := fun q => q.core.core.leader

abbrev step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n) :
    Fin n → ExpiringAgentState ψ κ τ := (protocol hψ κ τ).step ring C e

/-- Exactly one scheduler symbol becomes exactly one real K2 edge. The
population-protocol endpoint priority is preserved even on a singleton ring. -/
theorem observe_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n) :
    observe (step hψ ring C e) = rawStep (by decide) ring (observe C) e := by
  have hq := observe_row hψ (C e) (C (ring.rightNeighbor e))
  funext i
  simp only [observe, step, PopulationProtocol.step, protocol, rawStep,
    updatePair]
  split
  · exact congrArg Prod.fst hq
  · split
    · exact congrArg Prod.snd hq
    · rfl

theorem step_frame (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e i : Fin n) :
    putSignals (step hψ ring C e i) (observeCell (C i)) = C i := by
  unfold step PopulationProtocol.step protocol
  by_cases he : i = e
  · subst i
    simpa using (row_frame hψ (C e) (C (ring.rightNeighbor e))).1
  · by_cases hr : i = ring.rightNeighbor e
    · subst i
      simpa [he] using (row_frame hψ (C e) (C (ring.rightNeighbor e))).2
    · simp only [if_neg he, if_neg hr, putSignals_self]

/-- Complete words preserve all original non-K2 fields at their own sites. -/
theorem run_frame (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n)) (i : Fin n) :
    putSignals (run (step hψ ring) C es i) (observeCell (C i)) = C i := by
  induction es generalizing C with
  | nil => exact putSignals_self (C i)
  | cons e es ih =>
    have h := congrArg (fun q => putSignals q (observeCell (C i)))
      (ih (step hψ ring C e))
    simpa only [putSignals_twice, step_frame, run] using h

theorem run_nonK2 (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n)) (i : Fin n) :
    nonK2 (run (step hψ ring) C es i) = nonK2 (C i) := by
  have h := congrArg nonK2 (run_frame hψ ring C es i)
  simpa only [nonK2_putSignals] using h

theorem observe_run (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n)) :
    observe (run (step hψ ring) C es) =
      run (rawStep (by decide) ring) (observe C) es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih => simp only [run, ih, observe_step]

theorem run_output (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n)) (i : Fin n) :
    (run (step hψ ring) C es i).core.core.leader =
      (run (rawStep (by decide) ring) (observe C) es i).leader :=
  congrArg AgentState.leader (congrFun (observe_run hψ ring C es) i)

/-- If a UCell configuration is separately supplied with these four fields,
the two actual stages have identical observations along the same entire word.
This is a relation, not a fabricated physical UNode embedding. -/
theorem same_word_ucell (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (D : Fin n → StateBoundUnifiedCell.UCell ψ κ)
    (h : observe C = LabelFreeElimination.observe D) (es : List (Fin n)) :
    observe (run (step hψ ring) C es) =
      LabelFreeElimination.observe (run (LabelFreeElimination.step hψ ring) D es) := by
  rw [observe_run, LabelFreeElimination.observe_run, h]

end ExpiringK2Projection

#print axioms ExpiringK2Projection.observe_row
#print axioms ExpiringK2Projection.row_controls
#print axioms ExpiringK2Projection.run_frame
#print axioms ExpiringK2Projection.observe_run
#print axioms ExpiringK2Projection.same_word_ucell
