import Leader.Wu.Elimination.BirthDispatcher

/-! Same physical ring, same edge word, complete endpoint observations.
The condition below tests the actual evolving mixed execution. It is not a
producer of an interval satisfying the condition. No physical phase is reset. -/

namespace K2BirthDispatcher

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  LDSinkBoundedKernel ExpiringK2Projection

set_option autoImplicit false
set_option pp.structureInstances false

variable {ψ κ τ n : Nat}

attribute [local irreducible] row metadata birthEvent

theorem observe_step_of_no_birth (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (hn : birthEvent hψ (C e) (C (ring.rightNeighbor e)) = false) :
    ExpiringK2Projection.observe (step hψ ring C e) = shadowStep ring (ExpiringK2Projection.observe C) e := by
  have hq := observe_row_of_no_birth hψ (C e) (C (ring.rightNeighbor e)) hn
  funext i
  simp only [ExpiringK2Projection.observe, step, PopulationProtocol.step, protocol, shadowStep, updatePair]
  split
  · exact congrArg Prod.fst hq
  · split
    · exact congrArg Prod.snd hq
    · rfl

/-- A proof-side recursive condition on the actual mixed states at each
successive scheduled edge. The complete state is passed to every successor. -/
def NoBirthAlong (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) : List (Fin n) → Prop
  | [] => True
  | e :: es => birthEvent hψ (C e) (C (ring.rightNeighbor e)) = false ∧
      NoBirthAlong hψ ring (step hψ ring C e) es

theorem NoBirthAlong.take (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hn : NoBirthAlong hψ ring C es) (t : Nat) :
    NoBirthAlong hψ ring C (es.take t) := by
  induction t generalizing C es with
  | zero => trivial
  | succ t ih =>
    cases es with
    | nil => trivial
    | cons e es => exact ⟨hn.1, ih _ _ hn.2⟩

theorem observe_run_of_no_birth (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hn : NoBirthAlong hψ ring C es) :
    ExpiringK2Projection.observe (run (step hψ ring) C es) = run (shadowStep ring) (ExpiringK2Projection.observe C) es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
    simpa only [run, observe_step_of_no_birth hψ ring C e hn.1] using
      ih (step hψ ring C e) hn.2

/-- Every raw prefix has the same observed endpoint, not merely the final
prefix or a stopped/successful outcome. The scheduler word is unchanged. -/
theorem observe_all_prefixes_of_no_birth (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hn : NoBirthAlong hψ ring C es) (t : Nat) :
    ExpiringK2Projection.observe (run (step hψ ring) C (es.take t)) =
      run (shadowStep ring) (ExpiringK2Projection.observe C) (es.take t) :=
  observe_run_of_no_birth hψ ring C _ (NoBirthAlong.take hψ ring C es hn t)

/-- Direct equality to the frozen actual AdjacentLeaderElimination system.
The UCell configuration is supplied by the caller; no UNode or physical
state is invented to furnish it. Only initial observation equality is used. -/
theorem same_word_adjacent (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (D : Fin n → StateBoundUnifiedCell.UCell ψ κ) (es : List (Fin n))
    (h0 : ExpiringK2Projection.observe C = LabelFreeElimination.observe D)
    (hn : NoBirthAlong hψ ring C es) :
    ExpiringK2Projection.observe (run (step hψ ring) C es) =
      LabelFreeElimination.observe (run (AdjacentLeaderElimination.step hψ ring) D es) := by
  rw [observe_run_of_no_birth hψ ring C es hn, adjacent_observe_run hψ ring D es, h0]

theorem same_word_adjacent_all_prefixes (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (D : Fin n → StateBoundUnifiedCell.UCell ψ κ) (es : List (Fin n))
    (h0 : ExpiringK2Projection.observe C = LabelFreeElimination.observe D)
    (hn : NoBirthAlong hψ ring C es) (t : Nat) :
    ExpiringK2Projection.observe (run (step hψ ring) C (es.take t)) =
      LabelFreeElimination.observe (run (AdjacentLeaderElimination.step hψ ring) D (es.take t)) :=
  same_word_adjacent hψ ring C D _ h0 (NoBirthAlong.take hψ ring C es hn t)

/-- Full carrier records at unscheduled sites are retained exactly. -/
theorem step_other (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) : step hψ ring C e i = C i := by
  simp only [step, PopulationProtocol.step, protocol, if_neg hi, if_neg hj]

/-- The physical update's alias convention is explicit: on a self-edge the
left pair output wins. It never inserts an independent responder copy. -/
theorem step_alias (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (ha : ring.rightNeighbor e = e) :
    step hψ ring C e e = (row hψ (C e) (C e)).1 := by
  simp only [step, PopulationProtocol.step, protocol, ha, if_true]

/-- In particular this literal collision convention deletes a singleton
leader. Safety statements for larger rings cannot be extended to n=1. -/
theorem singleton_leader_deleted (hψ : 0 < ψ)
    (ring : DirectedRing 1) (C : Fin 1 → ExpiringAgentState ψ κ τ)
    (hl : (C 0).core.core.leader = true) :
    (step hψ ring C 0 0).core.core.leader = false := by
  have ha : ring.rightNeighbor (0 : Fin 1) = 0 := Subsingleton.elim _ _
  rw [step_alias hψ ring C 0 ha]
  have hm := metadata_existing_leaders hψ (C 0) (C 0)
  unfold row finalPhysical
  exact (collisionRow_of_both hψ _ _
    ((initializeNewborn_leader _ _).trans (hm.1 hl))
    ((initializeNewborn_leader _ _).trans (hm.2 hl))).1

#print axioms observe_step_of_no_birth
#print axioms same_word_adjacent_all_prefixes
#print axioms singleton_leader_deleted

end K2BirthDispatcher
