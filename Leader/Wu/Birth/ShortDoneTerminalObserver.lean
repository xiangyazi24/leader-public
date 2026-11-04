import Leader.Wu.Birth.ShortDoneTerminalConsumer

/-!
# Conditional observer for the terminal-entry repaired DONE consumer

`NoBirthAlong` is a consumer premise only.  This module does not produce it.
The physical transition is exactly `BirthShortDoneTerminalConsumer.step`, hence
exactly `BirthShortDoneTerminalHost.row` at every scheduled edge.
-/

namespace BirthShortDoneTerminalObserver

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
  K2OutputSafety
open K2BirthDispatcher ExpiringK2Projection LDSinkBoundedKernel

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ width κ τ n : Nat}

/-- The actual local birth bit: compare each original endpoint with the
normalized metadata endpoint that is really fed to `finalPhysical`. -/
def birthEvent (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ) : Bool :=
  let q := BirthShortDoneTerminalHost.metadata hψ hwidth hle l r
  K2BirthDispatcher.newborn l q.1 || K2BirthDispatcher.newborn r q.2

/-- Under the actual no-birth test, the terminal-host metadata has exactly the
same four K2 fields as the two original endpoints.  The leader equalities use
old-leader preservation plus the negative newborn test; the other three fields
are the concrete consumer's physical bullet frame. -/
theorem metadata_signal_of_no_birth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (hn : birthEvent hψ hwidth hle l r = false) :
    (observeCell (BirthShortDoneTerminalHost.metadata hψ hwidth hle l r).1,
      observeCell (BirthShortDoneTerminalHost.metadata hψ hwidth hle l r).2) =
      (observeCell l, observeCell r) := by
  have hp := BirthShortDoneTerminalConsumer.metadata_existing_leaders
    hψ hwidth hle l r
  have hb := BirthShortDoneTerminalConsumer.metadata_bullets
    hψ hwidth hle l r
  have hnb :
      K2BirthDispatcher.newborn l
          (BirthShortDoneTerminalHost.metadata hψ hwidth hle l r).1 = false ∧
      K2BirthDispatcher.newborn r
          (BirthShortDoneTerminalHost.metadata hψ hwidth hle l r).2 = false := by
    simpa only [birthEvent, Bool.or_eq_false_iff] using hn
  generalize BirthShortDoneTerminalHost.metadata hψ hwidth hle l r = q at hp hb hnb ⊢
  have hleadL : q.1.core.core.leader = l.core.core.leader := by
    cases hl : l.core.core.leader with
    | false => simpa [K2BirthDispatcher.newborn, hl] using hnb.1
    | true => simpa [hl] using (hp.1 hl)
  have hleadR : q.2.core.core.leader = r.core.core.leader := by
    cases hr : r.core.core.leader with
    | false => simpa [K2BirthDispatcher.newborn, hr] using hnb.2
    | true => simpa [hr] using (hp.2 hr)
  have hLs := congrArg
    (fun z : (Bool × Fin 3 × Fin 2) × (Bool × Fin 3 × Fin 2) => z.1.1) hb
  have hLb := congrArg
    (fun z : (Bool × Fin 3 × Fin 2) × (Bool × Fin 3 × Fin 2) => z.1.2.1) hb
  have hLz := congrArg
    (fun z : (Bool × Fin 3 × Fin 2) × (Bool × Fin 3 × Fin 2) => z.1.2.2) hb
  have hRs := congrArg
    (fun z : (Bool × Fin 3 × Fin 2) × (Bool × Fin 3 × Fin 2) => z.2.1) hb
  have hRb := congrArg
    (fun z : (Bool × Fin 3 × Fin 2) × (Bool × Fin 3 × Fin 2) => z.2.2.1) hb
  have hRz := congrArg
    (fun z : (Bool × Fin 3 × Fin 2) × (Bool × Fin 3 × Fin 2) => z.2.2.2) hb
  change q.1.core.core.shield = l.core.core.shield at hLs
  change q.1.core.core.bullet = l.core.core.bullet at hLb
  change q.1.core.core.signal_B = l.core.core.signal_B at hLz
  change q.2.core.core.shield = r.core.core.shield at hRs
  change q.2.core.core.bullet = r.core.core.bullet at hRb
  change q.2.core.core.signal_B = r.core.core.signal_B at hRz
  apply Prod.ext
  · unfold ExpiringK2Projection.observeCell K2OutputSafety.signalView
    apply congrArg PPLLNoCheckBirthConditionTwoProtocol.PeaceView.toState
    apply PPLLNoCheckBirthConditionTwoPhysical.PeaceView.ext
    · exact hleadL
    · rfl
    · exact hLs
    · exact hLb
    · exact hLz
  · unfold ExpiringK2Projection.observeCell K2OutputSafety.signalView
    apply congrArg PPLLNoCheckBirthConditionTwoProtocol.PeaceView.toState
    apply PPLLNoCheckBirthConditionTwoPhysical.PeaceView.ext
    · exact hleadR
    · rfl
    · exact hRs
    · exact hRb
    · exact hRz

/-- Exactly one no-birth elimination of newborn initialization, followed by the
single existing collision/K2 observer. -/
theorem observe_row_of_no_birth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (hn : birthEvent hψ hwidth hle l r = false) :
    (observeCell (BirthShortDoneTerminalHost.row hψ hwidth hle l r).1,
      observeCell (BirthShortDoneTerminalHost.row hψ hwidth hle l r).2) =
      K2BirthDispatcher.shadowRow (observeCell l) (observeCell r) := by
  have hnb :
      K2BirthDispatcher.newborn l
          (BirthShortDoneTerminalHost.metadata hψ hwidth hle l r).1 = false ∧
      K2BirthDispatcher.newborn r
          (BirthShortDoneTerminalHost.metadata hψ hwidth hle l r).2 = false := by
    simpa only [birthEvent, Bool.or_eq_false_iff] using hn
  unfold BirthShortDoneTerminalHost.row
  dsimp only
  rw [K2BirthDispatcher.finalPhysical_of_no_birth hψ l r _ _ hnb.1 hnb.2]
  exact (K2BirthDispatcher.observe_collisionRow hψ _ _).trans
    (congrArg (fun q : AgentState 1 × AgentState 1 =>
      K2BirthDispatcher.shadowRow q.1 q.2)
      (metadata_signal_of_no_birth hψ hwidth hle l r hn))

/-- Lift the local observer through the concrete consumer's actual
`PopulationProtocol.step`.  The nested split is the real endpoint priority;
when the two endpoints alias, the first/left output wins on both sides. -/
theorem observe_step_of_no_birth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (hn : birthEvent hψ hwidth hle (C e) (C (ring.rightNeighbor e)) = false) :
    ExpiringK2Projection.observe
        (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e) =
      K2BirthDispatcher.shadowStep ring (ExpiringK2Projection.observe C) e := by
  have hq := observe_row_of_no_birth hψ hwidth hle
    (C e) (C (ring.rightNeighbor e)) hn
  funext i
  simp only [ExpiringK2Projection.observe,
    BirthShortDoneTerminalConsumer.step, PopulationProtocol.step,
    BirthShortDoneTerminalConsumer.protocol,
    K2BirthDispatcher.shadowStep, updatePair]
  split
  · exact congrArg Prod.fst hq
  · split
    · exact congrArg Prod.snd hq
    · rfl

/-- Explicit self-edge observation: the concrete population protocol keeps the
left row output and performs no responder overwrite or second host-row call. -/
theorem observe_step_alias_of_no_birth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (ha : ring.rightNeighbor e = e)
    (hn : birthEvent hψ hwidth hle (C e) (C e) = false) :
    observeCell
        (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e e) =
      (K2BirthDispatcher.shadowRow (observeCell (C e)) (observeCell (C e))).1 := by
  have hs := BirthShortDoneTerminalConsumer.step_alias
    hψ hwidth hle ring C e ha
  have hq := observe_row_of_no_birth hψ hwidth hle (C e) (C e) hn
  exact (congrArg
      (fun u : ExpiringAgentState ψ κ τ => ExpiringK2Projection.observeCell u) hs).trans
    (congrArg Prod.fst hq)

/-- The sole scheduler-word premise.  Crucially, the recursive premise is
checked on the actual newly computed successor configuration.  This module
contains no theorem producing `NoBirthAlong`. -/
def NoBirthAlong (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) : List (Fin n) → Prop
  | [] => True
  | e :: es =>
      birthEvent hψ hwidth hle (C e) (C (ring.rightNeighbor e)) = false ∧
      NoBirthAlong hψ hwidth hle ring
        (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e) es

theorem NoBirthAlong.take (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hn : NoBirthAlong hψ hwidth hle ring C es) (t : Nat) :
    NoBirthAlong hψ hwidth hle ring C (es.take t) := by
  induction t generalizing C es with
  | zero => trivial
  | succ t ih =>
    cases es with
    | nil => trivial
    | cons e es => exact ⟨hn.1, ih _ _ hn.2⟩

/-- The concrete terminal-entry consumer and the frozen shadow system execute
exactly the same original scheduler word. -/
theorem observe_run_of_no_birth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hn : NoBirthAlong hψ hwidth hle ring C es) :
    ExpiringK2Projection.observe
        (run (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring) C es) =
      run (K2BirthDispatcher.shadowStep ring)
        (ExpiringK2Projection.observe C) es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
    simpa only [run,
      observe_step_of_no_birth hψ hwidth hle ring C e hn.1] using
      ih (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring C e) hn.2

/-- Every prefix of that same scheduler word has the exact four-field shadow
observation. -/
theorem observe_all_prefixes_of_no_birth (hψ : 0 < ψ)
    (hwidth : 0 < width) (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hn : NoBirthAlong hψ hwidth hle ring C es) (t : Nat) :
    ExpiringK2Projection.observe
        (run (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring)
          C (es.take t)) =
      run (K2BirthDispatcher.shadowStep ring)
        (ExpiringK2Projection.observe C) (es.take t) :=
  observe_run_of_no_birth hψ hwidth hle ring C _
    (NoBirthAlong.take hψ hwidth hle ring C es hn t)

/-- Same-word, same-prefix comparison with the frozen actual
`AdjacentLeaderElimination` observer; there is no independently chosen
scheduler word. -/
theorem same_word_adjacent_all_prefixes (hψ : 0 < ψ)
    (hwidth : 0 < width) (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (D : Fin n → StateBoundUnifiedCell.UCell ψ κ) (es : List (Fin n))
    (h0 : ExpiringK2Projection.observe C = LabelFreeElimination.observe D)
    (hn : NoBirthAlong hψ hwidth hle ring C es) (t : Nat) :
    ExpiringK2Projection.observe
        (run (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring)
          C (es.take t)) =
      LabelFreeElimination.observe
        (run (AdjacentLeaderElimination.step hψ ring) D (es.take t)) := by
  rw [observe_all_prefixes_of_no_birth hψ hwidth hle ring C es hn t,
    K2BirthDispatcher.adjacent_observe_run hψ ring D (es.take t), h0]

end BirthShortDoneTerminalObserver

#print axioms BirthShortDoneTerminalObserver.metadata_signal_of_no_birth
#print axioms BirthShortDoneTerminalObserver.observe_row_of_no_birth
#print axioms BirthShortDoneTerminalObserver.observe_step_of_no_birth
#print axioms BirthShortDoneTerminalObserver.observe_step_alias_of_no_birth
#print axioms BirthShortDoneTerminalObserver.NoBirthAlong.take
#print axioms BirthShortDoneTerminalObserver.observe_run_of_no_birth
#print axioms BirthShortDoneTerminalObserver.observe_all_prefixes_of_no_birth
#print axioms BirthShortDoneTerminalObserver.same_word_adjacent_all_prefixes
