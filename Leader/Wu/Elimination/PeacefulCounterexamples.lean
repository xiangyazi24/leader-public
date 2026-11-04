import Leader.Wu.Elimination.LeaderCountProgress

/-!
# Missing hypotheses in two proposed elimination safety interfaces

These executions use the actual label-free row on the existing finite cells.
They refute only the stated implications: the global signal class does not
make a one-leader endpoint safe, and literal peaceful witnesses may cross
an earlier unshielded leader and therefore need not be preserved.
-/

namespace K2PeacefulCounterexamples

open PPLL StateBoundUnifiedCell LDSinkBoundedKernel LabelFreeElimination
  K2FiniteProgress PPLLNoCheckBirthConditionTwoGeometry PPLLNoCheckBirthOutputLegitimacy

set_option autoImplicit false

theorem ring5 : DirectedRing 5 := ⟨by decide⟩

/-- Two unshielded leaders, each immediately before a live bullet. -/
def killer (i : Fin 5) : UCell 1 0 :=
  { legacy := { K2OutputSafety.boundedCanonical (by decide) 0 i with
      leader := decide (i = 0 ∨ i = 2)
      shield := false
      signal_B := 0
      bullet := if i = 1 ∨ i = 3 then 2 else 0 }
    control := (NondivisibleExample.seed7 0).control }

theorem killer_global : SignalGlobal ring5 killer := by
  apply signalGlobal_of_signals_zero
  · unfold K2GlobalGapClosure.Separated
    decide
  · intro i
    rfl

/-- The literal original word `[0,2]` removes both initial leaders. -/
theorem killer_counts :
    count killer = 2 ∧
    count (step (by decide) ring5 killer 0) = 1 ∧
    count (run (step (by decide) ring5) killer [0, 2]) = 0 := by decide

theorem killer_one_not_isSafe :
    ¬ PopulationProtocol.IsSafe (LabelFreeElimination.protocol (by decide) 0) ring5
      (step (by decide) ring5 killer 0) id := by
  intro hs
  let C := step (by decide) ring5 killer 0
  let D := step (by decide) ring5 C 2
  have hreach : PopulationProtocol.Reachable (LabelFreeElimination.protocol (by decide) 0) ring5 C D :=
    PopulationProtocol.OneStep.to_reachable ⟨2, rfl⟩
  have he := hs.2 D hreach 2
  change (D 2).legacy.leader = (C 2).legacy.leader at he
  have hd : (D 2).legacy.leader = false := by decide
  have hc : (C 2).legacy.leader = true := by decide
  rw [hd, hc] at he
  cases he

/-- Count one inside the actually closed global signal class is not yet
semantic output safety. No birth row or external dispatcher is involved. -/
theorem global_count_one_not_safe :
    ∃ C : Fin 5 → UCell 1 0,
      SignalGlobal ring5 C ∧ count C = 1 ∧
      ¬ PopulationProtocol.IsSafe (LabelFreeElimination.protocol (by decide) 0) ring5 C id :=
  ⟨step (by decide) ring5 killer 0,
    signalGlobal_step (by decide) ring5 killer killer_global 0,
    killer_counts.2.1, killer_one_not_isSafe⟩

/-- A literal peaceful witness from cell zero can pass the unshielded
leader at one and terminate at the shielded leader at three. -/
def crossing (i : Fin 5) : UCell 1 0 :=
  { legacy := { K2OutputSafety.boundedCanonical (by decide) 0 i with
      leader := decide (i = 1 ∨ i = 3)
      shield := decide (i = 3)
      signal_B := 0
      bullet := if i = 0 then 2 else 0 }
    control := (NondivisibleExample.seed7 0).control }

theorem crossing_global : SignalGlobal ring5 crossing := by
  apply signalGlobal_of_signals_zero
  · unfold K2GlobalGapClosure.Separated
    decide
  · intro i
    rfl

theorem crossing_hasLeader : hasLeader 5 (observe crossing) := ⟨1, by decide⟩

theorem crossing_literal_peaceful : noNonPeacefulBullet (by decide) ring5 (observe crossing) := by
  intro i hi
  have hloc : ∀ j : Fin 5, (observe crossing j).bullet = 2 → j = 0 := by decide
  have hi0 := hloc i hi
  subst i
  refine ⟨by decide, 3, by decide, by decide, by decide, ?_, ?_⟩
  · intro k _
    rfl
  · intro k _
    exact Subsingleton.elim _ _

/-- Edge `1→2` puts a signal on the old witness interval while both leaders
survive. The only shielded candidate target is no longer reachable through
zero signals; the nearer leader was never shielded. -/
theorem crossing_after_not_literal_peaceful :
    ¬ noNonPeacefulBullet (by decide) ring5
      (observe (step (by decide) ring5 crossing 1)) := by
  intro hs
  let D := observe (step (by decide) ring5 crossing 1)
  have hlive : (D 0).bullet = 2 := by decide
  obtain ⟨_, d, hd, ht, hsh, hz, _⟩ := hs 0 hlive
  have hblocked : ∀ d : Fin 5,
      (D (cwPos ring5 0 d.val)).isLeader →
      (D (cwPos ring5 0 d.val)).shield = true →
      ¬ (∀ k : Fin 5, k.val ≤ d.val → (D (cwPos ring5 0 k.val)).signal_B = 0) := by
    decide
  exact hblocked ⟨d, hd⟩ ht hsh (fun k hk => hz k.val hk)

/-- Even intersecting literal peacefulness with the old global signal
class does not repair its multileader closure defect. -/
theorem literal_peaceful_class_not_closed :
    ∃ C : Fin 5 → UCell 1 0,
      SignalGlobal ring5 C ∧ hasLeader 5 (observe C) ∧
      noNonPeacefulBullet (by decide) ring5 (observe C) ∧
      ¬ noNonPeacefulBullet (by decide) ring5
        (observe (step (by decide) ring5 C 1)) :=
  ⟨crossing, crossing_global, crossing_hasLeader, crossing_literal_peaceful,
    crossing_after_not_literal_peaceful⟩

end K2PeacefulCounterexamples

#print axioms K2PeacefulCounterexamples.killer_global
#print axioms K2PeacefulCounterexamples.killer_counts
#print axioms K2PeacefulCounterexamples.global_count_one_not_safe
#print axioms K2PeacefulCounterexamples.crossing_literal_peaceful
#print axioms K2PeacefulCounterexamples.crossing_after_not_literal_peaceful
#print axioms K2PeacefulCounterexamples.literal_peaceful_class_not_closed
