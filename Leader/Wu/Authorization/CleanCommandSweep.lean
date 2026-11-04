import Leader.Wu.Authorization.CleanCommandTransport

/-!
# All-ring removal of commands from retained paths

This module uses the complete original AuthF row theorem. For arbitrary raw
configurations and every AuthF configuration, one physical step preserves the
global path-or-no-command predicate. Serving the explicit word `List.finRange n`
then establishes it at every cell in exactly n complete interactions.

No standard-label, token, leader, reset, or provenance premise is imposed.
The directed-ring interface supplies n > 0; the proof includes n = 1 via the
original step's initiator-output priority. This is a global CLEAN-slot property,
not a serial-frontier, termination, or leader-election theorem.

Source-level nonvacuity: n = 1 and psi = 2 permit any raw cell state; the one
interaction stores the left output of the original pipeline on the self-edge.
-/

set_option autoImplicit false

namespace PPLLAuthCheckNoCmdSweep

open PPLL PPLLAuthF
open PPLLAuthCheckCleanNoCmd PPLLAuthCheckNoCmdFrame
open PPLLAuthResetDrain (authProtocol authRun)

section Sweep

variable {n ψ : Nat}

/-- A cell that is already `PathNoCmd` stays so through one complete
AuthF interaction, whether it is initiator, responder, or off the edge. -/
private theorem step_cell_pathNoCmd
    (hp : ψ > 0) (κ : Nat) (cfg : PPLLAuthF.Cfg)
    (ring : DirectedRing n) (C : Fin n → AuthState ψ)
    (e i : Fin n) (hi : PathNoCmd (C i)) :
    PathNoCmd ((authProtocol hp κ cfg).step ring C e i) := by
  -- For n = 1, rightNeighbor e = e.  The first branch is therefore selected;
  -- PopulationProtocol.step has left-output priority, so no n > 1 premise is needed.
  by_cases hie : i = e
  · subst i
    simpa [PopulationProtocol.step, authProtocol] using
      (pipeline_pathNoCmd hp κ cfg (C e) (C (ring.rightNeighbor e))).1
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      simpa [PopulationProtocol.step, authProtocol, hie] using
        (pipeline_pathNoCmd hp κ cfg (C e) (C (ring.rightNeighbor e))).2
    · simpa [PopulationProtocol.step, authProtocol, hie, hir] using hi

/-- The served initiator is `PathNoCmd` after one complete interaction,
with no hypothesis on its incoming state. -/
private theorem step_initiator_pathNoCmd
    (hp : ψ > 0) (κ : Nat) (cfg : PPLLAuthF.Cfg)
    (ring : DirectedRing n) (C : Fin n → AuthState ψ) (e : Fin n) :
    PathNoCmd ((authProtocol hp κ cfg).step ring C e e) := by
  simpa [PopulationProtocol.step, authProtocol] using
    (pipeline_pathNoCmd hp κ cfg (C e) (C (ring.rightNeighbor e))).1

/-- One original `authProtocol` / `PopulationProtocol.step` preserves the
global pointwise `PathNoCmd` predicate. -/
theorem step_global_pathNoCmd
    (hp : ψ > 0) (κ : Nat) (cfg : PPLLAuthF.Cfg)
    (ring : DirectedRing n) (C : Fin n → AuthState ψ) (e : Fin n)
    (hC : ∀ i, PathNoCmd (C i)) :
    ∀ i, PathNoCmd ((authProtocol hp κ cfg).step ring C e i) := by
  intro i
  exact step_cell_pathNoCmd hp κ cfg ring C e i (hC i)

/-- Along an arbitrary physical word, cell `i` is good at the end if it was
good initially or if it was served as an initiator somewhere in the word. -/
theorem authRun_pathNoCmd_or_mem
    (hp : ψ > 0) (κ : Nat) (cfg : PPLLAuthF.Cfg)
    (ring : DirectedRing n) (C : Fin n → AuthState ψ)
    (w : List (Fin n)) (i : Fin n)
    (h : PathNoCmd (C i) ∨ i ∈ w) :
    PathNoCmd (authRun hp κ cfg ring C w i) := by
  induction w generalizing C with
  | nil =>
      simpa [authRun] using h
  | cons e es ih =>
      have h' : PathNoCmd (C i) ∨ i = e ∨ i ∈ es := by
        simpa only [List.mem_cons] using h
      have hs :
          PathNoCmd (((authProtocol hp κ cfg).step ring C e) i) ∨ i ∈ es := by
        rcases h' with hgood | hmem
        · exact Or.inl (step_cell_pathNoCmd hp κ cfg ring C e i hgood)
        · rcases hmem with he | htail
          · subst i
            exact Or.inl (step_initiator_pathNoCmd hp κ cfg ring C e)
          · exact Or.inr htail
      change PathNoCmd
        (authRun hp κ cfg ring ((authProtocol hp κ cfg).step ring C e) es i)
      exact ih _ hs

/-- The concrete all-ring sweep: each physical cell is initiator exactly once. -/
def sweepWord (n : Nat) : List (Fin n) := List.finRange n

@[simp] theorem sweepWord_length (n : Nat) :
    (sweepWord n).length = n := by
  simp [sweepWord]

/-- After exactly `n` complete AuthF interactions along `List.finRange n`,
every cell is `PathNoCmd`, from an arbitrary initial configuration. -/
theorem finRange_sweep_pathNoCmd
    (hp : ψ > 0) (κ : Nat) (cfg : PPLLAuthF.Cfg)
    (ring : DirectedRing n) (C : Fin n → AuthState ψ) :
    ∀ i, PathNoCmd (authRun hp κ cfg ring C (sweepWord n) i) := by
  intro i
  exact authRun_pathNoCmd_or_mem hp κ cfg ring C (sweepWord n) i
    (Or.inr (by
      simpa [sweepWord] using List.mem_finRange i))

/-- Existential packaging with the exact interaction count. -/
theorem exists_finRange_sweep_pathNoCmd
    (hp : ψ > 0) (κ : Nat) (cfg : PPLLAuthF.Cfg)
    (ring : DirectedRing n) (C : Fin n → AuthState ψ) :
    ∃ w : List (Fin n), w.length = n ∧
      ∀ i, PathNoCmd (authRun hp κ cfg ring C w i) := by
  refine ⟨sweepWord n, sweepWord_length n, ?_⟩
  exact finRange_sweep_pathNoCmd hp κ cfg ring C

#print axioms step_global_pathNoCmd
#print axioms authRun_pathNoCmd_or_mem
#print axioms finRange_sweep_pathNoCmd
#print axioms exists_finRange_sweep_pathNoCmd

end Sweep

end PPLLAuthCheckNoCmdSweep
