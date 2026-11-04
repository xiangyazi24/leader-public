import Leader.Wu.Elimination.ArbitraryInputGoal
import Leader.Wu.Elimination.PeacefulSignalEntry

/-!
# Frozen peaceful-signal entry on the same collision-protocol words

The PS leaf is consumed at its physical separated/nearest-peaceful input.
Its success payload is inspected at the full word endpoint; terminal padding
is never removed. Zero-leader inputs retain the explicit terminal alternative.
-/

namespace K2ArbitraryElimination

open StateBoundUnifiedCell LDSinkBoundedKernel LabelFreeElimination
  K2PeacefulGlobal K2FiniteProgress K2FiniteSafeEliminationCore
  FiniteUniformStoppingTree LeaderCountDyadicTail FiniteAccounting K2PeacefulSignalEntry

set_option autoImplicit false
set_option Elab.async false

variable {n ψ κ : Nat}

/-- Three logarithmic PS blocks give the exact n⁻³ residual target. -/
def signalTime (n : Nat) : Nat := 2 * (n * n) * (3 * (Nat.log2 n + 1))

private theorem stopped_word_sum {S : Type} (next : S → Fin n → StopNode S)
    (w : StopNode S → Nat) (x : StopNode S) (T : Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun es => w (ControlledSchedulerMass.runWord next x es)) =
      treeWeight next w x T := by
  induction T generalizing x with
  | zero => simp [FixedSpanRenewalPayload.wordSum, allSchedules, ControlledSchedulerMass.runWord, treeWeight]
  | succ T ih =>
    rw [FixedSpanRenewalPayload.wordSum_succ]
    exact ofFn_sum_eq _ _ (fun e => ih (stepNode next x e))

/-- Every successful PS word reaches actual collision safety or the actual
safe-elimination domain, at its full physical endpoint. Failed stop nodes are
ruled out by the produced PS tracking theorem. -/
theorem signal_ready_word (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hs : AdjacentSeparationEntry.Separated ring C)
    (hp : PeacefulGlobal ring C) (es : List (Fin n)) :
    miss (Ready hψ ring) (run (AdjacentLeaderElimination.step hψ ring) C es) ≤
      activeWeight (ControlledSchedulerMass.runWord (psPhysicalStep hψ ring) (psInitialNode ring C) es) := by
  classical
  have ht := psTracksWord hψ hn ring C hp (psInitialNode ring C) (psTracksInitial ring C) es
  cases hx : ControlledSchedulerMass.runWord (psPhysicalStep hψ ring) (psInitialNode ring C) es with
  | active D => exact miss_le_one _ _
  | failure =>
    rw [hx] at ht
    exact False.elim ht
  | success =>
    have hpost := AdjacentLeaderPeaceful.peacefulGlobal_run hψ hn ring C hp es
    have hdone := psCollisionSuccessfulWord hψ hn ring C hs hp es hx
    have hready : Ready hψ ring (run (AdjacentLeaderElimination.step hψ ring) C es) := by
      rcases hdone with hsig | ⟨_, hsafe⟩
      · exact Or.inr ⟨hsig, hpost⟩
      · exact Or.inl (Or.inl hsafe)
    simp only [miss, if_pos hready, activeWeight]
    exact Nat.le_refl _

/-- Exact word enumeration converts the physical per-word handoff into
an original-scheduler numerator bound. There is no distribution transfer. -/
theorem signal_ready_mass (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hs : AdjacentSeparationEntry.Separated ring C)
    (hp : PeacefulGlobal ring C) (T : Nat) :
    wordSum (AdjacentLeaderElimination.step hψ ring) (miss (Ready hψ ring)) C T ≤
      activeCount (psPhysicalStep hψ ring) (psInitialNode ring C) T := by
  rw [← K2FiniteSafeEliminationExpected.wordSum_run]
  change _ ≤ treeWeight (psPhysicalStep hψ ring) activeWeight (psInitialNode ring C) T
  rw [← stopped_word_sum]
  rw [← FixedSpanRenewalPayload.rawWord_sum, ← FixedSpanRenewalPayload.rawWord_sum]
  exact ofFn_sum_le _ _ (fun i => signal_ready_word hψ hn ring C hs hp
    (FixedSpanRenewalPayload.rawWord n T i))

/-- The PS consumer accepts every actually prepared physical state,
including zero leaders, and produces the exact final-domain/Goal handoff. -/
theorem prepared_ready_tail (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Prepared ring C) :
    n ^ 3 * wordSum (AdjacentLeaderElimination.step hψ ring) (miss (Ready hψ ring)) C
      (signalTime n) ≤ n ^ signalTime n := by
  rcases hC with hz | ⟨hs, hp⟩
  · rw [miss_zero _ (Ready hψ ring) (ready_step hψ hn ring) C (Or.inl (Or.inr hz))]
    exact Nat.zero_le _
  · exact Nat.le_trans (Nat.mul_le_mul_left _ (signal_ready_mass hψ hn ring C hs hp _))
      (psLogTail hψ hn ring C hs hp 3)

end K2ArbitraryElimination

#print axioms K2ArbitraryElimination.signal_ready_word
#print axioms K2ArbitraryElimination.signal_ready_mass
#print axioms K2ArbitraryElimination.prepared_ready_tail
