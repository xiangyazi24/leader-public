import Leader.L3.Top.PinnedPhaseSweepCost
import Leader.L3.Top.PinnedPhaseFillExit
import Leader.L3.Top.PinnedPhaseClasses
import Leader.L3.Top.PinnedRaceUnfav

/-!
# Q7 (P.12): the preparation phase on the classes without an earlier strict stop

From a pending-only cut (or a strict stop) of `topClockStopClasses`, the expected time to a strict
stop or a misplaced-tail cut is at most `n * topClockV r`, `V = 2 r^2 + 5 r + 3`:

* the fill stage (`topFillStage`, `n * (2 r^2 + 4 r + 2)`) forms a settled tail, a misplaced cut
  away from the border (`exit_misplaced`) or an aligned window at the border;
* the aligned window launches the carry sweep that records a strict cyclic comparison terminal
  (`aligned_strict_cost`, `n * (r + 1)`).

Consumer: `TopClockPhaseBundle.prepare` (TopClockAssembly).
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- A settled tail at the border with a settled block behind it is an aligned window.

Consumer: `topStopPreparationPhase`. -/
theorem exit_align {r : Nat} {c : Nat → Cell} (hr : 2 ≤ r) (h : ExitShape r c 0) :
    AlignShape r c := by
  obtain ⟨_, _, hm, hr'⟩ := h
  exact ⟨hr, hm, fun j hj hj0 => hr' j hj0 hj⟩

/-- **P.12 preparation for the classes without an earlier strict stop.**

Consumer: `TopClockPhaseBundle.prepare` (TopClockAssembly). -/
theorem topStopPreparationPhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockPreparationPhase ring C s (topClockStopClasses ring C s) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  have hn0 : 0 < n := by omega
  have hr3 := span_ge_three hn
  intro Z hZ
  by_cases hstop : topFixedStrictStop ring C s Z
  · exact hit_now _ hn0 _ Z (Or.inl hstop) _
  · have hpend : (topClockStopClasses ring C s).pendingOnly Z := by
      rcases hZ with h | h
      · exact absurd h hstop
      · exact h
    obtain ⟨hpo, hNZ⟩ := hpend
    obtain ⟨Y0, hP, hs⟩ := pendingOnly_start ring C s hg Z hpo
    -- the fill stage, strengthened by `NoPrefixStop`
    let T0 : TopFixedTraceState n → Prop :=
      topClockStopOr ring C s (topClockStopClasses ring C s).misplacedTail
    let A : TopFixedTraceState n → Prop := fun Y =>
      AlignReg ring C s Y0 Y ∧ NoPrefixStop ring C s Y
    have h1 := topFillStage ring hn C s hl hbad Y0 Z hP hs
    have h1' := phase_nps_hit ring C s hn0
      (fun Y => PuPinAt ring C s Y0 Y ∧ ∃ h, ExitShape (topClockSpan n) (cellOf s Y) h)
      (fun Y => A Y ∨ T0 Y)
      (fun Y hY => Or.inr (Or.inl hY))
      (by
        intro Y hNY hY
        obtain ⟨hPY, h0, hex⟩ := hY
        by_cases h0z : h0 = 0
        · subst h0z
          exact Or.inl ⟨⟨hPY, exit_align (by omega) hex⟩, hNY⟩
        · exact Or.inr (Or.inr ⟨exit_misplaced ring C s hg Y0 Y hPY h0 hex (by omega), hNY⟩))
      Z (Or.inl hNZ) _ h1
    have h2 : ∀ y, A y → UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C) T0 y
        ((n * (topClockSpan n + 1) : Nat) : Rat) := by
      intro y hy
      have hcost := aligned_strict_cost ring C s hg Y0 y hy.1 (Or.inl hy.2)
      have hstopE : UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
          (topFixedStrictStop ring C s) y ((n * (topClockSpan n + 1) : Nat) : Rat) :=
        (UniformFirstHit.expectedHittingTimeAtMost_iff_cost (topFixedTraceNext ring C) _ hn0 y
          (n * (topClockSpan n + 1))).2 hcost
      exact hit_mono_target (topFixedTraceNext ring C) hn0 _ T0 (fun z hz => Or.inl hz) y _ hstopE
    have h3 := Prob.expectedHittingTimeAtMost_stage_le (topFixedTraceNext ring C) hn0 Z A T0
      (n * (2 * topClockSpan n * topClockSpan n + 4 * topClockSpan n + 2))
      (n * (topClockSpan n + 1)) h1' h2
    have e : n * (2 * topClockSpan n * topClockSpan n + 4 * topClockSpan n + 2) +
        n * (topClockSpan n + 1) = n * topClockV (topClockSpan n) := by
      rw [← Nat.mul_add]
      unfold topClockV
      congr 1
      rw [Nat.pow_two, Nat.mul_assoc]
      omega
    rw [e] at h3
    exact h3

end MarkedCells
end L3

#print axioms L3.MarkedCells.topStopPreparationPhase
