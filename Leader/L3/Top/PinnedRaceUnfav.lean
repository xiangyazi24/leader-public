import Leader.L3.Top.PinnedRacePhase
import Leader.L3.Top.SettledPotentialPhase
import Leader.L3.Top.SettledPotentialCost
import Leader.L3.ProbStages

/-!
# Q7 (P.13): the unfavourable branch for the pinned classes

An unfavourable cut is a pinned coloured cut (the actual losing successor, not a reset state).
From it the settled-work phase (P.6--P.10) reaches the pinned settled-empty class within
`n * topClockU r`, and the final mobile phase (P.11) reaches the pending-only class within
`n * r`; the stages compose by `expectedHittingTimeAtMost_stage_le`.

Consumer: `TopClockPhaseBundle.unfavourable` (TopClockAssembly).
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- A larger target has the smaller expected hitting bound.

Consumer: `topPinnedUnfavourablePhase`. -/
theorem hit_mono_target {S : Type} {n : Nat} (next : S → Fin n → S) (hn : 0 < n)
    (P Q : S → Prop) (hPQ : ∀ y, P y → Q y) (x : S) (B : Nat)
    (h : UniformFirstHit.ExpectedHittingTimeAtMost next P x (B : Rat)) :
    UniformFirstHit.ExpectedHittingTimeAtMost next Q x (B : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost next Q hn x B).2
  intro T
  have h1 := (UniformFirstHit.expectedHittingTimeAtMost_iff_cost next P hn x B).1 h T
  exact Nat.le_trans (costNumerator_mono_target next P Q (fun _ => True) (fun _ _ _ => trivial)
    (fun y _ hy => hPQ y hy) x trivial T) h1

/-- A target that holds at the start is hit at once.

Consumer: `topPinnedUnfavourablePhase`. -/
theorem hit_now {S : Type} {n : Nat} (next : S → Fin n → S) (hn : 0 < n)
    (P : S → Prop) (x : S) (hx : P x) (B : Nat) :
    UniformFirstHit.ExpectedHittingTimeAtMost next P x (B : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost next P hn x B).2
  intro T
  rw [costNumerator_terminal _ _ x hx T]
  exact Nat.zero_le _

/-- **P.13 unfavourable branch for the pinned classes.**  From the actual losing successor, a
strict stop or a pending-only cut is reached within `n * (topClockU r + r)`.

Consumer: `TopClockPhaseBundle.unfavourable` (TopClockAssembly). -/
theorem topPinnedUnfavourablePhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockUnfavourablePhase ring C s (topClockPinnedClasses ring C s) := by
  classical
  have hn0 : 0 < n := by omega
  intro Z hZ
  by_cases hstop : topFixedStrictStop ring C s Z
  · exact hit_now _ hn0 _ Z (Or.inl hstop) _
  · have hunf : (topClockPinnedClasses ring C s).unfavourable Z := by
      rcases hZ with h | h
      · exact absurd h hstop
      · exact h
    have hcol : (topClockPinnedClasses ring C s).coloured Z :=
      (topClockPinnedClasses ring C s).unfavourableSpec Z hunf
    have h1 := topClockPinnedSettledWorkPhase ring hn C s hl hbad Z (Or.inr hcol)
    have h1' := hit_mono_target (topFixedTraceNext ring C) hn0
      (topClockStopOr ring C s (topClockPinnedClasses ring C s).settledEmpty)
      (fun z => topClockStopOr ring C s (topClockPinnedClasses ring C s).settledEmpty z ∨
        topClockStopOr ring C s (topClockPinnedClasses ring C s).pendingOnly z)
      (fun y hy => Or.inl hy) Z _ h1
    have h2 : ∀ y, topClockStopOr ring C s (topClockPinnedClasses ring C s).settledEmpty y →
        UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
          (topClockStopOr ring C s (topClockPinnedClasses ring C s).pendingOnly) y
          ((n * topClockSpan n : Nat) : Rat) :=
      fun y hy => topClockPinnedMobilePhase ring hn C s hl hbad y hy
    have h3 := Prob.expectedHittingTimeAtMost_stage_le (topFixedTraceNext ring C) hn0 Z
      (topClockStopOr ring C s (topClockPinnedClasses ring C s).settledEmpty)
      (topClockStopOr ring C s (topClockPinnedClasses ring C s).pendingOnly)
      (n * topClockU (topClockSpan n)) (n * topClockSpan n) h1' h2
    have e : n * topClockU (topClockSpan n) + n * topClockSpan n =
        n * (topClockU (topClockSpan n) + topClockSpan n) := by rw [Nat.mul_add]
    rw [e] at h3
    exact h3

end MarkedCells
end L3

#print axioms L3.MarkedCells.hit_mono_target
#print axioms L3.MarkedCells.hit_now
#print axioms L3.MarkedCells.topPinnedUnfavourablePhase
