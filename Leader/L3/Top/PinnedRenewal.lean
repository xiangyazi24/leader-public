import Leader.L3.Top.PinnedRenewalGeneric
import Leader.L3.Top.PinnedRenewalRace
import Leader.L3.Top.PinnedRaceUnfav

/-!
# Q7 (P.13-P.14): the renewal phase at the stop classes

`topStopRenewalPhase`: from every state of `topClockStopOr ... pendingOnly` the strict stop is
reached within mean `n * (2 * C)`, with `C = V + 1 + U + r`.

The trial is staged exactly as in the specification of P.13:

* preparation (`topStopPreparationPhase`): from a pending-only cut, the race cut or a strict stop
  within `n V`;
* race (`stop_race_structure`): at a race cut two distinct letters decide, the outgoing edge to a
  favourable cut, the incoming edge to an unfavourable cut, every other letter keeps the race;
* favourable (`topStopFavourablePhase`): the strict stop within `n (r + V)`;
* unfavourable: the pending-only cut or a strict stop within `n (U + r)`, the payload of the
  actual losing successor, started again.

The generic geometric renewal `renewal_generic` turns this staging into the bound
`2 (n V) + n + n (r + V) + n (U + r) ≤ n (2 C)`, which uses `V ≤ U + 1` (`topClockV_le`).
There is no probability hypothesis: the factor two is the superharmonic inequality of the race,
whose input is the pair of distinct letters of `stop_race_structure`.

Consumer: `TopClockPhaseBundle.renew` (TopClockAssembly).
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The trial budget**: `V ≤ U + 1` once the span is at least three, so that the staged cost
`2 V + 1 + (r + V) + (U + r)` of one trial is at most `2 C`.

Consumer: `topStopRenewalPhase`. -/
theorem topClockV_le {r : Nat} (hr : 3 ≤ r) : topClockV r ≤ topClockU r + 1 := by
  unfold topClockV topClockU
  have h2 : 9 ≤ r ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.mul_le_mul hr hr
  have h3 : r ^ 2 * 3 ≤ r ^ 2 * (2 * r ^ 2 + 8 * r + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- The staged cost of one trial is within `n (2 C)`.

Consumer: `topStopRenewalPhase`. -/
theorem trial_budget {n r : Nat} (hr : 3 ≤ r) :
    2 * (n * topClockV r) + n + n * (r + topClockV r) + n * (topClockU r + r) ≤
      n * (2 * topClockC r) := by
  have hV := topClockV_le hr
  have e : 2 * (n * topClockV r) + n + n * (r + topClockV r) + n * (topClockU r + r) =
      n * (2 * topClockV r + 1 + (r + topClockV r) + (topClockU r + r)) := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm n 2]
  rw [e]
  apply Nat.mul_le_mul_left
  unfold topClockC
  omega

/-- **The renewal phase at the stop classes.**

Consumer: `TopClockPhaseBundle.renew` (TopClockAssembly). -/
theorem topStopRenewalPhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockRenewalPhase ring C s (topClockStopClasses ring C s) := by
  classical
  obtain ⟨_, _, _, hprep, _, hfav, hunf⟩ := topStopPhases ring hn C s hl hbad
  have hn0 : 0 < n := by omega
  intro Z hZ
  by_cases hst : topFixedStrictStop ring C s Z
  · exact hit_now _ hn0 _ Z hst _
  · have hA : (topClockStopClasses ring C s).pendingOnly Z := by
      rcases hZ with h | h
      · exact absurd h hst
      · exact h
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (topFixedTraceNext ring C) (topFixedStrictStop ring C s) hn0 Z _).2
    exact renewal_generic (topFixedTraceNext ring C) (topFixedStrictStop ring C s)
      (topClockStopClasses ring C s).pendingOnly (topClockStopClasses ring C s).misplacedTail
      (topClockStopClasses ring C s).favourable (topClockStopClasses ring C s).unfavourable
      (n * topClockV (topClockSpan n))
      (n * (topClockSpan n + topClockV (topClockSpan n)))
      (n * (topClockU (topClockSpan n) + topClockSpan n))
      (by
        intro x hx T
        exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
          (topFixedTraceNext ring C) _ hn0 x _).1 (hprep x (Or.inr hx)) T)
      (by
        intro y hy _
        exact stop_race_structure ring hn C s hl hbad y hy)
      (by
        intro w hw T
        exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
          (topFixedTraceNext ring C) _ hn0 w _).1 (hfav w (Or.inr hw)) T)
      (by
        intro z hz T
        exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
          (topFixedTraceNext ring C) _ hn0 z _).1 (hunf z (Or.inr hz)) T)
      (n * (2 * topClockC (topClockSpan n)))
      (trial_budget (span_ge_three hn)) Z hA

end MarkedCells
end L3

#print axioms L3.MarkedCells.topClockV_le
#print axioms L3.MarkedCells.trial_budget
#print axioms L3.MarkedCells.topStopRenewalPhase
