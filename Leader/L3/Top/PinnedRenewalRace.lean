import Leader.L3.Top.PinnedPhaseFavourableAssemble

/-!
# Q7 (P.13-P.14): the race cut of the stop classes has two distinct deciding letters

For a misplaced-tail cut without an earlier strict stop, with tail position `h` (nonborder):

* the outgoing edge `winSite s h` leads to a strict stop or a favourable cut;
* the incoming edge `winSite s (h - 1)` leads to a strict stop or an unfavourable cut;
* the two edges are distinct (`topPreparationRaceEdgesDistinct`);
* every other edge leads to a strict stop or again to a misplaced-tail cut.

This is the structural content of the race probability one half: the first of two distinct
letters decides, so one scheduler step decides favourably with mass at least `1/n` and
unfavourably with mass at most `1/n`.  The quantitative consequence is drawn in
`renewal_generic`.

Consumer: `Leader/L3/Top/PinnedRenewal.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The two deciding letters of a race cut of the stop classes.**

Consumer: `topStopRenewalPhase`. -/
theorem stop_race_structure {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) (y : TopFixedTraceState n)
    (hy : (topClockStopClasses ring C s).misplacedTail y) :
    ∃ e1 e2 : Fin n, e1 ≠ e2 ∧
      (topFixedStrictStop ring C s (topFixedTraceNext ring C y e1) ∨
        (topClockStopClasses ring C s).favourable (topFixedTraceNext ring C y e1)) ∧
      (topFixedStrictStop ring C s (topFixedTraceNext ring C y e2) ∨
        (topClockStopClasses ring C s).unfavourable (topFixedTraceNext ring C y e2)) ∧
      ∀ e, e ≠ e1 → e ≠ e2 →
        topFixedStrictStop ring C s (topFixedTraceNext ring C y e) ∨
          (topClockStopClasses ring C s).misplacedTail (topFixedTraceNext ring C y e) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  obtain ⟨⟨hpu, hdown, hreach, hpure, hsuf, h, hh⟩, hnps⟩ := hy
  have hpin := pupin_pinned ring C s y hpu
  have hreachY : topClockReached ring C y := hreach
  refine ⟨winSite s h.val, winSite s (h.val - 1),
    topPreparationRaceEdgesDistinct hn s h hh.1, ?_, ?_, ?_⟩
  · by_cases hst : topFixedStrictStop ring C s (topFixedTraceNext ring C y (winSite s h.val))
    · exact Or.inl hst
    · have hfv := race_favourable ring C s hg y h hpin hh
      refine Or.inr ⟨?_, noPrefixStop_next ring C s y _ hnps hst⟩
      refine ⟨topPreparationPinnedNext ring C s hg y _ hpin, hfv.1, ⟨hfv.2.1, hfv.2.2⟩, y.2,
        winSite s h.val, rfl, ?_⟩
      rw [← hreachY]
      exact hpu
  · by_cases hst : topFixedStrictStop ring C s
        (topFixedTraceNext ring C y (winSite s (h.val - 1)))
    · exact Or.inl hst
    · exact Or.inr ⟨race_unfavourable ring C s hg y h hpin hh,
        noPrefixStop_next ring C s y _ hnps hst⟩
  · intro e he1 he2
    by_cases hst : topFixedStrictStop ring C s (topFixedTraceNext ring C y e)
    · exact Or.inl hst
    · have hmo := misAt_off ring C s hg y hreachY h hh e he1 he2
      have hpu' := pupin_next ring C s hg y e hpu (misAt_free s _ h hmo)
      have hpin' := pupin_pinned ring C s _ hpu'
      exact Or.inr ⟨⟨hpu', pinned_down ring C s _ hpin',
        misTail_of_pinned ring C s hg _ h hpin' hmo⟩, noPrefixStop_next ring C s y e hnps hst⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.stop_race_structure
