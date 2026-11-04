import Leader.L3.Top.PinnedRaceCells

/-!
# Q7 (P.12 race): a third edge does not disturb a misplaced-tail cut

At a reached misplaced-tail cut with nonborder tail at `h`, every edge other than the outgoing
edge `winSite s h` and the incoming edge `winSite s (h - 1)` leaves the cut misplaced at the same
`h`: the tail and the settled non-tails to its right keep their checker inputs and their ghost
input atoms (a settled non-tail source or responder is framed by the row), the registers before
the tail stay `E/P` without carry, and the recorded samples stay recorded.

Consumer: `Leader/L3/Top/PinnedRacePhase.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The abstract cells of a misplaced-tail cut.

Consumer: `misAt_off`, `misAt_rank_zero`. -/
theorem misAt_cells {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (h : Fin (topClockSpan n))
    (hh : topClockConcreteMisplacedAt s Z h) :
    (∀ j, j < h.val → EP (cellOf s Z j) ∧ (cellOf s Z j).c = .off) ∧
    (∀ j, h.val ≤ j → j < topClockSpan n →
      (cellOf s Z j).i.isS = true ∧ (cellOf s Z j).c = .off) ∧
    cellOf s Z h.val = { i := .st, c := .off } := by
  obtain ⟨_, _, ⟨sample, _, _, _, _, htail, _⟩, hright, hleft, hcar⟩ := hh
  have hoff : ∀ j : Fin (topClockSpan n), (cellOf s Z j.val).c = .off := by
    intro j
    have := hcar j
    unfold topClockConcreteCarryAt at this
    by_cases hc : (cellOf s Z j.val).c = .off
    · exact hc
    · exfalso
      have := (siteCell_carry_on Z (winSite s j.val)).1 hc
      unfold winSite at this
      rw [‹(Z.1.1 (certSite s (topClockSpan n + j.val))).qCarry = .OFF›] at this
      exact absurd this (by decide)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    refine ⟨?_, hoff ⟨j, by omega⟩⟩
    have := hleft ⟨j, by omega⟩ hj
    unfold cellOf winSite
    exact (siteCell_ep Z _).2 this
  · intro j hj1 hj2
    refine ⟨?_, hoff ⟨j, hj2⟩⟩
    unfold cellOf winSite
    rw [isS_link]
    by_cases hjh : j = h.val
    · subst hjh
      unfold topClockConcreteInputAt at htail
      rw [htail]; rfl
    · obtain ⟨sample', _, _, _, _, hin', _⟩ := hright ⟨j, hj2⟩ (by simp; omega)
      unfold topClockConcreteInputAt at hin'
      rw [hin']; rfl
  · have hc := hoff h
    have hS : (Z.1.1 (winSite s h.val)).qIn = .S sample.value true := htail
    unfold cellOf siteCell
    simp only [hS, absIn]
    have := hoff h
    unfold cellOf siteCell at this
    simp only at this
    rw [this]
    simp

/-- **A misplaced-tail cut has marked-debt rank zero.**

Consumer: `race_unfavourable`. -/
theorem misAt_rank_zero {n : Nat} (s : Fin n) (Z : TopFixedTraceState n)
    (h : Fin (topClockSpan n)) (hh : topClockConcreteMisplacedAt s Z h) :
    rank (topClockSpan n) (cellOf s Z) = 0 := by
  obtain ⟨hL, hR, _⟩ := misAt_cells s Z h hh
  exact rank_zero_of_prefix (topClockSpan n) h.val (cellOf s Z) (by omega) hL hR

end MarkedCells
end L3

#print axioms L3.MarkedCells.misAt_cells
#print axioms L3.MarkedCells.misAt_rank_zero
