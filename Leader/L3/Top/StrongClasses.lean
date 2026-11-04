import Leader.L3.Top.MarkedDebtRows

/-!
# Q7: cut classes whose purity is permanent

`topClockConcretePureCohorts` is a statement about the exports recorded *so far*.
A state satisfying it can still export impure packets later, and then `pureCohorts`
never holds again; so the phases `TopClockSettledWorkPhase`, `TopClockFinalMobilePhase`
(all `∀ Z, stop-or cuts.coloured Z → ...`) quantify over states from which the target
may be unreachable.  Here every class after the first tail carries the extra clause
`MarkedDown`: the state extends a permanent first-tail cut.  `MarkedDown` is closed
under every edge, and by `topClockPureCohortsOfPermanent` implies the weak purity.

* `topClockStrongClasses` : the record with the clause added to every later class;
* `topClockMarkedDebtPhase_of_cuts` : the P.4--P.5 phase for any record whose first-tail
  class is the permanent cut and whose coloured class contains the coloured states that
  extend a permanent cut;
* `topClockMarkedDebtPhase_strong` : the corollary for `topClockStrongClasses`.

Consumer: `TopClockPhaseBundle.cuts` (TopClockAssembly), for the phases after P.4--P.5.
-/

namespace L3
namespace MarkedCells

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false

/-- The cut classes of `topFreshTailCorrectedClasses`, with every class after the first
tail restricted to the states that extend a permanent first-tail cut.

Consumer: `topClockMarkedDebtPhase_strong`. -/
noncomputable def topClockStrongClasses {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) : TopClockCutClasses ring C s :=
  { pureCohorts := fun Z => MarkedDown ring C s Z
    movingBarrier := topClockConcreteMovingBarrier s
    generatedCarryGap := topClockConcreteGeneratedCarryGap s
    frontProtection := topClockConcreteFrontProtection s
    noTerminalReseed := topClockConcreteNoTerminalReseed ring C s
    consecutivePendingSuffix := fun Z =>
      MarkedDown ring C s Z ∧ topClockConcreteConsecutivePendingSuffix s Z
    firstTail := topFreshTailPermanentCut ring C s
    coloured := fun Z => MarkedDown ring C s Z ∧ topClockConcreteColoured ring C s Z
    settledEmpty := fun Z => MarkedDown ring C s Z ∧ topClockConcreteSettledEmpty ring C s Z
    pendingOnly := fun Z => MarkedDown ring C s Z ∧ topClockConcretePendingOnly ring C s Z
    misplacedTail := fun Z => MarkedDown ring C s Z ∧ topClockConcreteMisplacedTail ring C s Z
    favourable := fun Z => MarkedDown ring C s Z ∧ topClockConcreteFavourable ring C s Z
    unfavourable := fun Z => MarkedDown ring C s Z ∧ topClockConcreteUnfavourable ring C s Z
    firstTailSpec := by
      intro Z h
      obtain ⟨hr, hg, _⟩ := topFreshTailPermanentCutSpec ring C s Z h
      exact ⟨hr, hg, markedDown_start ring C s Z h⟩
    colouredSpec := by
      intro Z h
      obtain ⟨hd, hr, _, hb, hgap, hf, hn⟩ := h
      exact ⟨hr, hd, hb, hgap, hf, hn⟩
    settledSpec := by
      intro Z h
      exact ⟨h.2.1, h.1, h.2.2.2⟩
    pendingSpec := by
      intro Z h
      exact ⟨h.2.1, h.1, ⟨h.1, h.2.2.2.1⟩, h.2.2.2.2⟩
    misplacedSpec := by
      intro Z h
      exact ⟨h.2.1, h.1, ⟨h.1, h.2.2.2.1⟩⟩
    favourableSpec := by
      intro Z h
      exact h.2.1
    unfavourableSpec := by
      intro Z h
      exact ⟨h.1, h.2.1⟩ }

/-- The P.4--P.5 phase for every record whose first-tail class is permanent and whose
coloured class contains the coloured states extending a permanent cut.

Consumer: `topClockMarkedDebtPhase_strong`. -/
theorem topClockMarkedDebtPhase_of_cuts {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) (hg : WinGeo ring C s)
    (cuts : TopClockCutClasses ring C s)
    (hfirst : ∀ Z, cuts.firstTail Z → topFreshTailPermanentCut ring C s Z)
    (hcol : ∀ Y, MarkedDown ring C s Y → topClockConcreteColoured ring C s Y →
      cuts.coloured Y) :
    TopClockMarkedDebtPhase ring C s cuts := by
  classical
  intro Z hZ
  have hn : 0 < n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) (topClockStopOr ring C s cuts.coloured)
    hn Z (n * topClockR (topClockSpan n))).2
  intro T
  by_cases hstop : topClockStopOr ring C s cuts.coloured Z
  · rw [costNumerator_terminal _ _ Z hstop T]
    exact Nat.zero_le _
  · have hf : cuts.firstTail Z := by
      rcases hZ with h | h
      · exact absurd (Or.inl h) hstop
      · exact h
    have hdown := markedDown_start ring C s Z (hfirst Z hf)
    have hpos : ∀ Y, MarkedDown ring C s Y →
        ¬ topClockStopOr ring C s cuts.coloured Y →
        0 < rank (topClockSpan n) (cellOf s Y) := by
      intro Y hY hnot
      by_cases h0 : rank (topClockSpan n) (cellOf s Y) = 0
      · exfalso
        exact hnot (Or.inr (hcol Y hY (rank_zero_coloured ring C s hg Y hY h0)))
      · omega
    have hcost := topMarkedCostOfRows
      (topFixedTraceNext ring C) (MarkedDown ring C s)
      (topClockStopOr ring C s cuts.coloured)
      (fun Y => rank (topClockSpan n) (cellOf s Y))
      (chosenEdge s)
      (fun Y hY e => markedDown_next ring C s Y e hY)
      hpos
      (by
        intro Y hY _ e
        right
        have hreach := markedDown_reached ring C s Y hY
        obtain ⟨cells', hstep, hagree⟩ := link_step ring C s Y hg hreach e
        have h1 := rank_step_le _ (by omega) _ _ hstep
        have h2 := rank_congr (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e))
          cells' hagree
        show rank (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e)) ≤ _
        omega)
      (by
        intro Y hY hnot
        right
        have hreach := markedDown_reached ring C s Y hY
        have hex := rank_progress (topClockSpan n) (by omega) (cellOf s Y) (hpos Y hY hnot)
        have hex' : ∃ p, p < topClockSpan n ∧
            rank (topClockSpan n) (edgeStep (topClockSpan n) (cellOf s Y) p) + 1 ≤
              rank (topClockSpan n) (cellOf s Y) := hex
        have hsel : chosenEdge s Y = winSite s (Classical.choose hex') := by
          unfold chosenEdge
          rw [dif_pos hex']
        have hspec := Classical.choose_spec hex'
        rw [hsel]
        have hagree := link_window ring C s Y hg hreach _ hspec.1
        have h2 := rank_congr (topClockSpan n)
          (cellOf s (topFixedTraceNext ring C Y (winSite s (Classical.choose hex'))))
          (edgeStep (topClockSpan n) (cellOf s Y) (Classical.choose hex')) hagree
        show rank (topClockSpan n)
          (cellOf s (topFixedTraceNext ring C Y (winSite s (Classical.choose hex')))) + 1 ≤ _
        omega)
      Z hdown T
    exact Nat.le_trans hcost
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (rank_start_bound _ _)))

/-- **P.4--P.5 for the permanent-purity classes.**

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly). -/
theorem topClockMarkedDebtPhase_strong {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockMarkedDebtPhase ring C s (topClockStrongClasses ring C s) :=
  topClockMarkedDebtPhase_of_cuts ring C s ⟨hn, hl, hbad⟩ (topClockStrongClasses ring C s)
    (fun _ h => h) (fun Y hY hc => ⟨hY, hc⟩)

end MarkedCells
end L3

#print axioms L3.MarkedCells.topClockMarkedDebtPhase_of_cuts
#print axioms L3.MarkedCells.topClockMarkedDebtPhase_strong
