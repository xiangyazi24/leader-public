import Leader.L3.Top.SuffixFinalMobile

/-!
# Q7: the pinned tail classes

`topClockFinalClasses` pins the first-tail anchor (`topClockPinned`) in `coloured`,
`settledEmpty` and `unfavourable`, but `pendingOnly` and `misplacedTail` are inherited from
`topClockStrongClasses` and do not carry the pin.  The race phase must reach the pinned
`unfavourable` class from `misplacedTail`, and nothing in `misplacedTail` supplied the anchor.
`topClockPinnedClasses` adds the pin to those two fields; every other field is that of
`topClockFinalClasses`.  P.4--P.5 does not read the two changed fields, and the P.11 clearing run
keeps the pin (its invariant already contains `MarkedFrom Y0 Y` and no old pending input with
respect to the clock of `Y0`), so both phases transfer.

Consumer: `TopClockPhaseBundle.cuts` (TopClockAssembly).
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false

/-- **The pinned tail classes.**  As `topClockFinalClasses`, with the pin also in `pendingOnly`
and `misplacedTail`.

Consumer: `TopClockPhaseBundle.cuts` (TopClockAssembly). -/
noncomputable def topClockPinnedClasses {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) : TopClockCutClasses ring C s :=
  { topClockFinalClasses ring C s with
    pendingOnly := fun Z =>
      topClockPinned ring C s Z ∧ (topClockStrongClasses ring C s).pendingOnly Z
    misplacedTail := fun Z =>
      topClockPinned ring C s Z ∧ (topClockStrongClasses ring C s).misplacedTail Z
    pendingSpec := by
      intro Z h
      exact (topClockStrongClasses ring C s).pendingSpec Z h.2
    misplacedSpec := by
      intro Z h
      exact (topClockStrongClasses ring C s).misplacedSpec Z h.2 }

/-- **P.4--P.5 for the pinned classes**: the final-class proof, since it reads only `firstTail`
and `coloured`.

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly). -/
theorem topClockPinnedMarkedPhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockMarkedDebtPhase ring C s (topClockPinnedClasses ring C s) :=
  topClockMarkedDebtPhase_final ring hn C s hl hbad

/-- **P.11 for the pinned classes.**  At every eligible entrance, from every
strict stop or settled-empty cut, the expected time to a strict stop or a pending-only cut is at
most `n * r`.

Consumer: `TopClockPhaseBundle.mobile` (TopClockAssembly). -/
theorem topClockPinnedMobilePhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockFinalMobilePhase ring C s (topClockPinnedClasses ring C s) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  intro Z hZ
  have hn0 : 0 < n := by omega
  have hr3 := span_ge_three hn
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) (topClockStopOr ring C s (topClockPinnedClasses ring C s).pendingOnly)
    hn0 Z (n * topClockSpan n)).2
  intro T
  by_cases hstop : topClockStopOr ring C s (topClockPinnedClasses ring C s).pendingOnly Z
  · rw [costNumerator_terminal _ _ Z hstop T]
    exact Nat.zero_le _
  · have hse : (topClockPinnedClasses ring C s).settledEmpty Z := by
      rcases hZ with h | h
      · exact absurd (Or.inl h) hstop
      · exact h
    obtain ⟨hpin, hconc, hbarZ, _, _⟩ := hse
    obtain ⟨Y0, hcut, hmf0, hold0⟩ := hpin
    have hZr : topClockReached ring C Z := hconc.1
    -- the invariant class of the clearing run
    let I : TopFixedTraceState n → Prop := fun Y =>
      MarkedFrom ring C Z Y ∧ ClearGood s Y ∧ topClockNoOldPending s Y Y0.1.2.clock
    have hIZ : I Z := ⟨markedFrom_start ring C Z hZr, clearGood_of_cut s Z hconc.2.2 hbarZ, hold0⟩
    have hpos : ∀ Y, I Y → ¬ topClockStopOr ring C s
        (topClockPinnedClasses ring C s).pendingOnly Y → 0 < clearPot s Y := by
      intro Y hY hnot
      by_cases h0 : clearPot s Y = 0
      · exfalso
        apply hnot
        right
        have hY0 := markedFrom_trans ring C Y0 Z Y hmf0 hY.1
        have hdown := markedFrom_down ring C s Y0 Y hcut hY0
        have hreach := markedFrom_reached ring C Z Y hY.1
        exact ⟨⟨Y0, hcut, hY0, hY.2.2⟩, hdown, hreach, markedDown_pure ring C s Y hdown,
          suffix_of_pinned ring C s hg Y0 Y hcut hY0 hY.2.2, shape_of_clear s Y hY.2.1 h0⟩
      · omega
    have hcost := topFinalCostOfRows
      (topFixedTraceNext ring C) I
      (topClockStopOr ring C s (topClockPinnedClasses ring C s).pendingOnly)
      (fun Y => clearPot s Y)
      (clearEdge s)
      (by
        intro Y hY hnot e
        have hph := hpos Y hY hnot
        have hreach := markedFrom_reached ring C Z Y hY.1
        have hY0 := markedFrom_trans ring C Y0 Z Y hmf0 hY.1
        have hτ : Y0.1.2.clock ≤ Y.1.2.clock := markedFrom_clock ring C Y0 Y hcut.1 hY0
        obtain ⟨hcg, _⟩ := clearGood_next ring C s hg Y hreach hY.2.1 hph e
        exact ⟨markedFrom_next ring C Z Y e hY.1, hcg,
          noOld_next ring C s hg _ Y hreach hτ e hY.2.2⟩)
      hpos
      (by
        intro Y hY hnot e
        right
        have hph := hpos Y hY hnot
        have hreach := markedFrom_reached ring C Z Y hY.1
        exact (clearGood_next ring C s hg Y hreach hY.2.1 hph e).2)
      (by
        intro Y hY hnot
        right
        have hph := hpos Y hY hnot
        have hreach := markedFrom_reached ring C Z Y hY.1
        exact clearPot_drop ring C s hg Y hreach hY.2.1 hph)
      Z hIZ T
    exact Nat.le_trans hcost
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (clearPot_le s Z)))

end MarkedCells
end L3

#print axioms L3.MarkedCells.topClockPinnedMarkedPhase
#print axioms L3.MarkedCells.topClockPinnedMobilePhase
