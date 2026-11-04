import Leader.L3.Top.FinalMobileClasses
import Leader.L3.Top.FinalMobileCost
import Leader.L3.Top.FinalMobileLink
import Leader.L3.Top.SuffixLinv

/-!
# Q7 (P.11): the final mobile phase without a premise

`topClockFinalMobilePhase_final_holds` proves `TopClockFinalMobilePhase` for the final classes.
The clearing run keeps the invariant "extends the settled-empty cut, no settled input, pending
inputs left of every obstacle, no old pending input" (`clearGood_next`, `noOld_next`); the serial
suffix of the pending inputs is not carried but derived at every state of the run
(`suffix_of_pinned`, from the labelled window invariant and the distinctness of the exported
operands).  Hence the serial-suffix append of the earlier conditional proof,
`TopFinalSuffixKeeps`, is not needed: `suffix_next_of_pinned` is the append, for every edge.

Consumer: `TopClockPhaseBundle.mobile` (TopClockAssembly).
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false

/-- Extensions of extensions are extensions.

Consumer: `topClockFinalMobilePhase_final_holds`. -/
theorem markedFrom_trans {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Y0 Z Y : TopFixedTraceState n) (h1 : MarkedFrom ring C Y0 Z) (h2 : MarkedFrom ring C Z Y) :
    MarkedFrom ring C Y0 Y := by
  obtain ⟨w0, hw0⟩ := h1
  obtain ⟨w, hw⟩ := h2
  refine ⟨w0 ++ w, ?_⟩
  rw [hw, hw0, topFixedTraceRun_snd, List.append_assoc]

/-- **The serial-suffix append.**  From a state that extends a permanent first-tail cut and has no
pending input that is old with respect to the clock of the cut, every edge keeps both, so the next
state has the serial suffix of its pending inputs: a packet accepted in the step is appended with
its own export serial, and no pending input is lost.

Consumer: `topClockFinalMobilePhase_final_holds`. -/
theorem suffix_next_of_pinned {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y0 Y : TopFixedTraceState n)
    (hcut : topFreshTailPermanentCut ring C s Y0) (hY : MarkedFrom ring C Y0 Y)
    (hold : topClockNoOldPending s Y Y0.1.2.clock) (e : Fin n) :
    topClockConcreteConsecutivePendingSuffix s (topFixedTraceNext ring C Y e) := by
  have hreach := markedFrom_reached ring C Y0 Y hY
  have hτ : Y0.1.2.clock ≤ Y.1.2.clock := markedFrom_clock ring C Y0 Y hcut.1 hY
  exact suffix_of_pinned ring C s hg Y0 _ hcut (markedFrom_next ring C Y0 Y e hY)
    (noOld_next ring C s hg _ Y hreach hτ e hold)

/-- **P.11 for the final classes, without a premise.**  At every eligible entrance, from every
strict stop or settled-empty cut, the expected time to a strict stop or a pending-only cut is at
most `n * r`.

Consumer: `TopClockPhaseBundle.mobile` (TopClockAssembly). -/
theorem topClockFinalMobilePhase_final_holds {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockFinalMobilePhase ring C s (topClockFinalClasses ring C s) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  intro Z hZ
  have hn0 : 0 < n := by omega
  have hr3 := span_ge_three hn
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) (topClockStopOr ring C s (topClockFinalClasses ring C s).pendingOnly)
    hn0 Z (n * topClockSpan n)).2
  intro T
  by_cases hstop : topClockStopOr ring C s (topClockFinalClasses ring C s).pendingOnly Z
  · rw [costNumerator_terminal _ _ Z hstop T]
    exact Nat.zero_le _
  · have hse : (topClockFinalClasses ring C s).settledEmpty Z := by
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
        (topClockFinalClasses ring C s).pendingOnly Y → 0 < clearPot s Y := by
      intro Y hY hnot
      by_cases h0 : clearPot s Y = 0
      · exfalso
        apply hnot
        right
        have hY0 := markedFrom_trans ring C Y0 Z Y hmf0 hY.1
        have hdown := markedFrom_down ring C s Y0 Y hcut hY0
        have hreach := markedFrom_reached ring C Z Y hY.1
        exact ⟨hdown, hreach, markedDown_pure ring C s Y hdown,
          suffix_of_pinned ring C s hg Y0 Y hcut hY0 hY.2.2, shape_of_clear s Y hY.2.1 h0⟩
      · omega
    have hcost := topFinalCostOfRows
      (topFixedTraceNext ring C) I
      (topClockStopOr ring C s (topClockFinalClasses ring C s).pendingOnly)
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

#print axioms L3.MarkedCells.suffix_next_of_pinned
#print axioms L3.MarkedCells.topClockFinalMobilePhase_final_holds
