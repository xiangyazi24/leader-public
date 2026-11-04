import Leader.L3.Top.PinnedRaceOff
import Leader.L3.Top.PinnedClasses
import Leader.L3.Top.FinalMobileCost

/-!
# Q7 (P.12): the two-edge race for the pinned classes

From a pinned misplaced-tail cut with nonborder tail at `h`:

* any edge other than the outgoing edge `winSite s h` and the incoming edge `winSite s (h - 1)`
  leaves the cut pinned and misplaced at `h` (`misAt_off`);
* the outgoing edge turns the tail into an erasure front: the successor is in the favourable class
  (`race_favourable`);
* the incoming edge makes the successor a pinned coloured cut: the unfavourable class
  (`race_unfavourable`), even when the edge merely frames.

Hence the first of the two edges ends the race, and one of them is selected within mean `n`.

Consumer: `TopClockPhaseBundle.race` (TopClockAssembly).
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- A pinned state misplaced at `h` is a misplaced-tail cut.

Consumer: `race_favourable`, `race_unfavourable`. -/
theorem misTail_of_pinned {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y : TopFixedTraceState n) (h : Fin (topClockSpan n))
    (hp : topClockPinned ring C s Y) (hm : topClockConcreteMisplacedAt s Y h) :
    topClockConcreteMisplacedTail ring C s Y := by
  obtain ⟨Y0, hcut, hfrom, hold⟩ := hp
  exact ⟨markedFrom_reached ring C Y0 Y hfrom,
    markedDown_pure ring C s Y (markedFrom_down ring C s Y0 Y hcut hfrom),
    suffix_of_pinned ring C s hg Y0 Y hcut hfrom hold, h, hm⟩

/-- An erasure-front cell is a physical front input.

Consumer: `race_favourable`. -/
theorem qIn_x_of_cell {n : Nat} (Y : TopFixedTraceState n) (v : Fin n)
    (h : (siteCell Y v).i = .x) : (Y.1.1 v).qIn = .X := by
  unfold siteCell at h
  simp only at h
  rcases hq : (Y.1.1 v).qIn with _ | _ | ⟨a, t⟩ | ⟨a, t⟩
  · rw [hq] at h; exact absurd h (by simp [absIn])
  · rfl
  · rw [hq] at h; cases t <;> exact absurd h (by simp [absIn])
  · rw [hq] at h; cases t <;> exact absurd h (by simp [absIn])

/-- **The outgoing edge wins: the successor is in the favourable class.**

Consumer: `topPinnedRacePhase`. -/
theorem race_favourable {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y : TopFixedTraceState n) (h : Fin (topClockSpan n))
    (hp : topClockPinned ring C s Y) (hm : topClockConcreteMisplacedAt s Y h) :
    (topClockPinnedClasses ring C s).favourable
      (topFixedTraceNext ring C Y (winSite s h.val)) := by
  have hreach : topClockReached ring C Y := by
    obtain ⟨Y0, _, hfrom, _⟩ := hp
    exact markedFrom_reached ring C Y0 Y hfrom
  have hnext := topPreparationPinnedNext ring C s hg Y (winSite s h.val) hp
  have hmis := misTail_of_pinned ring C s hg Y h hp hm
  have hrun : topFixedTraceRun ring C Y.2 = Y := hreach.symm
  have hh1 := hm.1
  have hh2 := hm.2.1
  have hr3 := span_ge_three hg.hn
  have hcells := misAt_cells s Y h hm
  have hag := link_window ring C s Y hg hreach h.val h.isLt h.val h.isLt
  have hx : (cellOf s (topFixedTraceNext ring C Y (winSite s h.val)) h.val).i = .x := by
    rw [hag]
    unfold edgeStep
    rw [if_pos hh2]
    simp only [setTwo, if_true]
    have hb : decide (h.val = 0) = false := by simp; omega
    exact pair_event_a (decide (h.val = 0)) false (cellOf s Y h.val) (cellOf s Y (h.val + 1))
      (by rw [hcells.2.2]) (by rw [hcells.2.2]) hb
  refine ⟨pinned_down ring C s _ hnext, topClockReachedNext ring C Y _ hreach, Y.2, h, ?_, ?_, rfl, ?_⟩
  · rw [hrun]; exact hmis
  · rw [hrun]; exact hm
  · exact qIn_x_of_cell _ _ hx

/-- The rank of a window does not rise along a real edge.

Consumer: `race_unfavourable`. -/
theorem rank_next_le {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) (e : Fin n) :
    rank (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e)) ≤
      rank (topClockSpan n) (cellOf s Y) := by
  have hr3 := span_ge_three hg.hn
  obtain ⟨cells', hstep, hagree⟩ := link_step ring C s Y hg hreach e
  have h1 := rank_step_le _ (by omega) _ _ hstep
  have h2 := rank_congr (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e)) cells' hagree
  omega

/-- **The incoming edge wins (or merely frames): the successor is in the unfavourable class.**

Consumer: `topPinnedRacePhase`. -/
theorem race_unfavourable {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y : TopFixedTraceState n) (h : Fin (topClockSpan n))
    (hp : topClockPinned ring C s Y) (hm : topClockConcreteMisplacedAt s Y h) :
    (topClockPinnedClasses ring C s).unfavourable
      (topFixedTraceNext ring C Y (winSite s (h.val - 1))) := by
  have hreach : topClockReached ring C Y := by
    obtain ⟨Y0, _, hfrom, _⟩ := hp
    exact markedFrom_reached ring C Y0 Y hfrom
  have hnext := topPreparationPinnedNext ring C s hg Y (winSite s (h.val - 1)) hp
  have hmis := misTail_of_pinned ring C s hg Y h hp hm
  have hrun : topFixedTraceRun ring C Y.2 = Y := hreach.symm
  have hrank : rank (topClockSpan n)
      (cellOf s (topFixedTraceNext ring C Y (winSite s (h.val - 1)))) = 0 := by
    have := rank_next_le ring C s hg Y hreach (winSite s (h.val - 1))
    have h0 := misAt_rank_zero s Y h hm
    omega
  have hcol := rank_zero_coloured ring C s hg _ (pinned_down ring C s _ hnext) hrank
  refine ⟨hnext, hcol, Y.2, h, ?_, ?_, ?_⟩
  · rw [hrun]; exact hmis
  · rw [hrun]; exact hm
  · change Y.2 ++ [winSite s (h.val - 1)] = Y.2 ++ [certSite s (topClockSpan n + h.val - 1)]
    have hh1 := hm.1
    have : topClockSpan n + (h.val - 1) = topClockSpan n + h.val - 1 := by omega
    unfold winSite
    rw [this]

/-- **P.12 race for the pinned classes.**  From a strict stop or a pinned misplaced-tail cut the
expected time to a strict stop, a favourable cut or an unfavourable cut is at most `n`.

Consumer: `TopClockPhaseBundle.race` (TopClockAssembly). -/
theorem topPinnedRacePhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockRacePhase ring C s (topClockPinnedClasses ring C s) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  intro Z hZ
  have hn0 : 0 < n := by omega
  let Pt : TopFixedTraceState n → Prop := fun Y =>
    topFixedStrictStop ring C s Y ∨ (topClockPinnedClasses ring C s).favourable Y ∨
      (topClockPinnedClasses ring C s).unfavourable Y
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) Pt hn0 Z n).2
  intro T
  by_cases hstop : topFixedStrictStop ring C s Z
  · rw [costNumerator_terminal _ _ Z (Or.inl hstop) T]
    exact Nat.zero_le _
  · have hmis : (topClockPinnedClasses ring C s).misplacedTail Z := by
      rcases hZ with h | h
      · exact absurd h hstop
      · exact h
    obtain ⟨hpin, hdown, hreach, hpure, hsuf, h, hh⟩ := hmis
    let R : TopFixedTraceState n → Prop := fun Y =>
      topClockPinned ring C s Y ∧ topClockConcreteMisplacedAt s Y h
    let I : TopFixedTraceState n → Prop := fun Y => R Y ∨ Pt Y
    have hreachR : ∀ Y, R Y → topClockReached ring C Y := by
      intro Y hY
      obtain ⟨Y0, _, hfrom, _⟩ := hY.1
      exact markedFrom_reached ring C Y0 Y hfrom
    have hcost := topFinalCostOfRows (topFixedTraceNext ring C) I Pt (fun _ => 1)
      (fun _ => winSite s h.val)
      (by
        intro Y hI hnot e
        rcases hI with hR | hP
        · by_cases he1 : e = winSite s h.val
          · subst he1
            exact Or.inr (Or.inr (Or.inl (race_favourable ring C s hg Y h hR.1 hR.2)))
          · by_cases he2 : e = winSite s (h.val - 1)
            · subst he2
              exact Or.inr (Or.inr (Or.inr (race_unfavourable ring C s hg Y h hR.1 hR.2)))
            · exact Or.inl ⟨topPreparationPinnedNext ring C s hg Y e hR.1,
                misAt_off ring C s hg Y (hreachR Y hR) h hR.2 e he1 he2⟩
        · exact absurd hP hnot)
      (fun _ _ _ => by omega)
      (fun Y _ _ e => Or.inr (Nat.le_refl _))
      (by
        intro Y hI hnot
        rcases hI with hR | hP
        · exact Or.inl (Or.inr (Or.inl (race_favourable ring C s hg Y h hR.1 hR.2)))
        · exact absurd hP hnot)
      Z (Or.inl ⟨hpin, hh⟩) T
    exact Nat.le_trans hcost (by simp)

end MarkedCells
end L3

#print axioms L3.MarkedCells.race_favourable
#print axioms L3.MarkedCells.race_unfavourable
#print axioms L3.MarkedCells.topPinnedRacePhase
