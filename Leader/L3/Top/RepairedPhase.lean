import Leader.L3.Top.RepairedMarked

/-!
# Q7: `TopClockMarkedDebtPhase` for the repaired classes

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly).
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false

/-- The marked rank of the abstract step of register `p` does not exceed the marked rank.

Consumer: `topClockMarkedDebtPhase_repaired`. -/
theorem rank_edgeStep_old_le (r p : Nat) (hr : 2 ≤ r) (hp : p < r) (cells : Nat → Cell)
    (o : Nat → Bool) (ho : ∀ j, j < r → o j = true → (cells j).i.isP = true)
    (hf : ∀ j, j < r → (cells j).c = .fresh → (cells j).i = .e) :
    rank r (markCells (edgeStep r cells p) (flagsAt r cells o p)) ≤ rank r (markCells cells o) := by
  unfold edgeStep flagsAt
  by_cases h : p + 1 < r
  · rw [if_pos h, if_pos h]
    exact rank_edge_old r p h cells o ho hf
  · rw [if_neg h, if_neg h]
    exact rank_term_old r hr cells o ho hf

/-- Marked rank zero at an extension of a permanent cut is the repaired coloured cut.

Consumer: `topClockMarkedDebtPhase_repaired`. -/
theorem repaired_of_zero {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z0 Y : TopFixedTraceState n)
    (hcut : topFreshTailPermanentCut ring C s Z0) (hY : MarkedFrom ring C Z0 Y)
    (h0 : rank (topClockSpan n)
      (markCells (cellOf s Y) (oldFlag s Z0.1.2.clock Y)) = 0) :
    (topClockRepairedClasses ring C s).coloured Y := by
  have hdown := markedFrom_down ring C s Z0 Y hcut hY
  have hreach := markedFrom_reached ring C Z0 Y hY
  have hinv := inv_reached ring C s hg Y hreach
  obtain ⟨hmk, _, _⟩ := rank_zero_old _ _ _ hinv h0
  have hreal : rank (topClockSpan n) (cellOf s Y) = 0 := by
    have hle := rank_mark_mono (topClockSpan n) (cellOf s Y) (oldFlag s Z0.1.2.clock Y)
      (fun _ => false) (fun j h => absurd h (by simp))
    have heq : markCells (cellOf s Y) (fun _ => false) = cellOf s Y := by
      funext j; simp [markCells, mk]
    rw [heq] at hle
    omega
  refine ⟨hdown, rank_zero_coloured ring C s hg Y hdown hreal, ?_⟩
  have hcut2 := hcut
  obtain ⟨_, _, anchor, hanchor, htime, _⟩ := hcut2
  obtain ⟨w, hw⟩ := hY
  have hYf : Y = w.foldl (topFixedTraceNext ring C) Z0 := by
    rw [hw, topFixedTraceRunAppendWord]
    have : topFixedTraceRun ring C Z0.2 = Z0 := hcut.1.symm
    rw [this]
  refine ⟨anchor, ?_, ?_⟩
  · rw [hYf]
    exact topClockTailAnchorWord ring C s anchor w Z0 hanchor
  · intro j hP
    by_cases hpost : topClockPostAnchor s Y anchor.time (topClockConcreteInputAtom s Y j)
    · exact hpost
    · exfalso
      have hfl : oldFlag s Z0.1.2.clock Y j.val = true := by
        rw [oldFlag_iff]
        refine ⟨j.isLt, ?_, ?_⟩
        · exact hP
        · rw [← htime]; exact hpost
      have := hmk j.val j.isLt
      rw [hfl] at this
      exact absurd this (by decide)

/-- The nominated edge of the repaired phase.

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly). -/
noncomputable def chosenOld {n : Nat} (s : Fin n) (Z0 Y : TopFixedTraceState n) : Fin n :=
  if h : ∃ p, p < topClockSpan n ∧
      rank (topClockSpan n) (markCells (edgeStep (topClockSpan n) (cellOf s Y) p)
        (flagsAt (topClockSpan n) (cellOf s Y) (oldFlag s Z0.1.2.clock Y) p)) + 1 ≤
      rank (topClockSpan n) (markCells (cellOf s Y) (oldFlag s Z0.1.2.clock Y)) then
    winSite s (Classical.choose h)
  else s

/-- **P.4--P.5 for the repaired classes.**  At every eligible entrance, from every strict
stop or permanent first-tail cut, the expected time to a strict stop or repaired coloured cut
is at most `n * R(r)`.

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly). -/
theorem topClockMarkedDebtPhase_repaired {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockMarkedDebtPhase ring C s (topClockRepairedClasses ring C s) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  intro Z hZ
  have hn0 : 0 < n := by omega
  have hr3 := span_ge_three hn
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) (topClockStopOr ring C s (topClockRepairedClasses ring C s).coloured)
    hn0 Z (n * topClockR (topClockSpan n))).2
  intro T
  by_cases hstop : topClockStopOr ring C s (topClockRepairedClasses ring C s).coloured Z
  · rw [costNumerator_terminal _ _ Z hstop T]
    exact Nat.zero_le _
  · have hf : topFreshTailPermanentCut ring C s Z := by
      rcases hZ with h | h
      · exact absurd (Or.inl h) hstop
      · exact h
    have hZr : topClockReached ring C Z := hf.1
    have hstart := markedFrom_start ring C Z hZr
    have hpos : ∀ Y, MarkedFrom ring C Z Y →
        ¬ topClockStopOr ring C s (topClockRepairedClasses ring C s).coloured Y →
        0 < rank (topClockSpan n) (markCells (cellOf s Y) (oldFlag s Z.1.2.clock Y)) := by
      intro Y hY hnot
      by_cases h0 : rank (topClockSpan n) (markCells (cellOf s Y) (oldFlag s Z.1.2.clock Y)) = 0
      · exfalso
        exact hnot (Or.inr (repaired_of_zero ring C s hg Z Y hf hY h0))
      · omega
    have hcost := topMarkedCostOfRows
      (topFixedTraceNext ring C) (MarkedFrom ring C Z)
      (topClockStopOr ring C s (topClockRepairedClasses ring C s).coloured)
      (fun Y => rank (topClockSpan n) (markCells (cellOf s Y) (oldFlag s Z.1.2.clock Y)))
      (chosenOld s Z)
      (fun Y hY e => markedFrom_next ring C Z Y e hY)
      hpos
      (by
        intro Y hY _ e
        right
        have hreach := markedFrom_reached ring C Z Y hY
        have hinv := inv_reached ring C s hg Y hreach
        have hτ := markedFrom_clock ring C Z Y hZr hY
        have ho : ∀ j, j < topClockSpan n → oldFlag s Z.1.2.clock Y j = true →
            (cellOf s Y j).i.isP = true := fun j _ h => oldFlag_isP s _ Y j h
        have hfr : ∀ j, j < topClockSpan n → (cellOf s Y j).c = .fresh →
            (cellOf s Y j).i = .e := fun j hj h => (hinv.1 j hj h).1
        show rank (topClockSpan n) (markCells (cellOf s (topFixedTraceNext ring C Y e))
          (oldFlag s Z.1.2.clock (topFixedTraceNext ring C Y e))) ≤ _
        by_cases hw : ∃ p, p < topClockSpan n ∧ e = winSite s p
        · obtain ⟨p, hp, rfl⟩ := hw
          exact Nat.le_trans (rank_next_window ring C s hg _ Y hreach p hp)
            (rank_edgeStep_old_le _ p (by omega) hp _ _ ho hfr)
        · by_cases hb : e = certSite s (topClockSpan n - 1)
          · exact rank_next_port ring C s hg _ Y hreach hτ e hb hinv
          · exact rank_next_frame ring C s hg _ Y e hw hb)
      (by
        intro Y hY hnot
        right
        have hreach := markedFrom_reached ring C Z Y hY
        have hinv := inv_reached ring C s hg Y hreach
        have ho : ∀ j, j < topClockSpan n → oldFlag s Z.1.2.clock Y j = true →
            (cellOf s Y j).i.isP = true := fun j _ h => oldFlag_isP s _ Y j h
        have hfr : ∀ j, j < topClockSpan n → (cellOf s Y j).c = .fresh →
            (cellOf s Y j).i = .e := fun j hj h => (hinv.1 j hj h).1
        have hex := rank_progress_old (topClockSpan n) (by omega) (cellOf s Y)
          (oldFlag s Z.1.2.clock Y) ho hfr (hpos Y hY hnot)
        have hsel : chosenOld s Z Y = winSite s (Classical.choose hex) := by
          unfold chosenOld
          rw [dif_pos hex]
        have hspec := Classical.choose_spec hex
        rw [hsel]
        have h1 := rank_next_window ring C s hg Z.1.2.clock Y hreach _ hspec.1
        show rank (topClockSpan n)
          (markCells (cellOf s (topFixedTraceNext ring C Y (winSite s (Classical.choose hex))))
            (oldFlag s Z.1.2.clock
              (topFixedTraceNext ring C Y (winSite s (Classical.choose hex))))) + 1 ≤ _
        have := hspec.2
        omega)
      Z hstart T
    exact Nat.le_trans hcost
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (rank_start_bound _ _)))

/-- **Item 4: the front cover applies from repaired coloured cuts.**  A repaired coloured cut
is a coloured cut, so the history colouring from it keeps the cover invariant at every state
reached along any continuation word.

Consumer: `Leader/L3/TopSettledWork.lean`. -/
theorem cover_after_repaired {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y0 : TopFixedTraceState n)
    (h : (topClockRepairedClasses ring C s).coloured Y0) (w : List (Fin n)) :
    ColourInv s (w.foldl (topFixedTraceNext ring C) Y0) (colourWord ring C s Y0 allActive w) :=
  cover_after_coloured ring C s hg Y0 h.2.1 w

end MarkedCells
end L3

#print axioms L3.MarkedCells.cover_after_repaired
#print axioms L3.MarkedCells.repaired_of_zero
#print axioms L3.MarkedCells.topClockMarkedDebtPhase_repaired
