import Leader.L3.Top.RepairedPhase

/-!
# Q7 (P.11): the final cut classes

`topClockRepairedClasses` has two clauses that P.11 cannot live with.

1. `HasNoOld` is `∃ anchor`.  The settled-empty cut must pin the anchor to the first-tail
   cut `Y0` that the state extends: with another, earlier anchor, packets accepted between
   the two tail exports have atoms outside the pure stream of `Y0`, and they may still be
   pending.  `topClockPinned` asks for no old pending input *after the clock of `Y0`*.
2. The settled-empty class does not carry the serial suffix.  The suffix of pending serials
   cannot be recovered along the P.11 run (no pending input ever leaves in that run), only
   carried; so it is a clause of the cut, to be established by P.6--P.10.

`topClockFinalClasses` changes exactly `coloured`, `settledEmpty`, `unfavourable`; every
spec is reproved, and P.4--P.5 is reproved for the new coloured class.

Consumer: `Leader/L3/TopFinalMobilePhase.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false

/-- The state extends a permanent first-tail cut `Y0` and has no pending input that is old
with respect to the clock of `Y0`.

Consumer: `topClockFinalClasses`. -/
def topClockPinned {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) : Prop :=
  ∃ Y0 : TopFixedTraceState n, topFreshTailPermanentCut ring C s Y0 ∧
    MarkedFrom ring C Y0 Z ∧ topClockNoOldPending s Z Y0.1.2.clock

/-- A pinned state extends a permanent cut.

Consumer: `topClockFinalClasses`. -/
theorem pinned_down {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (h : topClockPinned ring C s Z) : MarkedDown ring C s Z := by
  obtain ⟨Y0, hY0, hZ, _⟩ := h
  exact markedFrom_down ring C s Y0 Z hY0 hZ

/-- **The final cut classes.**

Consumer: `TopClockPhaseBundle.cuts`. -/
noncomputable def topClockFinalClasses {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) : TopClockCutClasses ring C s :=
  { topClockStrongClasses ring C s with
    coloured := fun Z => topClockPinned ring C s Z ∧ topClockConcreteColoured ring C s Z
    settledEmpty := fun Z =>
      topClockPinned ring C s Z ∧ topClockConcreteSettledEmpty ring C s Z ∧
        topClockConcreteMovingBarrier s Z ∧ topClockConcreteGeneratedCarryGap s Z ∧
        topClockConcreteConsecutivePendingSuffix s Z
    unfavourable := fun Z =>
      topClockPinned ring C s Z ∧ topClockConcreteUnfavourable ring C s Z
    colouredSpec := by
      intro Z h
      obtain ⟨hr, _, hb, hgap, hf, hn⟩ := h.2
      exact ⟨hr, pinned_down ring C s Z h.1, hb, hgap, hf, hn⟩
    settledSpec := by
      intro Z h
      exact ⟨h.2.1.1, pinned_down ring C s Z h.1, h.2.1.2.2⟩
    unfavourableSpec := by
      intro Z h
      exact ⟨h.1, h.2.1⟩ }

/-- Marked rank zero at an extension of a permanent cut is the final coloured cut.

Consumer: `topClockMarkedDebtPhase_final`. -/
theorem final_of_zero {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z0 Y : TopFixedTraceState n)
    (hcut : topFreshTailPermanentCut ring C s Z0) (hY : MarkedFrom ring C Z0 Y)
    (h0 : rank (topClockSpan n)
      (markCells (cellOf s Y) (oldFlag s Z0.1.2.clock Y)) = 0) :
    (topClockFinalClasses ring C s).coloured Y := by
  have hrep := repaired_of_zero ring C s hg Z0 Y hcut hY h0
  have hinv := inv_reached ring C s hg Y (markedFrom_reached ring C Z0 Y hY)
  obtain ⟨hmk, _, _⟩ := rank_zero_old _ _ _ hinv h0
  refine ⟨⟨Z0, hcut, hY, ?_⟩, hrep.2.1⟩
  intro j hP
  by_cases hpost : topClockPostAnchor s Y Z0.1.2.clock (topClockConcreteInputAtom s Y j)
  · exact hpost
  · exfalso
    have hfl : oldFlag s Z0.1.2.clock Y j.val = true := by
      rw [oldFlag_iff]
      exact ⟨j.isLt, hP, hpost⟩
    have := hmk j.val j.isLt
    rw [hfl] at this
    exact absurd this (by decide)

/-- The nominated edge of the final-class phase.

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly). -/
noncomputable def chosenFinal {n : Nat} (s : Fin n) (Z0 Y : TopFixedTraceState n) : Fin n :=
  if h : ∃ p, p < topClockSpan n ∧
      rank (topClockSpan n) (markCells (edgeStep (topClockSpan n) (cellOf s Y) p)
        (flagsAt (topClockSpan n) (cellOf s Y) (oldFlag s Z0.1.2.clock Y) p)) + 1 ≤
      rank (topClockSpan n) (markCells (cellOf s Y) (oldFlag s Z0.1.2.clock Y)) then
    winSite s (Classical.choose h)
  else s

/-- **P.4--P.5 for the final classes.**  At every eligible entrance, from every strict
stop or permanent first-tail cut, the expected time to a strict stop or repaired coloured cut
is at most `n * R(r)`.

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly). -/
theorem topClockMarkedDebtPhase_final {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockMarkedDebtPhase ring C s (topClockFinalClasses ring C s) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  intro Z hZ
  have hn0 : 0 < n := by omega
  have hr3 := span_ge_three hn
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) (topClockStopOr ring C s (topClockFinalClasses ring C s).coloured)
    hn0 Z (n * topClockR (topClockSpan n))).2
  intro T
  by_cases hstop : topClockStopOr ring C s (topClockFinalClasses ring C s).coloured Z
  · rw [costNumerator_terminal _ _ Z hstop T]
    exact Nat.zero_le _
  · have hf : topFreshTailPermanentCut ring C s Z := by
      rcases hZ with h | h
      · exact absurd (Or.inl h) hstop
      · exact h
    have hZr : topClockReached ring C Z := hf.1
    have hstart := markedFrom_start ring C Z hZr
    have hpos : ∀ Y, MarkedFrom ring C Z Y →
        ¬ topClockStopOr ring C s (topClockFinalClasses ring C s).coloured Y →
        0 < rank (topClockSpan n) (markCells (cellOf s Y) (oldFlag s Z.1.2.clock Y)) := by
      intro Y hY hnot
      by_cases h0 : rank (topClockSpan n) (markCells (cellOf s Y) (oldFlag s Z.1.2.clock Y)) = 0
      · exfalso
        exact hnot (Or.inr (final_of_zero ring C s hg Z Y hf hY h0))
      · omega
    have hcost := topMarkedCostOfRows
      (topFixedTraceNext ring C) (MarkedFrom ring C Z)
      (topClockStopOr ring C s (topClockFinalClasses ring C s).coloured)
      (fun Y => rank (topClockSpan n) (markCells (cellOf s Y) (oldFlag s Z.1.2.clock Y)))
      (chosenFinal s Z)
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
        have hsel : chosenFinal s Z Y = winSite s (Classical.choose hex) := by
          unfold chosenFinal
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

end MarkedCells
end L3

#print axioms L3.MarkedCells.final_of_zero
#print axioms L3.MarkedCells.topClockMarkedDebtPhase_final
