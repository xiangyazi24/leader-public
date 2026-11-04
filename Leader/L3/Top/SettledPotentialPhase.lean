import Leader.L3.Top.SettledPotentialConvert

/-!
# Q7 (P.6--P.10): the settled-work phase for the pinned classes

From every reached pinned coloured state the expected time to the pinned settled-empty class
(or a strict stop) is at most `n * U(r)`, `U(r) = r^2 (2 r^2 + 8 r + 1) + 5 r`.

The proof is a descent on the charge of the history colouring.  A level of the charge costs a
front stage (`n * 3 r`) and a supply stage (`n * (2 r^2 + r + 3)`); the charge starts below
`r^2 + 1`.  The two stages run on the product chain of states and colourings and are
transferred to the state chain.

Consumer: `TopClockPhaseBundle.settled` (TopClockAssembly).
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The levels of the charge fit in the budget `n * U(r)`.

Consumer: `topClockPinnedSettledWorkPhase`. -/
theorem levels_le_budget (n r : Nat) (hr : 3 ≤ r) :
    (r * r + 1) * levelCost n r ≤ n * topClockU r := by
  have hK : levelCost n r = n * (2 * (r * r) + 4 * r + 3) := by
    unfold levelCost
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [hK, Nat.mul_left_comm]
  apply Nat.mul_le_mul_left
  unfold topClockU
  rw [Nat.pow_two]
  have hR3 : 3 * r ≤ r * r := Nat.mul_le_mul_right r hr
  have h10 : 10 * (r * r) ≤ (r * r) * (4 * r - 2) :=
    Nat.le_trans (Nat.mul_le_mul_right (r * r) (show 10 ≤ 4 * r - 2 by omega))
      (Nat.le_of_eq (Nat.mul_comm _ _))
  have e1 : (r * r) * (2 * (r * r) + 8 * r + 1) =
      (r * r) * (2 * (r * r) + 4 * r + 3) + (r * r) * (4 * r - 2) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have e2 : (r * r + 1) * (2 * (r * r) + 4 * r + 3) =
      (r * r) * (2 * (r * r) + 4 * r + 3) + (2 * (r * r) + 4 * r + 3) := by
    rw [Nat.succ_mul]
  rw [e1, e2]
  omega

/-- **P.6--P.10 for the pinned classes.**  From every strict stop or pinned coloured cut, the
expected time to a strict stop or the pinned settled-empty class is at most `n * U(r)`.

Consumer: `TopClockPhaseBundle.settled` (TopClockAssembly). -/
theorem topClockPinnedSettledWorkPhase {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockSettledWorkPhase ring C s (topClockPinnedClasses ring C s) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  intro Z hZ
  have hn0 : 0 < n := by omega
  have hr3 := span_ge_three hn
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C) (topClockStopOr ring C s (topClockPinnedClasses ring C s).settledEmpty)
    hn0 Z (n * topClockU (topClockSpan n))).2
  intro T
  by_cases hstop : topClockStopOr ring C s (topClockPinnedClasses ring C s).settledEmpty Z
  · rw [costNumerator_terminal _ _ Z hstop T]
    exact Nat.zero_le _
  · have hcol : (topClockPinnedClasses ring C s).coloured Z := by
      rcases hZ with h | h
      · exact absurd (Or.inl h) hstop
      · exact h
    obtain ⟨hpin, hreach, _, hbar, hgap, _, _⟩ := hcol
    have h0 : ColourInv s Z allActive := by
      refine ⟨inv_reached ring C s hg Z hreach, noInh_of_gap s Z hgap, ?_, ?_⟩
      · intro u hu; exact absurd hu (by simp [allActive])
      · intro u hu; exact absurd hu (by simp [allActive])
    have hJ : StateInv ring C s Z := ⟨hreach, hpin, barrier_of_moving s Z hbar⟩
    have hlt : charge (topClockSpan n) (act (topClockSpan n) (cellOf s Z) allActive) <
        topClockSpan n * topClockSpan n + 1 := by
      have := charge_le (act (topClockSpan n) (cellOf s Z) allActive) (topClockSpan n)
      omega
    have hlev := levels_expected ring C s hg (topClockSpan n * topClockSpan n + 1) Z allActive
      ⟨hJ, h0⟩ hlt
    have hc1 := (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (topFixedTraceNext ring C) (fun Y => ¬ SettledAt s Y) hn0 Z _).1 hlev T
    -- the cleared class is part of the target
    let Jinv : TopFixedTraceState n → Prop := fun Y => StateInv ring C s Y ∧ ∃ d, ColourInv s Y d
    have hmono := costNumerator_mono_target (topFixedTraceNext ring C) (fun Y => ¬ SettledAt s Y)
      (topClockStopOr ring C s (topClockPinnedClasses ring C s).settledEmpty) Jinv
      (by
        intro Y hY e
        obtain ⟨hJ', d', hc'⟩ := hY
        have := pinv_next ring C s hg (Y, d') e ⟨hJ', hc'⟩
        exact ⟨this.1, _, this.2⟩)
      (by
        intro Y hY hns
        obtain ⟨hJ', d', hc'⟩ := hY
        exact Or.inr (settledEmpty_of_clear ring C s hg Y hJ' d' hc' hns))
      Z ⟨hJ, allActive, h0⟩ T
    refine Nat.le_trans hmono (Nat.le_trans hc1 ?_)
    apply Nat.mul_le_mul_left
    exact levels_le_budget n (topClockSpan n) hr3

end MarkedCells
end L3

#print axioms L3.MarkedCells.topClockPinnedSettledWorkPhase
