import Leader.L3.Top.SettledWorkFront
import Leader.L3.Top.SettledWorkPotTrace

/-!
# Q7 (P.7): a front's edge lowers the potential on the fixed trace

Consumer: `Leader/L3/Top/SettledWorkFrontClear.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The barrier is kept by every selected edge (no settled input needed).

Consumer: `Leader/L3/Top/SettledWorkFrontClear.lean`. -/
theorem barrier_next {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (e : Fin n)
    (hni : NoInh (topClockSpan n) (cellOf s Z))
    (hbar : Barrier (topClockSpan n) (cellOf s Z)) :
    Barrier (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) := by
  have hr3 := span_ge_three hg.hn
  have hr2 : 2 ≤ topClockSpan n := by omega
  by_cases hw : ∃ p, p < topClockSpan n ∧ e = winSite s p
  · obtain ⟨p, hp, rfl⟩ := hw
    have hag := link_window ring C s Z hg hreach p hp
    have hstep := edgeStep_step (topClockSpan n) (cellOf s Z) p hp
    exact barrier_cong _ _ _ (fun j hj => (hag j hj).symm)
      (barrier_step _ hr2 _ _ hbar hni hstep)
  · rcases link_shape ring C s Z hg hreach e hw with hag | hag | ⟨t, hag⟩
    · exact barrier_cong _ _ _ (fun j hj => (hag j hj).symm) hbar
    · exact barrier_cong _ _ _ (fun j hj => (hag j hj).symm)
        (barrier_step _ hr2 _ _ hbar hni Step.clean)
    · exact barrier_cong _ _ _ (fun j hj => (hag j hj).symm)
        (barrier_step _ hr2 _ _ hbar hni (Step.accept t))

/-- Arithmetic of the strict lexicographic comparison.

Consumer: `front_step_machine`. -/
theorem pot_lt_of (r A A' M M' : Nat) (hM' : M' ≤ 3 * r)
    (h : A' < A ∨ (A' ≤ A ∧ M' + 1 ≤ M)) :
    A' * (3 * r + 1) + M' + 1 ≤ A * (3 * r + 1) + M := by
  rcases h with h | ⟨h1, h2⟩
  · have : (A' + 1) * (3 * r + 1) ≤ A * (3 * r + 1) :=
      Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this
    omega
  · have := Nat.mul_le_mul_right (3 * r + 1) h1
    omega

/-- **The edge of a front lowers the potential on the fixed trace.**

Consumer: `Leader/L3/Top/SettledWorkFrontClear.lean`. -/
theorem front_step_machine {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (d : Nat → Prop) (p : Nat)
    (hp : p < topClockSpan n)
    (h : ColourInv s Z d) (hbar : Barrier (topClockSpan n) (cellOf s Z))
    (hex : SettledAt s Z) (hxx : (cellOf s Z p).i = .x) :
    Pot (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z (winSite s p)))
        (colourNext ring C s Z (winSite s p) d) + 1 ≤
      Pot (topClockSpan n) (cellOf s Z) d := by
  obtain ⟨hb', hch⟩ := charge_step_machine ring C s hg Z hreach d (winSite s p) h hbar hex
  obtain ⟨hinv, hni, hcov, hlt⟩ := h
  have hr3 := span_ge_three hg.hn
  have hr2 : 2 ≤ topClockSpan n := by omega
  unfold Pot
  have hidx := edgeIdx_window hg.hn s p hp
  have hag := link_window ring C s Z hg hreach p hp
  have hcol : colourNext ring C s Z (winSite s p) d =
      colourGen (topClockSpan n) (cellOf s Z) (edgeStep (topClockSpan n) (cellOf s Z) p) d
        (some p) := by
    unfold colourNext
    rw [hidx]
    exact colourGen_congr _ _ _ _ _ _ hag
  rw [hcol] at hch ⊢
  rw [act_congr _ _ _ _ hag] at hch
  rw [act_congr _ _ _ _ hag, Mn_cong _ _ _ _ hag]
  by_cases hp1 : p + 1 < topClockSpan n
  · have he : edgeStep (topClockSpan n) (cellOf s Z) p =
        setTwo (cellOf s Z) p
          (pair (decide (p = 0)) false (cellOf s Z p) (cellOf s Z (p + 1))).1
          (pair (decide (p = 0)) false (cellOf s Z p) (cellOf s Z (p + 1))).2 := by
      unfold edgeStep; rw [if_pos hp1]
    rw [he] at hch ⊢
    have hep := front_edge_pot _ _ d p hp1 hinv hni hxx
    refine pot_lt_of _ _ _ _ _ (Mn_le _ _ _) ?_
    rcases hep with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨hch, h1⟩
  · have hpr : p + 1 = topClockSpan n := by omega
    have he : edgeStep (topClockSpan n) (cellOf s Z) p =
        setOne (cellOf s Z) p
          (pair false true (cellOf s Z p) { i := .e, c := .off }).1 := by
      unfold edgeStep
      rw [if_neg hp1]
      have : topClockSpan n - 1 = p := by omega
      rw [this]
    rw [he] at hch ⊢
    have hep := front_term_pot _ _ d p hpr hinv hni hxx
    exact pot_lt_of _ _ _ _ _ (Mn_le _ _ _) (Or.inr ⟨hch, hep⟩)

end MarkedCells
end L3

#print axioms L3.MarkedCells.front_step_machine
