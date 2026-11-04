import Leader.L3.Top.PinnedRaceStayRows
import Leader.L3.Top.PinnedRaceLeft

/-!
# Q7 (P.12--P.13 favourable): the erasure front on the abstract window

A window with empty or pending carry-free registers on the left of the front, the front `x` at
position `k`, and settled non-tail inputs on its right, is moved by every edge to a window of the
same shape, with the front one position further right exactly on the edge at the front.

Consumer: `Leader/L3/TopPinnedSweepTrace.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The shape of a window carrying one erasure front at `k`.

Consumer: `sweep_edge`. -/
def SweepShape (r k : Nat) (cells : Nat → Cell) : Prop :=
  1 ≤ k ∧ k ≤ r ∧ (∀ j, j < k → LeftCell (cells j)) ∧
  (∀ j, j < r → j = k → cells j = ⟨.x, .off⟩) ∧
  (∀ j, j < r → k < j → cells j = ⟨.sn, .off⟩)

/-- The shape only reads the window.

Consumer: `sweep_edge`. -/
theorem sweepShape_congr (r k : Nat) (cells cells' : Nat → Cell)
    (h : ∀ j, j < r → cells' j = cells j) (hS : SweepShape r k cells) :
    SweepShape r k cells' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · intro j hj; rw [h j (by omega)]; exact h3 j hj
  · intro j hj hjk; rw [h j hj]; exact h4 j hj hjk
  · intro j hj hjk; rw [h j hj]; exact h5 j hj hjk

/-- An edge behind the front leaves both registers alone.

Consumer: `sweep_edge`. -/
theorem pair_behind (b : Bool) (x : Cell) (hx : LeftCell x) :
    pair b false x ⟨.x, .off⟩ = (x, ⟨.x, .off⟩) := by
  rcases x with ⟨xi, xk⟩
  obtain ⟨hx1, hx2⟩ := hx
  simp only at hx1 hx2
  subst hx2
  cases xi <;> cases b <;> first
    | decide
    | (exfalso; simp [Inp.isP] at hx1)

/-- The edge at the front moves it right.

Consumer: `sweep_edge`. -/
theorem pair_sweep (b : Bool) :
    pair b false ⟨.x, .off⟩ ⟨.sn, .off⟩ = (⟨.e, .off⟩, ⟨.x, .off⟩) := by
  cases b <;> decide

/-- An interior edge between two settled registers leaves them alone.

Consumer: `sweep_edge`. -/
theorem pair_settled :
    pair false false ⟨.sn, .off⟩ ⟨.sn, .off⟩ = (⟨.sn, .off⟩, ⟨.sn, .off⟩) := by
  decide

/-- **The edge step keeps the front shape; the front moves exactly on its own edge.**

Consumer: `sweep_step`. -/
theorem sweep_edge (r k : Nat) (cells : Nat → Cell) (hk : k < r)
    (hS : SweepShape r k cells) (p : Nat) (hp : p < r) :
    SweepShape r (if p = k then k + 1 else k) (edgeStep r cells p) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  have hS0 : SweepShape r k cells := ⟨h1, h2, h3, h4, h5⟩
  have hkx : cells k = ⟨.x, .off⟩ := h4 k hk rfl
  unfold edgeStep
  by_cases hpr : p + 1 < r
  · rw [if_pos hpr]
    have hnc : ∀ j, setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2 j =
        if j = p then (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        else if j = p + 1 then (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2
        else cells j := fun j => rfl
    by_cases hlt : p + 1 < k
    · have hl1 := h3 p (by omega)
      have hl2 := h3 (p + 1) hlt
      have hpp := pair_left (decide (p = 0)) (cells p) (cells (p + 1)) hl1 hl2
      rw [if_neg (by omega)]
      refine ⟨h1, h2, ?_, ?_, ?_⟩
      · intro j hj
        rw [hnc]
        by_cases a1 : j = p
        · rw [if_pos a1]; exact hpp.1
        · by_cases a2 : j = p + 1
          · rw [if_neg a1, if_pos a2]; exact hpp.2
          · rw [if_neg a1, if_neg a2]; exact h3 j hj
      · intro j hj hjk
        rw [hnc, if_neg (by omega), if_neg (by omega)]; exact h4 j hj hjk
      · intro j hj hjk
        rw [hnc, if_neg (by omega), if_neg (by omega)]; exact h5 j hj hjk
    · by_cases heq : p + 1 = k
      · rw [if_neg (by omega)]
        have hl1 := h3 p (by omega)
        have hy : cells (p + 1) = ⟨.x, .off⟩ := by rw [heq]; exact hkx
        have hab : pair (decide (p = 0)) false (cells p) (cells (p + 1)) =
            (cells p, ⟨.x, .off⟩) := by
          rw [hy]; exact pair_behind _ _ hl1
        apply sweepShape_congr r k cells _ _ hS0
        intro j _
        rw [hnc]
        simp only [hab]
        by_cases a1 : j = p
        · rw [if_pos a1, a1]
        · by_cases a2 : j = p + 1
          · rw [if_neg a1, if_pos a2, a2, hy]
          · rw [if_neg a1, if_neg a2]
      · by_cases hpk : p = k
        · rw [if_pos hpk]
          subst hpk
          have hy : cells (p + 1) = ⟨.sn, .off⟩ := h5 (p + 1) hpr (by omega)
          have hab : pair (decide (p = 0)) false (cells p) (cells (p + 1)) =
              (⟨.e, .off⟩, ⟨.x, .off⟩) := by
            rw [hkx, hy]; exact pair_sweep _
          refine ⟨by omega, by omega, ?_, ?_, ?_⟩
          · intro j hj
            rw [hnc]
            simp only [hab]
            by_cases a1 : j = p
            · rw [if_pos a1]; exact ⟨Or.inl rfl, rfl⟩
            · rw [if_neg a1, if_neg (by omega)]; exact h3 j (by omega)
          · intro j hj hjk
            rw [hnc]
            simp only [hab]
            rw [if_neg (by omega), if_pos hjk]
          · intro j hj hjk
            rw [hnc]
            simp only [hab]
            rw [if_neg (by omega), if_neg (by omega)]
            exact h5 j hj (by omega)
        · rw [if_neg hpk]
          have hgt : k < p := by omega
          have hx1 : cells p = ⟨.sn, .off⟩ := h5 p hp hgt
          have hy : cells (p + 1) = ⟨.sn, .off⟩ := h5 (p + 1) hpr (by omega)
          have hp0 : decide (p = 0) = false := by
            have : p ≠ 0 := by omega
            simp [this]
          have hab : pair (decide (p = 0)) false (cells p) (cells (p + 1)) =
              (⟨.sn, .off⟩, ⟨.sn, .off⟩) := by
            rw [hx1, hy, hp0]; exact pair_settled
          apply sweepShape_congr r k cells _ _ hS0
          intro j _
          rw [hnc]
          simp only [hab]
          by_cases a1 : j = p
          · rw [if_pos a1, a1, hx1]
          · by_cases a2 : j = p + 1
            · rw [if_neg a1, if_pos a2, a2, hy]
            · rw [if_neg a1, if_neg a2]
  · rw [if_neg hpr]
    have hpr1 : p = r - 1 := by omega
    by_cases hkr : k = r - 1
    · rw [if_pos (by omega)]
      have hc : cells (r - 1) = ⟨.x, .off⟩ := by rw [← hkr]; exact hkx
      have ht : (pair false true (cells (r - 1)) { i := .e, c := .off }).1 =
          ⟨.e, .off⟩ := by rw [hc]; decide
      refine ⟨by omega, by omega, ?_, ?_, ?_⟩
      · intro j hj
        simp only [setOne]
        by_cases a1 : j = r - 1
        · rw [if_pos a1, ht]; exact ⟨Or.inl rfl, rfl⟩
        · rw [if_neg a1]; exact h3 j (by omega)
      · intro j hj hjk
        omega
      · intro j hj hjk
        omega
    · rw [if_neg (by omega)]
      have hc : cells (r - 1) = ⟨.sn, .off⟩ := h5 (r - 1) (by omega) (by omega)
      have ht : (pair false true (cells (r - 1)) { i := .e, c := .off }).1 =
          ⟨.sn, .off⟩ := by rw [hc]; decide
      apply sweepShape_congr r k cells _ _ hS0
      intro j _
      simp only [setOne]
      by_cases a1 : j = r - 1
      · rw [if_pos a1, ht, a1, hc]
      · rw [if_neg a1]

end MarkedCells
end L3

#print axioms L3.MarkedCells.sweep_edge
