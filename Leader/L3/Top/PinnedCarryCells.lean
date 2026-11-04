import Leader.L3.Top.PinnedSweepCells

/-!
# Q7 (P.12 preparation): the carry sweep on the abstract window

A window of settled registers with the tail at the border is launched by the border edge into a
carry host; the host moves right one register per service of its own edge, consuming the settled
register it meets, while pending packets pile up on its left; at the last register the carry
retires.  This is the abstract-window part of the aligned completion.

Consumer: `Leader/L3/Top/PinnedCarryTrace.lean` (not yet written).
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- An aligned window before the launch: the tail at the border, settled registers behind it.

Consumer: `carry_align_edge`. -/
def AlignShape (r : Nat) (cells : Nat → Cell) : Prop :=
  2 ≤ r ∧ cells 0 = ⟨.st, .off⟩ ∧ ∀ j, j < r → 0 < j → cells j = ⟨.sn, .off⟩

/-- A window with the carry host at `k`: empty or pending registers on the left, the host with a
fresh carry, settled registers on the right.

Consumer: `carry_edge`. -/
def CarryShape (r k : Nat) (cells : Nat → Cell) : Prop :=
  k < r ∧ (∀ j, j < k → LeftCell (cells j)) ∧ cells k = ⟨.e, .fresh⟩ ∧
  ∀ j, j < r → k < j → cells j = ⟨.sn, .off⟩

/-- The window has been cleared by the retiring carry.

Consumer: `carry_edge`. -/
def CarryDone (r : Nat) (cells : Nat → Cell) : Prop := ∀ j, j < r → LeftCell (cells j)

/-- The border edge launches the carry.

Consumer: `carry_align_edge`. -/
theorem pair_border_launch : pair true false ⟨.st, .off⟩ ⟨.sn, .off⟩ = (⟨.e, .fresh⟩, ⟨.sn, .off⟩) := by
  decide

/-- An interior edge between a pending-or-empty register and the carry host leaves both alone.

Consumer: `carry_edge`. -/
theorem pair_host_left (b : Bool) (x : Cell) (hx : LeftCell x) :
    pair b false x ⟨.e, .fresh⟩ = (x, ⟨.e, .fresh⟩) := by
  rcases x with ⟨xi, xk⟩
  obtain ⟨hx1, hx2⟩ := hx
  simp only at hx1 hx2
  subst hx2
  cases xi <;> cases b <;> first
    | decide
    | (exfalso; simp [Inp.isP] at hx1)

/-- The host consumes the settled register it meets and passes the carry on.

Consumer: `carry_edge`. -/
theorem pair_host_advance (b : Bool) :
    pair b false ⟨.e, .fresh⟩ ⟨.sn, .off⟩ = (⟨.e, .off⟩, ⟨.e, .fresh⟩) := by
  cases b <;> decide

/-- The terminal edge retires the carry.

Consumer: `carry_edge`. -/
theorem pair_host_retire : (pair false true ⟨.e, .fresh⟩ ⟨.e, .off⟩).1 = ⟨.e, .off⟩ := by
  decide

/-- The terminal edge leaves a settled register alone.

Consumer: `carry_edge`. -/
theorem pair_terminal_settled : (pair false true ⟨.sn, .off⟩ ⟨.e, .off⟩).1 = ⟨.sn, .off⟩ := by
  decide

/-- **The edge step keeps the carry shape.**  The host moves right exactly on its own edge and
the carry retires at the last register.

Consumer: `carry_step`. -/
theorem carry_edge (r k : Nat) (cells : Nat → Cell) (hS : CarryShape r k cells) (p : Nat)
    (hp : p < r) :
    (p = k → k + 1 < r → CarryShape r (k + 1) (edgeStep r cells p)) ∧
    (p = k → ¬ k + 1 < r → CarryDone r (edgeStep r cells p)) ∧
    (p ≠ k → CarryShape r k (edgeStep r cells p)) := by
  obtain ⟨hk, h3, h4, h5⟩ := hS
  unfold edgeStep
  by_cases hpr : p + 1 < r
  · rw [if_pos hpr]
    have hnc : ∀ j, setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2 j =
        if j = p then (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        else if j = p + 1 then (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2
        else cells j := fun j => rfl
    refine ⟨?_, ?_, ?_⟩
    · intro hpk hk1
      subst hpk
      have hy : cells (p + 1) = ⟨.sn, .off⟩ := h5 (p + 1) hpr (by omega)
      have hab : pair (decide (p = 0)) false (cells p) (cells (p + 1)) =
          (⟨.e, .off⟩, ⟨.e, .fresh⟩) := by
        rw [h4, hy]; exact pair_host_advance _
      refine ⟨hk1, ?_, ?_, ?_⟩
      · intro j hj
        rw [hnc]
        simp only [hab]
        by_cases a1 : j = p
        · rw [if_pos a1]; exact ⟨Or.inl rfl, rfl⟩
        · rw [if_neg a1, if_neg (by omega)]; exact h3 j (by omega)
      · rw [hnc]
        simp only [hab]
        rw [if_neg (by omega)]
        simp
      · intro j hj hjk
        rw [hnc]
        simp only [hab]
        rw [if_neg (by omega), if_neg (by omega)]
        exact h5 j hj (by omega)
    · intro hpk hk1
      omega
    · intro hpk
      by_cases hlt : p + 1 < k
      · have hpp := pair_left (decide (p = 0)) (cells p) (cells (p + 1)) (h3 p (by omega))
          (h3 (p + 1) hlt)
        refine ⟨hk, ?_, ?_, ?_⟩
        · intro j hj
          rw [hnc]
          by_cases a1 : j = p
          · rw [if_pos a1]; exact hpp.1
          · by_cases a2 : j = p + 1
            · rw [if_neg a1, if_pos a2]; exact hpp.2
            · rw [if_neg a1, if_neg a2]; exact h3 j hj
        · rw [hnc, if_neg (by omega), if_neg (by omega)]; exact h4
        · intro j hj hjk
          rw [hnc, if_neg (by omega), if_neg (by omega)]; exact h5 j hj hjk
      · by_cases heq : p + 1 = k
        · have hy : cells (p + 1) = ⟨.e, .fresh⟩ := by rw [heq]; exact h4
          have hab : pair (decide (p = 0)) false (cells p) (cells (p + 1)) =
              (cells p, ⟨.e, .fresh⟩) := by
            rw [hy]; exact pair_host_left _ _ (h3 p (by omega))
          refine ⟨hk, ?_, ?_, ?_⟩
          · intro j hj
            rw [hnc]
            simp only [hab]
            by_cases a1 : j = p
            · rw [if_pos a1]; exact h3 p (by omega)
            · rw [if_neg a1, if_neg (by omega)]; exact h3 j hj
          · rw [hnc]
            simp only [hab]
            rw [if_neg (by omega), if_pos heq.symm]
          · intro j hj hjk
            rw [hnc]
            simp only [hab]
            rw [if_neg (by omega), if_neg (by omega)]; exact h5 j hj hjk
        · have hgt : k < p := by omega
          have hx1 : cells p = ⟨.sn, .off⟩ := h5 p hp hgt
          have hy : cells (p + 1) = ⟨.sn, .off⟩ := h5 (p + 1) hpr (by omega)
          have hp0 : decide (p = 0) = false := by
            have : p ≠ 0 := by omega
            simp [this]
          have hab : pair (decide (p = 0)) false (cells p) (cells (p + 1)) =
              (⟨.sn, .off⟩, ⟨.sn, .off⟩) := by
            rw [hx1, hy, hp0]; exact pair_settled
          refine ⟨hk, ?_, ?_, ?_⟩
          · intro j hj
            rw [hnc]
            simp only [hab]
            rw [if_neg (by omega), if_neg (by omega)]; exact h3 j hj
          · rw [hnc]
            simp only [hab]
            rw [if_neg (by omega), if_neg (by omega)]; exact h4
          · intro j hj hjk
            rw [hnc]
            simp only [hab]
            by_cases a1 : j = p
            · rw [if_pos a1]
            · by_cases a2 : j = p + 1
              · rw [if_neg a1, if_pos a2]
              · rw [if_neg a1, if_neg a2]; exact h5 j hj hjk
  · rw [if_neg hpr]
    have hpr1 : p = r - 1 := by omega
    refine ⟨?_, ?_, ?_⟩
    · intro hpk hk1
      omega
    · intro hpk hk1
      have hc : cells (r - 1) = ⟨.e, .fresh⟩ := by
        have : k = r - 1 := by omega
        rw [← this]; exact h4
      have ht : (pair false true (cells (r - 1)) { i := .e, c := .off }).1 = ⟨.e, .off⟩ := by
        rw [hc]; exact pair_host_retire
      intro j hj
      simp only [setOne]
      by_cases a1 : j = r - 1
      · rw [if_pos a1, ht]; exact ⟨Or.inl rfl, rfl⟩
      · rw [if_neg a1]; exact h3 j (by omega)
    · intro hpk
      have hgt : k < r - 1 := by omega
      have hc : cells (r - 1) = ⟨.sn, .off⟩ := h5 (r - 1) (by omega) hgt
      have ht : (pair false true (cells (r - 1)) { i := .e, c := .off }).1 = ⟨.sn, .off⟩ := by
        rw [hc]; exact pair_terminal_settled
      refine ⟨hk, ?_, ?_, ?_⟩
      · intro j hj
        simp only [setOne]
        rw [if_neg (by omega)]; exact h3 j hj
      · simp only [setOne]
        rw [if_neg (by omega)]; exact h4
      · intro j hj hjk
        simp only [setOne]
        by_cases a1 : j = r - 1
        · rw [if_pos a1, ht]
        · rw [if_neg a1]; exact h5 j hj hjk

/-- **The edge step keeps the aligned shape except on the border edge, which launches the
carry.**

Consumer: `carry_step`. -/
theorem carry_align_edge (r : Nat) (cells : Nat → Cell) (hS : AlignShape r cells) (p : Nat)
    (hp : p < r) :
    (p = 0 → CarryShape r 0 (edgeStep r cells p)) ∧
    (p ≠ 0 → AlignShape r (edgeStep r cells p)) := by
  obtain ⟨hr, h0, h1⟩ := hS
  unfold edgeStep
  by_cases hpr : p + 1 < r
  · rw [if_pos hpr]
    have hnc : ∀ j, setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2 j =
        if j = p then (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        else if j = p + 1 then (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2
        else cells j := fun j => rfl
    refine ⟨?_, ?_⟩
    · intro hp0
      have hx0 : cells p = ⟨.st, .off⟩ := by rw [hp0]; exact h0
      have hy : cells (p + 1) = ⟨.sn, .off⟩ := h1 (p + 1) hpr (by omega)
      have hd : decide (p = 0) = true := by simp [hp0]
      have hab : pair (decide (p = 0)) false (cells p) (cells (p + 1)) =
          (⟨.e, .fresh⟩, ⟨.sn, .off⟩) := by
        rw [hx0, hy, hd]; exact pair_border_launch
      refine ⟨by omega, ?_, ?_, ?_⟩
      · intro j hj; omega
      · rw [hnc]; simp only [hab]; rw [if_pos hp0.symm]
      · intro j hj hjk
        rw [hnc]
        simp only [hab]
        by_cases a2 : j = p + 1
        · rw [if_neg (by omega), if_pos a2]
        · rw [if_neg (by omega), if_neg a2]; exact h1 j hj (by omega)
    · intro hp0
      have hx1 : cells p = ⟨.sn, .off⟩ := h1 p hp (by omega)
      have hy : cells (p + 1) = ⟨.sn, .off⟩ := h1 (p + 1) hpr (by omega)
      have hp0' : decide (p = 0) = false := by simp [hp0]
      have hab : pair (decide (p = 0)) false (cells p) (cells (p + 1)) =
          (⟨.sn, .off⟩, ⟨.sn, .off⟩) := by
        rw [hx1, hy, hp0']; exact pair_settled
      refine ⟨hr, ?_, ?_⟩
      · rw [hnc]; simp only [hab]; rw [if_neg (by omega), if_neg (by omega)]; exact h0
      · intro j hj hj0
        rw [hnc]
        simp only [hab]
        by_cases a1 : j = p
        · rw [if_pos a1]
        · by_cases a2 : j = p + 1
          · rw [if_neg a1, if_pos a2]
          · rw [if_neg a1, if_neg a2]; exact h1 j hj hj0
  · rw [if_neg hpr]
    have hpr1 : p = r - 1 := by omega
    refine ⟨fun h => by omega, ?_⟩
    intro hp0
    have hc : cells (r - 1) = ⟨.sn, .off⟩ := h1 (r - 1) (by omega) (by omega)
    have ht : (pair false true (cells (r - 1)) { i := .e, c := .off }).1 = ⟨.sn, .off⟩ := by
      rw [hc]; exact pair_terminal_settled
    refine ⟨hr, ?_, ?_⟩
    · simp only [setOne]; rw [if_neg (by omega)]; exact h0
    · intro j hj hj0
      simp only [setOne]
      by_cases a1 : j = r - 1
      · rw [if_pos a1, ht]
      · rw [if_neg a1]; exact h1 j hj hj0

/-- The port edges keep the aligned shape.

Consumer: `carry_step`. -/
theorem align_setOne (r : Nat) (cells : Nat → Cell) (c : Cell) (hS : AlignShape r cells)
    (hc : c = cells 0) : AlignShape r (setOne cells 0 c) := by
  obtain ⟨hr, h0, h1⟩ := hS
  refine ⟨hr, ?_, ?_⟩
  · simp only [setOne]; simp [hc, h0]
  · intro j hj hj0
    simp only [setOne]
    rw [if_neg (by omega)]; exact h1 j hj hj0

/-- The port edges keep the carry shape.

Consumer: `carry_step`. -/
theorem carry_setOne (r k : Nat) (cells : Nat → Cell) (c : Cell) (hS : CarryShape r k cells)
    (hc : (0 < k → LeftCell c) ∧ (k = 0 → c = cells 0)) :
    CarryShape r k (setOne cells 0 c) := by
  obtain ⟨hk, h3, h4, h5⟩ := hS
  refine ⟨hk, ?_, ?_, ?_⟩
  · intro j hj
    simp only [setOne]
    by_cases a : j = 0
    · rw [if_pos a]; exact hc.1 (by omega)
    · rw [if_neg a]; exact h3 j hj
  · simp only [setOne]
    by_cases a : k = 0
    · rw [if_pos a, hc.2 a, ← a]; exact h4
    · rw [if_neg a]; exact h4
  · intro j hj hjk
    simp only [setOne]
    rw [if_neg (by omega)]; exact h5 j hj hjk

end MarkedCells
end L3

#print axioms L3.MarkedCells.carry_edge
#print axioms L3.MarkedCells.carry_align_edge
