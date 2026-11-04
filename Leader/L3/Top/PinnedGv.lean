import Leader.L3.Top.PinnedFill

/-!
# Q7 (P.8--P.10): basic facts of the measure `Gv`

Consumer: `Leader/L3/Top/PinnedStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- Two windows with the same settled, pending and carry pattern below `r`.

Consumer: `Gv_congr`. -/
def SamePat (r : Nat) (c1 c2 : Nat → Cell) : Prop :=
  ∀ k, k < r → (c1 k).i.isS = (c2 k).i.isS ∧ ((c1 k).c ≠ .off ↔ (c2 k).c ≠ .off) ∧
    (c1 k).i.isP = (c2 k).i.isP

/-- The first settled site is at most `r`.

Consumer: `Gv_congr`. -/
theorem fsOf_le (r : Nat) (cells : Nat → Cell) : fsOf r cells ≤ r := firstS_le _ r

/-- The fill weights only read the pending pattern.

Consumer: `Gv_congr`. -/
theorem fillW_congr (r : Nat) (c1 c2 : Nat → Cell) (h : SamePat r c1 c2) (k : Nat) (hk : k < r) :
    fillW r c1 k = fillW r c2 k := by
  unfold fillW
  rw [(h k hk).2.2]

/-- The first settled site only reads the settled pattern.

Consumer: `Gv_congr`. -/
theorem fsOf_congr (r : Nat) (c1 c2 : Nat → Cell) (h : SamePat r c1 c2) :
    fsOf r c1 = fsOf r c2 :=
  firstS_congr _ _ r (fun k hk => (h k hk).1)

/-- The live carry site only reads the carry pattern.

Consumer: `Gv_congr`. -/
theorem hpOf_congr (r : Nat) (c1 c2 : Nat → Cell) (h : SamePat r c1 c2) :
    hpOf r c1 = hpOf r c2 := by
  unfold hpOf
  apply firstS_congr
  intro k hk
  have := (h k hk).2.1
  by_cases h1 : (c1 k).c = .off <;> by_cases h2 : (c2 k).c = .off <;> simp_all

/-- The fill work only reads the patterns.

Consumer: `Gv_congr`. -/
theorem FT_congr (r : Nat) (c1 c2 : Nat → Cell) (h : SamePat r c1 c2) : FT r c1 = FT r c2 := by
  unfold FT
  rw [fsOf_congr r c1 c2 h]
  by_cases hf : fsOf r c2 < r
  · rw [if_pos hf, if_pos hf]
    have := fsOf_le r c2
    rw [wsum_congr (fillW r c1) (fillW r c2) _
      (fun k hk => fillW_congr r c1 c2 h k (by omega))]
  · rw [if_neg hf, if_neg hf]

/-- The measure only reads the patterns.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem Gv_congr (r : Nat) (c1 c2 : Nat → Cell) (h : SamePat r c1 c2) : Gv r c1 = Gv r c2 := by
  unfold Gv
  rw [hpOf_congr r c1 c2 h, FT_congr r c1 c2 h]
  by_cases hp : hpOf r c2 < r
  · rw [if_pos hp, if_pos hp]
    by_cases hq : hpOf r c2 + 1 < r
    · rw [(h _ hq).1]
    · simp [hq]
  · rw [if_neg hp, if_neg hp]

/-- A bounded sum.

Consumer: `FT_le`. -/
theorem wsum_le_below (f : Nat → Nat) (c : Nat) :
    ∀ a, (∀ k, k < a → f k ≤ c) → wsum f a ≤ a * c
  | 0, _ => by simp [wsum]
  | a + 1, h => by
      have := wsum_le_below f c a (fun k hk => h k (by omega))
      have := h a (by omega)
      simp only [wsum]
      rw [Nat.succ_mul]
      omega

/-- The fill work is bounded.

Consumer: `Gv_le`. -/
theorem FT_le (r : Nat) (cells : Nat → Cell) : FT r cells ≤ r * (2 * r + 2) + (r + 1) := by
  unfold FT
  split
  · rename_i hf
    have h1 := wsum_le_below (fillW r cells) (2 * r + 2) (fsOf r cells) (by
      intro k hk
      have := fsOf_le r cells
      unfold fillW
      split <;> omega)
    have h2 : fsOf r cells * (2 * r + 2) ≤ r * (2 * r + 2) :=
      Nat.mul_le_mul_right _ (fsOf_le r cells)
    omega
  · omega

/-- The measure is bounded by `2 r² + 4 r + 3`.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem Gv_le (r : Nat) (cells : Nat → Cell) (hr : 1 ≤ r) : Gv r cells ≤ r * (2 * r + 2) + (r + 1) + 1 + r := by
  have := FT_le r cells
  unfold Gv
  split
  · split <;> omega
  · omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.Gv_congr
#print axioms L3.MarkedCells.Gv_le
#print axioms L3.MarkedCells.fsOf_le
#print axioms L3.MarkedCells.fillW_congr
#print axioms L3.MarkedCells.fsOf_congr
#print axioms L3.MarkedCells.hpOf_congr
#print axioms L3.MarkedCells.FT_congr
#print axioms L3.MarkedCells.wsum_le_below
#print axioms L3.MarkedCells.FT_le
