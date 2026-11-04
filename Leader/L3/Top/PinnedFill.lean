import Leader.L3.Top.PinnedShape

/-!
# Q7 (P.8--P.10): the fill and carry measure of a front-free window

`firstS P m` is the first index below `m` where `P` holds (and `m` when there is none);
`wsum f a` is the sum of `f` below `a`.  The measure `Gv` of a window with no front is

* `r - j` while the live carry sits at `j` and its right neighbour is settled (the carry
  consumes a settled run and the charge falls before it can stop);
* otherwise one for a live carry plus the fill work: every site before the first settled site
  costs `1` when pending and `k + r + 3` when not (the packet that has to reach it is still to
  be delivered), plus the reserve `r + 1` for launching and consuming.

Consumer: `Leader/L3/Top/PinnedStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The first index below `m` where `P` holds, and `m` when there is none.

Consumer: `fsOf`. -/
def firstS (P : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => if firstS P m < m then firstS P m else if P m then m else m + 1

/-- The first index is at most the bound.

Consumer: `firstS_eq`. -/
theorem firstS_le (P : Nat → Bool) : ∀ m, firstS P m ≤ m
  | 0 => Nat.le_refl _
  | m + 1 => by
      have := firstS_le P m
      simp only [firstS]
      by_cases h1 : firstS P m < m
      · rw [if_pos h1]; omega
      · rw [if_neg h1]
        by_cases h2 : P m = true
        · rw [if_pos h2]; omega
        · rw [if_neg h2]; omega

/-- Nothing before the first index satisfies the predicate.

Consumer: `firstS_eq`. -/
theorem firstS_before (P : Nat → Bool) : ∀ m k, k < firstS P m → P k = false
  | 0, k, h => by simp [firstS] at h
  | m + 1, k, h => by
      simp only [firstS] at h
      by_cases h1 : firstS P m < m
      · rw [if_pos h1] at h
        exact firstS_before P m k h
      · rw [if_neg h1] at h
        by_cases h2 : P m = true
        · rw [if_pos h2] at h
          have := firstS_le P m
          have hk : k < m := h
          exact firstS_before P m k (by omega)
        · rw [if_neg h2] at h
          have := firstS_le P m
          by_cases hk : k < m
          · exact firstS_before P m k (by omega)
          · have : k = m := by omega
            subst this
            simpa using h2

/-- The first index, when below the bound, satisfies the predicate.

Consumer: `firstS_eq`. -/
theorem firstS_hit (P : Nat → Bool) : ∀ m, firstS P m < m → P (firstS P m) = true
  | 0, h => by simp [firstS] at h
  | m + 1, h => by
      simp only [firstS] at h ⊢
      by_cases h1 : firstS P m < m
      · rw [if_pos h1] at h ⊢
        exact firstS_hit P m h1
      · rw [if_neg h1] at h ⊢
        by_cases h2 : P m = true
        · rw [if_pos h2] at h ⊢
          exact h2
        · rw [if_neg h2] at h; omega

/-- The first index is the least witness.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem firstS_eq (P : Nat → Bool) (m a : Nat) (ha : a < m) (hP : P a = true)
    (hnot : ∀ k, k < a → P k = false) : firstS P m = a := by
  have h1 := firstS_le P m
  have h2 : firstS P m < m := by
    by_cases h : firstS P m < m
    · exact h
    · exfalso
      have h3 : firstS P m = m := by omega
      have := firstS_before P m a (by omega)
      rw [hP] at this; exact absurd this (by simp)
  have h4 := firstS_hit P m h2
  by_cases hlt : firstS P m < a
  · rw [hnot _ hlt] at h4; exact absurd h4 (by simp)
  · by_cases hgt : a < firstS P m
    · have := firstS_before P m a hgt
      rw [hP] at this; exact absurd this (by simp)
    · omega

/-- With no witness the first index is the bound.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem firstS_end (P : Nat → Bool) (m : Nat) (hnot : ∀ k, k < m → P k = false) :
    firstS P m = m := by
  have h1 := firstS_le P m
  by_cases h : firstS P m < m
  · have := firstS_hit P m h
    rw [hnot _ h] at this; exact absurd this (by simp)
  · omega

/-- The first index below the bound exists exactly when a witness does.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem firstS_lt_iff (P : Nat → Bool) (m : Nat) :
    firstS P m < m ↔ ∃ k, k < m ∧ P k = true := by
  constructor
  · intro h
    exact ⟨_, h, firstS_hit P m h⟩
  · rintro ⟨k, hk, hP⟩
    by_cases h : firstS P m < m
    · exact h
    · exfalso
      have h3 : firstS P m = m := by have := firstS_le P m; omega
      have := firstS_before P m k (by omega)
      rw [hP] at this; exact absurd this (by simp)

/-- The first index only depends on the predicate below the bound.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem firstS_congr (P Q : Nat → Bool) :
    ∀ m, (∀ k, k < m → P k = Q k) → firstS P m = firstS Q m
  | 0, _ => rfl
  | m + 1, h => by
      simp only [firstS]
      rw [firstS_congr P Q m (fun k hk => h k (by omega)), h m (by omega)]

/-- The sum of `f` below `a`.

Consumer: `Gv`. -/
def wsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => wsum f k + f k

/-- The sum only depends on the weights below the bound.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem wsum_congr (f g : Nat → Nat) :
    ∀ a, (∀ k, k < a → f k = g k) → wsum f a = wsum g a
  | 0, _ => rfl
  | a + 1, h => by
      simp only [wsum]
      rw [wsum_congr f g a (fun k hk => h k (by omega)), h a (by omega)]

/-- Editing two adjacent weights below the bound.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem wsum_edit (f g : Nat → Nat) (p : Nat) (h : ∀ k, k ≠ p → k ≠ p + 1 → g k = f k) :
    ∀ a, p + 2 ≤ a → wsum g a + f p + f (p + 1) = wsum f a + g p + g (p + 1) := by
  intro a
  induction a with
  | zero => intro ha; omega
  | succ a ih =>
      intro ha
      by_cases h2 : p + 2 ≤ a
      · have := ih h2
        simp only [wsum]
        rw [h a (by omega) (by omega)]
        omega
      · have hap : a = p + 1 := by omega
        subst hap
        have hc : wsum g p = wsum f p := wsum_congr g f p (fun k hk => h k (by omega) (by omega))
        simp only [wsum]
        rw [hc]
        omega

/-- Editing one weight below the bound.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
theorem wsum_edit_one (f g : Nat → Nat) (p : Nat) (h : ∀ k, k ≠ p → g k = f k) :
    ∀ a, p + 1 ≤ a → wsum g a + f p = wsum f a + g p := by
  intro a
  induction a with
  | zero => intro ha; omega
  | succ a ih =>
      intro ha
      by_cases h2 : p + 1 ≤ a
      · have := ih h2
        simp only [wsum]
        rw [h a (by omega)]
        omega
      · have hap : a = p := by omega
        subst hap
        have hc : wsum g a = wsum f a := wsum_congr g f a (fun k hk => h k (by omega))
        simp only [wsum]
        rw [hc]
        omega

/-- The sum is bounded by the bound times a uniform weight bound.

Consumer: `Gv_le`. -/
theorem wsum_le (f : Nat → Nat) (c : Nat) (hf : ∀ k, f k ≤ c) : ∀ a, wsum f a ≤ a * c
  | 0 => by simp [wsum]
  | a + 1 => by
      have := wsum_le f c hf a
      have := hf a
      simp only [wsum]
      rw [Nat.succ_mul]
      omega

/-- The fill weight of a site: `1` when pending, `k + r + 3` otherwise.

Consumer: `FT`. -/
def fillW (r : Nat) (cells : Nat → Cell) (k : Nat) : Nat :=
  if (cells k).i.isP = true then 1 else k + r + 3

/-- The first settled site (`r` when none).

Consumer: `FT`. -/
def fsOf (r : Nat) (cells : Nat → Cell) : Nat :=
  firstS (fun k => (cells k).i.isS) r

/-- The live carry site (`r` when none).

Consumer: `Gv`. -/
def hpOf (r : Nat) (cells : Nat → Cell) : Nat :=
  firstS (fun k => decide ((cells k).c ≠ .off)) r

/-- The fill work: the sites before the first settled site, plus the launch reserve.

Consumer: `Gv`. -/
def FT (r : Nat) (cells : Nat → Cell) : Nat :=
  if fsOf r cells < r then wsum (fillW r cells) (fsOf r cells) + (r + 1) else 0

/-- **The measure of a front-free window.**

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
def Gv (r : Nat) (cells : Nat → Cell) : Nat :=
  if hpOf r cells < r then
    (if hpOf r cells + 1 < r ∧ (cells (hpOf r cells + 1)).i.isS = true then r - hpOf r cells
     else 1 + FT r cells)
  else FT r cells

/-- The charge of the settled sites.

Consumer: `Leader/L3/Top/PinnedStep.lean`. -/
noncomputable def At (r : Nat) (cells : Nat → Cell) : Nat :=
  charge r (act r cells (fun _ => False))

end MarkedCells
end L3

#print axioms L3.MarkedCells.wsum_edit
#print axioms L3.MarkedCells.firstS_eq
#print axioms L3.MarkedCells.firstS_le
#print axioms L3.MarkedCells.firstS_before
#print axioms L3.MarkedCells.firstS_hit
#print axioms L3.MarkedCells.firstS_end
#print axioms L3.MarkedCells.firstS_lt_iff
#print axioms L3.MarkedCells.firstS_congr
#print axioms L3.MarkedCells.wsum_congr
#print axioms L3.MarkedCells.wsum_edit_one
#print axioms L3.MarkedCells.wsum_le
