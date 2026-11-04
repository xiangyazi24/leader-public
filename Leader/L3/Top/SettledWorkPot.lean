import Leader.L3.Top.SettledWorkTrace

/-!
# Q7 (P.7): the front debt `M = 2 D + X`

`D` counts the doomed settled inputs and `X` the erasure fronts of the abstract window.
This module has the counting lemmas and the local front count of one edge.

Consumer: `Leader/L3/Top/SettledWorkPotEdge.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- Number of `k < r` with `P k`.

Consumer: `cnt_edit`. -/
def cnt (P : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => cnt P k + (if P k then 1 else 0)

/-- The count is monotone in the predicate.

Consumer: `Leader/L3/Top/SettledWorkPotEdge.lean`. -/
theorem cnt_mono (P Q : Nat → Bool) (h : ∀ k, P k = true → Q k = true) :
    ∀ r, cnt P r ≤ cnt Q r
  | 0 => Nat.le_refl _
  | k + 1 => by
      have := cnt_mono P Q h k
      simp only [cnt]
      by_cases hp : P k = true
      · simp [hp, h k hp]; omega
      · simp [hp]; split <;> omega

/-- The count drops when a member is removed.

Consumer: `Leader/L3/Top/SettledWorkPotEdge.lean`. -/
theorem cnt_lt (P Q : Nat → Bool) (h : ∀ k, P k = true → Q k = true) (q : Nat)
    (hq : Q q = true) (hnq : P q = false) :
    ∀ r, q < r → cnt P r + 1 ≤ cnt Q r
  | 0 => fun h0 => by omega
  | k + 1 => fun hk => by
      simp only [cnt]
      by_cases hkq : q = k
      · subst hkq
        have := cnt_mono P Q h q
        simp [hq, hnq]; omega
      · have := cnt_lt P Q h q hq hnq k (by omega)
        by_cases hp : P k = true
        · simp [hp, h k hp]; omega
        · simp [hp]; split <;> omega

/-- Editing two adjacent positions of a predicate.

Consumer: `Leader/L3/Top/SettledWorkPotEdge.lean`. -/
theorem cnt_edit (P P' : Nat → Bool) (p : Nat) (h : ∀ j, j ≠ p → j ≠ p + 1 → P' j = P j) :
    ∀ k, p + 2 ≤ k → cnt P' k + (if P p then 1 else 0) + (if P (p + 1) then 1 else 0) =
      cnt P k + (if P' p then 1 else 0) + (if P' (p + 1) then 1 else 0) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro hk
      by_cases hk2 : p + 2 ≤ k
      · have := ih hk2
        simp only [cnt]
        rw [h k (by omega) (by omega)]
        omega
      · have hkk : k = p + 1 := by omega
        subst hkk
        have hc : cnt P' p = cnt P p := by
          have : ∀ m, m ≤ p → cnt P' m = cnt P m := by
            intro m
            induction m with
            | zero => intro _; rfl
            | succ m ihm =>
                intro hm
                simp only [cnt]
                rw [ihm (by omega), h m (by omega) (by omega)]
          exact this p (Nat.le_refl _)
        simp only [cnt]
        rw [hc]
        omega

/-- Editing one position of a predicate.

Consumer: `Leader/L3/Top/SettledWorkPotEdge.lean`. -/
theorem cnt_edit_one (P P' : Nat → Bool) (p : Nat) (h : ∀ j, j ≠ p → P' j = P j) :
    ∀ k, p + 1 ≤ k → cnt P' k + (if P p then 1 else 0) =
      cnt P k + (if P' p then 1 else 0) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro hk
      by_cases hk2 : p + 1 ≤ k
      · have := ih hk2
        simp only [cnt]
        rw [h k (by omega)]
        omega
      · have hkk : k = p := by omega
        subst hkk
        have hc : cnt P' k = cnt P k := by
          have : ∀ m, m ≤ k → cnt P' m = cnt P m := by
            intro m
            induction m with
            | zero => intro _; rfl
            | succ m ihm =>
                intro hm
                simp only [cnt]
                rw [ihm (by omega), h m (by omega)]
          exact this k (Nat.le_refl _)
        simp only [cnt]
        rw [hc]
        omega

/-- Front indicator of a cell.

Consumer: `pair_front`. -/
def fr (c : Cell) : Nat := if c.i = .x then 1 else 0

/-- One edge creates at most one front, and only from a non-border settled tail.

Consumer: `Leader/L3/Top/SettledWorkPotEdge.lean`. -/
theorem pair_front (b t : Bool) (x y : Cell) (hx : x.c ≠ .off → x.i = .e)
    (hy : y.c ≠ .off → y.i = .e) (hbt : b = true → t = false) :
    fr (pair b t x y).1 + (if t = false then fr (pair b t x y).2 else 0) ≤ fr x + fr y +
      (if x.i = .st ∧ x.c = .off ∧ b = false then 1 else 0) := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  cases xi <;> cases xc <;> cases yi <;> cases yc <;> cases b <;> cases t <;>
    simp (config := { decide := true }) [pair, inSlots, carries, fr, Inp.isP, Inp.isS]
      at hx hy hbt ⊢

end MarkedCells
end L3
