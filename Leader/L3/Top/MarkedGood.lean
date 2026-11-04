import Leader.L3.Top.MarkedRank
import Leader.L3.Top.MarkedInv

/-!
# Q7: rank zero is the coloured window; the rank is at most `4 r (r + 1)`

Consumer: `Leader/L3/Top/MarkedDebtRows.lean` (positivity row and start row of
`TopMarkedDebtRows`).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- Every pending input is strictly left of each settled input, front and carry.

Consumer: `rank_zero_coloured`. -/
def Barrier (r : Nat) (cells : Nat → Cell) : Prop :=
  ∀ i j, i < r → j < r → (cells i).i.isP = true → obC (cells j) = true → i < j

/-- Every live carry is the unique fresh one, with empty host and only `E`/`P` on its left.

Consumer: `rank_zero_coloured`. -/
def Gap (r : Nat) (cells : Nat → Cell) : Prop :=
  ∀ j, j < r → (cells j).c ≠ .off →
    (cells j).c = .fresh ∧ (cells j).i = .e ∧ (∀ i, i < j → EP (cells i)) ∧
      ∀ k, k < r → (cells k).c ≠ .off → k = j

/-- The obstacle flag stays set.

Consumer: `rank_zero_coloured`. -/
theorem scanFlags_true (cells : Nat → Cell) :
    ∀ k j ob vb, ob = true → (scanFlags cells k j ob vb).1 = true := by
  intro k
  induction k with
  | zero => intro j ob vb h; exact h
  | succ k ih =>
      intro j ob vb h
      exact ih _ _ _ (by simp only [nob, h, Bool.true_or])

/-- An obstacle before a register sets the obstacle flag there.

Consumer: `rank_zero_coloured`. -/
theorem scanFlags_obstacle (cells : Nat → Cell) :
    ∀ k j ob vb q, j ≤ q → q < j + k → obC (cells q) = true →
      (scanFlags cells k j ob vb).1 = true := by
  intro k
  induction k with
  | zero => intro j ob vb q h1 h2; omega
  | succ k ih =>
      intro j ob vb q h1 h2 h3
      by_cases hq : q = j
      · subst hq
        exact scanFlags_true cells k _ _ _ (by simp only [nob, h3, Bool.or_true])
      · exact ih (j + 1) _ _ q (by omega) (by omega) h3

/-- A zero scan has zero register weights.

Consumer: `rank_zero_coloured`. -/
theorem scan_zero_wt (r : Nat) (cells : Nat → Cell) :
    ∀ k j ob vb, scan r cells k j ob vb = 0 → ∀ i, i < k →
      wt r (j + i) (scanFlags cells i j ob vb).1 (scanFlags cells i j ob vb).2
        (cells (j + i)) = 0 := by
  intro k
  induction k with
  | zero => intro j ob vb _ i hi; omega
  | succ k ih =>
      intro j ob vb h i hi
      simp only [scan] at h
      have h1 : wt r j ob vb (cells j) = 0 := by omega
      have h2 : scan r cells k (j + 1) (nob ob (cells j)) (nvb ob vb (cells j)) = 0 := by
        omega
      cases i with
      | zero => simpa [scanFlags] using h1
      | succ i =>
          have := ih (j + 1) _ _ h2 i (by omega)
          have e : j + (i + 1) = j + 1 + i := by omega
          simp only [scanFlags, e]
          exact this

/-- A zero register weight means no violator and no inherited carry.

Consumer: `rank_zero_coloured`. -/
theorem wt_zero_facts (r j : Nat) (hj : j < r) (ob vb : Bool) (c : Cell)
    (h : wt r j ob vb c = 0) : violC ob c = false ∧ c.c ≠ .inh := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;> cases ob <;> cases vb <;>
    simp (config := { decide := true }) [wt, gateW, violC] at h ⊢ <;> omega

/-- Rank zero is the moving barrier.

Consumer: `rank_zero_coloured`. -/
theorem rank_zero_barrier (r : Nat) (cells : Nat → Cell) (h : rank r cells = 0) :
    Barrier r cells := by
  intro i j hi hj hP hobs
  have hz := scan_zero_wt r cells r 0 false false h i hi
  simp only [Nat.zero_add] at hz
  have hf := wt_zero_facts r i hi _ _ _ hz
  by_cases hij : i < j
  · exact hij
  · exfalso
    by_cases hji : j < i
    · have hflag := scanFlags_obstacle cells i 0 false false j (by omega) (by omega) hobs
      have := hf.1
      simp [violC, hP, hflag] at this
    · have hje : j = i := by omega
      subst hje
      have hne : (cells j).c ≠ .off := by
        intro hc
        rcases hcc : cells j with ⟨ci, cc⟩
        rw [hcc] at hP hobs hc
        simp only at hc
        subst hc
        cases ci <;> simp [obC, Inp.isP, Inp.isS] at hP hobs
      have := hf.1
      simp [violC, hP, hne] at this

/-- Rank zero with the invariants is the generated-carry gap.

Consumer: `rank_zero_coloured`. -/
theorem rank_zero_gap (r : Nat) (cells : Nat → Cell) (hinv : Inv r cells)
    (h : rank r cells = 0) : Gap r cells := by
  have hfresh : ∀ j, j < r → (cells j).c ≠ .off → (cells j).c = .fresh := by
    intro j hj hc
    have hz := scan_zero_wt r cells r 0 false false h j hj
    simp only [Nat.zero_add] at hz
    have hf := (wt_zero_facts r j hj _ _ _ hz).2
    cases hcc : (cells j).c <;> simp_all
  intro j hj hc
  have hf := hfresh j hj hc
  obtain ⟨hje, hleft⟩ := hinv.1 j hj hf
  exact ⟨hf, hje, hleft, fun k hk hkc => hinv.2 k j hk hj (hfresh k hk hkc) hf⟩

/-- A register weighs at most `4 r + 4`.

Consumer: `rank_zero_coloured`. -/
theorem wt_le (r j : Nat) (ob vb : Bool) (c : Cell) : wt r j ob vb c ≤ 4 * r + 4 := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;> cases ob <;> cases vb <;>
    simp (config := { decide := true }) [wt, gateW, violC] <;> omega

/-- A scan of `k` registers weighs at most `k (4 r + 4)`.

Consumer: `rank_zero_coloured`. -/
theorem scan_le (r : Nat) (cells : Nat → Cell) :
    ∀ k j ob vb, scan r cells k j ob vb ≤ k * (4 * r + 4) := by
  intro k
  induction k with
  | zero => intros; simp [scan]
  | succ k ih =>
      intro j ob vb
      have h1 := wt_le r j ob vb (cells j)
      have h2 := ih (j + 1) (nob ob (cells j)) (nvb ob vb (cells j))
      simp only [scan]
      rw [Nat.succ_mul]
      omega

/-- The rank is at most `r * (4 r + 4) = 4 r^2 + 4 r`.

Consumer: `rank_start_bound`. -/
theorem rank_le (r : Nat) (cells : Nat → Cell) : rank r cells ≤ r * (4 * r + 4) :=
  scan_le r cells r 0 false false

/-! ### No terminal reseed

Consumer: `rank_zero_coloured`. -/

theorem pair_y_settled (b : Bool) (x y : Cell)
    (h : (pair b false x y).2.i.isS = true) : y.i.isS = true := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  cases xi <;> cases xc <;> cases yi <;> cases yc <;> cases b <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, Inp.isP, Inp.isS] at h ⊢

/-- A terminal edge makes a settled input only from a settled or pending one.

Consumer: `rank_zero_coloured`. -/
theorem pair_term_settled (x y : Cell)
    (h : (pair false true x y).1.i.isS = true) :
    x.i.isS = true ∨ x.i.isP = true := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  cases xi <;> cases xc <;> cases yi <;> cases yc <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, Inp.isP, Inp.isS] at h ⊢

/-- With the barrier and a settled input anywhere, no edge makes a new settled input
at the terminal register.

Consumer: `rank_zero_coloured`. -/
theorem noReseed_abstract (r : Nat) (hr : 2 ≤ r) (cells cells' : Nat → Cell)
    (hbar : Barrier r cells) (hS : ∃ q, q < r ∧ (cells q).i.isS = true)
    (h : Step r cells cells') (hnew : (cells' (r - 1)).i.isS = true) :
    (cells (r - 1)).i.isS = true := by
  cases h with
  | frame => exact hnew
  | edge p hp =>
      by_cases h1 : r - 1 = p + 1
      · simp only [setTwo, h1, if_neg (show p + 1 ≠ p by omega), if_true] at hnew
        rw [h1]
        exact pair_y_settled _ _ _ hnew
      · have h2 : r - 1 ≠ p := by omega
        simpa [setTwo, h1, h2] using hnew
  | term =>
      simp only [setOne, if_true] at hnew
      rcases pair_term_settled _ _ hnew with h | h
      · exact h
      · exfalso
        obtain ⟨q, hq, hqs⟩ := hS
        have := hbar (r - 1) q (by omega) hq h (by
          simp [obC, hqs])
        omega
  | clean =>
      have : r - 1 ≠ 0 := by omega
      simpa [setOne, this] using hnew
  | accept t =>
      have : r - 1 ≠ 0 := by omega
      simpa [setOne, this] using hnew

end MarkedCells
end L3

#print axioms L3.MarkedCells.rank_zero_barrier
#print axioms L3.MarkedCells.rank_zero_gap
#print axioms L3.MarkedCells.rank_le
#print axioms L3.MarkedCells.noReseed_abstract
