import Leader.L3.DensityTail

/-!
# T21 steps 1 and 2: the clean cohort grid tail and its block charge

Pure natural-number arithmetic over the literal uniform scheduler words
(`LeaderCountDyadicTail.wordSum`). No real numbers, exponentials or logarithms.

* The clean grid. A state `lam : Nat → Nat` lists, for each row `i` (a packet), how many
  of its `C` cells (hops) are complete. Row `i` is *ready* when `lam i < C` and either `i = 0`
  or `lam i < lam (i - 1)` (a hop waits for the same packet's previous hop and the preceding
  packet's corresponding hop). Each cell `(i, j)` carries a fixed scheduler letter
  `letter i j`. Drawing letter `e` completes every ready row whose current cell carries `e`.
  No down-closed invariant is needed: the dynamics and the bounds hold for every `lam`, in
  particular for every residual ideal.
* The potential. `pathWeight a b` is `2^(a+b+1)` times the number of monotone lattice paths
  with `a` down and `b` right steps; `gridPotential` sums it over the ready cells. One letter
  multiplies the potential by at most `1 - 1/(2n)` on average (`gridPotentialSuper`), which is
  the Nat form of `E[e^{W/(2n)}] ≤ 2` summed over paths.
* The tail. `2^M * miss ≤ (2n-1)^M * potential` (`potentialTail`). On an `r × r` grid at
  `M = 12 n r` this gives `8 * 4^r * miss ≤ r * n^M`, so the miss mass is at most `1/8`.
* Step 1. `costNumerator_of_block` with `B = 12 n r`, quarter miss: cost `≤ 16 n r`, i.e. the
  charged form `2 * cost ≤ n^T * (32 n r)` consumed by the T20 clocks, also on a closed class.
-/

namespace L3.CohortTail

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree
open LeaderCountDyadicTail
open K2ArbitraryElimination.FiniteAccounting

/-! ## Finite row sums -/

/-- `rowSum f k = f 0 + ... + f (k - 1)`. -/
def rowSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => rowSum f k + f k

theorem rowSum_le (f g : Nat → Nat) (k : Nat) (h : ∀ i, i < k → f i ≤ g i) :
    rowSum f k ≤ rowSum g k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    exact Nat.add_le_add (ih (fun i hi => h i (by omega))) (h k (by omega))

theorem rowSum_add (f g : Nat → Nat) (k : Nat) :
    rowSum (fun i => f i + g i) k = rowSum f k + rowSum g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show rowSum (fun i => f i + g i) k + (f k + g k) = (rowSum f k + f k) + (rowSum g k + g k)
    rw [ih]
    omega

theorem rowSum_mul (a : Nat) (f : Nat → Nat) (k : Nat) :
    rowSum (fun i => a * f i) k = a * rowSum f k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show rowSum (fun i => a * f i) k + a * f k = a * (rowSum f k + f k)
    rw [ih, Nat.mul_add]

theorem rowSum_const (c k : Nat) : rowSum (fun _ => c) k = k * c := by
  induction k with
  | zero => simp [rowSum]
  | succ k ih =>
    show rowSum (fun _ => c) k + c = (k + 1) * c
    rw [ih, Nat.succ_mul]

theorem rowSum_shift (f : Nat → Nat) (k : Nat) :
    rowSum (fun i => if i = 0 then 0 else f (i - 1)) (k + 1) = rowSum f k := by
  induction k with
  | zero => simp [rowSum]
  | succ k ih =>
    show rowSum (fun i => if i = 0 then 0 else f (i - 1)) (k + 1) +
        (if k + 1 = 0 then 0 else f (k + 1 - 1)) = rowSum f k + f k
    rw [ih]
    simp

theorem rowSum_shift_le (f : Nat → Nat) (k : Nat) :
    rowSum (fun i => if i = 0 then 0 else f (i - 1)) k ≤ rowSum f k := by
  cases k with
  | zero => exact Nat.le_refl _
  | succ k =>
    rw [rowSum_shift]
    exact Nat.le_add_right _ _

/-- Summing over scheduler letters commutes with summing over rows. -/
theorem ofFn_rowSum {n : Nat} (g : Fin n → Nat → Nat) (k : Nat) :
    (List.ofFn (fun e => rowSum (g e) k)).sum =
      rowSum (fun i => (List.ofFn (fun e => g e i)).sum) k := by
  induction k with
  | zero =>
    show (List.ofFn (fun _ : Fin n => 0)).sum = 0
    rw [ofFn_sum_const, Nat.mul_zero]
  | succ k ih =>
    show (List.ofFn (fun e => rowSum (g e) k + g e k)).sum =
      rowSum (fun i => (List.ofFn (fun e => g e i)).sum) k + (List.ofFn (fun e => g e k)).sum
    rw [ofFn_sum_add, ih]

/-- Exactly one scheduler letter equals a given letter. -/
theorem ofFn_sum_indicator {n : Nat} (a : Fin n) (x : Nat) :
    (List.ofFn (fun e : Fin n => if a = e then x else 0)).sum = x := by
  induction n with
  | zero => exact a.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.sum_cons]
    cases a using Fin.cases with
    | zero =>
      have h : ∀ i : Fin n, (if (0 : Fin (n + 1)) = i.succ then x else 0) = 0 := by
        intro i
        rw [if_neg (fun h => Fin.succ_ne_zero i h.symm)]
      rw [if_pos rfl, ofFn_sum_eq _ (fun _ => 0) h, ofFn_sum_const, Nat.mul_zero, Nat.add_zero]
    | succ a =>
      rw [if_neg (Fin.succ_ne_zero a), Nat.zero_add]
      rw [ofFn_sum_eq _ (fun e : Fin n => if a = e then x else 0)
        (fun i => by simp only [Fin.succ_inj])]
      exact ih a

/-! ## Path weights -/

/-- `pathWeight a b = 2^(a+b+1) * #(monotone paths with a down and b right steps)`. -/
def pathWeight : Nat → Nat → Nat
  | 0, 0 => 2
  | a + 1, 0 => 2 * pathWeight a 0
  | 0, b + 1 => 2 * pathWeight 0 b
  | a + 1, b + 1 => 2 * (pathWeight a (b + 1) + pathWeight (a + 1) b)

theorem pathWeight_two (a b : Nat) : 2 ≤ pathWeight a b := by
  induction a generalizing b with
  | zero =>
    induction b with
    | zero => simp [pathWeight]
    | succ b ih => simp only [pathWeight]; omega
  | succ a iha =>
    induction b with
    | zero => have := iha 0; simp only [pathWeight]; omega
    | succ b ihb => have := iha (b + 1); simp only [pathWeight]; omega

/-- At most `2^(a+b)` monotone paths (`4^(r-1)` on the `r × r` grid), each weighted by
`2^(a+b+1)`. -/
theorem pathWeight_le (a b : Nat) : pathWeight a b ≤ 2 ^ (2 * (a + b) + 1) := by
  induction a generalizing b with
  | zero =>
    induction b with
    | zero => simp [pathWeight]
    | succ b ih =>
      simp only [pathWeight]
      have e : 2 * (0 + (b + 1)) + 1 = (2 * (0 + b) + 1) + 2 := by omega
      rw [e, Nat.pow_add]
      omega
  | succ a iha =>
    induction b with
    | zero =>
      have h := iha 0
      simp only [pathWeight]
      have e : 2 * (a + 1 + 0) + 1 = (2 * (a + 0) + 1) + 2 := by omega
      rw [e, Nat.pow_add]
      omega
    | succ b ihb =>
      have h := iha (b + 1)
      simp only [pathWeight]
      have e1 : a + 1 + b = a + (b + 1) := by omega
      have e2 : 2 * (a + 1 + (b + 1)) + 1 = (2 * (a + (b + 1)) + 1) + 2 := by omega
      rw [e1] at ihb
      rw [e2, Nat.pow_add]
      omega

/-- The weight of cell `(i, j)` in an `R × C` grid (zero outside). -/
def cellWeight (R C i j : Nat) : Nat :=
  if i < R ∧ j < C then pathWeight (R - 1 - i) (C - 1 - j) else 0

/-- A cell's weight pays twice the weights of its two successors. -/
theorem cellWeight_split (R C i j : Nat) (hi : i < R) (hj : j < C) :
    2 * (cellWeight R C i (j + 1) + cellWeight R C (i + 1) j) ≤ cellWeight R C i j := by
  unfold cellWeight
  rw [if_pos (⟨hi, hj⟩ : i < R ∧ j < C)]
  by_cases hj' : j + 1 < C <;> by_cases hi' : i + 1 < R
  · rw [if_pos (⟨hi, hj'⟩ : i < R ∧ j + 1 < C), if_pos (⟨hi', hj⟩ : i + 1 < R ∧ j < C)]
    have e1 : R - 1 - i = (R - 1 - (i + 1)) + 1 := by omega
    have e2 : C - 1 - j = (C - 1 - (j + 1)) + 1 := by omega
    rw [e1, e2]
    generalize R - 1 - (i + 1) = a
    generalize C - 1 - (j + 1) = b
    simp only [pathWeight]
    omega
  · rw [if_pos (⟨hi, hj'⟩ : i < R ∧ j + 1 < C),
      if_neg (fun h : i + 1 < R ∧ j < C => hi' h.1)]
    have e1 : R - 1 - i = 0 := by omega
    have e2 : C - 1 - j = (C - 1 - (j + 1)) + 1 := by omega
    rw [e1, e2]
    generalize C - 1 - (j + 1) = b
    simp only [pathWeight]
    omega
  · rw [if_neg (fun h : i < R ∧ j + 1 < C => hj' h.2),
      if_pos (⟨hi', hj⟩ : i + 1 < R ∧ j < C)]
    have e1 : R - 1 - i = (R - 1 - (i + 1)) + 1 := by omega
    have e2 : C - 1 - j = 0 := by omega
    rw [e1, e2]
    generalize R - 1 - (i + 1) = a
    simp only [pathWeight]
    omega
  · rw [if_neg (fun h : i < R ∧ j + 1 < C => hj' h.2),
      if_neg (fun h : i + 1 < R ∧ j < C => hi' h.1)]
    have e1 : R - 1 - i = 0 := by omega
    have e2 : C - 1 - j = 0 := by omega
    rw [e1, e2]
    simp [pathWeight]

theorem cellWeight_le (R C i j : Nat) : 8 * cellWeight R C i j ≤ 2 ^ (2 * (R + C)) := by
  unfold cellWeight
  split
  · rename_i h
    have hp := pathWeight_le (R - 1 - i) (C - 1 - j)
    have hexp : 2 * (R - 1 - i + (C - 1 - j)) + 1 + 3 ≤ 2 * (R + C) := by omega
    calc
      8 * pathWeight (R - 1 - i) (C - 1 - j) ≤ 8 * 2 ^ (2 * (R - 1 - i + (C - 1 - j)) + 1) :=
        Nat.mul_le_mul_left 8 hp
      _ = 2 ^ (2 * (R - 1 - i + (C - 1 - j)) + 1 + 3) := by
        rw [Nat.pow_add 2 _ 3]
        exact Nat.mul_comm _ _
      _ ≤ 2 ^ (2 * (R + C)) := Nat.pow_le_pow_right (by decide) hexp
  · simp

/-! ## The clean grid process -/

/-- Row `i` can complete its next cell. -/
abbrev gridReady (C : Nat) (lam : Nat → Nat) (i : Nat) : Prop :=
  lam i < C ∧ (i = 0 ∨ lam i < lam (i - 1))

/-- One scheduler letter completes every ready row whose current cell carries that letter. -/
def gridStep {n : Nat} (C : Nat) (letter : Nat → Nat → Fin n) (lam : Nat → Nat)
    (e : Fin n) : Nat → Nat :=
  fun i => if gridReady C lam i ∧ letter i (lam i) = e then lam i + 1 else lam i

/-- Every cell of the `R × C` grid is complete. -/
def gridDone (R C : Nat) (lam : Nat → Nat) : Prop := ∀ i, i < R → C ≤ lam i

def gridTerm (R C : Nat) (lam : Nat → Nat) (i : Nat) : Nat :=
  if gridReady C lam i then cellWeight R C i (lam i) else 0

/-- Sum of the path weights from the ready cells. -/
def gridPotential (R C : Nat) (lam : Nat → Nat) : Nat := rowSum (gridTerm R C lam) R

/-- Weight of the ready cells completed by letter `e`. -/
def gridCharge {n : Nat} (R C : Nat) (letter : Nat → Nat → Fin n) (lam : Nat → Nat)
    (e : Fin n) (i : Nat) : Nat :=
  if gridReady C lam i ∧ letter i (lam i) = e then cellWeight R C i (lam i) else 0

def gridKeep {n : Nat} (R C : Nat) (letter : Nat → Nat → Fin n) (lam : Nat → Nat)
    (e : Fin n) (i : Nat) : Nat :=
  if gridReady C lam i ∧ letter i (lam i) = e then 2 * cellWeight R C i (lam i + 1)
  else 2 * gridTerm R C lam i

def gridFlow {n : Nat} (R C : Nat) (letter : Nat → Nat → Fin n) (lam : Nat → Nat)
    (e : Fin n) (i : Nat) : Nat :=
  if gridReady C lam i ∧ letter i (lam i) = e then 2 * cellWeight R C (i + 1) (lam i) else 0

theorem gridStep_ge {n : Nat} (C : Nat) (letter : Nat → Nat → Fin n) (lam : Nat → Nat)
    (e : Fin n) (i : Nat) : lam i ≤ gridStep C letter lam e i := by
  unfold gridStep
  split <;> omega

theorem gridDone_closed {n : Nat} (R C : Nat) (letter : Nat → Nat → Fin n) :
    ∀ lam e, gridDone R C lam → gridDone R C (gridStep C letter lam e) := by
  intro lam e h i hi
  exact Nat.le_trans (h i hi) (gridStep_ge C letter lam e i)

theorem gridTerm_le (R C : Nat) (lam : Nat → Nat) (i : Nat) :
    gridTerm R C lam i ≤ cellWeight R C i (lam i) := by
  unfold gridTerm
  split <;> omega

/-- One row after one letter: it keeps its weight, moves right, or is released by the
row ahead (which then pays through its down successor). -/
theorem gridRow_bound {n : Nat} (R C : Nat) (letter : Nat → Nat → Fin n)
    (lam : Nat → Nat) (e : Fin n) (i : Nat) :
    2 * gridTerm R C (gridStep C letter lam e) i ≤
      gridKeep R C letter lam e i +
        (if i = 0 then 0 else gridFlow R C letter lam e (i - 1)) := by
  have hstep : ∀ k, gridStep C letter lam e k =
      if gridReady C lam k ∧ letter k (lam k) = e then lam k + 1 else lam k := fun _ => rfl
  have hle := gridTerm_le R C (gridStep C letter lam e) i
  by_cases hc : gridReady C lam i ∧ letter i (lam i) = e
  · have h1 : gridStep C letter lam e i = lam i + 1 := by rw [hstep, if_pos hc]
    unfold gridKeep
    rw [if_pos hc]
    rw [h1] at hle
    omega
  · have h1 : gridStep C letter lam e i = lam i := by rw [hstep, if_neg hc]
    unfold gridKeep
    rw [if_neg hc]
    rw [h1] at hle
    by_cases hr : gridReady C lam i
    · have : gridTerm R C lam i = cellWeight R C i (lam i) := by
        unfold gridTerm; rw [if_pos hr]
      omega
    · by_cases hr' : gridReady C (gridStep C letter lam e) i
      · obtain ⟨hlt, hor⟩ := hr'
        rw [h1] at hlt
        have hi0 : i ≠ 0 := by
          intro h0
          exact hr ⟨hlt, Or.inl h0⟩
        have hnot : ¬ lam i < lam (i - 1) := fun h => hr ⟨hlt, Or.inr h⟩
        have hgt : lam i < gridStep C letter lam e (i - 1) := by
          rcases hor with h0 | h
          · exact absurd h0 hi0
          · rw [h1] at h; exact h
        by_cases hck : gridReady C lam (i - 1) ∧ letter (i - 1) (lam (i - 1)) = e
        · have h2 : gridStep C letter lam e (i - 1) = lam (i - 1) + 1 := by
            rw [hstep, if_pos hck]
          have heq : lam (i - 1) = lam i := by omega
          have hsucc : i - 1 + 1 = i := by omega
          rw [if_neg hi0]
          unfold gridFlow
          rw [if_pos hck, hsucc, heq]
          omega
        · have h2 : gridStep C letter lam e (i - 1) = lam (i - 1) := by
            rw [hstep, if_neg hck]
          omega
      · have : gridTerm R C (gridStep C letter lam e) i = 0 := by
          unfold gridTerm; rw [if_neg hr']
        omega

/-- One letter: the new doubled potential plus the completed weight is at most the old
doubled potential. -/
theorem gridPotential_step {n : Nat} (R C : Nat) (letter : Nat → Nat → Fin n)
    (lam : Nat → Nat) (e : Fin n) :
    2 * gridPotential R C (gridStep C letter lam e) + rowSum (gridCharge R C letter lam e) R ≤
      2 * gridPotential R C lam := by
  have hA : rowSum (fun i => 2 * gridTerm R C (gridStep C letter lam e) i) R ≤
      rowSum (fun i => gridKeep R C letter lam e i +
        (if i = 0 then 0 else gridFlow R C letter lam e (i - 1))) R :=
    rowSum_le _ _ R (fun i _ => gridRow_bound R C letter lam e i)
  have hBD : rowSum (fun i => (gridKeep R C letter lam e i + gridFlow R C letter lam e i) +
      gridCharge R C letter lam e i) R ≤ rowSum (fun i => 2 * gridTerm R C lam i) R := by
    apply rowSum_le
    intro i hi
    unfold gridKeep gridFlow gridCharge
    by_cases hc : gridReady C lam i ∧ letter i (lam i) = e
    · rw [if_pos hc, if_pos hc, if_pos hc]
      have hs := cellWeight_split R C i (lam i) hi hc.1.1
      have ht : gridTerm R C lam i = cellWeight R C i (lam i) := by
        unfold gridTerm; rw [if_pos hc.1]
      omega
    · rw [if_neg hc, if_neg hc, if_neg hc]
      omega
  rw [rowSum_add] at hA
  rw [rowSum_add, rowSum_add] at hBD
  have hsh := rowSum_shift_le (gridFlow R C letter lam e) R
  rw [rowSum_mul] at hA hBD
  unfold gridPotential
  omega

/-- Summed over all letters: the potential contracts by `1 - 1/(2n)` on average. -/
theorem gridPotentialSuper {n : Nat} (R C : Nat) (letter : Nat → Nat → Fin n)
    (lam : Nat → Nat) :
    2 * (List.ofFn (fun e : Fin n => gridPotential R C (gridStep C letter lam e))).sum ≤
      (2 * n - 1) * gridPotential R C lam := by
  have h1 := ofFn_sum_le
    (fun e : Fin n => 2 * gridPotential R C (gridStep C letter lam e) +
      rowSum (gridCharge R C letter lam e) R)
    (fun _ => 2 * gridPotential R C lam)
    (fun e => gridPotential_step R C letter lam e)
  rw [ofFn_sum_add, ofFn_sum_const, ofFn_sum_mul_left] at h1
  have h2 : (List.ofFn (fun e : Fin n => rowSum (gridCharge R C letter lam e) R)).sum =
      gridPotential R C lam := by
    rw [ofFn_rowSum]
    unfold gridPotential
    congr 1
    funext i
    unfold gridCharge gridTerm
    by_cases hr : gridReady C lam i
    · rw [if_pos hr]
      rw [ofFn_sum_eq _ (fun e : Fin n => if letter i (lam i) = e then cellWeight R C i (lam i)
        else 0) (fun e => by
          by_cases he : letter i (lam i) = e
          · rw [if_pos ⟨hr, he⟩, if_pos he]
          · rw [if_neg (fun h => he h.2), if_neg he])]
      exact ofFn_sum_indicator _ _
    · rw [if_neg hr]
      rw [ofFn_sum_eq _ (fun _ => 0) (fun e => by rw [if_neg (fun h => hr h.1)]),
        ofFn_sum_const, Nat.mul_zero]
  rw [h2] at h1
  have e : (2 * n - 1) * gridPotential R C lam =
      n * (2 * gridPotential R C lam) - gridPotential R C lam := by
    rw [Nat.sub_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_left_comm n 2]
  rw [e]
  omega

/-! ## The dyadic tail from a contracting potential -/

/-- If a potential dominates the miss weight and contracts by `1 - 1/(2n)` on average at
every letter, then `2^M * miss ≤ (2n-1)^M * potential`. This is the Nat form of
`P(miss) ≤ (1 - 1/(2n))^M * potential`. -/
theorem potentialTail {S : Type} {n : Nat} (step : S → Fin n → S) (P : S → Prop)
    (hclosed : ∀ x e, P x → P (step x e)) (Φ w : S → Nat)
    (hsuper : ∀ x, P x → 2 * (List.ofFn (fun e => Φ (step x e))).sum ≤ (2 * n - 1) * Φ x)
    (hw : ∀ x, P x → w x ≤ Φ x) :
    ∀ M x, P x → 2 ^ M * wordSum step w x M ≤ (2 * n - 1) ^ M * Φ x := by
  intro M
  induction M with
  | zero => intro x hx; simpa using hw x hx
  | succ M ih =>
    intro x hx
    rw [wordSum_succ]
    calc
      2 ^ (M + 1) * (List.ofFn fun e => wordSum step w (step x e) M).sum
          = 2 * (List.ofFn fun e => 2 ^ M * wordSum step w (step x e) M).sum := by
            rw [ofFn_sum_mul_left, Nat.pow_succ]; ac_rfl
      _ ≤ 2 * (List.ofFn fun e => (2 * n - 1) ^ M * Φ (step x e)).sum :=
          Nat.mul_le_mul_left 2
            (ofFn_sum_le _ _ (fun e => ih (step x e) (hclosed x e hx)))
      _ = (2 * n - 1) ^ M * (2 * (List.ofFn fun e => Φ (step x e)).sum) := by
          rw [ofFn_sum_mul_left]; ac_rfl
      _ ≤ (2 * n - 1) ^ M * ((2 * n - 1) * Φ x) :=
          Nat.mul_le_mul_left _ (hsuper x hx)
      _ = (2 * n - 1) ^ (M + 1) * Φ x := by rw [Nat.pow_succ]; ac_rfl

/-- `(1 - 1/(2n))^(2n) ≤ 1/2`, cleared of denominators (from the existing Bernoulli lemma). -/
theorem halfLifeTwice (n : Nat) (hn : 0 < n) : 2 * (2 * n - 1) ^ (2 * n) ≤ (2 * n) ^ (2 * n) :=
  integer_half_life (2 * n) (by omega)

/-- `q` half-lives: `2^q * (2n-1)^(2nq) ≤ (2n)^(2nq)`. -/
theorem halfLifePow (n q : Nat) (hn : 0 < n) :
    2 ^ q * (2 * n - 1) ^ (2 * n * q) ≤ (2 * n) ^ (2 * n * q) := by
  have h := Nat.pow_le_pow_left (halfLifeTwice n hn) q
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at h
  exact h

/-! ## The grid tail -/

theorem gridTerm_prefix (R C : Nat) (lam : Nat → Nat) :
    ∀ k, k ≤ R → (∃ i, i < k ∧ lam i < C) → 1 ≤ rowSum (gridTerm R C lam) k := by
  intro k
  induction k with
  | zero => intro _ hex; obtain ⟨i, hi, _⟩ := hex; omega
  | succ k ih =>
    intro hk hex
    show 1 ≤ rowSum (gridTerm R C lam) k + gridTerm R C lam k
    by_cases h : ∃ i, i < k ∧ lam i < C
    · have := ih (by omega) h
      omega
    · obtain ⟨i, hi, hl⟩ := hex
      have hik : i = k := by
        apply Classical.byContradiction
        intro hne
        exact h ⟨i, by omega, hl⟩
      rw [hik] at hl
      have hready : gridReady C lam k := by
        refine ⟨hl, ?_⟩
        by_cases h0 : k = 0
        · exact Or.inl h0
        · right
          have : ¬ lam (k - 1) < C := fun h' => h ⟨k - 1, by omega, h'⟩
          omega
      have hw : 1 ≤ gridTerm R C lam k := by
        unfold gridTerm
        rw [if_pos hready]
        unfold cellWeight
        rw [if_pos (⟨by omega, hl⟩ : k < R ∧ lam k < C)]
        exact Nat.le_trans (by decide) (pathWeight_two _ _)
      omega

/-- The miss indicator is below the potential. -/
theorem gridMiss_le (R C : Nat) (lam : Nat → Nat) :
    miss (gridDone R C) lam ≤ gridPotential R C lam := by
  classical
  by_cases hd : gridDone R C lam
  · simp [miss, hd]
  · have hex : ∃ i, i < R ∧ lam i < C := by
      apply Classical.byContradiction
      intro hne
      apply hd
      intro i hi
      exact Nat.le_of_not_lt (fun h => hne ⟨i, hi, h⟩)
    have := gridTerm_prefix R C lam R (Nat.le_refl _) hex
    simp only [miss, if_neg hd]
    exact this

theorem gridPotential_le (R C : Nat) (lam : Nat → Nat) :
    8 * gridPotential R C lam ≤ R * 2 ^ (2 * (R + C)) := by
  unfold gridPotential
  rw [← rowSum_mul, ← rowSum_const]
  apply rowSum_le
  intro i _
  exact Nat.le_trans (Nat.mul_le_mul_left 8 (gridTerm_le R C lam i)) (cellWeight_le R C i _)

/-- The grid dyadic tail: `2^M * P(not done after M letters) ≤ (2n-1)^M * potential`,
from every state (in particular every residual ideal). -/
theorem gridTail {n : Nat} (R C : Nat) (letter : Nat → Nat → Fin n) (M : Nat)
    (lam : Nat → Nat) :
    2 ^ M * wordSum (gridStep C letter) (miss (gridDone R C)) lam M ≤
      (2 * n - 1) ^ M * gridPotential R C lam :=
  potentialTail (gridStep C letter) (fun _ => True) (fun _ _ _ => True.intro)
    (gridPotential R C) (miss (gridDone R C))
    (fun lam _ => gridPotentialSuper R C letter lam)
    (fun lam _ => gridMiss_le R C lam) M lam True.intro

/-- The dyadic binomial tail: a single chase of `L` letters `s 0, ..., s (L-1)` (a `1 × L`
grid). The chase advances exactly when its current letter is drawn, so the number of
advances in `M` letters is `Bin(M, 1/n)` until it stops at `L`; the count of words with
fewer than `L` advances satisfies `P(Bin(M,1/n) < L) ≤ 2^L (1 - 1/(2n))^M`. -/
theorem chaseTail {n : Nat} (L : Nat) (s : Nat → Fin n) (M : Nat) :
    2 ^ M * wordSum (gridStep L (fun _ j => s j)) (miss (gridDone 1 L)) (fun _ => 0) M ≤
      2 ^ L * (2 * n - 1) ^ M := by
  have h := gridTail 1 L (fun _ j => s j) M (fun _ => 0)
  have hp : gridPotential 1 L (fun _ => 0) ≤ 2 ^ L := by
    show 0 + gridTerm 1 L (fun _ => 0) 0 ≤ 2 ^ L
    have h1 := gridTerm_le 1 L (fun _ => 0) 0
    have h2 : cellWeight 1 L 0 0 ≤ 2 ^ L := by
      unfold cellWeight
      split
      · rename_i hL
        have hrow : ∀ b, pathWeight 0 b = 2 ^ (b + 1) := by
          intro b
          induction b with
          | zero => simp [pathWeight]
          | succ b ih => simp only [pathWeight, ih, Nat.pow_succ]; ac_rfl
        rw [hrow]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      · exact Nat.zero_le _
    omega
  calc
    _ ≤ (2 * n - 1) ^ M * gridPotential 1 L (fun _ => 0) := h
    _ ≤ (2 * n - 1) ^ M * 2 ^ L := Nat.mul_le_mul_left _ hp
    _ = 2 ^ L * (2 * n - 1) ^ M := Nat.mul_comm _ _

/-- The `r × r` grid at `M = 12 n r` letters, uniformly over residual ideals:
`P(miss) ≤ r / (8 * 4^r)`. -/
theorem gridSquareTail {n : Nat} (r : Nat) (letter : Nat → Nat → Fin n) (lam : Nat → Nat) :
    8 * 2 ^ (2 * r) * wordSum (gridStep r letter) (miss (gridDone r r)) lam (12 * n * r) ≤
      r * n ^ (12 * n * r) := by
  have hn : 0 < n := (letter 0 0).pos
  have hM : 12 * n * r = 2 * n * (6 * r) := by grind
  generalize hW : wordSum (gridStep r letter) (miss (gridDone r r)) lam (12 * n * r) = W
  have h1 := gridTail r r letter (12 * n * r) lam
  rw [hW] at h1
  have hq := halfLifePow n (6 * r) hn
  rw [← hM] at hq
  have hpot := gridPotential_le r r lam
  generalize gridPotential r r lam = Φ at h1 hpot
  have h2n : (2 * n) ^ (12 * n * r) = 2 ^ (12 * n * r) * n ^ (12 * n * r) := Nat.mul_pow _ _ _
  rw [h2n] at hq
  have hA : 0 < 2 ^ (12 * n * r) := Nat.two_pow_pos _
  generalize 2 ^ (12 * n * r) = A at h1 hq hA
  generalize n ^ (12 * n * r) = N at hq ⊢
  generalize (2 * n - 1) ^ (12 * n * r) = D at h1 hq
  have hX : A * (2 ^ (6 * r) * W) ≤ A * (N * Φ) :=
    calc
      A * (2 ^ (6 * r) * W) = 2 ^ (6 * r) * (A * W) := Nat.mul_left_comm _ _ _
      _ ≤ 2 ^ (6 * r) * (D * Φ) := Nat.mul_le_mul_left _ h1
      _ = (2 ^ (6 * r) * D) * Φ := (Nat.mul_assoc _ _ _).symm
      _ ≤ (A * N) * Φ := Nat.mul_le_mul_right _ hq
      _ = A * (N * Φ) := Nat.mul_assoc _ _ _
  have hY := Nat.le_of_mul_le_mul_left hX hA
  have hZ : 2 ^ (4 * r) * (8 * 2 ^ (2 * r) * W) ≤ 2 ^ (4 * r) * (r * N) :=
    calc
      2 ^ (4 * r) * (8 * 2 ^ (2 * r) * W) = 8 * (2 ^ (4 * r + 2 * r) * W) := by
        rw [Nat.pow_add]; ac_rfl
      _ = 8 * (2 ^ (6 * r) * W) := by rw [show 4 * r + 2 * r = 6 * r by omega]
      _ ≤ 8 * (N * Φ) := Nat.mul_le_mul_left 8 hY
      _ = N * (8 * Φ) := Nat.mul_left_comm _ _ _
      _ ≤ N * (r * 2 ^ (2 * (r + r))) := Nat.mul_le_mul_left N hpot
      _ = 2 ^ (4 * r) * (r * N) := by
        rw [show 2 * (r + r) = 4 * r by omega]; ac_rfl
  exact Nat.le_of_mul_le_mul_left hZ (Nat.two_pow_pos _)

/-- The miss mass of the `r × r` grid at `M = 12 n r` is at most `1/8`, hence at most `1/4`,
uniformly over residual ideals. -/
theorem gridSquareQuarter {n : Nat} (r : Nat) (letter : Nat → Nat → Fin n) (lam : Nat → Nat) :
    4 * wordSum (gridStep r letter) (miss (gridDone r r)) lam (12 * n * r) ≤
      n ^ (12 * n * r) := by
  have h := gridSquareTail r letter lam
  have hr : r ≤ 2 ^ (2 * r) :=
    Nat.le_trans (Nat.le_of_lt Nat.lt_two_pow_self)
      (Nat.pow_le_pow_right (by decide) (by omega))
  generalize wordSum (gridStep r letter) (miss (gridDone r r)) lam (12 * n * r) = W at h ⊢
  generalize n ^ (12 * n * r) = N at h ⊢
  have h' : 2 ^ (2 * r) * (8 * W) ≤ 2 ^ (2 * r) * N :=
    calc
      2 ^ (2 * r) * (8 * W) = 8 * 2 ^ (2 * r) * W := by ac_rfl
      _ ≤ r * N := h
      _ ≤ 2 ^ (2 * r) * N := Nat.mul_le_mul_right N hr
  have := Nat.le_of_mul_le_mul_left h' (Nat.two_pow_pos _)
  omega

/-! ## Step 1: the block restart at `B = 12 n r` -/

theorem cohortRenewalCeiling (n r : Nat) :
    L3.Prob.renewalCeiling (12 * n * r) 1 4 = 16 * n * r := by
  have he : (12 * n * r) * 4 = (16 * n * r) * 3 := by grind
  simp only [L3.Prob.renewalCeiling, L3.Prob.ceilNat]
  rw [he]
  simp

/-- Step 1: a uniform quarter block-miss bound at `B = 12 n r` with a closed target gives
expected cost at most `16 n r`. -/
theorem cohortBlockCost {S : Type} {n : Nat} (next : S → Fin n → S) (Good : S → Prop)
    (r : Nat) (hn : 0 < n) (hr : 0 < r)
    (hc : ∀ x e, Good x → Good (next x e))
    (hb : ∀ x, 4 * wordSum next (miss Good) x (12 * n * r) ≤ n ^ (12 * n * r)) :
    ∀ x T, costNumerator next Good x T ≤ n ^ T * (16 * n * r) := by
  have hB : 0 < 12 * n * r := Nat.mul_pos (Nat.mul_pos (by decide) hn) hr
  intro x T
  have h := L3.Density.costNumerator_of_block next Good (12 * n * r) 1 4 hB (by decide) hc
    (fun y => by simpa only [Nat.one_mul] using hb y) x T
  rwa [cohortRenewalCeiling] at h

/-- Step 1 in the charged form consumed by the T20 clocks (`BankRepairDigitChargedStage`,
unfolded): `2 * cost ≤ n^T * (32 n r)`. -/
theorem cohortBlockCharge {S : Type} {n : Nat} (next : S → Fin n → S) (Good : S → Prop)
    (r : Nat) (hn : 0 < n) (hr : 0 < r)
    (hc : ∀ x e, Good x → Good (next x e))
    (hb : ∀ x, 4 * wordSum next (miss Good) x (12 * n * r) ≤ n ^ (12 * n * r)) :
    ∀ x T, 2 * costNumerator next Good x T ≤ n ^ T * (32 * n * r) := by
  intro x T
  have h := Nat.mul_le_mul_left 2 (cohortBlockCost next Good r hn hr hc hb x T)
  have e : 2 * (n ^ T * (16 * n * r)) = n ^ T * (32 * n * r) := by grind
  omega

/-! ### The same on a closed class -/

/-- The step restricted to a closed class. -/
def classNext {S : Type} {n : Nat} (next : S → Fin n → S) (P : S → Prop)
    (hcl : ∀ x e, P x → P (next x e)) (x : {x // P x}) (e : Fin n) : {x // P x} :=
  ⟨next x.1 e, hcl x.1 e x.2⟩

theorem classCost {S : Type} {n : Nat} (next : S → Fin n → S) (P Good : S → Prop)
    (hcl : ∀ x e, P x → P (next x e)) :
    ∀ T (x : {x // P x}), costNumerator (classNext next P hcl) (fun y => Good y.1) x T =
      costNumerator next Good x.1 T := by
  intro T
  induction T with
  | zero => intro x; rfl
  | succ T ih =>
    intro x
    by_cases hg : Good x.1
    · rw [costNumerator_terminal (classNext next P hcl) (fun y => Good y.1) x hg,
        costNumerator_terminal next Good x.1 hg]
    · rw [costNumerator_succ (classNext next P hcl) (fun y => Good y.1) x hg,
        costNumerator_succ next Good x.1 hg]
      congr 1
      exact ofFn_sum_eq _ _ (fun e => ih _)

theorem classMiss {S : Type} {n : Nat} (next : S → Fin n → S) (P Good : S → Prop)
    (hcl : ∀ x e, P x → P (next x e)) :
    ∀ T (x : {x // P x}), wordSum (classNext next P hcl) (miss (fun y => Good y.1)) x T =
      wordSum next (miss Good) x.1 T := by
  intro T
  induction T with
  | zero => intro x; rfl
  | succ T ih =>
    intro x
    rw [wordSum_succ, wordSum_succ]
    exact ofFn_sum_eq _ _ (fun e => ih _)

/-- Step 1 on a closed class `P` (the post-strict class in the application): a quarter
block-miss bound from every state of `P` gives the `32 n r` charge from every state of `P`. -/
theorem cohortClassCharge {S : Type} {n : Nat} (next : S → Fin n → S) (P Good : S → Prop)
    (r : Nat) (hn : 0 < n) (hr : 0 < r)
    (hcl : ∀ x e, P x → P (next x e))
    (hc : ∀ x e, Good x → Good (next x e))
    (hb : ∀ x, P x → 4 * wordSum next (miss Good) x (12 * n * r) ≤ n ^ (12 * n * r)) :
    ∀ x, P x → ∀ T, 2 * costNumerator next Good x T ≤ n ^ T * (32 * n * r) := by
  intro x hx T
  have h := cohortBlockCharge (classNext next P hcl) (fun y => Good y.1) r hn hr
    (fun y e hy => hc y.1 e hy)
    (fun y => by rw [classMiss]; exact hb y.1 y.2) ⟨x, hx⟩ T
  rwa [classCost] at h

/-- The clean `r × r` grid itself completes in expected time at most `16 n r`, from every
state (charged form: `2 * cost ≤ n^T * (32 n r)`). -/
theorem gridSquareCharge {n : Nat} (r : Nat) (hr : 0 < r) (letter : Nat → Nat → Fin n) :
    ∀ lam T, 2 * costNumerator (gridStep r letter) (gridDone r r) lam T ≤
      n ^ T * (32 * n * r) :=
  cohortBlockCharge (gridStep r letter) (gridDone r r) r (letter 0 0).pos hr
    (gridDone_closed r r letter) (fun lam => gridSquareQuarter r letter lam)

/-! ## Interface for step 3: domination of the clean grid -/

/-- Pointwise order on the first `R` rows. -/
def rowsLe (R : Nat) (lam mu : Nat → Nat) : Prop := ∀ i, i < R → lam i ≤ mu i

/-- The clean grid is monotone: a row vector that is ahead stays ahead after any letter. -/
theorem gridStep_mono {n : Nat} (R C : Nat) (letter : Nat → Nat → Fin n)
    (lam mu : Nat → Nat) (e : Fin n) (h : rowsLe R lam mu) :
    rowsLe R (gridStep C letter lam e) (gridStep C letter mu e) := by
  intro i hi
  have hge := gridStep_ge C letter mu e i
  have hlam : ∀ k, gridStep C letter lam e k =
      if gridReady C lam k ∧ letter k (lam k) = e then lam k + 1 else lam k := fun _ => rfl
  have hmu : ∀ k, gridStep C letter mu e k =
      if gridReady C mu k ∧ letter k (mu k) = e then mu k + 1 else mu k := fun _ => rfl
  have hle := h i hi
  by_cases hc : gridReady C lam i ∧ letter i (lam i) = e
  · rw [hlam, if_pos hc]
    by_cases heq : lam i = mu i
    · have hc' : gridReady C mu i ∧ letter i (mu i) = e := by
        obtain ⟨⟨hlt, hor⟩, hl⟩ := hc
        refine ⟨⟨by omega, ?_⟩, by rw [← heq]; exact hl⟩
        rcases hor with h0 | hp
        · exact Or.inl h0
        · right
          have := h (i - 1) (by omega)
          omega
      rw [hmu, if_pos hc']
      omega
    · omega
  · rw [hlam, if_neg hc]
    omega

theorem gridDone_mono (R C : Nat) (lam mu : Nat → Nat) (h : rowsLe R lam mu)
    (hd : gridDone R C lam) : gridDone R C mu :=
  fun i hi => Nat.le_trans (hd i hi) (h i hi)

/-- Domination transfer. Let `proj` read off, on a closed class `P`, how many hops of each
packet of the chosen cohort are complete. If every real letter advances `proj` at least as
far as the clean grid step (while the target is not reached), and a complete grid implies the
target, then the real miss mass is at most the clean grid miss mass from any row vector
below `proj x`. No independence is used: the two chains read the same letters. -/
theorem gridDominationMiss {S : Type} {n : Nat} (next : S → Fin n → S) (P Good : S → Prop)
    (hcl : ∀ x e, P x → P (next x e)) (hc : ∀ x e, Good x → Good (next x e))
    (R C : Nat) (letter : Nat → Nat → Fin n) (proj : S → Nat → Nat)
    (hdom : ∀ x e, P x → ¬ Good x →
      rowsLe R (gridStep C letter (proj x) e) (proj (next x e)))
    (hgood : ∀ x, P x → gridDone R C (proj x) → Good x) :
    ∀ M x lam, P x → rowsLe R lam (proj x) →
      wordSum next (miss Good) x M ≤
        wordSum (gridStep C letter) (miss (gridDone R C)) lam M := by
  classical
  intro M
  induction M with
  | zero =>
    intro x lam hx hle
    show miss Good x ≤ miss (gridDone R C) lam
    by_cases hd : gridDone R C lam
    · have hg := hgood x hx (gridDone_mono R C lam (proj x) hle hd)
      simp [miss, hg]
    · have := miss_le_one Good x
      simp only [miss, if_neg hd]
      exact this
  | succ M ih =>
    intro x lam hx hle
    by_cases hg : Good x
    · rw [miss_zero next Good hc x hg]
      exact Nat.zero_le _
    · rw [wordSum_succ, wordSum_succ]
      apply ofFn_sum_le
      intro e
      apply ih (next x e) (gridStep C letter lam e) (hcl x e hx)
      intro i hi
      exact Nat.le_trans (gridStep_mono R C letter lam (proj x) e hle i hi)
        (hdom x e hx hg i hi)

/-- Step 1 + step 2 + the domination interface: a cohort whose real projection dominates the
clean `r × r` grid on a closed class completes with charge `32 n r` (expected `16 n r`)
from every state of the class. -/
theorem gridDominationCharge {S : Type} {n : Nat} (next : S → Fin n → S) (P Good : S → Prop)
    (hcl : ∀ x e, P x → P (next x e)) (hc : ∀ x e, Good x → Good (next x e))
    (r : Nat) (hr : 0 < r) (letter : Nat → Nat → Fin n) (proj : S → Nat → Nat)
    (hdom : ∀ x e, P x → ¬ Good x →
      rowsLe r (gridStep r letter (proj x) e) (proj (next x e)))
    (hgood : ∀ x, P x → gridDone r r (proj x) → Good x) :
    ∀ x, P x → ∀ T, 2 * costNumerator next Good x T ≤ n ^ T * (32 * n * r) :=
  cohortClassCharge next P Good r (letter 0 0).pos hr hcl hc
    (fun x hx => Nat.le_trans
      (Nat.mul_le_mul_left 4 (gridDominationMiss next P Good hcl hc r r letter proj hdom hgood
        (12 * n * r) x (proj x) hx (fun _ _ => Nat.le_refl _)))
      (gridSquareQuarter r letter (proj x)))

end L3.CohortTail
