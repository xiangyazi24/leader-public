import Leader.Wu.Birth.CheckChainWindowMass

set_option autoImplicit false

/-! # A light cone for pair-local ring steps

Cells `cell ring s k` for `lo ≤ k < hi` (with `1 ≤ lo` and `hi < n`) form an interval of the ring.  If two
configurations agree on the interval, then after one letter of a pair-local step they agree on the interval shrunk by
one cell at the left end when the letter is the edge entering it from the left, and by one cell at the right end
when the letter is the edge leaving its last cell (`step_interval`); along a word they agree on the interval shrunk
by the letters that hit the moving ends (`run_interval`).  The left end moves only through the ordered chain of
edges `cell (lo-1), cell lo, cell (lo+1), ...` (`leftReach`), so the number of words of length `T` in which the left
end advances by at least `g` cells is at most `binom T g * n^(T-g)` (`leftReach_count`), with
`binom T g * g! ≤ T^g` (`binom_mul_factorial_le`); symmetrically for the right end (`rightReach_count`). -/

namespace B6LightCone

open B6WindowLocality BirthCheckChainR1Ring BirthCheckChainR1Mass FixedSpanRenewalPayload FiniteUniformStoppingTree

variable {n : Nat} {X : Type}

/-- Interval update by one letter. -/
def shrink (ring : DirectedRing n) (s : Fin n) (p : Nat × Nat) (e : Fin n) : Nat × Nat :=
  (if e = cell ring s (p.1 - 1) then p.1 + 1 else p.1, if e = cell ring s (p.2 - 1) then p.2 - 1 else p.2)

theorem shrink_bounds (ring : DirectedRing n) (s : Fin n) (p : Nat × Nat) (e : Fin n) :
    p.1 ≤ (shrink ring s p e).1 ∧ (shrink ring s p e).2 ≤ p.2 := by
  simp only [shrink]
  constructor
  · split <;> omega
  · split <;> omega

theorem step_interval {step : (Fin n → X) → Fin n → (Fin n → X)} {ring : DirectedRing n} (hL : PairLocal ring step)
    (s : Fin n) (p : Nat × Nat) (hlo : 1 ≤ p.1) (hhi : p.2 < n) (C D : Fin n → X)
    (hCD : ∀ k, p.1 ≤ k → k < p.2 → C (cell ring s k) = D (cell ring s k)) (e : Fin n) :
    ∀ k, (shrink ring s p e).1 ≤ k → k < (shrink ring s p e).2 → step C e (cell ring s k) = step D e (cell ring s k) := by
  intro k hk1 hk2
  have hb := shrink_bounds ring s p e
  have hk1' : p.1 ≤ k := Nat.le_trans hb.1 hk1
  have hk2' : k < p.2 := Nat.lt_of_lt_of_le hk2 hb.2
  by_cases he : cell ring s k = e
  · -- k is the initiator; its responder is cell (k+1)
    have hr : ring.rightNeighbor e = cell ring s (k + 1) := by rw [← he, right_cell]
    by_cases hk3 : k + 1 < p.2
    · subst he
      have h1 := hCD k hk1' hk2'
      have h2 : D (ring.rightNeighbor (cell ring s k)) = C (ring.rightNeighbor (cell ring s k)) := by
        rw [hr]; exact (hCD (k + 1) (by omega) hk3).symm
      exact ((hL.pair C D (cell ring s k) h1.symm h2).1).symm
    · exfalso
      have hk4 : k + 1 = p.2 := by omega
      have hE : e = cell ring s (p.2 - 1) := by rw [← he, show p.2 - 1 = k by omega]
      unfold shrink at hk2
      simp only [hE, if_true] at hk2
      omega
  · by_cases hr : cell ring s k = ring.rightNeighbor e
    · -- k is the responder; its initiator is cell (k-1)
      have hk0 : 1 ≤ k := Nat.le_trans hlo hk1'
      have hE : e = cell ring s (k - 1) := by
        apply right_injective ring
        rw [← hr, right_cell, show k - 1 + 1 = k by omega]
      by_cases hk3 : p.1 ≤ k - 1
      · have h1 : D e = C e := by rw [hE]; exact (hCD (k - 1) hk3 (by omega)).symm
        have h2 : D (ring.rightNeighbor e) = C (ring.rightNeighbor e) := by
          rw [← hr]; exact (hCD k hk1' hk2').symm
        rw [hr]
        exact ((hL.pair C D e h1 h2).2).symm
      · exfalso
        have hE' : e = cell ring s (p.1 - 1) := by rw [hE, show k - 1 = p.1 - 1 by omega]
        unfold shrink at hk1
        simp only [hE', if_true] at hk1
        omega
    · rw [hL.other C e _ he hr, hL.other D e _ he hr]
      exact hCD k hk1' hk2'

/-- The interval after a word. -/
def shrinkWord (ring : DirectedRing n) (s : Fin n) : Nat × Nat → List (Fin n) → Nat × Nat
  | p, [] => p
  | p, e :: w => shrinkWord ring s (shrink ring s p e) w

theorem run_interval {step : (Fin n → X) → Fin n → (Fin n → X)} {ring : DirectedRing n} (hL : PairLocal ring step)
    (s : Fin n) : ∀ (w : List (Fin n)) (p : Nat × Nat) (C D : Fin n → X), 1 ≤ p.1 → p.2 < n →
      (∀ k, p.1 ≤ k → k < p.2 → C (cell ring s k) = D (cell ring s k)) →
      ∀ k, (shrinkWord ring s p w).1 ≤ k → k < (shrinkWord ring s p w).2 →
        w.foldl step C (cell ring s k) = w.foldl step D (cell ring s k)
  | [], p, C, D, _, _, hCD => fun k h1 h2 => hCD k h1 h2
  | e :: w, p, C, D, hlo, hhi, hCD => by
      have hb := shrink_bounds ring s p e
      exact run_interval hL s w (shrink ring s p e) (step C e) (step D e) (Nat.le_trans hlo hb.1)
        (Nat.lt_of_le_of_lt hb.2 hhi) (step_interval hL s p hlo hhi C D hCD e)

/-- The left end along a word. -/
def leftReach (ring : DirectedRing n) (s : Fin n) : Nat → List (Fin n) → Nat
  | lo, [] => lo
  | lo, e :: w => leftReach ring s (if e = cell ring s (lo - 1) then lo + 1 else lo) w

/-- The right end along a word. -/
def rightReach (ring : DirectedRing n) (s : Fin n) : Nat → List (Fin n) → Nat
  | hi, [] => hi
  | hi, e :: w => rightReach ring s (if e = cell ring s (hi - 1) then hi - 1 else hi) w

theorem shrinkWord_eq (ring : DirectedRing n) (s : Fin n) :
    ∀ (w : List (Fin n)) (p : Nat × Nat), shrinkWord ring s p w = (leftReach ring s p.1 w, rightReach ring s p.2 w)
  | [], _ => rfl
  | e :: w, p => by
      show shrinkWord ring s (shrink ring s p e) w = _
      rw [shrinkWord_eq ring s w]
      rfl

/-! ## Counting words that move an end far -/

/-- Factorial (core Lean has none). -/
def fact : Nat → Nat
  | 0 => 1
  | g + 1 => (g + 1) * fact g

/-- Binomial coefficients by Pascal's rule. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | T + 1, g + 1 => binom T g + binom T (g + 1)

theorem binom_mul_factorial_le : ∀ (T g : Nat), binom T g * fact g ≤ T ^ g
  | _, 0 => by simp [binom, fact]
  | 0, g + 1 => by simp [binom]
  | T + 1, g + 1 => by
      have h1 := binom_mul_factorial_le T g
      have h2 := binom_mul_factorial_le T (g + 1)
      have hf : fact (g + 1) = (g + 1) * fact g := rfl
      have hbern := B9OrderedWindowMatcher.bernoulli T g
      show (binom T g + binom T (g + 1)) * fact (g + 1) ≤ (T + 1) ^ (g + 1)
      rw [Nat.add_mul]
      have hA : binom T g * fact (g + 1) ≤ (g + 1) * T ^ g := by
        rw [hf, Nat.mul_left_comm]; exact Nat.mul_le_mul_left _ h1
      omega

theorem binom_succ_succ (T g : Nat) : binom (T + 1) (g + 1) = binom T g + binom T (g + 1) := rfl

theorem binom_eq_zero_of_lt : ∀ (T g : Nat), T < g → binom T g = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | T + 1, g + 1, h => by
      rw [binom_succ_succ, binom_eq_zero_of_lt T g (by omega), binom_eq_zero_of_lt T (g + 1) (by omega)]

/-- A sum over letters bounded by one exceptional letter and a uniform bound elsewhere. -/
theorem ofFn_sum_le_spike (F : Fin n → Nat) (c : Fin n) (B : Nat) (h : ∀ e, e ≠ c → F e ≤ B) :
    (List.ofFn F).sum ≤ F c + n * B := by
  have hs := B9SpliceTableV10d.ofFn_sum_split F (fun _ => B) c h
  rw [ofFn_sum_const] at hs
  omega

theorem leftReach_count (ring : DirectedRing n) (s : Fin n) :
    ∀ (T lo g : Nat), wordSum n T (fun w => if lo + g ≤ leftReach ring s lo w then 1 else 0) ≤
      binom T g * n ^ (T - g)
  | T, lo, 0 => by
      have h := wordSum_pair_le T (fun w => if lo + 0 ≤ leftReach ring s lo w then 1 else 0) (fun _ => 0)
        (fun u => by split <;> omega)
      simp only [binom, Nat.one_mul, Nat.sub_zero]
      omega
  | 0, lo, g + 1 => by
      unfold wordSum
      simp [allSchedules, leftReach, binom]
  | T + 1, lo, g + 1 => by
      rw [wordSum_succ]
      have hspike := ofFn_sum_le_spike
        (fun e : Fin n => wordSum n T (fun u => if lo + (g + 1) ≤ leftReach ring s lo (e :: u) then 1 else 0))
        (cell ring s (lo - 1)) (binom T (g + 1) * n ^ (T - (g + 1)))
        (by
          intro e he
          have hu : (fun u => if lo + (g + 1) ≤ leftReach ring s lo (e :: u) then 1 else 0) =
              (fun u => if lo + (g + 1) ≤ leftReach ring s lo u then 1 else 0) := by
            funext u; simp only [leftReach, if_neg he]
          show wordSum n T _ ≤ _
          rw [hu]; exact leftReach_count ring s T lo (g + 1))
      have hc : wordSum n T (fun u => if lo + (g + 1) ≤ leftReach ring s lo (cell ring s (lo - 1) :: u) then 1 else 0)
          ≤ binom T g * n ^ (T - g) := by
        have hu : (fun u => if lo + (g + 1) ≤ leftReach ring s lo (cell ring s (lo - 1) :: u) then 1 else 0) =
            (fun u => if (lo + 1) + g ≤ leftReach ring s (lo + 1) u then 1 else 0) := by
          funext u; simp only [leftReach, if_true]; rw [show lo + (g + 1) = lo + 1 + g by omega]
        rw [hu]; exact leftReach_count ring s T (lo + 1) g
      refine Nat.le_trans hspike ?_
      rw [binom_succ_succ, Nat.add_mul]
      have e1 : T + 1 - (g + 1) = T - g := by omega
      rw [e1]
      by_cases hg : g + 1 ≤ T
      · have e2 : n * (binom T (g + 1) * n ^ (T - (g + 1))) = binom T (g + 1) * n ^ (T - g) := by
          rw [Nat.mul_left_comm, ← Nat.pow_succ']
          congr 2
          omega
        omega
      · have hz : binom T (g + 1) = 0 := binom_eq_zero_of_lt T (g + 1) (by omega)
        rw [hz]; simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
        rw [hz] at hspike; simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero] at hspike
        exact hc

theorem rightReach_count (ring : DirectedRing n) (s : Fin n) :
    ∀ (T hi g : Nat), wordSum n T (fun w => if rightReach ring s hi w + g ≤ hi then 1 else 0) ≤
      binom T g * n ^ (T - g)
  | T, hi, 0 => by
      have h := wordSum_pair_le T (fun w => if rightReach ring s hi w + 0 ≤ hi then 1 else 0) (fun _ => 0)
        (fun u => by split <;> omega)
      simp only [binom, Nat.one_mul, Nat.sub_zero]
      omega
  | 0, hi, g + 1 => by
      unfold wordSum
      simp [allSchedules, rightReach, binom]
  | T + 1, hi, g + 1 => by
      rw [wordSum_succ]
      have hspike := ofFn_sum_le_spike
        (fun e : Fin n => wordSum n T (fun u => if rightReach ring s hi (e :: u) + (g + 1) ≤ hi then 1 else 0))
        (cell ring s (hi - 1)) (binom T (g + 1) * n ^ (T - (g + 1)))
        (by
          intro e he
          have hu : (fun u => if rightReach ring s hi (e :: u) + (g + 1) ≤ hi then 1 else 0) =
              (fun u => if rightReach ring s hi u + (g + 1) ≤ hi then 1 else 0) := by
            funext u; simp only [rightReach, if_neg he]
          show wordSum n T _ ≤ _
          rw [hu]; exact rightReach_count ring s T hi (g + 1))
      have hc : wordSum n T (fun u => if rightReach ring s hi (cell ring s (hi - 1) :: u) + (g + 1) ≤ hi then 1 else 0)
          ≤ binom T g * n ^ (T - g) := by
        have hmono := B9SpliceMatcherMass.wordSum_mono T
          (fun u => if rightReach ring s hi (cell ring s (hi - 1) :: u) + (g + 1) ≤ hi then 1 else 0)
          (fun u => if rightReach ring s (hi - 1) u + g ≤ hi - 1 then 1 else 0)
          (fun u => by
            simp only [rightReach, if_true]
            by_cases h1 : rightReach ring s (hi - 1) u + (g + 1) ≤ hi
            · rw [if_pos h1, if_pos (by omega)]
              exact Nat.le_refl 1
            · rw [if_neg h1]; exact Nat.zero_le _)
        exact Nat.le_trans hmono (rightReach_count ring s T (hi - 1) g)
      refine Nat.le_trans hspike ?_
      rw [binom_succ_succ, Nat.add_mul]
      have e1 : T + 1 - (g + 1) = T - g := by omega
      rw [e1]
      by_cases hg : g + 1 ≤ T
      · have e2 : n * (binom T (g + 1) * n ^ (T - (g + 1))) = binom T (g + 1) * n ^ (T - g) := by
          rw [Nat.mul_left_comm, ← Nat.pow_succ']
          congr 2
          omega
        omega
      · have hz : binom T (g + 1) = 0 := binom_eq_zero_of_lt T (g + 1) (by omega)
        rw [hz]; simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
        rw [hz] at hspike; simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero] at hspike
        exact hc

end B6LightCone
