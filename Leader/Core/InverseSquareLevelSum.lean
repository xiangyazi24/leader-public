import Lean

/-!
# Division-free summation of coalescence level budgets

The centered coalescence proof produces a residence-cost numerator `a m` at
each support level with `m^2 * a m <= 4*K`.  This module proves directly over
`Nat` that the sum over levels `2,...,n` is at most `3*K`; no reciprocals or
analytic series are introduced.
-/

namespace CoalescenceLevelSum

set_option autoImplicit false

/-- `intervalSum a lo fuel` sums `a lo, ..., a (lo+fuel-1)`. -/
def intervalSum (a : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | lo, fuel + 1 => a lo + intervalSum a (lo + 1) fuel

@[simp] theorem intervalSum_zero (a : Nat → Nat) (lo : Nat) :
    intervalSum a lo 0 = 0 := rfl

@[simp] theorem intervalSum_succ (a : Nat → Nat) (lo fuel : Nat) :
    intervalSum a lo (fuel + 1) =
      a lo + intervalSum a (lo + 1) fuel := rfl

/-- Squaring the division-free minimum-gap certificate. -/
theorem min_gap_square {m q n : Nat} (hgap : m * q ≤ 2 * n) :
    m ^ 2 * q ^ 2 ≤ 4 * n ^ 2 := by
  have hsq := Nat.mul_le_mul hgap hgap
  calc
    m ^ 2 * q ^ 2 = (m * q) * (m * q) := by
      simp only [Nat.pow_two]
      ac_rfl
    _ ≤ (2 * n) * (2 * n) := hsq
    _ = 4 * n ^ 2 := by
      simp only [Nat.pow_two]
      ac_rfl

/-- A division-free minimum-gap certificate places the selected gap below the
common fixed-level scale `Q = floor(2*n/m)`. -/
theorem gap_le_common_scale {m q n : Nat} (hm : 0 < m)
    (hgap : m * q ≤ 2 * n) :
    q ≤ (2 * n) / m := by
  apply (Nat.le_div_iff_mul_le hm).2
  simpa [Nat.mul_comm] using hgap

/-- The common scale still satisfies the original product bound. -/
theorem common_scale_mul_le (m n : Nat) :
    m * ((2 * n) / m) ≤ 2 * n := by
  simpa using Nat.mul_div_le (2 * n) m

/-- The restarted fixed-level budget `n*Q^2` becomes cubic after multiplying
by the square of the current support size. -/
theorem common_scale_cubic {m n Q : Nat} (hQ : m * Q ≤ 2 * n) :
    m ^ 2 * (n * Q ^ 2) ≤ 4 * n ^ 3 := by
  have hsq := min_gap_square hQ
  have hscaled := Nat.mul_le_mul_left n hsq
  calc
    m ^ 2 * (n * Q ^ 2) = n * (m ^ 2 * Q ^ 2) := by ac_rfl
    _ ≤ n * (4 * n ^ 2) := hscaled
    _ = 4 * n ^ 3 := by
      simp only [Nat.pow_succ]
      ac_rfl

/-- Converts the killed-walk duration and minimum-gap estimates into the exact
support-scaled one-trial cubic budget. -/
theorem scaled_trial_cost {m q n D T : Nat}
    (hduration : 2 * D ≤ n * q ^ 2 * n ^ T)
    (hgap : m * q ≤ 2 * n) :
    m ^ 2 * D ≤ 2 * n ^ 3 * n ^ T := by
  have hmul := Nat.mul_le_mul_left (m ^ 2) hduration
  have hsq := min_gap_square hgap
  have hsqScaled := Nat.mul_le_mul_left (n * n ^ T) hsq
  have htwo : 2 * (m ^ 2 * D) ≤ 2 * (2 * n ^ 3 * n ^ T) := by
    apply Nat.le_trans (by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul)
    apply Nat.le_trans (by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsqScaled)
    exact Nat.le_of_eq (by
      simp only [Nat.pow_succ]
      rw [show (4 : Nat) = 2 * 2 by decide]
      ac_rfl)
  exact Nat.le_of_mul_le_mul_left htwo (by omega)

/-- Telescoping tail estimate.  The square-scaled pointwise hypothesis is
weakened to `m*(m-1)` at the first level; the induction hypothesis pays the
remaining tail after multiplying once by `m`. -/
theorem intervalSum_tail_scaled (a : Nat → Nat) (K lo fuel : Nat)
    (hlo : 3 ≤ lo)
    (hlevel : ∀ i, lo ≤ i → i < lo + fuel →
      i ^ 2 * a i ≤ 4 * K) :
    (lo - 1) * intervalSum a lo fuel ≤ 4 * K := by
  induction fuel generalizing lo with
  | zero => simp [intervalSum]
  | succ fuel ih =>
      have hfirstSq : lo ^ 2 * a lo ≤ 4 * K :=
        hlevel lo (Nat.le_refl _) (by omega)
      have hcoeff : lo * (lo - 1) ≤ lo ^ 2 := by
        rw [Nat.pow_two]
        exact Nat.mul_le_mul_left lo (by omega)
      have hfirst : lo * (lo - 1) * a lo ≤ 4 * K :=
        Nat.le_trans (Nat.mul_le_mul_right (a lo) hcoeff) hfirstSq
      have htailLevel : ∀ i, lo + 1 ≤ i →
          i < (lo + 1) + fuel → i ^ 2 * a i ≤ 4 * K := by
        intro i hil hit
        exact hlevel i (by omega) (by omega)
      have htailRaw := ih (lo := lo + 1) (by omega) htailLevel
      have htail : lo * intervalSum a (lo + 1) fuel ≤ 4 * K := by
        simpa using htailRaw
      have htailScaled := Nat.mul_le_mul_left (lo - 1) htail
      have hsum := Nat.add_le_add hfirst htailScaled
      have hmul : lo * ((lo - 1) * intervalSum a lo (fuel + 1)) ≤
          lo * (4 * K) := by
        calc
          lo * ((lo - 1) * intervalSum a lo (fuel + 1)) =
              lo * (lo - 1) * a lo +
                (lo - 1) * (lo * intervalSum a (lo + 1) fuel) := by
                  simp only [intervalSum_succ, Nat.mul_add]
                  ac_rfl
          _ ≤ 4 * K + (lo - 1) * (4 * K) := hsum
          _ = lo * (4 * K) := by
            have hloSplit : lo = 1 + (lo - 1) := by omega
            rw [hloSplit, Nat.add_mul]
            simp
      exact Nat.le_of_mul_le_mul_left hmul (by omega)

/-- If every support level `m` has `m^2*a(m) <= 4*K`, then the total over
levels `2,...,n` is at most `3*K`.  The level-two term costs `K`; all levels
at least three cost at most `2*K` by the preceding telescoping tail. -/
theorem sum_levels_le_three_of_sq_scaled (a : Nat → Nat) (K n : Nat)
    (hn2 : 2 ≤ n)
    (hlevel : ∀ m, 2 ≤ m → m ≤ n →
      m ^ 2 * a m ≤ 4 * K) :
    intervalSum a 2 (n - 1) ≤ 3 * K := by
  have htwoRaw := hlevel 2 (by omega) hn2
  have htwoScaled : 4 * a 2 ≤ 4 * K := by simpa using htwoRaw
  have htwo : a 2 ≤ K :=
    Nat.le_of_mul_le_mul_left htwoScaled (by omega)
  have htailLevel : ∀ i, 3 ≤ i → i < 3 + (n - 2) →
      i ^ 2 * a i ≤ 4 * K := by
    intro i hi3 hin
    exact hlevel i (by omega) (by omega)
  have htailScaled := intervalSum_tail_scaled a K 3 (n - 2)
    (by omega) htailLevel
  have htailScaled' : 2 * intervalSum a 3 (n - 2) ≤ 4 * K := by
    simpa using htailScaled
  have htail : intervalSum a 3 (n - 2) ≤ 2 * K := by
    have hrewrite : 4 * K = 2 * (2 * K) := by omega
    rw [hrewrite] at htailScaled'
    exact Nat.le_of_mul_le_mul_left htailScaled' (by omega)
  have hsplit : intervalSum a 2 (n - 1) =
      a 2 + intervalSum a 3 (n - 2) := by
    have hn : n - 1 = (n - 2) + 1 := by omega
    rw [hn, intervalSum_succ]
  rw [hsplit]
  exact Nat.le_trans (Nat.add_le_add htwo htail) (by omega)

end CoalescenceLevelSum
