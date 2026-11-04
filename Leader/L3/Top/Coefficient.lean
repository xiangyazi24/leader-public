import Leader.L3.Headline.Assembly
import Leader.L3.RequestCoefficient

/-!
Pure Nat coefficient for the fixed-data strict TOP comparison.

Exactly two imports, no changed source
modules. The paper's h(r) is charged against the selected physical
checker ledger rather than against an unselected K_chk table.

The paper's finite table includes t=4 and t=6. The literal finite
compiler selects t=2,3,5; the large compiler starts at t>=6.
The main inequality is division-free: h(r) <= rate * N_t.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- The nominated-edge quota from certificate.tex (A.1). -/
def topCoefficientH (r : Nat) : Nat :=
  12 * r ^ 4 + 40 * r ^ 3 + 18 * r ^ 2 + 36 * r + 10

/-- The strict TOP quota at compiler certificate width t. -/
def topCoefficientWidthH (t : Nat) : Nat :=
  topCoefficientH (2 ^ t - 1)

/-- The paper's least permitted population at width t. -/
def topCoefficientMinPopulation (t : Nat) : Nat :=
  2 ^ (2 ^ (t - 1)) + 1

/-! The five exact finite TOP ceiling certificates.
No large table/orbit is evaluated. Each inequality is a small
closed Nat comparison, reduced by the Boolean comparison kernel. -/

theorem topCoefficientTableTwo :
    topCoefficientWidthH 2 ≤
      467 * topCoefficientMinPopulation 2 := by
  change (2332 : Nat) ≤ 467 * 5
  exact Nat.le_of_ble_eq_true rfl

theorem topCoefficientTableThree :
    topCoefficientWidthH 3 ≤
      2570 * topCoefficientMinPopulation 3 := by
  change (43676 : Nat) ≤ 2570 * 17
  exact Nat.le_of_ble_eq_true rfl

theorem topCoefficientTableFour :
    topCoefficientWidthH 4 ≤
      2908 * topCoefficientMinPopulation 4 := by
  change (747100 : Nat) ≤ 2908 * 257
  exact Nat.le_of_ble_eq_true rfl

theorem topCoefficientTableFive :
    topCoefficientWidthH 5 ≤
      188 * topCoefficientMinPopulation 5 := by
  change (12292316 : Nat) ≤ 188 * 65537
  exact Nat.le_of_ble_eq_true rfl

theorem topCoefficientTableSix :
    topCoefficientWidthH 6 ≤
      topCoefficientMinPopulation 6 := by
  change (199111132 : Nat) ≤ 4294967297
  exact Nat.le_of_ble_eq_true rfl

/-! The wide bound uses no factorial or primitive-tap hypothesis. -/

/-- For r >= 40, each subleading monomial is dominated by r^4.
Thus the exact A.1 polynomial is strictly below 16*r^4. -/
private theorem topCoefficientQuarticDominance (r : Nat)
    (hr : 40 ≤ r) :
    topCoefficientH r < 16 * r ^ 4 := by
  have hpos : 0 < r := by omega
  have htwo : 40 ≤ r ^ 2 := by
    calc
      40 ≤ r := hr
      _ = r ^ 1 := by simp
      _ ≤ r ^ 2 :=
        Nat.pow_le_pow_right hpos (by omega : 1 ≤ 2)
  have hthree : 40 ≤ r ^ 3 := by
    calc
      40 ≤ r := hr
      _ = r ^ 1 := by simp
      _ ≤ r ^ 3 :=
        Nat.pow_le_pow_right hpos (by omega : 1 ≤ 3)
  have hfour : 40 ≤ r ^ 4 := by
    calc
      40 ≤ r := hr
      _ = r ^ 1 := by simp
      _ ≤ r ^ 4 :=
        Nat.pow_le_pow_right hpos (by omega : 1 ≤ 4)
  have hcubic : 40 * r ^ 3 ≤ r ^ 4 := by
    calc
      40 * r ^ 3 ≤ r * r ^ 3 :=
        Nat.mul_le_mul_right (r ^ 3) hr
      _ = r ^ 4 := by simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc,
          Nat.mul_comm, Nat.mul_left_comm]
  have hsquare : 18 * r ^ 2 ≤ r ^ 4 := by
    calc
      18 * r ^ 2 ≤ (r ^ 2) * r ^ 2 :=
        Nat.mul_le_mul_right (r ^ 2) (by omega : 18 ≤ r ^ 2)
      _ = r ^ 4 := by simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc,
          Nat.mul_comm, Nat.mul_left_comm]
  have hlinear : 36 * r ≤ r ^ 4 := by
    calc
      36 * r ≤ (r ^ 3) * r :=
        Nat.mul_le_mul_right r (by omega : 36 ≤ r ^ 3)
      _ = r ^ 4 := by simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc,
          Nat.mul_comm, Nat.mul_left_comm]
  have hconstant : 10 < r ^ 4 := by omega
  unfold topCoefficientH
  omega

/-- A fourth power of the dyadic width can be combined into one
power of 2; the change of exponent is linear arithmetic. -/
private theorem topCoefficientDyadicFourth (t : Nat) :
    16 * (2 ^ t) ^ 4 = 2 ^ (4 * t + 4) := by
  have hpow : (2 ^ t) ^ 4 = 2 ^ (4 * t) := by
    calc
      (2 ^ t) ^ 4 =
          (2 ^ t) * (2 ^ t) * (2 ^ t) * (2 ^ t) := by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      _ = 2 ^ (t + t + t + t) := by
        rw [Nat.pow_add, Nat.pow_add, Nat.pow_add]
      _ = 2 ^ (4 * t) := by
        congr 1
        omega
  rw [hpow]
  change 2 ^ 4 * 2 ^ (4 * t) = 2 ^ (4 * t + 4)
  rw [← Nat.pow_add]
  congr 1
  omega

/-- 4t+4 <= 2^(t-1), first at t=6 and then by doubling.
The induction does not expand a doubly-exponential numeral. -/
private theorem topCoefficientDyadicExponent (t : Nat)
    (ht : 6 ≤ t) :
    4 * t + 4 ≤ 2 ^ (t - 1) := by
  have hall : ∀ k : Nat,
      4 * (k + 6) + 4 ≤ 2 ^ ((k + 6) - 1) := by
    intro k
    induction k with
    | zero =>
        change (28 : Nat) ≤ 32
        exact Nat.le_of_ble_eq_true rfl
    | succ k ih =>
        have he :
            (k + 1 + 6) - 1 = ((k + 6) - 1) + 1 := by omega
        rw [he, Nat.pow_succ]
        omega
  have hh := hall (t - 6)
  have he : t - 6 + 6 = t := by omega
  rw [he] at hh
  exact hh

/-- The strict h(r)<N_t comparison already holds for t>=6.
In particular the paper's t>=7 inequality holds without
using the weaker 1048576 budget, and t=6 is covered too. -/
theorem topCoefficientWidePopulation (t : Nat)
    (ht : 6 ≤ t) :
    topCoefficientWidthH t ≤ topCoefficientMinPopulation t := by
  have hp : 64 ≤ (2 : Nat) ^ t := by
    calc
      64 = (2 : Nat) ^ 6 := by rfl
      _ ≤ 2 ^ t :=
        Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) ht
  have hr : 40 ≤ (2 : Nat) ^ t - 1 := by omega
  have hquartic :=
    topCoefficientQuarticDominance (2 ^ t - 1) hr
  have hpower :
      (2 ^ t - 1) ^ 4 ≤ (2 ^ t) ^ 4 :=
    Nat.pow_le_pow_left (Nat.sub_le _ _) 4
  have hexponent := topCoefficientDyadicExponent t ht
  have hstrict :
      topCoefficientH (2 ^ t - 1) <
        2 ^ (2 ^ (t - 1)) := by
    calc
      topCoefficientH (2 ^ t - 1) <
          16 * (2 ^ t - 1) ^ 4 := hquartic
      _ ≤ 16 * (2 ^ t) ^ 4 :=
        Nat.mul_le_mul_left 16 hpower
      _ = 2 ^ (4 * t + 4) :=
        topCoefficientDyadicFourth t
      _ ≤ 2 ^ (2 ^ (t - 1)) :=
        Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) hexponent
  unfold topCoefficientWidthH topCoefficientMinPopulation
  omega

/-! Actual compiler and selected-ledger projections. -/

/-- The lower population floor implicit in the definition of
ceilLogTwo. This avoids any division and is valid at each cut. -/
private theorem topCoefficientPopulationAfterAdvice
    (n a : Nat) (hn : 2 ≤ n)
    (ha : a + 1 ≤ ceilLogTwo n) :
    2 ^ a + 1 ≤ n := by
  have hlo := (ceilLogTwo_spec n hn).1
  have hp :
      2 ^ a ≤ 2 ^ (ceilLogTwo n - 1) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) (by omega)
  omega

/-- The installed finite checker rows are 5963,6093,1154 on
the three literal finite compiler width bands. -/
private theorem topCoefficientFiniteLedgerRate (q : Nat)
    (hthree : 3 ≤ q) (hmax : q ≤ 32) :
    (headlineFiniteLedger q).2.2 =
      (if q ≤ 4 then 5963
       else if q ≤ 16 then 6093 else 1154) := by
  by_cases hfour : q ≤ 4
  · rw [if_pos hfour]
    have hc : q = 3 ∨ q = 4 := by omega
    rcases hc with h | h <;> subst q <;> rfl
  · rw [if_neg hfour]
    by_cases hsixteen : q ≤ 16
    · rw [if_pos hsixteen]
      have hc : q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨
          q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨
          q = 13 ∨ q = 14 ∨ q = 15 ∨ q = 16 := by omega
      rcases hc with h | h | h | h | h | h | h | h | h | h | h | h <;>
        subst q <;> rfl
    · rw [if_neg hsixteen]
      have hc : q = 17 ∨ q = 18 ∨ q = 19 ∨ q = 20 ∨
          q = 21 ∨ q = 22 ∨ q = 23 ∨ q = 24 ∨
          q = 25 ∨ q = 26 ∨ q = 27 ∨ q = 28 ∨
          q = 29 ∨ q = 30 ∨ q = 31 ∨ q = 32 := by omega
      rcases hc with h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h <;> subst q <;> rfl

private theorem topCoefficientFiniteCheckerRate (n : Nat)
    (hthree : 3 ≤ ceilLogTwo n)
    (hmax : ceilLogTwo n ≤ 32) :
    headlineCheckerRate n =
      (if ceilLogTwo n ≤ 4 then 5963
       else if ceilLogTwo n ≤ 16 then 6093 else 1154) := by
  unfold headlineCheckerRate headlineSelectedLedger
  rw [if_pos hmax]
  exact topCoefficientFiniteLedgerRate (ceilLogTwo n) hthree hmax

private theorem topCoefficientLargeLedgerRate (s : Nat)
    (hs : 6 ≤ s) :
    (headlineLargeLedger s).2.2 = 1048576 := by
  unfold headlineLargeLedger
  split
  · rename_i hmax
    have hc : s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 ∨
        s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨
        s = 14 ∨ s = 15 ∨ s = 16 := by omega
    rcases hc with h | h | h | h | h | h | h | h | h | h | h <;>
      subst s <;> rfl
  · rfl

private theorem topCoefficientLargeCheckerRate (n : Nat)
    (hq : 33 ≤ ceilLogTwo n) :
    headlineCheckerRate n = 1048576 := by
  unfold headlineCheckerRate headlineSelectedLedger
  rw [if_neg (by omega : ¬ ceilLogTwo n ≤ 32)]
  exact topCoefficientLargeLedgerRate
    (ceilLogTwo (ceilLogTwo n))
    (ceilLogTwo_ge_six (ceilLogTwo n) hq)

/-- Exactly the paper's n >= N_t lower bound at the literal
compiled certificate width. Covers all finite and large bands. -/
theorem topCoefficientCompiledPopulationFloor (n : Nat)
    (hn : 5 ≤ n) :
    topCoefficientMinPopulation
      (compileAdvice (ceilLogTwo n)).t ≤ n := by
  have hq : 3 ≤ ceilLogTwo n := ceilLogTwo_ge_three n hn
  by_cases hfour : ceilLogTwo n ≤ 4
  · have ht : (compileAdvice (ceilLogTwo n)).t = 2 := by
      rw [compileAdvice_t_finite (ceilLogTwo n) hq (by omega)]
      unfold finiteCertWidth
      rw [if_pos hfour]
    rw [ht]
    change (5 : Nat) ≤ n
    exact hn
  · by_cases hsixteen : ceilLogTwo n ≤ 16
    · have ht : (compileAdvice (ceilLogTwo n)).t = 3 := by
        rw [compileAdvice_t_finite (ceilLogTwo n) hq (by omega)]
        unfold finiteCertWidth
        rw [if_neg hfour, if_pos hsixteen]
      rw [ht]
      have hp := topCoefficientPopulationAfterAdvice
        n 4 (by omega) (by omega)
      change (17 : Nat) ≤ n
      exact hp
    · by_cases hthirtytwo : ceilLogTwo n ≤ 32
      · have ht : (compileAdvice (ceilLogTwo n)).t = 5 := by
          rw [compileAdvice_t_finite (ceilLogTwo n) hq hthirtytwo]
          unfold finiteCertWidth
          rw [if_neg hfour, if_neg hsixteen]
        rw [ht]
        have hp := topCoefficientPopulationAfterAdvice
          n 16 (by omega) (by omega)
        change (65537 : Nat) ≤ n
        exact hp
      · have hlarge : 33 ≤ ceilLogTwo n := by omega
        have ht := compileAdvice_t_large
          (ceilLogTwo n) hlarge
        rw [ht]
        exact HeadlineRequest.requestLargePopulationFloor
          n hn hlarge

/-- Division-free form of the required K_chk comparison:
h(2^t-1) <= (selected checker rate) * N_t.
Finite bands use the installed rate, while every large band
already satisfies h <= N_t. -/
theorem topCoefficientCrossMultiplied (n : Nat)
    (hn : 5 ≤ n) :
    topCoefficientWidthH
        (compileAdvice (ceilLogTwo n)).t ≤
      headlineCheckerRate n *
        topCoefficientMinPopulation
          (compileAdvice (ceilLogTwo n)).t := by
  have hq : 3 ≤ ceilLogTwo n := ceilLogTwo_ge_three n hn
  by_cases hfour : ceilLogTwo n ≤ 4
  · have ht : (compileAdvice (ceilLogTwo n)).t = 2 := by
      rw [compileAdvice_t_finite (ceilLogTwo n) hq (by omega)]
      unfold finiteCertWidth
      rw [if_pos hfour]
    have hr := topCoefficientFiniteCheckerRate n hq (by omega)
    rw [if_pos hfour] at hr
    rw [ht, hr]
    calc
      topCoefficientWidthH 2 ≤
          467 * topCoefficientMinPopulation 2 :=
        topCoefficientTableTwo
      _ ≤ 5963 * topCoefficientMinPopulation 2 :=
        Nat.mul_le_mul_right _ (by change 467 ≤ 5963; exact Nat.le_of_ble_eq_true rfl)
  · by_cases hsixteen : ceilLogTwo n ≤ 16
    · have ht : (compileAdvice (ceilLogTwo n)).t = 3 := by
        rw [compileAdvice_t_finite (ceilLogTwo n) hq (by omega)]
        unfold finiteCertWidth
        rw [if_neg hfour, if_pos hsixteen]
      have hr := topCoefficientFiniteCheckerRate n hq (by omega)
      rw [if_neg hfour, if_pos hsixteen] at hr
      rw [ht, hr]
      calc
        topCoefficientWidthH 3 ≤
            2570 * topCoefficientMinPopulation 3 :=
          topCoefficientTableThree
        _ ≤ 6093 * topCoefficientMinPopulation 3 :=
          Nat.mul_le_mul_right _ (by
            change 2570 ≤ 6093
            exact Nat.le_of_ble_eq_true rfl)
    · by_cases hthirtytwo : ceilLogTwo n ≤ 32
      · have ht : (compileAdvice (ceilLogTwo n)).t = 5 := by
          rw [compileAdvice_t_finite (ceilLogTwo n) hq hthirtytwo]
          unfold finiteCertWidth
          rw [if_neg hfour, if_neg hsixteen]
        have hr := topCoefficientFiniteCheckerRate n hq hthirtytwo
        rw [if_neg hfour, if_neg hsixteen] at hr
        rw [ht, hr]
        calc
          topCoefficientWidthH 5 ≤
              188 * topCoefficientMinPopulation 5 :=
            topCoefficientTableFive
          _ ≤ 1154 * topCoefficientMinPopulation 5 :=
            Nat.mul_le_mul_right _ (by change 188 ≤ 1154; exact Nat.le_of_ble_eq_true rfl)
      · have hlarge : 33 ≤ ceilLogTwo n := by omega
        have ht := compileAdvice_t_large
          (ceilLogTwo n) hlarge
        have hr := topCoefficientLargeCheckerRate n hlarge
        have hwidth :=
          ceilLogTwo_ge_six (ceilLogTwo n) hlarge
        rw [ht, hr]
        calc
          topCoefficientWidthH
              (ceilLogTwo (ceilLogTwo n)) ≤
              topCoefficientMinPopulation
                (ceilLogTwo (ceilLogTwo n)) :=
            topCoefficientWidePopulation
              (ceilLogTwo (ceilLogTwo n)) hwidth
          _ = 1 * topCoefficientMinPopulation
                (ceilLogTwo (ceilLogTwo n)) := by
            rw [Nat.one_mul]
          _ ≤ 1048576 *
              topCoefficientMinPopulation
                (ceilLogTwo (ceilLogTwo n)) :=
            Nat.mul_le_mul_right _ (by change 1 ≤ 1048576; exact Nat.le_of_ble_eq_true rfl)

/-- The strict TOP clock's h(r) interactions-per-site are
affordable at the actual population, not only at N_t. -/
theorem topCoefficientCheckerRateBound (n : Nat)
    (hn : 5 ≤ n) :
    topCoefficientWidthH
      (compileAdvice (ceilLogTwo n)).t ≤
        headlineCheckerRate n * n := by
  exact Nat.le_trans (topCoefficientCrossMultiplied n hn)
    (Nat.mul_le_mul_left (headlineCheckerRate n)
      (topCoefficientCompiledPopulationFloor n hn))

/-- The final contribution to the physical checker budget.
The TOP expected time n*h(r) fits rate*n^2 without using the
extra +1 reserved by the existing RAW clock. -/
theorem topCoefficientScaledBound (n : Nat)
    (hn : 5 ≤ n) :
    topCoefficientWidthH
        (compileAdvice (ceilLogTwo n)).t * n ≤
      headlineCheckerRate n * n ^ 2 := by
  have hh := topCoefficientCheckerRateBound n hn
  calc
    topCoefficientWidthH
        (compileAdvice (ceilLogTwo n)).t * n ≤
        (headlineCheckerRate n * n) * n :=
      Nat.mul_le_mul_right n hh
    _ = headlineCheckerRate n * n ^ 2 := by
      simp only [Nat.pow_two]
      ac_rfl

end L3
