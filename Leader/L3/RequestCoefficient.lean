import Leader.L3.Headline.Request

/-!
The progress-only scan branch gives p_scan(t) >= 1 / t!.
A separate polynomial-factorial majorant proves the all-width
coefficient bound. No recurrence table is evaluated above width five.
-/

namespace L3.HeadlineRequest

open CouponClear

set_option autoImplicit false
set_option Elab.async false

/-! ## Progress-only lower bound for the exact scan fraction -/

private theorem requestPairAddReciprocal
    (F : Nat) (a b : Nat × Nat)
    (ha : a.2 ≤ F * a.1) :
    (pairAdd a b).2 ≤ F * (pairAdd a b).1 := by
  change a.2 * b.2 ≤ F * (a.1 * b.2 + b.1 * a.2)
  have hnonnegative :
      a.1 * b.2 ≤ a.1 * b.2 + b.1 * a.2 := by omega
  calc
    a.2 * b.2 ≤ (F * a.1) * b.2 :=
      Nat.mul_le_mul_right b.2 ha
    _ = F * (a.1 * b.2) := by ac_rfl
    _ ≤ F * (a.1 * b.2 + b.1 * a.2) :=
      Nat.mul_le_mul_left F hnonnegative

private theorem requestPairFoldReciprocal
    (F : Nat) (xs : List (Nat × Nat)) :
    ∀ a : Nat × Nat, a.2 ≤ F * a.1 →
      (xs.foldl pairAdd a).2 ≤ F * (xs.foldl pairAdd a).1 := by
  induction xs with
  | nil =>
      intro a ha
      exact ha
  | cons b xs ih =>
      intro a ha
      exact ih (pairAdd a b) (requestPairAddReciprocal F a b ha)

private theorem requestPairDivReciprocal
    (F d : Nat) (a : Nat × Nat)
    (ha : a.2 ≤ F * a.1) :
    (pairDiv a d).2 ≤ (d * F) * (pairDiv a d).1 := by
  change a.2 * d ≤ (d * F) * a.1
  calc
    a.2 * d ≤ (F * a.1) * d := Nat.mul_le_mul_right d ha
    _ = (d * F) * a.1 := by ac_rfl

private theorem requestFactorialDifference
    (t j : Nat) (hj : j < t) :
    freshFact (t - j) =
      (t - j) * freshFact (t - (j + 1)) := by
  have hd : t - j = t - (j + 1) + 1 := by omega
  rw [hd] <;> rfl

/-- Every progress spine fits when fuel covers t-j. The additional
    first-hit summands are nonnegative, even for arbitrary lists B. -/
theorem requestScanFuelReciprocal
    (fuel t j : Nat) (B : List Nat)
    (hf : t - j ≤ fuel) :
    (pFuel fuel t j B).2 ≤
      freshFact (t - j) * (pFuel fuel t j B).1 := by
  induction fuel generalizing t j B with
  | zero =>
      have hj : ¬ j < t := by omega
      have hz : t - j = 0 := by omega
      simp [pFuel, hj, hz, freshFact]
  | succ fuel ih =>
      by_cases hj : j < t
      · rw [pFuel_first_step fuel t j B hj,
          requestFactorialDifference t j hj]
        exact requestPairDivReciprocal
          (freshFact (t - (j + 1))) (t - j) _
          (requestPairFoldReciprocal
            (freshFact (t - (j + 1)))
            (B.map (fun k : Nat =>
              pFuel fuel t j (eraseAvailable k B)))
            (pFuel fuel t (j + 1) (eraseAvailable (j + 1) B))
            (ih t (j + 1) (eraseAvailable (j + 1) B) (by omega)))
      · have hz : t - j = 0 := by omega
        simp [pFuel, hj, hz, freshFact]

/-- The original A-coordinate fraction has the same progress lower
    bound. No canonical-list cardinality estimate is needed here. -/
theorem requestScanAtReciprocal (t j : Nat) (A : List Nat) :
    (pPairAt t j A).2 ≤
      freshFact (t - j) * (pPairAt t j A).1 := by
  dsimp only [pPairAt]
  exact requestScanFuelReciprocal
    (t - j + (futureUnhit t j A).length)
    t j (futureUnhit t j A) (by omega)

/-- Division-free p_scan(t) >= 1/t!, for every natural width. -/
theorem requestScanPairReciprocal (t : Nat) :
    (pPair t).2 ≤ freshFact t * (pPair t).1 := by
  simpa only [pPair, Nat.sub_zero] using
    requestScanAtReciprocal t 0 []

/-! ## Harmonic and factorial majorants -/

private theorem requestHarmonicRow (a d k : Nat)
    (ha : a ≤ k * d) :
    a * (k + 1) + d ≤ (k + 1) * (d * (k + 1)) := by
  have hd : d ≤ d * (k + 1) := by
    have hh := Nat.mul_le_mul_left d (by omega : 1 ≤ k + 1)
    simpa only [Nat.mul_one] using hh
  calc
    a * (k + 1) + d ≤ (k * d) * (k + 1) + d * (k + 1) :=
      Nat.add_le_add (Nat.mul_le_mul_right (k + 1) ha) hd
    _ = (k + 1) * (d * (k + 1)) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      ac_rfl

/-- H_m <= m in the actual unreduced harmonicPair scale. -/
theorem requestHarmonicBound (m : Nat) :
    (harmonicPair m).1 ≤ m * (harmonicPair m).2 := by
  induction m with
  | zero =>
      change (0 : Nat) ≤ 0
      exact Nat.le_refl _
  | succ m ih =>
      change
        (harmonicPair m).1 * (m + 1) +
            1 * (harmonicPair m).2 ≤
          (m + 1) * ((harmonicPair m).2 * (m + 1))
      simp only [Nat.one_mul]
      exact requestHarmonicRow
        (harmonicPair m).1 (harmonicPair m).2 m ih

private theorem requestCouponUpperAlgebra
    (H D F M L t a b f : Nat)
    (hH : H ≤ M * D) (hp : b ≤ f * a) :
    (H * F * L ^ 2 + (2 * L + t) * D) * b ≤
      (D * a) * (f * (M * F * L ^ 2 + 2 * L + t)) := by
  have hcore :
      H * F * L ^ 2 + (2 * L + t) * D ≤
        D * (M * F * L ^ 2 + 2 * L + t) := by
    calc
      H * F * L ^ 2 + (2 * L + t) * D ≤
          (M * D) * F * L ^ 2 + (2 * L + t) * D :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_right (L ^ 2)
            (Nat.mul_le_mul_right F hH)) _
      _ = D * (M * F * L ^ 2 + 2 * L + t) := by
        simp only [Nat.add_mul, Nat.mul_add]
        ac_rfl
  calc
    (H * F * L ^ 2 + (2 * L + t) * D) * b ≤
        (D * (M * F * L ^ 2 + 2 * L + t)) * (f * a) :=
      Nat.mul_le_mul hcore hp
    _ = (D * a) * (f * (M * F * L ^ 2 + 2 * L + t)) := by
      ac_rfl

/-- The progress-only bound requested in part (c). -/
def requestProgressEnvelope (t : Nat) : Nat :=
  freshFact t *
    ((t + 3) * freshFact (t + 3) * (t + 2) ^ 2 +
      2 * (t + 2) + t)

/-- G(t) is bounded without evaluating the finite scan recursion. -/
theorem requestCouponProgressBound (t : Nat) :
    (couponGPair t).1 ≤
      (couponGPair t).2 * requestProgressEnvelope t := by
  exact requestCouponUpperAlgebra
    (harmonicPair (t + 3)).1 (harmonicPair (t + 3)).2
    (freshFact (t + 3)) (t + 3) (t + 2) t
    (pPair t).1 (pPair t).2 (freshFact t)
    (requestHarmonicBound (t + 3)) (requestScanPairReciprocal t)

/-- A larger expression with a simple multiplicative growth bound. -/
private def requestEnvelope (t : Nat) : Nat :=
  2 * freshFact t * freshFact (t + 3) * (t + 3) ^ 3

private theorem requestEnvelopeCore (t F : Nat) (hF : 1 ≤ F) :
    (t + 3) * F * (t + 2) ^ 2 + 2 * (t + 2) + t ≤
      2 * F * (t + 3) ^ 3 := by
  have hmain : (t + 3) * F * (t + 2) ^ 2 ≤
      F * (t + 3) ^ 3 := by
    calc
      (t + 3) * F * (t + 2) ^ 2 ≤
          (t + 3) * F * (t + 3) ^ 2 :=
        Nat.mul_le_mul_left ((t + 3) * F)
          (Nat.pow_le_pow_left (by omega : t + 2 ≤ t + 3) 2)
      _ = F * (t + 3) ^ 3 := by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
        ac_rfl
  have htailSquare : 2 * (t + 2) + t ≤ (t + 3) ^ 2 := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul,
      Nat.mul_add, Nat.add_mul]
    omega
  have htailCube : 2 * (t + 2) + t ≤ (t + 3) ^ 3 :=
    Nat.le_trans htailSquare
      (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3))
  have htail : 2 * (t + 2) + t ≤ F * (t + 3) ^ 3 := by
    calc
      2 * (t + 2) + t ≤ (t + 3) ^ 3 := htailCube
      _ = 1 * (t + 3) ^ 3 := (Nat.one_mul _).symm
      _ ≤ F * (t + 3) ^ 3 := Nat.mul_le_mul_right _ hF
  calc
    (t + 3) * F * (t + 2) ^ 2 + 2 * (t + 2) + t =
        (t + 3) * F * (t + 2) ^ 2 + (2 * (t + 2) + t) := by
      omega
    _ ≤ F * (t + 3) ^ 3 + F * (t + 3) ^ 3 :=
      Nat.add_le_add hmain htail
    _ = 2 * F * (t + 3) ^ 3 := by
      simp only [Nat.mul_assoc]
      omega

private theorem requestProgressBelowEnvelope (t : Nat) :
    requestProgressEnvelope t ≤ requestEnvelope t := by
  have hF : 1 ≤ freshFact (t + 3) := coupon_factorial_pos (t + 3)
  have hh := Nat.mul_le_mul_left (freshFact t)
    (requestEnvelopeCore t (freshFact (t + 3)) hF)
  calc
    requestProgressEnvelope t ≤
        freshFact t * (2 * freshFact (t + 3) * (t + 3) ^ 3) := hh
    _ = requestEnvelope t := by
      unfold requestEnvelope
      ac_rfl

private theorem requestCubeDouble (x y : Nat) (h : x ≤ 2 * y) :
    x ^ 3 ≤ 8 * y ^ 3 := by
  calc
    x ^ 3 ≤ (2 * y) ^ 3 := Nat.pow_le_pow_left h 3
    _ = (2 * 2 * 2) * (y * y * y) := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      ac_rfl
    _ = 8 * y ^ 3 := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

private theorem requestEnvelopeStepArithmetic (t f F : Nat) :
    2 * ((t + 1) * f) * ((t + 4) * F) * (t + 4) ^ 3 ≤
      (8 * (t + 1) * (t + 4)) *
        (2 * f * F * (t + 3) ^ 3) := by
  have hc := requestCubeDouble (t + 4) (t + 3) (by omega)
  calc
    2 * ((t + 1) * f) * ((t + 4) * F) * (t + 4) ^ 3 ≤
        2 * ((t + 1) * f) * ((t + 4) * F) *
          (8 * (t + 3) ^ 3) :=
      Nat.mul_le_mul_left _ hc
    _ = (8 * (t + 1) * (t + 4)) *
        (2 * f * F * (t + 3) ^ 3) := by ac_rfl

private theorem requestEnvelopeStep (t : Nat) :
    requestEnvelope (t + 1) ≤
      (8 * (t + 1) * (t + 4)) * requestEnvelope t := by
  have hf : freshFact (t + 1) = (t + 1) * freshFact t := rfl
  have hF : freshFact (t + 1 + 3) =
      (t + 4) * freshFact (t + 3) := by
    have he : t + 1 + 3 = (t + 3) + 1 := by omega
    rw [he] <;> rfl
  have he : t + 1 + 3 = t + 4 := by omega
  unfold requestEnvelope
  rw [hf, hF, he]
  exact requestEnvelopeStepArithmetic t (freshFact t) (freshFact (t + 3))

private theorem requestLinearBelowPower (t : Nat) (ht : 3 ≤ t) :
    t + 4 ≤ 2 ^ t := by
  have hall : ∀ k : Nat, (k + 3) + 4 ≤ 2 ^ (k + 3) := by
    intro k
    induction k with
    | zero =>
        change (7 : Nat) ≤ 8
        decide
    | succ k ih =>
        have he : k + 1 + 3 = (k + 3) + 1 := by omega
        rw [he, Nat.pow_succ]
        omega
  have hh := hall (t - 3)
  have he : t - 3 + 3 = t := by omega
  rw [he] at hh
  exact hh

private theorem requestLinearExponent (t : Nat) (ht : 6 ≤ t) :
    2 * t + 3 ≤ 2 ^ (t - 1) := by
  have hall : ∀ k : Nat,
      2 * (k + 6) + 3 ≤ 2 ^ ((k + 6) - 1) := by
    intro k
    induction k with
    | zero =>
        change (15 : Nat) ≤ 32
        decide
    | succ k ih =>
        have he : (k + 1 + 6) - 1 = ((k + 6) - 1) + 1 := by omega
        rw [he, Nat.pow_succ]
        omega
  have hh := hall (t - 6)
  have he : t - 6 + 6 = t := by omega
  rw [he] at hh
  exact hh

private theorem requestGrowthFactor (t : Nat) (ht : 6 ≤ t) :
    8 * (t + 1) * (t + 4) ≤ 2 ^ (2 ^ (t - 1)) := by
  have hlarge := requestLinearBelowPower t (by omega)
  have hsmall : t + 1 ≤ 2 ^ t := by omega
  have hprod : 8 * (t + 1) * (t + 4) ≤
      8 * (2 ^ t) * (2 ^ t) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 8 hsmall) hlarge
  have hexp := requestLinearExponent t ht
  calc
    8 * (t + 1) * (t + 4) ≤ 8 * (2 ^ t) * (2 ^ t) := hprod
    _ = 2 ^ (t + t + 3) := by
      rw [Nat.pow_add, Nat.pow_add]
      change 8 * (2 ^ t) * (2 ^ t) = ((2 ^ t) * (2 ^ t)) * 8
      ac_rfl
    _ ≤ 2 ^ (2 ^ (t - 1)) :=
      Nat.pow_le_pow_right (by decide) (by omega)

private theorem requestDyadicSquare (t : Nat) (ht : 1 ≤ t) :
    2 ^ (2 ^ ((t + 1) - 1)) =
      2 ^ (2 ^ (t - 1)) * 2 ^ (2 ^ (t - 1)) := by
  have he : t = (t - 1) + 1 := by omega
  have hdouble : 2 ^ t = 2 ^ (t - 1) + 2 ^ (t - 1) := by
    calc
      2 ^ t = 2 ^ ((t - 1) + 1) := congrArg (fun k : Nat => 2 ^ k) he
      _ = 2 ^ (t - 1) * 2 := Nat.pow_succ 2 (t - 1)
      _ = 2 ^ (t - 1) + 2 ^ (t - 1) := by omega
  rw [Nat.add_sub_cancel, hdouble, Nat.pow_add]

private theorem requestEnvelopeSix :
    requestEnvelope 6 ≤ 1048577 * 2 ^ (2 ^ (6 - 1)) := by
  change (380936908800 : Nat) ≤ 4503603922337792
  decide

private theorem requestEnvelopeDyadicBound (t : Nat) (ht : 6 ≤ t) :
    requestEnvelope t ≤ 1048577 * 2 ^ (2 ^ (t - 1)) := by
  have hall : ∀ k : Nat,
      requestEnvelope (k + 6) ≤
        1048577 * 2 ^ (2 ^ ((k + 6) - 1)) := by
    intro k
    induction k with
    | zero =>
        exact requestEnvelopeSix
    | succ k ih =>
        have he : k + 1 + 6 = (k + 6) + 1 := by omega
        rw [he]
        calc
          requestEnvelope ((k + 6) + 1) ≤
              (8 * ((k + 6) + 1) * ((k + 6) + 4)) *
                requestEnvelope (k + 6) := requestEnvelopeStep (k + 6)
          _ ≤ 2 ^ (2 ^ ((k + 6) - 1)) *
              (1048577 * 2 ^ (2 ^ ((k + 6) - 1))) :=
            Nat.mul_le_mul (requestGrowthFactor (k + 6) (by omega)) ih
          _ = 1048577 *
              (2 ^ (2 ^ ((k + 6) - 1)) *
                2 ^ (2 ^ ((k + 6) - 1))) := by ac_rfl
          _ = 1048577 * 2 ^ (2 ^ (((k + 6) + 1) - 1)) := by
            rw [requestDyadicSquare (k + 6) (by omega)]
  have hh := hall (t - 6)
  have he : t - 6 + 6 = t := by omega
  rw [he] at hh
  exact hh

/-- Part (c) holds for every t>=6; the estimate actually holds
    before adding the +1 in the population floor. -/
theorem requestProgressEnvelopeBound (t : Nat) (ht : 6 ≤ t) :
    requestProgressEnvelope t ≤
      1048577 * (2 ^ (2 ^ (t - 1)) + 1) := by
  calc
    requestProgressEnvelope t ≤ requestEnvelope t :=
      requestProgressBelowEnvelope t
    _ ≤ 1048577 * 2 ^ (2 ^ (t - 1)) := requestEnvelopeDyadicBound t ht
    _ ≤ 1048577 * (2 ^ (2 ^ (t - 1)) + 1) :=
      Nat.mul_le_mul_left 1048577 (by omega)

/-- Uniform large-width coupon coefficient, with the exact
    original numerator and denominator, not a rounded p_scan. -/
theorem requestCouponLargeWidth (t : Nat) (ht : 6 ≤ t) :
    (couponGPair t).1 ≤
      (couponGPair t).2 * (1048577 * (2 ^ (2 ^ (t - 1)) + 1)) := by
  exact Nat.le_trans (requestCouponProgressBound t)
    (Nat.mul_le_mul_left _ (requestProgressEnvelopeBound t ht))

/-! ## Finite-width certificates, using the exact fractions -/

private theorem requestRatioBound (A K a b r s : Nat)
    (hr : 0 < r) (hp : a * s = r * b)
    (hnum : A * s ≤ K * r) :
    A * b ≤ K * a := by
  have hs : r * (A * b) ≤ r * (K * a) := by
    calc
      r * (A * b) = A * (r * b) := by ac_rfl
      _ = A * (a * s) := by rw [hp]
      _ = (A * s) * a := by ac_rfl
      _ ≤ (K * r) * a := Nat.mul_le_mul_right a hnum
      _ = r * (K * a) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hs hr

private theorem requestMultiplyRatio (F A K a b : Nat)
    (h : A * b ≤ K * a) :
    (F * A) * b ≤ K * (F * a) := by
  calc
    (F * A) * b = F * (A * b) := by ac_rfl
    _ ≤ F * (K * a) := Nat.mul_le_mul_left F h
    _ = K * (F * a) := by ac_rfl

private theorem requestCouponTwoFloor :
    (couponGPair 2).1 ≤ 5963 * 5 * (couponGPair 2).2 := by
  change (2109120 : Nat) ≤ 5963 * 5 * 360
  decide

private theorem requestCouponFiveFloor :
    (couponGPair 5).1 ≤ 1154 * 65537 * (couponGPair 5).2 := by
  have hh : harmonicPair 8 = (109584, 40320) := by rfl
  have hf : freshFact 8 = 40320 := by rfl
  have hratio :
      5369635 * (pPair 5).2 ≤ (1154 * 65537) * (pPair 5).1 :=
    requestRatioBound 5369635 (1154 * 65537)
      (pPair 5).1 (pPair 5).2 767441 10800000
      (by decide) p_scan_five (by decide)
  change
    ((harmonicPair 8).1 * freshFact 8 * 7 ^ 2 +
      19 * (harmonicPair 8).2) * (pPair 5).2 ≤
    (1154 * 65537) * ((harmonicPair 8).2 * (pPair 5).1)
  rw [hh, hf]
  change (40320 * 5369635) * (pPair 5).2 ≤
    (1154 * 65537) * (40320 * (pPair 5).1)
  exact requestMultiplyRatio 40320 5369635 (1154 * 65537)
    (pPair 5).1 (pPair 5).2 hratio

private theorem requestBandLift (N D k m n : Nat)
    (h : N ≤ k * m * D) (hm : m ≤ n) :
    N ≤ D * ((k + 1) * n) := by
  calc
    N ≤ k * m * D := h
    _ ≤ ((k + 1) * n) * D :=
      Nat.mul_le_mul_right D (Nat.mul_le_mul (by omega : k ≤ k + 1) hm)
    _ = D * ((k + 1) * n) := Nat.mul_comm _ _

private theorem requestCouponTwo (n : Nat) (hn : 5 ≤ n) :
    (couponGPair 2).1 ≤ (couponGPair 2).2 * (5964 * n) := by
  exact requestBandLift (couponGPair 2).1 (couponGPair 2).2
    5963 5 n requestCouponTwoFloor hn

private theorem requestCouponThree (n : Nat) (hn : 17 ≤ n) :
    (couponGPair 3).1 ≤ (couponGPair 3).2 * (6094 * n) := by
  exact requestBandLift (couponGPair 3).1 (couponGPair 3).2
    6093 17 n couponG_three_band.2 hn

private theorem requestCouponFive (n : Nat) (hn : 65537 ≤ n) :
    (couponGPair 5).1 ≤ (couponGPair 5).2 * (1155 * n) := by
  exact requestBandLift (couponGPair 5).1 (couponGPair 5).2
    1154 65537 n requestCouponFiveFloor hn

/-! ## Population floors and literal selected-ledger projections -/

private theorem requestPopulationAfterAdvice (n a : Nat)
    (hn : 2 ≤ n) (ha : a + 1 ≤ ceilLogTwo n) :
    2 ^ a + 1 ≤ n := by
  have hlo := (ceilLogTwo_spec n hn).1
  have hp : 2 ^ a ≤ 2 ^ (ceilLogTwo n - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem requestLargePopulationFloor (n : Nat)
    (hn : 5 ≤ n) (hq : 33 ≤ ceilLogTwo n) :
    2 ^ (2 ^ (ceilLogTwo (ceilLogTwo n) - 1)) + 1 ≤ n := by
  have hinner := (ceilLogTwo_spec (ceilLogTwo n) (by omega)).1
  exact requestPopulationAfterAdvice n
    (2 ^ (ceilLogTwo (ceilLogTwo n) - 1)) (by omega) (by omega)

private theorem requestFiniteCheckerValue (q : Nat)
    (hthree : 3 ≤ q) (hmax : q ≤ 32) :
    (headlineFiniteLedger q).2.2 =
      (if q ≤ 4 then 5963 else if q ≤ 16 then 6093 else 1154) := by
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

private theorem requestLargeCheckerValue (s : Nat) (hs : 6 ≤ s) :
    (headlineLargeLedger s).2.2 = 1048576 := by
  unfold headlineLargeLedger
  split
  · rename_i hmax
    have hc : s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 ∨ s = 10 ∨
        s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 := by
      omega
    rcases hc with h | h | h | h | h | h | h | h | h | h | h <;>
      subst s <;> rfl
  · rfl

private theorem requestCheckerFinite (n : Nat)
    (hthree : 3 ≤ ceilLogTwo n) (hmax : ceilLogTwo n ≤ 32) :
    headlineCheckerRate n =
      (if ceilLogTwo n ≤ 4 then 5963
       else if ceilLogTwo n ≤ 16 then 6093 else 1154) := by
  unfold headlineCheckerRate headlineSelectedLedger
  rw [if_pos hmax]
  exact requestFiniteCheckerValue (ceilLogTwo n) hthree hmax

private theorem requestCheckerLarge (n : Nat)
    (hq : 33 ≤ ceilLogTwo n) :
    headlineCheckerRate n = 1048576 := by
  unfold headlineCheckerRate headlineSelectedLedger
  rw [if_neg (by omega : ¬ ceilLogTwo n ≤ 32)]
  exact requestLargeCheckerValue (ceilLogTwo (ceilLogTwo n))
    (ceilLogTwo_ge_six (ceilLogTwo n) hq)

/-- The exact numeric premise of requestRawExpectedOfCoefficient,
    now discharged for every headline population n>=5. -/
theorem requestCouponCoefficient (n : Nat) (hn : 5 ≤ n) :
    (CouponClear.couponGPair (compileAdvice (ceilLogTwo n)).t).1 ≤
      (CouponClear.couponGPair (compileAdvice (ceilLogTwo n)).t).2 *
        ((headlineCheckerRate n + 1) * n) := by
  have hq : 3 ≤ ceilLogTwo n := ceilLogTwo_ge_three n hn
  by_cases hfour : ceilLogTwo n ≤ 4
  · have ht : (compileAdvice (ceilLogTwo n)).t = 2 := by
      rw [compileAdvice_t_finite (ceilLogTwo n) hq (by omega)]
      unfold finiteCertWidth
      rw [if_pos hfour]
    have hr := requestCheckerFinite n hq (by omega)
    rw [if_pos hfour] at hr
    rw [ht, hr]
    exact requestCouponTwo n hn
  · by_cases hsixteen : ceilLogTwo n ≤ 16
    · have ht : (compileAdvice (ceilLogTwo n)).t = 3 := by
        rw [compileAdvice_t_finite (ceilLogTwo n) hq (by omega)]
        unfold finiteCertWidth
        rw [if_neg hfour, if_pos hsixteen]
      have hr := requestCheckerFinite n hq (by omega)
      rw [if_neg hfour, if_pos hsixteen] at hr
      have hpopulation : 17 ≤ n := by
        have hh := requestPopulationAfterAdvice n 4 (by omega) (by omega)
        exact hh
      rw [ht, hr]
      exact requestCouponThree n hpopulation
    · by_cases hthirtytwo : ceilLogTwo n ≤ 32
      · have ht : (compileAdvice (ceilLogTwo n)).t = 5 := by
          rw [compileAdvice_t_finite (ceilLogTwo n) hq hthirtytwo]
          unfold finiteCertWidth
          rw [if_neg hfour, if_neg hsixteen]
        have hr := requestCheckerFinite n hq hthirtytwo
        rw [if_neg hfour, if_neg hsixteen] at hr
        have hpopulation : 65537 ≤ n := by
          have hh := requestPopulationAfterAdvice n 16 (by omega) (by omega)
          exact hh
        rw [ht, hr]
        exact requestCouponFive n hpopulation
      · have hlarge : 33 ≤ ceilLogTwo n := by omega
        have ht := compileAdvice_t_large (ceilLogTwo n) hlarge
        have hr := requestCheckerLarge n hlarge
        have hwidth := ceilLogTwo_ge_six (ceilLogTwo n) hlarge
        have hpopulation := requestLargePopulationFloor n hn hlarge
        have hcoupon := requestCouponLargeWidth
          (ceilLogTwo (ceilLogTwo n)) hwidth
        have hscaled :
            (couponGPair (ceilLogTwo (ceilLogTwo n))).2 *
                (1048577 *
                  (2 ^ (2 ^ (ceilLogTwo (ceilLogTwo n) - 1)) + 1)) ≤
              (couponGPair (ceilLogTwo (ceilLogTwo n))).2 *
                (1048577 * n) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 1048577 hpopulation)
        rw [ht, hr]
        exact Nat.le_trans hcoupon hscaled

/-- The real raw-failure request clock, with no outstanding numeric
    premise. TOP-only failure is not among this theorem's hypotheses. -/
theorem requestRawExpected {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hg : headlineGrantReady ring C)
    (hl : ∀ i : Fin n, (C i).l = false)
    (hr : ∀ i : Fin n, (C i).req = false)
    (hbad : RequestRawFailure C s) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring) (requestStoppedTarget ring) C
      (((headlineCheckerRate n + 1) * n ^ 2 : Nat) : Rat) := by
  exact requestRawExpectedOfCoefficient ring hn C s hg hl hr hbad
    (CouponClear.couponGPair_den_pos ((compileAdvice (ceilLogTwo n)).t))
    (requestCouponCoefficient n hn)

end L3.HeadlineRequest
