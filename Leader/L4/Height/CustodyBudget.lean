import Leader.L4.Height.Constants

namespace L4.Height

/-- Smallest circumference in packed advice band s. -/
def packedBandMin (s : Nat) : Nat :=
  2 ^ (2 ^ (s - 1)) + 1

/-- Quadratic coefficient for the two radius costs and the geometry cost. -/
def custodyCoefficient (U C : Nat) : Nat :=
  (520 * U + 2 ^ 32) / (2 ^ 32 + 1) + 2 ^ 45 * fact 44 * C

/-- Multiplication by the denominator recovers the numerator of a
natural-number ceiling quotient, including the zero case. -/
private theorem nat_ceiling_lower (a d : Nat) (hd : 1 ≤ d) :
    a ≤ d * ((a + d - 1) / d) := by
  let q := (a + d - 1) / d
  change a ≤ d * q
  by_cases h : a ≤ d * q
  · exact h
  · have hlt : d * q < a := Nat.lt_of_not_ge h
    have hmul : (q + 1) * d ≤ a + d - 1 := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q d]
      omega
    have hq : q + 1 ≤ (a + d - 1) / d :=
      (Nat.le_div_iff_mul_le (by omega : 0 < d)).2 hmul
    have hqq : q + 1 ≤ q := by
      simpa [q] using hq
    omega

/-- Doubling the radius and advancing the exponent by eight
multiplies the physical certification horizon by at most 1024. -/
theorem radius_horizon_growth (k kNext J JNext : Nat)
    (hJ : 8 ≤ J) (hk : kNext ≤ 2 * k)
    (hInc : JNext ≤ J + 8) :
    4096 * kNext * JNext * 2 ^ JNext ≤
      1024 * (4096 * k * J * 2 ^ J) := by
  have hJnext : JNext ≤ 2 * J := by omega
  have hpow : 2 ^ JNext ≤ 256 * 2 ^ J := by
    calc
      2 ^ JNext ≤ 2 ^ (J + 8) :=
        Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hInc
      _ = 256 * 2 ^ J := by
        rw [Nat.pow_add]
        have hsmall : (2 : Nat) ^ 8 = 256 := by decide
        rw [hsmall]
        ac_rfl
  have hprod :
      kNext * JNext * 2 ^ JNext ≤
        (2 * k) * (2 * J) * (256 * 2 ^ J) :=
    Nat.mul_le_mul (Nat.mul_le_mul hk hJnext) hpow
  calc
    4096 * kNext * JNext * 2 ^ JNext =
        4096 * (kNext * JNext * 2 ^ JNext) := by ac_rfl
    _ ≤ 4096 * ((2 * k) * (2 * J) * (256 * 2 ^ J)) :=
      Nat.mul_le_mul_left 4096 hprod
    _ = (2 * 2 * 256) * (4096 * k * J * 2 ^ J) := by ac_rfl
    _ = 1024 * (4096 * k * J * 2 ^ J) := by
      rw [show (2 : Nat) * 2 * 256 = 1024 by decide]

/-- Every packed band's least size grows by at least 2048. -/
theorem packed_band_min_growth (s : Nat) (hs : 6 ≤ s) :
    2048 * packedBandMin s ≤ packedBandMin (s + 1) := by
  have hExponent : 5 ≤ s - 1 := by omega
  have hPowerExponent : 32 ≤ 2 ^ (s - 1) := by
    calc
      32 = (2 : Nat) ^ 5 := by decide
      _ ≤ 2 ^ (s - 1) :=
        Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hExponent
  let a : Nat := 2 ^ (2 ^ (s - 1))
  have haFull : 2 ^ 32 ≤ a :=
    Nat.pow_le_pow_right
      (by decide : 0 < (2 : Nat)) hPowerExponent
  have ha : 4096 ≤ a := by
    calc
      4096 = (2 : Nat) ^ 12 := by decide
      _ ≤ 2 ^ 32 :=
        Nat.pow_le_pow_right
          (by decide : 0 < (2 : Nat)) (by decide : 12 ≤ 32)
      _ ≤ a := haFull
  have hExponentNext :
      2 ^ ((s + 1) - 1) =
        2 ^ (s - 1) + 2 ^ (s - 1) := by
    have hindex : (s + 1) - 1 = (s - 1) + 1 := by omega
    rw [hindex, Nat.pow_succ]
    omega
  unfold packedBandMin
  rw [hExponentNext, Nat.pow_add]
  change 2048 * (a + 1) ≤ a * a + 1
  have hsquare : 2049 * a ≤ a * a :=
    Nat.mul_le_mul_right a (by omega : 2049 ≤ a)
  have hlinear : 2048 * (a + 1) ≤ 2049 * a := by omega
  omega

/-- The certification numerator grows by at most the band-width factor. -/
private theorem custody_numerator_growth
    (U₁ U₂ : Nat → Nat) (s : Nat)
    (hLeft : U₁ (s + 1) ≤ 1024 * U₁ s)
    (hRight : U₂ (s + 1) ≤ 1024 * U₂ s) :
    4 * (U₁ (s + 1) + U₂ (s + 1)) * (2 ^ (s + 1) + 1) ≤
      2048 * (4 * (U₁ s + U₂ s) * (2 ^ s + 1)) := by
  have hsum :
      U₁ (s + 1) + U₂ (s + 1) ≤
        1024 * (U₁ s + U₂ s) := by
    calc
      U₁ (s + 1) + U₂ (s + 1) ≤
          1024 * U₁ s + 1024 * U₂ s :=
        Nat.add_le_add hLeft hRight
      _ = 1024 * (U₁ s + U₂ s) := by rw [Nat.mul_add]
  have htop : 2 ^ (s + 1) + 1 ≤ 2 * (2 ^ s + 1) := by
    rw [Nat.pow_succ]
    omega
  have hprod :
      (U₁ (s + 1) + U₂ (s + 1)) * (2 ^ (s + 1) + 1) ≤
        (1024 * (U₁ s + U₂ s)) * (2 * (2 ^ s + 1)) :=
    Nat.mul_le_mul hsum htop
  calc
    4 * (U₁ (s + 1) + U₂ (s + 1)) * (2 ^ (s + 1) + 1) =
        4 * ((U₁ (s + 1) + U₂ (s + 1)) *
          (2 ^ (s + 1) + 1)) := by ac_rfl
    _ ≤ 4 * ((1024 * (U₁ s + U₂ s)) *
          (2 * (2 ^ s + 1))) := Nat.mul_le_mul_left 4 hprod
    _ = (1024 * 2) * (4 * (U₁ s + U₂ s) * (2 ^ s + 1)) := by
      ac_rfl
    _ = 2048 * (4 * (U₁ s + U₂ s) * (2 ^ s + 1)) := by
      rw [show (1024 : Nat) * 2 = 2048 by decide]

/-- Uniform certification numerator divided by the minimum circumference
is controlled by the first packed advice band. -/
private theorem custody_band_factor
    (U₁ U₂ : Nat → Nat)
    (hGrowth : ∀ s, 6 ≤ s →
      U₁ (s + 1) ≤ 1024 * U₁ s ∧
        U₂ (s + 1) ≤ 1024 * U₂ s)
    (hFirst : U₁ 6 ≤ U₂ 6)
    (s : Nat) (hs : 6 ≤ s) :
    4 * (U₁ s + U₂ s) * (2 ^ s + 1) ≤
      ((520 * U₂ 6 + 2 ^ 32) / (2 ^ 32 + 1)) *
        packedBandMin s := by
  let c : Nat := (520 * U₂ 6 + 2 ^ 32) / (2 ^ 32 + 1)
  have hceil : 520 * U₂ 6 ≤ (2 ^ 32 + 1) * c := by
    have hd : 1 ≤ 2 ^ 32 + 1 := by omega
    have hshift :
        520 * U₂ 6 + (2 ^ 32 + 1) - 1 =
          520 * U₂ 6 + 2 ^ 32 := by omega
    calc
      520 * U₂ 6 ≤
          (2 ^ 32 + 1) *
            ((520 * U₂ 6 + (2 ^ 32 + 1) - 1) /
              (2 ^ 32 + 1)) :=
        nat_ceiling_lower (520 * U₂ 6) (2 ^ 32 + 1) hd
      _ = (2 ^ 32 + 1) * c := by
        rw [hshift]
  have hbandFirst : packedBandMin 6 = 2 ^ 32 + 1 := by rfl
  have hfirstSum : U₁ 6 + U₂ 6 ≤ 2 * U₂ 6 := by omega
  have hbaseNumerator :
      4 * (U₁ 6 + U₂ 6) * (2 ^ 6 + 1) ≤
        520 * U₂ 6 := by
    calc
      4 * (U₁ 6 + U₂ 6) * (2 ^ 6 + 1) ≤
          4 * (2 * U₂ 6) * (2 ^ 6 + 1) :=
        Nat.mul_le_mul_right (2 ^ 6 + 1)
          (Nat.mul_le_mul_left 4 hfirstSum)
      _ = 520 * U₂ 6 := by
        have hpow : (2 : Nat) ^ 6 + 1 = 65 := by decide
        rw [hpow]
        omega
  have hbase :
      4 * (U₁ 6 + U₂ 6) * (2 ^ 6 + 1) ≤
        c * packedBandMin 6 := by
    calc
      4 * (U₁ 6 + U₂ 6) * (2 ^ 6 + 1) ≤
          520 * U₂ 6 := hbaseNumerator
      _ ≤ (2 ^ 32 + 1) * c := hceil
      _ = c * packedBandMin 6 := by
        rw [hbandFirst]
        exact Nat.mul_comm _ _
  have hbands : ∀ t : Nat,
      4 * (U₁ (6 + t) + U₂ (6 + t)) * (2 ^ (6 + t) + 1) ≤
        c * packedBandMin (6 + t) := by
    intro t
    induction t with
    | zero =>
        simpa only [Nat.add_zero] using hbase
    | succ t ih =>
        have hj : 6 ≤ 6 + t := by omega
        have hg := hGrowth (6 + t) hj
        have hnumerator :=
          custody_numerator_growth U₁ U₂ (6 + t) hg.1 hg.2
        have hdenominator :=
          packed_band_min_growth (6 + t) hj
        have hnext :
            4 * (U₁ ((6 + t) + 1) + U₂ ((6 + t) + 1)) *
                (2 ^ ((6 + t) + 1) + 1) ≤
              c * packedBandMin ((6 + t) + 1) := by
          calc
            4 * (U₁ ((6 + t) + 1) + U₂ ((6 + t) + 1)) *
                (2 ^ ((6 + t) + 1) + 1) ≤
                2048 * (4 * (U₁ (6 + t) + U₂ (6 + t)) *
                  (2 ^ (6 + t) + 1)) := hnumerator
            _ ≤ 2048 * (c * packedBandMin (6 + t)) :=
              Nat.mul_le_mul_left 2048 ih
            _ = c * (2048 * packedBandMin (6 + t)) := by ac_rfl
            _ ≤ c * packedBandMin ((6 + t) + 1) :=
              Nat.mul_le_mul_left c hdenominator
        simpa only [Nat.add_assoc] using hnext
  have hindex : 6 + (s - 6) = s := by omega
  simpa only [hindex] using hbands (s - 6)

/-- Normalize the first two physical packed-band costs by n squared.
This is conditional on the supplied per-radius horizon bounds. -/
theorem custody_budget_all_bands
    (U₁ U₂ : Nat → Nat)
    (hGrowth : ∀ s, 6 ≤ s →
      U₁ (s + 1) ≤ 1024 * U₁ s ∧
        U₂ (s + 1) ≤ 1024 * U₂ s)
    (hFirst : U₁ 6 ≤ U₂ 6)
    (s n C₂ : Nat)
    (hs : 6 ≤ s) (hMin : packedBandMin s ≤ n)
    (hTop : ceilingLogTwo n ≤ 2 ^ s) :
    4 * n * (U₁ s + U₂ s) * (ceilingLogTwo n + 1) +
      C₂ * n * (1 + ceilingLogTwo n) ^ 44
      ≤ custodyCoefficient (U₂ 6) C₂ * n ^ 2 := by
  let c : Nat := (520 * U₂ 6 + 2 ^ 32) / (2 ^ 32 + 1)
  have hband :
      4 * (U₁ s + U₂ s) * (2 ^ s + 1) ≤
        c * packedBandMin s :=
    custody_band_factor U₁ U₂ hGrowth hFirst s hs
  have hn : 1 ≤ n := by
    have hpositive : 1 ≤ packedBandMin s := by
      unfold packedBandMin
      change (0 : Nat) + 1 ≤ 2 ^ (2 ^ (s - 1)) + 1
      exact Nat.add_le_add_right (Nat.zero_le _) 1
    omega
  have hheight : ceilingLogTwo n + 1 ≤ 2 ^ s + 1 := by omega
  have hlinear :
      4 * (U₁ s + U₂ s) * (ceilingLogTwo n + 1) ≤
        c * n := by
    calc
      4 * (U₁ s + U₂ s) * (ceilingLogTwo n + 1) ≤
          4 * (U₁ s + U₂ s) * (2 ^ s + 1) :=
        Nat.mul_le_mul_left (4 * (U₁ s + U₂ s)) hheight
      _ ≤ c * packedBandMin s := hband
      _ ≤ c * n := Nat.mul_le_mul_left c hMin
  have hcertification :
      4 * n * (U₁ s + U₂ s) * (ceilingLogTwo n + 1) ≤
        c * n ^ 2 := by
    calc
      4 * n * (U₁ s + U₂ s) * (ceilingLogTwo n + 1) =
          n * (4 * (U₁ s + U₂ s) * (ceilingLogTwo n + 1)) := by
        ac_rfl
      _ ≤ n * (c * n) := Nat.mul_le_mul_left n hlinear
      _ = c * n ^ 2 := by
        simp only [Nat.pow_two]
        ac_rfl
  have hgeometry :
      C₂ * n * (1 + ceilingLogTwo n) ^ 44 ≤
        (2 ^ 45 * fact 44 * C₂) * n ^ 2 := by
    calc
      C₂ * n * (1 + ceilingLogTwo n) ^ 44 ≤
          C₂ * n * (2 ^ 45 * fact 44 * n) :=
        Nat.mul_le_mul_left (C₂ * n) (clog_bound n hn)
      _ = (2 ^ 45 * fact 44 * C₂) * n ^ 2 := by
        simp only [Nat.pow_two]
        ac_rfl
  have hsum := Nat.add_le_add hcertification hgeometry
  calc
    4 * n * (U₁ s + U₂ s) * (ceilingLogTwo n + 1) +
        C₂ * n * (1 + ceilingLogTwo n) ^ 44 ≤
        c * n ^ 2 + (2 ^ 45 * fact 44 * C₂) * n ^ 2 := hsum
    _ = (c + 2 ^ 45 * fact 44 * C₂) * n ^ 2 := by
      rw [Nat.add_mul]
    _ = custodyCoefficient (U₂ 6) C₂ * n ^ 2 := by rfl

end L4.Height

