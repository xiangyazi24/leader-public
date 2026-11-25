import Leader.L4.Height.Core

namespace L4.Height

set_option maxHeartbeats 2000000

/-- Factorial, with `fact 0 = 1`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Pascal binomial coefficients. -/
def choose : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- The zeroth binomial coefficient. -/
theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by
  cases n <;> rfl

/-- The first binomial coefficient. -/
theorem choose_succ_one (n : Nat) : choose (n + 1) 1 = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change choose (n + 1) 0 + choose (n + 1) 1 = n + 2
      rw [choose_zero_right, ih]
      omega

/-- The multiplicative Pascal identity
`(k+1) choose(n+1,k+1) = (n+1) choose(n,k)`. -/
theorem choose_mul_succ (n k : Nat) :
    (k + 1) * choose (n + 1) (k + 1) =
      (n + 1) * choose n k := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [choose]
  | succ n ih =>
      cases k with
      | zero =>
          rw [choose_succ_one, choose_zero_right]
          omega
      | succ k =>
          change
            (k + 2) *
                (choose (n + 1) (k + 1) +
                  choose (n + 1) (k + 2)) =
              (n + 2) * (choose n k + choose n (k + 1))
          have hleft := ih k
          have hright := ih (k + 1)
          have hpascal :
              choose (n + 1) (k + 1) =
                choose n k + choose n (k + 1) := rfl
          have houter :
              (k + 2) *
                  (choose (n + 1) (k + 1) +
                    choose (n + 1) (k + 2)) =
                (k + 2) * choose (n + 1) (k + 1) +
                  (k + 2) * choose (n + 1) (k + 2) := by
            exact Nat.mul_add _ _ _
          have hsplit :
              (k + 2) * choose (n + 1) (k + 1) =
                (k + 1) * choose (n + 1) (k + 1) +
                  choose (n + 1) (k + 1) := by
            calc
              (k + 2) * choose (n + 1) (k + 1) =
                  ((k + 1) + 1) * choose (n + 1) (k + 1) := by
                    have hk : k + 2 = (k + 1) + 1 := by omega
                    rw [hk]
              _ = (k + 1) * choose (n + 1) (k + 1) +
                    1 * choose (n + 1) (k + 1) := by
                    rw [Nat.add_mul]
              _ = (k + 1) * choose (n + 1) (k + 1) +
                    choose (n + 1) (k + 1) := by
                    rw [Nat.one_mul]
          have htarget :
              (n + 2) * (choose n k + choose n (k + 1)) =
                (n + 1) * choose n k +
                  (n + 1) * choose n (k + 1) +
                    (choose n k + choose n (k + 1)) := by
            calc
              (n + 2) * (choose n k + choose n (k + 1)) =
                  ((n + 1) + 1) *
                    (choose n k + choose n (k + 1)) := by
                    have hn : n + 2 = (n + 1) + 1 := by omega
                    rw [hn]
              _ = (n + 1) * (choose n k + choose n (k + 1)) +
                    1 * (choose n k + choose n (k + 1)) := by
                    rw [Nat.add_mul]
              _ = (n + 1) * choose n k +
                    (n + 1) * choose n (k + 1) +
                      (choose n k + choose n (k + 1)) := by
                    rw [Nat.mul_add, Nat.one_mul]
          calc
            (k + 2) *
                (choose (n + 1) (k + 1) +
                  choose (n + 1) (k + 2)) =
              (k + 2) * choose (n + 1) (k + 1) +
                (k + 2) * choose (n + 1) (k + 2) := houter
            _ = ((k + 1) * choose (n + 1) (k + 1) +
                  choose (n + 1) (k + 1)) +
                (k + 2) * choose (n + 1) (k + 2) := by
                  rw [hsplit]
            _ = ((n + 1) * choose n k +
                  choose (n + 1) (k + 1)) +
                (n + 1) * choose n (k + 1) := by
                  rw [hleft, hright]
            _ = (n + 1) * choose n k +
                  (n + 1) * choose n (k + 1) +
                    choose (n + 1) (k + 1) := by
                  ac_rfl
            _ = (n + 1) * choose n k +
                  (n + 1) * choose n (k + 1) +
                    (choose n k + choose n (k + 1)) := by
                  rw [hpascal]
            _ = (n + 2) * (choose n k + choose n (k + 1)) :=
                  htarget.symm

/-- The shifted factorial identity for the binomial coefficient. -/
theorem choose_shifted_identity (u d : Nat) :
    fact d * choose (u + d) d =
      (List.range d).foldl (fun z i => z * (u + i + 1)) 1 := by
  induction d with
  | zero =>
      simp [fact, choose_zero_right]
  | succ d ih =>
      have hmul := choose_mul_succ (u + d) d
      calc
        fact (d + 1) * choose (u + (d + 1)) (d + 1) =
            fact d *
              ((d + 1) * choose ((u + d) + 1) (d + 1)) := by
                have hu : u + (d + 1) = (u + d) + 1 := by omega
                rw [fact, hu]
                ac_rfl
        _ = fact d * (((u + d) + 1) * choose (u + d) d) := by
              rw [hmul]
        _ = (fact d * choose (u + d) d) * (u + d + 1) := by
              ac_rfl
        _ = (List.range d).foldl
              (fun z i => z * (u + i + 1)) 1 * (u + d + 1) := by
              rw [ih]
        _ = (List.range (d + 1)).foldl
              (fun z i => z * (u + i + 1)) 1 := by
              rw [List.range_succ, List.foldl_append]
              rfl

/-- The binomial coefficient is bounded by the full row sum. -/
theorem choose_le_two_pow (n k : Nat) :
    choose n k ≤ 2 ^ n := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [choose]
  | succ n ih =>
      cases k with
      | zero =>
          rw [choose_zero_right]
          have hp : 0 < 2 ^ (n + 1) := Nat.pow_pos (by omega)
          omega
      | succ k =>
          change choose n k + choose n (k + 1) ≤ 2 ^ (n + 1)
          have hleft := ih k
          have hright := ih (k + 1)
          have hsum :
              choose n k + choose n (k + 1) ≤
                2 ^ n + 2 ^ n := Nat.add_le_add hleft hright
          calc
            choose n k + choose n (k + 1)
                ≤ 2 ^ n + 2 ^ n := hsum
            _ = 2 ^ (n + 1) := by
                  rw [Nat.pow_succ]
                  omega

/-- The polynomial is bounded by factorial times the shifted binomial. -/
theorem pow_le_fact_choose (u d : Nat) :
    (1 + u) ^ d ≤ fact d * choose (u + d) d := by
  rw [choose_shifted_identity]
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.pow_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact Nat.mul_le_mul ih (by omega)

/-- Ceiling base-two logarithm: zero at zero and one, and
`log2 (n-1)+1` thereafter. -/
def ceilingLogTwo (n : Nat) : Nat :=
  if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- The nontrivial branch of `ceilingLogTwo`. -/
theorem ceilingLogTwo_eq (n : Nat) (hn : 2 ≤ n) :
    ceilingLogTwo n = Nat.log2 (n - 1) + 1 := by
  unfold ceilingLogTwo
  have h : ¬ n ≤ 1 := by omega
  rw [if_neg h]

/-- The defining two-sided power interval for the ceiling logarithm. -/
theorem ceilingLogTwo_spec (n : Nat) (hn : 2 ≤ n) :
    2 ^ (ceilingLogTwo n - 1) < n ∧
      n ≤ 2 ^ ceilingLogTwo n := by
  rw [ceilingLogTwo_eq n hn]
  have hne : n - 1 ≠ 0 := by omega
  have hlog := (Nat.log2_eq_iff hne).1 rfl
  simp only [Nat.add_sub_cancel]
  omega

/-- A power of two at the ceiling-log scale is at most twice `n`. -/
theorem ceilingLog2_upper (n : Nat) (hn : 1 ≤ n) :
    2 ^ ceilingLogTwo n ≤ 2 * n := by
  by_cases hsmall : n ≤ 1
  · have hnEq : n = 1 := by omega
    subst n
    simp [ceilingLogTwo]
  · have hnTwo : 2 ≤ n := by omega
    rw [ceilingLogTwo_eq n hnTwo]
    have hne : n - 1 ≠ 0 := by omega
    have hlog := (Nat.log2_eq_iff hne).1 rfl
    calc
      2 ^ (Nat.log2 (n - 1) + 1) =
          2 ^ Nat.log2 (n - 1) * 2 := by
            rw [Nat.pow_succ]
      _ ≤ (n - 1) * 2 := Nat.mul_le_mul_right 2 hlog.1
      _ ≤ 2 * n := by omega

/-- Geometry's logarithmic factor is linear in `n` after the ceiling step. -/
theorem clog_bound (n : Nat) (hn : 1 ≤ n) :
    (1 + ceilingLogTwo n) ^ 44 ≤ 2 ^ 45 * fact 44 * n := by
  have hpoly := pow_le_fact_choose (ceilingLogTwo n) 44
  have hchoose := choose_le_two_pow (ceilingLogTwo n + 44) 44
  have hchooseScaled :
      fact 44 * choose (ceilingLogTwo n + 44) 44 ≤
        fact 44 * 2 ^ (ceilingLogTwo n + 44) :=
    Nat.mul_le_mul_left _ hchoose
  have hfirst := Nat.le_trans hpoly hchooseScaled
  have hceil := ceilingLog2_upper n hn
  have hpowfortyfive : (2 : Nat) ^ 45 = 2 ^ 44 * 2 := by
    change (2 : Nat) ^ (44 + 1) = 2 ^ 44 * 2
    exact Nat.pow_succ 2 44
  have htwo :
      2 ^ (ceilingLogTwo n + 44) ≤ 2 ^ 45 * n := by
    rw [Nat.pow_add]
    calc
      2 ^ ceilingLogTwo n * 2 ^ 44
          ≤ (2 * n) * 2 ^ 44 :=
            Nat.mul_le_mul_right _ hceil
      _ = (2 ^ 44 * 2) * n := by ac_rfl
      _ = 2 ^ 45 * n := by rw [← hpowfortyfive]
  have htwoScaled :
      fact 44 * 2 ^ (ceilingLogTwo n + 44) ≤
        fact 44 * (2 ^ 45 * n) :=
    Nat.mul_le_mul_left _ htwo
  have htotal := Nat.le_trans hfirst htwoScaled
  calc
    (1 + ceilingLogTwo n) ^ 44
        ≤ fact 44 * (2 ^ 45 * n) := htotal
    _ = 2 ^ 45 * fact 44 * n := by ac_rfl

/-- The physical anchor/clock/display contribution. -/
theorem anchor_physical (bL n r m : Nat) (hmr : m * r ≤ n) :
    (8 + 2 ^ 30) * (2 ^ (5 * bL + 34) * n * r) * m
      ≤ 2 ^ (5 * bL + 65) * n ^ 2 := by
  have hc : 8 + 2 ^ 30 ≤ 2 ^ 31 := by omega
  have hprod : r * m ≤ n := by
    calc
      r * m = m * r := Nat.mul_comm _ _
      _ ≤ n := hmr
  have hpowers :
      2 ^ 31 * 2 ^ (5 * bL + 34) = 2 ^ (5 * bL + 65) := by
    calc
      2 ^ 31 * 2 ^ (5 * bL + 34) =
          2 ^ (31 + (5 * bL + 34)) :=
            (Nat.pow_add 2 31 (5 * bL + 34)).symm
      _ = 2 ^ (5 * bL + 65) := by
            rw [show 31 + (5 * bL + 34) = 5 * bL + 65 by omega]
  calc
    (8 + 2 ^ 30) * (2 ^ (5 * bL + 34) * n * r) * m =
        (8 + 2 ^ 30) *
          (2 ^ (5 * bL + 34) * n * (r * m)) := by
            ac_rfl
    _ ≤ 2 ^ 31 *
          (2 ^ (5 * bL + 34) * n * (r * m)) :=
            Nat.mul_le_mul_right _ hc
    _ = (2 ^ 31 * 2 ^ (5 * bL + 34) * n) * (r * m) := by
          ac_rfl
    _ ≤ (2 ^ 31 * 2 ^ (5 * bL + 34) * n) * n :=
          Nat.mul_le_mul_left _ hprod
    _ = 2 ^ (5 * bL + 65) * n ^ 2 := by
          rw [hpowers]
          simp only [Nat.pow_two]
          ac_rfl

/-- The observer contribution is at most seven quadratic units. -/
theorem observer (n : Nat) (hn : 4 ≤ n) :
    5 * n ^ 2 + 7 * n ≤ 7 * n ^ 2 := by
  have hbase : 7 ≤ 2 * n := by omega
  have hmul := Nat.mul_le_mul_right n hbase
  have hlinear : 7 * n ≤ 2 * n ^ 2 := by
    calc
      7 * n ≤ (2 * n) * n := hmul
      _ = 2 * n ^ 2 := by
            simp only [Nat.pow_two]
            ac_rfl
  calc
    5 * n ^ 2 + 7 * n
        ≤ 5 * n ^ 2 + 2 * n ^ 2 :=
          Nat.add_le_add_left hlinear _
    _ = (5 + 2) * n ^ 2 := by rw [Nat.add_mul]
    _ = 7 * n ^ 2 := by rfl

/-- Add five independently bounded contributions. -/
theorem sum_to_K
    (c₁ c₂ c₃ c₄ c₅ a₁ a₂ a₃ a₄ a₅ n : Nat)
    (h₁ : c₁ ≤ a₁ * n ^ 2)
    (h₂ : c₂ ≤ a₂ * n ^ 2)
    (h₃ : c₃ ≤ a₃ * n ^ 2)
    (h₄ : c₄ ≤ a₄ * n ^ 2)
    (h₅ : c₅ ≤ a₅ * n ^ 2) :
    c₁ + c₂ + c₃ + c₄ + c₅
      ≤ (a₁ + a₂ + a₃ + a₄ + a₅) * n ^ 2 := by
  have hsTwelve := Nat.add_le_add h₁ h₂
  have hsThree := Nat.add_le_add hsTwelve h₃
  have hsFour := Nat.add_le_add hsThree h₄
  have hsFive := Nat.add_le_add hsFour h₅
  calc
    c₁ + c₂ + c₃ + c₄ + c₅
        ≤ (((a₁ * n ^ 2 + a₂ * n ^ 2) + a₃ * n ^ 2) +
          a₄ * n ^ 2) + a₅ * n ^ 2 := hsFive
    _ = (a₁ + a₂ + a₃ + a₄ + a₅) * n ^ 2 := by
          simp only [Nat.add_mul]

end L4.Height
