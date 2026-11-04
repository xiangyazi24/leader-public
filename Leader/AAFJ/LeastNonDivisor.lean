import Lean

namespace AAFJExactN

/-! ## Constructive least nondivisor -/

private def firstNonDivisor (n start fuel : Nat) : Nat :=
  match fuel with
  | 0 => start
  | fuel + 1 =>
      if start ∣ n then firstNonDivisor n (start + 1) fuel else start

/-- The least integer `k ≥ 2` which does not divide `n`, for positive `n`.
The definition is total; its specification below assumes `0 < n`. -/
def leastNonDivisor (n : Nat) : Nat :=
  firstNonDivisor n 2 n

private theorem firstNonDivisor_spec
    (n start fuel : Nat) (hn : 0 < n) (hcover : n < start + fuel) :
    start ≤ firstNonDivisor n start fuel ∧
      ¬ firstNonDivisor n start fuel ∣ n ∧
      ∀ j, start ≤ j → j < firstNonDivisor n start fuel → j ∣ n := by
  induction fuel generalizing start with
  | zero =>
      simp only [firstNonDivisor]
      refine ⟨Nat.le_refl _, ?_, ?_⟩
      · intro hdiv
        have hle : start ≤ n := Nat.le_of_dvd hn hdiv
        omega
      · intro j hj hjlt
        omega
  | succ fuel ih =>
      simp only [firstNonDivisor]
      by_cases hs : start ∣ n
      · rw [if_pos hs]
        rcases ih (start := start + 1) (by omega) with
          ⟨hlo, hnd, hmin⟩
        refine ⟨by omega, hnd, ?_⟩
        intro j hj hjlt
        by_cases hjs : j = start
        · simpa [hjs] using hs
        · exact hmin j (by omega) hjlt
      · rw [if_neg hs]
        refine ⟨Nat.le_refl _, hs, ?_⟩
        intro j hj hjlt
        omega

theorem leastNonDivisor_spec (n : Nat) (hn : 0 < n) :
    2 ≤ leastNonDivisor n ∧
      ¬ leastNonDivisor n ∣ n ∧
      ∀ j, 2 ≤ j → j < leastNonDivisor n → j ∣ n := by
  unfold leastNonDivisor
  exact firstNonDivisor_spec n 2 n hn (by omega)

theorem exists_leastNonDivisor (n : Nat) (hn : 0 < n) :
    ∃ k, 2 ≤ k ∧ ¬ k ∣ n ∧ ∀ j, 2 ≤ j → j < k → j ∣ n :=
  ⟨leastNonDivisor n, leastNonDivisor_spec n hn⟩

theorem leastNonDivisor_ge_two {n : Nat} (hn : 0 < n) :
    2 ≤ leastNonDivisor n :=
  (leastNonDivisor_spec n hn).1

theorem leastNonDivisor_not_dvd {n : Nat} (hn : 0 < n) :
    ¬ leastNonDivisor n ∣ n :=
  (leastNonDivisor_spec n hn).2.1

theorem dvd_of_lt_leastNonDivisor {n j : Nat} (hn : 0 < n)
    (h2 : 2 ≤ j) (hj : j < leastNonDivisor n) : j ∣ n :=
  (leastNonDivisor_spec n hn).2.2 j h2 hj

/-! ## Prefix least common multiples -/

/-- `prefixLcm m = lcm(1,2,...,m)`, with the empty prefix equal to `1`. -/
def prefixLcm : Nat → Nat
  | 0 => 1
  | m + 1 => Nat.lcm (prefixLcm m) (m + 1)

@[simp] theorem prefixLcm_zero : prefixLcm 0 = 1 := rfl
@[simp] theorem prefixLcm_succ (m : Nat) :
    prefixLcm (m + 1) = Nat.lcm (prefixLcm m) (m + 1) := rfl

theorem prefixLcm_dvd_iff (m t : Nat) :
    prefixLcm m ∣ t ↔ ∀ j, 1 ≤ j → j ≤ m → j ∣ t := by
  induction m with
  | zero =>
      constructor
      · intro _ j hj1 hj0
        omega
      · intro _
        exact Nat.one_dvd t
  | succ m ih =>
      rw [prefixLcm_succ, Nat.lcm_dvd_iff, ih]
      constructor
      · rintro ⟨hprev, hlast⟩ j hj1 hjm
        rcases Nat.lt_or_eq_of_le hjm with hjlt | rfl
        · exact hprev j hj1 (by omega)
        · exact hlast
      · intro h
        refine ⟨?_, h (m + 1) (by omega) (by omega)⟩
        intro j hj1 hjm
        exact h j hj1 (by omega)

theorem prefixLcm_pos : ∀ m : Nat, 0 < prefixLcm m
  | 0 => by simp [prefixLcm]
  | m + 1 => by
      rw [prefixLcm_succ]
      exact Nat.lcm_pos (prefixLcm_pos m) (by omega)

/-- On the exact-size family `n = lcm(1,…,m)`, every candidate modulus at
most `m` divides `n`.  Hence the least usable AAFJ modulus is strictly larger
than `m`.  This is the elementary obstruction to reclassifying the explicit
`Fin k` carrier as polyloglogarithmically many local states. -/
theorem prefixLcm_lt_leastNonDivisor (m : Nat) :
    m < leastNonDivisor (prefixLcm m) := by
  have hn : 0 < prefixLcm m := prefixLcm_pos m
  have hk2 : 2 ≤ leastNonDivisor (prefixLcm m) :=
    leastNonDivisor_ge_two hn
  apply Nat.lt_of_not_ge
  intro hkm
  have hall := (prefixLcm_dvd_iff m (prefixLcm m)).1
    (Nat.dvd_refl (prefixLcm m))
  have hkdiv : leastNonDivisor (prefixLcm m) ∣ prefixLcm m :=
    hall (leastNonDivisor (prefixLcm m)) (by omega) hkm
  exact (leastNonDivisor_not_dvd hn) hkdiv

/-! ## A core-only binomial triangle -/

/-- Pascal's binomial coefficient, defined locally to avoid Mathlib. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

private theorem binom_eq_zero_of_lt {n k : Nat} (h : n < k) :
    binom n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => simp [binom]
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          simp only [binom]
          rw [ih (k := k) (by omega), ih (k := k + 1) (by omega)]

private theorem binom_pos_of_le {n k : Nat} (h : k ≤ n) :
    0 < binom n k := by
  induction n generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      simp [binom]
  | succ n ih =>
      cases k with
      | zero => simp [binom]
      | succ k =>
          simp only [binom]
          have hp := ih (k := k) (by omega)
          omega

private theorem binom_diag : ∀ n : Nat, binom n n = 1
  | 0 => rfl
  | n + 1 => by
      simp only [binom]
      rw [binom_diag n,
        binom_eq_zero_of_lt (n := n) (k := n + 1) (by omega)]

/-- Two elementary multiplicative identities for adjacent Pascal entries. -/
private theorem binom_vertical_adjacent (n : Nat) :
    (∀ k, k ≤ n →
      (n + 1 - k) * binom (n + 1) k = (n + 1) * binom n k) ∧
    (∀ k, k ≤ n →
      (k + 1) * binom (n + 1) (k + 1) =
        (n + 1 - k) * binom (n + 1) k) := by
  induction n with
  | zero =>
      constructor
      · intro k hk
        have hk0 : k = 0 := by omega
        subst k
        rfl
      · intro k hk
        have hk0 : k = 0 := by omega
        subst k
        rfl
  | succ n ih =>
      rcases ih with ⟨hvPrev, haPrev⟩
      have hvCurrent : ∀ k, k ≤ n + 1 →
          (n + 2 - k) * binom (n + 2) k =
            (n + 2) * binom (n + 1) k := by
        intro k hk
        cases k with
        | zero => simp [binom]
        | succ k =>
            have hk' : k ≤ n := by omega
            have ha := haPrev k hk'
            simp only [binom]
            have hcoef : n + 2 - (k + 1) = n + 1 - k := by omega
            rw [hcoef, Nat.mul_add, ← ha]
            change
              (k + 1) * (binom n k + binom n (k + 1)) +
                  (n + 1 - k) * (binom n k + binom n (k + 1)) =
                (n + 2) * (binom n k + binom n (k + 1))
            rw [← Nat.add_mul]
            have hsum : (k + 1) + (n + 1 - k) = n + 2 := by omega
            rw [hsum]
      refine ⟨hvCurrent, ?_⟩
      intro k hk
      have hv := hvCurrent k hk
      by_cases htop : k = n + 1
      · subst k
        simpa [binom_diag] using hv.symm
      · have hk' : k ≤ n := by omega
        have ha := haPrev k hk'
        rw [hv]
        change
          (k + 1) *
              (binom (n + 1) k + binom (n + 1) (k + 1)) =
            (n + 2) * binom (n + 1) k
        rw [Nat.mul_add, ha, ← Nat.add_mul]
        have hsum : (k + 1) + (n + 1 - k) = n + 2 := by omega
        rw [hsum]

private theorem binom_vertical {n k : Nat} (hk : k ≤ n) :
    (n + 1 - k) * binom (n + 1) k = (n + 1) * binom n k :=
  (binom_vertical_adjacent n).1 k hk

private theorem binom_adjacent {n k : Nat} (hk : k ≤ n) :
    (k + 1) * binom (n + 1) (k + 1) =
      (n + 1 - k) * binom (n + 1) k :=
  (binom_vertical_adjacent n).2 k hk

/-! ## Leibniz denominator triangle and local LCM exchange -/

/-- Integer denominator in the Leibniz harmonic triangle. -/
def leibniz (n k : Nat) : Nat :=
  (n + 1) * binom n k

private theorem leibniz_pos {n k : Nat} (hk : k ≤ n) :
    0 < leibniz n k := by
  exact Nat.mul_pos (by omega) (binom_pos_of_le hk)

private theorem leibniz_up_entry {n k : Nat} (hk : k ≤ n) :
    (n + 2) * leibniz n k =
      (n + 1 - k) * leibniz (n + 1) k := by
  have hv := binom_vertical hk
  simp only [leibniz]
  rw [← hv]
  ac_rfl

private theorem leibniz_right_entry {n k : Nat} (hk : k ≤ n) :
    (n + 2) * leibniz n k =
      (k + 1) * leibniz (n + 1) (k + 1) := by
  have hv := binom_vertical hk
  have ha := binom_adjacent hk
  have hcore : (n + 1) * binom n k =
      (k + 1) * binom (n + 1) (k + 1) := by
    calc
      (n + 1) * binom n k =
          (n + 1 - k) * binom (n + 1) k := hv.symm
      _ = (k + 1) * binom (n + 1) (k + 1) := ha.symm
  simp only [leibniz]
  rw [hcore]
  ac_rfl

private theorem lcm_exchange_of_triplet
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (_hc : 0 < c)
    (htrip : a * b = c * (b - a)) :
    Nat.lcm b a = Nat.lcm b c := by
  have hab : a ≤ b := by
    by_cases hle : a ≤ b
    · exact hle
    · have hba : b < a := by omega
      have hz : b - a = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hba)
      have hzero : a * b = 0 := by rw [htrip, hz, Nat.mul_zero]
      have hpos : 0 < a * b := Nat.mul_pos ha hb
      omega
  have hg : a * Nat.gcd b c = c * Nat.gcd b a := by
    calc
      a * Nat.gcd b c = Nat.gcd (a * b) (a * c) :=
        (Nat.gcd_mul_left a b c).symm
      _ = Nat.gcd (c * (b - a)) (a * c) := by rw [htrip]
      _ = Nat.gcd (c * (b - a)) (c * a) := by rw [Nat.mul_comm a c]
      _ = c * Nat.gcd (b - a) a := Nat.gcd_mul_left c (b - a) a
      _ = c * Nat.gcd b a := by rw [Nat.gcd_sub_self_left hab]
  have hcancel : 0 < a * Nat.gcd b c :=
    Nat.mul_pos ha (Nat.gcd_pos_of_pos_left c hb)
  apply Nat.eq_of_mul_eq_mul_right hcancel
  calc
    Nat.lcm b a * (a * Nat.gcd b c) =
        Nat.lcm b a * (c * Nat.gcd b a) := by rw [hg]
    _ = c * (Nat.lcm b a * Nat.gcd b a) := by ac_rfl
    _ = c * (b * a) := by rw [Nat.lcm_mul_gcd]
    _ = a * (b * c) := by ac_rfl
    _ = a * (Nat.lcm b c * Nat.gcd b c) := by rw [Nat.lcm_mul_gcd]
    _ = Nat.lcm b c * (a * Nat.gcd b c) := by ac_rfl

private theorem leibniz_triplet_property {n k : Nat} (hk : k ≤ n) :
    leibniz n k * leibniz (n + 1) k =
      leibniz (n + 1) (k + 1) *
        (leibniz (n + 1) k - leibniz n k) := by
  let a := leibniz n k
  let b := leibniz (n + 1) k
  let c := leibniz (n + 1) (k + 1)
  have hup : (n + 2) * a = (n + 1 - k) * b := by
    simpa [a, b] using leibniz_up_entry hk
  have hright : (n + 2) * a = (k + 1) * c := by
    simpa [a, c] using leibniz_right_entry hk
  have hdiff : (n + 2) * (b - a) = (k + 1) * b := by
    rw [Nat.mul_sub, hup, ← Nat.sub_mul]
    have hcoef : n + 2 - (n + 1 - k) = k + 1 := by omega
    rw [hcoef]
  change a * b = c * (b - a)
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < n + 2)
  calc
    (n + 2) * (a * b) = ((n + 2) * a) * b :=
      (Nat.mul_assoc (n + 2) a b).symm
    _ = ((k + 1) * c) * b := by rw [hright]
    _ = c * ((k + 1) * b) := by ac_rfl
    _ = c * ((n + 2) * (b - a)) := by rw [← hdiff]
    _ = (n + 2) * (c * (b - a)) := by ac_rfl

private theorem leibniz_triplet_lcm {n k : Nat} (hk : k ≤ n) :
    Nat.lcm (leibniz (n + 1) k) (leibniz n k) =
      Nat.lcm (leibniz (n + 1) k) (leibniz (n + 1) (k + 1)) := by
  exact lcm_exchange_of_triplet
    (leibniz_pos hk)
    (leibniz_pos (by omega : k ≤ n + 1))
    (leibniz_pos (by omega : k + 1 ≤ n + 1))
    (leibniz_triplet_property hk)

/-! ## Row LCM equals the consecutive prefix LCM -/

def rowTailLcm (n start : Nat) : Nat → Nat
  | 0 => 1
  | fuel + 1 =>
      Nat.lcm (leibniz n start) (rowTailLcm n (start + 1) fuel)

def rowLcm (n : Nat) : Nat :=
  rowTailLcm n 0 (n + 1)

private theorem rowTail_wriggle
    (n start fuel : Nat) (hshape : start + fuel = n + 1) :
    Nat.lcm (leibniz (n + 1) start) (rowTailLcm n start fuel) =
      rowTailLcm (n + 1) start (fuel + 1) := by
  induction fuel generalizing start with
  | zero =>
      simp [rowTailLcm]
  | succ fuel ih =>
      have hk : start ≤ n := by omega
      have hshape' : start + 1 + fuel = n + 1 := by omega
      change
        Nat.lcm (leibniz (n + 1) start)
            (Nat.lcm (leibniz n start)
              (rowTailLcm n (start + 1) fuel)) =
          Nat.lcm (leibniz (n + 1) start)
            (rowTailLcm (n + 1) (start + 1) (fuel + 1))
      calc
        Nat.lcm (leibniz (n + 1) start)
            (Nat.lcm (leibniz n start)
              (rowTailLcm n (start + 1) fuel)) =
          Nat.lcm
            (Nat.lcm (leibniz (n + 1) start) (leibniz n start))
            (rowTailLcm n (start + 1) fuel) :=
              (Nat.lcm_assoc _ _ _).symm
        _ = Nat.lcm
            (Nat.lcm (leibniz (n + 1) start)
              (leibniz (n + 1) (start + 1)))
            (rowTailLcm n (start + 1) fuel) := by
              rw [leibniz_triplet_lcm hk]
        _ = Nat.lcm (leibniz (n + 1) start)
            (Nat.lcm (leibniz (n + 1) (start + 1))
              (rowTailLcm n (start + 1) fuel)) :=
              Nat.lcm_assoc _ _ _
        _ = Nat.lcm (leibniz (n + 1) start)
            (rowTailLcm (n + 1) (start + 1) (fuel + 1)) := by
              rw [ih (start := start + 1) hshape']

private theorem rowLcm_succ (n : Nat) :
    rowLcm (n + 1) = Nat.lcm (n + 2) (rowLcm n) := by
  have h := rowTail_wriggle n 0 (n + 1) (by omega)
  simpa [rowLcm, leibniz, binom] using h.symm

private theorem rowLcm_eq_prefixLcm_succ (n : Nat) :
    rowLcm n = prefixLcm (n + 1) := by
  induction n with
  | zero =>
      simp [rowLcm, rowTailLcm, prefixLcm, leibniz, binom]
  | succ n ih =>
      rw [rowLcm_succ, ih]
      change Nat.lcm (n + 2) (prefixLcm (n + 1)) =
        Nat.lcm (prefixLcm (n + 1)) (n + 2)
      exact Nat.lcm_comm _ _

private theorem rowLcm_pos (n : Nat) : 0 < rowLcm n := by
  rw [rowLcm_eq_prefixLcm_succ]
  exact prefixLcm_pos _

/-! ## Row sums -/

def binomPrefixSum (n : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => binomPrefixSum n m + binom n m

private theorem binomPrefixSum_succ (n m : Nat) :
    binomPrefixSum n (m + 1) = binomPrefixSum n m + binom n m := rfl

private theorem binomPrefixSum_pascal (n m : Nat) :
    binomPrefixSum (n + 1) (m + 1) =
      binomPrefixSum n m + binomPrefixSum n (m + 1) := by
  induction m with
  | zero => simp [binomPrefixSum, binom]
  | succ m ih =>
      calc
        binomPrefixSum (n + 1) ((m + 1) + 1) =
            binomPrefixSum (n + 1) (m + 1) +
              binom (n + 1) (m + 1) :=
                binomPrefixSum_succ (n + 1) (m + 1)
        _ = (binomPrefixSum n m + binomPrefixSum n (m + 1)) +
              (binom n m + binom n (m + 1)) := by
                rw [ih]
                rfl
        _ = binomPrefixSum n (m + 1) +
              (binomPrefixSum n (m + 1) + binom n (m + 1)) := by
                simp only [binomPrefixSum_succ n m]
                ac_rfl
        _ = binomPrefixSum n (m + 1) +
              binomPrefixSum n ((m + 1) + 1) := by
                exact congrArg (fun x => binomPrefixSum n (m + 1) + x)
                  (binomPrefixSum_succ n (m + 1)).symm

def binomRowSum (n : Nat) : Nat :=
  binomPrefixSum n (n + 1)

private theorem binomRowSum_succ (n : Nat) :
    binomRowSum (n + 1) = 2 * binomRowSum n := by
  have hp := binomPrefixSum_pascal n (n + 1)
  have hz : binom n (n + 1) = 0 := binom_eq_zero_of_lt (by omega)
  have hstep :
      binomPrefixSum n ((n + 1) + 1) = binomPrefixSum n (n + 1) := by
    rw [binomPrefixSum_succ, hz, Nat.add_zero]
  rw [hstep] at hp
  simpa [binomRowSum, Nat.two_mul] using hp

private theorem binomRowSum_eq_pow_two : ∀ n : Nat,
    binomRowSum n = 2 ^ n
  | 0 => by simp [binomRowSum, binomPrefixSum, binom]
  | n + 1 => by
      rw [binomRowSum_succ, binomRowSum_eq_pow_two n, Nat.pow_succ]
      ac_rfl

def leibnizPrefixSum (n : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => leibnizPrefixSum n m + leibniz n m

private theorem leibnizPrefixSum_succ (n m : Nat) :
    leibnizPrefixSum n (m + 1) =
      leibnizPrefixSum n m + leibniz n m := rfl

private theorem leibnizPrefixSum_eq_mul (n m : Nat) :
    leibnizPrefixSum n m = (n + 1) * binomPrefixSum n m := by
  induction m with
  | zero => simp [leibnizPrefixSum, binomPrefixSum]
  | succ m ih =>
      rw [leibnizPrefixSum_succ, binomPrefixSum_succ, ih]
      simp only [leibniz, Nat.mul_add]

private theorem leibnizRowSum_eq (n : Nat) :
    leibnizPrefixSum n (n + 1) = (n + 1) * 2 ^ n := by
  rw [leibnizPrefixSum_eq_mul]
  change (n + 1) * binomRowSum n = (n + 1) * 2 ^ n
  rw [binomRowSum_eq_pow_two]

/-! ## Every row entry divides the row LCM -/

private theorem leibniz_dvd_rowTailLcm
    (n start fuel j : Nat) (hlo : start ≤ j) (hi : j < start + fuel) :
    leibniz n j ∣ rowTailLcm n start fuel := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
      simp only [rowTailLcm]
      by_cases hjs : j = start
      · subst j
        exact Nat.dvd_lcm_left _ _
      · have htail : leibniz n j ∣ rowTailLcm n (start + 1) fuel :=
          ih (start := start + 1) (by omega) (by omega)
        exact Nat.dvd_trans htail (Nat.dvd_lcm_right _ _)

private theorem leibniz_dvd_rowLcm {n k : Nat} (hk : k ≤ n) :
    leibniz n k ∣ rowLcm n := by
  unfold rowLcm
  exact leibniz_dvd_rowTailLcm n 0 (n + 1) k (by omega) (by omega)

private theorem leibniz_le_rowLcm {n k : Nat} (hk : k ≤ n) :
    leibniz n k ≤ rowLcm n :=
  Nat.le_of_dvd (rowLcm_pos n) (leibniz_dvd_rowLcm hk)

private theorem leibnizPrefixSum_le_rowLcm_mul
    (n m : Nat) (hm : m ≤ n + 1) :
    leibnizPrefixSum n m ≤ m * rowLcm n := by
  induction m with
  | zero => simp [leibnizPrefixSum]
  | succ m ih =>
      rw [leibnizPrefixSum_succ, Nat.succ_mul]
      exact Nat.add_le_add (ih (by omega)) (leibniz_le_rowLcm (by omega))

/-! ## Exponential lower bound for consecutive LCM -/

private theorem two_pow_le_rowLcm (n : Nat) :
    2 ^ n ≤ rowLcm n := by
  have hsum := leibnizPrefixSum_le_rowLcm_mul n (n + 1) (by omega)
  rw [leibnizRowSum_eq] at hsum
  exact Nat.le_of_mul_le_mul_left hsum (by omega)

theorem two_pow_le_prefixLcm_succ (n : Nat) :
    2 ^ n ≤ prefixLcm (n + 1) := by
  simpa [rowLcm_eq_prefixLcm_succ] using two_pow_le_rowLcm n

theorem two_pow_pred_le_prefixLcm (m : Nat) :
    2 ^ (m - 1) ≤ prefixLcm m := by
  cases m with
  | zero => simp [prefixLcm]
  | succ m => simpa using two_pow_le_prefixLcm_succ m

/-! ## Minimality bridge and logarithmic AAFJ state bound -/

theorem prefixLcm_before_least_dvd {n : Nat} (hn : 0 < n) :
    prefixLcm (leastNonDivisor n - 1) ∣ n := by
  rw [prefixLcm_dvd_iff]
  intro j hj1 hjk
  by_cases h1 : j = 1
  · subst j
    exact Nat.one_dvd n
  · have hk2 := leastNonDivisor_ge_two hn
    exact dvd_of_lt_leastNonDivisor hn (by omega) (by omega)

theorem prefixLcm_before_least_le {n : Nat} (hn : 0 < n) :
    prefixLcm (leastNonDivisor n - 1) ≤ n :=
  Nat.le_of_dvd hn (prefixLcm_before_least_dvd hn)

theorem leastNonDivisor_le_log2_add_two {n : Nat} (hn : 0 < n) :
    leastNonDivisor n ≤ Nat.log2 n + 2 := by
  let k := leastNonDivisor n
  have hk2 : 2 ≤ k := leastNonDivisor_ge_two hn
  have hlower := two_pow_pred_le_prefixLcm (k - 1)
  have hsub : (k - 1) - 1 = k - 2 := by omega
  rw [hsub] at hlower
  have hupper : prefixLcm (k - 1) ≤ n := by
    simpa [k] using prefixLcm_before_least_le hn
  have hpow : 2 ^ (k - 2) ≤ n := Nat.le_trans hlower hupper
  have hlog : k - 2 ≤ Nat.log2 n :=
    (Nat.le_log2 (Nat.ne_of_gt hn)).2 hpow
  omega

theorem leastNonDivisor_one : leastNonDivisor 1 = 2 := by
  have hlo := leastNonDivisor_ge_two (n := 1) (by decide)
  have hhi := leastNonDivisor_le_log2_add_two (n := 1) (by decide)
  have hlog : Nat.log2 1 = 0 := by
    rw [Nat.log2_def]
    simp
  rw [hlog] at hhi
  omega

/-- Literal carrier size of the generalized `P_k` branch at `k = snd(n)`. -/
def pkStateCount (n : Nat) : Nat :=
  16 * leastNonDivisor n

theorem pkStateCount_le_log2 {n : Nat} (hn : 0 < n) :
    pkStateCount n ≤ 16 * Nat.log2 n + 32 := by
  unfold pkStateCount
  have hk := leastNonDivisor_le_log2_add_two hn
  calc
    16 * leastNonDivisor n ≤ 16 * (Nat.log2 n + 2) :=
      Nat.mul_le_mul_left 16 hk
    _ = 16 * Nat.log2 n + 32 := by omega

theorem pkStateCount_le_48_log2 {n : Nat} (hn : 2 ≤ n) :
    pkStateCount n ≤ 48 * Nat.log2 n := by
  have hs := pkStateCount_le_log2 (n := n) (by omega)
  have hlog : 1 ≤ Nat.log2 n := by
    rw [Nat.log2_def n, if_pos hn]
    omega
  omega

/-- Actual carrier size of the corrected exact-size family, including its
dedicated one- and two-agent protocols. -/
def exactFamilyStateCount (n : Nat) : Nat :=
  if n = 1 then 1 else if n = 2 then 2 else pkStateCount n

@[simp] theorem exactFamilyStateCount_one : exactFamilyStateCount 1 = 1 := by
  simp [exactFamilyStateCount]

@[simp] theorem exactFamilyStateCount_two : exactFamilyStateCount 2 = 2 := by
  simp [exactFamilyStateCount]

theorem exactFamilyStateCount_le_log2 {n : Nat} (hn : 0 < n) :
    exactFamilyStateCount n ≤ 16 * Nat.log2 n + 32 := by
  by_cases h1 : n = 1
  · subst n
    simp [exactFamilyStateCount]
  · by_cases h2 : n = 2
    · subst n
      simp [exactFamilyStateCount]
    · simp only [exactFamilyStateCount, h1, h2, if_false]
      exact pkStateCount_le_log2 hn

theorem exactFamilyStateCount_le_48_log2 {n : Nat} (hn : 2 ≤ n) :
    exactFamilyStateCount n ≤ 48 * Nat.log2 n := by
  by_cases h2 : n = 2
  · subst n
    have hlog : Nat.log2 2 = 1 := by decide
    simp [exactFamilyStateCount, hlog]
  · have h1 : n ≠ 1 := by omega
    simp only [exactFamilyStateCount, h1, h2, if_false]
    exact pkStateCount_le_48_log2 hn

end AAFJExactN
