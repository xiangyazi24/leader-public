import Leader.Core.LeaderCountDyadicTail

/-! Division-free uniform lower bound for an incoming-hit/no-outgoing block.
Natural subtraction is used only after proving the relevant partition. -/

set_option autoImplicit false

namespace BirthResponderHazardMassArithmetic

open LeaderCountDyadicTail

/-- The elementary lower Bernoulli bound, kept entirely in natural integers. -/
theorem survival_scaled (n t : Nat) (ht : t ≤ n) :
    (n - t) * n ^ t ≤ n * (n - 1) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have ht' : t ≤ n := by omega
      have hn : 0 < n := by omega
      have hc : (n - (t + 1)) * n ≤ (n - t) * (n - 1) := by
        have hs : n - t = n - (t + 1) + 1 := by omega
        have hn' : n = (n - 1) + 1 := by omega
        calc
          (n - (t + 1)) * n = (n - (t + 1)) * ((n - 1) + 1) := congrArg _ hn'
          _ = (n - (t + 1)) * (n - 1) + (n - (t + 1)) := by
            rw [Nat.mul_add, Nat.mul_one]
          _ ≤ (n - (t + 1)) * (n - 1) + (n - 1) := Nat.add_le_add_left (by omega) _
          _ = (n - t) * (n - 1) := by rw [hs, Nat.add_mul, Nat.one_mul]
      calc
        (n - (t + 1)) * n ^ (t + 1) = ((n - (t + 1)) * n) * n ^ t := by
          rw [Nat.pow_succ]
          ac_rfl
        _ ≤ ((n - t) * (n - 1)) * n ^ t := Nat.mul_le_mul_right _ hc
        _ = ((n - t) * n ^ t) * (n - 1) := by ac_rfl
        _ ≤ (n * (n - 1) ^ t) * (n - 1) := Nat.mul_le_mul_right _ (ih ht')
        _ = n * (n - 1) ^ (t + 1) := by rw [Nat.pow_succ, Nat.mul_assoc]

private theorem split_coefficient (n : Nat) (hn : 2 ≤ n) :
    n * (n + (n - 2)) ≤ 8 * ((n / 2) * (n - n / 2)) := by
  generalize hm : n / 2 = m
  have hmpos : 0 < m := by omega
  have hcases : n = m + m ∨ n = m + m + 1 := by omega
  rcases hcases with he | ho
  · have hs : n - m = m := by omega
    rw [hs]
    calc
      n * (n + (n - 2)) ≤ n * (n + n) := Nat.mul_le_mul_left _ (by omega)
      _ = 8 * (m * m) := by
        rw [he]
        simp [Nat.add_mul, Nat.mul_add]
        omega
  · have hs : n - m = m + 1 := by omega
    have hd : n + (n - 2) = m + m + m + m := by omega
    rw [hs, hd, ho]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega

/-- Exactly the candidate one-block count. Its interpretation as a count
is supplied by the companion counting module. -/
def blockNumerator (n : Nat) : Nat := (n - 1) ^ n - (n - 2) ^ n

theorem blockNumerator_partition (n : Nat) :
    blockNumerator n + (n - 2) ^ n = (n - 1) ^ n := by
  apply Nat.sub_add_cancel
  exact Nat.pow_le_pow_left (by omega) n

/-- An eighth of all `n^n` words suffice for every `n >= 2`.
The odd-size split is retained exactly, avoiding an unjustified quarter
survival estimate from rounding two half-blocks. -/
theorem one_block_eighth (n : Nat) (hn : 2 ≤ n) :
    n ^ n ≤ 8 * blockNumerator n := by
  let m := n / 2
  let k := n - m
  let P := (n - 1) ^ n
  let A := blockNumerator n
  let B := (n - 2) ^ n
  let D := n + (n - 2)
  have hm : 0 < m := by dsimp only [m]; omega
  have hk : 0 < k := by dsimp only [k, m]; omega
  have hmk : m + k = n := by dsimp only [k, m]; omega
  have hk' : n - k = m := by omega
  have hs1 := survival_scaled n m (by omega)
  have hs2 := survival_scaled n k (by omega)
  have hs : (m * k) * n ^ n ≤ (n * n) * P := by
    have hh := Nat.mul_le_mul hs1 hs2
    rw [hk'] at hh
    change (k * n ^ m) * (m * n ^ k) ≤ _ at hh
    calc
      (m * k) * n ^ n = (k * n ^ m) * (m * n ^ k) := by
        rw [← hmk, Nat.pow_add]
        ac_rfl
      _ ≤ (n * (n - 1) ^ m) * (n * (n - 1) ^ k) := hh
      _ = (n * n) * P := by
        dsimp only [P]
        rw [← hmk, Nat.pow_add]
        ac_rfl
  have hber := bernoulli_scaled (n - 2) n
  have hp : n - 2 + 1 = n - 1 := by omega
  rw [hp] at hber
  have hab : A + B = P := blockNumerator_partition n
  have hD : n * P ≤ D * A := by
    have hb : D * B ≤ (n - 2) * P := by
      simpa only [D, B, P, Nat.add_comm] using hber
    have he : D * A + D * B = n * P + (n - 2) * P := by
      rw [← Nat.mul_add, hab]
      exact Nat.add_mul n (n - 2) P
    omega
  have hc : n * D ≤ 8 * (m * k) := split_coefficient n hn
  have hscaled : (m * k) * n ^ n ≤ (m * k) * (8 * A) := by
    calc
      (m * k) * n ^ n ≤ (n * n) * P := hs
      _ = n * (n * P) := Nat.mul_assoc _ _ _
      _ ≤ n * (D * A) := Nat.mul_le_mul_left n hD
      _ = (n * D) * A := (Nat.mul_assoc _ _ _).symm
      _ ≤ (8 * (m * k)) * A := Nat.mul_le_mul_right A hc
      _ = (m * k) * (8 * A) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled (Nat.mul_pos hm hk)

theorem repeated_block_eighth (n blocks : Nat) (hn : 2 ≤ n) :
    n ^ (n * blocks) ≤ 8 ^ blocks * blockNumerator n ^ blocks := by
  have h := Nat.pow_le_pow_left (one_block_eighth n hn) blocks
  simpa only [Nat.mul_pow, ← Nat.pow_mul] using h

end BirthResponderHazardMassArithmetic

#print axioms BirthResponderHazardMassArithmetic.blockNumerator_partition
#print axioms BirthResponderHazardMassArithmetic.one_block_eighth
#print axioms BirthResponderHazardMassArithmetic.repeated_block_eighth
