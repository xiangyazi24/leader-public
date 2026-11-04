import Leader.L3.Bank.RepairDigitAllPairsClock

/-!
# R10c: the 201 ledger with the composed structural clock

`widthStructuralClockOfPairs` charges the structural stage `3 ((L + 3) (2 c)) + 2`
(`L = ceilLogTwo n`). With the paper's per-pair clock `c = n h(r)` (Lemma e-packet,
`h = bankRepairDigitPairEnvelope`), this is at most `3 P_pair n + 2`, about 1.5 times the
structural micro-charge `2 P_pair n` (`P_pair = 4 h (2^{s-1} + 3)` and `L ≤ 2^s`). The loss is the
Markov half block (factor 2) and the doubled renewal ceiling, against the paper's moment
argument (`lem:e-max`, `E z^T < 40`); the logarithm is paid once in both.

The BANK total still fits: the non-wave part is at most `(2 ν + 5 P) n + 2 ≤ 7 ν n + 2`, and
`8 ν_s < 2^{2^{s-1}} < n` (`nuEightOfGrowth`, the same induction as
`bankRepairDigitNuSixOfGrowth` with factor 8; base `8 ν_7 < 2^64`).
-/

namespace L3.DigitStructuralFit

open L3
open L3.RenewalReferenceClock

set_option autoImplicit false

/-- The base width with factor eight. Consumer: `nuEightOfGrowth`. -/
theorem nuBaseEight : 8 * bankRepairDigitNu 7 < 2 ^ bankRepairDigitExponent 7 := by
  have hclosed : 8 * 860812189133 + 1 ≤ (2 : Nat) ^ 64 := Nat.le_of_ble_eq_true rfl
  rw [bankRepairDigitNuBase]
  change 8 * 860812189133 < (2 : Nat) ^ 64
  omega

/-- The exponent doubles with the width. Consumer: `nuEightOfGrowth`. -/
theorem powerSucc (s : Nat) (hs : 1 ≤ s) :
    2 ^ bankRepairDigitExponent (s + 1) =
      2 ^ bankRepairDigitExponent s * 2 ^ bankRepairDigitExponent s := by
  have hstep : bankRepairDigitExponent (s + 1) =
      bankRepairDigitExponent s + bankRepairDigitExponent s := by
    unfold bankRepairDigitExponent
    rw [show s + 1 - 1 = s by omega]
    have h : 2 ^ s = 2 ^ (s - 1) * 2 := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    omega
  rw [hstep, Nat.pow_add]

/-- **`8 ν_s < 2^{2^{s-1}}` at every BANK width**: the growth induction of
`bankRepairDigitNuSixOfGrowth` with factor eight. Consumer: `structuralLedgerFit`. -/
theorem nuEightOfGrowth (s : Nat) (hs : 7 ≤ s) :
    8 * bankRepairDigitNu s < 2 ^ bankRepairDigitExponent s := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, s = 7 + k := ⟨s - 7, by omega⟩
  induction k with
  | zero => simpa only [Nat.add_zero] using nuBaseEight
  | succ k ih =>
    have hgrowth := bankRepairDigitNuGrowthProved (7 + k) (by omega)
    have hpos : 0 < 2 ^ bankRepairDigitExponent (7 + k) := Nat.pow_pos (by omega)
    have hle : 8 * bankRepairDigitNu (7 + k + 1) ≤
        (8 * bankRepairDigitNu (7 + k)) * 2 ^ bankRepairDigitExponent (7 + k) := by
      calc 8 * bankRepairDigitNu (7 + k + 1) ≤
            8 * (bankRepairDigitNu (7 + k) * 2 ^ bankRepairDigitExponent (7 + k)) :=
            Nat.mul_le_mul_left 8 hgrowth
        _ = (8 * bankRepairDigitNu (7 + k)) * 2 ^ bankRepairDigitExponent (7 + k) := by ac_rfl
    have hlt : (8 * bankRepairDigitNu (7 + k)) * 2 ^ bankRepairDigitExponent (7 + k) <
        2 ^ bankRepairDigitExponent (7 + k) * 2 ^ bankRepairDigitExponent (7 + k) :=
      Nat.mul_lt_mul_of_pos_right (ih (by omega)) hpos
    have hnext : 8 * bankRepairDigitNu (7 + k + 1) < 2 ^ bankRepairDigitExponent (7 + k + 1) := by
      rw [powerSucc (7 + k) (by omega)]
      exact Nat.lt_of_le_of_lt hle hlt
    simpa only [Nat.add_succ] using hnext

/-- **The BANK ledger with the composed structural clock fits 201**: boundary, first zero, the
structural charge of `widthStructuralClockOfPairs` at the paper's per-pair clock
`c = n h(r)`, the entry charge `6 n (5 R + 2 + L)`, the `200 n^2` wave and the comparison stage
total at most `201 n^2`. Consumer: the R10c digit half-stage composition with the structural
premise of `widthDigitValueWaveOfStructural` (in place of `entryLedgerFit`'s
`bankRepairDigitStructuralMicroCharge`). -/
theorem structuralLedgerFit {n : Nat} (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    bankRepairDigitBoundaryMicroCharge n + bankRepairDigitFirstZeroMicroCharge n +
        (3 * ((ceilLogTwo n + 3) * (2 * (n * bankRepairDigitPairEnvelope
          (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)))))) + 2) +
        6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) +
        bankRepairDigitValueWaveMicroCharge n + bankRepairDigitComparisonMicroCharge n ≤
      201 * n ^ 2 := by
  have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
  have ht : (compileAdvice (ceilLogTwo n)).t = ceilLogTwo (ceilLogTwo n) :=
    compileAdvice_t_large _ (by omega)
  have hs7 : 7 ≤ ceilLogTwo (ceilLogTwo n) := bankRepairDigitWidthBank hbank
  have h8 := nuEightOfGrowth (ceilLogTwo (ceilLogTwo n)) hs7
  have hpop := bankRepairDigitPopulationLower hn hbank
  have hP := bankRepairDigitPairUpperLeNu (ceilLogTwo (ceilLogTwo n))
  have hL : ceilLogTwo n ≤ 2 ^ ceilLogTwo (ceilLogTwo n) :=
    (ceilLogTwo_spec (ceilLogTwo n) (by omega)).2
  have heq : bankRepairDigitBoundaryMicroCharge n + bankRepairDigitFirstZeroMicroCharge n +
        bankRepairDigitStructuralMicroCharge n + bankRepairDigitValueWaveMicroCharge n +
        bankRepairDigitComparisonMicroCharge n =
      2 * (bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) +
        bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n))) * n + 200 * n ^ 2 := by
    unfold bankRepairDigitBoundaryMicroCharge bankRepairDigitFirstZeroMicroCharge
      bankRepairDigitStructuralMicroCharge bankRepairDigitValueWaveMicroCharge
      bankRepairDigitComparisonMicroCharge bankRepairDigitNu
    simp only [Nat.mul_add, Nat.add_mul]
    ac_rfl
  have hS : bankRepairDigitStructuralMicroCharge n =
      2 * (bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n)) * n) := by
    unfold bankRepairDigitStructuralMicroCharge
    rw [Nat.mul_assoc]
  -- the entry numerator is below 2 P (as in entryLedgerFit)
  have hPlow : 6 * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) ≤
      2 * bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n)) := by
    unfold digitSpan
    rw [ht]
    unfold bankRepairDigitPairUpper bankRepairDigitPairEnvelope bankRepairDigitRadius
      bankRepairDigitExponent
    generalize hsv : ceilLogTwo (ceilLogTwo n) = s at hs7 hL ⊢
    have h2s : 2 ^ s = 2 * 2 ^ (s - 1) := by
      rw [show s = (s - 1) + 1 by omega, Nat.pow_succ]
      simp only [Nat.add_sub_cancel]
      ac_rfl
    generalize hr : 2 ^ s - 1 = r
    generalize hE : 2 ^ (s - 1) = E at h2s
    have hE2 : ceilLogTwo n ≤ 2 * E := by omega
    generalize ha : 12 * r ^ 4 + 40 * r ^ 3 + 18 * r ^ 2 + 36 * r + 10 = a
    have ha1 : 36 * r + 10 ≤ a := by omega
    have hab1 : a * 3 ≤ a * (E + 3) := Nat.mul_le_mul_left a (by omega)
    have hab2 : 10 * (E + 3) ≤ a * (E + 3) := Nat.mul_le_mul_right (E + 3) (by omega)
    have hexp : 4 * a * (E + 3) = 4 * (a * (E + 3)) := by ac_rfl
    rw [hexp]
    omega
  -- the composed structural charge is at most 3 P n + 2
  have hLE : ceilLogTwo n ≤ 2 * bankRepairDigitExponent (ceilLogTwo (ceilLogTwo n)) := by
    unfold bankRepairDigitExponent
    have h2s : 2 ^ ceilLogTwo (ceilLogTwo n) = 2 * 2 ^ (ceilLogTwo (ceilLogTwo n) - 1) := by
      have h : 2 ^ ceilLogTwo (ceilLogTwo n) = 2 ^ (ceilLogTwo (ceilLogTwo n) - 1) * 2 := by
        rw [← Nat.pow_succ]
        congr 1
        omega
      omega
    omega
  have hS' : 3 * ((ceilLogTwo n + 3) * (2 * (n * bankRepairDigitPairEnvelope
        (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)))))) + 2 ≤
      3 * (bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n)) * n) + 2 := by
    generalize hm : n * bankRepairDigitPairEnvelope
      (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) = m
    have h3 : bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n)) * n =
        4 * ((bankRepairDigitExponent (ceilLogTwo (ceilLogTwo n)) + 3) * m) := by
      rw [← hm]
      unfold bankRepairDigitPairUpper
      ac_rfl
    have h1 : (ceilLogTwo n + 3) * (2 * m) ≤
        (2 * (bankRepairDigitExponent (ceilLogTwo (ceilLogTwo n)) + 3)) * (2 * m) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (2 * (bankRepairDigitExponent (ceilLogTwo (ceilLogTwo n)) + 3)) * (2 * m) =
        2 * 2 * ((bankRepairDigitExponent (ceilLogTwo (ceilLogTwo n)) + 3) * m) := by ac_rfl
    omega
  have hentry : 6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) ≤
      2 * (bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n)) * n) := by
    have h := Nat.mul_le_mul_right n hPlow
    have e1 : 6 * n * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) =
        6 * (5 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 + ceilLogTwo n) * n := by ac_rfl
    have e2 : 2 * bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n)) * n =
        2 * (bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n)) * n) := Nat.mul_assoc _ _ _
    omega
  have hA : 2 * (bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) +
        bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n))) * n =
      2 * (bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) * n) +
        2 * (bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n)) * n) := by
    rw [Nat.mul_assoc, Nat.add_mul, Nat.mul_add]
  have hPn : bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n)) * n ≤
      bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) * n := Nat.mul_le_mul_right n hP
  have h7 : 7 * bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) + 2 ≤ n := by omega
  have hmul := Nat.mul_le_mul_right n h7
  have hexp : (7 * bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) + 2) * n =
      7 * (bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) * n) + 2 * n := by
    rw [Nat.add_mul, Nat.mul_assoc]
  have hsq : n ^ 2 = n * n := Nat.pow_two n
  omega

end L3.DigitStructuralFit

#print axioms L3.DigitStructuralFit.nuBaseEight
#print axioms L3.DigitStructuralFit.powerSucc
#print axioms L3.DigitStructuralFit.nuEightOfGrowth
#print axioms L3.DigitStructuralFit.structuralLedgerFit
