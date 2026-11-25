import Leader.L3.Bank.TrialRenewal
import Leader.L3.Prime.SignedParams

/-!
# Compiled BANK spatial integer cutoffs

The C.17 result is only the
frozen-union UPPER cutoff, not the frozen success LOWER bound.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Paper C.12, C.13's radius reserve, and the 2048 floor reserve,
collected from existing source theorems for the same R. -/
theorem grantCutoffsCompiledRadiusReserves
    (n R : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2) :
    1024 *
      (224 * ((compileAdvice (ceilLogTwo n)).b + 2) +
        32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
          ((compileAdvice (ceilLogTwo n)).K + 2)) ≤ R ∧
    1024 *
      ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) +
        32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
          ((compileAdvice (ceilLogTwo n)).K + 1) +
        32 * ((compileAdvice (ceilLogTwo n)).b + 1)) ≤ R ∧
    2048 ≤ R * n := by
  exact ⟨grantClockSpatialPaperRadiusCutoff n R hn hsp hradius,
    grantClockSpatialCThirteenRadius n R hn hsp hradius,
    grantClockSpatialRadiusPopulationProduct
      n R hn hsp hradius⟩

/-- Cross-multiplied C.14 failure-duration coefficient. -/
theorem grantCutoffsCompiledFailureCoefficient
    (q : Nat)
    (hsp : (compileAdvice q).useSmall = false) :
    (8 * (compileAdvice q).b + 12) * 2 ^ (compileAdvice q).K <
      (8 * (compileAdvice q).b + 13) *
        (2 ^ (compileAdvice q).K - 1) := by
  exact grantClockSpatialC14Coefficient q
    (grantClockSpatialAdviceEighty q hsp)

/-- A quotient bound with completely opaque numerator and divisor. -/
private theorem grantCutoffsIndexFloorOpaque
    (a f H : Nat)
    (hf : 0 < f) (h : H * f ≤ a) :
    H ≤ a / f := by
  by_cases hSmall : H ≤ a / f
  · exact hSmall
  · have hNext : a / f + 1 ≤ H := by omega
    have hMul := Nat.mul_le_mul_right f hNext
    have hDiv : a % f + (a / f) * f = a := by
      simpa only [Nat.mul_comm] using Nat.mod_add_div a f
    have hRem : a % f < f := Nat.mod_lt a hf
    have hUpper : a < (a / f + 1) * f := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    omega

/-- C.16: the original compiled window contains at least 22517
regenerative indices, independently of the pending G13 mass join. -/
theorem grantCutoffsCompiledIndexCountLower
    (n R W : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8) :
    22517 ≤ bankTrialRenewalIndexWindowCount
      n (ceilLogTwo n) W := by
  have hQuota :=
    (bankTrialRenewalIndexCompiledQuotas
      n R W hn hsp hradius hW).2
  have hStep :
      0 < bankTrialRenewalIndexStepCharge
        (ceilLogTwo n) := by
    unfold bankTrialRenewalIndexStepCharge
    omega
  have hDen :
      0 < n * bankTrialRenewalIndexStepCharge
        (ceilLogTwo n) :=
    Nat.mul_pos (by omega : 0 < n) hStep
  have hExpand :
      n * (bankTrialRenewalIndexColdCharge (ceilLogTwo n) +
        22517 * bankTrialRenewalIndexStepCharge
          (ceilLogTwo n)) =
      n * bankTrialRenewalIndexColdCharge (ceilLogTwo n) +
        22517 * (n * bankTrialRenewalIndexStepCharge
          (ceilLogTwo n)) := by
    rw [Nat.mul_add]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hExpand] at hQuota
  have hClean :
      n * bankTrialRenewalIndexColdCharge
        (ceilLogTwo n) ≤ W := by omega
  have hAvailable :
      22517 * (n * bankTrialRenewalIndexStepCharge
        (ceilLogTwo n)) ≤
      W - n * bankTrialRenewalIndexColdCharge
        (ceilLogTwo n) := by omega
  change 22517 ≤
    (W - n * bankTrialRenewalIndexColdCharge (ceilLogTwo n)) /
      (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n))
  exact grantCutoffsIndexFloorOpaque
    (W - n * bankTrialRenewalIndexColdCharge (ceilLogTwo n))
    (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n))
    22517 hDen hAvailable

/-- Pure square-to-linear inequality, including zero. -/
private theorem grantCutoffsSquareLinear
    (a n : Nat) (h : a ^ 2 ≤ n) : a ≤ n := by
  have hSelf : a ≤ a * a := by
    cases a with
    | zero =>
        simp
    | succ k =>
        have hOne : 1 ≤ k + 1 := by omega
        have hMul := Nat.mul_le_mul_left (k + 1) hOne
        simpa only [Nat.mul_one] using hMul
  calc
    a ≤ a * a := hSelf
    _ = a ^ 2 := by rw [Nat.pow_two]
    _ ≤ n := h

/-- Off the L3-PRIME signed band, at the compiled advice K=2q+kappa, the
denominator 2^K dominates the population square. No symbolic power enters omega.
(On the signed band `K = 2q - t_s` and this can fail; consumers use
`grantCutoffsRadiusPopulationFitsHeads`.) -/
theorem grantCutoffsPopulationSquareFitsHeads
    (n : Nat) (hn : 5 ≤ n) (hus : ¬ signedBand (ceilLogTwo n)) :
    n * n ≤ 2 ^ (compileAdvice (ceilLogTwo n)).K := by
  have hCeil : n ≤ 2 ^ (ceilLogTwo n) :=
    (ceilLogTwo_spec n (by omega : 2 ≤ n)).2
  have hDouble :
      2 * ceilLogTwo n ≤
        (compileAdvice (ceilLogTwo n)).K := by
    rw [compileAdvice_K_unsigned _ hus]
    omega
  calc
    n * n ≤
        (2 ^ (ceilLogTwo n)) * (2 ^ (ceilLogTwo n)) :=
      Nat.mul_le_mul hCeil hCeil
    _ = 2 ^ (ceilLogTwo n + ceilLogTwo n) :=
      (Nat.pow_add 2 (ceilLogTwo n) (ceilLogTwo n)).symm
    _ = 2 ^ (2 * ceilLogTwo n) := by
      rw [show ceilLogTwo n + ceilLogTwo n =
        2 * ceilLogTwo n by omega]
    _ ≤ 2 ^ (compileAdvice (ceilLogTwo n)).K :=
      Nat.pow_le_pow_right
        (by decide : 0 < (2 : Nat)) hDouble

/-- `4 q^2 < 2^(q-1)` for `q ≥ 13`. -/
private theorem grantCutoffsQuadBelowPow (q : Nat) (hq : 13 ≤ q) :
    4 * (q * q) < 2 ^ (q - 1) := by
  have key : ∀ k : Nat, 4 * ((k + 13) * (k + 13)) < 2 ^ (k + 12) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        have hpow : 2 ^ (k + 1 + 12) = 2 * 2 ^ (k + 12) := by
          rw [show k + 1 + 12 = (k + 12) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        have hsq : (k + 1 + 13) * (k + 1 + 13) = (k + 13) * (k + 13) + (2 * k + 27) := by
          rw [show k + 1 + 13 = (k + 13) + 1 by omega, Nat.add_mul, Nat.mul_add, Nat.mul_one,
            Nat.one_mul]
          omega
        have hge : 2 * k + 27 ≤ (k + 13) * (k + 13) := by
          have : 13 * (k + 13) ≤ (k + 13) * (k + 13) := Nat.mul_le_mul_right _ (by omega)
          omega
        rw [hpow, hsq]
        omega
  have h := key (q - 13)
  rw [show q - 13 + 13 = q by omega, show q - 13 + 12 = q - 1 by omega] at h
  exact h

/-- L3-PRIME C.17 (`L3PRIME-TRANSFER.tex` T1, C.17 via `3q - 2 ≤ 2K`): the frozen
window numerator `R n` fits the head denominator `2^K` on both bands.  Unsigned:
`R ≤ n` and `n^2 ≤ 2^K`.  Signed (`K = 2q - t_s`): `2^t < q` and `R q ≤ n`
(`R^2 ≤ n` and `4 q^2 < 2^(q-1) < n`), so `R n 2^t ≤ n^2 ≤ 2^(2q) = 2^K 2^t`. -/
theorem grantCutoffsRadiusPopulationFitsHeads
    (n R : Nat) (hn : 5 ≤ n)
    (hradius : (256 * R) ^ 2 ≤ n ∧ n < (256 * (R + 1)) ^ 2) :
    R * n ≤ 2 ^ (compileAdvice (ceilLogTwo n)).K := by
  have hRsq : R * R ≤ n := by
    have h1 : R * R ≤ (256 * R) * (256 * R) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (256 * R) ^ 2 = (256 * R) * (256 * R) := Nat.pow_two _
    omega
  have hRle : R ≤ n := by
    by_cases hR0 : R = 0
    · omega
    · have : R ≤ R * R := Nat.le_mul_of_pos_left R (by omega)
      omega
  by_cases hsb : signedBand (ceilLogTwo n)
  · obtain ⟨hc, hK, _, hlt⟩ := compileAdvice_K_signed_bounds (ceilLogTwo n) hsb
    have hspecN := ceilLogTwo_spec n (by omega)
    have hqle := ceilLogTwo_le_self (ceilLogTwo n)
    have hq2 : 2 ≤ ceilLogTwo n := by omega
    have hspecQ := ceilLogTwo_spec (ceilLogTwo n) hq2
    rw [hK]
    generalize hqdef : ceilLogTwo n = q at hK hlt hspecN hqle hspecQ hc hq2 ⊢
    generalize hcdef : ceilLogTwo q = c at hK hlt hspecQ hc hqle ⊢
    generalize htdef : signedT c = t at hK hlt ⊢
    -- 2^t < q
    have ht : 2 ^ t < q := by
      have h1 : 2 ^ t ≤ 2 ^ (c - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    -- R q ≤ n
    have hRq : R * q ≤ n := by
      by_cases hRq : q ≤ R
      · have := Nat.mul_le_mul_left R hRq
        omega
      · have h1 : R * q ≤ q * q := Nat.mul_le_mul_right q (by omega)
        have h2 := grantCutoffsQuadBelowPow q (by omega)
        omega
    have hmain : (R * n) * 2 ^ t ≤ 2 ^ (2 * q - t) * 2 ^ t := by
      have e : 2 ^ (2 * q - t) * 2 ^ t = 2 ^ q * 2 ^ q := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      rw [e]
      calc (R * n) * 2 ^ t ≤ (R * n) * q := Nat.mul_le_mul_left _ (by omega)
        _ = (R * q) * n := by ac_rfl
        _ ≤ n * n := Nat.mul_le_mul_right n hRq
        _ ≤ 2 ^ q * 2 ^ q := Nat.mul_le_mul hspecN.2 hspecN.2
    exact Nat.le_of_mul_le_mul_right hmain (Nat.two_pow_pos t)
  · have hsq := grantCutoffsPopulationSquareFitsHeads n hn hsb
    have := Nat.mul_le_mul_right n hRle
    omega

/-- New C.17 upper cutoff, initially over opaque naturals. -/
private theorem grantCutoffsFrozenUpperOpaque
    (n R W M f P : Nat)
    (hM : M ≤ n)
    (hR : R ≤ n)
    (hW : 8 * W ≤ R * n)
    (hf : 128 ≤ f)
    (hP : R * n ≤ P) :
    1024 * M * W ≤ f * n * P := by
  have hMW := Nat.mul_le_mul_right W hM
  calc
    1024 * M * W = 1024 * (M * W) := by
      rw [Nat.mul_assoc]
    _ ≤ 1024 * (n * W) :=
      Nat.mul_le_mul_left 1024 hMW
    _ = (128 * n) * (8 * W) := by
      rw [show (1024 : Nat) = 128 * 8 by decide]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (128 * n) * (R * n) :=
      Nat.mul_le_mul_left (128 * n) hW
    _ ≤ (128 * n) * P :=
      Nat.mul_le_mul_left (128 * n) hP
    _ = 128 * (n * P) := by
      simp only [Nat.mul_assoc]
    _ ≤ f * (n * P) :=
      Nat.mul_le_mul_right (n * P) hf
    _ = f * n * P := by rw [Nat.mul_assoc]

/-- Sufficient upper smallness for C.17's selected-root union.
For M<=n, the raw numerator M*W/(f*n*2^K) is <=1/1024.
The success lower bound and physical product are NOT claimed. -/
theorem grantCutoffsFrozenUnionSmallness
    (n R W M : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hM : M ≤ n) :
    1024 * M * W ≤
      (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
        n * 2 ^ (compileAdvice (ceilLogTwo n)).K := by
  have hR : R ≤ n := by
    have hScale : R ≤ 256 * R := by omega
    exact Nat.le_trans hScale
      (grantCutoffsSquareLinear
        (256 * R) n hradius.1)
  have hWindow : 8 * W ≤ R * n := by
    rw [hW]
    have hDiv := Nat.mod_add_div (R * n) 8
    omega
  have hAdvice := grantClockSpatialAdviceEighty
    (ceilLogTwo n) hsp
  have hWidth :=
    (grantClockSpatialWidthBounds (ceilLogTwo n) hAdvice).1
  have hb : 18 ≤ (compileAdvice (ceilLogTwo n)).b := by
    change 18 ≤ (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hf :
      128 ≤ 8 * (compileAdvice (ceilLogTwo n)).b + 13 := by
    omega
  exact grantCutoffsFrozenUpperOpaque n R W M
    (8 * (compileAdvice (ceilLogTwo n)).b + 13)
    (2 ^ (compileAdvice (ceilLogTwo n)).K)
    hM hR hWindow hf
    (grantCutoffsRadiusPopulationFitsHeads n R hn hradius)

/-- Attenuation of any frozen numerator bounded by W. -/
theorem grantCutoffsFrozenUnionSmallnessOfNumerator
    (n R W M z : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hM : M ≤ n)
    (hz : z ≤ W) :
    1024 * M * z ≤
      (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
        n * 2 ^ (compileAdvice (ceilLogTwo n)).K := by
  calc
    1024 * M * z ≤ 1024 * M * W :=
      Nat.mul_le_mul_left (1024 * M) hz
    _ ≤ _ := grantCutoffsFrozenUnionSmallness
      n R W M hn hsp hradius hW hM

/-- Reexport the already proved C.18 strict integer certificate.
It cannot, by itself, prove a physical eta/epsilon_F ratio. -/
theorem grantCutoffsDefectRatioCoefficient :
    157 * 100 * 1000 * 8192 * 1024 ^ 4 <
      608 * 2 ^ 20 * 1023 ^ 3 * 49 * 489 * 255 :=
  grantClockSpatialC18Strict

end L3

#print axioms L3.grantCutoffsCompiledRadiusReserves
#print axioms L3.grantCutoffsCompiledIndexCountLower
#print axioms L3.grantCutoffsPopulationSquareFitsHeads
#print axioms L3.grantCutoffsFrozenUnionSmallness
#print axioms L3.grantCutoffsFrozenUnionSmallnessOfNumerator
