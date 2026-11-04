import Leader.L3.Bank.TrialRenewal

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

/-- At the compiled advice K=2q+kappa, the denominator 2^K
dominates the population square. No symbolic power enters omega. -/
theorem grantCutoffsPopulationSquareFitsHeads
    (n : Nat) (hn : 5 ≤ n) :
    n * n ≤ 2 ^ (compileAdvice (ceilLogTwo n)).K := by
  have hCeil : n ≤ 2 ^ (ceilLogTwo n) :=
    (ceilLogTwo_spec n (by omega : 2 ≤ n)).2
  have hDouble :
      2 * ceilLogTwo n ≤
        (compileAdvice (ceilLogTwo n)).K := by
    change 2 * ceilLogTwo n ≤
      2 * ceilLogTwo n + productionKappa (ceilLogTwo n)
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

/-- New C.17 upper cutoff, initially over opaque naturals. -/
private theorem grantCutoffsFrozenUpperOpaque
    (n R W M f P : Nat)
    (hM : M ≤ n)
    (hR : R ≤ n)
    (hW : 8 * W ≤ R * n)
    (hf : 128 ≤ f)
    (hP : n * n ≤ P) :
    1024 * M * W ≤ f * n * P := by
  have hMW := Nat.mul_le_mul_right W hM
  have hRmul := Nat.mul_le_mul_right n hR
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
    _ ≤ (128 * n) * (n * n) :=
      Nat.mul_le_mul_left (128 * n) hRmul
    _ = 128 * (n * (n * n)) := by
      simp only [Nat.mul_assoc]
    _ ≤ f * (n * (n * n)) :=
      Nat.mul_le_mul_right (n * (n * n)) hf
    _ = (f * n) * (n * n) := by
      simp only [Nat.mul_assoc]
    _ ≤ (f * n) * P :=
      Nat.mul_le_mul_left (f * n) hP
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
    (grantCutoffsPopulationSquareFitsHeads n hn)

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
