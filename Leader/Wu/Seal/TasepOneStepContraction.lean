import Leader.Wu.Seal.TasepIncomingNumerator
import Leader.Wu.Seal.TasepDistanceTwoComparison

namespace PPLLCompleteMultiLeaderCleanup
namespace SealTasepGeometricDecay

open PPLL PPLLResearchFormulation PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepFiniteTimeSol
open SealJohnsonEnergyIdentity SealTasepL2Contraction
open PPartialSealSweepTasepMovingParticleComparisonSol

set_option autoImplicit false
set_option Elab.async false

/-- Exact denominator-cleared one-step L2 contraction. -/
theorem sealTasepGeometricL2OneStep {n : Nat} (ring : DirectedRing n) (hn : 1 < n) (k : Nat)
    (hP : SealTasepPoincareAt ring k) (f : SealObs n) (hzero : sealSliceIntSum k f = 0) :
    (4 * n ^ 3) * sealAllPairsSquaredEnergy k (sealPStarNumerator ring k f) <=
      (n ^ 2 * (4 * n ^ 3 - 1)) * sealAllPairsSquaredEnergy k f := by
  let g := sealPStarNumerator ring k f
  have hzg : sealSliceIntSum k g = 0 := by
    change sealSliceIntSum k (sealPStarNumerator ring k f) = 0
    rw [sealPStarNumerator_sum ring hn k f, hzero]
    simp
  have hzA : SealJohnsonPoincareA2a.sealSliceIntSum k f = 0 := by
    simpa [SealJohnsonPoincareA2a.sealSliceIntSum, sealSliceIntSum] using hzero
  have hzgA : SealJohnsonPoincareA2a.sealSliceIntSum k g = 0 := by
    simpa [SealJohnsonPoincareA2a.sealSliceIntSum, sealSliceIntSum] using hzg
  have hEf := SealJohnsonPoincareA2b.sealAllPairsMeanZero n k f hzA
  have hEg := SealJohnsonPoincareA2b.sealAllPairsMeanZero n k g hzgA
  have hQ : sealPStarQuadraticInt ring k f =
      (SealJohnsonPoincareA2a.sealSliceIntNormSq k g : Int) := by
    calc
      _ = sealSliceSquareInt k g := by simpa [g] using (sealPStarNumerator_square ring hn k f).symm
      _ = _ := sealSliceSquareInt_eq_normSq k g
  have hN : sealSliceSquareInt k f =
      (SealJohnsonPoincareA2a.sealSliceIntNormSq k f : Int) :=
    sealSliceSquareInt_eq_normSq k f
  have hv := sealPStar_variance_drop_wordSum ring hn k f hzero
  rw [hQ, hN] at hv
  have hvNat :
      fullCommonSuccessorSquaredEnergy ring k f +
          2 * SealJohnsonPoincareA2a.sealSliceIntNormSq k g =
        2 * (n ^ 2 * SealJohnsonPoincareA2a.sealSliceIntNormSq k f) := by
    apply Int.ofNat_inj.mp
    simpa using hv
  have hdrop :
      sealAllPairsSquaredEnergy k g +
          (tasepFrontConfigSlice n k).length * fullCommonSuccessorSquaredEnergy ring k f =
        n ^ 2 * sealAllPairsSquaredEnergy k f := by
    rw [hEg, hEf]
    calc
      2 * (tasepFrontConfigSlice n k).length * SealJohnsonPoincareA2a.sealSliceIntNormSq k g +
          (tasepFrontConfigSlice n k).length * fullCommonSuccessorSquaredEnergy ring k f =
        (tasepFrontConfigSlice n k).length *
          (2 * SealJohnsonPoincareA2a.sealSliceIntNormSq k g) +
          (tasepFrontConfigSlice n k).length * fullCommonSuccessorSquaredEnergy ring k f := by ac_rfl
      _ = (tasepFrontConfigSlice n k).length *
          (2 * SealJohnsonPoincareA2a.sealSliceIntNormSq k g +
            fullCommonSuccessorSquaredEnergy ring k f) := by
        rw [Nat.mul_add]
      _ = (tasepFrontConfigSlice n k).length *
          (fullCommonSuccessorSquaredEnergy ring k f +
            2 * SealJohnsonPoincareA2a.sealSliceIntNormSq k g) := by
        rw [Nat.add_comm]
      _ = (tasepFrontConfigSlice n k).length *
          (2 * (n ^ 2 * SealJohnsonPoincareA2a.sealSliceIntNormSq k f)) := by rw [hvNat]
      _ = n ^ 2 *
          (2 * (tasepFrontConfigSlice n k).length *
            SealJohnsonPoincareA2a.sealSliceIntNormSq k f) := by ac_rfl
  have hp := hP f
  have hsum :
      4 * n * sealAllPairsSquaredEnergy k g + sealAllPairsSquaredEnergy k f <=
        (4 * n ^ 3) * sealAllPairsSquaredEnergy k f := by
    calc
      _ <= 4 * n * sealAllPairsSquaredEnergy k g +
          4 * n * (tasepFrontConfigSlice n k).length *
            fullCommonSuccessorSquaredEnergy ring k f := Nat.add_le_add_left hp _
      _ = (4 * n) * sealAllPairsSquaredEnergy k g +
          (4 * n) * ((tasepFrontConfigSlice n k).length *
            fullCommonSuccessorSquaredEnergy ring k f) := by ac_rfl
      _ = (4 * n) * (sealAllPairsSquaredEnergy k g +
          (tasepFrontConfigSlice n k).length *
            fullCommonSuccessorSquaredEnergy ring k f) := by
        rw [Nat.mul_add]
      _ = (4 * n) * (n ^ 2 * sealAllPairsSquaredEnergy k f) := by rw [hdrop]
      _ = (4 * n ^ 3) * sealAllPairsSquaredEnergy k f := by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
        ac_rfl
  have hn0 : 0 < n := by omega
  have hn3 : 0 < n ^ 3 := Nat.pow_pos hn0
  have hcoef : 1 <= 4 * n ^ 3 := by omega
  have hcoefSplit : 4 * n ^ 3 = 1 + (4 * n ^ 3 - 1) := by omega
  have hsplit :
      (4 * n ^ 3) * sealAllPairsSquaredEnergy k f =
        sealAllPairsSquaredEnergy k f +
          (4 * n ^ 3 - 1) * sealAllPairsSquaredEnergy k f := by
    rw [hcoefSplit, Nat.add_mul]
    simp
  rw [hsplit] at hsum
  have hsum' :
      sealAllPairsSquaredEnergy k f + 4 * n * sealAllPairsSquaredEnergy k g <=
        sealAllPairsSquaredEnergy k f +
          (4 * n ^ 3 - 1) * sealAllPairsSquaredEnergy k f := by
    calc
      _ = 4 * n * sealAllPairsSquaredEnergy k g + sealAllPairsSquaredEnergy k f := Nat.add_comm _ _
      _ <= _ := hsum
  have hc : 4 * n * sealAllPairsSquaredEnergy k g <=
      (4 * n ^ 3 - 1) * sealAllPairsSquaredEnergy k f :=
    Nat.le_of_add_le_add_left hsum'
  have hs : n ^ 2 * (4 * n * sealAllPairsSquaredEnergy k g) <=
      n ^ 2 * ((4 * n ^ 3 - 1) * sealAllPairsSquaredEnergy k f) :=
    Nat.mul_le_mul_left (n ^ 2) hc
  calc
    (4 * n ^ 3) * sealAllPairsSquaredEnergy k g =
        n ^ 2 * (4 * n * sealAllPairsSquaredEnergy k g) := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      ac_rfl
    _ <= n ^ 2 * ((4 * n ^ 3 - 1) * sealAllPairsSquaredEnergy k f) := hs
    _ = (n ^ 2 * (4 * n ^ 3 - 1)) * sealAllPairsSquaredEnergy k f := by ac_rfl

end SealTasepGeometricDecay
end PPLLCompleteMultiLeaderCleanup

#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepGeometricDecay.sealTasepGeometricL2OneStep
