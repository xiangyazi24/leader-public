import Leader.Wu.Seal.JohnsonEnergySharpConstant

namespace PPLLCompleteMultiLeaderCleanup
namespace SealJohnsonPoincareA2a

open PPLL PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepFiniteTimeSol
open SealJohnsonEnergyIdentity

set_option autoImplicit false

abbrev SealIntObs (n : Nat) := (Fin n -> Bool) -> Int

def sealSliceIntSum {n : Nat} (k : Nat) (f : SealIntObs n) : Int :=
  ((tasepFrontConfigSlice n k).map f).sum

def sealSliceIntDot {n : Nat} (k : Nat)
    (f g : SealIntObs n) : Int :=
  ((tasepFrontConfigSlice n k).map (fun F => f F * g F)).sum

def sealSliceIntNormSq {n : Nat} (k : Nat) (f : SealIntObs n) : Nat :=
  ((tasepFrontConfigSlice n k).map
    (fun F => Int.natAbs (f F) ^ 2)).sum

def sealOrderedSwapLaplacianInt {n : Nat} (k : Nat)
    (f : SealIntObs n) (F : Fin n -> Bool) : Int :=
  (List.ofFn (fun x : Fin n =>
    (List.ofFn (fun z : Fin n =>
      f F - f (sealTransposeFrontConfig F x z))).sum)).sum

def sealJohnsonDepth (n k : Nat) : Nat := Nat.min k (n - k)

def sealJohnsonEigenvalue (n j : Nat) : Nat := j * (n + 1 - j)

def sealPositiveSpectralNorm {n : Nat} (k : Nat)
    (g : Fin (sealJohnsonDepth n k + 1) -> SealIntObs n) : Nat :=
  (List.ofFn (fun j : Fin (sealJohnsonDepth n k + 1) =>
    if j.val = 0 then 0 else sealSliceIntNormSq k (g j))).sum

def sealEigenWeightedNorm {n : Nat} (k : Nat)
    (g : Fin (sealJohnsonDepth n k + 1) -> SealIntObs n) : Nat :=
  (List.ofFn (fun j : Fin (sealJohnsonDepth n k + 1) =>
    sealJohnsonEigenvalue n j.val * sealSliceIntNormSq k (g j))).sum

def sealDeficitSquares {n : Nat} (k : Nat)
    (g : Fin (sealJohnsonDepth n k + 1) -> SealIntObs n) : Nat :=
  4 * (tasepFrontConfigSlice n k).length *
    (List.ofFn (fun j : Fin (sealJohnsonDepth n k + 1) =>
      (j.val - 1) * (n - j.val) * sealSliceIntNormSq k (g j))).sum

def sealSliceTransposeClosedStatement : Prop :=
  ∀ (n k : Nat) (F : Fin n -> Bool) (x z : Fin n),
    F ∈ tasepFrontConfigSlice n k ->
      sealTransposeFrontConfig F x z ∈ tasepFrontConfigSlice n k

def sealAllPairsMeanZeroStatement : Prop :=
  ∀ (n k : Nat) (f : SealIntObs n),
    sealSliceIntSum k f = 0 ->
      sealAllPairsSquaredEnergy k f =
        2 * (tasepFrontConfigSlice n k).length * sealSliceIntNormSq k f

def sealOrderedSwapGreenStatement : Prop :=
  ∀ (n k : Nat) (f : SealIntObs n),
    (sealArbitraryTranspositionEnergy k f : Int) =
      2 * sealSliceIntDot k f (sealOrderedSwapLaplacianInt k f)

def sealJohnsonScaledSpectralData {n : Nat} (k : Nat)
    (phi : SealIntObs n) (D : Nat)
    (g : Fin (sealJohnsonDepth n k + 1) -> SealIntObs n) : Prop :=
  0 < D /\
  (∃ c : Int, ∀ F, F ∈ tasepFrontConfigSlice n k -> g 0 F = c) /\
  (∀ F, F ∈ tasepFrontConfigSlice n k ->
    (D : Int) * phi F =
      (List.ofFn (fun j : Fin (sealJohnsonDepth n k + 1) => g j F)).sum) /\
  (∀ j : Fin (sealJohnsonDepth n k + 1), 0 < j.val ->
    sealSliceIntSum k (g j) = 0) /\
  (∀ i j : Fin (sealJohnsonDepth n k + 1), i != j ->
    sealSliceIntDot k (g i) (g j) = 0) /\
  (∀ j : Fin (sealJohnsonDepth n k + 1),
    ∀ F, F ∈ tasepFrontConfigSlice n k ->
      sealOrderedSwapLaplacianInt k (g j) F =
        ((2 * sealJohnsonEigenvalue n j.val : Nat) : Int) * g j F)

def sealJohnsonSpectralDecompositionStatement : Prop :=
  ∀ (n k : Nat) (phi : SealIntObs n),
    0 < k -> k < n ->
      ∃ (D : Nat)
        (g : Fin (sealJohnsonDepth n k + 1) -> SealIntObs n),
        sealJohnsonScaledSpectralData k phi D g

def sealAllPairsParsevalStatement : Prop :=
  ∀ (n k : Nat) (phi : SealIntObs n) (D : Nat)
      (g : Fin (sealJohnsonDepth n k + 1) -> SealIntObs n),
    sealJohnsonScaledSpectralData k phi D g ->
      D ^ 2 * sealAllPairsSquaredEnergy k phi =
        2 * (tasepFrontConfigSlice n k).length * sealPositiveSpectralNorm k g

def sealTranspositionParsevalStatement : Prop :=
  ∀ (n k : Nat) (phi : SealIntObs n) (D : Nat)
      (g : Fin (sealJohnsonDepth n k + 1) -> SealIntObs n),
    sealJohnsonScaledSpectralData k phi D g ->
      D ^ 2 * sealArbitraryTranspositionEnergy k phi =
        4 * sealEigenWeightedNorm k g

def sealDeficitCertificateStatement : Prop :=
  ∀ (n k : Nat) (phi : SealIntObs n) (D : Nat)
      (g : Fin (sealJohnsonDepth n k + 1) -> SealIntObs n),
    sealJohnsonScaledSpectralData k phi D g ->
      D ^ 2 * (tasepFrontConfigSlice n k).length *
          sealArbitraryTranspositionEnergy k phi =
        D ^ 2 * (2 * n * sealAllPairsSquaredEnergy k phi) +
          sealDeficitSquares k g

def sealDeficitCertificateClosesStatement : Prop :=
  ∀ (n k : Nat) (phi : SealIntObs n) (D : Nat)
      (g : Fin (sealJohnsonDepth n k + 1) -> SealIntObs n),
    sealJohnsonScaledSpectralData k phi D g ->
    D ^ 2 * (tasepFrontConfigSlice n k).length *
        sealArbitraryTranspositionEnergy k phi =
      D ^ 2 * (2 * n * sealAllPairsSquaredEnergy k phi) +
        sealDeficitSquares k g ->
    2 * n * sealAllPairsSquaredEnergy k phi <=
      (tasepFrontConfigSlice n k).length *
        sealArbitraryTranspositionEnergy k phi

def sealJohnsonPoincareStatement : Prop :=
  ∀ (n k : Nat) (phi : SealIntObs n),
    0 < k -> k < n ->
      2 * n * sealAllPairsSquaredEnergy k phi <=
        (tasepFrontConfigSlice n k).length *
          sealArbitraryTranspositionEnergy k phi

/-! Witnesses: explicit scaled spectral data. -/

def sealLinearComponents4 (j : Fin 3) (F : Fin 4 -> Bool) : Int :=
  if j.val = 0 then 1
  else if j.val = 1 then 2 * sealLinearPhi4 F - 1
  else 0

def sealPointJ1Scaled4 (F : Fin 4 -> Bool) : Int :=
  3 * (((if F 0 then (1 : Int) else 0) +
    (if F 1 then (1 : Int) else 0)) - 1)

def sealPointComponents4 (j : Fin 3) (F : Fin 4 -> Bool) : Int :=
  if j.val = 0 then 1
  else if j.val = 1 then sealPointJ1Scaled4 F
  else 6 * sealPointPhi4 F - 1 - sealPointJ1Scaled4 F

theorem seal_linear_scaled_data_check :
    sealJohnsonScaledSpectralData (n := 4) 2 sealLinearPhi4 2 sealLinearComponents4 := by
  unfold sealJohnsonScaledSpectralData
  exact ⟨by decide, ⟨1, by decide⟩, by decide, by decide, by decide, by decide⟩

theorem seal_linear_deficit_certificate_check :
    2 ^ 2 * (tasepFrontConfigSlice 4 2).length *
        sealArbitraryTranspositionEnergy 2 sealLinearPhi4 =
      2 ^ 2 * (2 * 4 * sealAllPairsSquaredEnergy 2 sealLinearPhi4) +
        sealDeficitSquares (n := 4) 2 sealLinearComponents4 := by
  decide

theorem seal_point_scaled_data_check :
    sealJohnsonScaledSpectralData (n := 4) 2 sealPointPhi4 6 sealPointComponents4 := by
  unfold sealJohnsonScaledSpectralData
  exact ⟨by decide, ⟨1, by decide⟩, by decide, by decide, by decide, by decide⟩

theorem seal_point_deficit_certificate_check :
    6 ^ 2 * (tasepFrontConfigSlice 4 2).length *
        sealArbitraryTranspositionEnergy 2 sealPointPhi4 =
      6 ^ 2 * (2 * 4 * sealAllPairsSquaredEnergy 2 sealPointPhi4) +
        sealDeficitSquares (n := 4) 2 sealPointComponents4 := by
  decide

end SealJohnsonPoincareA2a
end PPLLCompleteMultiLeaderCleanup

#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonPoincareA2a.seal_linear_scaled_data_check
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonPoincareA2a.seal_linear_deficit_certificate_check
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonPoincareA2a.seal_point_scaled_data_check
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonPoincareA2a.seal_point_deficit_certificate_check
