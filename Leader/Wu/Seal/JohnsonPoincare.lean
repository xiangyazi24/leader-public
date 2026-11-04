import Leader.Wu.Seal.JohnsonCentering


namespace PPLLCompleteMultiLeaderCleanup
namespace SealJohnsonSpectralRoute


open PPLL PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepMixingFirstBrickSol
open PPartialSealSweepTasepFiniteTimeSol
open SealJohnsonEnergyIdentity SealJohnsonPoincareA2a


set_option autoImplicit false
set_option Elab.async false


private theorem isumMapCongr
    {α : Type} (xs : List α) (f g : α -> Int)
    (h : forall x, f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [h a, ih]


private theorem castSumNat (xs : List Nat) :
    (xs.sum : Int) =
      (xs.map (fun a : Nat => (a : Int))).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.sum_cons, List.map_cons]
      rw [Int.natCast_add, ih]


private theorem castMapSumNat
    {α : Type} (xs : List α) (f : α -> Nat) :
    ((xs.map f).sum : Int) =
      (xs.map (fun x => (f x : Int))).sum := by
  simpa [List.map_map, Function.comp_def] using castSumNat (xs.map f)


/-- Local copy of A2b's private norm cast, with the Johnson norm name exposed. -/
private theorem sealSliceIntNormSq_cast
    {n : Nat} (k : Nat) (f : SealIntObs n) :
    (sealSliceIntNormSq k f : Int) = sealJohnsonNormInt k f := by
  unfold sealJohnsonNormInt sealSliceIntNormSq sealSliceIntDot
  calc
    (((tasepFrontConfigSlice n k).map
      (fun F => Int.natAbs (f F) ^ 2)).sum : Int) =
        ((tasepFrontConfigSlice n k).map
          (fun F => ((Int.natAbs (f F) ^ 2 : Nat) : Int))).sum :=
      castMapSumNat _ _
    _ = ((tasepFrontConfigSlice n k).map
        (fun F => f F * f F)).sum := by
      apply isumMapCongr
      intro F
      simpa [Nat.pow_two] using
        (Int.natAbs_mul_self (a := f F))


/-- Step 11c: convert the sharp mean-zero Johnson gap back to the exact
repository Poincare inequality for an arbitrary integer observable. -/
theorem sealJohnsonPoincare :
    sealJohnsonPoincareStatement := by
  unfold sealJohnsonPoincareStatement
  intro n k phi hk hkn


  let S := (tasepFrontConfigSlice n k).length
  let f := sealJohnsonCentered k phi


  have hcenter := sealJohnsonCentering n k phi hk hkn
  change
    sealSliceIntSum k f = 0 /\
      sealAllPairsSquaredEnergy k f =
        S ^ 2 * sealAllPairsSquaredEnergy k phi /\
      sealArbitraryTranspositionEnergy k f =
        S ^ 2 * sealArbitraryTranspositionEnergy k phi at hcenter


  have hgap := sealJohnsonMeanZeroGap n k f hk hkn hcenter.1


  have hpairs :=
    SealJohnsonPoincareA2b.sealAllPairsMeanZero n k f hcenter.1


  have hgreen :=
    SealJohnsonPoincareA2b.sealOrderedSwapGreen n k f
  change
    (sealArbitraryTranspositionEnergy k f : Int) =
      2 * sealJohnsonDirichletInt k f at hgreen


  have hnorm := sealSliceIntNormSq_cast k f


  have hcenterInt :
      ((2 * n * sealAllPairsSquaredEnergy k f : Nat) : Int) <=
        ((S * sealArbitraryTranspositionEnergy k f : Nat) : Int) := by
    calc
      ((2 * n * sealAllPairsSquaredEnergy k f : Nat) : Int) =
          (2 * (S : Int)) *
            (2 * (n : Int) * sealJohnsonNormInt k f) := by
        rw [hpairs]
        simp only [Int.natCast_mul]
        rw [hnorm]
        ac_rfl
      _ <= (2 * (S : Int)) * sealJohnsonDirichletInt k f :=
        Int.mul_le_mul_of_nonneg_left hgap (by omega)
      _ = (S : Int) * (2 * sealJohnsonDirichletInt k f) := by
        ac_rfl
      _ = (S : Int) *
          (sealArbitraryTranspositionEnergy k f : Int) := by
        rw [<- hgreen]
      _ = ((S * sealArbitraryTranspositionEnergy k f : Nat) : Int) := by
        rw [Int.natCast_mul]


  have hcenterNat :
      2 * n * sealAllPairsSquaredEnergy k f <=
        S * sealArbitraryTranspositionEnergy k f :=
    Int.ofNat_le.mp hcenterInt


  rw [hcenter.2.1, hcenter.2.2] at hcenterNat


  have hmul :
      S ^ 2 * (2 * n * sealAllPairsSquaredEnergy k phi) <=
        S ^ 2 *
          (S * sealArbitraryTranspositionEnergy k phi) := by
    calc
      S ^ 2 * (2 * n * sealAllPairsSquaredEnergy k phi) =
          2 * n *
            (S ^ 2 * sealAllPairsSquaredEnergy k phi) := by
        ac_rfl
      _ <= S *
          (S ^ 2 * sealArbitraryTranspositionEnergy k phi) :=
        hcenterNat
      _ = S ^ 2 *
          (S * sealArbitraryTranspositionEnergy k phi) := by
        ac_rfl


  have hS : 0 < S :=
    sealJohnsonSliceCardPositive n k hk hkn
  exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos hS)


end SealJohnsonSpectralRoute
end PPLLCompleteMultiLeaderCleanup


#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonPoincare
