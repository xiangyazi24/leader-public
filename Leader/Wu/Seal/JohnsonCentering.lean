import Leader.Wu.Seal.JohnsonMeanZeroGap

namespace PPLLCompleteMultiLeaderCleanup
namespace SealJohnsonSpectralRoute

open PPLL PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepMixingFirstBrickSol
open PPartialSealSweepTasepFiniteTimeSol
open SealJohnsonEnergyIdentity SealJohnsonPoincareA2a

set_option autoImplicit false
set_option Elab.async false

private theorem nsumMapCongr
    {α : Type} (xs : List α) (f g : α -> Nat)
    (h : forall x, f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [h a, ih]

private theorem nsumMapMulLeft
    {α : Type} (xs : List α) (c : Nat) (f : α -> Nat) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

private theorem nsumNestedMulLeft
    {α β : Type} (xs : List α) (ys : List β)
    (c : Nat) (f : α -> β -> Nat) :
    (xs.map (fun x =>
      (ys.map (fun y => c * f x y)).sum)).sum =
      c * (xs.map (fun x => (ys.map (fun y => f x y)).sum)).sum := by
  calc
    _ = (xs.map (fun x => c * (ys.map (fun y => f x y)).sum)).sum := by
      apply nsumMapCongr
      intro x
      exact nsumMapMulLeft ys c (fun y => f x y)
    _ = _ := nsumMapMulLeft xs c _

private theorem isumMapSub
    {α : Type} (xs : List α) (f g : α -> Int) :
    (xs.map (fun x => f x - g x)).sum =
      (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

private theorem isumMapMulLeft
    {α : Type} (xs : List α) (c : Int) (f : α -> Int) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Int.mul_add]

private theorem isumMapConst
    {α : Type} (xs : List α) (c : Int) :
    (xs.map (fun _ => c)).sum = (xs.length : Int) * c := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Int.natCast_succ, ih, Int.add_mul, Int.one_mul]
      omega

private theorem ofFnEqOfPointwise
    {α : Type} {m : Nat} (f g : Fin m -> α)
    (h : forall i, f i = g i) :
    List.ofFn f = List.ofFn g := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.ofFn_succ, h 0,
        ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => h i.succ)]

private theorem nsumOfFnMulLeft
    {m : Nat} (c : Nat) (f : Fin m -> Nat) :
    (List.ofFn (fun i => c * f i)).sum = c * (List.ofFn f).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        ih (fun i => f i.succ), Nat.mul_add]

private theorem nsumDoubleOfFnMulLeft
    {m q : Nat} (c : Nat) (f : Fin m -> Fin q -> Nat) :
    (List.ofFn (fun i =>
      (List.ofFn (fun j => c * f i j)).sum)).sum =
      c * (List.ofFn (fun i => (List.ofFn (fun j => f i j)).sum)).sum := by
  calc
    _ = (List.ofFn (fun i =>
        c * (List.ofFn (fun j => f i j)).sum)).sum := by
      apply congrArg List.sum
      apply ofFnEqOfPointwise
      intro i
      exact nsumOfFnMulLeft c (fun j => f i j)
    _ = _ := nsumOfFnMulLeft c _

private theorem frontSliceCardPosOfLe
    (n k : Nat) (hkn : k <= n) :
    0 < frontSliceCard n k := by
  induction n generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [frontSliceCard_succ_succ]
          have hleft : 0 < frontSliceCard n k := ih k (by omega)
          omega

/-- Step 11a: every interior Boolean slice has positive cardinality. -/
theorem sealJohnsonSliceCardPositive :
    sealJohnsonSliceCardPositiveStatement := by
  unfold sealJohnsonSliceCardPositiveStatement
  intro n k _hk hkn
  rw [tasepFrontConfigSlice_length_eq_card]
  exact frontSliceCardPosOfLe n k (by omega)

/-- Step 11b: integral centering is mean zero and scales both Nat energies
by the exact square of the slice cardinality. -/
theorem sealJohnsonCentering :
    sealJohnsonCenteringStatement := by
  unfold sealJohnsonCenteringStatement
  intro n k phi _hk _hkn
  let S := (tasepFrontConfigSlice n k).length
  let f := sealJohnsonCentered k phi
  change
    sealSliceIntSum k f = 0 /\
      sealAllPairsSquaredEnergy k f =
        S ^ 2 * sealAllPairsSquaredEnergy k phi /\
      sealArbitraryTranspositionEnergy k f =
        S ^ 2 * sealArbitraryTranspositionEnergy k phi

  have hdiff (F G : Fin n -> Bool) :
      f F - f G = (S : Int) * (phi F - phi G) := by
    dsimp [f, sealJohnsonCentered, S]
    rw [Int.mul_sub]
    omega

  have hgap (F G : Fin n -> Bool) :
      sealSquaredGap f F G = S ^ 2 * sealSquaredGap phi F G := by
    unfold sealSquaredGap
    rw [hdiff F G, Int.natAbs_mul,
      Int.natAbs_natCast, Nat.mul_pow]

  have hzero : sealSliceIntSum k f = 0 := by
    unfold sealSliceIntSum
    show ((tasepFrontConfigSlice n k).map (fun F =>
      ((tasepFrontConfigSlice n k).length : Int) * phi F - sealSliceIntSum k phi)).sum = 0
    rw [isumMapSub, isumMapMulLeft, isumMapConst]
    unfold sealSliceIntSum
    exact Int.sub_self _

  have hall :
      sealAllPairsSquaredEnergy k f =
        S ^ 2 * sealAllPairsSquaredEnergy k phi := by
    unfold sealAllPairsSquaredEnergy
    calc
      _ = ((tasepFrontConfigSlice n k).map (fun F =>
          ((tasepFrontConfigSlice n k).map (fun G =>
            S ^ 2 * sealSquaredGap phi F G)).sum)).sum := by
        apply nsumMapCongr
        intro F
        apply nsumMapCongr
        intro G
        exact hgap F G
      _ = _ := nsumNestedMulLeft
        (tasepFrontConfigSlice n k) (tasepFrontConfigSlice n k)
        (S ^ 2) (fun F G => sealSquaredGap phi F G)

  have htrans :
      sealArbitraryTranspositionEnergy k f =
        S ^ 2 * sealArbitraryTranspositionEnergy k phi := by
    unfold sealArbitraryTranspositionEnergy
    calc
      _ = (List.ofFn (fun x : Fin n =>
          (List.ofFn (fun z : Fin n =>
            ((tasepFrontConfigSlice n k).map (fun F =>
              S ^ 2 * sealSquaredGap phi F
                (sealTransposeFrontConfig F x z))).sum)).sum)).sum := by
        apply congrArg List.sum
        apply ofFnEqOfPointwise
        intro x
        apply congrArg List.sum
        apply ofFnEqOfPointwise
        intro z
        apply nsumMapCongr
        intro F
        exact hgap F (sealTransposeFrontConfig F x z)
      _ = (List.ofFn (fun x : Fin n =>
          (List.ofFn (fun z : Fin n =>
            S ^ 2 * ((tasepFrontConfigSlice n k).map (fun F =>
              sealSquaredGap phi F
                (sealTransposeFrontConfig F x z))).sum)).sum)).sum := by
        apply congrArg List.sum
        apply ofFnEqOfPointwise
        intro x
        apply congrArg List.sum
        apply ofFnEqOfPointwise
        intro z
        exact nsumMapMulLeft (tasepFrontConfigSlice n k) (S ^ 2)
          (fun F => sealSquaredGap phi F
            (sealTransposeFrontConfig F x z))
      _ = _ := nsumDoubleOfFnMulLeft (S ^ 2)
        (fun x z =>
          ((tasepFrontConfigSlice n k).map (fun F =>
            sealSquaredGap phi F
              (sealTransposeFrontConfig F x z))).sum)

  exact ⟨hzero, hall, htrans⟩

end SealJohnsonSpectralRoute
end PPLLCompleteMultiLeaderCleanup

#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonSliceCardPositive
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonCentering
