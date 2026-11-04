import Leader.Wu.Seal.MixingReduction
import Leader.Wu.Seal.TasepFiniteTime
import Leader.Wu.Seal.TasepPointwisePoincare
import Leader.Wu.Seal.TasepDistanceTwoComparison
import Leader.Wu.Seal.JohnsonEnergySharpConstant


namespace PPLLCompleteMultiLeaderCleanup
namespace SealTasepL2Contraction


open PPLL PPLLResearchFormulation PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepFiniteTimeSol
open PPartialSealSweepTasepPointwisePoincareSol
open PPartialSealSweepTasepMovingParticleComparisonSol
open Q11574FixedFrontMassMixing SealJohnsonEnergyIdentity


set_option autoImplicit false
set_option Elab.async false


abbrev SealObs (n : Nat) := (Fin n -> Bool) -> Int


private theorem isumMapAdd {a : Type} (xs : List a) (f g : a -> Int) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega


private theorem isumMapSub {a : Type} (xs : List a) (f g : a -> Int) :
    (xs.map (fun x => f x - g x)).sum =
      (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega


private theorem isumMapMulLeft {a : Type} (xs : List a)
    (c : Int) (f : a -> Int) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, Int.mul_add]


private theorem isumMapConst {a : Type} (xs : List a) (c : Int) :
    (xs.map (fun _ => c)).sum = (xs.length : Int) * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Int.natCast_succ, ih, Int.add_mul, Int.one_mul]
      omega


private theorem isumMapComm {a b : Type} (xs : List a) (ys : List b)
    (f : a -> b -> Int) :
    (xs.map (fun x => (ys.map (fun y => f x y)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      simpa using (isumMapConst ys 0).symm
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      simpa using (isumMapAdd ys (fun y => f x y)
        (fun y => (xs.map (fun z => f z y)).sum)).symm


private theorem castMapSumNat {a : Type} (xs : List a) (f : a -> Nat) :
    ((xs.map f).sum : Int) = (xs.map (fun x => (f x : Int))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Int.natCast_add, ih]


def sealSliceIntSum {n : Nat} (k : Nat) (f : SealObs n) : Int :=
  ((tasepFrontConfigSlice n k).map f).sum


def sealSliceSquareInt {n : Nat} (k : Nat) (f : SealObs n) : Int :=
  ((tasepFrontConfigSlice n k).map (fun F => f F * f F)).sum


noncomputable def sealPStarQuadraticInt {n : Nat}
    (ring : DirectedRing n) (k : Nat) (f : SealObs n) : Int :=
  ((tasepFrontConfigSlice n k).map (fun F =>
    ((tasepFrontConfigSlice n k).map (fun G =>
      (tasepCommonSuccessorPairCount ring F G : Int) * f F * f G)).sum)).sum


noncomputable def sealCommonLeftSquareInt {n : Nat}
    (ring : DirectedRing n) (k : Nat) (f : SealObs n) : Int :=
  ((tasepFrontConfigSlice n k).map (fun F =>
    ((tasepFrontConfigSlice n k).map (fun G =>
      (tasepCommonSuccessorPairCount ring F G : Int) * (f F * f F))).sum)).sum


noncomputable def sealCommonRightSquareInt {n : Nat}
    (ring : DirectedRing n) (k : Nat) (f : SealObs n) : Int :=
  ((tasepFrontConfigSlice n k).map (fun F =>
    ((tasepFrontConfigSlice n k).map (fun G =>
      (tasepCommonSuccessorPairCount ring F G : Int) * (f G * f G))).sum)).sum


/-- Restatement of the static input, avoiding the separately queued integration file. -/
def SealTasepPoincareAt {n : Nat}
    (ring : DirectedRing n) (k : Nat) : Prop :=
  forall phi : SealObs n,
    sealAllPairsSquaredEnergy k phi <=
      4 * n * (tasepFrontConfigSlice n k).length *
        fullCommonSuccessorSquaredEnergy ring k phi


private theorem weightedSquareSplit (c a b : Int) :
    c * ((a - b) * (a - b)) =
      c * a * a + c * b * b - 2 * (c * a * b) := by
  calc
    c * ((a - b) * (a - b)) =
        c * (a * (a - b) - b * (a - b)) := by rw [Int.sub_mul]
    _ = c * (a * (a - b)) - c * (b * (a - b)) := by rw [Int.mul_sub]
    _ = c * (a * a - a * b) - c * (b * a - b * b) := by
      rw [Int.mul_sub a a b, Int.mul_sub b a b]
    _ = (c * a * a - c * a * b) - (c * b * a - c * b * b) := by
      rw [Int.mul_sub c (a * a) (a * b), Int.mul_sub c (b * a) (b * b)]
      simp only [Int.mul_assoc]
    _ = c * a * a + c * b * b - 2 * (c * a * b) := by
      have hcomm : c * b * a = c * a * b := by ac_rfl
      rw [hcomm]
      omega


private theorem fullCommonEnergyCast {n : Nat}
    (ring : DirectedRing n) (k : Nat) (f : SealObs n) :
    (fullCommonSuccessorSquaredEnergy ring k f : Int) =
      ((tasepFrontConfigSlice n k).map (fun F =>
        ((tasepFrontConfigSlice n k).map (fun G =>
          (tasepCommonSuccessorPairCount ring F G : Int) *
            ((f F - f G) * (f F - f G)))).sum)).sum := by
  unfold fullCommonSuccessorSquaredEnergy
  calc
    (((tasepFrontConfigSlice n k).map (fun F =>
      ((tasepFrontConfigSlice n k).map (fun G =>
        tasepCommonSuccessorPairCount ring F G *
          frontSquaredGap f F G)).sum)).sum : Int) =
      ((tasepFrontConfigSlice n k).map (fun F =>
        (((tasepFrontConfigSlice n k).map (fun G =>
          tasepCommonSuccessorPairCount ring F G *
            frontSquaredGap f F G)).sum : Int))).sum := castMapSumNat _ _
    _ = ((tasepFrontConfigSlice n k).map (fun F =>
        ((tasepFrontConfigSlice n k).map (fun G =>
          ((tasepCommonSuccessorPairCount ring F G *
            frontSquaredGap f F G : Nat) : Int))).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro F _
      exact castMapSumNat _ _
    _ = _ := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro F _
      apply congrArg List.sum
      apply List.map_congr_left
      intro G _
      have hs : (frontSquaredGap f F G : Int) =
          (f F - f G) * (f F - f G) := by
        simpa [frontSquaredGap, Nat.pow_two] using
          (Int.natAbs_mul_self (a := f F - f G))
      rw [Int.natCast_mul, hs]


private theorem commonRowSumInt {n : Nat}
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat)
    (F : Fin n -> Bool) (hF : F ∈ tasepFrontConfigSlice n k) :
    ((tasepFrontConfigSlice n k).map (fun G =>
      (tasepCommonSuccessorPairCount ring F G : Int))).sum =
      ((n ^ 2 : Nat) : Int) := by
  calc
    _ = (((tasepFrontConfigSlice n k).map
        (tasepCommonSuccessorPairCount ring F)).sum : Int) :=
      (castMapSumNat _ _).symm
    _ = ((n ^ 2 : Nat) : Int) := by
      rw [tasepCommonSuccessorPairCount_sum_fixedSlice ring hn k F hF]


private theorem commonColSumInt {n : Nat}
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat)
    (G : Fin n -> Bool) (hG : G ∈ tasepFrontConfigSlice n k) :
    ((tasepFrontConfigSlice n k).map (fun F =>
      (tasepCommonSuccessorPairCount ring F G : Int))).sum =
      ((n ^ 2 : Nat) : Int) := by
  calc
    _ = (((tasepFrontConfigSlice n k).map (fun F =>
        tasepCommonSuccessorPairCount ring F G)).sum : Int) :=
      (castMapSumNat _ _).symm
    _ = ((n ^ 2 : Nat) : Int) := by
      rw [tasepCommonSuccessorPairCount_sum_fixedSlice_reverse ring hn k G hG]


private theorem fullCommonEnergySplit {n : Nat}
    (ring : DirectedRing n) (k : Nat) (f : SealObs n) :
    (fullCommonSuccessorSquaredEnergy ring k f : Int) =
      sealCommonLeftSquareInt ring k f + sealCommonRightSquareInt ring k f -
        2 * sealPStarQuadraticInt ring k f := by
  rw [fullCommonEnergyCast]
  unfold sealCommonLeftSquareInt sealCommonRightSquareInt sealPStarQuadraticInt
  calc
    _ = ((tasepFrontConfigSlice n k).map (fun F =>
      ((tasepFrontConfigSlice n k).map (fun G =>
        (tasepCommonSuccessorPairCount ring F G : Int) * (f F * f F) +
        (tasepCommonSuccessorPairCount ring F G : Int) * (f G * f G) -
        2 * ((tasepCommonSuccessorPairCount ring F G : Int) * f F * f G))).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro F _
      apply congrArg List.sum
      apply List.map_congr_left
      intro G _
      simpa [Int.mul_assoc] using
        weightedSquareSplit (tasepCommonSuccessorPairCount ring F G : Int) (f F) (f G)
    _ = _ := by
      calc
        _ = ((tasepFrontConfigSlice n k).map (fun F =>
          ((tasepFrontConfigSlice n k).map (fun G =>
            (tasepCommonSuccessorPairCount ring F G : Int) * (f F * f F))).sum +
          ((tasepFrontConfigSlice n k).map (fun G =>
            (tasepCommonSuccessorPairCount ring F G : Int) * (f G * f G))).sum -
          2 * ((tasepFrontConfigSlice n k).map (fun G =>
            (tasepCommonSuccessorPairCount ring F G : Int) * f F * f G)).sum)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro F _
          rw [isumMapSub, isumMapAdd, isumMapMulLeft]
        _ = _ := by
          try simp only [sealCommonLeftSquareInt, sealCommonRightSquareInt, sealPStarQuadraticInt]
          rw [isumMapSub, isumMapAdd, isumMapMulLeft]


private theorem leftSquareNormalized {n : Nat}
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat) (f : SealObs n) :
    sealCommonLeftSquareInt ring k f =
      ((n ^ 2 : Nat) : Int) * sealSliceSquareInt k f := by
  unfold sealCommonLeftSquareInt sealSliceSquareInt
  calc
    _ = ((tasepFrontConfigSlice n k).map (fun F =>
        (f F * f F) * ((tasepFrontConfigSlice n k).map (fun G =>
          (tasepCommonSuccessorPairCount ring F G : Int))).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro F _
      rw [<- isumMapMulLeft]
      apply congrArg List.sum
      apply List.map_congr_left
      intro G _
      ac_rfl
    _ = ((tasepFrontConfigSlice n k).map (fun F =>
        (f F * f F) * ((n ^ 2 : Nat) : Int))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro F hF
      rw [commonRowSumInt ring hn k F hF]
    _ = _ := by
      rw [<- isumMapMulLeft]
      apply congrArg List.sum
      apply List.map_congr_left
      intro F _
      ac_rfl


private theorem rightSquareNormalized {n : Nat}
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat) (f : SealObs n) :
    sealCommonRightSquareInt ring k f =
      ((n ^ 2 : Nat) : Int) * sealSliceSquareInt k f := by
  unfold sealCommonRightSquareInt sealSliceSquareInt
  rw [isumMapComm]
  calc
    _ = ((tasepFrontConfigSlice n k).map (fun G =>
        (f G * f G) * ((tasepFrontConfigSlice n k).map (fun F =>
          (tasepCommonSuccessorPairCount ring F G : Int))).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro G _
      rw [<- isumMapMulLeft]
      apply congrArg List.sum
      apply List.map_congr_left
      intro F _
      ac_rfl
    _ = ((tasepFrontConfigSlice n k).map (fun G =>
        (f G * f G) * ((n ^ 2 : Nat) : Int))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro G hG
      rw [commonColSumInt ring hn k G hG]
    _ = _ := by
      rw [<- isumMapMulLeft]
      apply congrArg List.sum
      apply List.map_congr_left
      intro G _
      ac_rfl


/-- Item 1.  Since `sealPStarQuadraticInt / n^2` is `||P* f||_2^2`, this is
`Var(f) - Var(P* f) = E_(P P*)(f)` after uniform-slice normalization. -/
theorem sealPStar_variance_drop_wordSum {n : Nat}
    (ring : DirectedRing n) (hn : 1 < n) (k : Nat)
    (f : SealObs n) (_hcenter : sealSliceIntSum k f = 0) :
    (fullCommonSuccessorSquaredEnergy ring k f : Int) +
        2 * sealPStarQuadraticInt ring k f =
      2 * (((n ^ 2 : Nat) : Int) * sealSliceSquareInt k f) := by
  rw [fullCommonEnergySplit ring k f,
    leftSquareNormalized ring hn k f,
    rightSquareNormalized ring hn k f]
  omega


/-- Incoming one-step numerator: exactly `n * P* f`. -/
noncomputable def sealPStarNumerator {n : Nat}
    (ring : DirectedRing n) (k : Nat) (f : SealObs n) : SealObs n :=
  fun G => ((tasepSliceIncomingPairs ring k G).map (fun p => f p.1)).sum


noncomputable def sealPStarNumeratorIter {n : Nat}
    (ring : DirectedRing n) (k : Nat) (f : SealObs n) : Nat -> SealObs n
  | 0 => f
  | t + 1 => sealPStarNumerator ring k (sealPStarNumeratorIter ring k f t)


/-- Item 2, exact cleared form.  Dividing by `n^(2*t)` gives squared-L2 decay
by `(1 - 1/(4*n^3))^t`; specializing `t = 16*n^4` is the requested horizon. -/
def SealTasepGeometricL2DecayAt {n : Nat}
    (ring : DirectedRing n) (k : Nat) : Prop :=
  1 < n -> SealTasepPoincareAt ring k ->
    forall f : SealObs n, sealSliceIntSum k f = 0 -> forall t : Nat,
      (4 * n ^ 3) ^ t *
          sealAllPairsSquaredEnergy k (sealPStarNumeratorIter ring k f t) <=
        (n ^ 2 * (4 * n ^ 3 - 1)) ^ t *
          sealAllPairsSquaredEnergy k f


/-- Item 3.  This isolates exactly the remaining L2-at-`16*n^4` to marked-11
pointwise conversion, with the static Poincaré hypothesis inline. -/
def SealTasepL2ToPointwise16n4At {n : Nat}
    (ring : DirectedRing n) (k : Nat) : Prop :=
  3 <= n -> 2 <= k -> k < n -> SealTasepPoincareAt ring k ->
    (forall f : SealObs n, sealSliceIntSum k f = 0 ->
      (4 * n ^ 3) ^ (16 * n ^ 4) *
          sealAllPairsSquaredEnergy k
            (sealPStarNumeratorIter ring k f (16 * n ^ 4)) <=
        (n ^ 2 * (4 * n ^ 3 - 1)) ^ (16 * n ^ 4) *
          sealAllPairsSquaredEnergy k f) ->
    Q11574HalfStationaryMarked11At ring k (16 * n ^ 4)


end SealTasepL2Contraction
end PPLLCompleteMultiLeaderCleanup


#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepL2Contraction.sealPStar_variance_drop_wordSum
#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepL2Contraction.SealTasepGeometricL2DecayAt
#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepL2Contraction.SealTasepL2ToPointwise16n4At
