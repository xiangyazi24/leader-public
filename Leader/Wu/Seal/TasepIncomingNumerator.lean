import Leader.Wu.Seal.TasepFiberPartition
import Leader.Wu.Seal.TasepJohnsonComparison

namespace PPLLCompleteMultiLeaderCleanup
namespace SealTasepGeometricDecay

open PPLL PPLLResearchFormulation PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepABGateBreakthroughSol
open PPartialSealSweepTasepFiniteTimeSol PPartialSealSweepTasepPointwisePoincareSol
open PPartialSealSweepTasepMovingParticleComparisonSol
open SealJohnsonEnergyIdentity SealTasepL2Contraction
open SealTasepGeometricDecayFiberList

set_option autoImplicit false
set_option Elab.async false

private theorem incomingEqFilter {n : Nat} (ring : DirectedRing n) (k : Nat)
    (G : Fin n -> Bool) :
    tasepSliceIncomingPairs ring k G =
      (tasepSliceSchedulerPairs n k).filter
        (fun p => eqb (localStep ring clockwiseTasepPair p.1 p.2) G) := by
  classical
  unfold tasepSliceIncomingPairs
  apply congrArg
    (fun q : (((Fin n -> Bool) × Fin n) -> Bool) =>
      (tasepSliceSchedulerPairs n k).filter q)
  funext p
  by_cases h : localStep ring clockwiseTasepPair p.1 p.2 = G <;>
    simp [eqb, h]

private theorem schedulerEndpointMem {n k : Nat} (ring : DirectedRing n)
    (hn : 1 < n) (p : (Fin n -> Bool) × Fin n)
    (hp : p ∈ tasepSliceSchedulerPairs n k) :
    localStep ring clockwiseTasepPair p.1 p.2 ∈
      tasepFrontConfigSlice n k := by
  have hF := (mem_tasepSliceSchedulerPairs_iff p.1 p.2).mp hp
  rw [mem_tasepFrontConfigSlice_iff] at hF ⊢
  exact (frontConfigMass_clockwiseTasep_localStep ring hn p.1 p.2).trans hF

private theorem commonCountCast {n : Nat} (ring : DirectedRing n)
    (F G : Fin n -> Bool) :
    (tasepCommonSuccessorPairCount ring F G : Int) =
      (List.ofFn (fun first : Fin n =>
        (List.ofFn (fun second : Fin n =>
          if eqb (localStep ring clockwiseTasepPair F first)
              (localStep ring clockwiseTasepPair G second)
          then (1 : Int) else 0)).sum)).sum := by
  classical
  unfold tasepCommonSuccessorPairCount
  rw [castOfFnSumNat]
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext first
  rw [castOfFnSumNat]
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext second
  by_cases h : localStep ring clockwiseTasepPair F first =
      localStep ring clockwiseTasepPair G second <;> simp [eqb, h]

private theorem commonWeighted {n : Nat} (ring : DirectedRing n)
    (F G : Fin n -> Bool) (a b : Int) :
    (List.ofFn (fun first : Fin n =>
      (List.ofFn (fun second : Fin n =>
        if eqb (localStep ring clockwiseTasepPair F first)
            (localStep ring clockwiseTasepPair G second)
        then a * b else 0)).sum)).sum =
      (tasepCommonSuccessorPairCount ring F G : Int) * a * b := by
  calc
    _ = (List.ofFn (fun first : Fin n =>
        (List.ofFn (fun second : Fin n =>
          (if eqb (localStep ring clockwiseTasepPair F first)
              (localStep ring clockwiseTasepPair G second)
           then (1 : Int) else 0) * (a * b))).sum)).sum := by
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext first
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext second
      cases h : eqb (localStep ring clockwiseTasepPair F first)
          (localStep ring clockwiseTasepPair G second) <;> simp [h]
    _ = (List.ofFn (fun first : Fin n =>
        (List.ofFn (fun second : Fin n =>
          if eqb (localStep ring clockwiseTasepPair F first)
              (localStep ring clockwiseTasepPair G second)
          then (1 : Int) else 0)).sum * (a * b))).sum := by
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext first
      exact isumOfFnMulRight _ _
    _ = (List.ofFn (fun first : Fin n =>
        (List.ofFn (fun second : Fin n =>
          if eqb (localStep ring clockwiseTasepPair F first)
              (localStep ring clockwiseTasepPair G second)
          then (1 : Int) else 0)).sum)).sum * (a * b) :=
      isumOfFnMulRight _ _
    _ = _ := by rw [<- commonCountCast ring F G]; ac_rfl

private theorem schedulerCommonQuadratic {n : Nat} (ring : DirectedRing n)
    (k : Nat) (f : SealObs n) :
    ((tasepSliceSchedulerPairs n k).map (fun p =>
      ((tasepSliceSchedulerPairs n k).map (fun q =>
        if eqb (localStep ring clockwiseTasepPair p.1 p.2)
            (localStep ring clockwiseTasepPair q.1 q.2)
        then f p.1 * f q.1 else 0)).sum)).sum =
      sealPStarQuadraticInt ring k f := by
  classical
  unfold tasepSliceSchedulerPairs
  calc
    _ = ((tasepFrontConfigSlice n k).map (fun F =>
        (List.ofFn (fun first : Fin n =>
          ((tasepFrontConfigSlice n k).map (fun G =>
            (List.ofFn (fun second : Fin n =>
              if eqb (localStep ring clockwiseTasepPair F first)
                  (localStep ring clockwiseTasepPair G second)
              then f F * f G else 0)).sum)).sum)).sum)).sum := by
      simp only [isumFlatMap, List.map_ofFn, Function.comp_def]
    _ = ((tasepFrontConfigSlice n k).map (fun F =>
        ((tasepFrontConfigSlice n k).map (fun G =>
          (List.ofFn (fun first : Fin n =>
            (List.ofFn (fun second : Fin n =>
              if eqb (localStep ring clockwiseTasepPair F first)
                  (localStep ring clockwiseTasepPair G second)
              then f F * f G else 0)).sum)).sum)).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro F _
      simpa [List.map_ofFn, Function.comp_def] using
        (isumMapComm (List.ofFn (fun first : Fin n => first))
          (tasepFrontConfigSlice n k)
          (fun first G =>
            (List.ofFn (fun second : Fin n =>
              if eqb (localStep ring clockwiseTasepPair F first)
                  (localStep ring clockwiseTasepPair G second)
              then f F * f G else 0)).sum))
    _ = _ := by
      unfold sealPStarQuadraticInt
      apply congrArg List.sum
      apply List.map_congr_left
      intro F _
      apply congrArg List.sum
      apply List.map_congr_left
      intro G _
      exact commonWeighted ring F G (f F) (f G)

/-- The incoming numerator preserves slice sum, with the exact factor `n`. -/
theorem sealPStarNumerator_sum {n : Nat} (ring : DirectedRing n)
    (hn : 1 < n) (k : Nat) (f : SealObs n) :
    sealSliceIntSum k (sealPStarNumerator ring k f) =
      (n : Int) * sealSliceIntSum k f := by
  classical
  have hp := fiberPartitionSum (tasepSliceSchedulerPairs n k)
    (tasepFrontConfigSlice n k)
    (fun p => localStep ring clockwiseTasepPair p.1 p.2)
    (fun p => f p.1) (tasepFrontConfigSlice_nodup n k)
    (schedulerEndpointMem ring hn)
  calc
    sealSliceIntSum k (sealPStarNumerator ring k f) =
        ((tasepFrontConfigSlice n k).map (fun G =>
          (((tasepSliceSchedulerPairs n k).filter
            (fun p => eqb
              (localStep ring clockwiseTasepPair p.1 p.2) G)).map
                (fun p => f p.1)).sum)).sum := by
      unfold sealSliceIntSum sealPStarNumerator
      apply congrArg List.sum
      apply List.map_congr_left
      intro G _
      simp only [incomingEqFilter]
    _ = ((tasepSliceSchedulerPairs n k).map (fun p => f p.1)).sum := hp
    _ = (n : Int) * sealSliceIntSum k f := by
      unfold tasepSliceSchedulerPairs sealSliceIntSum
      rw [isumFlatMap]
      calc
        _ = ((tasepFrontConfigSlice n k).map
            (fun F => (n : Int) * f F)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro F _
          simpa [List.map_ofFn, Function.comp_def] using
            isumOfFnConst n (f F)
        _ = _ := isumMapMulLeft _ (n : Int) f

/-- The square norm of the incoming numerator is the common-successor quadratic form. -/
theorem sealPStarNumerator_square {n : Nat} (ring : DirectedRing n)
    (hn : 1 < n) (k : Nat) (f : SealObs n) :
    sealSliceSquareInt k (sealPStarNumerator ring k f) =
      sealPStarQuadraticInt ring k f := by
  classical
  have hp := fiberPartitionSquare (tasepSliceSchedulerPairs n k)
    (tasepFrontConfigSlice n k)
    (fun p => localStep ring clockwiseTasepPair p.1 p.2)
    (fun p => f p.1) (tasepFrontConfigSlice_nodup n k)
    (schedulerEndpointMem ring hn)
  calc
    sealSliceSquareInt k (sealPStarNumerator ring k f) =
        ((tasepFrontConfigSlice n k).map (fun G =>
          (((tasepSliceSchedulerPairs n k).filter
            (fun p => eqb
              (localStep ring clockwiseTasepPair p.1 p.2) G)).map
                (fun p => f p.1)).sum *
          (((tasepSliceSchedulerPairs n k).filter
            (fun p => eqb
              (localStep ring clockwiseTasepPair p.1 p.2) G)).map
                (fun p => f p.1)).sum)).sum := by
      unfold sealSliceSquareInt sealPStarNumerator
      apply congrArg List.sum
      apply List.map_congr_left
      intro G _
      simp only [incomingEqFilter]
    _ = ((tasepSliceSchedulerPairs n k).map (fun p =>
        ((tasepSliceSchedulerPairs n k).map (fun q =>
          if eqb (localStep ring clockwiseTasepPair p.1 p.2)
              (localStep ring clockwiseTasepPair q.1 q.2)
          then f p.1 * f q.1 else 0)).sum)).sum := hp
    _ = _ := schedulerCommonQuadratic ring k f

/-- Concrete cast bridge used by the one-step argument. -/
theorem sealSliceSquareInt_eq_normSq {n : Nat} (k : Nat) (f : SealObs n) :
    sealSliceSquareInt k f =
      (SealJohnsonPoincareA2a.sealSliceIntNormSq k f : Int) := by
  symm
  unfold SealJohnsonPoincareA2a.sealSliceIntNormSq sealSliceSquareInt
  calc
    _ = ((tasepFrontConfigSlice n k).map
        (fun F => ((Int.natAbs (f F) ^ 2 : Nat) : Int))).sum :=
      castMapSumNat _ _
    _ = _ := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro F _
      simpa [Nat.pow_two] using (Int.natAbs_mul_self (a := f F))

end SealTasepGeometricDecay
end PPLLCompleteMultiLeaderCleanup

#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepGeometricDecay.sealPStarNumerator_sum
#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepGeometricDecay.sealPStarNumerator_square
#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepGeometricDecay.sealSliceSquareInt_eq_normSq
