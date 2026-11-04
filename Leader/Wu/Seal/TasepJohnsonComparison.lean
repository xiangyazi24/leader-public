import Leader.Wu.Seal.JohnsonPoincare
import Leader.Wu.Seal.MixingReduction
import Leader.Wu.Seal.TasepPointwisePoincare
import Leader.Wu.Seal.TasepArbitraryDistance

namespace PPLLCompleteMultiLeaderCleanup
namespace SealTasepMixingIntegration

open PPLL PPLLResearchFormulation PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepFiniteTimeSol
open PPartialSealSweepTasepMovingParticleComparisonSol
open PPartialSealSweepTasepPointwisePoincareSol
open PPartialSealSweepTasepArbitraryDistanceSol
open SealJohnsonEnergyIdentity SealJohnsonPoincareA2a
open SealJohnsonSpectralRoute
open Q11574FixedFrontMassMixing
open PPartialSealSweepABGateBreakthroughSol

set_option autoImplicit false
set_option Elab.async false

/-- Step 1: the sharp Johnson inequality on one interior mass slice. -/
def SealJohnsonPoincareAt {n : Nat} (k : Nat) : Prop :=
  forall phi : (Fin n -> Bool) -> Int,
    2 * n * sealAllPairsSquaredEnergy k phi <=
      (tasepFrontConfigSlice n k).length *
        sealArbitraryTranspositionEnergy k phi

/-- Step 2: the sharp static comparison from ordered transpositions to the
literal `P P*` full common-successor energy. -/
def SealTasepComparisonAt {n : Nat}
    (ring : DirectedRing n) (k : Nat) : Prop :=
  forall phi : (Fin n -> Bool) -> Int,
    sealArbitraryTranspositionEnergy k phi <=
      8 * n ^ 2 * fullCommonSuccessorSquaredEnergy ring k phi

/-- Step 3: denominator-cleared TASEP Poincare inequality.  After the standard
normalizations this is `Var_pi <= 4*n^3 E_(P P*)`. -/
def SealTasepPoincareAt {n : Nat}
    (ring : DirectedRing n) (k : Nat) : Prop :=
  forall phi : (Fin n -> Bool) -> Int,
    sealAllPairsSquaredEnergy k phi <=
      4 * n * (tasepFrontConfigSlice n k).length *
        fullCommonSuccessorSquaredEnergy ring k phi

/-- Step 4: the same inequality viewed as the spectral-gap statement for
`R = P P*`; normalized gap is at least `1 / (4*n^3)`. -/
def SealTasepSpectralGapAt {n : Nat}
    (ring : DirectedRing n) (k : Nat) : Prop :=
  SealTasepPoincareAt ring k

/-- Step 5: the still-missing dynamical bridge.  Its proof must implement the
one-step squared-L2 contraction, iterate it to `16*n^4`, then convert L2 to the
pointwise marked-event lower bound. -/
def SealTasepL2ToPointwise16n4At {n : Nat}
    (ring : DirectedRing n) (k : Nat) : Prop :=
  SealTasepSpectralGapAt ring k ->
    Q11574HalfStationaryMarked11At ring k (16 * n ^ 4)

/-- Step 6: the exact half-stationary contract. -/
def SealHalfStationary16n4At {n : Nat}
    (ring : DirectedRing n) (k : Nat) : Prop :=
  Q11574HalfStationaryMarked11At ring k (16 * n ^ 4)

private theorem sealTransposeFrontConfig_eq_transposeFrontConfig
    {n : Nat} (F : Fin n -> Bool) (x z : Fin n) :
    sealTransposeFrontConfig F x z = transposeFrontConfig F x z := by
  rfl

private theorem transpositionEnergy_bridge
    {n k : Nat} (ring : DirectedRing n)
    (phi : (Fin n -> Bool) -> Int) :
    sealArbitraryTranspositionEnergy k phi =
      arbitraryTranspositionEnergy ring k phi := by
  unfold sealArbitraryTranspositionEnergy arbitraryTranspositionEnergy
  unfold tasepFinIndexList arbitrarySliceSum
  simp only [List.map_ofFn, Function.comp_def]
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext x
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext z
  apply congrArg List.sum
  apply List.map_congr_left
  intro F _hF
  unfold sealSquaredGap frontSquaredGap
  rw [sealTransposeFrontConfig_eq_transposeFrontConfig F x z]

private theorem adjacent_to_full_common
    {n k : Nat} (ring : DirectedRing n) (hn : 3 <= n)
    (phi : (Fin n -> Bool) -> Int) :
    n * adjacentCyclicSquaredEnergy ring k phi <=
      2 * fullCommonSuccessorSquaredEnergy ring k phi := by
  simpa [adjacentCyclicSquaredEnergy, fullCommonSuccessorSquaredEnergy,
    frontSquaredGap] using
    (n_mul_sum_fixedSlice_allSwapEdge_squaredGap_le_two_mul_commonSuccessor_squaredGap
      ring hn k phi)

/-- Available static comparison, with no conservative extra factor `n`. -/
theorem sealJohnson_to_tasepComparison
    {n k : Nat} (ring : DirectedRing n) (hn : 3 <= n) :
    SealTasepComparisonAt ring k := by
  intro phi
  rw [transpositionEnergy_bridge ring phi]
  have hroute :=
    arbitraryTranspositionEnergy_le_four_mul_cube_adjacent
      (k := k) ring (by omega) phi
  have hadj := adjacent_to_full_common (k := k) ring hn phi
  have hscaled :
      n * arbitraryTranspositionEnergy ring k phi <=
        n * (8 * n ^ 2 * fullCommonSuccessorSquaredEnergy ring k phi) := by
    calc
      n * arbitraryTranspositionEnergy ring k phi <=
          n * (4 * n ^ 3 * adjacentCyclicSquaredEnergy ring k phi) :=
        Nat.mul_le_mul_left n hroute
      _ = 4 * n ^ 3 *
          (n * adjacentCyclicSquaredEnergy ring k phi) := by ac_rfl
      _ <= 4 * n ^ 3 *
          (2 * fullCommonSuccessorSquaredEnergy ring k phi) :=
        Nat.mul_le_mul_left (4 * n ^ 3) hadj
      _ = n * (8 * n ^ 2 *
          fullCommonSuccessorSquaredEnergy ring k phi) := by
        rw [show (8 : Nat) = 4 * 2 from rfl, Nat.pow_succ]
        ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled (by omega)

/-- First integration link requested in this round: the proved Johnson gap plus
the available comparisons gives the sharp reversiblized TASEP Poincare bound. -/
theorem sealJohnson_to_tasepPoincare
    {n k : Nat} (ring : DirectedRing n)
    (hn : 3 <= n) (hk : 0 < k) (hkn : k < n) :
    SealTasepPoincareAt ring k := by
  intro phi
  have hj := sealJohnsonPoincare n k phi hk hkn
  have hc := sealJohnson_to_tasepComparison (k := k) ring hn phi
  have hchain :
      2 * n * sealAllPairsSquaredEnergy k phi <=
        (tasepFrontConfigSlice n k).length *
          (8 * n ^ 2 * fullCommonSuccessorSquaredEnergy ring k phi) := by
    exact Nat.le_trans hj
      (Nat.mul_le_mul_left (tasepFrontConfigSlice n k).length hc)
  have hscaled :
      2 * n * sealAllPairsSquaredEnergy k phi <=
        2 * n *
          (4 * n * (tasepFrontConfigSlice n k).length *
            fullCommonSuccessorSquaredEnergy ring k phi) := by
    calc
      2 * n * sealAllPairsSquaredEnergy k phi <=
          (tasepFrontConfigSlice n k).length *
            (8 * n ^ 2 * fullCommonSuccessorSquaredEnergy ring k phi) :=
        hchain
      _ = 2 * n *
          (4 * n * (tasepFrontConfigSlice n k).length *
            fullCommonSuccessorSquaredEnergy ring k phi) := by
        rw [Nat.pow_two, show (8 : Nat) = 2 * 4 from rfl]
        ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled (by omega)

/-- Poincare and spectral-gap packaging are the same denominator-cleared fact. -/
theorem tasepPoincare_to_spectralGap
    {n k : Nat} (ring : DirectedRing n)
    (h : SealTasepPoincareAt ring k) :
    SealTasepSpectralGapAt ring k := h

/-- Everything after the static gap is now isolated in one explicit missing
finite-time L2-to-pointwise proposition. -/
theorem halfStationary_of_l2ToPointwise
    {n k : Nat} (ring : DirectedRing n)
    (hgap : SealTasepSpectralGapAt ring k)
    (hl2 : SealTasepL2ToPointwise16n4At ring k) :
    SealHalfStationary16n4At ring k :=
  hl2 hgap

/-- Once the dynamical bridge is supplied, the half-stationary contract packages the endpoint bound. -/
theorem endpointBound_of_integration
    {n k : Nat} (ring : DirectedRing n)
    (hn : 3 <= n) (hk : 2 <= k) (hkn : k < n)
    (hl2 : SealTasepL2ToPointwise16n4At ring k) :
    FixedFrontMassTasepMarked11EndpointBoundAt
      ring k (16 * n ^ 4) := by
  have hgap : SealTasepSpectralGapAt ring k :=
    tasepPoincare_to_spectralGap ring
      (sealJohnson_to_tasepPoincare ring hn (by omega) hkn)
  exact q11574_fixedFrontMassTasepMarked11EndpointBoundAt_16n4_of_halfStationary
    ring hn hk hkn (hl2 hgap)

end SealTasepMixingIntegration
end PPLLCompleteMultiLeaderCleanup

#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepMixingIntegration.sealJohnson_to_tasepComparison
#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepMixingIntegration.sealJohnson_to_tasepPoincare
#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepMixingIntegration.endpointBound_of_integration
