import Leader.Wu.Seal.JohnsonPoincareStatements


namespace PPLLCompleteMultiLeaderCleanup
namespace SealJohnsonSpectralRoute


open PPLL PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepFiniteTimeSol
open SealJohnsonEnergyIdentity SealJohnsonPoincareA2a


set_option autoImplicit false


/-! ## Incidence operators on the existing Boolean slice carrier -/


/-- Change one Boolean coordinate. -/
def sealSetBit {n : Nat} (F : Fin n -> Bool)
    (x : Fin n) (b : Bool) : Fin n -> Bool :=
  fun i => if i = x then b else F i


/-- Johnson down map: on the `(k-1)` slice, sum `f` over all one-bit
extensions to the `k` slice.  It is defined on the ambient Boolean cube so no
new dependent carrier is needed. -/
def sealJohnsonDown {n : Nat} (f : SealIntObs n) : SealIntObs n :=
  fun F =>
    (List.ofFn (fun x : Fin n =>
      if F x then 0 else f (sealSetBit F x true))).sum


/-- Johnson up map: on the `k` slice, sum `g` over all one-bit deletions to the
`(k-1)` slice. -/
def sealJohnsonUp {n : Nat} (g : SealIntObs n) : SealIntObs n :=
  fun F =>
    (List.ofFn (fun x : Fin n =>
      if F x then g (sealSetBit F x false) else 0)).sum


/-- The scalar in `T_k = 2 (c I - U D)`. -/
def sealJohnsonC (n k : Nat) : Nat :=
  k * (n + 1 - k)


/-- Integer square norm on one fixed-mass slice. -/
def sealJohnsonNormInt {n : Nat} (k : Nat)
    (f : SealIntObs n) : Int :=
  sealSliceIntDot k f f


/-- Quadratic form of the ordered-swap Laplacian. -/
def sealJohnsonDirichletInt {n : Nat} (k : Nat)
    (f : SealIntObs n) : Int :=
  sealSliceIntDot k f (sealOrderedSwapLaplacianInt k f)


/-- Square norm of `T_k f`. -/
def sealJohnsonLaplacianNormInt {n : Nat} (k : Nat)
    (f : SealIntObs n) : Int :=
  let Tf := sealOrderedSwapLaplacianInt k f
  sealSliceIntDot k Tf Tf


/-- Integral centering: no division by the slice cardinality. -/
def sealJohnsonCentered {n : Nat} (k : Nat)
    (phi : SealIntObs n) : SealIntObs n :=
  fun F =>
    ((tasepFrontConfigSlice n k).length : Int) * phi F -
      sealSliceIntSum k phi


/-! ## Lemma chain, in proof order -/


/-- 1. One-bit insertion/deletion stays in the neighboring mass slice. -/
def sealJohnsonSetBitSliceStatement : Prop :=
  forall (n k : Nat) (F : Fin n -> Bool) (x : Fin n),
    0 < k -> k <= n ->
      (F ∈ tasepFrontConfigSlice n (k - 1) -> F x = false ->
        sealSetBit F x true ∈ tasepFrontConfigSlice n k) /\
      (F ∈ tasepFrontConfigSlice n k -> F x = true ->
        sealSetBit F x false ∈ tasepFrontConfigSlice n (k - 1))


/-- 2. `U` is the counting-measure adjoint of `D`. -/
def sealJohnsonUpDownAdjointStatement : Prop :=
  forall (n k : Nat) (f g : SealIntObs n),
    0 < k -> k <= n ->
      sealSliceIntDot k f (sealJohnsonUp g) =
        sealSliceIntDot (k - 1) (sealJohnsonDown f) g


/-- 3. Johnson up/down commutator on level `k-1`:
`D_k U_{k-1} - U_{k-2} D_{k-1} = (n-2k+2) I`. -/
def sealJohnsonCommutatorStatement : Prop :=
  forall (n k : Nat) (g : SealIntObs n) (F : Fin n -> Bool),
    0 < k -> k <= n ->
    F ∈ tasepFrontConfigSlice n (k - 1) ->
      sealJohnsonDown (sealJohnsonUp g) F =
        sealJohnsonUp (sealJohnsonDown g) F +
          ((n : Int) - 2 * (k : Int) + 2) * g F


/-- 4. Ordered-swap Laplacian through incidence maps.  The factor two is
exactly because `(x,z)` and `(z,x)` are both present in the repository energy. -/
def sealJohnsonLaplacianUpDownStatement : Prop :=
  forall (n k : Nat) (f : SealIntObs n) (F : Fin n -> Bool),
    0 < k -> k <= n -> F ∈ tasepFrontConfigSlice n k ->
      sealOrderedSwapLaplacianInt k f F =
        2 * (sealJohnsonC n k : Int) * f F -
          2 * sealJohnsonUp (sealJohnsonDown f) F


/-- 5. `D` intertwines the ordered-swap Laplacians. -/
def sealJohnsonDownIntertwiningStatement : Prop :=
  forall (n k : Nat) (f : SealIntObs n) (F : Fin n -> Bool),
    0 < k -> k <= n ->
    F ∈ tasepFrontConfigSlice n (k - 1) ->
      sealJohnsonDown (sealOrderedSwapLaplacianInt k f) F =
        sealOrderedSwapLaplacianInt (k - 1) (sealJohnsonDown f) F


/-- 6. Down preserves mean zero. -/
def sealJohnsonDownMeanZeroStatement : Prop :=
  forall (n k : Nat) (f : SealIntObs n),
    0 < k -> k <= n ->
    sealSliceIntSum k f = 0 ->
      sealSliceIntSum (k - 1) (sealJohnsonDown f) = 0


/-- 7. The two scalar recurrences obtained from 2, 4 and 5. -/
def sealJohnsonQuadraticRecurrenceStatement : Prop :=
  forall (n k : Nat) (f : SealIntObs n),
    0 < k -> k <= n ->
    let g := sealJohnsonDown f
    let N := sealJohnsonNormInt k f
    let E := sealJohnsonDirichletInt k f
    let M := sealJohnsonLaplacianNormInt k f
    let H := sealJohnsonNormInt (k - 1) g
    let Edown := sealJohnsonDirichletInt (k - 1) g
    let c : Int := (sealJohnsonC n k : Int)
    E = 2 * c * N - 2 * H /\
      2 * Edown = 2 * c * E - M


/-- 8. Finite integer Cauchy.  This can be proved without a field, e.g. by the
usual sum-of-squares/Lagrange identity on the finite slice list. -/
def sealJohnsonCauchyStatement : Prop :=
  forall (n k : Nat) (f g : SealIntObs n),
    sealSliceIntDot k f g ^ 2 <=
      sealJohnsonNormInt k f * sealJohnsonNormInt k g


/-- 9. Elementary coefficient bound needed only in the `H = 0` branch. -/
def sealJohnsonCoefficientBoundStatement : Prop :=
  forall (n k : Nat),
    0 < k -> k < n -> n <= sealJohnsonC n k


/-- 10. Pure scalar closure of the induction step. -/
def sealJohnsonFactorClosureStatement : Prop :=
  forall (n k : Nat) (N E M H : Int),
    0 <= N -> 0 <= H ->
    (n : Int) <= (sealJohnsonC n k : Int) ->
    E = 2 * (sealJohnsonC n k : Int) * N - 2 * H ->
    4 * (n : Int) * H <=
      2 * (sealJohnsonC n k : Int) * E - M ->
    E ^ 2 <= N * M ->
      2 * (n : Int) * N <= E


/-- 11. Base level.  Mean zero kills `D_1 f`, so `T_1 f = 2 n f`. -/
def sealJohnsonBaseGapStatement : Prop :=
  forall (n : Nat) (f : SealIntObs n),
    1 < n -> sealSliceIntSum 1 f = 0 ->
      2 * (n : Int) * sealJohnsonNormInt 1 f <=
        sealJohnsonDirichletInt 1 f


/-- 12. Sharp induction step in `k`.  The hypothesis is precisely the sharp
level-`k-1` gap applied to `D_k f`. -/
def sealJohnsonInductionStepStatement : Prop :=
  forall (n k : Nat) (f : SealIntObs n),
    1 < k -> k < n ->
    sealSliceIntSum k f = 0 ->
    2 * (n : Int) *
        sealJohnsonNormInt (k - 1) (sealJohnsonDown f) <=
      sealJohnsonDirichletInt (k - 1) (sealJohnsonDown f) ->
      2 * (n : Int) * sealJohnsonNormInt k f <=
        sealJohnsonDirichletInt k f


/-- 13. Sharp mean-zero ordered-swap gap. -/
def sealJohnsonMeanZeroGapStatement : Prop :=
  forall (n k : Nat) (f : SealIntObs n),
    0 < k -> k < n -> sealSliceIntSum k f = 0 ->
      2 * (n : Int) * sealJohnsonNormInt k f <=
        sealJohnsonDirichletInt k f


/-- 14. The nontrivial fixed-mass slice is nonempty, needed for cancellation
when returning from integral centering. -/
def sealJohnsonSliceCardPositiveStatement : Prop :=
  forall (n k : Nat),
    0 < k -> k < n -> 0 < (tasepFrontConfigSlice n k).length


/-- 15. Integral centering is mean zero and scales both repository energies by
exactly `S^2`. -/
def sealJohnsonCenteringStatement : Prop :=
  forall (n k : Nat) (phi : SealIntObs n),
    0 < k -> k < n ->
    let S := (tasepFrontConfigSlice n k).length
    let f := sealJohnsonCentered k phi
    sealSliceIntSum k f = 0 /\
      sealAllPairsSquaredEnergy k f =
        S ^ 2 * sealAllPairsSquaredEnergy k phi /\
      sealArbitraryTranspositionEnergy k f =
        S ^ 2 * sealArbitraryTranspositionEnergy k phi


/-- 16. Final bridge to the exact A2a target.  The imported all-pairs and Green
statements supply the two finite-sum identities; no spectral decomposition is
used. -/
def sealJohnsonUpDownClosesStatement : Prop :=
  sealJohnsonMeanZeroGapStatement ->
  sealJohnsonSliceCardPositiveStatement ->
  sealJohnsonCenteringStatement ->
  sealAllPairsMeanZeroStatement ->
  sealOrderedSwapGreenStatement ->
  sealJohnsonPoincareStatement


/-! ## Small executable checks of the key operator/arithmetic step -/


/-- One finite predicate checking the identities actually used in the induction
at a concrete `(n,k,phi)`.  It checks mean-zero centering, mean-zero after down,
the up/down Laplacian identity, the commutator, intertwining, both scalar
recurrences, Cauchy, and the resulting sharp `2n` gap. -/
def sealJohnsonKeyStepAt (n k : Nat) (phi : SealIntObs n) : Prop :=
  let f := sealJohnsonCentered k phi
  let g := sealJohnsonDown f
  let Tf := sealOrderedSwapLaplacianInt k f
  let c : Int := (sealJohnsonC n k : Int)
  let N := sealJohnsonNormInt k f
  let E := sealJohnsonDirichletInt k f
  let M := sealJohnsonLaplacianNormInt k f
  let H := sealJohnsonNormInt (k - 1) g
  let Edown := sealJohnsonDirichletInt (k - 1) g
  sealSliceIntSum k f = 0 /\
  sealSliceIntSum (k - 1) g = 0 /\
  (forall F, F ∈ tasepFrontConfigSlice n k ->
    Tf F = 2 * c * f F - 2 * sealJohnsonUp g F) /\
  (forall F, F ∈ tasepFrontConfigSlice n (k - 1) ->
    sealJohnsonDown (sealJohnsonUp g) F =
      sealJohnsonUp (sealJohnsonDown g) F +
        ((n : Int) - 2 * (k : Int) + 2) * g F) /\
  (forall F, F ∈ tasepFrontConfigSlice n (k - 1) ->
    sealJohnsonDown Tf F =
      sealOrderedSwapLaplacianInt (k - 1) g F) /\
  (n : Int) <= c /\
  E = 2 * c * N - 2 * H /\
  2 * Edown = 2 * c * E - M /\
  E ^ 2 <= N * M /\
  2 * (n : Int) * N <= E


/-- Small non-eigenvector observables for executable route checks. -/
def sealRoutePhi2 (F : Fin 2 -> Bool) : Int :=
  (if F 0 then 2 else -1) +
    (if F 1 then -1 else 1)


def sealRoutePhi3 (F : Fin 3 -> Bool) : Int :=
  (if F 0 && F 1 then 3 else 0) +
    (if F 2 then -2 else 1)


def sealRoutePhi5 (F : Fin 5 -> Bool) : Int :=
  (if F 0 && F 2 then 3 else -1) +
    (if F 1 then -2 else 1) +
    (if F 4 then 4 else -1)


/-- `n = 2`, base slice. -/
theorem seal_up_down_key_n2_k1_check :
    sealJohnsonKeyStepAt 2 1 sealRoutePhi2 := by
  unfold sealJohnsonKeyStepAt
  decide


/-- `n = 3`, nontrivial induction side `k = 2`. -/
theorem seal_up_down_key_n3_k2_check :
    sealJohnsonKeyStepAt 3 2 sealRoutePhi3 := by
  unfold sealJohnsonKeyStepAt
  decide


/-- `n = 4`, use the accepted point observable, which has higher Johnson
content and is strict in the Poincare inequality. -/
theorem seal_up_down_key_n4_k2_check :
    sealJohnsonKeyStepAt 4 2 sealPointPhi4 := by
  unfold sealJohnsonKeyStepAt
  decide


/-- `n = 5`, `k = 3` also checks the route beyond the half-slice; no complement
argument is needed by the up/down induction. -/
theorem seal_up_down_key_n5_k3_check :
    sealJohnsonKeyStepAt 5 3 sealRoutePhi5 := by
  unfold sealJohnsonKeyStepAt
  decide


end SealJohnsonSpectralRoute
end PPLLCompleteMultiLeaderCleanup


#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.seal_up_down_key_n2_k1_check
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.seal_up_down_key_n3_k2_check
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.seal_up_down_key_n4_k2_check
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.seal_up_down_key_n5_k3_check
