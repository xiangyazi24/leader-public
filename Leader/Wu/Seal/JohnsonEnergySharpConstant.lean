import Leader.Wu.Seal.TasepFiniteTime

namespace PPLLCompleteMultiLeaderCleanup
namespace SealJohnsonEnergyIdentity

open PPLL PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepFiniteTimeSol

set_option autoImplicit false

/-!
# Complete-transposition energy on a fixed-mass slice

This file records a small exact obstruction that is important for the seal
mixing route.

The complete coordinate-transposition chain on a fixed-mass Boolean slice is
the Johnson walk.  Its Dirichlet energy is *not* a fixed multiple of the full
slice variance for arbitrary observables.  The sharp statement needed
is an inequality

  2 * n * A_all <= |Omega| * A_trans,

not an identity.

The closed n = 4, k = 2 calculations below give two observables with distinct
energy/variance ratios.  They also show that this constant is attained
by a coordinate indicator, so the desired inequality constant is sharp.
-/

/-- Exchange two arbitrary coordinates.  This is the same literal operation
used downstream by `transposeFrontConfig`; it is repeated here because this
stage is required to import only `PPartialSealSweepTasepFiniteTimeSol`. -/
def sealTransposeFrontConfig {n : Nat}
    (F : Fin n -> Bool) (x z : Fin n) : Fin n -> Bool :=
  fun i => if i = x then F z else if i = z then F x else F i

/-- Squared integer gap, kept in Nat exactly as in the later comparison files. -/
def sealSquaredGap {n : Nat}
    (phi : (Fin n -> Bool) -> Int)
    (F G : Fin n -> Bool) : Nat :=
  Int.natAbs (phi F - phi G) ^ 2

/-- Unnormalized all-pairs squared variation on the mass-k slice. -/
def sealAllPairsSquaredEnergy {n : Nat} (k : Nat)
    (phi : (Fin n -> Bool) -> Int) : Nat :=
  ((tasepFrontConfigSlice n k).map (fun F =>
    ((tasepFrontConfigSlice n k).map (fun G =>
      sealSquaredGap phi F G)).sum)).sum

/-- Unnormalized complete-transposition energy.  Ordered coordinate
pairs are used; diagonal and same-bit swaps are retained but contribute zero. -/
def sealArbitraryTranspositionEnergy {n : Nat} (k : Nat)
    (phi : (Fin n -> Bool) -> Int) : Nat :=
  (List.ofFn (fun x : Fin n =>
    (List.ofFn (fun z : Fin n =>
      ((tasepFrontConfigSlice n k).map (fun F =>
        sealSquaredGap phi F
          (sealTransposeFrontConfig F x z))).sum)).sum)).sum

/-! ## The smallest useful closed Johnson-slice witness -/

/-- First Johnson eigenspace witness: occupancy of coordinate zero. -/
def sealLinearPhi4 (F : Fin 4 -> Bool) : Int :=
  if F 0 then 1 else 0

/-- A point indicator on the mass-two slice: only `{0,1}` has value one. -/
def sealPointPhi4 (F : Fin 4 -> Bool) : Int :=
  if F 0 && F 1 then 1 else 0

theorem seal_massTwo_sliceFour_card :
    (tasepFrontConfigSlice 4 2).length = 6 := by
  decide

theorem seal_linear_allPairs :
    sealAllPairsSquaredEnergy 2 sealLinearPhi4 = 18 := by
  decide

theorem seal_linear_transposition :
    sealArbitraryTranspositionEnergy 2 sealLinearPhi4 = 24 := by
  decide

theorem seal_point_allPairs :
    sealAllPairsSquaredEnergy 2 sealPointPhi4 = 10 := by
  decide

theorem seal_point_transposition :
    sealArbitraryTranspositionEnergy 2 sealPointPhi4 = 16 := by
  decide

/-- The denominator-cleared sharp constant is attained by the linear
coordinate indicator at n = 4, k = 2. -/
theorem seal_q11607_constant_attained :
    2 * 4 * sealAllPairsSquaredEnergy 2 sealLinearPhi4 =
      (tasepFrontConfigSlice 4 2).length *
        sealArbitraryTranspositionEnergy 2 sealLinearPhi4 := by
  rw [seal_massTwo_sliceFour_card,
    seal_linear_allPairs, seal_linear_transposition]

/-- The same expression is strictly larger on the point indicator.  Hence the
sharp Poincare relation cannot be an identity for all observables. -/
theorem seal_q11607_relation_strict_for_point :
    2 * 4 * sealAllPairsSquaredEnergy 2 sealPointPhi4 <
      (tasepFrontConfigSlice 4 2).length *
        sealArbitraryTranspositionEnergy 2 sealPointPhi4 := by
  rw [seal_massTwo_sliceFour_card,
    seal_point_allPairs, seal_point_transposition]
  decide

/-- Direct negation of the requested universal equality at the sharp
constant. -/
theorem seal_q11607_not_an_identity :
    ¬ (forall phi : (Fin 4 -> Bool) -> Int,
      2 * 4 * sealAllPairsSquaredEnergy 2 phi =
        (tasepFrontConfigSlice 4 2).length *
          sealArbitraryTranspositionEnergy 2 phi) := by
  intro h
  have hp := h sealPointPhi4
  have hs := seal_q11607_relation_strict_for_point
  exact (Nat.ne_of_lt hs) hp

/-- Stronger obstruction: there is no positive rational proportionality
constant `q/p` for which transposition energy equals that constant times
all-pairs variation for every observable on this slice. -/
theorem seal_no_positive_rational_exact_multiple :
    ¬ (exists p q : Nat,
      0 < p /\ 0 < q /\
      forall phi : (Fin 4 -> Bool) -> Int,
        p * sealArbitraryTranspositionEnergy 2 phi =
          q * sealAllPairsSquaredEnergy 2 phi) := by
  rintro ⟨p, q, hp, hq, h⟩
  have hlinear := h sealLinearPhi4
  have hpoint := h sealPointPhi4
  rw [seal_linear_transposition, seal_linear_allPairs] at hlinear
  rw [seal_point_transposition, seal_point_allPairs] at hpoint
  omega

end SealJohnsonEnergyIdentity
end PPLLCompleteMultiLeaderCleanup

#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonEnergyIdentity.seal_massTwo_sliceFour_card
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonEnergyIdentity.seal_q11607_constant_attained
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonEnergyIdentity.seal_q11607_relation_strict_for_point
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonEnergyIdentity.seal_q11607_not_an_identity
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonEnergyIdentity.seal_no_positive_rational_exact_multiple
