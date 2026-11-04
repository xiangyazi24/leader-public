import Leader.Wu.Seal.JohnsonQuadraticRecurrence
import Leader.Wu.Seal.JohnsonSliceIdentities

namespace PPLLCompleteMultiLeaderCleanup
namespace SealJohnsonSpectralRoute

open PPLL PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepMixingFirstBrickSol
open PPartialSealSweepTasepFiniteTimeSol
open SealJohnsonEnergyIdentity SealJohnsonPoincareA2a

set_option autoImplicit false
set_option Elab.async false

private theorem intMulSelfNonneg (a : Int) : 0 <= a * a := by
  by_cases ha : 0 <= a
  · exact Int.mul_nonneg ha ha
  · have ha' : a <= 0 := Int.le_of_not_le ha
    exact Int.mul_nonneg_of_nonpos_of_nonpos ha' ha'

private theorem listMapSumNonneg
    {α : Type} (xs : List α) (f : α -> Int)
    (h : forall x, 0 <= f x) : 0 <= (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Int.add_nonneg (h x) ih

private theorem sealJohnsonNormInt_nonneg
    {n : Nat} (k : Nat) (f : SealIntObs n) :
    0 <= sealJohnsonNormInt k f := by
  unfold sealJohnsonNormInt sealSliceIntDot
  apply listMapSumNonneg
  intro F
  exact intMulSelfNonneg (f F)

private theorem intPowTwo (x : Int) : x ^ 2 = x * x := by
  rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]

private theorem fourScale (n H : Int) :
    4 * n * H = 2 * (2 * n * H) := by
  have h4 : (4 : Int) = 2 * 2 := by omega
  rw [h4]
  ac_rfl

private theorem factorLeft
    (n c N E H : Int)
    (hE : E = 2 * c * N - 2 * H) :
    (4 * n * H) * N =
      (2 * n * N) * (2 * c * N - E) := by
  have hx : 2 * c * N - E = 2 * H := by omega
  rw [hx]
  have h4 : (4 : Int) = 2 * 2 := by omega
  rw [h4]
  ac_rfl

private theorem factorRight (c E N : Int) :
    E * (2 * c * N - E) =
      2 * c * E * N - E * E := by
  rw [Int.mul_sub]
  have h : E * (2 * c * N) = 2 * c * E * N := by ac_rfl
  rw [h]

private theorem listSqSumZeroOfLengthOne
    {α : Type} (xs : List α) (f : α -> Int)
    (hlen : xs.length = 1)
    (hsum : (xs.map f).sum = 0) :
    (xs.map (fun x => f x * f x)).sum = 0 := by
  cases xs with
  | nil => simp at hlen
  | cons a xs =>
      cases xs with
      | nil =>
          simp only [List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, Int.add_zero] at hsum ⊢
          rw [hsum]
          rfl
      | cons b xs =>
          simp only [List.length_cons] at hlen
          omega

private theorem levelZeroNorm_eq_zero
    {n : Nat} (f : SealIntObs n)
    (hzero : sealSliceIntSum 0 f = 0) :
    sealJohnsonNormInt 0 f = 0 := by
  have hlen : (tasepFrontConfigSlice n 0).length = 1 := by
    rw [tasepFrontConfigSlice_length_eq_card]
    exact frontSliceCard_any_zero n
  unfold sealJohnsonNormInt sealSliceIntDot
  apply listSqSumZeroOfLengthOne _ f hlen
  simpa [sealSliceIntSum] using hzero

/-- Step 9a: c_k = k(n+1-k) is at least n in every interior slice. -/
theorem sealJohnsonCoefficientBound :
    sealJohnsonCoefficientBoundStatement := by
  unfold sealJohnsonCoefficientBoundStatement
  intro n k hk hkn
  unfold sealJohnsonC
  have hsplit : n + 1 - k = (n - k) + 1 := by omega
  rw [hsplit, Nat.mul_add, Nat.mul_one]
  have hk1 : 1 <= k := by omega
  have hmul : n - k <= k * (n - k) := by
    calc
      n - k = 1 * (n - k) := by simp
      _ <= k * (n - k) := Nat.mul_le_mul_right (n - k) hk1
  omega

/-- Step 9b: scalar factor closure for the induction recurrence. -/
theorem sealJohnsonFactorClosure :
    sealJohnsonFactorClosureStatement := by
  unfold sealJohnsonFactorClosureStatement
  intro n k N E M H hN hH hnc hE hstep hc
  rw [intPowTwo] at hc
  by_cases hHz : H = 0
  · have hE0 : E = 2 * (sealJohnsonC n k : Int) * N := by
      rw [hHz] at hE
      simpa using hE
    have h2 :
        2 * (n : Int) <= 2 * (sealJohnsonC n k : Int) :=
      Int.mul_le_mul_of_nonneg_left hnc (by omega)
    have hm := Int.mul_le_mul_of_nonneg_right h2 hN
    rw [hE0]
    exact hm
  · have hHpos : 0 < H := by omega
    have hxpos :
        0 < 2 * (sealJohnsonC n k : Int) * N - E := by omega
    have hscaled := Int.mul_le_mul_of_nonneg_right hstep hN
    have hc' : E * E <= M * N := by
      calc
        E * E <= N * M := hc
        _ = M * N := Int.mul_comm _ _
    have hright :
        (2 * (sealJohnsonC n k : Int) * E - M) * N <=
          E * (2 * (sealJohnsonC n k : Int) * N - E) := by
      rw [Int.sub_mul, factorRight]
      omega
    have hprod :
        (2 * (n : Int) * N) *
            (2 * (sealJohnsonC n k : Int) * N - E) <=
          E * (2 * (sealJohnsonC n k : Int) * N - E) := by
      calc
        _ = (4 * (n : Int) * H) * N :=
          (factorLeft (n : Int) (sealJohnsonC n k : Int)
            N E H hE).symm
        _ <= (2 * (sealJohnsonC n k : Int) * E - M) * N := hscaled
        _ <= _ := hright
    by_cases hgoal : 2 * (n : Int) * N <= E
    · exact hgoal
    · have hlt : E < 2 * (n : Int) * N := by omega
      have hstrict := Int.mul_lt_mul_of_pos_right hlt hxpos
      omega

/-- Step 10a: the k=1 mean-zero gap. -/
theorem sealJohnsonBaseGap :
    sealJohnsonBaseGapStatement := by
  unfold sealJohnsonBaseGapStatement
  intro n f hn hzero
  have hdown :=
    sealJohnsonDownMeanZero n 1 f (by omega) (by omega) hzero
  have hH : sealJohnsonNormInt 0 (sealJohnsonDown f) = 0 :=
    levelZeroNorm_eq_zero (sealJohnsonDown f) (by simpa using hdown)
  have hr := sealJohnsonQuadraticRecurrence n 1 f (by omega) (by omega)
  have hfirst :
      sealJohnsonDirichletInt 1 f =
        2 * (sealJohnsonC n 1 : Int) * sealJohnsonNormInt 1 f -
          2 * sealJohnsonNormInt 0 (sealJohnsonDown f) := by
    simpa using hr.1
  have hc : sealJohnsonC n 1 = n := by simp [sealJohnsonC]
  rw [hc, hH] at hfirst
  omega

/-- Step 10b: one up-down induction step. -/
theorem sealJohnsonInductionStep :
    sealJohnsonInductionStepStatement := by
  unfold sealJohnsonInductionStepStatement
  intro n k f hk1 hkn hzero hgap
  have hk : 0 < k := by omega
  have hkle : k <= n := by omega
  let g := sealJohnsonDown f
  let N := sealJohnsonNormInt k f
  let E := sealJohnsonDirichletInt k f
  let M := sealJohnsonLaplacianNormInt k f
  let H := sealJohnsonNormInt (k - 1) g
  let Edown := sealJohnsonDirichletInt (k - 1) g
  let c : Int := (sealJohnsonC n k : Int)
  have hr := sealJohnsonQuadraticRecurrence n k f hk hkle
  change E = 2 * c * N - 2 * H /\
    2 * Edown = 2 * c * E - M at hr
  change 2 * (n : Int) * H <= Edown at hgap
  have hN : 0 <= N := sealJohnsonNormInt_nonneg k f
  have hH : 0 <= H := sealJohnsonNormInt_nonneg (k - 1) g
  have hcoeffNat := sealJohnsonCoefficientBound n k hk hkn
  have hcoeff : (n : Int) <= c := Int.ofNat_le.mpr hcoeffNat
  have htwice :=
    Int.mul_le_mul_of_nonneg_left hgap (by omega : (0 : Int) <= 2)
  have hstep : 4 * (n : Int) * H <= 2 * c * E - M := by
    calc
      4 * (n : Int) * H = 2 * (2 * (n : Int) * H) :=
        fourScale (n : Int) H
      _ <= 2 * Edown := htwice
      _ = 2 * c * E - M := hr.2
  have hc := sealJohnsonCauchy n k f
    (sealOrderedSwapLaplacianInt k f)
  change E ^ 2 <= N * M at hc
  exact sealJohnsonFactorClosure n k N E M H
    hN hH hcoeff hr.1 hstep hc

/-- Step 10c: induction on k gives the mean-zero Johnson gap. -/
theorem sealJohnsonMeanZeroGap :
    sealJohnsonMeanZeroGapStatement := by
  unfold sealJohnsonMeanZeroGapStatement
  intro n k
  induction k with
  | zero =>
      intro f hk _ _
      omega
  | succ k ih =>
      intro f hk hkn hzero
      by_cases hk0 : k = 0
      · subst k
        exact sealJohnsonBaseGap n f (by omega) hzero
      · apply sealJohnsonInductionStep n (k + 1) f
          (by omega) hkn hzero
        have hz := sealJohnsonDownMeanZero n (k + 1) f
          (by omega) (by omega) hzero
        exact ih (sealJohnsonDown f) (by omega) (by omega)
          (by simpa using hz)

end SealJohnsonSpectralRoute
end PPLLCompleteMultiLeaderCleanup

#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonCoefficientBound
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonFactorClosure
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonBaseGap
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonInductionStep
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonMeanZeroGap
