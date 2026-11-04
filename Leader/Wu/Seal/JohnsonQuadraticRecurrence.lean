import Leader.Wu.Seal.JohnsonDownIntertwining

namespace PPLLCompleteMultiLeaderCleanup
namespace SealJohnsonSpectralRoute

open PPLL PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepRotationBridgeSol
open PPartialSealSweepTasepFiniteTimeSol
open SealJohnsonEnergyIdentity SealJohnsonPoincareA2a

set_option autoImplicit false
set_option Elab.async false

private theorem listMapSumCongr
    {alpha : Type} (xs : List alpha) (f g : alpha -> Int)
    (h : forall x, x ∈ xs -> f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [h x (by simp), ih]
      intro y hy
      exact h y (by simp [hy])

private theorem listMapAdd
    {alpha : Type} (xs : List alpha) (f g : alpha -> Int) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

private theorem listMapSub
    {alpha : Type} (xs : List alpha) (f g : alpha -> Int) :
    (xs.map (fun x => f x - g x)).sum =
      (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

private theorem listMapMulLeft
    {alpha : Type} (xs : List alpha) (c : Int) (f : alpha -> Int) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Int.mul_add]

private theorem dotCensusTerm (a c v w : Int) :
    a * (2 * c * v - 2 * w) =
      2 * c * (a * v) - 2 * (a * w) := by
  have h1 : a * (2 * c * v) = 2 * c * (a * v) := by
    calc
      a * (2 * c * v) = (a * (2 * c)) * v := by
        rw [← Int.mul_assoc]
      _ = ((2 * c) * a) * v := by rw [Int.mul_comm a (2 * c)]
      _ = 2 * c * (a * v) := by rw [Int.mul_assoc]
  have h2 : a * (2 * w) = 2 * (a * w) := by
    calc
      a * (2 * w) = (a * 2) * w := by rw [← Int.mul_assoc]
      _ = (2 * a) * w := by rw [Int.mul_comm a 2]
      _ = 2 * (a * w) := by rw [Int.mul_assoc]
  rw [Int.mul_sub, h1, h2]

private theorem dotLaplacianCensus
    {n : Nat} (k : Nat) (a f : SealIntObs n)
    (hk : 0 < k) (hkn : k <= n) :
    sealSliceIntDot k a (sealOrderedSwapLaplacianInt k f) =
      2 * (sealJohnsonC n k : Int) * sealSliceIntDot k a f -
        2 * sealSliceIntDot k a (sealJohnsonUp (sealJohnsonDown f)) := by
  unfold sealSliceIntDot
  calc
    ((tasepFrontConfigSlice n k).map
      (fun F => a F * sealOrderedSwapLaplacianInt k f F)).sum =
        ((tasepFrontConfigSlice n k).map (fun F =>
          2 * (sealJohnsonC n k : Int) * (a F * f F) -
            2 * (a F * sealJohnsonUp (sealJohnsonDown f) F))).sum := by
      apply listMapSumCongr
      intro F hF
      rw [sealJohnsonLaplacianUpDown n k f F hk hkn hF]
      exact dotCensusTerm (a F) (sealJohnsonC n k : Int)
        (f F) (sealJohnsonUp (sealJohnsonDown f) F)
    _ = ((tasepFrontConfigSlice n k).map
          (fun F => 2 * (sealJohnsonC n k : Int) * (a F * f F))).sum -
        ((tasepFrontConfigSlice n k).map
          (fun F => 2 * (a F * sealJohnsonUp (sealJohnsonDown f) F))).sum :=
      listMapSub _ _ _
    _ = 2 * (sealJohnsonC n k : Int) *
          ((tasepFrontConfigSlice n k).map (fun F => a F * f F)).sum -
        2 * ((tasepFrontConfigSlice n k).map
          (fun F => a F * sealJohnsonUp (sealJohnsonDown f) F)).sum := by
      rw [listMapMulLeft, listMapMulLeft]

private theorem sealSliceIntDot_comm
    {n : Nat} (k : Nat) (f g : SealIntObs n) :
    sealSliceIntDot k f g = sealSliceIntDot k g f := by
  unfold sealSliceIntDot
  apply listMapSumCongr
  intro F _
  exact Int.mul_comm _ _

/-- Step 7: the two quadratic recurrences. -/
theorem sealJohnsonQuadraticRecurrence :
    sealJohnsonQuadraticRecurrenceStatement := by
  unfold sealJohnsonQuadraticRecurrenceStatement
  intro n k f hk hkn
  dsimp only
  have h1 := dotLaplacianCensus (n := n) k f f hk hkn
  have ha1 := sealJohnsonUpDownAdjoint n k f (sealJohnsonDown f) hk hkn
  rw [ha1] at h1
  have hfirst :
      sealJohnsonDirichletInt k f =
        2 * (sealJohnsonC n k : Int) * sealJohnsonNormInt k f -
          2 * sealJohnsonNormInt (k - 1) (sealJohnsonDown f) := by
    simpa [sealJohnsonDirichletInt, sealJohnsonNormInt] using h1

  have hinter :
      sealSliceIntDot (k - 1)
          (sealJohnsonDown (sealOrderedSwapLaplacianInt k f))
          (sealJohnsonDown f) =
        sealSliceIntDot (k - 1)
          (sealOrderedSwapLaplacianInt (k - 1) (sealJohnsonDown f))
          (sealJohnsonDown f) := by
    unfold sealSliceIntDot
    apply listMapSumCongr
    intro F hF
    rw [sealJohnsonDownIntertwining n k f F hk hkn hF]
  have hcross :
      sealSliceIntDot k (sealOrderedSwapLaplacianInt k f)
          (sealJohnsonUp (sealJohnsonDown f)) =
        sealSliceIntDot (k - 1) (sealJohnsonDown f)
          (sealOrderedSwapLaplacianInt (k - 1) (sealJohnsonDown f)) := by
    calc
      _ = sealSliceIntDot (k - 1)
          (sealJohnsonDown (sealOrderedSwapLaplacianInt k f))
          (sealJohnsonDown f) :=
        sealJohnsonUpDownAdjoint n k
          (sealOrderedSwapLaplacianInt k f) (sealJohnsonDown f) hk hkn
      _ = sealSliceIntDot (k - 1)
          (sealOrderedSwapLaplacianInt (k - 1) (sealJohnsonDown f))
          (sealJohnsonDown f) := hinter
      _ = _ := sealSliceIntDot_comm _ _ _
  have h2 := dotLaplacianCensus (n := n) k
    (sealOrderedSwapLaplacianInt k f) f hk hkn
  rw [sealSliceIntDot_comm k (sealOrderedSwapLaplacianInt k f) f,
    hcross] at h2
  have h2' :
      sealJohnsonLaplacianNormInt k f =
        2 * (sealJohnsonC n k : Int) * sealJohnsonDirichletInt k f -
          2 * sealJohnsonDirichletInt (k - 1) (sealJohnsonDown f) := by
    simpa [sealJohnsonLaplacianNormInt, sealJohnsonDirichletInt] using h2
  constructor
  · exact hfirst
  · omega

private theorem intMulSelfNonneg (a : Int) : 0 <= a * a := by
  by_cases ha : 0 <= a
  · exact Int.mul_nonneg ha ha
  · have ha' : a <= 0 := Int.le_of_not_le ha
    exact Int.mul_nonneg_of_nonpos_of_nonpos ha' ha'

private theorem listMapSumNonneg
    {alpha : Type} (xs : List alpha) (f : alpha -> Int)
    (h : forall x, 0 <= f x) : 0 <= (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Int.add_nonneg (h x) ih

private theorem intPowTwo (x : Int) : x ^ 2 = x * x := by
  rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]

private theorem mul4Swap (a b c d : Int) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  calc
    (a * b) * (c * d) = a * (b * (c * d)) := Int.mul_assoc _ _ _
    _ = a * ((b * c) * d) := by rw [Int.mul_assoc b c d]
    _ = a * ((c * b) * d) := by rw [Int.mul_comm b c]
    _ = a * (c * (b * d)) := by rw [Int.mul_assoc]
    _ = (a * c) * (b * d) := by rw [← Int.mul_assoc]

private theorem lagrangeTerm (a b c d : Int) :
    (a * d - c * b) ^ 2 =
      (a * a) * (d * d) + (b * b) * (c * c) -
        2 * (a * b) * (c * d) := by
  have h1 := mul4Swap a d a d
  have h2 : (c * b) * (c * b) = (b * b) * (c * c) := by
    calc
      _ = (c * c) * (b * b) := mul4Swap c b c b
      _ = _ := Int.mul_comm _ _
  have h3 : (a * d) * (c * b) = (a * b) * (c * d) := by
    calc
      _ = (a * c) * (d * b) := mul4Swap a d c b
      _ = (a * c) * (b * d) := by rw [Int.mul_comm d b]
      _ = (a * b) * (c * d) := mul4Swap a c b d
  have h4 : (c * b) * (a * d) = (a * b) * (c * d) := by
    calc
      _ = (a * d) * (c * b) := Int.mul_comm _ _
      _ = _ := h3
  have hs : 2 * (a * b) * (c * d) = 2 * ((a * b) * (c * d)) :=
    Int.mul_assoc _ _ _
  simp only [intPowTwo, Int.sub_mul, Int.mul_sub]
  rw [h1, h2, h3, h4, hs]
  omega

private theorem lagrangeRowNonneg
    {alpha : Type} (xs : List alpha) (a b : alpha -> Int) (x : alpha) :
    0 <= (a x * a x) * (xs.map (fun y => b y * b y)).sum +
      (b x * b x) * (xs.map (fun y => a y * a y)).sum -
      2 * (a x * b x) * (xs.map (fun y => a y * b y)).sum := by
  have hs :
      0 <= (xs.map (fun y => (a x * b y - a y * b x) ^ 2)).sum := by
    apply listMapSumNonneg
    intro y
    simpa only [intPowTwo] using intMulSelfNonneg (a x * b y - a y * b x)
  have heq :
      (xs.map (fun y => (a x * b y - a y * b x) ^ 2)).sum =
        (a x * a x) * (xs.map (fun y => b y * b y)).sum +
        (b x * b x) * (xs.map (fun y => a y * a y)).sum -
        2 * (a x * b x) * (xs.map (fun y => a y * b y)).sum := by
    calc
      _ = (xs.map (fun y =>
          (a x * a x) * (b y * b y) +
          (b x * b x) * (a y * a y) -
          2 * (a x * b x) * (a y * b y))).sum := by
        apply listMapSumCongr
        intro y _
        exact lagrangeTerm (a x) (b x) (a y) (b y)
      _ = (xs.map (fun y =>
            (a x * a x) * (b y * b y) +
            (b x * b x) * (a y * a y))).sum -
          (xs.map (fun y =>
            2 * (a x * b x) * (a y * b y))).sum := listMapSub _ _ _
      _ = ((xs.map (fun y => (a x * a x) * (b y * b y))).sum +
            (xs.map (fun y => (b x * b x) * (a y * a y))).sum) -
          (xs.map (fun y => 2 * (a x * b x) * (a y * b y))).sum := by
        rw [listMapAdd]
      _ = _ := by
        rw [listMapMulLeft, listMapMulLeft, listMapMulLeft]
  rw [heq] at hs
  exact hs

private theorem cauchyStepArith (a b A B D : Int)
    (h0 : D * D <= A * B)
    (h1 : 0 <= (a * a) * B + (b * b) * A - 2 * (a * b) * D) :
    (a * b + D) * (a * b + D) <=
      (a * a + A) * (b * b + B) := by
  have hab := mul4Swap a b a b
  have hcross : D * (a * b) = (a * b) * D := Int.mul_comm _ _
  have hAb : A * (b * b) = (b * b) * A := Int.mul_comm _ _
  have hscale : 2 * (a * b) * D = 2 * ((a * b) * D) :=
    Int.mul_assoc _ _ _
  rw [hscale] at h1
  simp only [Int.add_mul, Int.mul_add]
  rw [hab, hcross, hAb]
  omega

private theorem listCauchyMul
    {alpha : Type} (xs : List alpha) (a b : alpha -> Int) :
    (xs.map (fun x => a x * b x)).sum *
        (xs.map (fun x => a x * b x)).sum <=
      (xs.map (fun x => a x * a x)).sum *
        (xs.map (fun x => b x * b x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hr := lagrangeRowNonneg xs a b x
      simp only [List.map_cons, List.sum_cons]
      exact cauchyStepArith (a x) (b x)
        (xs.map (fun y => a y * a y)).sum
        (xs.map (fun y => b y * b y)).sum
        (xs.map (fun y => a y * b y)).sum ih hr

/-- Step 8: finite integer Cauchy from the Lagrange sum-of-squares identity. -/
theorem sealJohnsonCauchy :
    sealJohnsonCauchyStatement := by
  unfold sealJohnsonCauchyStatement
  intro n k f g
  have h := listCauchyMul (tasepFrontConfigSlice n k) f g
  simpa only [sealSliceIntDot, sealJohnsonNormInt, intPowTwo] using h

end SealJohnsonSpectralRoute
end PPLLCompleteMultiLeaderCleanup

#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonQuadraticRecurrence
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonCauchy
