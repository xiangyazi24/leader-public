import Leader.Wu.Seal.JohnsonLaplacianUpDown

namespace PPLLCompleteMultiLeaderCleanup
namespace SealJohnsonSpectralRoute

open PPLL PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepRotationBridgeSol
open PPartialSealSweepTasepFiniteTimeSol
open SealJohnsonEnergyIdentity SealJohnsonPoincareA2a

set_option autoImplicit false
set_option Elab.async false

private theorem isumSub
    {m : Nat} (f g : Fin m -> Int) :
    (List.ofFn (fun i => f i - g i)).sum =
      (List.ofFn f).sum - (List.ofFn g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih]
      omega

private theorem isumMulLeft
    {m : Nat} (c : Int) (f : Fin m -> Int) :
    (List.ofFn (fun i => c * f i)).sum = c * (List.ofFn f).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih, Int.mul_add]

private theorem isumZero {m : Nat} :
    (List.ofFn (fun _ : Fin m => (0 : Int))).sum = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.ofFn_succ, ih]

private theorem isumIfFalseMulLeft
    {n : Nat} (F : Fin n -> Bool) (c : Int) (f : Fin n -> Int) :
    (List.ofFn (fun i => if F i then 0 else c * f i)).sum =
      c * (List.ofFn (fun i => if F i then 0 else f i)).sum := by
  calc
    (List.ofFn (fun i => if F i then 0 else c * f i)).sum =
        (List.ofFn (fun i => c * (if F i then 0 else f i))).sum := by
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext i
      cases h : F i <;> simp [h]
    _ = _ := isumMulLeft c _

private theorem isumIfFalseLinear
    {n : Nat} (F : Fin n -> Bool) (a b : Int)
    (f g : Fin n -> Int) :
    (List.ofFn (fun i =>
      if F i then 0 else a * f i - b * g i)).sum =
      a * (List.ofFn (fun i => if F i then 0 else f i)).sum -
        b * (List.ofFn (fun i => if F i then 0 else g i)).sum := by
  calc
    (List.ofFn (fun i =>
      if F i then 0 else a * f i - b * g i)).sum =
        (List.ofFn (fun i =>
          (if F i then 0 else a * f i) -
            (if F i then 0 else b * g i))).sum := by
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext i
      cases h : F i <;> simp [h]
    _ = (List.ofFn (fun i => if F i then 0 else a * f i)).sum -
        (List.ofFn (fun i => if F i then 0 else b * g i)).sum :=
      isumSub _ _
    _ = _ := by
      rw [isumIfFalseMulLeft, isumIfFalseMulLeft]

private theorem listMapSumCongr
    {alpha : Type} (xs : List alpha) (f g : alpha -> Int)
    (h : forall x, x ∈ xs -> f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [h a (by simp), ih]
      intro x hx
      exact h x (by simp [hx])

private theorem listMapMulRight
    {alpha : Type} (xs : List alpha) (f : alpha -> Int) (c : Int) :
    (xs.map (fun x => f x * c)).sum = (xs.map f).sum * c := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Int.add_mul]

private theorem isumIndicator
    {n : Nat} (F : Fin n -> Bool) :
    (List.ofFn (fun i => if F i then (1 : Int) else 0)).sum =
      (frontConfigMass F : Int) := by
  unfold frontConfigMass
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, Int.natCast_add]
      cases h : F 0 <;>
        simp [h, ih (fun i : Fin n => F i.succ)]

private theorem bitFalseOfMassZero
    {n : Nat} (F : Fin n -> Bool)
    (hm : frontConfigMass F = 0) (x : Fin n) : F x = false := by
  cases hx : F x with
  | false => rfl
  | true =>
      let g : Fin n -> Nat := fun i =>
        if i = x then 0 else if F i then 1 else 0
      have h := PPLLEpochVoterSumTools.sum_ofFn_balance_one
        (fun i : Fin n => if F i then 1 else 0) g x (by
          intro i hix
          simp [g, hix])
      unfold frontConfigMass at hm
      have hg : g x = 0 := by simp [g]
      have hfx : (if F x then 1 else 0) = 1 := by simp [hx]
      rw [hm, hg, hfx] at h
      omega

private theorem transposeAllFalse
    {n : Nat} (F : Fin n -> Bool)
    (hF : forall i, F i = false) (x z : Fin n) :
    sealTransposeFrontConfig F x z = F := by
  funext i
  simp [sealTransposeFrontConfig, hF]

private theorem laplacianZeroCensus
    {n : Nat} (g : SealIntObs n) (F : Fin n -> Bool)
    (hF : F ∈ tasepFrontConfigSlice n 0) :
    sealOrderedSwapLaplacianInt 0 g F =
      2 * (sealJohnsonC n 0 : Int) * g F -
        2 * sealJohnsonUp (sealJohnsonDown g) F := by
  have hm := (mem_tasepFrontConfigSlice_iff F).1 hF
  have hall : forall i, F i = false := fun i =>
    bitFalseOfMassZero F hm i
  have hlap : sealOrderedSwapLaplacianInt 0 g F = 0 := by
    unfold sealOrderedSwapLaplacianInt
    calc
      (List.ofFn (fun x : Fin n =>
        (List.ofFn (fun z : Fin n =>
          g F - g (sealTransposeFrontConfig F x z))).sum)).sum =
          (List.ofFn (fun _ : Fin n => (0 : Int))).sum := by
        apply congrArg List.sum
        apply congrArg List.ofFn
        funext x
        calc
          (List.ofFn (fun z : Fin n =>
            g F - g (sealTransposeFrontConfig F x z))).sum =
              (List.ofFn (fun _ : Fin n => (0 : Int))).sum := by
            apply congrArg List.sum
            apply congrArg List.ofFn
            funext z
            rw [transposeAllFalse F hall x z]
            omega
          _ = 0 := isumZero
      _ = 0 := isumZero
  have hup : sealJohnsonUp (sealJohnsonDown g) F = 0 := by
    unfold sealJohnsonUp
    calc
      (List.ofFn (fun x : Fin n =>
        if F x then
          sealJohnsonDown g (sealSetBit F x false) else 0)).sum =
          (List.ofFn (fun _ : Fin n => (0 : Int))).sum := by
        apply congrArg List.sum
        apply congrArg List.ofFn
        funext x
        simp [hall x]
      _ = 0 := isumZero
  rw [hlap, hup]
  simp [sealJohnsonC]

private theorem sealCExpandInt
    (n k : Nat) (hkn : k <= n) :
    (sealJohnsonC n k : Int) =
      (k : Int) * ((n : Int) + 1 - (k : Int)) := by
  unfold sealJohnsonC
  rw [Int.natCast_mul]
  have h : ((n + 1 - k : Nat) : Int) =
      (n : Int) + 1 - (k : Int) := by omega
  rw [h]

private theorem cStepArith (N K : Int) :
    K * (N + 1 - K) =
      (K - 1) * (N + 2 - K) + (N - 2 * K + 2) := by
  simp only [Int.mul_sub, Int.sub_mul, Int.mul_add, Int.add_mul,
    Int.mul_one, Int.one_mul]
  omega

private theorem sealCStep
    (n k : Nat) (hk : 0 < k) (hkn : k <= n) :
    (sealJohnsonC n k : Int) =
      (sealJohnsonC n (k - 1) : Int) +
        ((n : Int) - 2 * (k : Int) + 2) := by
  have hp : k - 1 <= n := by omega
  rw [sealCExpandInt n k hkn, sealCExpandInt n (k - 1) hp]
  have hkcast : ((k - 1 : Nat) : Int) = (k : Int) - 1 := by omega
  rw [hkcast]
  have hs : (n : Int) + 1 - ((k : Int) - 1) =
      (n : Int) + 2 - (k : Int) := by omega
  rw [hs]
  exact cStepArith (n : Int) (k : Int)

private theorem intertwineArith
    (ck cp d u v : Int) (hc : ck = cp + d) :
    2 * ck * v - 2 * (u + d * v) =
      2 * cp * v - 2 * u := by
  rw [hc]
  simp only [Int.mul_add, Int.add_mul, Int.mul_assoc]
  omega

private theorem downLaplacianCensus
    {n k : Nat} (f : SealIntObs n) (F : Fin n -> Bool)
    (hk : 0 < k) (hkn : k <= n)
    (hF : F ∈ tasepFrontConfigSlice n (k - 1)) :
    sealJohnsonDown (sealOrderedSwapLaplacianInt k f) F =
      2 * (sealJohnsonC n k : Int) * sealJohnsonDown f F -
        2 * sealJohnsonDown (sealJohnsonUp (sealJohnsonDown f)) F := by
  change
    (List.ofFn (fun x : Fin n =>
      if F x then 0 else
        sealOrderedSwapLaplacianInt k f
          (sealSetBit F x true))).sum =
      2 * (sealJohnsonC n k : Int) *
        (List.ofFn (fun x : Fin n =>
          if F x then 0 else f (sealSetBit F x true))).sum -
      2 * (List.ofFn (fun x : Fin n =>
        if F x then 0 else
          sealJohnsonUp (sealJohnsonDown f)
            (sealSetBit F x true))).sum
  calc
    (List.ofFn (fun x : Fin n =>
      if F x then 0 else
        sealOrderedSwapLaplacianInt k f
          (sealSetBit F x true))).sum =
      (List.ofFn (fun x : Fin n =>
        if F x then 0 else
          2 * (sealJohnsonC n k : Int) * f (sealSetBit F x true) -
            2 * sealJohnsonUp (sealJohnsonDown f)
              (sealSetBit F x true))).sum := by
        apply congrArg List.sum
        apply congrArg List.ofFn
        funext x
        cases hx : F x with
        | false =>
            have hs := (sealJohnsonSetBitSlice n k F x hk hkn).1 hF hx
            simpa [hx] using
              (sealJohnsonLaplacianUpDown n k f
                (sealSetBit F x true) hk hkn hs)
        | true => simp [hx]
    _ = _ := isumIfFalseLinear F
      (2 * (sealJohnsonC n k : Int)) 2
      (fun x => f (sealSetBit F x true))
      (fun x => sealJohnsonUp (sealJohnsonDown f)
        (sealSetBit F x true))

/-- Step 5: D_k T_k = T_(k-1) D_k, including the k=1 / level-zero edge. -/
theorem sealJohnsonDownIntertwining :
    sealJohnsonDownIntertwiningStatement := by
  unfold sealJohnsonDownIntertwiningStatement
  intro n k f F hk hkn hF
  have hcomm := sealJohnsonCommutator n k
    (sealJohnsonDown f) F hk hkn hF
  have hc := sealCStep n k hk hkn
  have hmid :
      sealJohnsonDown (sealOrderedSwapLaplacianInt k f) F =
        2 * (sealJohnsonC n (k - 1) : Int) * sealJohnsonDown f F -
          2 * sealJohnsonUp (sealJohnsonDown (sealJohnsonDown f)) F := by
    calc
      sealJohnsonDown (sealOrderedSwapLaplacianInt k f) F =
          2 * (sealJohnsonC n k : Int) * sealJohnsonDown f F -
            2 * sealJohnsonDown
              (sealJohnsonUp (sealJohnsonDown f)) F :=
        downLaplacianCensus f F hk hkn hF
      _ = 2 * (sealJohnsonC n k : Int) * sealJohnsonDown f F -
          2 * (sealJohnsonUp (sealJohnsonDown (sealJohnsonDown f)) F +
            ((n : Int) - 2 * (k : Int) + 2) * sealJohnsonDown f F) := by
        rw [hcomm]
      _ = _ := intertwineArith
        (sealJohnsonC n k : Int)
        (sealJohnsonC n (k - 1) : Int)
        ((n : Int) - 2 * (k : Int) + 2)
        (sealJohnsonUp (sealJohnsonDown (sealJohnsonDown f)) F)
        (sealJohnsonDown f F) hc
  by_cases hk1 : k = 1
  · subst k
    have hz := laplacianZeroCensus (sealJohnsonDown f) F (by
      simpa using hF)
    exact hmid.trans hz.symm
  · have hkpred : 0 < k - 1 := by omega
    have hlower := sealJohnsonLaplacianUpDown n (k - 1)
      (sealJohnsonDown f) F hkpred (by omega) hF
    exact hmid.trans hlower.symm

private theorem upOneOnSlice
    {n k : Nat} (F : Fin n -> Bool)
    (hF : F ∈ tasepFrontConfigSlice n k) :
    sealJohnsonUp (fun _ : (Fin n -> Bool) => (1 : Int)) F = (k : Int) := by
  have hm := (mem_tasepFrontConfigSlice_iff F).1 hF
  unfold sealJohnsonUp
  simpa [hm] using (isumIndicator F)

/-- Step 6: D preserves mean zero. -/
theorem sealJohnsonDownMeanZero :
    sealJohnsonDownMeanZeroStatement := by
  unfold sealJohnsonDownMeanZeroStatement
  intro n k f hk hkn hzero
  let one : SealIntObs n := fun _ => 1
  have hadj := sealJohnsonUpDownAdjoint n k f one hk hkn
  have hleft :
      sealSliceIntDot k f (sealJohnsonUp one) =
        (k : Int) * sealSliceIntSum k f := by
    unfold sealSliceIntDot sealSliceIntSum
    calc
      ((tasepFrontConfigSlice n k).map
        (fun F => f F * sealJohnsonUp one F)).sum =
          ((tasepFrontConfigSlice n k).map
            (fun F => f F * (k : Int))).sum := by
        apply listMapSumCongr
        intro F hF
        rw [show sealJohnsonUp one F = (k : Int) by
          exact upOneOnSlice F hF]
      _ = ((tasepFrontConfigSlice n k).map f).sum * (k : Int) :=
        listMapMulRight _ f _
      _ = (k : Int) * ((tasepFrontConfigSlice n k).map f).sum :=
        Int.mul_comm _ _
  have hright :
      sealSliceIntDot (k - 1) (sealJohnsonDown f) one =
        sealSliceIntSum (k - 1) (sealJohnsonDown f) := by
    unfold sealSliceIntDot sealSliceIntSum
    apply listMapSumCongr
    intro F _
    exact Int.mul_one _
  have heq := hleft.symm.trans (hadj.trans hright)
  rw [hzero, Int.mul_zero] at heq
  exact heq.symm

end SealJohnsonSpectralRoute
end PPLLCompleteMultiLeaderCleanup

#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonDownIntertwining
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonDownMeanZero
