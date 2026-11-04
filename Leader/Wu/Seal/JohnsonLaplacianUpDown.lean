import Leader.Wu.Seal.JohnsonCommutator


namespace PPLLCompleteMultiLeaderCleanup
namespace SealJohnsonSpectralRoute


open PPLL PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepRotationBridgeSol
open PPartialSealSweepTasepFiniteTimeSol
open SealJohnsonEnergyIdentity SealJohnsonPoincareA2a


set_option autoImplicit false
set_option Elab.async false


private theorem isumAdd
    {m : Nat} (f g : Fin m -> Int) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih]
      omega


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


private theorem isumMulRight
    {m : Nat} (f : Fin m -> Int) (c : Int) :
    (List.ofFn (fun i => f i * c)).sum =
      (List.ofFn f).sum * c := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih, Int.add_mul]


private theorem isumConst
    {m : Nat} (c : Int) :
    (List.ofFn (fun _ : Fin m => c)).sum = (m : Int) * c := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, ih,
        Int.natCast_succ, Int.add_mul, Int.one_mul]
      exact Int.add_comm _ _


private theorem isumZero {m : Nat} :
    (List.ofFn (fun _ : Fin m => (0 : Int))).sum = 0 := by
  simpa using (isumConst (m := m) (0 : Int))


private theorem isumComm
    {m q : Nat} (f : Fin m -> Fin q -> Int) :
    (List.ofFn (fun i =>
      (List.ofFn (fun j => f i j)).sum)).sum =
      (List.ofFn (fun j =>
        (List.ofFn (fun i => f i j)).sum)).sum := by
  induction m with
  | zero => simp [isumZero]
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, ih]
      rw [← isumAdd]
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext j
      rw [List.ofFn_succ, List.sum_cons]


private theorem isumBalanceOne
    {m : Nat} (f g : Fin m -> Int) (j : Fin m)
    (hother : forall i, i ≠ j -> f i = g i) :
    (List.ofFn f).sum + g j = (List.ofFn g).sum + f j := by
  induction m with
  | zero => exact Fin.elim0 j
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hj0 : j = 0
      · subst j
        have htail :
            (List.ofFn (fun i : Fin m => f i.succ)).sum =
              (List.ofFn (fun i : Fin m => g i.succ)).sum := by
          apply congrArg List.sum
          apply congrArg List.ofFn
          funext i
          apply hother i.succ
          intro hbad
          have hv := congrArg Fin.val hbad
          simp at hv
        rw [htail]
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := by
            intro h
            apply hj0
            apply Fin.ext
            simpa using h
          omega
        let j' : Fin m := ⟨j.val - 1, by omega⟩
        have hjsucc : j'.succ = j := by
          apply Fin.ext
          change j.val - 1 + 1 = j.val
          omega
        have hhead : f 0 = g 0 := hother 0 (Ne.symm hj0)
        have htail := ih
          (fun i : Fin m => f i.succ)
          (fun i : Fin m => g i.succ) j'
          (by
            intro i hij
            apply hother i.succ
            intro hbad
            apply hij
            apply Fin.ext
            have hv := congrArg Fin.val hbad
            change i.val + 1 = j.val at hv
            change i.val = j.val - 1
            omega)
        rw [hjsucc] at htail
        omega


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


private theorem isumIfTrueConst
    {n : Nat} (F : Fin n -> Bool) (a : Int) :
    (List.ofFn (fun i => if F i then a else 0)).sum =
      (frontConfigMass F : Int) * a := by
  rw [← isumIndicator F]
  rw [← isumMulRight
    (fun i : Fin n => if F i then (1 : Int) else 0) a]
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext i
  cases h : F i <;> simp [h]


private theorem isumIfFalseConst
    {n : Nat} (F : Fin n -> Bool) (a : Int) :
    (List.ofFn (fun i => if F i then 0 else a)).sum =
      ((n : Int) - (frontConfigMass F : Int)) * a := by
  calc
    (List.ofFn (fun i => if F i then 0 else a)).sum =
      (List.ofFn (fun i =>
        a - (if F i then a else 0))).sum := by
        apply congrArg List.sum
        apply congrArg List.ofFn
        funext i
        cases h : F i <;> simp [h]
    _ = (List.ofFn (fun _ : Fin n => a)).sum -
        (List.ofFn (fun i => if F i then a else 0)).sum :=
      isumSub _ _
    _ = (n : Int) * a - (frontConfigMass F : Int) * a := by
      rw [isumConst, isumIfTrueConst]
    _ = ((n : Int) - (frontConfigMass F : Int)) * a := by
      rw [Int.sub_mul]


private theorem setBit_false_true_restore
    {n : Nat} (F : Fin n -> Bool) (x : Fin n)
    (hx : F x = true) :
    sealSetBit (sealSetBit F x false) x true = F := by
  funext i
  by_cases hix : i = x
  · subst i
    simp [sealSetBit, hx]
  · simp [sealSetBit, hix]


private def replacementSum
    {n : Nat} (f : SealIntObs n) (F : Fin n -> Bool) : Int :=
  (List.ofFn (fun z : Fin n =>
    (List.ofFn (fun x : Fin n =>
      if F z then
        if F x then 0 else
          f (sealSetBit (sealSetBit F z false) x true)
      else 0)).sum)).sum


private theorem upDownRow
    {n : Nat} (f : SealIntObs n) (F : Fin n -> Bool)
    (z : Fin n) (hz : F z = true) :
    sealJohnsonDown f (sealSetBit F z false) =
      f F +
        (List.ofFn (fun x : Fin n =>
          if F x then 0 else
            f (sealSetBit (sealSetBit F z false) x true))).sum := by
  unfold sealJohnsonDown
  have h := isumBalanceOne
    (fun x : Fin n =>
      if sealSetBit F z false x then 0 else
        f (sealSetBit (sealSetBit F z false) x true))
    (fun x : Fin n =>
      if F x then 0 else
        f (sealSetBit (sealSetBit F z false) x true)) z (by
        intro x hxz
        simp [sealSetBit, hxz])
  have hr := setBit_false_true_restore F z hz
  simpa [sealSetBit, hz, hr, Int.add_comm] using h


private theorem upDown_expand
    {n : Nat} (f : SealIntObs n) (F : Fin n -> Bool) :
    sealJohnsonUp (sealJohnsonDown f) F =
      (frontConfigMass F : Int) * f F + replacementSum f F := by
  unfold sealJohnsonUp
  calc
    (List.ofFn (fun z : Fin n =>
      if F z then sealJohnsonDown f (sealSetBit F z false) else 0)).sum =
      (List.ofFn (fun z : Fin n =>
        (if F z then f F else 0) +
          (List.ofFn (fun x : Fin n =>
            if F z then
              if F x then 0 else
                f (sealSetBit (sealSetBit F z false) x true)
            else 0)).sum)).sum := by
        apply congrArg List.sum
        apply congrArg List.ofFn
        funext z
        cases hz : F z with
        | false => simp [hz, isumZero]
        | true => simpa [hz] using upDownRow f F z hz
    _ = (List.ofFn (fun z : Fin n =>
          if F z then f F else 0)).sum + replacementSum f F :=
      isumAdd _ _
    _ = (frontConfigMass F : Int) * f F + replacementSum f F := by
      rw [isumIfTrueConst]


private theorem transpose_same
    {n : Nat} (F : Fin n -> Bool) (x z : Fin n)
    (h : F x = F z) :
    sealTransposeFrontConfig F x z = F := by
  funext i
  by_cases hix : i = x
  · subst i
    simp [sealTransposeFrontConfig, h]
  · by_cases hiz : i = z
    · subst i
      simp [sealTransposeFrontConfig, hix, h]
    · simp [sealTransposeFrontConfig, hix, hiz]


private theorem transpose_false_true
    {n : Nat} (F : Fin n -> Bool) (x z : Fin n)
    (hx : F x = false) (hz : F z = true) :
    sealTransposeFrontConfig F x z =
      sealSetBit (sealSetBit F z false) x true := by
  have hxz : x ≠ z := by
    intro h
    subst z
    rw [hx] at hz
    cases hz
  funext i
  by_cases hix : i = x
  · subst i
    simp [sealTransposeFrontConfig, sealSetBit,
      hxz, Ne.symm hxz, hx, hz]
  · by_cases hiz : i = z
    · subst i
      simp [sealTransposeFrontConfig, sealSetBit,
        hxz, Ne.symm hxz, hix, hx, hz]
    · simp [sealTransposeFrontConfig, sealSetBit,
        hix, hiz, hx, hz]


private theorem transpose_true_false
    {n : Nat} (F : Fin n -> Bool) (x z : Fin n)
    (hx : F x = true) (hz : F z = false) :
    sealTransposeFrontConfig F x z =
      sealSetBit (sealSetBit F x false) z true := by
  have hxz : x ≠ z := by
    intro h
    subst z
    rw [hx] at hz
    cases hz
  funext i
  by_cases hix : i = x
  · subst i
    simp [sealTransposeFrontConfig, sealSetBit,
      hxz, Ne.symm hxz, hx, hz]
  · by_cases hiz : i = z
    · subst i
      simp [sealTransposeFrontConfig, sealSetBit,
        hxz, Ne.symm hxz, hix, hx, hz]
    · simp [sealTransposeFrontConfig, sealSetBit,
        hix, hiz, hx, hz]


private def swapForwardTerm
    {n : Nat} (f : SealIntObs n) (F : Fin n -> Bool)
    (x z : Fin n) : Int :=
  if F x then 0 else if F z then
    f F - f (sealSetBit (sealSetBit F z false) x true)
  else 0


private def swapReverseTerm
    {n : Nat} (f : SealIntObs n) (F : Fin n -> Bool)
    (x z : Fin n) : Int :=
  if F x then
    if F z then 0 else
      f F - f (sealSetBit (sealSetBit F x false) z true)
  else 0


private def swapForwardSum
    {n : Nat} (f : SealIntObs n) (F : Fin n -> Bool) : Int :=
  (List.ofFn (fun x : Fin n =>
    (List.ofFn (fun z : Fin n => swapForwardTerm f F x z)).sum)).sum


private def swapReverseSum
    {n : Nat} (f : SealIntObs n) (F : Fin n -> Bool) : Int :=
  (List.ofFn (fun x : Fin n =>
    (List.ofFn (fun z : Fin n => swapReverseTerm f F x z)).sum)).sum


private theorem swapTermSplit
    {n : Nat} (f : SealIntObs n) (F : Fin n -> Bool)
    (x z : Fin n) :
    f F - f (sealTransposeFrontConfig F x z) =
      swapForwardTerm f F x z + swapReverseTerm f F x z := by
  cases hx : F x with
  | false =>
      cases hz : F z with
      | false =>
          rw [transpose_same F x z (by rw [hx, hz])]
          simp [swapForwardTerm, swapReverseTerm, hx, hz]
      | true =>
          rw [transpose_false_true F x z hx hz]
          simp [swapForwardTerm, swapReverseTerm, hx, hz]
  | true =>
      cases hz : F z with
      | false =>
          rw [transpose_true_false F x z hx hz]
          simp [swapForwardTerm, swapReverseTerm, hx, hz]
      | true =>
          rw [transpose_same F x z (by rw [hx, hz])]
          simp [swapForwardTerm, swapReverseTerm, hx, hz]


private theorem swapSplit
    {n : Nat} (k : Nat) (f : SealIntObs n) (F : Fin n -> Bool) :
    sealOrderedSwapLaplacianInt k f F =
      swapForwardSum f F + swapReverseSum f F := by
  unfold sealOrderedSwapLaplacianInt swapForwardSum swapReverseSum
  calc
    (List.ofFn (fun x : Fin n =>
      (List.ofFn (fun z : Fin n =>
        f F - f (sealTransposeFrontConfig F x z))).sum)).sum =
      (List.ofFn (fun x : Fin n =>
        (List.ofFn (fun z : Fin n =>
          swapForwardTerm f F x z +
            swapReverseTerm f F x z)).sum)).sum := by
        apply congrArg List.sum
        apply congrArg List.ofFn
        funext x
        apply congrArg List.sum
        apply congrArg List.ofFn
        funext z
        exact swapTermSplit f F x z
    _ = (List.ofFn (fun x : Fin n =>
          (List.ofFn (fun z : Fin n => swapForwardTerm f F x z)).sum +
          (List.ofFn (fun z : Fin n => swapReverseTerm f F x z)).sum)).sum := by
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext x
      exact isumAdd _ _
    _ =
      (List.ofFn (fun x : Fin n =>
        (List.ofFn (fun z : Fin n => swapForwardTerm f F x z)).sum)).sum +
      (List.ofFn (fun x : Fin n =>
        (List.ofFn (fun z : Fin n => swapReverseTerm f F x z)).sum)).sum :=
      isumAdd _ _


private theorem swapReverse_eq_forward
    {n : Nat} (f : SealIntObs n) (F : Fin n -> Bool) :
    swapReverseSum f F = swapForwardSum f F := by
  unfold swapReverseSum swapForwardSum
  calc
    (List.ofFn (fun x : Fin n =>
      (List.ofFn (fun z : Fin n => swapReverseTerm f F x z)).sum)).sum =
      (List.ofFn (fun z : Fin n =>
        (List.ofFn (fun x : Fin n => swapReverseTerm f F x z)).sum)).sum :=
      isumComm _
    _ = (List.ofFn (fun z : Fin n =>
        (List.ofFn (fun x : Fin n => swapForwardTerm f F z x)).sum)).sum := by
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext z
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext x
      unfold swapReverseTerm swapForwardTerm
      cases hx : F x <;> cases hz : F z <;> simp [hx, hz]
    _ = _ := rfl


private theorem swap_two_forward
    {n : Nat} (k : Nat) (f : SealIntObs n) (F : Fin n -> Bool) :
    sealOrderedSwapLaplacianInt k f F = 2 * swapForwardSum f F := by
  rw [swapSplit k f F, swapReverse_eq_forward]
  omega


private def swapConstantSum
    {n : Nat} (f : SealIntObs n) (F : Fin n -> Bool) : Int :=
  (List.ofFn (fun x : Fin n =>
    (List.ofFn (fun z : Fin n =>
      if F x then 0 else if F z then f F else 0)).sum)).sum


private def swapReplacementXSum
    {n : Nat} (f : SealIntObs n) (F : Fin n -> Bool) : Int :=
  (List.ofFn (fun x : Fin n =>
    (List.ofFn (fun z : Fin n =>
      if F x then 0 else if F z then
        f (sealSetBit (sealSetBit F z false) x true)
      else 0)).sum)).sum


private theorem swapConstant_expand
    {n : Nat} (f : SealIntObs n) (F : Fin n -> Bool) :
    swapConstantSum f F =
      (frontConfigMass F : Int) *
        ((n : Int) - (frontConfigMass F : Int)) * f F := by
  unfold swapConstantSum
  calc
    (List.ofFn (fun x : Fin n =>
      (List.ofFn (fun z : Fin n =>
        if F x then 0 else if F z then f F else 0)).sum)).sum =
      (List.ofFn (fun x : Fin n =>
        if F x then 0 else (frontConfigMass F : Int) * f F)).sum := by
        apply congrArg List.sum
        apply congrArg List.ofFn
        funext x
        cases hx : F x with
        | false => simpa [hx] using isumIfTrueConst F (f F)
        | true => simp [hx, isumZero]
    _ = ((n : Int) - (frontConfigMass F : Int)) *
          ((frontConfigMass F : Int) * f F) :=
      isumIfFalseConst F ((frontConfigMass F : Int) * f F)
    _ = (frontConfigMass F : Int) *
          ((n : Int) - (frontConfigMass F : Int)) * f F := by
      rw [← Int.mul_assoc]
      rw [Int.mul_comm
        ((n : Int) - (frontConfigMass F : Int))
        (frontConfigMass F : Int)]


private theorem swapReplacementX_eq
    {n : Nat} (f : SealIntObs n) (F : Fin n -> Bool) :
    swapReplacementXSum f F = replacementSum f F := by
  unfold swapReplacementXSum replacementSum
  calc
    (List.ofFn (fun x : Fin n =>
      (List.ofFn (fun z : Fin n =>
        if F x then 0 else if F z then
          f (sealSetBit (sealSetBit F z false) x true)
        else 0)).sum)).sum =
      (List.ofFn (fun z : Fin n =>
        (List.ofFn (fun x : Fin n =>
          if F x then 0 else if F z then
            f (sealSetBit (sealSetBit F z false) x true)
          else 0)).sum)).sum := isumComm _
    _ = _ := by
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext z
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext x
      cases hx : F x <;> cases hz : F z <;> simp [hx, hz]


private theorem forward_expand
    {n : Nat} (f : SealIntObs n) (F : Fin n -> Bool) :
    swapForwardSum f F =
      (frontConfigMass F : Int) *
          ((n : Int) - (frontConfigMass F : Int)) * f F -
        replacementSum f F := by
  unfold swapForwardSum
  calc
    (List.ofFn (fun x : Fin n =>
      (List.ofFn (fun z : Fin n => swapForwardTerm f F x z)).sum)).sum =
      (List.ofFn (fun x : Fin n =>
        (List.ofFn (fun z : Fin n =>
          (if F x then 0 else if F z then f F else 0) -
          (if F x then 0 else if F z then
            f (sealSetBit (sealSetBit F z false) x true)
          else 0))).sum)).sum := by
        apply congrArg List.sum
        apply congrArg List.ofFn
        funext x
        apply congrArg List.sum
        apply congrArg List.ofFn
        funext z
        cases hx : F x <;> cases hz : F z <;>
          simp [swapForwardTerm, hx, hz]
    _ = (List.ofFn (fun x : Fin n =>
        (List.ofFn (fun z : Fin n =>
          if F x then 0 else if F z then f F else 0)).sum -
        (List.ofFn (fun z : Fin n =>
          if F x then 0 else if F z then
            f (sealSetBit (sealSetBit F z false) x true)
          else 0)).sum)).sum := by
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext x
      exact isumSub _ _
    _ = swapConstantSum f F - swapReplacementXSum f F := by
      rw [isumSub]
      rfl
    _ = (frontConfigMass F : Int) *
          ((n : Int) - (frontConfigMass F : Int)) * f F -
        replacementSum f F := by
      rw [swapConstant_expand, swapReplacementX_eq]


theorem sealJohnsonLaplacianUpDown :
    sealJohnsonLaplacianUpDownStatement := by
  unfold sealJohnsonLaplacianUpDownStatement
  intro n k f F hk hkn hF
  have hmNat := (mem_tasepFrontConfigSlice_iff F).1 hF
  have hm : (frontConfigMass F : Int) = (k : Int) := by
    rw [hmNat]
  have hCnat : sealJohnsonC n k = k * (n - k) + k := by
    unfold sealJohnsonC
    have hs : n + 1 - k = (n - k) + 1 := by omega
    rw [hs, Nat.mul_add, Nat.mul_one]
  have hcastSub : ((n - k : Nat) : Int) =
      (n : Int) - (k : Int) := by
    omega
  have hC : (sealJohnsonC n k : Int) =
      (k : Int) * ((n : Int) - (k : Int)) + (k : Int) := by
    rw [hCnat, Int.natCast_add, Int.natCast_mul, hcastSub]
  have harith : forall A K V R : Int,
      2 * (A * V - R) =
        2 * (A + K) * V - 2 * (K * V + R) := by
    intro A K V R
    rw [Int.mul_sub]
    rw [Int.mul_assoc]
    rw [Int.add_mul]
    rw [Int.mul_add]
    rw [Int.mul_add]
    omega
  rw [swap_two_forward k f F, forward_expand f F,
    upDown_expand f F, hm]
  simp only [hC]
  exact harith
    ((k : Int) * ((n : Int) - (k : Int)))
    (k : Int) (f F) (replacementSum f F)


end SealJohnsonSpectralRoute
end PPLLCompleteMultiLeaderCleanup


#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonLaplacianUpDown
