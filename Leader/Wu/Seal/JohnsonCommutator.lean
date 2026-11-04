import Leader.Wu.Seal.JohnsonUpDownAdjoint

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

private def trueCountI {n : Nat} (F : Fin n -> Bool) : Int :=
  (List.ofFn (fun i => if F i then (1 : Int) else 0)).sum

private def falseCountI {n : Nat} (F : Fin n -> Bool) : Int :=
  (List.ofFn (fun i => if F i then (0 : Int) else 1)).sum

private theorem trueCount_eq_mass
    {n : Nat} (F : Fin n -> Bool) :
    trueCountI F = (frontConfigMass F : Int) := by
  unfold trueCountI frontConfigMass
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, Int.natCast_add]
      cases h : F 0 <;>
        simp [h, ih (fun i : Fin n => F i.succ)]

private theorem true_false_total
    {n : Nat} (F : Fin n -> Bool) :
    trueCountI F + falseCountI F = (n : Int) := by
  unfold trueCountI falseCountI
  calc
    (List.ofFn (fun i => if F i then (1 : Int) else 0)).sum +
        (List.ofFn (fun i => if F i then (0 : Int) else 1)).sum =
      (List.ofFn (fun i =>
        (if F i then (1 : Int) else 0) +
          (if F i then (0 : Int) else 1))).sum :=
      (isumAdd _ _).symm
    _ = (List.ofFn (fun _ : Fin n => (1 : Int))).sum := by
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext i
      cases h : F i <;> simp [h]
    _ = (n : Int) := by
      simpa using (isumConst (m := n) (1 : Int))

private theorem counts_of_slice
    {n k : Nat} (F : Fin n -> Bool)
    (hF : F ∈ tasepFrontConfigSlice n k) :
    trueCountI F = (k : Int) /\
      falseCountI F = (n : Int) - (k : Int) := by
  have hm := (mem_tasepFrontConfigSlice_iff F).1 hF
  have ht := trueCount_eq_mass F
  rw [hm] at ht
  have htot := true_false_total F
  exact ⟨ht, by omega⟩

private theorem isumIfTrueConst
    {n : Nat} (F : Fin n -> Bool) (a : Int) :
    (List.ofFn (fun i => if F i then a else 0)).sum =
      trueCountI F * a := by
  unfold trueCountI
  rw [← isumMulRight
    (fun i : Fin n => if F i then (1 : Int) else 0) a]
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext i
  cases h : F i <;> simp [h]

private theorem isumIfFalseConst
    {n : Nat} (F : Fin n -> Bool) (a : Int) :
    (List.ofFn (fun i => if F i then 0 else a)).sum =
      falseCountI F * a := by
  unfold falseCountI
  rw [← isumMulRight
    (fun i : Fin n => if F i then (0 : Int) else 1) a]
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext i
  cases h : F i <;> simp [h]

private theorem setBit_true_false_restore
    {n : Nat} (F : Fin n -> Bool) (x : Fin n)
    (hx : F x = false) :
    sealSetBit (sealSetBit F x true) x false = F := by
  funext i
  by_cases hix : i = x
  · subst i
    simp [sealSetBit, hx]
  · simp [sealSetBit, hix]

private theorem setBit_false_true_restore
    {n : Nat} (F : Fin n -> Bool) (x : Fin n)
    (hx : F x = true) :
    sealSetBit (sealSetBit F x false) x true = F := by
  funext i
  by_cases hix : i = x
  · subst i
    simp [sealSetBit, hx]
  · simp [sealSetBit, hix]

private theorem setBit_comm
    {n : Nat} (F : Fin n -> Bool) (x z : Fin n)
    (hxz : x ≠ z) :
    sealSetBit (sealSetBit F x true) z false =
      sealSetBit (sealSetBit F z false) x true := by
  funext i
  by_cases hix : i = x
  · subst i
    simp [sealSetBit, hxz, Ne.symm hxz]
  · by_cases hiz : i = z
    · subst i
      simp [sealSetBit, hxz, Ne.symm hxz, hix]
    · simp [sealSetBit, hix, hiz]

private def genuineReplacementSum
    {n : Nat} (g : SealIntObs n) (F : Fin n -> Bool) : Int :=
  (List.ofFn (fun x : Fin n =>
    (List.ofFn (fun z : Fin n =>
      if F x then 0 else if F z then
        g (sealSetBit (sealSetBit F x true) z false)
      else 0)).sum)).sum

private def genuineReplacementSumRev
    {n : Nat} (g : SealIntObs n) (F : Fin n -> Bool) : Int :=
  (List.ofFn (fun z : Fin n =>
    (List.ofFn (fun x : Fin n =>
      if F z then
        if F x then 0 else
          g (sealSetBit (sealSetBit F z false) x true)
      else 0)).sum)).sum

private theorem genuine_rev_eq
    {n : Nat} (g : SealIntObs n) (F : Fin n -> Bool) :
    genuineReplacementSumRev g F = genuineReplacementSum g F := by
  unfold genuineReplacementSumRev genuineReplacementSum
  calc
    (List.ofFn (fun z : Fin n =>
      (List.ofFn (fun x : Fin n =>
        if F z then if F x then 0 else
          g (sealSetBit (sealSetBit F z false) x true)
        else 0)).sum)).sum =
      (List.ofFn (fun x : Fin n =>
        (List.ofFn (fun z : Fin n =>
          if F z then if F x then 0 else
            g (sealSetBit (sealSetBit F z false) x true)
          else 0)).sum)).sum := isumComm _
    _ = _ := by
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext x
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext z
      cases hx : F x with
      | false =>
          cases hz : F z with
          | false => simp [hx, hz]
          | true =>
              have hxz : x ≠ z := by
                intro h
                subst z
                rw [hx] at hz
                cases hz
              simp [hx, hz, setBit_comm F x z hxz]
      | true => simp [hx]

private theorem downUpRow
    {n : Nat} (g : SealIntObs n) (F : Fin n -> Bool)
    (x : Fin n) (hx : F x = false) :
    sealJohnsonUp g (sealSetBit F x true) =
      g F +
        (List.ofFn (fun z : Fin n =>
          if F z then
            g (sealSetBit (sealSetBit F x true) z false)
          else 0)).sum := by
  unfold sealJohnsonUp
  have h := isumBalanceOne
    (fun z : Fin n =>
      if sealSetBit F x true z then
        g (sealSetBit (sealSetBit F x true) z false)
      else 0)
    (fun z : Fin n =>
      if F z then
        g (sealSetBit (sealSetBit F x true) z false)
      else 0) x (by
        intro z hzx
        simp [sealSetBit, hzx])
  have hr := setBit_true_false_restore F x hx
  simpa [sealSetBit, hx, hr, Int.add_comm] using h

private theorem upDownRow
    {n : Nat} (g : SealIntObs n) (F : Fin n -> Bool)
    (z : Fin n) (hz : F z = true) :
    sealJohnsonDown g (sealSetBit F z false) =
      g F +
        (List.ofFn (fun x : Fin n =>
          if F x then 0 else
            g (sealSetBit (sealSetBit F z false) x true))).sum := by
  unfold sealJohnsonDown
  have h := isumBalanceOne
    (fun x : Fin n =>
      if sealSetBit F z false x then 0 else
        g (sealSetBit (sealSetBit F z false) x true))
    (fun x : Fin n =>
      if F x then 0 else
        g (sealSetBit (sealSetBit F z false) x true)) z (by
        intro x hxz
        simp [sealSetBit, hxz])
  have hr := setBit_false_true_restore F z hz
  simpa [sealSetBit, hz, hr, Int.add_comm] using h

private theorem downUp_expand
    {n : Nat} (g : SealIntObs n) (F : Fin n -> Bool) :
    sealJohnsonDown (sealJohnsonUp g) F =
      falseCountI F * g F + genuineReplacementSum g F := by
  unfold sealJohnsonDown
  calc
    (List.ofFn (fun x : Fin n =>
      if F x then 0 else sealJohnsonUp g (sealSetBit F x true))).sum =
      (List.ofFn (fun x : Fin n =>
        (if F x then 0 else g F) +
          (List.ofFn (fun z : Fin n =>
            if F x then 0 else if F z then
              g (sealSetBit (sealSetBit F x true) z false)
            else 0)).sum)).sum := by
        apply congrArg List.sum
        apply congrArg List.ofFn
        funext x
        cases hx : F x with
        | false => simpa [hx] using downUpRow g F x hx
        | true => simp [hx, isumZero]
    _ = (List.ofFn (fun x : Fin n =>
          if F x then 0 else g F)).sum +
        (List.ofFn (fun x : Fin n =>
          (List.ofFn (fun z : Fin n =>
            if F x then 0 else if F z then
              g (sealSetBit (sealSetBit F x true) z false)
            else 0)).sum)).sum := isumAdd _ _
    _ = falseCountI F * g F + genuineReplacementSum g F := by
      rw [isumIfFalseConst]
      rfl

private theorem upDown_expand
    {n : Nat} (g : SealIntObs n) (F : Fin n -> Bool) :
    sealJohnsonUp (sealJohnsonDown g) F =
      trueCountI F * g F + genuineReplacementSum g F := by
  unfold sealJohnsonUp
  calc
    (List.ofFn (fun z : Fin n =>
      if F z then sealJohnsonDown g (sealSetBit F z false) else 0)).sum =
      (List.ofFn (fun z : Fin n =>
        (if F z then g F else 0) +
          (List.ofFn (fun x : Fin n =>
            if F z then
              if F x then 0 else
                g (sealSetBit (sealSetBit F z false) x true)
            else 0)).sum)).sum := by
        apply congrArg List.sum
        apply congrArg List.ofFn
        funext z
        cases hz : F z with
        | false => simp [hz, isumZero]
        | true => simpa [hz] using upDownRow g F z hz
    _ = (List.ofFn (fun z : Fin n =>
          if F z then g F else 0)).sum +
        genuineReplacementSumRev g F := isumAdd _ _
    _ = trueCountI F * g F + genuineReplacementSumRev g F := by
      rw [isumIfTrueConst]
    _ = trueCountI F * g F + genuineReplacementSum g F := by
      rw [genuine_rev_eq]

theorem sealJohnsonCommutator :
    sealJohnsonCommutatorStatement := by
  unfold sealJohnsonCommutatorStatement
  intro n k g F hk hkn hF
  have hc := counts_of_slice F hF
  have hcoef :
      falseCountI F = trueCountI F +
        ((n : Int) - 2 * (k : Int) + 2) := by
    rcases hc with ⟨ht, hf⟩
    omega
  rw [downUp_expand, upDown_expand, hcoef, Int.add_mul]
  omega

end SealJohnsonSpectralRoute
end PPLLCompleteMultiLeaderCleanup

#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonCommutator
