import Leader.Wu.Seal.JohnsonUpDownOperators
import Leader.Wu.Epoch.VoterSumTools


namespace PPLLCompleteMultiLeaderCleanup
namespace SealJohnsonSpectralRoute


open PPLL PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepRotationBridgeSol
open PPartialSealSweepTasepFiniteTimeSol
open SealJohnsonEnergyIdentity SealJohnsonPoincareA2a


set_option autoImplicit false
set_option Elab.async false


/-! ## 1. One-bit slice closure -/


private theorem sealSetBit_mass_true
    {n : Nat} (F : Fin n -> Bool) (x : Fin n)
    (hx : F x = false) :
    frontConfigMass (sealSetBit F x true) = frontConfigMass F + 1 := by
  unfold frontConfigMass
  have h := PPLLEpochVoterSumTools.sum_ofFn_balance_one
    (fun i : Fin n => if sealSetBit F x true i then 1 else 0)
    (fun i : Fin n => if F i then 1 else 0) x (by
      intro i hix
      simp [sealSetBit, hix])
  simpa [sealSetBit, hx] using h


private theorem sealSetBit_mass_false
    {n : Nat} (F : Fin n -> Bool) (x : Fin n)
    (hx : F x = true) :
    frontConfigMass (sealSetBit F x false) + 1 = frontConfigMass F := by
  unfold frontConfigMass
  have h := PPLLEpochVoterSumTools.sum_ofFn_balance_one
    (fun i : Fin n => if sealSetBit F x false i then 1 else 0)
    (fun i : Fin n => if F i then 1 else 0) x (by
      intro i hix
      simp [sealSetBit, hix])
  simpa [sealSetBit, hx] using h


theorem sealJohnsonSetBitSlice :
    sealJohnsonSetBitSliceStatement := by
  unfold sealJohnsonSetBitSliceStatement
  intro n k F x hk hkn
  constructor
  · intro hF hx
    apply (mem_tasepFrontConfigSlice_iff _).2
    have hm := (mem_tasepFrontConfigSlice_iff F).1 hF
    have hs := sealSetBit_mass_true F x hx
    omega
  · intro hF hx
    apply (mem_tasepFrontConfigSlice_iff _).2
    have hm := (mem_tasepFrontConfigSlice_iff F).1 hF
    have hs := sealSetBit_mass_false F x hx
    omega


/-! ## 2. Incidence bijection at one coordinate -/


private def sealUpperPart {n : Nat} (k : Nat) (x : Fin n) :
    List (Fin n -> Bool) :=
  (tasepFrontConfigSlice n k).filter
    (fun F => decide (F x = true))


private def sealLowerPart {n : Nat} (k : Nat) (x : Fin n) :
    List (Fin n -> Bool) :=
  (tasepFrontConfigSlice n (k - 1)).filter
    (fun F => decide (F x = false))


private theorem mem_sealUpperPart
    {n k : Nat} (x : Fin n) (F : Fin n -> Bool) :
    F ∈ sealUpperPart k x <->
      F ∈ tasepFrontConfigSlice n k /\ F x = true := by
  simp [sealUpperPart]


private theorem mem_sealLowerPart
    {n k : Nat} (x : Fin n) (F : Fin n -> Bool) :
    F ∈ sealLowerPart k x <->
      F ∈ tasepFrontConfigSlice n (k - 1) /\ F x = false := by
  simp [sealLowerPart]


private theorem sealFilterNodup
    {alpha : Type} (xs : List alpha) (p : alpha -> Bool)
    (hxs : xs.Nodup) : (xs.filter p).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at hxs |- 
  exact hxs.filter p


private theorem sealNodupMapOn
    {alpha beta : Type} {xs : List alpha}
    (hxs : xs.Nodup) (f : alpha -> beta)
    (hinj : forall a, a ∈ xs -> forall b, b ∈ xs ->
      f a = f b -> a = b) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rw [List.nodup_cons] at hxs
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        rw [List.mem_map] at hm
        obtain ⟨b, hb, hba⟩ := hm
        have heq : b = a :=
          hinj b (by simp [hb]) a (by simp) hba
        subst b
        exact hxs.1 hb
      · apply ih hxs.2
        intro b hb c hc hbc
        exact hinj b (by simp [hb]) c (by simp [hc]) hbc


private theorem sealSetBit_false_true_restore
    {n : Nat} (F : Fin n -> Bool) (x : Fin n)
    (hx : F x = true) :
    sealSetBit (sealSetBit F x false) x true = F := by
  funext i
  by_cases hix : i = x
  · subst i
    simp [sealSetBit, hx]
  · simp [sealSetBit, hix]


private theorem sealSetBit_true_false_restore
    {n : Nat} (F : Fin n -> Bool) (x : Fin n)
    (hx : F x = false) :
    sealSetBit (sealSetBit F x true) x false = F := by
  funext i
  by_cases hix : i = x
  · subst i
    simp [sealSetBit, hx]
  · simp [sealSetBit, hix]


private theorem sealSetBit_false_injective_on_upper
    {n k : Nat} (x : Fin n) {F G : Fin n -> Bool}
    (hF : F ∈ sealUpperPart k x)
    (hG : G ∈ sealUpperPart k x)
    (hset : sealSetBit F x false = sealSetBit G x false) : F = G := by
  have hFx := (mem_sealUpperPart x F).1 hF
  have hGx := (mem_sealUpperPart x G).1 hG
  funext i
  by_cases hix : i = x
  · subst i
    rw [hFx.2, hGx.2]
  · have h := congrFun hset i
    simpa [sealSetBit, hix] using h


private theorem sealUpperLowerPerm
    (n k : Nat) (x : Fin n) (hk : 0 < k) (hkn : k <= n) :
    ((sealUpperPart k x).map
      (fun F => sealSetBit F x false)).Perm
        (sealLowerPart k x) := by
  classical
  have hu : (sealUpperPart k x).Nodup := by
    unfold sealUpperPart
    exact sealFilterNodup _ _ (tasepFrontConfigSlice_nodup n k)
  have hm :
      ((sealUpperPart k x).map
        (fun F => sealSetBit F x false)).Nodup := by
    exact sealNodupMapOn hu _ (fun F hF G hG hEq =>
      sealSetBit_false_injective_on_upper x hF hG hEq)
  have hl : (sealLowerPart k x).Nodup := by
    unfold sealLowerPart
    exact sealFilterNodup _ _
      (tasepFrontConfigSlice_nodup n (k - 1))
  apply (List.perm_ext_iff_of_nodup hm hl).2
  intro G
  rw [List.mem_map]
  constructor
  · rintro ⟨F, hF, rfl⟩
    have hf := (mem_sealUpperPart x F).1 hF
    apply (mem_sealLowerPart x _).2
    refine ⟨(sealJohnsonSetBitSlice n k F x hk hkn).2
      hf.1 hf.2, ?_⟩
    simp [sealSetBit]
  · intro hG
    have hg := (mem_sealLowerPart x G).1 hG
    let F := sealSetBit G x true
    refine ⟨F, ?_, ?_⟩
    · apply (mem_sealUpperPart x F).2
      refine ⟨(sealJohnsonSetBitSlice n k G x hk hkn).1
        hg.1 hg.2, ?_⟩
      simp [F, sealSetBit]
    · simpa [F] using sealSetBit_true_false_restore G x hg.2


/-! ## Integer finite-sum algebra -/


private theorem sealIsumMapCongr
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


private theorem sealIsumMapAdd
    {alpha : Type} (xs : List alpha) (f g : alpha -> Int) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega


private theorem sealIsumMapComm
    {alpha beta : Type} (xs : List alpha) (ys : List beta)
    (f : alpha -> beta -> Int) :
    (xs.map (fun x => (ys.map (fun y => f x y)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      induction ys with
      | nil => rfl
      | cons b ys ih => simp only [List.map_cons, List.sum_cons]; omega
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, <- sealIsumMapAdd]


private theorem sealIsumMapOfFnComm
    {alpha : Type} {m : Nat} (xs : List alpha)
    (f : alpha -> Fin m -> Int) :
    (xs.map (fun x => (List.ofFn (fun i => f x i)).sum)).sum =
      (List.ofFn (fun i => (xs.map (fun x => f x i)).sum)).sum := by
  simpa [List.map_ofFn, Function.comp_def] using
    (sealIsumMapComm xs (List.ofFn (fun i : Fin m => i)) f)


private theorem sealIsumOfFnMulLeft
    {m : Nat} (c : Int) (f : Fin m -> Int) :
    (List.ofFn (fun i => c * f i)).sum = c * (List.ofFn f).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih, Int.mul_add]


private theorem sealIsumOfFnMulRight
    {m : Nat} (f : Fin m -> Int) (c : Int) :
    (List.ofFn (fun i => f i * c)).sum = (List.ofFn f).sum * c := by
  calc
    (List.ofFn (fun i => f i * c)).sum =
        (List.ofFn (fun i => c * f i)).sum := by
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext i
      exact Int.mul_comm _ _
    _ = c * (List.ofFn f).sum := sealIsumOfFnMulLeft c f
    _ = (List.ofFn f).sum * c := Int.mul_comm _ _


private theorem sealIsumFilter
    {alpha : Type} (xs : List alpha) (p : alpha -> Bool)
    (v : alpha -> Int) :
    ((xs.filter p).map v).sum =
      (xs.map (fun a => if p a then v a else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases h : p a <;> simp [h, ih]


private theorem sealPermSumInt
    {xs ys : List Int} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons x h ih => simp [ih]
  | swap x y xs =>
      simp only [List.sum_cons]
      omega
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2


private theorem sealUpperPartSum
    {n k : Nat} (x : Fin n) (v : (Fin n -> Bool) -> Int) :
    ((sealUpperPart k x).map v).sum =
      ((tasepFrontConfigSlice n k).map
        (fun F => if F x then v F else 0)).sum := by
  unfold sealUpperPart
  calc
    (((tasepFrontConfigSlice n k).filter
      (fun F => decide (F x = true))).map v).sum =
        ((tasepFrontConfigSlice n k).map (fun F =>
          if decide (F x = true) then v F else 0)).sum :=
      sealIsumFilter _ _ v
    _ = _ := by
      apply sealIsumMapCongr
      intro F _
      cases h : F x <;> simp [h]


private theorem sealLowerPartSum
    {n k : Nat} (x : Fin n) (v : (Fin n -> Bool) -> Int) :
    ((sealLowerPart k x).map v).sum =
      ((tasepFrontConfigSlice n (k - 1)).map
        (fun F => if F x then 0 else v F)).sum := by
  unfold sealLowerPart
  calc
    (((tasepFrontConfigSlice n (k - 1)).filter
      (fun F => decide (F x = false))).map v).sum =
        ((tasepFrontConfigSlice n (k - 1)).map (fun F =>
          if decide (F x = false) then v F else 0)).sum :=
      sealIsumFilter _ _ v
    _ = _ := by
      apply sealIsumMapCongr
      intro F _
      cases h : F x <;> simp [h]


private theorem sealMulUpExpand
    {n : Nat} (F : Fin n -> Bool) (a : Int) (g : SealIntObs n) :
    a * sealJohnsonUp g F =
      (List.ofFn (fun x : Fin n =>
        if F x then a * g (sealSetBit F x false) else 0)).sum := by
  unfold sealJohnsonUp
  rw [<- sealIsumOfFnMulLeft a
    (fun x : Fin n => if F x then g (sealSetBit F x false) else 0)]
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext x
  cases h : F x <;> simp [h]


private theorem sealDownMulExpand
    {n : Nat} (F : Fin n -> Bool) (f : SealIntObs n) (b : Int) :
    sealJohnsonDown f F * b =
      (List.ofFn (fun x : Fin n =>
        if F x then 0 else f (sealSetBit F x true) * b)).sum := by
  unfold sealJohnsonDown
  rw [<- sealIsumOfFnMulRight
    (fun x : Fin n => if F x then 0 else f (sealSetBit F x true)) b]
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext x
  cases h : F x <;> simp [h]


private theorem sealIncidenceReindex
    (n k : Nat) (f g : SealIntObs n) (x : Fin n)
    (hk : 0 < k) (hkn : k <= n) :
    ((sealUpperPart k x).map
      (fun F => f F * g (sealSetBit F x false))).sum =
      ((sealLowerPart k x).map
        (fun G => f (sealSetBit G x true) * g G)).sum := by
  have hp := (sealUpperLowerPerm n k x hk hkn).map
    (fun G => f (sealSetBit G x true) * g G)
  have hs := sealPermSumInt hp
  simp only [List.map_map, Function.comp_def] at hs
  have hr :
      ((sealUpperPart k x).map
        (fun F => f F * g (sealSetBit F x false))).sum =
      ((sealUpperPart k x).map (fun F =>
        f (sealSetBit (sealSetBit F x false) x true) *
          g (sealSetBit F x false))).sum := by
    apply sealIsumMapCongr
    intro F hF
    rw [sealSetBit_false_true_restore F x
      ((mem_sealUpperPart x F).1 hF).2]
  exact hr.trans hs


/-! ## 2. Counting-measure adjointness -/


theorem sealJohnsonUpDownAdjoint :
    sealJohnsonUpDownAdjointStatement := by
  unfold sealJohnsonUpDownAdjointStatement
  intro n k f g hk hkn
  unfold sealSliceIntDot
  calc
    ((tasepFrontConfigSlice n k).map
      (fun F => f F * sealJohnsonUp g F)).sum =
        ((tasepFrontConfigSlice n k).map (fun F =>
          (List.ofFn (fun x : Fin n =>
            if F x then
              f F * g (sealSetBit F x false)
            else 0)).sum)).sum := by
      apply sealIsumMapCongr
      intro F _
      exact sealMulUpExpand F (f F) g
    _ = (List.ofFn (fun x : Fin n =>
        ((tasepFrontConfigSlice n k).map (fun F =>
          if F x then
            f F * g (sealSetBit F x false)
          else 0)).sum)).sum :=
      sealIsumMapOfFnComm _ _
    _ = (List.ofFn (fun x : Fin n =>
        ((sealUpperPart k x).map (fun F =>
          f F * g (sealSetBit F x false))).sum)).sum := by
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext x
      exact (sealUpperPartSum x
        (fun F => f F * g (sealSetBit F x false))).symm
    _ = (List.ofFn (fun x : Fin n =>
        ((sealLowerPart k x).map (fun G =>
          f (sealSetBit G x true) * g G)).sum)).sum := by
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext x
      exact sealIncidenceReindex n k f g x hk hkn
    _ = (List.ofFn (fun x : Fin n =>
        ((tasepFrontConfigSlice n (k - 1)).map (fun G =>
          if G x then 0 else
            f (sealSetBit G x true) * g G)).sum)).sum := by
      apply congrArg List.sum
      apply congrArg List.ofFn
      funext x
      exact sealLowerPartSum x
        (fun G => f (sealSetBit G x true) * g G)
    _ = ((tasepFrontConfigSlice n (k - 1)).map (fun G =>
        (List.ofFn (fun x : Fin n =>
          if G x then 0 else
            f (sealSetBit G x true) * g G)).sum)).sum :=
      (sealIsumMapOfFnComm _ _).symm
    _ = ((tasepFrontConfigSlice n (k - 1)).map
        (fun G => sealJohnsonDown f G * g G)).sum := by
      apply sealIsumMapCongr
      intro G _
      exact (sealDownMulExpand G f (g G)).symm


end SealJohnsonSpectralRoute
end PPLLCompleteMultiLeaderCleanup


#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonSetBitSlice
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonSpectralRoute.sealJohnsonUpDownAdjoint
