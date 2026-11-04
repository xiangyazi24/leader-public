import Leader.Wu.Seal.JohnsonPoincareStatements

namespace PPLLCompleteMultiLeaderCleanup
namespace SealJohnsonPoincareA2b

open PPLL PPLLNoCheckBirthConditionTwoGeometry
open PPartialSealSweepTasepRotationBridgeSol
open PPartialSealSweepTasepFiniteTimeSol
open SealJohnsonEnergyIdentity
open SealJohnsonPoincareA2a

set_option autoImplicit false
set_option Elab.async false

/-! Small finite-sum library, all core Lean. -/

private theorem isum_map_congr
    {α : Type} (xs : List α) (f g : α -> Int)
    (h : ∀ x, f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [h a, ih]

private theorem isum_map_add
    {α : Type} (xs : List α) (f g : α -> Int) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

private theorem isum_map_sub
    {α : Type} (xs : List α) (f g : α -> Int) :
    (xs.map (fun x => f x - g x)).sum =
      (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

private theorem isum_map_mul_left
    {α : Type} (xs : List α) (c : Int) (f : α -> Int) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Int.mul_add]

private theorem isum_map_const
    {α : Type} (xs : List α) (c : Int) :
    (xs.map (fun _ => c)).sum = (xs.length : Int) * c := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Int.natCast_succ, ih, Int.add_mul, Int.one_mul]
      omega

private theorem isum_map_comm
    {α β : Type} (xs : List α) (ys : List β)
    (f : α -> β -> Int) :
    (xs.map (fun x => (ys.map (fun y => f x y)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      simpa using (isum_map_const ys 0).symm
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      simpa using
        (isum_map_add ys (fun y => f a y)
          (fun y => (xs.map (fun x => f x y)).sum)).symm

private theorem ofFn_eq_of_pointwise
    {α : Type} {m : Nat} (f g : Fin m -> α)
    (h : ∀ i, f i = g i) :
    List.ofFn f = List.ofFn g := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.ofFn_succ, h 0,
        ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => h i.succ)]

private theorem isum_map_ofFn_comm
    {α : Type} {m : Nat} (xs : List α)
    (f : α -> Fin m -> Int) :
    (xs.map (fun x => (List.ofFn (fun i => f x i)).sum)).sum =
      (List.ofFn (fun i => (xs.map (fun x => f x i)).sum)).sum := by
  simpa [List.map_ofFn, Function.comp_def] using
    (isum_map_comm xs (List.ofFn (fun i : Fin m => i)) f)

private theorem isum_map_double_ofFn_comm
    {α : Type} {m q : Nat} (xs : List α)
    (f : α -> Fin m -> Fin q -> Int) :
    (xs.map (fun x =>
      (List.ofFn (fun i =>
        (List.ofFn (fun j => f x i j)).sum)).sum)).sum =
      (List.ofFn (fun i =>
        (List.ofFn (fun j =>
          (xs.map (fun x => f x i j)).sum)).sum)).sum := by
  calc
    (xs.map (fun x =>
      (List.ofFn (fun i =>
        (List.ofFn (fun j => f x i j)).sum)).sum)).sum =
        (List.ofFn (fun i =>
          (xs.map (fun x =>
            (List.ofFn (fun j => f x i j)).sum)).sum)).sum :=
      isum_map_ofFn_comm xs _
    _ = _ := by
      apply congrArg List.sum
      apply ofFn_eq_of_pointwise
      intro i
      exact isum_map_ofFn_comm xs (fun x j => f x i j)

private theorem isum_ofFn_mul_left
    {m : Nat} (c : Int) (f : Fin m -> Int) :
    (List.ofFn (fun i => c * f i)).sum = c * (List.ofFn f).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        ih (fun i => f i.succ), Int.mul_add]

private theorem isum_double_ofFn_mul_left
    {m q : Nat} (c : Int) (f : Fin m -> Fin q -> Int) :
    (List.ofFn (fun i =>
      (List.ofFn (fun j => c * f i j)).sum)).sum =
      c * (List.ofFn (fun i => (List.ofFn (fun j => f i j)).sum)).sum := by
  calc
    (List.ofFn (fun i =>
      (List.ofFn (fun j => c * f i j)).sum)).sum =
        (List.ofFn (fun i =>
          c * (List.ofFn (fun j => f i j)).sum)).sum := by
      apply congrArg List.sum
      apply ofFn_eq_of_pointwise
      intro i
      exact isum_ofFn_mul_left c (fun j => f i j)
    _ = _ := isum_ofFn_mul_left c _

private theorem cast_sum_nat (xs : List Nat) :
    (xs.sum : Int) =
      (xs.map (fun a : Nat => (a : Int))).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.sum_cons, List.map_cons]
      rw [Int.natCast_add, ih]

private theorem cast_map_sum_nat
    {α : Type} (xs : List α) (f : α -> Nat) :
    ((xs.map f).sum : Int) =
      (xs.map (fun x => (f x : Int))).sum := by
  simpa [List.map_map, Function.comp_def] using cast_sum_nat (xs.map f)

private theorem cast_ofFn_sum_nat
    {m : Nat} (f : Fin m -> Nat) :
    ((List.ofFn f).sum : Int) =
      (List.ofFn (fun i => (f i : Int))).sum := by
  simpa [List.map_ofFn, Function.comp_def] using cast_sum_nat (List.ofFn f)

private theorem perm_sum_int
    {xs ys : List Int} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons x h ih => simp [ih]
  | swap x y xs =>
      simp only [List.sum_cons]
      omega
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

private theorem ofFn_nodup
    {α : Type} {r : Nat} (f : Fin r -> α)
    (hf : ∀ i j, f i = f j -> i = j) : (List.ofFn f).Nodup := by
  induction r with
  | zero =>
      rw [List.ofFn_zero]
      exact List.nodup_nil
  | succ r ih =>
      rw [List.ofFn_succ]
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        rcases List.mem_ofFn.mp hm with ⟨i, hi⟩
        have hv := congrArg Fin.val (hf i.succ 0 hi)
        change i.val + 1 = 0 at hv
        omega
      · apply ih
        intro i j he
        have hv := congrArg Fin.val (hf i.succ j.succ he)
        apply Fin.ext
        change i.val + 1 = j.val + 1 at hv
        omega

private theorem nodup_map_of_injective
    {α β : Type} {xs : List α} (hxs : xs.Nodup)
    (f : α -> β) (hf : Function.Injective f) :
    (xs.map f).Nodup := by
  exact List.Pairwise.map f (fun _ _ hne => hf.ne hne) hxs

private theorem injective_of_involutive
    {α : Type} (f : α -> α)
    (h : ∀ x, f (f x) = x) : Function.Injective f := by
  intro a b hab
  calc
    a = f (f a) := (h a).symm
    _ = f (f b) := congrArg f hab
    _ = b := h b

/-! 1. Slice closure. -/

private def swapIndex {n : Nat} (x z i : Fin n) : Fin n :=
  if i = x then z else if i = z then x else i

private theorem swapIndex_involutive
    {n : Nat} (x z : Fin n) :
    ∀ i, swapIndex x z (swapIndex x z i) = i := by
  intro i
  by_cases hxz : x = z
  · subst z
    by_cases h : i = x <;> simp [swapIndex, h]
  · by_cases hix : i = x
    · subst i
      simp [swapIndex, hxz]
    · by_cases hiz : i = z
      · subst i
        simp [swapIndex, hxz, hix]
      · simp [swapIndex, hxz, hix, hiz]

private theorem sealTranspose_apply_eq
    {n : Nat} (F : Fin n -> Bool) (x z i : Fin n) :
    sealTransposeFrontConfig F x z i = F (swapIndex x z i) := by
  unfold sealTransposeFrontConfig swapIndex
  by_cases hix : i = x
  · simp [hix]
  · by_cases hiz : i = z
    · by_cases hzx : z = x <;> simp [hix, hiz, hzx]
    · simp [hix, hiz]

private theorem index_swap_perm
    {n : Nat} (x z : Fin n) :
    (List.ofFn (fun i : Fin n => swapIndex x z i)).Perm
      (List.ofFn (fun i : Fin n => i)) := by
  have hinj : Function.Injective (swapIndex x z) :=
    injective_of_involutive (swapIndex x z)
      (swapIndex_involutive x z)
  have hl := ofFn_nodup (fun i : Fin n => swapIndex x z i)
    (fun i j h => hinj h)
  have hr := ofFn_nodup (fun i : Fin n => i) (fun _ _ h => h)
  apply (List.perm_ext_iff_of_nodup hl hr).2
  intro i
  constructor
  · intro _
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  · intro _
    exact List.mem_ofFn.mpr
      ⟨swapIndex x z i, swapIndex_involutive x z i⟩

private theorem frontConfigMass_sealTranspose
    {n : Nat} (F : Fin n -> Bool) (x z : Fin n) :
    frontConfigMass (sealTransposeFrontConfig F x z) = frontConfigMass F := by
  let weight : Fin n -> Nat := fun i => if F i then 1 else 0
  have hp := (index_swap_perm x z).map weight
  have hs := hp.sum_nat
  simpa [frontConfigMass, sealTranspose_apply_eq, weight,
    List.map_ofFn, Function.comp_def] using hs

private theorem sealTranspose_involutive
    {n : Nat} (x z : Fin n) :
    ∀ F : Fin n -> Bool,
      sealTransposeFrontConfig (sealTransposeFrontConfig F x z) x z = F := by
  intro F
  funext i
  rw [sealTranspose_apply_eq, sealTranspose_apply_eq,
    swapIndex_involutive x z i]

@[simp] private theorem sealTranspose_twice
    {n : Nat} (F : Fin n -> Bool) (x z : Fin n) :
    sealTransposeFrontConfig (sealTransposeFrontConfig F x z) x z = F :=
  sealTranspose_involutive x z F

theorem sealSliceTransposeClosed : sealSliceTransposeClosedStatement := by
  intro n k F x z hF
  rw [mem_tasepFrontConfigSlice_iff] at hF ⊢
  rw [frontConfigMass_sealTranspose]
  exact hF

private theorem slice_map_transpose_perm
    {n k : Nat} (x z : Fin n) :
    ((tasepFrontConfigSlice n k).map
      (fun F => sealTransposeFrontConfig F x z)).Perm
      (tasepFrontConfigSlice n k) := by
  have hinj : Function.Injective
      (fun F : Fin n -> Bool => sealTransposeFrontConfig F x z) :=
    injective_of_involutive
      (fun F : Fin n -> Bool => sealTransposeFrontConfig F x z)
      (sealTranspose_involutive x z)
  have hl := nodup_map_of_injective
    (tasepFrontConfigSlice_nodup n k) _ hinj
  apply (List.perm_ext_iff_of_nodup hl
    (tasepFrontConfigSlice_nodup n k)).2
  intro G
  constructor
  · intro hG
    rw [List.mem_map] at hG
    obtain ⟨F, hF, rfl⟩ := hG
    exact sealSliceTransposeClosed n k F x z hF
  · intro hG
    rw [List.mem_map]
    refine ⟨sealTransposeFrontConfig G x z,
      sealSliceTransposeClosed n k G x z hG, ?_⟩
    exact sealTranspose_twice G x z

/-! Mean-zero all-pairs identity. -/

private def allPairsInt {n : Nat} (k : Nat) (f : SealIntObs n) : Int :=
  ((tasepFrontConfigSlice n k).map (fun F =>
    ((tasepFrontConfigSlice n k).map (fun G =>
      (f F - f G) * (f F - f G))).sum)).sum

private theorem normSq_cast
    {n : Nat} (k : Nat) (f : SealIntObs n) :
    (sealSliceIntNormSq k f : Int) = sealSliceIntDot k f f := by
  unfold sealSliceIntNormSq sealSliceIntDot
  calc
    (((tasepFrontConfigSlice n k).map
      (fun F => Int.natAbs (f F) ^ 2)).sum : Int) =
        ((tasepFrontConfigSlice n k).map
          (fun F => ((Int.natAbs (f F) ^ 2 : Nat) : Int))).sum :=
      cast_map_sum_nat _ _
    _ = ((tasepFrontConfigSlice n k).map
        (fun F => f F * f F)).sum := by
      apply isum_map_congr
      intro F
      simpa [Nat.pow_two] using
        (Int.natAbs_mul_self (a := f F))

private theorem allPairs_cast
    {n : Nat} (k : Nat) (f : SealIntObs n) :
    (sealAllPairsSquaredEnergy k f : Int) = allPairsInt k f := by
  unfold sealAllPairsSquaredEnergy allPairsInt
  calc
    (((tasepFrontConfigSlice n k).map (fun F =>
      ((tasepFrontConfigSlice n k).map (fun G =>
        sealSquaredGap f F G)).sum)).sum : Int) =
      ((tasepFrontConfigSlice n k).map (fun F =>
        (((tasepFrontConfigSlice n k).map (fun G =>
          sealSquaredGap f F G)).sum : Int))).sum :=
      cast_map_sum_nat _ _
    _ = ((tasepFrontConfigSlice n k).map (fun F =>
        ((tasepFrontConfigSlice n k).map (fun G =>
          (sealSquaredGap f F G : Int))).sum)).sum := by
      apply isum_map_congr
      intro F
      exact cast_map_sum_nat _ _
    _ = ((tasepFrontConfigSlice n k).map (fun F =>
        ((tasepFrontConfigSlice n k).map (fun G =>
          (f F - f G) * (f F - f G))).sum)).sum := by
      apply isum_map_congr
      intro F
      apply isum_map_congr
      intro G
      simpa [sealSquaredGap, Nat.pow_two] using
        (Int.natAbs_mul_self (a := f F - f G))

private theorem sq_sub_expand (a b : Int) :
    (a - b) * (a - b) = a * a - 2 * (a * b) + b * b := by
  simp only [Int.sub_mul, Int.mul_sub]
  rw [Int.mul_comm b a]
  omega

private theorem gap_row_mean_zero
    {α : Type} (xs : List α) (f : α -> Int) (a : α)
    (hsum : (xs.map f).sum = 0) :
    (xs.map (fun b => (f a - f b) * (f a - f b))).sum =
      (xs.length : Int) * (f a * f a) +
        (xs.map (fun b => f b * f b)).sum := by
  calc
    (xs.map (fun b => (f a - f b) * (f a - f b))).sum =
        (xs.map (fun b =>
          (f a * f a - 2 * (f a * f b)) + f b * f b)).sum := by
      apply isum_map_congr
      intro b
      exact sq_sub_expand (f a) (f b)
    _ = (xs.map (fun b => f a * f a - 2 * (f a * f b))).sum +
        (xs.map (fun b => f b * f b)).sum := isum_map_add _ _ _
    _ = ((xs.map (fun _ => f a * f a)).sum -
          (xs.map (fun b => 2 * (f a * f b))).sum) +
        (xs.map (fun b => f b * f b)).sum := by
      rw [isum_map_sub]
    _ = ((xs.length : Int) * (f a * f a) -
          2 * (f a * (xs.map f).sum)) +
        (xs.map (fun b => f b * f b)).sum := by
      rw [isum_map_const]
      rw [isum_map_mul_left xs 2 (fun b => f a * f b)]
      rw [isum_map_mul_left xs (f a) f]
    _ = _ := by
      rw [hsum]
      simp

private theorem allPairsInt_mean_zero
    {n : Nat} (k : Nat) (f : SealIntObs n)
    (hzero : sealSliceIntSum k f = 0) :
    allPairsInt k f =
      2 * (tasepFrontConfigSlice n k).length * sealSliceIntDot k f f := by
  have hz : ((tasepFrontConfigSlice n k).map f).sum = 0 := by
    simpa [sealSliceIntSum] using hzero
  unfold allPairsInt sealSliceIntDot
  let N : Int :=
    ((tasepFrontConfigSlice n k).map (fun F => f F * f F)).sum
  calc
    ((tasepFrontConfigSlice n k).map (fun F =>
      ((tasepFrontConfigSlice n k).map (fun G =>
        (f F - f G) * (f F - f G))).sum)).sum =
      ((tasepFrontConfigSlice n k).map (fun F =>
        ((tasepFrontConfigSlice n k).length : Int) * (f F * f F) + N)).sum := by
      apply isum_map_congr
      intro F
      simpa [N] using
        gap_row_mean_zero (tasepFrontConfigSlice n k) f F hz
    _ = ((tasepFrontConfigSlice n k).map (fun F =>
          ((tasepFrontConfigSlice n k).length : Int) * (f F * f F))).sum +
        ((tasepFrontConfigSlice n k).map (fun _ => N)).sum :=
      isum_map_add _ _ _
    _ = ((tasepFrontConfigSlice n k).length : Int) * N +
        ((tasepFrontConfigSlice n k).length : Int) * N := by
      rw [isum_map_mul_left, isum_map_const]
    _ = 2 * (((tasepFrontConfigSlice n k).length : Int) * N) := by
      omega
    _ = 2 * (tasepFrontConfigSlice n k).length * N := by
      exact (Int.mul_assoc (2 : Int)
        ((tasepFrontConfigSlice n k).length : Int) N).symm
    _ = _ := by rfl

theorem sealAllPairsMeanZero : sealAllPairsMeanZeroStatement := by
  intro n k f hzero
  have hInt :
      (sealAllPairsSquaredEnergy k f : Int) =
        ((2 * (tasepFrontConfigSlice n k).length *
          sealSliceIntNormSq k f : Nat) : Int) := by
    calc
      (sealAllPairsSquaredEnergy k f : Int) = allPairsInt k f :=
        allPairs_cast k f
      _ = 2 * (tasepFrontConfigSlice n k).length *
          sealSliceIntDot k f f := allPairsInt_mean_zero k f hzero
      _ = ((2 * (tasepFrontConfigSlice n k).length *
          sealSliceIntNormSq k f : Nat) : Int) := by
        rw [← normSq_cast]
        simp
  exact Int.ofNat_inj.mp hInt

/-! Ordered-swap Green identity. -/

private def transEnergyInt {n : Nat} (k : Nat) (f : SealIntObs n) : Int :=
  (List.ofFn (fun x : Fin n =>
    (List.ofFn (fun z : Fin n =>
      ((tasepFrontConfigSlice n k).map (fun F =>
        (f F - f (sealTransposeFrontConfig F x z)) *
          (f F - f (sealTransposeFrontConfig F x z)))).sum)).sum)).sum

private def swapDotInt {n : Nat} (k : Nat) (f : SealIntObs n) : Int :=
  (List.ofFn (fun x : Fin n =>
    (List.ofFn (fun z : Fin n =>
      ((tasepFrontConfigSlice n k).map (fun F =>
        f F * (f F - f (sealTransposeFrontConfig F x z)))).sum)).sum)).sum

private theorem transEnergy_cast
    {n : Nat} (k : Nat) (f : SealIntObs n) :
    (sealArbitraryTranspositionEnergy k f : Int) = transEnergyInt k f := by
  unfold sealArbitraryTranspositionEnergy transEnergyInt
  calc
    ((List.ofFn (fun x : Fin n =>
      (List.ofFn (fun z : Fin n =>
        ((tasepFrontConfigSlice n k).map (fun F =>
          sealSquaredGap f F
            (sealTransposeFrontConfig F x z))).sum)).sum)).sum : Int) =
      (List.ofFn (fun x : Fin n =>
        ((List.ofFn (fun z : Fin n =>
          ((tasepFrontConfigSlice n k).map (fun F =>
            sealSquaredGap f F
              (sealTransposeFrontConfig F x z))).sum)).sum : Int))).sum :=
      cast_ofFn_sum_nat _
    _ = (List.ofFn (fun x : Fin n =>
        (List.ofFn (fun z : Fin n =>
          (((tasepFrontConfigSlice n k).map (fun F =>
            sealSquaredGap f F
              (sealTransposeFrontConfig F x z))).sum : Int))).sum)).sum := by
      apply congrArg List.sum
      apply ofFn_eq_of_pointwise
      intro x
      exact cast_ofFn_sum_nat _
    _ = (List.ofFn (fun x : Fin n =>
        (List.ofFn (fun z : Fin n =>
          ((tasepFrontConfigSlice n k).map (fun F =>
            (sealSquaredGap f F
              (sealTransposeFrontConfig F x z) : Int))).sum)).sum)).sum := by
      apply congrArg List.sum
      apply ofFn_eq_of_pointwise
      intro x
      apply congrArg List.sum
      apply ofFn_eq_of_pointwise
      intro z
      exact cast_map_sum_nat _ _
    _ = _ := by
      apply congrArg List.sum
      apply ofFn_eq_of_pointwise
      intro x
      apply congrArg List.sum
      apply ofFn_eq_of_pointwise
      intro z
      apply isum_map_congr
      intro F
      simpa [sealSquaredGap, Nat.pow_two] using
        (Int.natAbs_mul_self
          (a := f F - f (sealTransposeFrontConfig F x z)))

private theorem sq_sub_split (a b : Int) :
    (a - b) * (a - b) = a * (a - b) + b * (b - a) := by
  simp only [Int.sub_mul, Int.mul_sub]
  omega

private theorem fixed_swap_green
    {n : Nat} (k : Nat) (f : SealIntObs n) (x z : Fin n) :
    ((tasepFrontConfigSlice n k).map (fun F =>
      (f F - f (sealTransposeFrontConfig F x z)) *
        (f F - f (sealTransposeFrontConfig F x z)))).sum =
      2 * ((tasepFrontConfigSlice n k).map (fun F =>
        f F * (f F - f (sealTransposeFrontConfig F x z)))).sum := by
  have hp := (slice_map_transpose_perm (n := n) (k := k) x z).map
    (fun F => f F * (f F - f (sealTransposeFrontConfig F x z)))
  have hs := perm_sum_int hp
  have hreindex :
      ((tasepFrontConfigSlice n k).map (fun F =>
        f (sealTransposeFrontConfig F x z) *
          (f (sealTransposeFrontConfig F x z) - f F))).sum =
      ((tasepFrontConfigSlice n k).map (fun F =>
        f F * (f F - f (sealTransposeFrontConfig F x z)))).sum := by
    simpa [List.map_map, Function.comp_def] using hs
  calc
    ((tasepFrontConfigSlice n k).map (fun F =>
      (f F - f (sealTransposeFrontConfig F x z)) *
        (f F - f (sealTransposeFrontConfig F x z)))).sum =
      ((tasepFrontConfigSlice n k).map (fun F =>
        f F * (f F - f (sealTransposeFrontConfig F x z)) +
          f (sealTransposeFrontConfig F x z) *
            (f (sealTransposeFrontConfig F x z) - f F))).sum := by
      apply isum_map_congr
      intro F
      exact sq_sub_split _ _
    _ = ((tasepFrontConfigSlice n k).map (fun F =>
          f F * (f F - f (sealTransposeFrontConfig F x z)))).sum +
        ((tasepFrontConfigSlice n k).map (fun F =>
          f (sealTransposeFrontConfig F x z) *
            (f (sealTransposeFrontConfig F x z) - f F))).sum :=
      isum_map_add _ _ _
    _ = ((tasepFrontConfigSlice n k).map (fun F =>
          f F * (f F - f (sealTransposeFrontConfig F x z)))).sum +
        ((tasepFrontConfigSlice n k).map (fun F =>
          f F * (f F - f (sealTransposeFrontConfig F x z)))).sum := by
      rw [hreindex]
    _ = _ := by omega

private theorem dot_laplacian_eq_swapDotInt
    {n : Nat} (k : Nat) (f : SealIntObs n) :
    sealSliceIntDot k f (sealOrderedSwapLaplacianInt k f) =
      swapDotInt k f := by
  unfold sealSliceIntDot sealOrderedSwapLaplacianInt swapDotInt
  calc
    ((tasepFrontConfigSlice n k).map (fun F =>
      f F * (List.ofFn (fun x : Fin n =>
        (List.ofFn (fun z : Fin n =>
          f F - f (sealTransposeFrontConfig F x z))).sum)).sum)).sum =
      ((tasepFrontConfigSlice n k).map (fun F =>
        (List.ofFn (fun x : Fin n =>
          (List.ofFn (fun z : Fin n =>
            f F * (f F - f (sealTransposeFrontConfig F x z)))).sum)).sum)).sum := by
      apply isum_map_congr
      intro F
      calc
        f F * (List.ofFn (fun x : Fin n =>
          (List.ofFn (fun z : Fin n =>
            f F - f (sealTransposeFrontConfig F x z))).sum)).sum =
          (List.ofFn (fun x : Fin n =>
            f F * (List.ofFn (fun z : Fin n =>
              f F - f (sealTransposeFrontConfig F x z))).sum)).sum :=
          (isum_ofFn_mul_left (f F) _).symm
        _ = (List.ofFn (fun x : Fin n =>
            (List.ofFn (fun z : Fin n =>
              f F * (f F - f (sealTransposeFrontConfig F x z)))).sum)).sum := by
          apply congrArg List.sum
          apply ofFn_eq_of_pointwise
          intro x
          exact (isum_ofFn_mul_left (f F) _).symm
    _ = _ := isum_map_double_ofFn_comm
      (tasepFrontConfigSlice n k)
      (fun F x z => f F * (f F - f (sealTransposeFrontConfig F x z)))

theorem sealOrderedSwapGreen : sealOrderedSwapGreenStatement := by
  intro n k f
  rw [transEnergy_cast, dot_laplacian_eq_swapDotInt]
  unfold transEnergyInt swapDotInt
  calc
    (List.ofFn (fun x : Fin n =>
      (List.ofFn (fun z : Fin n =>
        ((tasepFrontConfigSlice n k).map (fun F =>
          (f F - f (sealTransposeFrontConfig F x z)) *
            (f F - f (sealTransposeFrontConfig F x z)))).sum)).sum)).sum =
      (List.ofFn (fun x : Fin n =>
        (List.ofFn (fun z : Fin n =>
          2 * ((tasepFrontConfigSlice n k).map (fun F =>
            f F * (f F - f (sealTransposeFrontConfig F x z)))).sum)).sum)).sum := by
      apply congrArg List.sum
      apply ofFn_eq_of_pointwise
      intro x
      apply congrArg List.sum
      apply ofFn_eq_of_pointwise
      intro z
      exact fixed_swap_green k f x z
    _ = 2 * (List.ofFn (fun x : Fin n =>
        (List.ofFn (fun z : Fin n =>
          ((tasepFrontConfigSlice n k).map (fun F =>
            f F * (f F - f (sealTransposeFrontConfig F x z)))).sum)).sum)).sum :=
      isum_double_ofFn_mul_left 2 _

end SealJohnsonPoincareA2b
end PPLLCompleteMultiLeaderCleanup

#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonPoincareA2b.sealSliceTransposeClosed
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonPoincareA2b.sealAllPairsMeanZero
#print axioms PPLLCompleteMultiLeaderCleanup.SealJohnsonPoincareA2b.sealOrderedSwapGreen
