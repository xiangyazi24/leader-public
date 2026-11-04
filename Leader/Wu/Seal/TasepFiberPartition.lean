import Leader.Wu.Seal.TasepVarianceDrop

namespace PPLLCompleteMultiLeaderCleanup
namespace SealTasepGeometricDecayFiberList

set_option autoImplicit false
set_option Elab.async false

noncomputable def eqb {a : Type} (x y : a) : Bool :=
  @ite Bool (x = y) (Classical.propDecidable _) true false

theorem isumMapAdd {a : Type} (xs : List a) (f g : a -> Int) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem isumMapMulLeft {a : Type} (xs : List a) (c : Int) (f : a -> Int) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Int.mul_add]

theorem isumMapConst {a : Type} (xs : List a) (c : Int) :
    (xs.map (fun _ => c)).sum = (xs.length : Int) * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Int.natCast_succ, ih, Int.add_mul, Int.one_mul]
      omega

theorem isumMapComm {a b : Type} (xs : List a) (ys : List b)
    (f : a -> b -> Int) :
    (xs.map (fun x => (ys.map (fun y => f x y)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      simpa using (isumMapConst ys 0).symm
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      simpa using
        (isumMapAdd ys (fun y => f x y)
          (fun y => (xs.map (fun z => f z y)).sum)).symm

theorem isumFlatMap {a b : Type} (xs : List a) (ys : a -> List b)
    (f : b -> Int) :
    ((xs.flatMap ys).map f).sum =
      (xs.map (fun x => ((ys x).map f).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, ih]

theorem isumFilter {a : Type} (xs : List a) (p : a -> Bool)
    (f : a -> Int) :
    ((xs.filter p).map f).sum =
      (xs.map (fun x => if p x then f x else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h : p x
      · simp [List.filter_cons, h, ih]
      · simp [List.filter_cons, h, ih]

theorem isumMapMul {a b : Type} (xs : List a) (ys : List b)
    (f : a -> Int) (g : b -> Int) :
    (xs.map f).sum * (ys.map g).sum =
      (xs.map (fun x => (ys.map (fun y => f x * g y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Int.add_mul, ih, <- isumMapMulLeft ys (f x) g]

theorem isumOfFnConst (m : Nat) (c : Int) :
    (List.ofFn (fun _ : Fin m => c)).sum = (m : Int) * c := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Int.natCast_succ,
        Int.add_mul, Int.one_mul]
      omega

theorem isumOfFnMulRight {m : Nat} (f : Fin m -> Int) (c : Int) :
    (List.ofFn (fun i => f i * c)).sum = (List.ofFn f).sum * c := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons,
        ih (fun i => f i.succ), Int.add_mul]

theorem castMapSumNat {a : Type} (xs : List a) (f : a -> Nat) :
    ((xs.map f).sum : Int) = (xs.map (fun x => (f x : Int))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Int.natCast_add, ih]

theorem castOfFnSumNat {m : Nat} (f : Fin m -> Nat) :
    ((List.ofFn f).sum : Int) =
      (List.ofFn (fun i => (f i : Int))).sum := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, Int.natCast_add,
        List.ofFn_succ, List.sum_cons, ih (fun i => f i.succ)]

theorem isumEqFiber {b : Type} (ys : List b) (hys : ys.Nodup)
    (y : b) (c : Int) :
    (ys.map (fun z => if eqb y z then c else 0)).sum =
      @ite Int (y ∈ ys) (Classical.propDecidable _) c 0 := by
  classical
  induction ys with
  | nil => simp
  | cons z ys ih =>
      rw [List.nodup_cons] at hys
      simp only [List.map_cons, List.sum_cons]
      rw [ih hys.2]
      by_cases hyz : y = z
      · subst z
        have heqb : eqb y y = true := by
          unfold eqb
          rw [if_pos rfl]
        have hhead : y ∈ y :: ys := List.mem_cons_self
        rw [if_pos heqb, if_neg hys.1, if_pos hhead]
        omega
      · have heqb : eqb y z = false := by
          unfold eqb
          rw [if_neg hyz]
        have hnot : ¬ eqb y z = true := by
          rw [heqb]
          decide
        rw [if_neg hnot]
        by_cases hy : y ∈ ys
        · have hcons : y ∈ z :: ys := List.mem_cons_of_mem z hy
          rw [if_pos hy, if_pos hcons]
          omega
        · have hcons : y ∉ z :: ys := by
            intro hm
            rcases List.mem_cons.mp hm with h | h
            · exact hyz h
            · exact hy h
          rw [if_neg hy, if_neg hcons]
          omega

theorem isumFiberProduct {b : Type} (ys : List b) (hys : ys.Nodup)
    (a b : b) (u v : Int) (ha : a ∈ ys) :
    (ys.map (fun y =>
      (if eqb a y then u else 0) *
        (if eqb b y then v else 0))).sum =
      if eqb a b then u * v else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    calc
      _ = (ys.map (fun y => if eqb a y then u * v else 0)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro y _
        by_cases hay : a = y <;> simp [eqb, hay]
      _ = u * v := by
        rw [isumEqFiber ys hys a (u * v)]
        rw [if_pos ha]
      _ = _ := by simp [eqb]
  · calc
      _ = (ys.map (fun _ => (0 : Int))).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro y _
        by_cases hay : a = y
        · have hby : b ≠ y := by
            intro h
            exact hab (hay.trans h.symm)
          simp [eqb, hay, hby]
        · simp [eqb, hay]
      _ = 0 := by simpa using (isumMapConst ys (0 : Int))
      _ = _ := by simp [eqb, hab]

theorem fiberPartitionSum {a b : Type} (xs : List a) (ys : List b)
    (out : a -> b) (w : a -> Int) (hys : ys.Nodup)
    (hout : ∀ x, x ∈ xs -> out x ∈ ys) :
    (ys.map (fun y =>
      ((xs.filter (fun x => eqb (out x) y)).map w).sum)).sum =
      (xs.map w).sum := by
  classical
  calc
    _ = (ys.map (fun y =>
        (xs.map (fun x => if eqb (out x) y then w x else 0)).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro y _
      exact isumFilter xs (fun x => eqb (out x) y) w
    _ = (xs.map (fun x =>
        (ys.map (fun y => if eqb (out x) y then w x else 0)).sum)).sum :=
      isumMapComm ys xs _
    _ = _ := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro x hx
      rw [isumEqFiber ys hys (out x) (w x)]
      rw [if_pos (hout x hx)]

theorem fiberPartitionSquare {a b : Type} (xs : List a) (ys : List b)
    (out : a -> b) (w : a -> Int) (hys : ys.Nodup)
    (hout : ∀ x, x ∈ xs -> out x ∈ ys) :
    (ys.map (fun y =>
      ((xs.filter (fun x => eqb (out x) y)).map w).sum *
        ((xs.filter (fun x => eqb (out x) y)).map w).sum)).sum =
      (xs.map (fun x => (xs.map (fun z =>
        if eqb (out x) (out z) then w x * w z else 0)).sum)).sum := by
  classical
  calc
    _ = (ys.map (fun y =>
        (xs.map (fun x => if eqb (out x) y then w x else 0)).sum *
          (xs.map (fun x => if eqb (out x) y then w x else 0)).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro y _
      simp only [isumFilter]
    _ = (ys.map (fun y => (xs.map (fun x =>
        (xs.map (fun z =>
          (if eqb (out x) y then w x else 0) *
            (if eqb (out z) y then w z else 0))).sum)).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro y _
      rw [isumMapMul]
    _ = (xs.map (fun x => (xs.map (fun z =>
        (ys.map (fun y =>
          (if eqb (out x) y then w x else 0) *
            (if eqb (out z) y then w z else 0))).sum)).sum)).sum := by
      calc
        _ = (xs.map (fun x => (ys.map (fun y =>
            (xs.map (fun z =>
              (if eqb (out x) y then w x else 0) *
                (if eqb (out z) y then w z else 0))).sum)).sum)).sum :=
          isumMapComm ys xs _
        _ = _ := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro x _
          exact isumMapComm ys xs _
    _ = _ := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro x hx
      apply congrArg List.sum
      apply List.map_congr_left
      intro z _
      exact isumFiberProduct ys hys (out x) (out z)
        (w x) (w z) (hout x hx)

end SealTasepGeometricDecayFiberList
end PPLLCompleteMultiLeaderCleanup

#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepGeometricDecayFiberList.fiberPartitionSum
#print axioms PPLLCompleteMultiLeaderCleanup.SealTasepGeometricDecayFiberList.fiberPartitionSquare
