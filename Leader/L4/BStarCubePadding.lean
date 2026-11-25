import Leader.L4.BStarWarmupQuarter

namespace L4.BStarCubePadding
open BStarWarmupQuarter Classical

/-- Extra coordinates do not change a quarter bound for a predicate
that depends only on an injective projection of the uniform cube. -/
theorem lift_quarter {M K : Nat} (f : Fin M→Fin K) (inj : Function.Injective f)
    (bad : List (Bits M)) (q : 4*bad.length≤2^M) :
    ∃ padded : List (Bits K),padded.Nodup ∧
      (∀ a,a∈padded ↔ (fun j=>a (f j))∈bad) ∧ 4*padded.length≤2^K := by
  let used := (List.finRange M).map f
  let extra := (List.finRange K).filter fun i=>decide (i∉used)
  let D := extra.length
  have usedLen : used.length=M := by simp [used]
  have U (i : Fin K) : i∈used ↔ ∃ j,f j=i := by simp [used]
  have X (i : Fin K) : i∈extra ↔ i∉used := by simp [extra]
  have full (i : Fin K) : i∈used++extra := by
    by_cases H : i∈used
    · exact List.mem_append_left _ H
    · exact List.mem_append_right _ ((X i).mpr H)
  have nd : (used++extra).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨?_,(List.nodup_finRange K).filter _,?_⟩
    · change ((List.finRange M).map f).Nodup
      rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
      exact (List.nodup_finRange M).imp (fun ne eq=>ne (inj eq))
    · intro i A j E eq
      subst j
      exact (X i).mp E A
  have len := Nat.le_antisymm (nd.length_le_of_subset (fun x _=>List.mem_finRange x))
    ((List.nodup_finRange K).length_le_of_subset (fun x _=>full x))
  have cardinal : M+D=K := by simpa only [List.length_append,usedLen,List.length_finRange] using len
  let paste : Bits M→Bits D→Bits K := fun a b i =>
    if H : ∃ j,f j=i then a (Classical.choose H)
    else b ⟨extra.idxOf i,List.idxOf_lt_length_iff.mpr ((X i).mpr (fun u=>H ((U i).mp u)))⟩
  have pasted (a : Bits K) :
      paste (fun j=>a (f j)) (fun j=>a extra[j.val])=a := by
    funext i
    unfold paste
    split
    next H => exact congrArg a (Classical.choose_spec H)
    next H =>
      apply congrArg a
      exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr ((X i).mpr (fun u=>H ((U i).mp u))))
  let padded := (allBits K).filter (fun a=>decide ((fun j=>a (f j))∈bad))
  have mem (a : Bits K) : a∈padded ↔ (fun j=>a (f j))∈bad := by
    simp [padded,mem_allBits]
  let big := bad.flatMap (fun a=>(allBits D).map (paste a))
  have sub : padded⊆big := by
    intro a A
    exact List.mem_flatMap.mpr ⟨_,(mem a).mp A,
      List.mem_map.mpr ⟨(fun j=>a extra[j.val]),mem_allBits _ _,pasted a⟩⟩
  have nodup : padded.Nodup := (allBits_nodup K).filter _
  have lenAny (xs : List (Bits M)) :
      (xs.flatMap (fun a=>(allBits D).map (paste a))).length=xs.length*2^D := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_map,allBits_length,
        List.length_cons,ih,Nat.add_mul,Nat.one_mul,Nat.add_comm]
  have lenBig : big.length=bad.length*2^D := lenAny bad
  refine ⟨padded,nodup,mem,?_⟩
  calc
    4*padded.length ≤ 4*big.length := Nat.mul_le_mul_left _ (nodup.length_le_of_subset sub)
    _ = (4*bad.length)*2^D := by rw [lenBig,Nat.mul_assoc]
    _ ≤ 2^M*2^D := Nat.mul_le_mul_right _ q
    _ = 2^K := by rw [←Nat.pow_add,cardinal]

#print axioms lift_quarter
end L4.BStarCubePadding
