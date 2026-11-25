import Leader.L4.BStarCopyLeftFence
import Leader.L4.BStarCopyRightFence

namespace L4.BStarNativeCopyReadback
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongPackets
open BStarCopyFenceSaturation BStarCopyLeftPending BStarCopyRightMixed
open BStarCopyLeftFence BStarCopyRightFence
open BStarCopyRightStrip (addr)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

private theorem lane_lookup (F : Nat→Lane) (i count j : Nat) (J : j<count) :
    (laneRead F i count)[j]?=some (F (i+j)).retained := by
  induction count generalizing i j with
  | zero => omega
  | succ count ih =>
    cases j with
    | zero => simp [laneRead]
    | succ j =>
      simp only [laneRead,List.getElem?_cons_succ]
      rw [ih (i+1) j (by omega)]
      rw [show i+1+j=i+(j+1) by omega]

private theorem right_plan (seam last : Nat) (sz : last+1=seam+r) :
    planOf (fun k=>k-seam) seam last=List.range r := by
  unfold planOf
  rw [show last+1-seam=r by omega]
  apply List.ext_getElem?
  intro j
  by_cases hj : j<r
  · simp [hj]
  · simp [hj]

theorem both_at_digit (x : X) (root : Fin n) (seam last : Nat)
    (left right : Nat→BitVec 36) (size : last+1=seam+r)
    (L : laneRead (ldRead x root) 0 r=(pending id r).reverse.map (Digit9.data ∘ left))
    (R : laneRead (rdRead x root r) 0 r=
      (planOf (fun i=>i-seam) seam last).reverse.map (Digit9.data ∘ right))
    (j : Fin r) :
    (readLane 1 (x (addr root j.val)).long).retained=.data (left j.val) ∧
    (readLane 3 (x (addr root j.val)).long).retained=.data (right j.val) := by
  have E : (pending id r).reverse=List.range r := by simp [pending]
  have p := congrArg (fun l : List Digit9=>l[j.val]?) L
  rw [lane_lookup _ _ _ _ j.isLt,E] at p
  have B : ((List.range r).map (Digit9.data ∘ left))[j.val]?=some (.data (left j.val)) := by
    simp [j.isLt]
  have LL := Option.some.inj (p.trans B)
  let i := r-1-j.val
  have hi : i<r := by dsimp [i]; have := j.isLt; omega
  have Q := congrArg (fun l : List Digit9=>l[i]?) R
  rw [lane_lookup _ _ _ _ hi,right_plan seam last size] at Q
  have rdIndex : r-1-(0+i)=j.val := by dsimp only [i]; have := j.isLt; omega
  have RQ : ((List.range r).reverse.map (Digit9.data ∘ right))[i]?=some (.data (right j.val)) := by
    rw [List.getElem?_map,List.getElem?_eq_getElem (by simpa using hi),List.getElem_reverse]
    simp only [List.length_range]
    have eq : r-1-i=j.val := by omega
    simp [List.getElem_range,eq]
  have RR := Option.some.inj (Q.trans RQ)
  constructor
  · simpa only [ldRead,Nat.zero_add,Sheet.index] using LL
  · simpa only [rdRead,rdIndex,Sheet.index] using RR

#print axioms both_at_digit
end L4.BStarNativeCopyReadback
