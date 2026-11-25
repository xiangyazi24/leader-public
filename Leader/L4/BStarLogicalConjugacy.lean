import Leader.L4.BStarCycleGeometry
import Leader.L4.BStarWarmupEventQuarter
import Leader.L4.Height.Core

namespace L4.BStarLogicalConjugacy
open BStarH6WordChart BStarAcquireAnchors BStarNativePortGeometry
open BStarCycleGeometry BStarWarmupReceiptChoice BStarWarmupArrival
open BStarFirstArrival L4.Compiler.Native L4.Height

variable {n : Nat} {h : Fin n→Bool}

/-- Physical H6 predecessor is exactly the accepted finite logical
predecessor. This includes rings with one or two headers. -/
theorem atIndex_left (hh : ∃ i,h i=true) (j : Fin (total h)) :
    atIndex hh (left (total_pos h hh) j)=neighborHeader hh (atIndex hh j) 0 := by
  have hm:=total_pos h hh
  have N (j : Fin (total h)) : next j=right hm j := rfl
  have L : ∀ j : Fin (total h),left hm (right hm j)=j := by
    intro j
    apply Fin.ext
    by_cases small : j.val+1<total h
    · simp only [left,right,Nat.mod_eq_of_lt small]
      rw [show j.val+1+total h-1=j.val+total h by omega,Nat.add_mod]
      simp [Nat.mod_eq_of_lt j.isLt]
    · have eq : j.val+1=total h := by omega
      simp only [left,right,eq,Nat.mod_self,Nat.zero_add]
      rw [Nat.mod_eq_of_lt (show total h-1<total h by omega)]
      omega
  apply index_injective hh
  rw [index_atIndex]
  have T := next_index_left hh (atIndex hh j)
  rw [index_atIndex,N] at T
  exact (congrArg (left hm) T).symm.trans (L _)

theorem atIndex_right (hh : ∃ i,h i=true) (j : Fin (total h)) :
    atIndex hh (right (total_pos h hh) j)=neighborHeader hh (atIndex hh j) 2 :=
  atIndex_next hh j

theorem atIndex_center (hh : ∃ i,h i=true) (j : Fin (total h)) :
    atIndex hh j=neighborHeader hh (atIndex hh j) 1 := (BStarNativeNeedLift.self_port hh _).symm

theorem physical_injective (hh : ∃ i,h i=true) :
    Function.Injective (fun j : Fin (total h) => (atIndex hh j).val) := by
  intro j k E
  have K : atIndex hh j=atIndex hh k := Subtype.ext E
  exact (index_atIndex hh j).symm.trans ((congrArg (index hh) K).trans (index_atIndex hh k))

/-- Transport one literal completed-cube phase along the canonical
cyclic index. No callback or hypothesized neighbor alignment. -/
theorem cube_phase (hh : ∃ i,h i=true)
    (r : Nat) (reserve : BStarWarmupKeys.Key n→Option Bool) (lo opening cap : Nat)
    (assign : Fin (BStarWarmupKeys.joint reserve lo opening cap).length→Bool)
    (level : Nat) (s : Header h→Snapshot) :
    (fun j : Fin (total h) => cubeUpdate r reserve lo opening cap assign level
      (atIndex hh j) (s (atIndex hh j))
      (fun q=>s (neighborHeader hh (atIndex hh j) q))) =
    phaseStep (heightMod r) (level%32) (total_pos h hh)
      (fun j=>cubeBit reserve lo opening cap assign (atIndex hh j).val level)
      (fun j=>s (atIndex hh j)) := by
  funext j
  unfold cubeUpdate phaseStep
  dsimp only
  rw [atIndex_left,atIndex_right]

/-- The entire level recurrence of the completed cube transports to
the accepted finite logical phase table, on the same H6 ring. -/
theorem cube_levels (hh : ∃ i,h i=true)
    (r : Nat) (reserve : BStarWarmupKeys.Key n→Option Bool) (lo opening cap : Nat)
    (assign : Fin (BStarWarmupKeys.joint reserve lo opening cap).length→Bool)
    (s : Header h→Snapshot) (k : Nat) :
    let U : Update (Fin (total h)) Snapshot (Fin 3) :=
      fun level i own port=>phaseUpdate (heightMod r) (level%32)
        (port 0) own (port 2) (cubeBit reserve lo opening cap assign (atIndex hh i).val level)
    let neighbor : Fin (total h)→Fin 3→Fin (total h) := fun i q =>
      if q=0 then left (total_pos h hh) i else if q=2 then right (total_pos h hh) i else i
    (fun j : Fin (total h) => levels (neighborHeader hh) (cubeUpdate r reserve lo opening cap assign)
      opening s k (atIndex hh j)) =
      levels neighbor U opening (fun j=>s (atIndex hh j)) k := by
  dsimp only
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    simp only [levels]
    have E := congrFun (cube_phase hh r reserve lo opening cap assign (opening+k)
      (levels (neighborHeader hh) (cubeUpdate r reserve lo opening cap assign) opening s k)) i
    rw [E]
    unfold phaseStep
    simp only [if_pos,show (2:Fin 3)≠0 by decide,ite_false]
    rw [congrFun ih i,congrFun ih (left (total_pos h hh) i),congrFun ih (right (total_pos h hh) i)]

end L4.BStarLogicalConjugacy
