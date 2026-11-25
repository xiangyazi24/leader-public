import Leader.L4.Height.SyncRound
import Leader.L4.BStarLogicalConjugacy
import Leader.L4.BStarMainLogicalProjection

namespace L4.BStarAlignedLogicalRounds
open BStarH6WordChart BStarAcquireAnchors BStarNativePortGeometry BStarCycleGeometry
open BStarLogicalConjugacy BStarFirstArrival BStarWarmupArrival BStarWarmupReceiptChoice
open BStarWarmupEventQuarter BStarWarmupKeys BStarMainLogicalProjection
open L4.Compiler.Native L4.Height

variable {n : Nat} {h : Fin n→Bool}

noncomputable def choices (hh : ∃ i,h i=true)
    (reserve : Key n→Option Bool) (lo opening cap : Nat)
    (assign : Fin (joint reserve lo opening cap).length→Bool) :
    Nat→Fin (total h)→Bool :=
  fun level i=>cubeBit reserve lo opening cap assign (atIndex hh i).val level

theorem cube_syncLevels (hh : ∃ i,h i=true)
    (r M : Nat) (reserve : Key n→Option Bool) (lo opening cap : Nat)
    (assign : Fin (joint reserve lo opening cap).length→Bool)
    (phase : ∀ k,clockOf M (opening+k)%32=(opening+k)%32)
    (seed : Header h→Snapshot) (k : Nat) :
    (fun j=>evolve (neighborHeader hh) (cubeUpdate r reserve lo opening cap assign)
      opening seed k (atIndex hh j)) =
    syncLevels (heightMod r) M opening (total_pos h hh)
      (choices hh reserve lo opening cap assign) (fun j=>seed (atIndex hh j)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [syncLevels,phase]
    simp only [evolve,levels]
    rw [cube_phase,ih]
    rfl

/-- The actual finite H6 cube recurrence over 32Q levels is exactly
the accepted logical run from its opening slice with the same phase-one
bits. No physical reach hypothesis is needed for this identity. -/
theorem aligned_rounds (hh : ∃ i,h i=true)
    (r M : Nat) (period : 32∣M/2)
    (reserve : Key n→Option Bool) (lo opening cap : Nat) (A : opening%32=0)
    (assign : Fin (joint reserve lo opening cap).length→Bool)
    (seed : Header h→Snapshot) (Q : Nat) :
    (fun j=>evolve (neighborHeader hh) (cubeUpdate r reserve lo opening cap assign)
      opening seed (32*Q) (atIndex hh j)) =
    runRounds (heightMod r) (total_pos h hh)
      (roundBits (choices hh reserve lo opening cap assign) opening Q)
      (fun j=>seed (atIndex hh j)) := by
  have mod (k : Nat) : (opening+k)%32=k%32 := by
    rw [Nat.add_mod,A]
    simp
  have H (k : Nat) : clockOf M (opening+k)%32=k%32 := clockOf_mod_phase period A
  rw [cube_syncLevels hh r M reserve lo opening cap assign (fun k=>(H k).trans (mod k).symm)]
  exact syncLevels_runRounds (total_pos h hh) _ _ H

/-- The exact identified coordinate supplies the literal cube value. -/
theorem choice_at_index (reserve : Key n→Option Bool) (lo opening cap : Nat)
    (a : BStarWarmupQuarter.Bits (jointSize reserve lo opening cap))
    (k : Key n) (j : Fin (jointSize reserve lo opening cap))
    (E : sumCoordinate reserve lo opening cap k=some j) :
    cubeBit reserve lo opening cap (joinList reserve lo opening cap a) k.1 k.2=a j := by
  have W := (sum_fiber reserve lo opening cap j k).mp E
  unfold sumKey at W
  let t := j.cast (joint_length reserve lo opening cap).symm
  have C : complete reserve lo opening cap (joinList reserve lo opening cap a) k=
      some (joinList reserve lo opening cap a t) := W.symm ▸ complete_index _ _ _ _ _ t
  unfold cubeBit
  have K : (k.1,k.2)=k := Prod.eta _
  rw [K,C]
  change a (t.cast (joint_length reserve lo opening cap))=a j
  congr 1

def roundIndex {Q m : Nat} (j : Fin Q) (i : Fin m) : Fin (Q*m) :=
  ⟨j.val*m+i.val,by
    have C := Nat.mul_le_mul_right m (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at C
    omega⟩

theorem roundIndex_key (hh : ∃ i,h i=true) (op : Nat)
    {Q : Nat} (j : Fin Q) (i : Fin (total h)) :
    logicalKey (total_pos h hh) (fun x=>(atIndex hh x).val) op (roundIndex j i) =
      ((atIndex hh i).val,op+32*j.val+1) := by
  have hm:=total_pos h hh
  apply Prod.ext
  · change (atIndex hh ⟨(j.val*total h+i.val)%total h,_⟩).val=(atIndex hh i).val
    apply congrArg (fun x : Fin (total h)=>(atIndex hh x).val)
    apply Fin.ext
    change (j.val*total h+i.val)%total h=i.val
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt i.isLt]
  · change op+32*((j.val*total h+i.val)/total h)+1=op+32*j.val+1
    rw [Nat.add_comm (j.val*total h) i.val,Nat.add_mul_div_right _ _ hm,Nat.div_eq_of_lt i.isLt,Nat.zero_add]

theorem roundBits_ofFn {m : Nat} (c : Nat→Fin m→Bool) (op Q : Nat) :
    roundBits c op Q=List.ofFn (fun j : Fin Q=>c (op+32*j.val+1)) := by
  induction Q with
  | zero => rfl
  | succ Q ih =>
    rw [roundBits_succ,ih]
    exact (List.ofFn_succ_last (f:=fun j : Fin (Q+1)=>c (op+32*j.val+1))).symm

/-- For any assignment of both cubes, the actual logical round bits
are those selected by the exact main-key embedding, in the same
round-major order as the accepted flattening convention. -/
theorem choices_from_main (hh : ∃ i,h i=true)
    (reserve : Key n→Option Bool) (lo opening cap Q : Nat)
    (a : BStarWarmupQuarter.Bits (jointSize reserve lo opening cap))
    (f : Fin (Q*total h)→Fin (keys reserve opening cap).length)
    (key : ∀ j, sumCoordinate reserve lo opening cap
      (logicalKey (total_pos h hh) (fun i=>(atIndex hh i).val) opening j) =
      some ((f j).natAdd (keys reserve lo opening).length)) :
    roundBits (choices hh reserve lo opening cap (joinList reserve lo opening cap a)) opening Q =
      List.ofFn (fun j : Fin Q => fun i : Fin (total h) =>
        BStarWarmupQuarter.main a (f (roundIndex j i))) := by
  rw [roundBits_ofFn]
  congr 1
  funext j i
  have E := key (roundIndex j i)
  rw [roundIndex_key hh opening] at E
  exact choice_at_index reserve lo opening cap a _ _ E

end L4.BStarAlignedLogicalRounds
