import Leader.L4.BStarLogicalMainQuarter
import Leader.L4.BStarBoundedOpening

namespace L4.BStarDisplayPermanence
open BStarAcquireAnchors BStarH6WordChart BStarNativePortGeometry BStarCycleGeometry
open BStarLogicalConjugacy BStarAlignedLogicalRounds BStarFirstArrival
open BStarWarmupArrival BStarWarmupReceiptChoice BStarWarmupEventQuarter BStarBoundedOpening
open BStarStaggeredArrival
open L4.Height L4.Compiler.Native

/-- Only phase zero rewrites the current anchor flag. -/
theorem phase_keeps_display (B p : Nat) (l c r : Snapshot) (bit : Bool) (nonzero : p≠0) :
    (phaseUpdate B p l c r bit).anchor=c.anchor := by
  unfold phaseUpdate
  split
  all_goals first | contradiction | rfl

/-- For every positive level after a successful aligned logical slice,
the display flag is that slice's one anchor, for arbitrary choices.
At level zero the old flag is deliberately not constrained. -/
theorem logical_display {m B M cap : Nat} (hm : 0<m) (hB : m<B)
    (period : 32∣M/2) (aligned : cap%32=0)
    (choice : Nat→Fin m→Bool) (seed : Fin m→Snapshot) (bounded : Bounded B seed)
    (leader : Fin m) (one : ∀ j,IsAnchor hm seed j↔j=leader) :
    ∀ k,0<k → ∀ j,(syncLevels B M cap hm choice seed k j).anchor=decide (j=leader) := by
  have phase (k : Nat) : clockOf M (cap+k)%32=k%32 := clockOf_mod_phase period aligned
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
    intro _ j
    rw [syncLevels,phase]
    by_cases phaseZero : k%32=0
    · rw [phaseZero]
      let q := k/32
      have K : k=32*q := by
        have E := Nat.mod_add_div k 32
        rw [phaseZero,Nat.zero_add] at E
        exact E.symm
      have S := syncLevels_runRounds (B:=B) (M:=M) (ellzero:=cap) (k:=q) hm choice seed phase
      have same := single_anchor_runRounds B hm hB (roundBits choice cap q) seed leader bounded one j
      change decide (IsAnchor hm (syncLevels B M cap hm choice seed k) j)=decide (j=leader)
      rw [K,S]
      by_cases eq : j=leader
      · rw [decide_eq_true ((same).2 eq),decide_eq_true eq]
      · rw [decide_eq_false (fun a=>eq ((same).1 a)),decide_eq_false eq]
    · unfold phaseStep
      rw [phase_keeps_display _ _ _ _ _ _ phaseZero]
      apply ih
      by_cases Z : k=0
      · exact (phaseZero (by rw [Z])).elim
      · exact Nat.pos_of_ne_zero Z

variable {n : Nat} {h : Fin n→Bool}

theorem cube_sync_from (hh : ∃ i,h i=true)
    (r M : Nat) (reserve : BStarWarmupKeys.Key n→Option Bool) (lo opening hi cap : Nat)
    (assign : Fin (BStarWarmupKeys.joint reserve lo opening hi).length→Bool)
    (phase : ∀ k,clockOf M (cap+k)%32=(cap+k)%32)
    (seed : Header h→Snapshot) (k : Nat) :
    (fun j=>evolve (neighborHeader hh) (cubeUpdate r reserve lo opening hi assign)
      cap seed k (atIndex hh j)) =
    syncLevels (heightMod r) M cap (total_pos h hh)
      (choices hh reserve lo opening hi assign) (fun j=>seed (atIndex hh j)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [syncLevels,phase]
    simp only [evolve,levels]
    rw [cube_phase,ih]
    rfl

/-- If the stored current lift has crossed the first publication from
cap to cap+1, it displays the unique anchor of the cap snapshot. This
also covers arbitrary later lifts in the certified finite replay. -/
theorem trace_display_after_cap {T : Nat}
    (R : Trace (Header h) Snapshot (Fin 3) T)
    (hh : ∃ i,h i=true) (r M : Nat) (period : 32∣M/2)
    (reserve : BStarWarmupKeys.Key n→Option Bool) (lo opening hi cap : Nat)
    (aligned : cap%32=0) (height : total h<heightMod r)
    (assign : Fin (BStarWarmupKeys.joint reserve lo opening hi).length→Bool)
    (neighbors : R.neighbor=neighborHeader hh)
    (W : FollowsBelow R hi (cubeUpdate r reserve lo opening hi assign))
    (initial : ∀ i,R.level 0 i≤cap)
    (s : Header h→Snapshot)
    (view : ∀ i,∃ u,FirstAt R i cap u ∧ s i=R.curr u i)
    (bounded : Bounded (heightMod r) (fun j=>s (atIndex hh j)))
    (leader : Fin (total h))
    (one : ∀ j,IsAnchor (total_pos h hh) (fun j=>s (atIndex hh j)) j↔j=leader)
    (t : Nat) (ht : t≤T) (j : Fin (total h))
    (crossed : cap<R.level t (atIndex hh j)) (below : R.level t (atIndex hh j)≤hi) :
    (R.curr t (atIndex hh j)).anchor=decide (j=leader) := by
  let U := cubeUpdate r (h:=h) reserve lo opening hi assign
  let k := R.level t (atIndex hh j)-cap
  have Hcap : cap≤hi := by omega
  have C : fromTrace R U cap=s := by
    funext i
    obtain ⟨u,F,V⟩ := view i
    have a := (represents R hi U W u F.1 i).1 (by rw [F.2.1]; exact Hcap)
    rw [F.2.1] at a
    exact (V.trans a).symm
  have lev : R.level t (atIndex hh j)=cap+k := by
    unfold k
    omega
  have curr := (represents R hi U W t ht (atIndex hh j)).1 below
  rw [lev] at curr
  have restart := oracle_restarts R U cap initial k
  rw [C,neighbors] at restart
  rw [curr,congrFun restart (atIndex hh j)]
  have mod (q : Nat) : (cap+q)%32=q%32 := by
    rw [Nat.add_mod,aligned]
    simp
  have phase (q : Nat) : clockOf M (cap+q)%32=(cap+q)%32 :=
    (clockOf_mod_phase period aligned).trans (mod q).symm
  rw [congrFun (cube_sync_from hh r M reserve lo opening hi cap assign phase s k) j]
  apply logical_display (total_pos h hh) height period aligned _ _ bounded leader one
  unfold k
  omega

end L4.BStarDisplayPermanence
