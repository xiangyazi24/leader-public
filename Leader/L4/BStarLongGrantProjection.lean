import Leader.L4.BStarLongGrantFrame
import Leader.L4.BStarGrantRetention

/-! Exact grants in the output of the concrete long producer. -/
namespace L4.BStarLongGrantProjection
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongClaims
open BStarLongWork BStarLongCommand BStarLongTransport BStarLongGrant

def read (x : Pair (BitVec LW)) (s : Side) (j : Fin 3) : BitVec 1 :=
  (grant j).read (BStarLongGrant.atOld x s)

def grants (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (o : Offers) (s : Side) (j : Fin 3) : Bool :=
  (geometry g s).axes.h6 && result (original (BStarLongGrant.atOld x s))
    (fun k => requested o s k releaseOp) (fun k => requested o s k acquire) j

def writesAt (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (o : Offers) (s : Side) (j : Fin 3) : Bool :=
  support (geometry g s).axes.h6 (original (BStarLongGrant.atOld x s))
    (fun k => requested o s k releaseOp) (fun k => requested o s k acquire) j

theorem grant_bounds (j : Fin 3) : 2357≤(grant j).offset ∧ (grant j).offset<2360 := by
  simp only [grant]
  have := j.isLt
  omega

theorem fold_frames (ls : List (Bool × Patch LW)) (x : Pair (BitVec LW))
    (s : Side) (j : Fin 3) (h : ∀ t∈ls, BStarLongGrantFrame.Frame t.2) :
    read (ls.foldl runWrite x) s j=read x s j := by
  induction ls generalizing x with
  | nil => rfl
  | cons t ls ih =>
    rw [List.foldl_cons,ih _ (fun u hu => h u (List.mem_cons_of_mem _ hu))]
    obtain ⟨b,q⟩ := t
    have F (raw : BitVec LW) : (grant j).read (q.apply raw)=(grant j).read raw := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have I : i=0 := by omega
      subst i
      simpa [Field.read] using Patch.hold q raw _ (h _ List.mem_cons_self _
        (grant_bounds j).1 (grant_bounds j).2)
    cases b <;> cases s <;> simp [read,BStarLongGrant.atOld,lane,runWrite,F]

def target (g : Pair LongGeometry) (x : Pair (BitVec LW)) (o : Offers)
    (s : Side) (j : Fin 3) : Write LW :=
  ⟨right s,1,grant j,BitVec.ofBool (grants g x o s j)⟩

theorem target_mem (g : Pair LongGeometry) (x : Pair (BitVec LW)) (o : Offers)
    (s : Side) (j : Fin 3) (h : writesAt g x o s j=true) :
    target g x o s j ∈ (BStarLongGrant.run g x o).writes := by
  have Q : target g x o s j ∈ siteWrites g x o s := by
    apply List.mem_filterMap.mpr
    exact ⟨j,List.mem_finRange j,by simp [target,grants,show support (geometry g s).axes.h6 (original (BStarLongGrant.atOld x s)) (fun k => requested o s k releaseOp) (fun k => requested o s k acquire) j=true from h]⟩
  cases s <;> simp [BStarLongGrant.run,Q]

theorem grant_fold (g : Pair LongGeometry) (x y : Pair (BitVec LW)) (o : Offers)
    (s : Side) (j : Fin 3) :
    read (((BStarLongGrant.run g x o).writes.map Write.patch).foldl runWrite y) s j =
      if writesAt g x o s j then BitVec.ofBool (grants g x o s j) else read y s j := by
  classical
  let T := target g x o s j
  have step (t : Write LW) (h : t∈(BStarLongGrant.run g x o).writes) (z : Pair (BitVec LW)) :
      read (runWrite z t.patch) s j =
        if t=T then BitVec.ofBool (grants g x o s j) else read z s j := by
    have E : ∃ r k, writesAt g x o r k=true ∧ t=target g x o r k := by
      have A : ∀ r, t∈siteWrites g x o r → ∃ k, writesAt g x o r k=true ∧ t=target g x o r k := by
        intro r ht
        obtain ⟨k,_,hk⟩ := List.mem_filterMap.mp ht
        change (if writesAt g x o r k then some (target g x o r k) else none)=some t at hk
        split at hk
        · rename_i H
          exact ⟨k,H,(Option.some.inj hk).symm⟩
        · contradiction
      rcases List.mem_append.mp h with h|h
      · exact ⟨.left,A .left h⟩
      · exact ⟨.right,A .right h⟩
    obtain ⟨r,k,_,rfl⟩ := E
    by_cases he : r=s
    · subst r
      by_cases hk : k=j
      · subst k
        simp only [T]
        cases s <;> simp [read,BStarLongGrant.atOld,lane,runWrite,target,right,Write.patch,Field.read_assign]
      · have D : Disjoint (grant j) (grant k) := by
          have K : k.val≠j.val := fun e => hk (Fin.ext e)
          simp only [Disjoint,grant]
          have := k.isLt
          have := j.isLt
          omega
        have K : target g x o s k≠T := by
          intro E
          have D := congrArg (fun w : Write LW => w.field.offset) E
          change 2359-k.val=2359-j.val at D
          exact hk (Fin.ext (by have := k.isLt; have := j.isLt; omega))
        rw [if_neg K]
        cases s <;> simp [read,BStarLongGrant.atOld,lane,runWrite,target,right,Write.patch,
          Field.read_other_assign _ _ _ _ D]
    · have H : target g x o r k≠T := by
        intro E
        have D := congrArg Write.right E
        cases r <;> cases s <;> simp_all [target,T,right]
      rw [if_neg H]
      cases r <;> cases s <;> simp_all [read,BStarLongGrant.atOld,lane,runWrite,target,right,Write.patch]
  have fold (L : List (Write LW)) (H : ∀ t∈L, t∈(BStarLongGrant.run g x o).writes) (z : Pair (BitVec LW)) :
      read ((L.map Write.patch).foldl runWrite z) s j =
        if T∈L then BitVec.ofBool (grants g x o s j) else read z s j := by
    induction L generalizing z with
    | nil => simp
    | cons a L ih =>
      rw [List.map_cons,List.foldl_cons,ih (fun t ht => H t (List.mem_cons_of_mem _ ht)),
        step a (H a List.mem_cons_self)]
      by_cases A : T∈L
      · simp [A]
      · simp [A,eq_comm]
  rw [fold _ (fun _ h => h)]
  by_cases H : writesAt g x o s j=true
  · simp [H,target_mem g x o s j H,T]
  · have HN : T∉(BStarLongGrant.run g x o).writes := by
      intro HT
      have Q : (lane (right s) (BStarLongGrant.run g x o).patch).mask.getLsbD (grant j).offset=true := by
        apply (Trace.mask_iff (⟨(BStarLongGrant.run g x o).writes,[]⟩ : Trace LW Unit) _ _).mpr
        exact ⟨T,HT,rfl,Nat.le_refl _,Nat.lt_succ_self _⟩
      obtain ⟨k,hk,hk'⟩ := (patch_grant_support g x o s _).mp Q
      have E : k=j := by
        change 2359-k.val=2359-j.val at hk'
        exact Fin.ext (by have := k.isLt; have := j.isLt; omega)
      subst k
      exact H hk
    simp [HN,H]

theorem canonical_clean (old : Ports) (h : conflict old=false) (j : Fin 3) :
    canonical old j=old j := by
  cases W : old 1
  · simp [canonical,W]
  · have E : old 0=false ∧ old 2=false := by simpa [conflict,W] using h
    have V : j.val=0 ∨ j.val=1 ∨ j.val=2 := by have := j.isLt; omega
    rcases V with V|V|V
    · have H : j=0 := Fin.ext V
      simp [H,canonical,W,E]
    · have H : j=1 := Fin.ext V
      simp [H,canonical,W]
    · have H : j=2 := Fin.ext V
      simp [H,canonical,W,E]

theorem no_write_means_old (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (o : Offers) (s : Side) (j : Fin 3) (H : writesAt g x o s j=false) :
    BitVec.ofBool (grants g x o s j)=read x s j := by
  let old := original (BStarLongGrant.atOld x s)
  let rel := fun k => requested o s k releaseOp
  let ask := fun k => requested o s k acquire
  let hd := (geometry g s).axes.h6
  change support hd old rel ask j=false at H
  have ⟨hh,hc,hr,hw⟩ :
      hd=true ∧ conflict old=false ∧ rel j=false ∧ win old rel ask j=false := by
    simpa [support,Bool.or_assoc] using H
  change BitVec.ofBool (hd && result old rel ask j)=read x s j
  simp only [hh,Bool.true_and,result,hr,Bool.not_false,hw,Bool.and_true,Bool.or_false,
    canonical_clean old hc]
  change BitVec.ofBool ((read x s j).getLsbD 0)=read x s j
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have K : k=0 := by omega
  subst k
  simp

/-- Exact grant value on arbitrary old bytes and geometry, no assumed
canonical grant or absence of concurrent offers. The requests are from the
actual old-pair cancellation-resolved command stage, before Grant.run. -/
theorem actual_grants (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (s : Side) (j : Fin 3) :
    read (patchPair (longWork g x) x) s j =
      BitVec.ofBool (grants g x (BStarLongCommandData.round g x).offered s j) := by
  rw [long_exec]
  let d := BStarLongCommandData.round g x
  let u := BStarLongGrant.run g x d.offered
  let row : Selected := u.departures.foldl
    (fun acc o => Selected.append acc (selected g x o)) ⟨[],[],[]⟩
  let first := normalization g (readK x)
  let last := observations g (readK x) (first++row.k)
  let pre := first.map lowerOne ++ [(false,nonheader g.1),(true,nonheader g.2)]
  let post := d.writes.map Write.patch ++ row.work ++ (row.k++last).map lowerOne
  have preF : ∀ t∈pre, BStarLongGrantFrame.Frame t.2 := by
    intro t ht
    simp only [pre,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with ht|(rfl|rfl)
    · obtain ⟨w,_,rfl⟩ := List.mem_map.mp ht
      exact BStarLongGrantFrame.route_frame w
    · exact BStarLongGrantFrame.clear_frame _
    · exact BStarLongGrantFrame.clear_frame _
  have postF : ∀ t∈post, BStarLongGrantFrame.Frame t.2 := by
    intro t ht
    rcases List.mem_append.mp ht with h|h
    · rcases List.mem_append.mp h with h|h
      · exact BStarLongGrantFrame.copy_frame _ _ _ t h
      · exact BStarLongGrantFrame.selected_fold_frame g x _ _ (by simp) t h
    · obtain ⟨w,_,rfl⟩ := List.mem_map.mp h
      exact BStarLongGrantFrame.route_frame w
  have E : (longTrace g x).assignments = (pre++u.writes.map Write.patch)++post := by
    simp only [longTrace,first,last,pre,post,row,u,d,List.append_assoc]
  rw [E,List.foldl_append,fold_frames post _ _ _ postF,List.foldl_append,grant_fold]
  rw [fold_frames pre _ _ _ preF]
  cases H : writesAt g x d.offered s j
  · rw [no_write_means_old g x d.offered s j H]
    rfl
  · rfl

theorem actual_keeps_incidence (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (s : Side) (j : Fin 3)
    (hh : (geometry g s).axes.h6=true)
    (hold : canonical (original (BStarLongGrant.atOld x s)) j=true)
    (nr : requested (BStarLongCommandData.round g x).offered s j releaseOp=false) :
    read (patchPair (longWork g x) x) s j=1 := by
  rw [actual_grants]
  simp [grants,hh,BStarGrantRetention.keep_canonical _ _ _ j hold,nr]

theorem joined_grants (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (s : Side) (j : Fin 3) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    read (Pair.map LargeSite.long (largePair b x)) s j =
      BitVec.ofBool (grants g raw (BStarLongCommandData.round g raw).offered s j) := by
  dsimp only
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let work := longWork g raw
  let scratch := longScratch g raw
  let q := (work.1.compose scratch.1,work.2.compose scratch.2)
  change read (patchPair (LongDoorGuard.pairGuard manifest g raw q) raw) s j = _
  have B := grant_bounds j
  have F : ∀ z : BitVec LW, (grant j).read ((LongDoorGuard.repair manifest).apply z) =
      (grant j).read z := by
    intro z
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have I : i=0 := by omega
    subst i
    simp only [Field.read,BitVec.getLsbD_extractLsb',Nat.zero_lt_succ,decide_true,
      Bool.true_and,Nat.add_zero]
    apply LongDoorGuard.repair_holds_outside
    · right
      exact Nat.le_trans (by decide) B.1
    · right
      exact Nat.le_trans (by decide) B.1
  have S (y : Pair (BitVec LW)) :
      read (patchPair scratch y) s j=read y s j := by
    unfold read
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have I : i=0 := by omega
    subst i
    simp only [Field.read,BitVec.getLsbD_extractLsb',Nat.zero_lt_succ,decide_true,
      Bool.true_and,Nat.add_zero]
    obtain ⟨L,R⟩ := longScratch_mask g raw (grant j).offset
    have A : scratch.1.mask.getLsbD (grant j).offset=false :=
      Bool.eq_false_iff.mpr fun h => by rcases L.mp h with H|H <;> omega
    have C : scratch.2.mask.getLsbD (grant j).offset=false :=
      Bool.eq_false_iff.mpr fun h => by have := (R.mp h).1; omega
    cases s
    · exact Patch.hold _ _ _ A
    · exact Patch.hold _ _ _ C
  have E : read (patchPair (LongDoorGuard.pairGuard manifest g raw q) raw) s j =
      read (patchPair scratch (patchPair work raw)) s j := by
    cases s
    · simp [read,BStarLongGrant.atOld,lane,patchPair,LongDoorGuard.pairGuard,q,Patch.compose_apply]
    · change (grant j).read
        ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2 q.2).apply raw.2) =
          (grant j).read (scratch.2.apply (work.2.apply raw.2))
      unfold LongDoorGuard.guard
      split
      · rw [Patch.compose_apply,F]
        exact congrArg ((grant j).read) (Patch.compose_apply _ _ _)
      · exact congrArg ((grant j).read) (Patch.compose_apply _ _ _)

  rw [E,S]
  exact actual_grants g raw s j

theorem joined_keeps_incidence (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (s : Side) (j : Fin 3) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (geometry g s).axes.h6=true →
    canonical (original (BStarLongGrant.atOld raw s)) j=true →
    requested (BStarLongCommandData.round g raw).offered s j releaseOp=false →
    read (Pair.map LargeSite.long (largePair b x)) s j=1 := by
  dsimp only
  intro hh hc hn
  rw [joined_grants]
  simp [grants,hh,BStarGrantRetention.keep_canonical _ _ _ j hc,hn]

#print axioms grant_fold
#print axioms actual_grants
#print axioms actual_keeps_incidence
#print axioms joined_grants
#print axioms joined_keeps_incidence
end L4.BStarLongGrantProjection
