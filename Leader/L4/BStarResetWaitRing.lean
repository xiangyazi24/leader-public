import Leader.L4.BStarResetTaggedRows
import Leader.L4.BStarAcquireWaitControl
import Leader.L4.BStarLongLandingCore

namespace L4.BStarResetWaitRing
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongCommand BStarLongDoor BStarLongWork BStarLongEvents
open BStarCommitIssue BStarAcquireWaitControl BStarResetTaggedRows

private def Frame (q : Patch LW) : Prop :=
  ∀ i, 2195≤i → i<2206 → q.mask.getLsbD i=false
private def Keeps (t : Bool × Patch LW) : Prop := t.1=true ∨ Frame t.2

private theorem prior_frame {n : Nat} (f : Field LW n) (v : BitVec n)
    (h : f.offset+n≤2195 ∨ 2206≤f.offset) : Frame (f.assign v) := by
  intro i lo hi
  apply Bool.eq_false_iff.mpr
  intro H
  obtain ⟨L,U⟩ := (Field.inMask f v i).mp H
  rcases h with h|h <;> omega

private theorem weaken {q : Patch LW} (h : BStarAcquireJoinedIssue.Frame q) : Frame q :=
  fun i L U => h i (.inr ⟨L,U⟩)

private theorem read_frame {n : Nat} (f : Field LW n) (q : Patch LW) (x : BitVec LW)
    (L : 2195≤f.offset) (U : f.offset+n≤2206) (H : Frame q) :
    f.read (q.apply x)=f.read x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simpa only [Field.read,BitVec.getLsbD_extractLsb',hk,decide_true,Bool.true_and] using
    Patch.hold q x (f.offset+k) (H _ (by omega) (by omega))

private theorem control_frame (q : Patch LW) (x : BitVec LW) (H : Frame q) :
    control (q.apply x)=control x :=
  Prod.ext (read_frame ctrlPhase q x (by decide) (by decide) H)
    (read_frame ctrlOp q x (by decide) (by decide) H)

private theorem fold_frame (ws : List (Bool × Patch LW)) (x : Pair (BitVec LW))
    (h : ∀ t∈ws,Keeps t) : control (ws.foldl runWrite x).1=control x.1 := by
  induction ws generalizing x with
  | nil => rfl
  | cons t ts ih =>
    rw [List.foldl_cons,ih _ (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    rcases h t List.mem_cons_self with H|H
    · simp [runWrite,H]
    · obtain ⟨s,q⟩ := t
      cases s
      · exact control_frame _ _ H
      · rfl

private theorem routing_frame (w : KWrite) : Keeps (lowerOne w) := by
  rcases w with ⟨⟨s,j⟩,t⟩
  apply Or.inr
  change Frame ((kField j).assign _)
  apply prior_frame _ _ (.inl ?_)
  change 1192+52*(10-j.val)+52≤2195
  omega

private theorem grant_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) :
    ∀ t∈(BStarLongGrant.run g x os).writes.map Write.patch,Keeps t := by
  have F (s : Side) (t) (ht : t∈BStarLongGrant.siteWrites g x os s) : Keeps t.patch := by
    obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp ht
    split at hj
    · cases hj
      apply Or.inr
      apply prior_frame _ _ (.inr ?_)
      change 2206≤2359-j.val
      have := j.isLt
      omega
    · contradiction
  intro t ht
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ht
  exact (List.mem_append.mp hw).elim (F .left w) (F .right w)

private theorem copy_frame (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    ∀ t∈(BStarLongCommandData.round g x).writes.map Write.patch,Keeps t := by
  intro t ht
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ht
  obtain ⟨⟨a,u⟩,_,rfl⟩ := List.mem_map.mp hw
  apply Or.inr
  rw [BStarLongPackets.writeAt_patch]
  unfold BStarLongPackets.Leaf.assign
  apply prior_frame _ _ (.inl ?_)
  have := u.fits
  change 728+116*(3-(BStarLongPackets.Sheet.index a.occurrence).val)+u.offset+u.width≤2195
  omega

private theorem work_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (o : CmdOffer) (h : o∈actualOffers g x) :
    ∀ w∈(selected g x o).work,Keeps w := by
  rcases o with ⟨c,a⟩
  cases a <;> simp only [selected]
  all_goals try (intro _ E; exact (List.not_mem_nil E).elim)
  · rename_i t
    have H := BStarLongLandingCore.actual_door_right g x c t h
    split <;> intro w hw
    · exact (List.not_mem_nil hw).elim
    · obtain rfl := List.mem_singleton.mp hw
      exact .inl (by simp [H])
    · obtain rfl := List.mem_singleton.mp hw
      exact .inl (by simp [H])
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · exact .inr (weaken (BStarAcquireJoinedIssue.numeric_visit _ _ _ _))
    · exact .inr (weaken (BStarAcquireJoinedIssue.execute_frame _ _ _ _))

private theorem fold_work (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (a : Selected) :
    (os.foldl (fun acc o => acc.append (selected g x o)) a).work=
      a.work++os.flatMap (fun o => (selected g x o).work) := by
  induction os generalizing a with
  | nil => simp
  | cons h t ih =>
    simpa [Selected.append,List.append_assoc] using ih (a.append (selected g x h))


theorem work_left (g : Pair LongGeometry) (x : Pair (BitVec LW)) (hh : g.1.axes.h6=true) :
    control (patchPair (longWork g x) x).1=control x.1 := by
  let d := BStarLongCommandData.round g x
  let u := BStarLongGrant.run g x d.offered
  let O := actualOffers g x
  let sr : Selected := O.foldl (fun acc o => acc.append (selected g x o)) ⟨[],[],[]⟩
  let start := normalization g (readK x)
  let final := observations g (readK x) (start++sr.k)
  have W : sr.work=O.flatMap (fun o => (selected g x o).work) := by
    simpa [sr] using fold_work g x O ⟨[],[],[]⟩
  rw [long_exec]
  change control ((start.map lowerOne ++ [(false,nonheader g.1),(true,nonheader g.2)] ++
    u.writes.map Write.patch ++ d.writes.map Write.patch ++ sr.work ++ (sr.k++final).map lowerOne).foldl runWrite x).1=_
  rw [W]
  apply fold_frame
  intro t ht
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with (((((h|(rfl|rfl))|h)|h)|h)|h)
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp h
    exact routing_frame a
  · exact .inr (by simp [nonheader,hh,Frame,Patch.empty])
  · exact .inl rfl
  · exact grant_frame g x d.offered t h
  · exact copy_frame g x t h
  · obtain ⟨o,ho,ht⟩ := List.mem_flatMap.mp h
    exact work_frame g x o ho t ht
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp h
    exact routing_frame a

theorem joined_left (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (oldHeaders b x.1).h6=true →
    control (largePair b x).1.long=control x.1.long := by
  dsimp only
  intro hh
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g raw
  let q := longScratch g raw
  change control ((w.1.compose q.1).apply raw.1)=_
  rw [Patch.compose_apply]
  change control (((shField.assign (BitVec.ofBool g.2.axes.h6)).compose
    (seField.assign (BitVec.ofBool (g.2.inside && g.2.last)))).apply (w.1.apply raw.1))=_
  rw [Patch.compose_apply,
    control_frame _ _ (prior_frame seField _ (.inr (by decide))),
    control_frame _ _ (prior_frame shField _ (.inr (by decide)))]
  exact work_left g raw hh

theorem joined_right (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (oldHeaders b x.2).h6=true →
    LongDoorGuard.valid manifest x.2.long=true →
    (ctrlPhase.read x.2.long).toNat=2 →
    (atSite x.2.long 0=.trail ∨ ∃ v, atSite x.2.long 0=.forward v ∧ ResetF v) →
    control (largePair b x).2.long=control x.2.long := by
  dsimp only
  intro hh valid ph front
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  exact (joined_control k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x valid).trans
    (door_projection g raw hh [] (f:=id) (by
      have E : oldDoor raw.2 (bind g.2 0 (atSite raw.2 0))=.hold := by
        rcases front with T|⟨v,F,hv⟩
        · rw [show atSite raw.2 0=.trail from T]
          exact wait_holds_trail _ valid ph
        · rw [show atSite raw.2 0=.forward v from F,bind_reset _ _ _ hv]
          exact wait_holds_forward _ _ valid ph
      change (match oldDoor raw.2 (bind g.2 0 (atSite raw.2 0)) with
      | .hold => (⟨[],[],[]⟩ : Selected)
      | .write q => ⟨[],[(true,q)],[]⟩
      | .acceptTour op p => ⟨[],[(true,BStarLongArithmetic.acceptFile raw.2 op p)],[]⟩).work=[]
      rw [E]) (fun _ => rfl))

/-- Every physical mark retains both owner control fields while the old
owner has valid WAIT and an outward front or trail at K0. The outgoing
mark may change K0 itself; this theorem only freezes controller bytes. -/
theorem step_control (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    {n : Nat} (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e i : Fin n) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (oldHeaders b (x i)).h6=true →
    LongDoorGuard.valid manifest (x i).long=true →
    (ctrlPhase.read (x i).long).toNat=2 →
    (atSite (x i).long 0=.trail ∨ ∃ v, atSite (x i).long 0=.forward v ∧ ResetF v) →
    control (AllSizeS1Geometry.step b x e i).long=control (x i).long := by
  dsimp only
  intro hh v ph front
  by_cases E : i=e
  · subst i
    simpa only [AllSizeS1Geometry.step,if_true] using
      joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) hh
  · by_cases J : i=rightNeighbor e
    · subst i
      simpa only [AllSizeS1Geometry.step,if_neg E,if_true] using
        joined_right k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) hh v ph front
    · simp only [AllSizeS1Geometry.step,if_neg E,if_neg J]

theorem valid_of_control_eq (x y : BitVec LW) (h : control x=control y) :
    LongDoorGuard.valid manifest x=LongDoorGuard.valid manifest y := by
  have p := congrArg Prod.fst h
  have o := congrArg Prod.snd h
  change ctrlPhase.read x=ctrlPhase.read y at p
  change ctrlOp.read x=ctrlOp.read y at o
  change ((((ctrlPhase.read x).toNat==1) || ((ctrlPhase.read x).toNat==2)) &&
    decide ((ctrlOp.read x).toNat<manifest.opcodes)) =
    ((((ctrlPhase.read y).toNat==1) || ((ctrlPhase.read y).toNat==2)) &&
    decide ((ctrlOp.read y).toNat<manifest.opcodes))
  rw [p,o]

#print axioms step_control
end L4.BStarResetWaitRing
