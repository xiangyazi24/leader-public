import Leader.L4.BStarAcquireJoinedIssue

/-! Exact source-control projection of the selected old right door.
A literal hold preserves control even if other endpoints route tokens. -/
namespace L4.BStarAcquireWaitControl
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongClaims
open BStarLongTransport BStarLongCommand BStarLongDoor BStarLongWork BStarLongEvents
open BStarCommitIssue BStarAcquireSource

def control (x : BitVec LW) := (ctrlPhase.read x,ctrlOp.read x)

private def Frame (q : Patch LW) : Prop :=
  ∀ i, 2195≤i → i<2206 → q.mask.getLsbD i=false
private def Keeps (t : Bool × Patch LW) : Prop := t.1=false ∨ Frame t.2

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
    (h : ∀ t∈ws,Keeps t) : control (ws.foldl runWrite x).2=control x.2 := by
  induction ws generalizing x with
  | nil => rfl
  | cons t ts ih =>
    rw [List.foldl_cons,ih _ (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    rcases h t List.mem_cons_self with H|H
    · simp [runWrite,H]
    · obtain ⟨s,q⟩ := t
      cases s
      · rfl
      · exact control_frame _ _ H

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
    (o : CmdOffer) (h : ∀ t : Token,o.2≠.door t) :
    ∀ w∈(selected g x o).work,Keeps w := by
  rcases o with ⟨c,a⟩
  cases a <;> simp only [selected]
  all_goals try (intro _ E; exact (List.not_mem_nil E).elim)
  · exact (h _ rfl).elim
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

theorem door_projection (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (hh : g.2.axes.h6=true) (effect : List (Bool × Patch LW))
    (he : (selected g x (doorClaim,.door (bind g.2 0 (atSite x.2 0)))).work=effect)
    (f : (BitVec 2 × BitVec 9) → (BitVec 2 × BitVec 9))
    (H : ∀ y, control (effect.foldl runWrite y).2=f (control y.2)) :
    control (patchPair (longWork g x) x).2=f (control x.2) := by
  let d := BStarLongCommandData.round g x
  let u := BStarLongGrant.run g x d.offered
  let O := actualOffers g x
  let door : CmdOffer := (doorClaim,.door (bind g.2 0 (atSite x.2 0)))
  obtain ⟨pre,post,E,NP,NQ⟩ := BStarDoorUnique.actual_door_split g x hh
  change O=pre++door::post at E
  change (selected g x door).work=effect at he
  let sr : Selected := O.foldl (fun acc o => acc.append (selected g x o)) ⟨[],[],[]⟩
  have W : sr.work=pre.flatMap (fun o => (selected g x o).work) ++
      effect ++ post.flatMap (fun o => (selected g x o).work) := by
    have Q := fold_work g x O ⟨[],[],[]⟩
    change sr.work=[]++O.flatMap _ at Q
    simpa [E,he,List.append_assoc] using Q
  let start := normalization g (readK x)
  let final := observations g (readK x) (start++sr.k)
  let before := start.map lowerOne ++ [(false,nonheader g.1),(true,nonheader g.2)] ++
    u.writes.map Write.patch ++ d.writes.map Write.patch ++ pre.flatMap (fun o => (selected g x o).work)
  let after := post.flatMap (fun o => (selected g x o).work) ++ (sr.k++final).map lowerOne
  have A (t) (ht : t∈after) : Keeps t := by
    rcases List.mem_append.mp ht with h|h
    · obtain ⟨o,ho,ht⟩ := List.mem_flatMap.mp h
      exact work_frame g x o (NQ o ho) t ht
    · obtain ⟨w,_,rfl⟩ := List.mem_map.mp h
      exact routing_frame w
  have B (t) (ht : t∈before) : Keeps t := by
    simp only [before,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with ((((h|(rfl|rfl))|h)|h)|h)
    · obtain ⟨w,_,rfl⟩ := List.mem_map.mp h
      exact routing_frame w
    · exact .inl rfl
    · exact .inr (by simp [nonheader,hh,Frame,Patch.empty])
    · exact grant_frame g x d.offered t h
    · exact copy_frame g x t h
    · obtain ⟨o,ho,ht⟩ := List.mem_flatMap.mp h
      exact work_frame g x o (NP o ho) t ht
  have X : (longTrace g x).assignments=before++effect++after := by
    change start.map lowerOne ++ [(false,nonheader g.1),(true,nonheader g.2)] ++
      u.writes.map Write.patch ++ d.writes.map Write.patch ++ sr.work ++ (sr.k++final).map lowerOne=_
    rw [W]
    simp only [before,after,List.append_assoc]
  rw [long_exec,X,List.foldl_append,fold_frame _ _ A,List.foldl_append,H,fold_frame _ _ B]

theorem joined_control (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (valid : LongDoorGuard.valid manifest x.2.long=true) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    control (largePair b x).2.long=control (patchPair (longWork g raw) raw).2 := by
  dsimp only
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g raw
  let q := longScratch g raw
  change control ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2 (w.2.compose q.2)).apply raw.2)=_
  have V : LongDoorGuard.valid manifest raw.2=true := valid
  simp only [LongDoorGuard.guard,V,Bool.not_true,Bool.and_false,Bool.false_eq_true,if_false,
    Patch.compose_apply]
  exact control_frame _ _ (prior_frame BStarTrace.offField _ (.inr (by decide)))

private theorem valid_from (x : BitVec LW) (p : (ctrlPhase.read x).toNat=1 ∨ (ctrlPhase.read x).toNat=2)
    (o : (ctrlOp.read x).toNat=acquire) : LongDoorGuard.valid manifest x=true := by
  change ((((ctrlPhase.read x).toNat==1) || ((ctrlPhase.read x).toNat==2)) &&
    decide ((ctrlOp.read x).toNat<manifest.opcodes))=true
  rcases p with e|e <;> simp [e,o] <;> decide

theorem joined_acquire_entry (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (oldHeaders b x.2).h6=true →
    (ctrlPhase.read x.2.long).toNat=1 →
    (ctrlOp.read x.2.long).toNat=acquire →
    atSite (largePair b x).2.long 0=.forward initPayload ∧
      control (largePair b x).2.long=(2,ctrlOp.read x.2.long) := by
  dsimp only
  intro hh ph op
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  refine ⟨(BStarAcquireJoinedIssue.joined_issue k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x hh ph op).1,?_⟩
  rw [joined_control k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x (valid_from _ (.inl ph) op)]
  apply door_projection g raw hh [(true,issued acquire (2^33))] (f:=fun C => (2,C.2))
  · have H : oldDoor raw.2 (bind g.2 0 (atSite raw.2 0))=.write (issued acquire (2^33)) :=
      acquire_issue raw.2 _ ph op
    simp [selected,doorClaim,atOld,R,lane,H]
  · intro y
    change control ((issued acquire (2^33)).apply y.2)=(2,ctrlOp.read y.2)
    simp only [issued,acquire,show (5==1)=false by decide,Bool.false_eq_true,if_false,
      Patch.compose_apply]
    unfold setToken
    rw [control_frame _ _ (prior_frame (kField 0) _ (.inl (by decide)))]
    unfold control
    rw [Field.read_assign, Field.read_other_assign _ _ _ _ (.inl (by decide))]

/-- Actual old WAIT with a literal HOLD keeps both source control fields.
Receipt, fault restart and a right nonheader are intentionally excluded. -/
theorem joined_wait_hold (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := longGeometry b x.2
    (oldHeaders b x.2).h6=true →
    (ctrlPhase.read x.2.long).toNat=2 →
    (ctrlOp.read x.2.long).toNat=acquire →
    oldDoor x.2.long (bind g 0 (atSite x.2.long 0))=.hold →
    control (largePair b x).2.long=control x.2.long := by
  dsimp only
  intro hh ph op hold
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  rw [joined_control k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x (valid_from _ (.inr ph) op)]
  apply door_projection g raw hh [] (f:=id)
  · have H : oldDoor raw.2 (bind g.2 0 (atSite raw.2 0))=.hold := hold
    change (match oldDoor raw.2 (bind g.2 0 (atSite raw.2 0)) with
      | .hold => (⟨[],[],[]⟩ : Selected)
      | .write q => ⟨[],[(true,q)],[]⟩
      | .acceptTour op p => ⟨[],[(true,BStarLongArithmetic.acceptFile raw.2 op p)],[]⟩).work=[]
    rw [H]
  · intro y
    rfl

theorem old_wait_hold_iff (x : BitVec LW) (tok : Token)
    (ph : (ctrlPhase.read x).toNat=2) (op : (ctrlOp.read x).toNat=acquire) :
    oldDoor x tok=.hold ↔ tok=.trail ∨ ∃ p, tok=.forward p := by
  have V := valid_from x (.inr ph) op
  cases tok with
  | trail => simp [wait_holds_trail _ V ph]
  | forward p => simp [wait_holds_forward _ _ V ph]
  | empty => simp [wait_empty_repairs _ V ph]
  | reply p =>
    simp only [oldDoor,V,Bool.not_true,Bool.false_eq_true,if_false,ph,show (2==1)=false by decide]
    split
    · simp
    · split <;> simp

#print axioms joined_acquire_entry
#print axioms joined_wait_hold
end L4.BStarAcquireWaitControl
