import Leader.L4.BStarStageDescriptorHistory
import Leader.L4.BStarAcquireFrame
import Leader.L4.BStarArithmeticControllerReturn
import Leader.L4.BStarH6WordChart
import Leader.L4.AllSizeS1Geometry
import Leader.L4.BStarResetSchedule
import Leader.L4.BStarLongLandingCore

namespace L4.BStarStageSourceFrame
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongTransport BStarLongClaims BStarLongDoor

def Frame (p : Patch LW) : Prop :=
  ∀ i, 2155 ≤ i → i < 2195 → p.mask.getLsbD i=false

theorem zero : Frame (.empty LW) := by simp [Frame,Patch.empty]

theorem compose {p q : Patch LW} (hp : Frame p) (hq : Frame q) :
    Frame (p.compose q) := by
  intro i lo hi
  simp [Patch.compose,hp i lo hi,hq i lo hi]

theorem assign {n : Nat} (f : Field LW n) (b : BitVec n)
    (h : f.offset+n≤2155 ∨ 2195≤f.offset) : Frame (f.assign b) := by
  intro i lo hi
  apply Bool.eq_false_iff.mpr
  intro hm
  have := (Field.inMask f b i).mp hm
  rcases h with h|h <;> omega

theorem fuse_loop (l : List (Patch LW)) (p : Patch LW) (hp : Frame p)
    (h : ∀ q∈l, Frame q) : Frame (l.foldl Patch.compose p) := by
  induction l generalizing p with
  | nil => exact hp
  | cons a l ih =>
    exact ih _ (compose hp (h a List.mem_cons_self)) (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem fuse (l : List (Patch LW)) (h : ∀ q∈l, Frame q) :
    Frame (BStarLongOutgoing.fuse l) := fuse_loop l _ zero h

theorem number (j n : Nat) : Frame (BStarLongArithmetic.writeNum j n) := by
  apply assign
  left
  have h := BStarLongRegisters.range_bound BStarLongRegisters.wordWidths j
  rw [BStarLongRegisters.manifest_registers.2.1] at h
  exact Nat.le_trans h (by decide)

theorem scalar (j n : Nat) : Frame (BStarLongArithmetic.writeScalar j n) := by
  apply assign
  left
  have h := BStarLongRegisters.scalar_before_choice j
  exact Nat.le_trans h (by decide)

theorem numeric_visit (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) :
    Frame (BStarLongArithmetic.visit g j x p).1 := by
  unfold BStarLongArithmetic.visit
  split
  · exact zero
  split
  · exact zero
  split
  · exact zero
  rename_i idx _ c _
  cases c <;> simp only [BStarLongArithmetic.physicalDigit]
  all_goals first | exact zero | exact number _ _ | (split <;> first | exact zero | exact number _ _)

open BStarLongOutgoing BStarLongPublication in
theorem stage_frame (head inside : Bool) (x : BitVec LW) (d : Descriptor) (n : Nat) :
    Frame (stagePatch head inside x d n) := by
  have hd (b : Bool) (bank : Fin 3) :
      ∀ q∈dimDigits x b bank, Frame q := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    exact assign _ _ (.inr (by simp [bankDigit,bankPart,bankBase]; omega))
  have hh (b : Bool) (bank : Fin 3) :
      ∀ q∈dimHeaders n b bank, Frame q := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    exact assign _ _ (.inr (by simp [bankHeader,bankPart,bankBase]; omega))
  unfold stagePatch
  apply fuse
  intro q hq
  simp only [List.mem_append] at hq
  rcases hq with hi|he
  · cases inside <;> simp only [Bool.false_eq_true,if_false,List.not_mem_nil,
        if_true,List.mem_append] at hi
    exact hi.elim (hd false d.b0 q) (hd true d.b1 q)
  · cases head <;> simp only [Bool.false_eq_true,if_false,List.not_mem_nil,
        if_true,List.mem_append,List.mem_singleton] at he
    rcases he with (he|he)|rfl
    · exact hh false d.b0 q he
    · exact hh true d.b1 q he
    · exact assign _ _ (.inr (by decide))

open BStarLongOutgoing BStarLongPublication in
theorem execute_frame (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) :
    Frame (execute g j x p).row := by
  have dc : Frame descriptorClear :=
    compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide)))
  have sf (d : Descriptor) : Frame (sealField.assign (packOptional (some d))) :=
    assign _ _ (.inr (by decide))
  have setterF (b : Fin 3) : Frame (setter b) :=
    compose (compose (assign _ _ (.inr (by decide)))
      (assign _ _ (.inr (by decide)))) (assign _ _ (.inr (by decide)))
  have cf (head : Bool) (d : Descriptor) (b : Fin 3) :
      Frame (commit head j x d b).1 := by
    unfold commit
    split
    · exact setterF _
    · exact zero
  simp only [execute,hold,refuse]
  split
  · exact zero
  split
  · exact dc
  split
  · split
    · exact zero
    · split
      · exact zero
      · exact stage_frame _ _ _ _ _
  split
  · split
    · exact zero
    · split
      · exact sf _
      · exact zero
  split
  · split
    · exact zero
    · split
      · split
        · exact cf _ _ _
        · exact zero
      · exact zero
  · exact zero


theorem route_frame (w : KWrite) : Frame (lowerOne w).2 := by
  rcases w with ⟨⟨s,j⟩,t⟩
  change Frame (setToken j t)
  unfold setToken
  apply assign
  left
  change 1192+52*(10-j.val)+52≤2155
  omega

theorem packet_frame (w : At Sheet) (a : BStarLongPackets.Leaf) :
    Frame (BStarLongPackets.writeAt w a).patch.2 := by
  rw [BStarLongPackets.writeAt_patch]
  unfold BStarLongPackets.Leaf.assign
  apply assign
  left
  have := a.fits
  change 728+116*(3-(BStarLongPackets.Sheet.index w.occurrence).val)+a.offset+a.width ≤2155
  omega

private theorem grant_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) (w : Write LW) (hw : w∈(BStarLongGrant.run g x os).writes) :
    Frame w.patch.2 := by
  have one (s : Side) (h : w∈BStarLongGrant.siteWrites g x os s) : Frame w.patch.2 := by
    unfold BStarLongGrant.siteWrites at h
    obtain ⟨j,_,hh⟩ := List.mem_filterMap.mp h
    split at hh
    · injection hh with E
      subst w
      change Frame ((grant j).assign _)
      apply assign
      right
      change 2195≤2357+2-j.val
      have := j.isLt
      omega
    · contradiction
  exact (List.mem_append.mp hw).elim (one .left) (one .right)

theorem non_door_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (o : CmdOffer) (h : ∀ k, o.2≠.door k) :
    ∀ w∈(selected g x o).work, Frame w.2 := by
  obtain ⟨c,q⟩ := o
  cases q <;> simp only [selected]
  all_goals try (intro t ht; simp at ht; done)
  · exact (h _ rfl).elim
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · exact numeric_visit _ _ _ _
    · exact execute_frame _ _ _ _

/-- Normal observations, grant updates, packet data and all non-door
departures preserve the ACQUIRE file on a retained old source header.
The premise is only the exact remaining door departures on this endpoint. -/
theorem long_work_frame (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Bool)
    (hh : (lane s g).axes.h6=true)
    (door : ∀ o∈(BStarLongGrant.run g x (BStarLongCommandData.round g x).offered).departures,
      (∃ k, o.2=.door k) → ∀ w∈(selected g x o).work, w.1=s → Frame w.2) :
    Frame (lane s (longWork g x)) := by
  have fold (os : List CmdOffer) (acc : Selected)
      (ha : ∀ w∈acc.work, w.1=s → Frame w.2)
      (ho : ∀ o∈os, ∀ w∈(selected g x o).work, w.1=s → Frame w.2) :
      ∀ w∈(os.foldl (fun a o => Selected.append a (selected g x o)) acc).work,
        w.1=s → Frame w.2 := by
    induction os generalizing acc with
    | nil => exact ha
    | cons a os ih =>
      apply ih
      · intro w hw
        exact (List.mem_append.mp hw).elim (ha w) (ho a List.mem_cons_self w)
      · exact fun o h => ho o (List.mem_cons_of_mem _ h)
  intro i lo hi
  rw [exact_assignment_mask]
  apply Bool.eq_false_iff.mpr
  intro hany
  obtain ⟨w,hw,hm⟩ := List.any_eq_true.mp hany
  have hs := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hm).1
  have H : Frame w.2 := by
    simp only [longTrace,List.mem_append] at hw
    rcases hw with ((((hn|hc)|hg)|hp)|hd)|hr
    · obtain ⟨t,_,rfl⟩ := List.mem_map.mp hn
      exact route_frame t
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl <;> subst s <;> simp [lane] at hh <;> simp [nonheader,hh,zero]
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
      exact grant_frame g x _ t ht
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hp
      obtain ⟨⟨a,b⟩,_,rfl⟩ := List.mem_map.mp ht
      exact packet_frame a b
    · apply fold _ ⟨[],[],[]⟩ (by simp) _ w hd hs
      intro o ho w hw he
      by_cases hd : ∃ k, o.2=.door k
      · exact door o ho hd w hw he
      · exact non_door_frame g x o (fun k H => hd ⟨k,H⟩) w hw
    · obtain ⟨t,_,rfl⟩ := List.mem_map.mp hr
      exact route_frame t
  rw [H i lo hi] at hm
  simp at hm

theorem field_hold {n : Nat} (f : Field LW n) (q : Patch LW) (x : BitVec LW)
    (h : Frame q) (lo : 2155≤f.offset) (hi : f.offset+n≤2195) :
    f.read (q.apply x)=f.read x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  have hold := q.hold x (f.offset+i) (h _ (by omega) (by omega))
  simpa only [Field.read,BitVec.getLsbD_extractLsb',hi',decide_true,Bool.true_and] using hold


open BStarLongCommand BStarLongEvents BStarCommitIssue BStarH6WordChart

private def Keeps (t : Bool × Patch LW) : Prop := t.1=false ∨ Frame t.2

private theorem fold_field {n : Nat} (f : Field LW n) (lo : 2155≤f.offset)
    (hi : f.offset+n≤2195) (ws : List (Bool × Patch LW)) (x : Pair (BitVec LW))
    (h : ∀ t∈ws,Keeps t) : f.read (ws.foldl runWrite x).2=f.read x.2 := by
  induction ws generalizing x with
  | nil => rfl
  | cons t ts ih =>
    rw [List.foldl_cons,ih _ (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    rcases h t List.mem_cons_self with H|H
    · simp [runWrite,H]
    · obtain ⟨s,q⟩ := t
      cases s
      · rfl
      · exact field_hold _ _ _ H lo hi

private theorem copy_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (t : Bool × Patch LW) (h : t ∈ (BStarLongCommandData.round g x).writes.map Write.patch) :
    Keeps t := by
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp h
  obtain ⟨⟨a,b⟩,_,rfl⟩ := List.mem_map.mp hw
  exact .inr (packet_frame a b)

private theorem fold_work (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (a : Selected) :
    (os.foldl (fun acc o => acc.append (selected g x o)) a).work=
      a.work++os.flatMap (fun o => (selected g x o).work) := by
  induction os generalizing a with
  | nil => simp
  | cons h t ih =>
    simpa [Selected.append,List.append_assoc] using ih (a.append (selected g x h))

/-- Separate the literal selected door patch from all simultaneous
old-pair non-door writes, on either captured-field projection. -/
theorem door_field {n : Nat} (f : Field LW n) (lo : 2155≤f.offset)
    (hi : f.offset+n≤2195) (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (hh : g.2.axes.h6=true) (q : Patch LW)
    (he : (selected g x (doorClaim,.door (bind g.2 0 (atSite x.2 0)))).work=[(true,q)])
    (k : BitVec n → BitVec n)
    (H : ∀ y, f.read (q.apply y)=k (f.read y)) :
    f.read (patchPair (longWork g x) x).2=k (f.read x.2) := by
  let effect : List (Bool × Patch LW) := [(true,q)]
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
      exact .inr (non_door_frame g x o (NQ o ho) t ht)
    · obtain ⟨w,_,rfl⟩ := List.mem_map.mp h
      exact .inr (route_frame w)
  have B (t) (ht : t∈before) : Keeps t := by
    simp only [before,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with ((((h|(rfl|rfl))|h)|h)|h)
    · obtain ⟨w,_,rfl⟩ := List.mem_map.mp h
      exact .inr (route_frame w)
    · exact .inl rfl
    · exact .inr (by simp [nonheader,hh,Frame,Patch.empty])
    · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp h
      exact .inr (grant_frame g x d.offered w hw)
    · exact copy_frame g x t h
    · obtain ⟨o,ho,ht⟩ := List.mem_flatMap.mp h
      exact .inr (non_door_frame g x o (NP o ho) t ht)
  have X : (longTrace g x).assignments=before++effect++after := by
    change start.map lowerOne ++ [(false,nonheader g.1),(true,nonheader g.2)] ++
      u.writes.map Write.patch ++ d.writes.map Write.patch ++ sr.work ++ (sr.k++final).map lowerOne=_
    rw [W]
    simp only [before,after,List.append_assoc]
  rw [long_exec,X,List.foldl_append,fold_field f lo hi _ _ A,List.foldl_append]
  change f.read (q.apply (before.foldl runWrite x).2)=_
  rw [H,fold_field f lo hi _ _ B]



open BStarFinalCandidate BStarLongArithmetic


private theorem schedule_frames {n : Nat} (f : Field LW n)
    (lo : 1764≤f.offset) (hi : f.offset+n≤2195) (x : BitVec LW) :
    f.read ((schedule stageOp).apply x)=f.read x := by
  unfold schedule setToken
  simp only [Patch.compose_apply]
  rw [Field.read_other_assign f (kField 0) _ _ (.inr lo),
    Field.read_other_assign f ctrlOp _ _ (.inl hi),
    Field.read_other_assign f ctrlPhase _ _ (.inl (Nat.le_trans hi (by decide)))]

private theorem final_desc_over (old y : BitVec LW) (h : ((capturedSelector 1).read old).toNat<3) :
    sourceDescriptor.read ((finalEffect old h).apply y)=
      BStarLongPublication.encode (finalDesc old h) := by
  simp only [finalEffect,Patch.compose_apply]
  rw [schedule_frames sourceDescriptor (by decide) (by decide),
    Field.read_other_assign sourceDescriptor candidateHeaders _ _ (by decide),
    Field.read_other_assign sourceDescriptor need _ _ (by decide),Field.read_assign]

private theorem final_capture_over (old y : BitVec LW) (h : ((capturedSelector 1).read old).toNat<3) :
    (capturedSelector 1).read ((finalEffect old h).apply y)=(capturedSelector 1).read y := by
  simp only [finalEffect,Patch.compose_apply]
  rw [schedule_frames (capturedSelector 1) (by decide) (by decide),
    Field.read_other_assign (capturedSelector 1) candidateHeaders _ _ (by decide),
    Field.read_other_assign (capturedSelector 1) need _ _ (by decide),
    Field.read_other_assign (capturedSelector 1) sourceDescriptor _ _ (by decide)]
  apply field_hold _ _ _ _ (by decide) (by decide)
  apply fuse
  intro q H
  obtain ⟨⟨i,v⟩,_,rfl⟩ := List.mem_map.mp H
  exact scalar i v

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "A" => production k₁ k₂ t₂ J₁ J₂ r c p c₁

/-- Exact fully joined selected last arithmetic receipt. The
descriptor is freshly installed, the ACQUIRE center bits retained. -/
theorem joined_final_receipt (x : Pair (LargeSite A)) (f : Payload)
    (hdr : (oldHeaders B x.2).h6=true)
    (V : LongDoorGuard.valid manifest x.2.long=true)
    (ph : (ctrlPhase.read x.2.long).toNat=2)
    (op : (ctrlOp.read x.2.long).toNat=lastOp)
    (R : bind (longGeometry B x.2) 0 (atSite x.2.long 0)=.reply f)
    (F : f.fault=0) (O : f.opcode.toNat=lastOp)
    (h : ((capturedSelector 1).read x.2.long).toNat<3) :
    sourceDescriptor.read (largePair B x).2.long =
      BStarLongPublication.encode (finalDesc x.2.long h) ∧
    (capturedSelector 1).read (largePair B x).2.long =
      (capturedSelector 1).read x.2.long := by
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have RR : bind g.2 0 (atSite raw.2 0)=.reply f := R
  have S := BStarResetControllerEntry.wait_reply_selected g raw f hdr V ph R
  have E := S.2.2
  change (selected g raw (doorClaim,.door (.reply f))).work=[(true,_)] at E
  have N : (f.fault != 0 || f.opcode.toNat != (ctrlOp.read raw.2).toNat)=false := by
    change (f.fault != 0 || f.opcode.toNat != (ctrlOp.read x.2.long).toNat)=false
    simp [F,O,op]
  have ar : (arithKind (ctrlOp.read raw.2).toNat).isSome=true := by
    change (arithKind (ctrlOp.read x.2.long).toNat).isSome=true
    rw [op]
    decide
  have hh : ((capturedSelector 1).read raw.2).toNat<3 := h
  have E' : (selected g raw (doorClaim,.door (bind g.2 0 (atSite raw.2 0)))).work=
      [(true,finalEffect raw.2 hh)] := by
    rw [if_neg (show ¬(f.fault != 0 || f.opcode.toNat != (ctrlOp.read raw.2).toNat)=true from fun k => by rw [N] at k; cases k),if_pos ar] at E
    rw [RR,E,show (ctrlOp.read raw.2).toNat=lastOp from op,final_receipt_exact raw.2 f hh]
  have project {m : Nat} (field : Field LW m) (hi : field.offset+m≤2195) :
      field.read (largePair B x).2.long=field.read (patchPair (longWork g raw) raw).2 := by
    change field.read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
      ((longWork g raw).2.compose (longScratch g raw).2)).apply raw.2)=_
    have VV : LongDoorGuard.valid manifest raw.2=true := V
    simp only [LongDoorGuard.guard,VV,Bool.not_true,Bool.and_false,Bool.false_eq_true,if_false,
      Patch.compose_apply]
    exact Field.read_other_assign field offField _ _ (.inl (Nat.le_trans hi (by decide)))
  constructor
  · rw [project sourceDescriptor (by decide)]
    change sourceDescriptor.read (patchPair (longWork g raw) raw).2 = BStarLongPublication.encode (finalDesc raw.2 hh)
    exact door_field sourceDescriptor (by decide) (by decide) g raw hdr (finalEffect raw.2 hh) E'
      (fun _ => BStarLongPublication.encode (finalDesc raw.2 hh)) (fun y => final_desc_over raw.2 y hh)
  · rw [project (capturedSelector 1) (by decide)]
    change (capturedSelector 1).read (patchPair (longWork g raw) raw).2 = (capturedSelector 1).read raw.2
    exact door_field (capturedSelector 1) (by decide) (by decide) g raw hdr (finalEffect raw.2 hh) E' id
      (fun y => final_capture_over raw.2 y hh)


/-- On an outgoing mark of the source header its left long endpoint
may route arbitrary foreign work but cannot accept a source door. -/
theorem left_foreign_field (x : Pair (LargeSite A))
    (hdr : (oldHeaders B x.1).h6=true)
    {m : Nat} (field : Field LW m) (lo : 2155≤field.offset) (hi : field.offset+m≤2195) :
    field.read (largePair B x).1.long=field.read x.1.long := by
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have H := long_work_frame g raw false hdr (by
    rintro ⟨C,t⟩ O ⟨k,rfl⟩ w hw left
    have R := BStarLongLandingCore.actual_door_right g raw C k O
    simp only [selected,R] at hw
    split at hw
    · simp at hw
    · have e := congrArg Prod.fst (List.mem_singleton.mp hw)
      exact (Bool.noConfusion (left.symm.trans e))
    · have e := congrArg Prod.fst (List.mem_singleton.mp hw)
      exact (Bool.noConfusion (left.symm.trans e)))
  change field.read (((longWork g raw).1.compose (longScratch g raw).1).apply raw.1)=field.read raw.1
  simp only [longScratch,Patch.compose_apply]
  rw [Field.read_other_assign field seField _ _ (.inl (Nat.le_trans hi (by decide))),
    Field.read_other_assign field shField _ _ (.inl (Nat.le_trans hi (by decide)))]
  exact field_hold _ _ _ H lo hi

/-- Concrete selected mark not entering this source preserves its
seven descriptor bits and its captured center selector. -/
theorem foreign_mark (x : Fin n → LargeSite A) (i e : Fin n)
    (ex : rightNeighbor e≠i)
    (hdr : oldH6 B x i=true) :
    let y := AllSizeS1Geometry.step B x e
    sourceDescriptor.read (y i).long=sourceDescriptor.read (x i).long ∧
      (capturedSelector 1).read (y i).long=(capturedSelector 1).read (x i).long := by
  dsimp only
  by_cases E : i=e
  · subst i
    simp only [AllSizeS1Geometry.step,if_true]
    let pair := (x e,x (rightNeighbor e))
    have H : (oldHeaders B pair.1).h6=true := hdr
    exact ⟨left_foreign_field hp pair H sourceDescriptor (by decide) (by decide),
      left_foreign_field hp pair H (capturedSelector 1) (by decide) (by decide)⟩
  · simp only [AllSizeS1Geometry.step,if_neg E,if_neg (Ne.symm ex),and_self]


/-- Arbitrarily many interleaved marks, none acting at the source door.
The source must still be an old H6 at each actual mark (e.g. fixed Layout). -/
theorem foreign_word (x : Fin n → LargeSite A) (i : Fin n) (w : List (Fin n))
    (foreign : ∀ e∈w, rightNeighbor e≠i)
    (header : ∀ u e v, w=u++e::v →
      oldH6 B (BStarResetSchedule.run (AllSizeS1Geometry.step B) x u) i=true) :
    let y := BStarResetSchedule.run (AllSizeS1Geometry.step B) x w
    sourceDescriptor.read (y i).long=sourceDescriptor.read (x i).long ∧
      (capturedSelector 1).read (y i).long=(capturedSelector 1).read (x i).long := by
  induction w generalizing x with
  | nil => exact ⟨rfl,rfl⟩
  | cons e w ih =>
    have S := foreign_mark hp x i e (foreign e List.mem_cons_self) (header [] e w rfl)
    have T := ih (AllSizeS1Geometry.step B x e)
      (fun f H => foreign f (List.mem_cons_of_mem _ H))
      (fun a f b E => header (e::a) f b (congrArg (List.cons e) E))
    exact ⟨T.1.trans S.1,T.2.trans S.2⟩

#print axioms joined_final_receipt
#print axioms foreign_word
end L4.BStarStageSourceFrame
