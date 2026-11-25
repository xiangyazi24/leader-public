import Leader.L4.BStarClearanceOffset

/-! Literal long-work assignments frame the effective offset interval; offset refresh is a separate scratch assignment. -/
namespace L4.BStarClearanceOffsetMask
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongTransport BStarLongClaims

def Frame (p : Patch LW) : Prop :=
  ∀ i, 2364 ≤ i → i < 2367 → p.mask.getLsbD i=false

theorem zero : Frame (.empty LW) := by simp [Frame,Patch.empty]

theorem compose {p q : Patch LW} (hp : Frame p) (hq : Frame q) :
    Frame (p.compose q) := by
  intro i lo hi
  simp [Patch.compose,hp i lo hi,hq i lo hi]

theorem assign {n : Nat} (f : Field LW n) (b : BitVec n)
    (h : f.offset+n≤2364 ∨ 2367≤f.offset) : Frame (f.assign b) := by
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

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem schedule_frame (op : Nat) : Frame (schedule op) := by
  unfold schedule
  apply compose (compose (assign _ _ (.inl (by decide))) (assign _ _ (.inl (by decide))))
  exact assign _ _ (.inl (by decide))

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem repair_frame : Frame faultRestart := by
  unfold faultRestart LongDoorGuard.repair
  apply compose (compose (assign _ _ (.inl (by decide))) (assign _ _ (.inl (by decide))))
  exact compose (assign _ _ (.inl (by decide))) (assign _ _ (.inl (by decide)))

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem issue_frame (op n : Nat) : Frame (issued op n) := by
  have h : Frame ((ctrlPhase.assign 2).compose (setToken 0 (forward op n))) :=
    compose (assign _ _ (.inl (by decide))) (assign _ _ (.inl (by decide)))
  unfold issued
  split
  · exact compose (assign _ _ (.inl (by decide))) h
  · exact h

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem reply_frame (op : Nat) (p : Payload) (x : BitVec LW) :
    Frame (afterReply op p x) := by
  have ca (a : BitVec 6) : Frame (captures.assign a) := assign _ _ (.inl (by decide))
  have ch (a : BitVec 27) : Frame (capturedHeaders.assign a) := assign _ _ (.inl (by decide))
  have sh (a : BitVec 18) : Frame (candidateHeaders.assign a) := assign _ _ (.inl (by decide))
  have sd (a : BitVec 7) : Frame (sourceDescriptor.assign a) := assign _ _ (.inl (by decide))
  have co (a : BitVec 2) : Frame (choice.assign a) := assign _ _ (.inl (by decide))
  have nd (a : BitVec 1) : Frame (need.assign a) := assign _ _ (.inl (by decide))
  have de (a : BitVec 1) : Frame (delta.assign a) := assign _ _ (.inl (by decide))
  have fl (a : BitVec 369) : Frame (scalarFile.assign a) := assign _ _ (.inl (by decide))
  unfold afterReply
  dsimp only
  repeat first
    | split
    | with_reducible exact repair_frame
    | with_reducible exact schedule_frame _
    | with_reducible apply compose
    | with_reducible exact ca _
    | with_reducible exact ch _
    | with_reducible exact sh _
    | with_reducible exact sd _
    | with_reducible exact co _
    | with_reducible exact nd _
    | with_reducible exact de _
    | with_reducible exact fl _

set_option maxHeartbeats 1200000 in
open BStarLongDoor BStarLongArithmetic in
theorem accept_frame (x : BitVec LW) (op : Nat) (p : Payload) :
    Frame (acceptFile x op p) := by
  unfold acceptFile
  split
  · exact repair_frame
  split
  · exact repair_frame
  rename_i i _ c _
  dsimp only
  have sc : ∀ ys : Pending, Frame (BStarLongOutgoing.fuse
      (ys.reverse.map fun (i,y) => writeScalar i y)) := by
    intro ys
    apply fuse
    intro q hq
    obtain ⟨⟨a,b⟩,_,rfl⟩ := List.mem_map.mp hq
    exact scalar a b
  split
  · exact compose (sc _) (schedule_frame _)
  split
  · exact compose (compose (sc _) (compose (compose (assign _ _ (.inl (by decide)))
      (assign _ _ (.inl (by decide)))) (assign _ _ (.inl (by decide))))) (schedule_frame _)
  · exact repair_frame

open BStarLongOutgoing BStarLongPublication in
theorem stage_frame (head inside : Bool) (x : BitVec LW) (d : Descriptor) (n : Nat) :
    Frame (stagePatch head inside x d n) := by
  have hd (b : Bool) (bank : Fin 3) :
      ∀ q∈dimDigits x b bank, Frame q := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    exact assign _ _ (.inl (by simp [bankDigit,bankPart,bankBase]; omega))
  have hh (b : Bool) (bank : Fin 3) :
      ∀ q∈dimHeaders n b bank, Frame q := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    exact assign _ _ (.inl (by simp [bankHeader,bankPart,bankBase]; omega))
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
    · exact assign _ _ (.inl (by decide))

open BStarLongOutgoing BStarLongPublication in
theorem execute_frame (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) :
    Frame (execute g j x p).row := by
  have dc : Frame descriptorClear :=
    compose (assign _ _ (.inl (by decide))) (assign _ _ (.inl (by decide)))
  have sf (d : Descriptor) : Frame (sealField.assign (packOptional (some d))) :=
    assign _ _ (.inl (by decide))
  have setterF (b : Fin 3) : Frame (setter b) :=
    compose (compose (assign _ _ (.inl (by decide)))
      (assign _ _ (.inl (by decide)))) (assign _ _ (.inl (by decide)))
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

theorem selected_frame (g : Pair LongGeometry) (x : Pair (BitVec LW)) (o : CmdOffer) :
    ∀ t∈(selected g x o).work, Frame t.2 := by
  obtain ⟨c,q⟩ := o
  cases q <;> simp only [selected]
  all_goals try (intro t ht; simp at ht; done)
  · split
    · intro t ht; simp at ht
    · intro t ht
      obtain rfl := List.mem_singleton.mp ht
      rename_i s p hp
      unfold BStarLongDoor.oldDoor at hp
      dsimp only at hp
      repeat first
        | contradiction
        | (injection hp with hp'; rw [← hp']; exact repair_frame)
        | (injection hp with hp'; rw [← hp']; exact issue_frame _ _)
        | (injection hp with hp'; rw [← hp']; exact reply_frame _ _ _)
        | split at hp
    · intro t ht
      obtain rfl := List.mem_singleton.mp ht
      exact accept_frame _ _ _
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · exact numeric_visit _ _ _ _
    · exact execute_frame _ _ _ _

theorem selected_fold_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (acc : Selected) (H : ∀ t∈acc.work, Frame t.2) :
    ∀ t∈(os.foldl (fun acc o => Selected.append acc (selected g x o)) acc).work,
      Frame t.2 := by
  induction os generalizing acc with
  | nil => exact H
  | cons o os ih =>
    apply ih
    intro t ht
    exact (List.mem_append.mp ht).elim (H t) (selected_frame g x o t)

theorem clear_frame (g : LongGeometry) : Frame (nonheader g) := by
  unfold nonheader
  split
  · exact zero
  · unfold BStarLongOutgoing.descriptorClear BStarLongDoor.clearFile
    exact compose (compose (compose (BStarClearanceOffsetMask.assign _ _ (.inl (by decide)))
      (BStarClearanceOffsetMask.assign _ _ (.inl (by decide))))
      (BStarClearanceOffsetMask.assign _ _ (.inl (by decide))))
      (compose (BStarClearanceOffsetMask.assign _ _ (.inl (by decide)))
        (BStarClearanceOffsetMask.assign _ _ (.inl (by decide))))

theorem route_frame (w : KWrite) : Frame (lowerOne w).2 := by
  rcases w with ⟨⟨s,j⟩,t⟩
  change Frame (setToken j t)
  unfold setToken
  apply assign
  left
  change 1192+52*(10-j.val)+52≤2364
  omega

theorem packet_frame (w : At Sheet) (a : BStarLongPackets.Leaf) :
    Frame (BStarLongPackets.writeAt w a).patch.2 := by
  rw [BStarLongPackets.writeAt_patch]
  unfold BStarLongPackets.Leaf.assign
  apply BStarClearanceOffsetMask.assign
  left
  have := a.fits
  change 728+116*(3-(BStarLongPackets.Sheet.index w.occurrence).val)+a.offset+a.width ≤2364
  omega

theorem copy_frame (g : Pair LongGeometry) (old : At Sheet → BStarLongPackets.Lane)
    (os : List BStarLongPrep.Offer) :
    ∀ t∈(BStarLongPrep.writes g old os).map Write.patch, Frame t.2 := by
  intro t ht
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ht
  obtain ⟨⟨a,u⟩,_,rfl⟩ := List.mem_map.mp hw
  exact packet_frame a u

theorem grant_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) :
    ∀ t∈(BStarLongGrant.run g x os).writes.map Write.patch, Frame t.2 := by
  unfold BStarLongGrant.run
  simp only [List.map_append,List.mem_append]
  intro t ht
  have T (s : Side) (H : t∈(BStarLongGrant.siteWrites g x os s).map Write.patch) : Frame t.2 := by
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp H
    obtain ⟨j,_,G⟩ := List.mem_filterMap.mp hw
    split at G
    · cases G
      apply assign
      left
      change 2359-j.val+1≤2364
      omega
    · contradiction
  exact ht.elim (T .left) (T .right)

theorem work_assignments (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    ∀ t∈(longTrace g x).assignments, Frame t.2 := by
  intro t ht
  simp only [longTrace,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with (((((hn|(rfl|rfl))|ha)|hd)|hw)|hl)
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hn
    exact route_frame a
  · exact clear_frame _
  · exact clear_frame _
  · exact grant_frame g x _ t ha
  · exact copy_frame g _ _ t hd
  · exact selected_fold_frame g x _ _ (by simp) t hw
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hl
    exact route_frame a

private theorem field_holds (z : BitVec LW) (p : Patch LW) (h : Frame p) :
    offField.read (p.apply z)=offField.read z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  exact Patch.hold _ _ _ (h _ (by change 2364≤2364+i; omega) (by change 2364+i<2367; omega))

private theorem fold_holds (w : List (Bool × Patch LW)) (z : Pair (BitVec LW))
    (H : ∀ t∈w, Frame t.2) :
    offField.read ((w.foldl runWrite z).1)=offField.read z.1 := by
  induction w generalizing z with
  | nil => rfl
  | cons t w ih =>
    rw [List.foldl_cons,ih _ (fun u hu => H u (List.mem_cons_of_mem _ hu))]
    obtain ⟨s,q⟩ := t
    cases s
    · exact field_holds z.1 q (H _ List.mem_cons_self)
    · rfl

/-- On the actual joined pair, the initiating cell retains all its
raw offset bits. This closes the offset-specific frame in five_covers. -/
theorem joined_left (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    offsetL (largePair b x).1.long=offsetL x.1.long := by
  dsimp only
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g raw
  let q := longScratch g raw
  have F : offField.read ((q.1).apply (w.1.apply raw.1))=offField.read (w.1.apply raw.1) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    exact (longScratch_holds g (w.1.apply raw.1,raw.2) (2364+i)).1 (by omega) (by omega)
  have W : offField.read (w.1.apply raw.1)=offField.read raw.1 := by
    change offField.read (patchPair (longWork g raw) raw).1=_
    rw [long_exec]
    exact fold_holds _ _ (work_assignments g raw)
  have E : offField.read (largePair b x).1.long=offField.read raw.1 := by
    change offField.read ((w.1.compose q.1).apply raw.1)=_
    rw [Patch.compose_apply,F,W]
  exact congrArg (fun z : BitVec 3 => min 5 z.toNat) E

theorem leftFrame {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : BStarClearanceOffset.X k₁ k₂ t₂ J₁ J₂ r c p c₁ n) (e : Fin n) :
    BStarClearanceOffset.LeftFrame hp x e :=
  joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))

#print axioms joined_left
end L4.BStarClearanceOffsetMask
