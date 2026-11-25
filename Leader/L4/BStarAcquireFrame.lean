import Leader.L4.BStarLongWork

/-! Successful normal long source and non-door rows frame the ACQUIRE capture file. -/
namespace L4.BStarAcquireFrame
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongTransport BStarLongClaims

def Frame (p : Patch LW) : Prop :=
  ∀ i, 2162 ≤ i → i < 2195 → p.mask.getLsbD i=false

theorem zero : Frame (.empty LW) := by simp [Frame,Patch.empty]

theorem compose {p q : Patch LW} (hp : Frame p) (hq : Frame q) :
    Frame (p.compose q) := by
  intro i lo hi
  simp [Patch.compose,hp i lo hi,hq i lo hi]

theorem assign {n : Nat} (f : Field LW n) (b : BitVec n)
    (h : f.offset+n≤2162 ∨ 2195≤f.offset) : Frame (f.assign b) := by
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
  apply compose (compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide))))
  exact assign _ _ (.inl (by decide))

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem issue_frame (op n : Nat) (hn : op≠1) : Frame (issued op n) := by
  simp only [issued,beq_iff_eq,if_neg hn]
  exact compose (assign _ _ (.inr (by decide))) (assign _ _ (.inl (by decide)))

set_option maxHeartbeats 1800000 in
open BStarLongDoor in
theorem reply_frame (op : Nat) (p : Payload) (x : BitVec LW)
    (hn : op≠BStarLongCommand.acquire) (ok : afterReply op p x≠faultRestart) :
    Frame (afterReply op p x) := by
  have sh (a : BitVec 18) : Frame (candidateHeaders.assign a) := assign _ _ (.inl (by decide))
  have sd (a : BitVec 7) : Frame (sourceDescriptor.assign a) := assign _ _ (.inl (by decide))
  have co (a : BitVec 2) : Frame (choice.assign a) := assign _ _ (.inl (by decide))
  have nd (a : BitVec 1) : Frame (need.assign a) := assign _ _ (.inl (by decide))
  have de (a : BitVec 1) : Frame (delta.assign a) := assign _ _ (.inl (by decide))
  have fl (a : BitVec 369) : Frame (scalarFile.assign a) := assign _ _ (.inl (by decide))
  unfold afterReply at ok ⊢
  simp only [beq_iff_eq,if_neg hn] at ok ⊢
  by_cases A : op = BStarLongCommand.admit
  · rw [if_pos A]
    exact schedule_frame _
  rw [if_neg A] at ok ⊢
  by_cases B : op=1
  · rw [if_pos B]
    exact compose (schedule_frame _) (compose (compose (sd _) (co _)) (sh _))
  rw [if_neg B] at ok ⊢
  by_cases C : op=12
  · rw [if_pos C]
    exact compose (schedule_frame _) (compose (fl _) (nd _))
  rw [if_neg C] at ok ⊢
  by_cases T : ((op==BStarLongCommand.sealOp) || (op==BStarLongCommand.bitOp))=true
  · rw [if_pos T] at ok ⊢
    cases D : BStarLongPublication.decode (sourceDescriptor.read x) with
    | none => rw [D] at ok; exact False.elim (ok rfl)
    | some d =>
      rw [D] at ok; dsimp only at ok ⊢
      by_cases E : op=BStarLongCommand.sealOp
      · erw [if_pos E] at ok ⊢
        by_cases F : ((p.argument.toNat%2==1) != d.need)=true
        · erw [if_pos F] at ok; exact False.elim (ok rfl)
        · erw [if_neg F]
          split
          · exact schedule_frame _
          · exact compose (schedule_frame _) (co _)
      · erw [if_neg E] at ok ⊢
        by_cases F : (!d.need)=true
        · erw [if_pos F] at ok; exact False.elim (ok rfl)
        · erw [if_neg F]
          exact compose (compose (schedule_frame _) (de _)) (co _)
  · rw [if_neg T]
    exact schedule_frame _

set_option maxHeartbeats 1200000 in
open BStarLongDoor BStarLongArithmetic in
theorem accept_frame (x : BitVec LW) (op : Nat) (p : Payload)
    (ok : acceptFile x op p≠faultRestart) : Frame (acceptFile x op p) := by
  unfold acceptFile at ok ⊢
  cases E : nodeOf op
  · rw [E] at ok
    exact False.elim (ok rfl)
  rename_i i
  rw [E] at ok
  dsimp only at ok ⊢
  cases D : get i
  · rw [D] at ok
    exact False.elim (ok rfl)
  rw [D] at ok
  dsimp only at ok ⊢
  have sc : ∀ ys : Pending, Frame (BStarLongOutgoing.fuse
      (ys.reverse.map fun (i,y) => writeScalar i y)) := by
    intro ys
    apply fuse
    intro q hq
    obtain ⟨⟨a,b⟩,_,rfl⟩ := List.mem_map.mp hq
    exact scalar a b
  by_cases K : op < 407
  · rw [if_pos K]
    exact compose (sc _) (schedule_frame _)
  rw [if_neg K] at ok ⊢
  by_cases V : ((capturedSelector 1).read x).toNat < 3
  · rw [dif_pos V]
    exact compose (compose (sc _) (compose (compose (assign _ _ (.inl (by decide)))
      (assign _ _ (.inl (by decide)))) (assign _ _ (.inl (by decide))))) (schedule_frame _)
  · rw [dif_neg V] at ok
    exact False.elim (ok rfl)

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
  change 1192+52*(10-j.val)+52≤2162
  omega

theorem packet_frame (w : At Sheet) (a : BStarLongPackets.Leaf) :
    Frame (BStarLongPackets.writeAt w a).patch.2 := by
  rw [BStarLongPackets.writeAt_patch]
  unfold BStarLongPackets.Leaf.assign
  apply assign
  left
  have := a.fits
  change 728+116*(3-(BStarLongPackets.Sheet.index w.occurrence).val)+a.offset+a.width ≤2162
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

open BStarLongDoor in
theorem captures_hold (q : Patch LW) (x : BitVec LW) (h : Frame q) :
    capturedHeaders.read (q.apply x)=capturedHeaders.read x ∧
    captures.read (q.apply x)=captures.read x := by
  have field {n : Nat} (f : Field LW n)
      (lo : 2162≤f.offset) (hi : f.offset+n≤2195) :
      f.read (q.apply x)=f.read x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi'
    have hold := q.hold x (f.offset+i) (h _ (by omega) (by omega))
    simpa only [Field.read,BitVec.getLsbD_extractLsb',hi',decide_true,Bool.true_and] using hold
  exact ⟨field _ (by decide) (by decide),field _ (by decide) (by decide)⟩

open BStarLongDoor BStarLongArithmetic in
/-- Successful source classifications; restart paths and writes to the
capture file are intentionally not admitted. -/
inductive Normal (x : BitVec LW) : Decision → Prop where
  | hold : Normal x .hold
  | issue (op n : Nat) (h : op≠1) : Normal x (.write (issued op n))
  | reply (op : Nat) (p : Payload) (h : op≠BStarLongCommand.acquire)
      (ok : afterReply op p x≠faultRestart) : Normal x (.write (afterReply op p x))
  | tour (op : Nat) (p : Payload) (ok : acceptFile x op p≠faultRestart) :
      Normal x (.acceptTour op p)

theorem normal_door_frames (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (k : Token)
    (hn : Normal (BStarLongWork.atOld x c.source)
      (BStarLongDoor.oldDoor (BStarLongWork.atOld x c.source) k)) :
    ∀ w∈(selected g x (c,.door k)).work, Frame w.2 := by
  simp only [selected]
  generalize BStarLongDoor.oldDoor (BStarLongWork.atOld x c.source) k=d at hn ⊢
  cases hn with
  | hold => simp
  | issue op n h =>
    intro w hw
    obtain rfl := List.mem_singleton.mp hw
    exact issue_frame op n h
  | reply op p h ok =>
    intro w hw
    obtain rfl := List.mem_singleton.mp hw
    exact reply_frame _ _ _ h ok
  | tour op p ok =>
    intro w hw
    obtain rfl := List.mem_singleton.mp hw
    exact accept_frame _ _ _ ok

open BStarLongDoor in
theorem long_work_preserves (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Bool)
    (hh : (lane s g).axes.h6=true)
    (normal : ∀ c k, (c,.door k)∈
      (BStarLongGrant.run g x (BStarLongCommandData.round g x).offered).departures →
      (c.source.side==.right)=s →
      Normal (BStarLongWork.atOld x c.source) (oldDoor (BStarLongWork.atOld x c.source) k)) :
    let y := lane s (patchPair (longWork g x) x)
    capturedHeaders.read y=capturedHeaders.read (lane s x) ∧
    captures.read y=captures.read (lane s x) := by
  have F := long_work_frame g x s hh (by
    rintro ⟨c,o⟩ ho ⟨k,rfl⟩ w hw hs
    have E : w.1=(c.source.side==.right) := by
      simp only [selected] at hw
      split at hw
      · simp at hw
      · exact congrArg Prod.fst (List.mem_singleton.mp hw)
      · exact congrArg Prod.fst (List.mem_singleton.mp hw)
    exact normal_door_frames g x c k (normal c k ho (E.symm.trans hs)) w hw)
  have H := captures_hold (lane s (longWork g x)) (lane s x) F
  cases s <;> exact H

end L4.BStarAcquireFrame
