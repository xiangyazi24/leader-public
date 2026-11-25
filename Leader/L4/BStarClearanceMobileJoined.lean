import Leader.L4.BStarClearanceMobile
import Leader.L4.BStarLongWork

/-! The full joined row preserves all COPY-lane projections of its literal data round. -/
namespace L4.BStarClearanceMobileJoined
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongTransport BStarLongClaims

def Frame (p : Patch LW) : Prop :=
  ∀ i, 728 ≤ i → i < 1192 → p.mask.getLsbD i=false

theorem zero : Frame (.empty LW) := by simp [Frame,Patch.empty]

theorem compose {p q : Patch LW} (hp : Frame p) (hq : Frame q) :
    Frame (p.compose q) := by
  intro i lo hi
  simp [Patch.compose,hp i lo hi,hq i lo hi]

theorem assign {n : Nat} (f : Field LW n) (b : BitVec n)
    (h : f.offset+n≤728 ∨ 1192≤f.offset) : Frame (f.assign b) := by
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
  exact h

theorem scalar (j n : Nat) : Frame (BStarLongArithmetic.writeScalar j n) :=
  assign _ _ (.inr (Nat.le_add_right 1192 _ |> fun h =>
    Nat.le_trans h (Nat.add_le_add_right (by decide : 1192≤1764) _)))

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

open BStarLongDoor in
theorem schedule_frame (op : Nat) : Frame (schedule op) := by
  unfold schedule
  apply compose (compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide))))
  exact assign _ _ (.inr (by decide))

open BStarLongDoor in
theorem repair_frame : Frame faultRestart := by
  unfold faultRestart LongDoorGuard.repair
  apply compose (compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide))))
  exact compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide)))

open BStarLongDoor in
theorem issue_frame (op n : Nat) : Frame (issued op n) := by
  have h : Frame ((ctrlPhase.assign 2).compose (setToken 0 (forward op n))) :=
    compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide)))
  unfold issued
  split
  · exact compose (assign _ _ (.inr (by decide))) h
  · exact h

open BStarLongDoor in
theorem reply_frame (op : Nat) (p : Payload) (x : BitVec LW) :
    Frame (afterReply op p x) := by
  have ca (a : BitVec 6) : Frame (captures.assign a) := assign _ _ (.inr (by decide))
  have ch (a : BitVec 27) : Frame (capturedHeaders.assign a) := assign _ _ (.inr (by decide))
  have sh (a : BitVec 18) : Frame (candidateHeaders.assign a) := assign _ _ (.inr (by decide))
  have sd (a : BitVec 7) : Frame (sourceDescriptor.assign a) := assign _ _ (.inr (by decide))
  have co (a : BitVec 2) : Frame (choice.assign a) := assign _ _ (.inr (by decide))
  have nd (a : BitVec 1) : Frame (need.assign a) := assign _ _ (.inr (by decide))
  have de (a : BitVec 1) : Frame (delta.assign a) := assign _ _ (.inr (by decide))
  have fl (a : BitVec 369) : Frame (scalarFile.assign a) := assign _ _ (.inr (by decide))
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
  · exact compose (compose (sc _) (compose (compose (assign _ _ (.inr (by decide)))
      (assign _ _ (.inr (by decide)))) (assign _ _ (.inr (by decide))))) (schedule_frame _)
  · exact repair_frame

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
    exact compose (compose (compose (BStarClearanceMobileJoined.assign _ _ (.inr (by decide)))
      (BStarClearanceMobileJoined.assign _ _ (.inr (by decide))))
      (BStarClearanceMobileJoined.assign _ _ (.inr (by decide))))
      (compose (BStarClearanceMobileJoined.assign _ _ (.inr (by decide)))
        (BStarClearanceMobileJoined.assign _ _ (.inr (by decide))))

theorem grant_site_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) (s : Side) :
    ∀ t∈(BStarLongGrant.siteWrites g x os s).map Write.patch, Frame t.2 := by
  intro t ht
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ht
  obtain ⟨j,_,H⟩ := List.mem_filterMap.mp hw
  split at H
  · cases H
    apply BStarClearanceMobileJoined.assign
    right
    change 1192≤2359-j.val
    have := j.isLt
    omega
  · contradiction

theorem grant_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : BStarLongGrant.Offers) :
    ∀ t∈(BStarLongGrant.run g x os).writes.map Write.patch, Frame t.2 := by
  unfold BStarLongGrant.run
  simp only [List.map_append,List.mem_append]
  intro t h
  exact h.elim (grant_site_frame g x os .left t) (grant_site_frame g x os .right t)


open BStarLongPackets BStarLongPrep

theorem read_hold (p : Patch LW) (x : BitVec LW) (s : Fin 4) (hp : Frame p) :
    readLane s (p.apply x)=readLane s x := by
  have H {k : Nat} (f : Field LW k) (lo : 728≤f.offset) (hi : f.offset+k≤1192) :
      f.read (p.apply x)=f.read x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hb
    simp only [Field.read,BitVec.getLsbD_extractLsb',hb,decide_true,Bool.true_and]
    exact Patch.hold _ _ _ (hp _ (by omega) (by omega))
  have K (a k : Nat) (fit : a+k≤116) :
      (lanePart s a k fit).read (p.apply x)=(lanePart s a k fit).read x := by
    apply H
    · change 728≤728+116*(3-s.val)+a; omega
    · change 728+116*(3-s.val)+a+k≤1192; omega
  simp only [readLane,laneGate,laneError,laneMobile,laneFrozen,laneRetained,readBit,K]

theorem hold_view (ts : List (Bool × Patch LW)) (x : Pair (BitVec LW))
    (h : ∀ t∈ts, Frame t.2) : view (ts.foldl runWrite x)=view x := by
  induction ts generalizing x with
  | nil => rfl
  | cons t ts ih =>
    rw [List.foldl_cons, ih _ (fun w hw => h w (List.mem_cons_of_mem _ hw))]
    funext a
    rcases t with ⟨side,p⟩
    have F := h (side,p) List.mem_cons_self
    rcases a with ⟨aSide,j⟩
    cases side with
    | false =>
      cases aSide with
      | left =>
        change readLane (Sheet.index j) (p.apply x.1)=readLane (Sheet.index j) x.1
        exact read_hold p _ _ F
      | right => rfl
    | true =>
      cases aSide with
      | left => rfl
      | right =>
        change readLane (Sheet.index j) (p.apply x.2)=readLane (Sheet.index j) x.2
        exact read_hold p _ _ F

private theorem token_frame (t : KWrite) : Frame (lowerOne t).2 := by
  apply assign
  right
  change 1192≤1192+52*(10-t.1.occurrence.val)
  omega

private theorem k_frames (ts : List KWrite) : ∀ w∈ts.map lowerOne, Frame w.2 := by
  intro w hw
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hw
  exact token_frame u

/-- Every raw COPY lane of the actual packed long work equals its
literal dedicated COPY round, for arbitrary dirty bytes. -/
theorem work_view (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    view (patchPair (longWork g x) x)=view (patchPair (BStarLongCommandData.patch g x) x) := by
  let d := BStarLongCommandData.round g x
  let auth := BStarLongGrant.run g x d.offered
  let acc := auth.departures.foldl (fun a o => Selected.append a (selected g x o)) ⟨[],[],[]⟩
  let pre := (normalization g (readK x)).map lowerOne ++
    [(false,nonheader g.1),(true,nonheader g.2)] ++ auth.writes.map Write.patch
  let post := acc.work ++ (acc.k++observations g (readK x)
    (normalization g (readK x)++acc.k)).map lowerOne
  have E : (longTrace g x).assignments=pre++d.writes.map Write.patch++post := by
    simp only [longTrace,pre,post,d,auth,acc,List.append_assoc]
  have A : ∀ w∈pre, Frame w.2 := by
    intro w hw
    simp only [pre,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with (hh|(rfl|rfl))|hh
    · exact k_frames _ w hh
    · exact clear_frame _
    · exact clear_frame _
    · exact grant_frame g x d.offered w hh
  have B : ∀ w∈post, Frame w.2 := by
    intro w hw
    rcases List.mem_append.mp hw with hh|hh
    · exact selected_fold_frame g x auth.departures _ (by simp) w hh
    · exact k_frames _ w hh
  rw [long_exec,E]
  have Z := List.foldl_append (f:=runWrite) (b:=x) (l:=pre++d.writes.map Write.patch) (l':=post)
  rw [Z,hold_view _ _ B,List.foldl_append]
  rw [BStarLongCommandData.round_transfer]
  change view ((d.writes.map Write.patch).foldl runWrite (pre.foldl runWrite x))=_
  simp only [d,BStarLongCommandData.round,BStarLongPrep.writes,List.map_map,Function.comp_def]
  rw [fold_view,hold_view _ _ A]

/-- The concrete scratch refresh and invalid-door override both lie
above COPY storage. Consequently the full joined pair has exactly
the same decoded lane map as the dedicated literal COPY round. -/
theorem joined_view (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    view (Pair.map LargeSite.long (largePair b x))=view (patchPair (BStarLongCommandData.patch g raw) raw) := by
  dsimp only
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have left : Frame (longScratch g raw).1 :=
    compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide)))
  have right : Frame (longScratch g raw).2 := assign _ _ (.inr (by decide))
  have repair : Frame (LongDoorGuard.repair manifest) := by
    unfold LongDoorGuard.repair
    apply compose (compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide))))
    exact compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide)))
  rw [←work_view]
  funext z
  rcases z with ⟨s,j⟩
  cases s with
  | left =>
    change readLane (Sheet.index j)
      (((longWork g raw).1.compose (longScratch g raw).1).apply raw.1) = _
    rw [Patch.compose_apply,read_hold _ _ _ left]
    rfl
  | right =>
    change readLane (Sheet.index j)
      ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
        ((longWork g raw).2.compose (longScratch g raw).2)).apply raw.2) = _
    unfold LongDoorGuard.guard
    split
    · rw [Patch.compose_apply,read_hold _ _ _ repair,Patch.compose_apply,read_hold _ _ _ right]
      rfl
    · rw [Patch.compose_apply,read_hold _ _ _ right]
      rfl

#print axioms work_view
#print axioms joined_view
end L4.BStarClearanceMobileJoined
