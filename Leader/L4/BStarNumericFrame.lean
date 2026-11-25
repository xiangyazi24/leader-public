import Leader.L4.BStarNumericCarry
import Leader.L4.BStarClearanceOffsetMask

namespace L4.BStarNumericFrame
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken
open BStarLongWork BStarLongTransport BStarLongClaims

def Frame (p : Patch LW) : Prop :=
  ∀ i, i < 728 → p.mask.getLsbD i=false

theorem zero : Frame (.empty LW) := by simp [Frame,Patch.empty]

theorem compose {p q : Patch LW} (hp : Frame p) (hq : Frame q) :
    Frame (p.compose q) := by
  intro i hi
  simp [Patch.compose,hp i hi,hq i hi]

theorem assign {n : Nat} (f : Field LW n) (b : BitVec n)
    (h : 728≤f.offset) : Frame (f.assign b) := by
  intro i hi
  apply Bool.eq_false_iff.mpr
  intro hm
  have := (Field.inMask f b i).mp hm
  omega

theorem fuse_loop (l : List (Patch LW)) (p : Patch LW) (hp : Frame p)
    (h : ∀ q∈l, Frame q) : Frame (l.foldl Patch.compose p) := by
  induction l generalizing p with
  | nil => exact hp
  | cons a l ih =>
    exact ih _ (compose hp (h a List.mem_cons_self)) (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem fuse (l : List (Patch LW)) (h : ∀ q∈l, Frame q) :
    Frame (BStarLongOutgoing.fuse l) := fuse_loop l _ zero h

theorem scalar (j n : Nat) : Frame (BStarLongArithmetic.writeScalar j n) := by
  apply assign
  change 728≤1764+BStarLongRegisters.offsetAt BStarLongRegisters.scalarWidths j
  omega

open BStarLongDoor in
theorem schedule_frame (op : Nat) : Frame (schedule op) := by
  unfold schedule
  apply compose (compose (assign _ _ (by decide)) (assign _ _ (by decide)))
  exact assign _ _ (by decide)

open BStarLongDoor in
theorem repair_frame : Frame faultRestart := by
  unfold faultRestart LongDoorGuard.repair
  apply compose (compose (assign _ _ (by decide)) (assign _ _ (by decide)))
  exact compose (assign _ _ (by decide)) (assign _ _ (by decide))

open BStarLongDoor in
theorem issue_frame (op n : Nat) : Frame (issued op n) := by
  have h : Frame ((ctrlPhase.assign 2).compose (setToken 0 (forward op n))) :=
    compose (assign _ _ (by decide)) (assign _ _ (by decide))
  unfold issued
  split
  · exact compose (assign _ _ (by decide)) h
  · exact h

open BStarLongDoor in
theorem reply_frame (op : Nat) (p : Payload) (x : BitVec LW) :
    Frame (afterReply op p x) := by
  have ca (a : BitVec 6) : Frame (captures.assign a) := assign _ _ (by decide)
  have ch (a : BitVec 27) : Frame (capturedHeaders.assign a) := assign _ _ (by decide)
  have sh (a : BitVec 18) : Frame (candidateHeaders.assign a) := assign _ _ (by decide)
  have sd (a : BitVec 7) : Frame (sourceDescriptor.assign a) := assign _ _ (by decide)
  have co (a : BitVec 2) : Frame (choice.assign a) := assign _ _ (by decide)
  have nd (a : BitVec 1) : Frame (need.assign a) := assign _ _ (by decide)
  have de (a : BitVec 1) : Frame (delta.assign a) := assign _ _ (by decide)
  have fl (a : BitVec 369) : Frame (scalarFile.assign a) := assign _ _ (by decide)
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
  · exact compose (compose (sc _) (compose (compose (assign _ _ (by decide))
      (assign _ _ (by decide))) (assign _ _ (by decide)))) (schedule_frame _)
  · exact repair_frame

open BStarLongOutgoing BStarLongPublication in
theorem stage_frame (head inside : Bool) (x : BitVec LW) (d : Descriptor) (n : Nat) :
    Frame (stagePatch head inside x d n) := by
  have hd (b : Bool) (bank : Fin 3) :
      ∀ q∈dimDigits x b bank, Frame q := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    exact assign _ _ (by simp [bankDigit,bankPart,bankBase]; omega)
  have hh (b : Bool) (bank : Fin 3) :
      ∀ q∈dimHeaders n b bank, Frame q := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    exact assign _ _ (by simp [bankHeader,bankPart,bankBase]; omega)
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
    · exact assign _ _ (by decide)

open BStarLongOutgoing BStarLongPublication in
theorem execute_frame (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p : Payload) :
    Frame (execute g j x p).row := by
  have dc : Frame descriptorClear :=
    compose (assign _ _ (by decide)) (assign _ _ (by decide))
  have sf (d : Descriptor) : Frame (sealField.assign (packOptional (some d))) :=
    assign _ _ (by decide)
  have setterF (b : Fin 3) : Frame (setter b) :=
    compose (compose (assign _ _ (by decide))
      (assign _ _ (by decide))) (assign _ _ (by decide))
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

theorem clear_frame (g : LongGeometry) : Frame (nonheader g) := by
  unfold nonheader
  split
  · exact zero
  · unfold BStarLongOutgoing.descriptorClear BStarLongDoor.clearFile
    exact compose (compose (compose (BStarNumericFrame.assign _ _ (by decide))
      (BStarNumericFrame.assign _ _ (by decide)))
      (BStarNumericFrame.assign _ _ (by decide)))
      (compose (BStarNumericFrame.assign _ _ (by decide))
        (BStarNumericFrame.assign _ _ (by decide)))

theorem route_frame (w : KWrite) : Frame (lowerOne w).2 := by
  rcases w with ⟨⟨s,j⟩,t⟩
  change Frame (setToken j t)
  unfold setToken
  apply assign
  change 728≤1192+52*(10-j.val)
  omega

theorem packet_frame (w : At Sheet) (a : BStarLongPackets.Leaf) :
    Frame (BStarLongPackets.writeAt w a).patch.2 := by
  rw [BStarLongPackets.writeAt_patch]
  unfold BStarLongPackets.Leaf.assign
  apply BStarNumericFrame.assign
  change 728+116*(3-(BStarLongPackets.Sheet.index w.occurrence).val)+a.offset ≥728
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
      change 728≤2359-j.val
      omega
    · contradiction
  exact ht.elim (T .left) (T .right)



open BStarNumericCarry BStarLongEvents BStarLongCommand BStarLongArithmetic
open BStarLongRegisters BStarLongRouting

private theorem in_numeric (i b : Nat) (H : b<widthAt wordWidths i) :
    (numeric i).offset+b<728 := by
  have K := range_bound wordWidths i
  rw [manifest_registers.2.1] at K
  change offsetAt wordWidths i+b<728
  omega

private theorem field_of_frame (i : Nat) (q : Patch LW) (H : Frame q) :
    FieldFrame (numeric i) q := fun b B => H _ (in_numeric i b B)

private theorem assign_disjoint {m n : Nat} (f : Field LW m) (g : Field LW n)
    (v : BitVec n) (D : Disjoint g f) : FieldFrame f (g.assign v) := by
  intro i I
  apply Bool.eq_false_iff.mpr
  intro H
  have B := (Field.inMask g v _).mp H
  rcases D with D|D <;> omega

/-- The old digit handler writes only its decoded register. It cannot
change a different word register, even if the handler is foreign. -/
theorem digit_other (g : LongGeometry) (x : BitVec LW) (i j : Nat)
    (p : Payload) (c : L4.Compiler.Native.Code) (N : i≠j) :
    FieldFrame (numeric j) (physicalDigit g x i c p).1 := by
  have W (v : Nat) : FieldFrame (numeric j) (writeNum i v) :=
    assign_disjoint _ _ _ (numeric_distinct i j N)
  have E : FieldFrame (numeric j) (.empty LW) := field_of_frame _ _ zero
  cases c <;> simp only [physicalDigit]
  all_goals first | exact E | exact W _ | (split <;> first | exact E | exact W _)

private theorem visit_other (g : LongGeometry) (k : Fin 11) (x : BitVec LW) (p : Payload)
    (j : Nat) (excluded : nodeOf p.opcode.toNat≠some j) :
    FieldFrame (numeric j) (visit g k x p).1 := by
  unfold visit
  split
  · exact field_of_frame _ _ zero
  split
  · exact field_of_frame _ _ zero
  · rename_i i I
    split
    · exact field_of_frame _ _ zero
    · exact digit_other _ _ i j p _ (fun e => excluded (e ▸ I))

private theorem selected_num_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (o : CmdOffer) (j : Nat) (s : Bool)
    (guard : ∀ p, o.2=.advance p → (o.1.source.side==.right)=s →
      o.1.source.occurrence.val=1 → nodeOf p.opcode.toNat≠some j) :
    ∀ t∈(selected g x o).work,t.1=s → FieldFrame (numeric j) t.2 := by
  obtain ⟨c,q⟩ := o
  cases q <;> simp only [selected]
  all_goals try (intro t ht; simp at ht; done)
  · split
    · intro t ht; simp at ht
    · intro t ht _
      obtain rfl := List.mem_singleton.mp ht
      have hp := ‹BStarLongDoor.oldDoor _ _=.write _›
      apply field_of_frame
      unfold BStarLongDoor.oldDoor at hp
      dsimp only at hp
      repeat first
        | contradiction
        | (injection hp with hp'; rw [← hp']; exact repair_frame)
        | (injection hp with hp'; rw [← hp']; exact issue_frame _ _)
        | (injection hp with hp'; rw [← hp']; exact reply_frame _ _ _)
        | split at hp
    · intro t ht _
      obtain rfl := List.mem_singleton.mp ht
      exact field_of_frame _ _ (accept_frame _ _ _)
  · rename_i p
    intro t ht S
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · by_cases H : c.source.occurrence.val=1
      · exact visit_other _ _ _ _ j (guard p rfl S H)
      · rw [visit_padding _ _ _ _ (.inl H)]
        exact field_of_frame _ _ zero
    · exact field_of_frame _ _ (execute_frame _ _ _ _)

private theorem selected_fold_num_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (acc : Selected) (j : Nat) (s : Bool)
    (H : ∀ t∈acc.work,t.1=s → FieldFrame (numeric j) t.2)
    (rules : ∀ o∈os,∀ p, o.2=.advance p → (o.1.source.side==.right)=s →
      o.1.source.occurrence.val=1 → nodeOf p.opcode.toNat≠some j) :
    ∀ t∈(os.foldl (fun acc o => Selected.append acc (selected g x o)) acc).work,
        t.1=s → FieldFrame (numeric j) t.2 := by
  induction os generalizing acc with
  | nil => exact H
  | cons o os ih =>
    apply ih _ _ (fun q h => rules q (List.mem_cons_of_mem _ h))
    intro t ht E
    exact (List.mem_append.mp ht).elim (fun hm => H t hm E)
      (fun hm => selected_num_frame g x o j s (rules o List.mem_cons_self) t hm E)

/-- The actual ordered long-work list frames a numeric field unless
its own endpoint has a selected K1 advance decoding to that register. -/
theorem assignments_other (g : Pair LongGeometry) (x : Pair (BitVec LW)) (j : Nat) (s : Bool)
    (guard : ∀ C p, (C,.advance p)∈actualOffers g x → (C.source.side==.right)=s →
      C.source.occurrence.val=1 → nodeOf p.opcode.toNat≠some j) :
    ∀ t∈(longTrace g x).assignments,t.1=s → FieldFrame (numeric j) t.2 := by
  intro t ht E
  simp only [longTrace,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with (((((hn|(rfl|rfl))|ha)|hd)|hw)|hl)
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hn
    exact field_of_frame _ _ (route_frame a)
  · exact field_of_frame _ _ (clear_frame _)
  · exact field_of_frame _ _ (clear_frame _)
  · exact field_of_frame _ _ (grant_frame g x _ t ha)
  · exact field_of_frame _ _ (copy_frame g _ _ t hd)
  · apply selected_fold_num_frame g x (actualOffers g x) ⟨[],[],[]⟩ j s (by simp) _ t hw E
    rintro ⟨C,a⟩ use p rfl
    exact guard C p use
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hl
    exact field_of_frame _ _ (route_frame a)

#print axioms assignments_other

private theorem scratch_numeric (g : Pair LongGeometry) (orig x : Pair (BitVec LW)) (j : Nat) (s : Bool) :
    (numeric j).read (lane s (patchPair (longScratch g orig) x))=(numeric j).read (lane s x) := by
  -- Scratch masks depend on the side only, not on bytes used to
  -- compute its assigned values.
  have mask : FieldFrame (numeric j) (lane s (longScratch g orig)) := by
    intro i H
    have I := in_numeric j i H
    obtain ⟨L,R⟩ := longScratch_mask g orig ((numeric j).offset+i)
    cases s
    · apply Bool.eq_false_iff.mpr
      intro q
      rcases L.mp q with e|e <;> omega
    · apply Bool.eq_false_iff.mpr
      intro q
      have E := R.mp q
      omega
  cases s <;> exact field_frame _ _ _ mask

/-- Outside an actual selected K1 departure decoding this register
on this endpoint, no literal packed write in the full joined step can
alter the numeric field. This includes foreign work, arbitrary
normalization, outer-door repair and scratch refresh. -/
theorem joined_other (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (j : Nat) (s : Bool) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (∀ C u, (C,.advance u)∈actualOffers g raw → (C.source.side==.right)=s →
      C.source.occurrence.val=1 → nodeOf u.opcode.toNat≠some j) →
    (numeric j).read (lane s (Pair.map LargeSite.long (largePair b x)))=
      (numeric j).read (lane s raw) := by
  dsimp only
  intro guard
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g raw
  let q := longScratch g raw
  have F : (numeric j).read (lane s (patchPair (longWork g raw) raw)) =
      (numeric j).read (lane s raw) := by
    rw [long_exec]
    exact fold_field _ s _ _ (assignments_other g raw j s guard)
  have Q := scratch_numeric g raw (patchPair w raw) j s
  cases s
  · change (numeric j).read ((w.1.compose q.1).apply raw.1)=(numeric j).read raw.1
    rw [Patch.compose_apply]
    exact Q.trans F
  · change (numeric j).read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
      (w.2.compose q.2)).apply raw.2)=(numeric j).read raw.2
    have E : (numeric j).read ((w.2.compose q.2).apply raw.2)=(numeric j).read raw.2 := by
      rw [Patch.compose_apply]
      exact Q.trans F
    cases H : g.2.axes.h6
    · rw [LongDoorGuard.no_authority]; exact E
    · cases V : LongDoorGuard.valid manifest raw.2
      · rw [LongDoorGuard.invalid_override _ _ _ V,Patch.compose_apply]
        exact (field_frame (numeric j) _ _ (field_of_frame _ _ repair_frame)).trans E
      · rw [LongDoorGuard.valid_no_override _ _ _ V]; exact E

#print axioms joined_other

open BStarH6WordChart BStarLongLiteral

/-- The right endpoint can never be an old numeric-write initiator:
the literal unique K1 departure is always left-to-right. -/
theorem joined_right (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (j : Nat) :
    (numeric j).read (largePair (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp) x).2.long=
      (numeric j).read x.2.long := by
  apply joined_other k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x j true
  intro C u sel S K
  have hm : C∈orderedCommands (Pair.map (longGeometry (bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp)) x) := by
    rw [←actualOffers_claims _ (Pair.map LargeSite.long x)]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  rw [center_of _ C hm K] at S
  contradiction

/-- Full-ring one-mark field frame. Only the old initiator's actual
selected centre opcode has to be excluded. -/
theorem step_other {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e i : Fin n) (j : Nat) (sep : e≠rightNeighbor e) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := oldPair b x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    (i=e → ∀ C u, (C,.advance u)∈actualOffers g raw →
      C.source.occurrence.val=1 → nodeOf u.opcode.toNat≠some j) →
    (numeric j).read (AllSizeS1Geometry.step b x e i).long=(numeric j).read (x i).long := by
  dsimp only
  intro guard
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  by_cases E : i=e
  · subst i
    change (numeric j).read (AllSizeS1Geometry.step b x e e).long=(numeric j).read (x e).long
    simp only [AllSizeS1Geometry.step,if_pos rfl]
    exact joined_other _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) j false
      (fun C u sel _ J => guard rfl C u sel J)
  · by_cases H : i=rightNeighbor e
    · subst i
      change (numeric j).read (AllSizeS1Geometry.step b x e (rightNeighbor e)).long=_
      simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep)]
      exact joined_right _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) j
    · simp [AllSizeS1Geometry.step,E,H]

#print axioms step_other

private theorem fold_work (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (a : Selected) :
    (os.foldl (fun acc o => acc.append (selected g x o)) a).work=
      a.work++os.flatMap (fun o => (selected g x o).work) := by
  induction os generalizing a with
  | nil => simp
  | cons h t ih =>
    simpa [Selected.append,List.append_assoc] using ih (a.append (selected g x h))

/-- Literal numeric read after the designated healthy selected visit;
all simultaneous work on the physical initiator is accounted for. -/
theorem work_digit (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (C : CommandClaim) (p : Payload) (sel : (C,.advance p)∈actualOffers g x)
    (J : C.source.occurrence.val=1) (N : Numeric p) (i : Nat)
    (c : L4.Compiler.Native.Code) (ix : nodeOf p.opcode.toNat=some i)
    (code : BStarLongArithmetic.get i=some c) (I : g.1.inside=true)
    (H : (physicalDigit g.1 x.1 i c p).2.fault=0) (j : Nat) :
    (numeric j).read (patchPair (longWork g x) x).1 =
      (numeric j).read ((physicalDigit g.1 x.1 i c p).1.apply x.1) := by
  let O := actualOffers g x
  let d := BStarLongCommandData.round g x
  let u := BStarLongGrant.run g x d.offered
  let sr : Selected := O.foldl (fun acc o => acc.append (selected g x o)) ⟨[],[],[]⟩
  obtain ⟨pre,post,S⟩ := List.mem_iff_append.mp sel
  change O=pre++(C,.advance p)::post at S
  have cm : C∈orderedCommands g := by
    rw [←actualOffers_claims g x]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have L : C.source=L 1 := by rw [center_of g C cm J]; rfl
  let patch := (physicalDigit g.1 x.1 i c p).1
  have selW : (selected g x (C,.advance p)).work=[(false,patch),(false,.empty LW)] := by
    have Q := selected_digit g x C p i c N ix code J
      (by rw [L]; exact I)
      (by rw [L]; exact H)
    rw [L] at Q
    exact Q.1
  have counts : ((pre.map Prod.fst).filter centerClaim).length+
      ((post.map Prod.fst).filter centerClaim).length=0 := by
    have Q := congrArg (fun v : List CommandClaim => (v.filter centerClaim).length)
      (actualOffers_claims g x)
    change ((O.map Prod.fst).filter centerClaim).length=_ at Q
    rw [one_center_claim,S] at Q
    simp only [List.map_append,List.map_cons,List.filter_append,List.filter_cons,centerClaim,J,
      BEq.rfl,if_true,List.length_append,List.length_cons,List.length_nil] at Q
    omega
  have noC {ls : List CmdOffer} (Z : ((ls.map Prod.fst).filter centerClaim).length=0)
      (o : CmdOffer) (M : o∈ls) :
      o.1.source.occurrence.val≠1 := by
    intro E
    have K : o.1∈(ls.map Prod.fst).filter centerClaim :=
      List.mem_filter.mpr ⟨List.mem_map.mpr ⟨o,M,rfl⟩,by simp [centerClaim,E]⟩
    have P := List.length_pos_of_mem K
    omega
  have W : sr.work=pre.flatMap (fun o => (selected g x o).work) ++
      [(false,patch),(false,.empty LW)] ++ post.flatMap (fun o => (selected g x o).work) := by
    have Q := fold_work g x O ⟨[],[],[]⟩
    change sr.work=[]++O.flatMap _ at Q
    simpa [S,selW,List.append_assoc] using Q
  let start := normalization g (readK x)
  let final := observations g (readK x) (start++sr.k)
  let before := start.map lowerOne ++ [(false,nonheader g.1),(true,nonheader g.2)] ++
    u.writes.map Write.patch ++ d.writes.map Write.patch ++ pre.flatMap (fun o => (selected g x o).work)
  let after := (false,.empty LW)::(post.flatMap (fun o => (selected g x o).work) ++
    (sr.k++final).map lowerOne)
  have B (t : Bool × Patch LW) (ht : t∈before) (E : t.1=false) : FieldFrame (numeric j) t.2 := by
    simp only [before,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with ((((h|(rfl|rfl))|h)|h)|h)
    · obtain ⟨w,_,rfl⟩ := List.mem_map.mp h
      exact field_of_frame _ _ (route_frame w)
    · exact field_of_frame _ _ (clear_frame _)
    · exact field_of_frame _ _ (clear_frame _)
    · exact field_of_frame _ _ (grant_frame g x _ t h)
    · exact field_of_frame _ _ (copy_frame g _ _ t h)
    · obtain ⟨o,ho,H⟩ := List.mem_flatMap.mp h
      exact selected_num_frame g x o j false (fun _ _ _ Z => (noC (by omega) o ho Z).elim) t H E
  have A (t : Bool × Patch LW) (ht : t∈after) (E : t.1=false) : FieldFrame (numeric j) t.2 := by
    rcases List.mem_cons.mp ht with rfl|h
    · exact field_of_frame _ _ zero
    · rcases List.mem_append.mp h with h|h
      · obtain ⟨o,ho,H⟩ := List.mem_flatMap.mp h
        exact selected_num_frame g x o j false (fun _ _ _ Z => (noC (by omega) o ho Z).elim) t H E
      · obtain ⟨w,_,rfl⟩ := List.mem_map.mp h
        exact field_of_frame _ _ (route_frame w)
  have trace : (longTrace g x).assignments=before++(false,patch)::after := by
    change start.map lowerOne ++ [(false,nonheader g.1),(true,nonheader g.2)] ++
      u.writes.map Write.patch ++ d.writes.map Write.patch ++ sr.work ++
      (sr.k++final).map lowerOne=_
    rw [W]
    simp [before,after,List.append_assoc]
  change (numeric j).read (patchPair (lower (longTrace g x).assignments) x).1=_
  rw [trace]
  exact field_one_write (numeric j) false before after x patch B A

#print axioms work_digit

/-- The actual published-row join's numerical initiator field is the
projected physical digit result. Scratch is also included in this
comparison. The full right side remains framed by joined_right. -/
theorem step_digit {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e : Fin n) (C : CommandClaim) (u : Payload) (i : Nat) (v : L4.Compiler.Native.Code)
    (j : Nat) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := oldPair b x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    (C,.advance u)∈actualOffers g raw → C.source.occurrence.val=1 →
    Numeric u → nodeOf u.opcode.toNat=some i → BStarLongArithmetic.get i=some v → g.1.inside=true →
    (physicalDigit g.1 raw.1 i v u).2.fault=0 →
    (numeric j).read (AllSizeS1Geometry.step b x e e).long =
      (numeric j).read ((physicalDigit g.1 raw.1 i v u).1.apply raw.1) := by
  dsimp only
  intro sel J H I K inside healthy
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := oldPair b x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let w := longWork g raw
  let q := longScratch g raw
  have E := work_digit g raw C u sel J H i v I K inside healthy j
  have Q := scratch_numeric g raw (patchPair w raw) j false
  simp only [AllSizeS1Geometry.step,if_pos rfl]
  change (numeric j).read ((w.1.compose q.1).apply raw.1)=_
  rw [Patch.compose_apply]
  exact Q.trans E

#print axioms step_digit

/-- Over a physical raw subword, only actual visits decoding the
chosen register can alter it at the given location. The exclusion is
on each exact old-prefix state, not on a hypothetical abstract mark. -/
theorem word_other {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
    (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (i : Fin n) (j : Nat) (tape : List (Fin n))
    (sep : ∀ e : Fin n,e≠rightNeighbor e) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let step := AllSizeS1Geometry.step (n:=n) b
    (∀ pre e post, tape=pre++e::post → i=e →
      let y := BStarResetSchedule.run step x pre
      ∀ C u, (C,.advance u)∈actualOffers (oldPair b y e)
        ((y e).long,(y (rightNeighbor e)).long) →
        C.source.occurrence.val=1 → nodeOf u.opcode.toNat≠some j) →
    (numeric j).read ((BStarResetSchedule.run step x tape) i).long = (numeric j).read (x i).long := by
  dsimp only
  intro avoid
  induction tape generalizing x with
  | nil => rfl
  | cons e rest ih =>
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let y := AllSizeS1Geometry.step b x e
    have L := step_other hp x e i j (sep e) (avoid [] e rest rfl)
    have R := ih y (fun pre mark post split eq =>
      avoid (e::pre) mark post (congrArg (List.cons e) split) eq)
    exact R.trans L

#print axioms word_other
end L4.BStarNumericFrame
