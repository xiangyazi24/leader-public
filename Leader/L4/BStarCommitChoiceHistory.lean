import Leader.L4.BStarCommitChoiceFrame
import Leader.L4.BStarResetControllerEntry
import Leader.L4.BStarLongLandingCore

namespace L4.BStarCommitChoiceHistory
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken BStarLongLayout
open BStarLongDoor BStarLongCommand BStarCommitIssue BStarCommitChoiceFrame
open BStarResetControllerEntry BStarH6WordChart BStarLongEvents BStarLongTransport

/-- The source marks that actually consume either a matching SEAL or BIT
reply. This extracts the selected old door patch, not its authenticity. -/
theorem reply_work (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (f : Payload)
    (hdr : g.2.axes.h6=true) (V : LongDoorGuard.valid manifest raw.2=true)
    (ph : (ctrlPhase.read raw.2).toNat=2) (op : Nat)
    (P : (ctrlOp.read raw.2).toNat=op)
    (R : bind g.2 0 (atSite raw.2 0)=.reply f)
    (F : f.fault=0) (O : f.opcode.toNat=op)
    (N : (arithKind op).isSome=false) :
    (selected g raw (doorClaim,.door (bind g.2 0 (atSite raw.2 0)))).work=
      [(true,afterReply op f raw.2)] := by
  have E := (BStarResetControllerEntry.wait_reply_selected g raw f hdr V ph R).2.2
  change (selected g raw (doorClaim,.door (.reply f))).work=[(true,_)] at E
  rw [P] at E
  simpa [R,F,O,N] using E

def pick (d : Desc) (f : Payload) : Fin 3 :=
  if f.argument.toNat%2=1 then d.b1 else d.b0

private theorem schedule_frame (op : Nat) : Frame (schedule op) := by
  unfold schedule setToken
  exact compose (compose (assign _ _ (Or.inr (by decide))) (assign _ _ (Or.inr (by decide))))
    (assign _ _ (Or.inl (by decide)))

private theorem select_projection (op : Nat) (b : Fin 3) (y : BitVec LW) :
    choice.read (((schedule op).compose (choice.assign (BitVec.ofNat 2 b.val))).apply y)=
      BitVec.ofNat 2 b.val ∧
    sourceDescriptor.read (((schedule op).compose (choice.assign (BitVec.ofNat 2 b.val))).apply y)=
      sourceDescriptor.read y := by
  simp only [Patch.compose_apply]
  rw [Field.read_assign,Field.read_other_assign sourceDescriptor choice _ _ (by decide)]
  exact ⟨rfl,field_hold _ _ _ (schedule_frame op) (by decide) (by decide)⟩

private theorem bit_projection (f : Payload) (d : Desc) (y : BitVec LW) :
    let b := f.argument.toNat%2==1
    let q := ((schedule commitOp).compose (delta.assign (BitVec.ofBool b))).compose
      (choice.assign (BitVec.ofNat 2 (if b then d.b1.val else d.b0.val)))
    choice.read (q.apply y)=BitVec.ofNat 2 (pick d f).val ∧
      sourceDescriptor.read (q.apply y)=sourceDescriptor.read y := by
  dsimp only
  simp only [Patch.compose_apply]
  rw [Field.read_assign,Field.read_other_assign sourceDescriptor choice _ _ (by decide),
    Field.read_other_assign sourceDescriptor delta _ _ (by decide)]
  exact ⟨by by_cases h : f.argument.toNat%2=1 <;> simp [pick,beq_iff_eq,h],field_hold _ _ _ (schedule_frame commitOp) (by decide) (by decide)⟩

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "A" => production k₁ k₂ t₂ J₁ J₂ r c p c₁

private theorem joined_right_field (x : Pair (LargeSite A))
    (V : LongDoorGuard.valid manifest x.2.long=true)
    {m : Nat} (field : Field LW m) (hi : field.offset+m≤2195) :
    let g := Pair.map (longGeometry B) x
    let raw := Pair.map LargeSite.long x
    field.read (largePair B x).2.long=field.read (patchPair (longWork g raw) raw).2 := by
  dsimp only
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  change field.read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
    ((longWork g raw).2.compose (longScratch g raw).2)).apply raw.2)=_
  have VV : LongDoorGuard.valid manifest raw.2=true := V
  simp only [LongDoorGuard.guard,VV,Bool.not_true,Bool.and_false,Bool.false_eq_true,if_false,
    Patch.compose_apply]
  exact Field.read_other_assign field offField _ _ (.inl (Nat.le_trans hi (by decide)))

/-- Exact joined good receipt writes choice from the selected branch
and leaves the seven descriptor bits untouched. The true SEAL branch
therefore leaves choice dormant until the later BIT receipt. -/
theorem joined_choice_receipt (x : Pair (LargeSite A)) (f : Payload) (op : Nat)
    (hdr : (oldHeaders B x.2).h6=true)
    (V : LongDoorGuard.valid manifest x.2.long=true)
    (ph : (ctrlPhase.read x.2.long).toNat=2)
    (pc : (ctrlOp.read x.2.long).toNat=op)
    (R : bind (longGeometry B x.2) 0 (atSite x.2.long 0)=.reply f)
    (F : f.fault=0) (O : f.opcode.toNat=op)
    (N : (arithKind op).isSome=false)
    (q : Patch LW) (Q : afterReply op f x.2.long=q)
    (b : BitVec 2 → BitVec 2)
    (fr : ∀ y, choice.read (q.apply y)=b (choice.read y) ∧
      sourceDescriptor.read (q.apply y)=sourceDescriptor.read y) :
    choice.read (largePair B x).2.long=b (choice.read x.2.long) ∧
      sourceDescriptor.read (largePair B x).2.long=sourceDescriptor.read x.2.long := by
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have E := reply_work g raw f hdr V ph op pc R F O N
  have Q' : afterReply op f raw.2=q := Q
  rw [Q'] at E
  constructor
  · rw [joined_right_field hp x V choice (by decide)]
    exact door_field choice (by decide) (by decide) g raw hdr q E b (fun y => (fr y).1)
  · rw [joined_right_field hp x V sourceDescriptor (by decide)]
    exact door_field sourceDescriptor (by decide) (by decide) g raw hdr q E id (fun y => (fr y).2)

/-- The two genuinely selected receipt types instantiate the same joined old-row projection. -/
inductive ChoiceReply (op : Nat) (f : Payload) (d : Desc) : Fin 3 → Prop where
  | sealCase (opcode : op=sealOp) (need : d.need=false) (parity : f.argument.toNat%2≠1) :
      ChoiceReply op f d d.b0
  | bit (opcode : op=bitOp) (need : d.need=true) : ChoiceReply op f d (pick d f)

theorem receipt_selects_bank (x : Pair (LargeSite A)) (f : Payload) (op : Nat) (d : Desc) (b : Fin 3)
    (hdr : (oldHeaders B x.2).h6=true)
    (V : LongDoorGuard.valid manifest x.2.long=true)
    (ph : (ctrlPhase.read x.2.long).toNat=2)
    (pc : (ctrlOp.read x.2.long).toNat=op)
    (R : bind (longGeometry B x.2) 0 (atSite x.2.long 0)=.reply f)
    (F : f.fault=0) (O : f.opcode.toNat=op)
    (D : BStarLongPublication.decode (sourceDescriptor.read x.2.long)=some d)
    (caseOf : ChoiceReply op f d b) :
    choice.read (largePair B x).2.long=BitVec.ofNat 2 b.val ∧
      sourceDescriptor.read (largePair B x).2.long=sourceDescriptor.read x.2.long := by
  cases caseOf with
  | sealCase E need parity =>
    exact joined_choice_receipt hp x f sealOp hdr V ph (pc.trans E) R F (O.trans E) (by decide) _
      (seal_no_need_schedules_commit _ f d D need parity) (fun _ => BitVec.ofNat 2 d.b0.val)
      (select_projection commitOp d.b0)
  | bit E need =>
    exact joined_choice_receipt hp x f bitOp hdr V ph (pc.trans E) R F (O.trans E) (by decide) _
      (bit_schedules_commit _ f d D need) (fun _ => BitVec.ofNat 2 (pick d f).val) (bit_projection f d)

theorem seal_requests_bit (x : Pair (LargeSite A)) (f : Payload) (d : Desc)
    (hdr : (oldHeaders B x.2).h6=true)
    (V : LongDoorGuard.valid manifest x.2.long=true)
    (ph : (ctrlPhase.read x.2.long).toNat=2)
    (pc : (ctrlOp.read x.2.long).toNat=sealOp)
    (R : bind (longGeometry B x.2) 0 (atSite x.2.long 0)=.reply f)
    (F : f.fault=0) (O : f.opcode.toNat=sealOp)
    (D : BStarLongPublication.decode (sourceDescriptor.read x.2.long)=some d)
    (need : d.need=true) (parity : f.argument.toNat%2=1) :
    choice.read (largePair B x).2.long=choice.read x.2.long ∧
      sourceDescriptor.read (largePair B x).2.long=sourceDescriptor.read x.2.long := by
  exact joined_choice_receipt hp x f sealOp hdr V ph pc R F O (by decide) _
    (seal_need_schedules_bit _ f d D need parity) id
    (fun y => ⟨field_hold _ _ _ (schedule_frame bitOp) (by decide) (by decide),
      field_hold _ _ _ (schedule_frame bitOp) (by decide) (by decide)⟩)

/-- BIT issue and intervening old WAIT F/T cannot replace either
source-file value. No matching receipt or restart is classified here. -/
theorem bit_flight (x : Pair (LargeSite A))
    (hdr : (oldHeaders B x.2).h6=true)
    (V : LongDoorGuard.valid manifest x.2.long=true)
    (pc : (ctrlOp.read x.2.long).toNat=bitOp)
    (good : let k := bind (longGeometry B x.2) 0 (atSite x.2.long 0)
      ((ctrlPhase.read x.2.long).toNat=1 ∧ ∃ a, initial bitOp x.2.long=some a) ∨
      ((ctrlPhase.read x.2.long).toNat=2 ∧ (k=.trail ∨ ∃ q,k=.forward q))) :
    choice.read (largePair B x).2.long=choice.read x.2.long ∧
      sourceDescriptor.read (largePair B x).2.long=sourceDescriptor.read x.2.long := by
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let k := bind g.2 0 (atSite raw.2 0)
  have VV : LongDoorGuard.valid manifest raw.2=true := V
  have PC : (ctrlOp.read raw.2).toNat=bitOp := pc
  have decision : oldDoor raw.2 k=.hold ∨ ∃ a,oldDoor raw.2 k=.write (issued bitOp a) := by
    change ((ctrlPhase.read raw.2).toNat=1 ∧ ∃ a, initial bitOp raw.2=some a) ∨
      ((ctrlPhase.read raw.2).toNat=2 ∧ (k=.trail ∨ ∃ q,k=.forward q)) at good
    rcases good with ⟨P,a,H⟩|⟨P,T⟩
    · exact .inr ⟨a,by simp [oldDoor,VV,PC,P,H]⟩
    · rcases T with E|⟨q,E⟩
      · exact .inl (E ▸ wait_holds_trail _ VV P)
      · exact .inl (E ▸ wait_holds_forward _ q VV P)
  have H := long_work_frame g raw true hdr (by
    rintro ⟨C,t⟩ O ⟨v,rfl⟩ w hw _
    have M : (C,.door v)∈(actualOffers g raw).filter BStarDoorUnique.doorAction :=
      List.mem_filter.mpr ⟨O,rfl⟩
    rw [BStarDoorUnique.actual_door_singleton g raw hdr] at M
    obtain ⟨rfl,E⟩ := Prod.mk.inj (List.mem_singleton.mp M)
    have T := Offer.door.inj E
    change v=k at T
    subst v
    change w∈(match oldDoor raw.2 k with
      | .hold => (⟨[],[],[]⟩ : Selected)
      | .write q => ⟨[],[(true,q)],[]⟩
      | .acceptTour op p => ⟨[],[(true,BStarLongArithmetic.acceptFile raw.2 op p)],[]⟩).work at hw
    rcases decision with E|⟨a,E⟩
    · simp [E] at hw
    · rw [E] at hw
      obtain rfl := List.mem_singleton.mp hw
      have eq : (bitOp==1)=false := by decide
      simp only [issued,eq,Bool.false_eq_true,if_false]
      exact compose (assign _ _ (.inr (by decide))) (assign _ _ (.inl (by decide))))
  rw [joined_right_field hp x V choice (by decide),
    joined_right_field hp x V sourceDescriptor (by decide)]
  exact ⟨field_hold _ _ _ H (by decide) (by decide),
    field_hold _ _ _ H (by decide) (by decide)⟩

/-- The descriptor and low two bank bits of a genuine COMMIT launch
are exactly the old source-file values; the old branch choice gates issue. -/
theorem launched_commit (old new : BitVec LW) (d : Desc) (i : Fin 3)
    (pc : (ctrlOp.read old).toNat=commitOp)
    (D : BStarLongPublication.decode (sourceDescriptor.read old)=some d)
    (bank : choice.read old=BitVec.ofNat 2 i.val)
    (L : ∃ a, initial (ctrlOp.read old).toNat old=some a ∧
      snapshot new=((forward (ctrlOp.read old).toNat a,2),ctrlOp.read old)) :
    ∃ p, atSite new 0=.forward p ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/4))=some d ∧
      p.argument.toNat%4=i.val := by
  obtain ⟨arg,H,E⟩ := L
  rw [pc,commit_initial,D] at H
  change (if Allows old d then some (argument old) else none)=some arg at H
  split at H
  · have Y : argument old=arg := Option.some.inj H
    let p : Payload := ⟨0,BitVec.ofNat 9 commitOp,0,0,BitVec.ofNat 34 (argument old)⟩
    rw [pc,←Y] at E
    refine ⟨p,congrArg (fun q => q.1.1) E,?_,?_⟩
    · change BStarLongPublication.decode (BitVec.ofNat 7 ((BitVec.ofNat 34 (argument old)).toNat/4))=some d
      rw [(issued_argument old).1,show BitVec.ofNat 7 (sourceDescriptor.read old).toNat=sourceDescriptor.read old by simp]
      exact D
    · change (BitVec.ofNat 34 (argument old)).toNat%4=i.val
      rw [(issued_argument old).2,bank,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      exact Nat.lt_trans i.isLt (by decide)
  · contradiction

/-- The literal chosen right door really emits the bank/descriptor
packet, without a caller-supplied launch predicate. -/
theorem joined_commit (x : Pair (LargeSite A)) (d : Desc) (i : Fin 3)
    (hdr : (oldHeaders B x.2).h6=true)
    (V : LongDoorGuard.valid manifest x.2.long=true)
    (phase : (ctrlPhase.read x.2.long).toNat=1)
    (pc : (ctrlOp.read x.2.long).toNat=commitOp)
    (D : BStarLongPublication.decode (sourceDescriptor.read x.2.long)=some d)
    (bank : choice.read x.2.long=BitVec.ofNat 2 i.val)
    (perm : i=d.b0 ∨ (d.need=true ∧ i=d.b1)) :
    ∃ p, atSite (largePair B x).2.long 0=.forward p ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/4))=some d ∧
      p.argument.toNat%4=i.val := by
  let old : BitVec LW := x.2.long
  let new : BitVec LW := (largePair B x).2.long
  have L : (choice.read old).toNat=i.val := by
    change (choice.read x.2.long).toNat=i.val
    rw [bank,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    exact Nat.lt_trans i.isLt (by decide)
  have allowed : Allows old d=true := by
    unfold Allows
    rw [L]
    rcases perm with E|⟨N,E⟩ <;> simp [E]
    exact Or.inr N
  have op : (ctrlOp.read old).toNat=commitOp := pc
  have DD : BStarLongPublication.decode (sourceDescriptor.read old)=some d := D
  have H : initial (ctrlOp.read old).toNat old=some (argument old) := by
    rw [op,commit_initial,DD]
    simp [allowed]
  have Y := exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x hdr V phase
  change snapshot new=(match initial (ctrlOp.read old).toNat old with
    | none => ((.empty,1),0)
    | some a => ((forward (ctrlOp.read old).toNat a,2),ctrlOp.read old)) at Y
  rw [H] at Y
  exact launched_commit old new d i op DD bank ⟨_,H,Y⟩

/-- On an outgoing mark of the source header its left long endpoint
may route arbitrary foreign work but cannot accept a source door. -/
theorem left_foreign_field (x : Pair (LargeSite A))
    (hdr : (oldHeaders B x.1).h6=true)
    {m : Nat} (field : Field LW m) (lo : 2133≤field.offset) (hi : field.offset+m≤2195) :
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
seven descriptor bits and its choice. -/
theorem foreign_mark (x : Fin n → LargeSite A) (i e : Fin n)
    (ex : rightNeighbor e≠i)
    (hdr : oldH6 B x i=true) :
    let y := AllSizeS1Geometry.step B x e
    sourceDescriptor.read (y i).long=sourceDescriptor.read (x i).long ∧
      choice.read (y i).long=choice.read (x i).long := by
  dsimp only
  by_cases E : i=e
  · subst i
    simp only [AllSizeS1Geometry.step,if_true]
    let pair := (x e,x (rightNeighbor e))
    have H : (oldHeaders B pair.1).h6=true := hdr
    exact ⟨left_foreign_field hp pair H sourceDescriptor (by decide) (by decide),
      left_foreign_field hp pair H choice (by decide) (by decide)⟩
  · simp only [AllSizeS1Geometry.step,if_neg E,if_neg (Ne.symm ex),and_self]


/-- Arbitrarily many interleaved marks, none acting at the source door.
The source must still be an old H6 at each actual mark (e.g. fixed Layout). -/
theorem foreign_word (x : Fin n → LargeSite A) (i : Fin n) (w : List (Fin n))
    (foreign : ∀ e∈w, rightNeighbor e≠i)
    (header : ∀ u e v, w=u++e::v →
      oldH6 B (BStarResetSchedule.run (AllSizeS1Geometry.step B) x u) i=true) :
    let y := BStarResetSchedule.run (AllSizeS1Geometry.step B) x w
    sourceDescriptor.read (y i).long=sourceDescriptor.read (x i).long ∧
      choice.read (y i).long=choice.read (x i).long := by
  induction w generalizing x with
  | nil => exact ⟨rfl,rfl⟩
  | cons e w ih =>
    have S := foreign_mark hp x i e (foreign e List.mem_cons_self) (header [] e w rfl)
    have T := ih (AllSizeS1Geometry.step B x e)
      (fun f H => foreign f (List.mem_cons_of_mem _ H))
      (fun a f b E => header (e::a) f b (congrArg (List.cons e) E))
    exact ⟨T.1.trans S.1,T.2.trans S.2⟩


#print axioms bit_flight
#print axioms joined_commit
#print axioms receipt_selects_bank
#print axioms foreign_word
#print axioms joined_choice_receipt
#print axioms launched_commit
end L4.BStarCommitChoiceHistory
