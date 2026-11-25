import Leader.L4.BStarCommitChoiceHistory
import Leader.L4.BStarGeneratedPCAncestry

namespace L4.BStarCommitGeneratedTail
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongLayout
open BStarLongDoor BStarLongCommand BStarCommitIssue BStarCommitChoiceHistory
open BStarGeneratedOwner BStarGeneratedPCAncestry BStarAcquireVisitOrder BStarLiteralPC
open BStarH6WordChart BStarResetControllerProgress BStarCommitChoiceFrame
open BStarLongClaims BStarLongEvents BStarLongTransport
open BStarResetMarkAdapter BStarSeparatorControl BStarAcquireForwardTrace

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

private theorem at_owner_door {addr : Nat → Pos n} {len op : Nat} {x : X} {e : Fin n}
    (evt : Event hp addr len x e (.busy op (.back 0)) .idle) :
    rightNeighbor e=(addr 0).1 := by
  cases evt with
  | consume _ E _ =>
    rw [E]
    exact RearTrace.right_predecessor _

/-- The final-tail owner consume acts on the same bound old reply and
physical source as the generated-owner event. -/
theorem consume_tail {base x : X} {addr : Nat → Pos n} {len op : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy op (.back 0)))
    (evt : Event hp addr len x e (.busy op (.back 0)) .idle)
    (go : let pc := (ctrlOp.read (step x e (addr 0).1).long).toNat
      pc=409 ∨ pc=410 ∨ pc=411) :
    let a := (addr 0).1
    let old := (x a).long
    let fresh := (step x e a).long
    rightNeighbor e=a ∧ ∃ f,
      bind (longGeometry B (x a)) 0 (atSite old 0)=.reply f ∧
      f.fault=0 ∧ f.opcode.toNat=op ∧
      (ctrlOp.read fresh).toNat=pcNext old f ∧
      ((ctrlOp.read fresh).toNat=409 → op=408) ∧
      ((ctrlOp.read fresh).toNat=410 → op=409) ∧
      ((ctrlOp.read fresh).toNat=411 → op=409 ∨ op=410) := by
  dsimp only at go ⊢
  obtain ⟨f,R,N⟩ := consume_pc hp H hh sep cur evt
  have A := next_publication_tail _ f (N ▸ go)
  have opE := cur.1.2.2.2
  have Match := (congrArg BitVec.toNat A.2.1).trans opE
  refine ⟨at_owner_door hp evt,f,R,A.1,Match,N,?_,?_,?_⟩
  · intro P
    exact opE.symm.trans (A.2.2.1 (N.symm.trans P))
  · intro P
    exact opE.symm.trans (A.2.2.2.1 (N.symm.trans P))
  · intro P
    exact (A.2.2.2.2 (N.symm.trans P)).imp (opE.symm.trans) (opE.symm.trans)

theorem seal_pc (x : BitVec LW) (f : Payload) (d : Desc)
    (pc : (ctrlOp.read x).toNat=409) (F : f.fault=0) (O : f.opcode.toNat=409)
    (D : BStarLongPublication.decode (sourceDescriptor.read x)=some d) :
    pcNext x f=(if (f.argument.toNat%2==1) != d.need then 0
      else if f.argument.toNat%2=1 then 410 else 411) := by
  simp only [pcNext,pc,F,O,bne_self_eq_false,Bool.false_or,Bool.false_eq_true,if_false]
  change nextOrdinary x 409 f=_
  simp [nextOrdinary,D,beq_iff_eq]

theorem bit_pc (x : BitVec LW) (f : Payload) (d : Desc)
    (pc : (ctrlOp.read x).toNat=410) (F : f.fault=0) (O : f.opcode.toNat=410)
    (D : BStarLongPublication.decode (sourceDescriptor.read x)=some d) :
    pcNext x f=(if !d.need then 0 else 411) := by
  simp only [pcNext,pc,F,O,bne_self_eq_false,Bool.false_or,Bool.false_eq_true,if_false]
  change nextOrdinary x 410 f=_
  simp [nextOrdinary,D]


private theorem stageSchedule (op : Nat) : Frame (schedule op) := by
  unfold schedule setToken
  exact compose (compose (assign _ _ (Or.inr (by decide))) (assign _ _ (Or.inr (by decide))))
    (assign _ _ (Or.inl (by decide)))

/-- The real final-tail consume keeps its old descriptor. If the new
PC is COMMIT, its choice follows the actual bound generated reply. -/
theorem selected_tail_result {base x : X} {addr : Nat → Pos n} {len op : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy op (.back 0)))
    (evt : Event hp addr len x e (.busy op (.back 0)) .idle)
    (d : Desc)
    (D : BStarLongPublication.decode (sourceDescriptor.read (x (addr 0).1).long)=some d)
    (go : let pc := (ctrlOp.read (step x e (addr 0).1).long).toNat
      pc=409 ∨ pc=410 ∨ pc=411) :
    let a := (addr 0).1
    let old := (x a).long
    let fresh := (step x e a).long
    sourceDescriptor.read fresh=sourceDescriptor.read old ∧
    ∃ f, bind (longGeometry B (x a)) 0 (atSite old 0)=.reply f ∧
      ((ctrlOp.read fresh).toNat=411 →
        (op=409 ∧ d.need=false ∧ f.argument.toNat%2≠1 ∧
          choice.read fresh=BitVec.ofNat 2 d.b0.val) ∨
        (op=410 ∧ d.need=true ∧ choice.read fresh=BitVec.ofNat 2 (pick d f).val)) := by
  dsimp only at go ⊢
  obtain ⟨E,f,R,F,O,N,J,K,L⟩ := consume_tail hp H hh sep cur evt go
  let a := (addr 0).1
  let old : BitVec LW := (x a).long
  let fresh : BitVec LW := (step x e a).long
  let pair := (x e,x (rightNeighbor e))
  have oldEq : (x (rightNeighbor e)).long=(x a).long := congrArg (fun i => (x i).long) E
  have oldHdr : (oldHeaders B pair.2).h6=true := by change oldH6 B x (rightNeighbor e)=true; rwa [E]
  have V : LongDoorGuard.valid manifest pair.2.long=true := by
    change LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true
    rw [oldEq]; exact cur.1.2.1
  have P : (ctrlPhase.read pair.2.long).toNat=2 := by
    change (ctrlPhase.read (x (rightNeighbor e)).long).toNat=2
    rw [oldEq]; exact cur.1.2.2.1
  have C : (ctrlOp.read pair.2.long).toNat=op := by
    change (ctrlOp.read (x (rightNeighbor e)).long).toNat=op
    rw [oldEq]; exact cur.1.2.2.2
  have DD : BStarLongPublication.decode (sourceDescriptor.read pair.2.long)=some d := by
    change BStarLongPublication.decode (sourceDescriptor.read (x (rightNeighbor e)).long)=some d
    rw [oldEq]; exact D
  have RR : bind (longGeometry B pair.2) 0 (atSite pair.2.long 0)=.reply f := by
    change bind (longGeometry B (x (rightNeighbor e))) 0 (atSite (x (rightNeighbor e)).long 0)=.reply f
    rwa [E]
  have newEq : (largePair B pair).2.long=fresh := by
    have S : step x e a=(largePair B pair).2 := by
      change step x e (addr 0).1=(largePair B pair).2; rw [←E]; simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
    exact (congrArg LargeSite.long S).symm
  have oldEq' : pair.2.long=old := oldEq
  have NC : (ctrlOp.read fresh).toNat=pcNext old f := N
  have oldPC : (ctrlOp.read old).toNat=op := cur.1.2.2.2
  change sourceDescriptor.read fresh=sourceDescriptor.read old ∧ _
  by_cases fin : (ctrlOp.read fresh).toNat=411
  · rcases L fin with opS|opB
    · have branch := seal_pc old f d (oldPC.trans opS) F (O.trans opS) D
      have M := NC.symm.trans fin
      rw [branch] at M
      have Hs : d.need=false ∧ f.argument.toNat%2≠1 := by
        cases h : d.need <;> by_cases parity : f.argument.toNat%2=1 <;>
          simp [h,parity] at M ⊢
      have t := receipt_selects_bank hp pair f op d d.b0 oldHdr V P C RR F O DD
        (.sealCase opS Hs.1 Hs.2)
      rw [newEq,oldEq'] at t
      exact ⟨t.2,f,R,fun _ => .inl ⟨opS,Hs.1,Hs.2,t.1⟩⟩
    · have branch := bit_pc old f d (oldPC.trans opB) F (O.trans opB) D
      have M := NC.symm.trans fin
      rw [branch] at M
      have Hs : d.need=true := by cases q : d.need <;> simp [q] at M ⊢
      have t := receipt_selects_bank hp pair f op d (pick d f) oldHdr V P C RR F O DD
        (.bit opB Hs)
      rw [newEq,oldEq'] at t
      exact ⟨t.2,f,R,fun _ => .inr ⟨opB,Hs,t.1⟩⟩
  · rcases go with toSeal|toBit|bad
    · have opS := J toSeal
      have W : afterReply op f pair.2.long=schedule 409 := by
        rw [opS]; rfl
      have t := joined_choice_receipt hp pair f op oldHdr V P C RR F O
        (opS.symm ▸ (by decide : (arithKind 408).isSome=false)) _ W id
        (fun y => ⟨field_hold _ _ _ (stageSchedule 409) (by decide) (by decide),
          field_hold _ _ _ (stageSchedule 409) (by decide) (by decide)⟩)
      rw [newEq,oldEq'] at t
      exact ⟨t.2,f,R,fun bad => (fin bad).elim⟩
    · have opS := K toBit
      have branch := seal_pc old f d (oldPC.trans opS) F (O.trans opS) D
      have M := NC.symm.trans toBit
      rw [branch] at M
      have Hs : d.need=true ∧ f.argument.toNat%2=1 := by
        cases h : d.need <;> by_cases parity : f.argument.toNat%2=1 <;>
          simp [h,parity] at M ⊢
      have t := seal_requests_bit hp pair f d oldHdr V P (C.trans opS) RR F (O.trans opS) DD Hs.1 Hs.2
      rw [newEq,oldEq'] at t
      exact ⟨t.2,f,R,fun bad => (fin bad).elim⟩
    · exact (fin bad).elim

private theorem local_right_field (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
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

/-- An issue other than CLEAR and intervening old WAIT F/T cannot replace either
source-file value. No matching receipt or restart is classified here. -/
theorem source_flight (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (hdr : (oldHeaders B x.2).h6=true)
    (V : LongDoorGuard.valid manifest x.2.long=true)
    (op : Nat) (notClear : op≠1)
    (pc : (ctrlOp.read x.2.long).toNat=op)
    (good : let k := bind (longGeometry B x.2) 0 (atSite x.2.long 0)
      ((ctrlPhase.read x.2.long).toNat=1 ∧ ∃ a, initial op x.2.long=some a) ∨
      ((ctrlPhase.read x.2.long).toNat=2 ∧ (k=.trail ∨ ∃ q,k=.forward q))) :
    choice.read (largePair B x).2.long=choice.read x.2.long ∧
      sourceDescriptor.read (largePair B x).2.long=sourceDescriptor.read x.2.long := by
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let k := bind g.2 0 (atSite raw.2 0)
  have VV : LongDoorGuard.valid manifest raw.2=true := V
  have PC : (ctrlOp.read raw.2).toNat=op := pc
  have decision : oldDoor raw.2 k=.hold ∨ ∃ a,oldDoor raw.2 k=.write (issued op a) := by
    change ((ctrlPhase.read raw.2).toNat=1 ∧ ∃ a, initial op raw.2=some a) ∨
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
      have eq : (op==1)=false := beq_eq_false_iff_ne.mpr notClear
      simp only [issued,eq,Bool.false_eq_true,if_false]
      exact compose (assign _ _ (.inr (by decide))) (assign _ _ (.inl (by decide))))
  rw [local_right_field hp x V choice (by decide),
    local_right_field hp x V sourceDescriptor (by decide)]
  exact ⟨field_hold _ _ _ H (by decide) (by decide),
    field_hold _ _ _ H (by decide) (by decide)⟩


/-- The literal old source is bound F/T throughout a generated transit
before its back-zero receipt. -/
private theorem transit_old_class {addr : Nat → Pos n} {len : Nat} {x : X}
    {z : BStarSeparatingRail.Cursor} (H : (addr 0).2=0)
    (G : BStarSeparatingRail.Good anyTag len (project addr x) z) (live : z≠.back 0) :
    let a := (addr 0).1
    let g := longGeometry B (x a)
    let k := bind g 0 (atSite (x a).long 0)
    k=.trail ∨ ∃ q,k=.forward q := by
  have at0 : project addr x 0=atSite (x (addr 0).1).long 0 := by
    unfold project atCursor
    rw [H]
    rfl
  cases z with
  | out j =>
    cases j with
    | zero =>
      obtain ⟨f,F⟩ := G.2.1
      rw [at0] at F
      exact .inr (F.symm ▸ bound_F _ _ f)
    | succ j =>
      have T := G.2.2 0 (Nat.zero_lt_succ j)
      rw [at0] at T
      exact .inl (T.symm ▸ rfl)
  | back j =>
    cases j with
    | zero => exact (live rfl).elim
    | succ j =>
      have T := G.2.2.1 0 (Nat.zero_lt_succ j)
      rw [at0] at T
      exact .inl (T.symm ▸ rfl)

/-- Same-word frame for actual generated non-consuming events. In
particular arbitrary foreign interleavings and source-owner transit
do not alter the descriptor. A rejected issue is not a successful flight. -/
theorem generated_flight {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {u v : Mode} (H : (addr 0).2=0) (hh : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x u) (evt : Event hp addr len x e u v)
    (notClear : (ctrlOp.read (x (addr 0).1).long).toNat≠1)
    (casesOK : ¬(u=.idle ∧ v=.idle ∧ rightNeighbor e=(addr 0).1))
    (notConsume : ∀ op, u≠.busy op (.back 0) ∨ v≠.idle) :
    let a := (addr 0).1
    choice.read (step x e a).long=choice.read (x a).long ∧
      sourceDescriptor.read (step x e a).long=sourceDescriptor.read (x a).long := by
  dsimp only
  by_cases E : rightNeighbor e=(addr 0).1
  · let pair := (x e,x (rightNeighbor e))
    have EQ : step x e (addr 0).1=(largePair B pair).2 := by
      rw [←E]; simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
    rw [EQ,←E]
    have HH : (oldHeaders B pair.2).h6=true := by change oldH6 B x (rightNeighbor e)=true; rwa [E]
    let old : BitVec LW := (x (addr 0).1).long
    let k := bind (longGeometry B (x (addr 0).1)) 0 (atSite old 0)
    have facts : LongDoorGuard.valid manifest old=true ∧
        (((ctrlPhase.read old).toNat=1 ∧ ∃ a, initial (ctrlOp.read old).toNat old=some a) ∨
          ((ctrlPhase.read old).toNat=2 ∧ (k=.trail ∨ ∃ q,k=.forward q))) := by
      cases evt with
      | idle_hold _ => exact (casesOK ⟨rfl,rfl,E⟩).elim
      | bad_issue _ _ => exact (casesOK ⟨rfl,rfl,E⟩).elim
      | launch _ L =>
        obtain ⟨A,a,W,_⟩ := L
        exact ⟨A.1,.inl ⟨A.2,a,W⟩⟩
      | transit op z _ live _ =>
        exact ⟨cur.1.2.1,.inr ⟨cur.1.2.2.1,transit_old_class hp H cur.2.1 live⟩⟩
      | arrived_hold _ ne =>
        have key : e=RearTrace.predecessor (addr 0).1 := by
          rw [←E,RearTrace.predecessor_right]
        exact (ne key).elim
      | consume op _ _ => exact ((notConsume op).elim (fun z => z rfl) (fun z => z rfl)).elim
    have N : (ctrlOp.read pair.2.long).toNat≠1 := by
      change (ctrlOp.read (x (rightNeighbor e)).long).toNat≠1
      rw [E]; exact notClear
    let good (site : Fin n) : Prop :=
      let raw : BitVec LW := (x site).long
      let token := bind (longGeometry B (x site)) 0 (atSite raw 0)
      ((ctrlPhase.read raw).toNat=1 ∧ ∃ a, initial (ctrlOp.read raw).toNat raw=some a) ∨
      ((ctrlPhase.read raw).toNat=2 ∧ (token=.trail ∨ ∃ q,token=.forward q))
    have W : good (rightNeighbor e) := E.symm ▸ (show good _ from facts.2)
    have VV : LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true := by rw [E]; exact facts.1
    exact source_flight hp pair HH VV _ N rfl W
  · have F := foreign_mark hp x (addr 0).1 e E hh
    exact ⟨F.2,F.1⟩

/-- A finite tape before the bank-selecting receipt. The caller supplies
only accepted PC labels and actual generated events, not file equality. -/
inductive BeforeChoice (base : X) (addr : Nat → Pos n) (len : Nat) : X → List (Fin n) → Prop where
  | nil (x : X) : BeforeChoice base addr len x []
  | flight {x : X} {e : Fin n} {w : List (Fin n)} {u v : Mode}
      (header : oldH6 B x (addr 0).1=true) (sep : e≠rightNeighbor e)
      (cur : Current hp base addr len x u) (evt : Event hp addr len x e u v)
      (nonClear : (ctrlOp.read (x (addr 0).1).long).toNat≠1)
      (notBad : ¬(u=.idle ∧ v=.idle ∧ rightNeighbor e=(addr 0).1))
      (notConsume : ∀ op, u≠.busy op (.back 0) ∨ v≠.idle)
      (rest : BeforeChoice base addr len (step x e) w) :
      BeforeChoice base addr len x (e::w)
  | consume {x : X} {e : Fin n} {w : List (Fin n)} {op : Nat}
      (header : oldH6 B x (addr 0).1=true) (sep : e≠rightNeighbor e)
      (cur : Current hp base addr len x (.busy op (.back 0)))
      (evt : Event hp addr len x e (.busy op (.back 0)) .idle)
      (advance : let pc := (ctrlOp.read (step x e (addr 0).1).long).toNat
        pc=409 ∨ pc=410)
      (rest : BeforeChoice base addr len (step x e) w) :
      BeforeChoice base addr len x (e::w)

local notation "run" => BStarResetSchedule.run step

theorem before_choice_descriptor {base x : X} {addr : Nat → Pos n} {len : Nat}
    {w : List (Fin n)} (k0 : (addr 0).2=0) (d : Desc)
    (D : BStarLongPublication.decode (sourceDescriptor.read (x (addr 0).1).long)=some d)
    (T : BeforeChoice hp base addr len x w) :
    sourceDescriptor.read ((run x w) (addr 0).1).long=
      sourceDescriptor.read (x (addr 0).1).long := by
  induction T with
  | nil => rfl
  | flight h sep cur evt c b t _ ih =>
    have E := (generated_flight hp k0 h sep cur evt c b t).2
    exact (ih (congrArg BStarLongPublication.decode E |>.trans D)).trans E
  | consume h sep cur evt a _ ih =>
    have E := (selected_tail_result hp k0 h sep cur evt d D
      (a.imp id Or.inl)).1
    exact (ih (congrArg BStarLongPublication.decode E |>.trans D)).trans E

/-- Physical generated receipt-to-issue suffix: the bank is chosen by
the bound SEAL/BIT reply, then both fields survive arbitrary foreign
marks up to the first actual legal COMMIT issue at that same door. -/
theorem receipt_to_commit {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {e : Fin n} (k0 : (addr 0).2=0) (hh : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy op (.back 0)))
    (evt : Event hp addr len x e (.busy op (.back 0)) .idle)
    (d : Desc)
    (D : BStarLongPublication.decode (sourceDescriptor.read (x (addr 0).1).long)=some d)
    (nextCommit : (ctrlOp.read (step x e (addr 0).1).long).toNat=411)
    (w : List (Fin n))
    (foreign : ∀ m∈w, rightNeighbor m≠(addr 0).1)
    (header : ∀ pre m tail,w=pre++m::tail →
      oldH6 B (run (step x e) pre) (addr 0).1=true)
    (lastHeader : oldH6 B (run (step x e) w) (addr 0).1=true)
    (lastV : LongDoorGuard.valid manifest ((run (step x e) w) (addr 0).1).long=true)
    (phase : (ctrlPhase.read ((run (step x e) w) (addr 0).1).long).toNat=1)
    (pc : (ctrlOp.read ((run (step x e) w) (addr 0).1).long).toNat=commitOp) :
    let a := (addr 0).1
    let z := run (step x e) w
    ∃ f p bank, bind (longGeometry B (x a)) 0 (atSite (x a).long 0)=.reply f ∧
      ((op=409 ∧ d.need=false ∧ f.argument.toNat%2≠1 ∧ bank=d.b0) ∨
        (op=410 ∧ d.need=true ∧ bank=pick d f)) ∧
      atSite (step z e a).long 0=.forward p ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/4))=some d ∧
      p.argument.toNat%4=bank.val := by
  dsimp only
  have E := at_owner_door hp evt
  obtain ⟨retained,f,R,choose⟩ := selected_tail_result hp k0 hh sep cur evt d D (.inr (.inr nextCommit))
  have F := foreign_word hp (step x e) (addr 0).1 w foreign header
  let z := run (step x e) w
  let pair := (z e,z (rightNeighbor e))
  have actual : step z e (addr 0).1=(largePair B pair).2 := by
    rw [←E]; simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
  have hdr : (oldHeaders B pair.2).h6=true := by change oldH6 B z (rightNeighbor e)=true; rwa [E]
  let old : BitVec LW := (z (addr 0).1).long
  have source : pair.2.long=old := congrArg (fun i => (z i).long) E
  have H : BStarLongPublication.decode (sourceDescriptor.read pair.2.long)=some d := by
    rw [source]
    exact (congrArg BStarLongPublication.decode (F.1.trans retained)).trans D
  have VP : LongDoorGuard.valid manifest pair.2.long=true := by rw [source]; exact lastV
  have PP : (ctrlPhase.read pair.2.long).toNat=1 := by rw [source]; exact phase
  have PC : (ctrlOp.read pair.2.long).toNat=commitOp := by rw [source]; exact pc
  have issue (b : Fin 3)
      (bank : choice.read (step x e (addr 0).1).long=BitVec.ofNat 2 b.val)
      (perm : b=d.b0 ∨ (d.need=true ∧ b=d.b1)) :
      ∃ p, atSite (step z e (addr 0).1).long 0=.forward p ∧
        BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/4))=some d ∧
        p.argument.toNat%4=b.val := by
    have bank' : choice.read pair.2.long=BitVec.ofNat 2 b.val := by
      rw [source]
      exact F.2.trans bank
    rw [actual]
    exact joined_commit hp pair d b hdr VP PP PC H bank' perm
  rcases choose nextCommit with ⟨C,N,P,Bank⟩|⟨C,N,Bank⟩
  · obtain ⟨p,T,S,Q⟩ := issue d.b0 Bank (.inl rfl)
    exact ⟨f,p,d.b0,R,.inl ⟨C,N,P,rfl⟩,T,S,Q⟩
  · have perm : pick d f=d.b0 ∨ (d.need=true ∧ pick d f=d.b1) := by
      unfold pick
      split
      · exact .inr ⟨N,rfl⟩
      · exact .inl rfl
    obtain ⟨p,T,S,Q⟩ := issue (pick d f) Bank perm
    exact ⟨f,p,pick d f,R,.inr ⟨C,N,rfl⟩,T,S,Q⟩

#print axioms receipt_to_commit
#print axioms before_choice_descriptor
#print axioms generated_flight
#print axioms source_flight
#print axioms consume_tail
#print axioms selected_tail_result
end L4.BStarCommitGeneratedTail
