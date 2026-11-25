import Leader.L4.BStarAttemptCuts
import Leader.L4.BStarCommitOwnerOrigin

namespace L4.BStarCommitReceiptAuth
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongLayout BStarLongCommand
open BStarLongDoor BStarH6WordChart BStarAcquireVisitOrder BStarCommitChoiceHistory
open BStarCommitGeneratedTail BStarGeneratedOwner BStarGeneratedPCAncestry
open BStarLiteralPC BStarResetControllerProgress BStarCommitChoiceFrame
open BStarResetChartTouch BStarAcquireLiteralChain BStarLongFixedRouting
open BStarGeneratedTapeCuts BStarAcquireAnchors BStarCommitIssue

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarCommitTailScan.pc

private theorem no_desc_pc (x : BitVec LW) (f : Payload) (op : Nat)
    (old : (ctrlOp.read x).toNat=op)
    (F : f.fault=0) (O : f.opcode.toNat=op)
    (opS : op=409 ∨ op=410)
    (D : BStarLongPublication.decode (sourceDescriptor.read x)=none) : pcNext x f=0 := by
  rcases opS with rfl|rfl <;>
    simp only [pcNext,old,F,O,bne_self_eq_false,Bool.false_or,Bool.false_eq_true,if_false]
  · change nextOrdinary x 409 f=0
    simp [nextOrdinary,D]
  · change nextOrdinary x 410 f=0
    simp [nextOrdinary,D]

private theorem schedule_desc (op : Nat) (x : BitVec LW) :
    sourceDescriptor.read ((schedule op).apply x)=sourceDescriptor.read x := by
  apply field_hold _ _ _ _ (by decide) (by decide)
  unfold schedule setToken
  exact compose (compose (assign _ _ (Or.inr (by decide))) (assign _ _ (Or.inr (by decide))))
    (assign _ _ (Or.inl (by decide)))

/-- The actual earlier pre-choice consumes retain descriptor *bytes*
without any valid-descriptor hypothesis. Only entrance into BIT has
a descriptor requirement; its successful PC supplies it. -/
theorem early_consume_descriptor {base x : X} {addr : Nat → Pos n} {len op : Nat} {e : Fin n}
    (K : (addr 0).2=0) (H : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x (.busy op (.back 0)))
    (E : Event hp addr len x e (.busy op (.back 0)) .idle)
    (pc' : pc (step x e) (addr 0).1=409 ∨ pc (step x e) (addr 0).1=410) :
    sourceDescriptor.read (step x e (addr 0).1).long=sourceDescriptor.read (x (addr 0).1).long := by
  let root := (addr 0).1
  obtain ⟨R,f,M,F,O,N,fromStage,fromSeal,_⟩ :=
    consume_tail hp K H sep I E (pc'.imp id Or.inl)
  let old : BitVec LW := (x root).long
  cases D : BStarLongPublication.decode (sourceDescriptor.read old) with
  | some d =>
    exact (selected_tail_result hp K H sep I E d D (pc'.imp id Or.inl)).1
  | none =>
    rcases pc' with A|A
    · have P := fromStage A
      let pair := (x e,x (rightNeighbor e))
      have newEq : step x e root=(largePair B pair).2 := by
        change step x e (addr 0).1=(largePair B pair).2
        rw [←R]; simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
      have hdr : (oldHeaders B pair.2).h6=true := by change oldH6 B x (rightNeighbor e)=true; rwa [R]
      let raw : BitVec LW := pair.2.long
      have rawOld : raw=old := congrArg (fun i => (x i).long) R
      have V : LongDoorGuard.valid manifest raw=true := by rw [rawOld]; exact I.1.2.1
      have phase : (ctrlPhase.read raw).toNat=2 := by rw [rawOld]; exact I.1.2.2.1
      have opcode : (ctrlOp.read raw).toNat=408 := by rw [rawOld]; exact I.1.2.2.2.trans P
      have reply : bind (longGeometry B pair.2) 0 (atSite raw 0)=.reply f := by
        change bind (longGeometry B (x (rightNeighbor e))) 0 (atSite (x (rightNeighbor e)).long 0)=.reply f
        rwa [R]
      have W : afterReply 408 f raw=schedule 409 := rfl
      have hold := (joined_choice_receipt hp pair f 408 hdr V phase opcode reply F (O.trans P)
        (by decide) _ W id (fun y => ⟨by
          unfold schedule setToken
          simp only [Patch.compose_apply]
          rw [Field.read_other_assign choice (kField 0) _ _ (.inr (by decide)),
            Field.read_other_assign choice ctrlOp _ _ (.inl (by decide)),
            Field.read_other_assign choice ctrlPhase _ _ (.inl (by decide))]
          rfl,
        schedule_desc 409 y⟩)).2
      change sourceDescriptor.read (largePair B pair).2.long=sourceDescriptor.read raw at hold
      rw [rawOld] at hold
      change sourceDescriptor.read (step x e root).long=sourceDescriptor.read old
      rw [newEq]; exact hold
    · have P := fromSeal A
      have Z := no_desc_pc old f op I.1.2.2.2 F O (.inl P) D
      exact (by
        change pc (step x e) root=pcNext old f at N
        change pc (step x e) root=410 at A
        omega)

theorem before_choice_bytes {base x : X} {addr : Nat → Pos n} {len : Nat}
    {w : List (Fin n)} (K : (addr 0).2=0)
    (T : BeforeChoice hp base addr len x w) :
    sourceDescriptor.read ((run x w) (addr 0).1).long=
      sourceDescriptor.read (x (addr 0).1).long := by
  induction T with
  | nil => rfl
  | flight h sep cur evt c b t _ ih =>
    exact ih.trans (generated_flight hp K h sep cur evt c b t).2
  | consume h sep cur evt a _ ih =>
    exact ih.trans (early_consume_descriptor hp K h sep cur evt a)

/-- A generated consume into 411 certifies that the *old* descriptor
decodes; neither a forged ready state nor a supplied bank is needed. -/
theorem selecting_has_descriptor {base x : X} {addr : Nat → Pos n} {len op : Nat} {e : Fin n}
    (K : (addr 0).2=0) (H : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x (.busy op (.back 0)))
    (E : Event hp addr len x e (.busy op (.back 0)) .idle)
    (pc' : pc (step x e) (addr 0).1=411) :
    ∃ d, BStarLongPublication.decode (sourceDescriptor.read (x (addr 0).1).long)=some d := by
  let old : BitVec LW := (x (addr 0).1).long
  obtain ⟨_,f,_,F,O,N,_,_,pre⟩ := consume_tail hp K H sep I E (.inr (.inr pc'))
  have P := pre pc'
  change pc (step x e) (addr 0).1=pcNext old f at N
  change ∃ d,BStarLongPublication.decode (sourceDescriptor.read old)=some d
  cases D : BStarLongPublication.decode (sourceDescriptor.read old) with
  | some d => exact ⟨d,rfl⟩
  | none =>
    have Z := no_desc_pc old f op I.1.2.2.2 F O P D
    omega

/-- The result of a bank-selecting receipt on the same attempt. The
BIT alternative refers to the actual returned parity rather than an
unconstrained bank choice read from the later source file. -/
def ReceiptBank (op : Nat) (d : Desc) (f : Payload) (bank : Fin 3) : Prop :=
  (op=409 ∧ d.need=false ∧ f.argument.toNat%2≠1 ∧ bank=d.b0) ∨
  (op=410 ∧ d.need=true ∧ bank=pick d f)

/-- From the real recovered generated tape to ready COMMIT, extract
its actual selecting receipt. The decoded descriptor is the same from
the 408 cut through the ready ISSUE411 bytes. -/
theorem at_ready_commit {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w .idle)
    (early : pc x (S.getD 0 fall).1<6)
    (last : pc (run x w) (S.getD 0 fall).1=411) :
    let root := (S.getD 0 fall).1
    ∃ (before408 beforePick afterPick : List (Fin n)) (select : Fin n)
      (op : Nat) (f : Payload) (d : Desc) (bank : Fin 3),
      w=before408++beforePick++select::afterPick ∧
      pc (run x before408) root=408 ∧
      (let y := run (run x before408) beforePick
       bind (longGeometry B (y root)) 0 (atSite (y root).long 0)=.reply f) ∧
      ReceiptBank op d f bank ∧
      BStarLongPublication.decode (sourceDescriptor.read ((run x before408) root).long)=some d ∧
      sourceDescriptor.read ((run x w) root).long=
        sourceDescriptor.read ((run x before408) root).long ∧
      choice.read ((run x w) root).long=BitVec.ofNat 2 bank.val := by
  dsimp only
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  obtain ⟨lead,mid,late,hold,accept,select,op,W,_,_,_,first,finish,mm,
      P408,_,_,T408,_,cur,ev,P411,_,_,foreign⟩ :=
    BStarAttemptCuts.attempt_cuts hp C Q I fiber closed sep T early last
  let preStage := lead++accept::first
  let half := run (step (run x lead) accept) first
  let y := run half finish
  have PH : run x preStage=half := by simp only [preStage,half,BStarResetSchedule.run_append]; rfl
  have WY : run x (preStage++finish)=y := by rw [BStarResetSchedule.run_append,PH]
  have WW : w=preStage++finish++select::hold := by
    rw [W,mm]
    simp only [preStage,List.append_assoc,List.cons_append]
  have YY : run x w=run (step y select) hold := by
    rw [WW,BStarResetSchedule.run_append]
    change run (step (run x (preStage++finish)) select) hold=_
    rw [WY]
  have A := root_cuts hp C Q I closed fiber (preStage++finish)
  rw [WY] at A
  have yh : oldH6 B y root=true := A.1
  obtain ⟨d,D⟩ := selecting_has_descriptor hp A.2 yh (sep select) cur ev P411
  obtain ⟨R,f,ret,choose⟩ := selected_tail_result hp A.2 yh (sep select) cur ev d D (.inr (.inr P411))
  have R0 := before_choice_bytes hp A.2 T408
  have EqFor (u : List (Fin n)) : run (step y select) u=run x ((preStage++finish)++select::u) := by
    rw [BStarResetSchedule.run_append,WY]; rfl
  have FH := foreign_word hp (step y select) root hold foreign
    (fun u _ _ _ => by rw [EqFor]; exact (root_cuts hp C Q I closed fiber _).1)
  have bitEq : sourceDescriptor.read ((run x w) root).long=
      sourceDescriptor.read ((run x preStage) root).long := by
    rw [YY,PH]
    exact FH.1.trans (R.trans R0)
  have descHalf : BStarLongPublication.decode (sourceDescriptor.read ((run x preStage) root).long)=some d := by
    rw [PH,←R0]
    exact D
  rcases choose P411 with ⟨a,b,c,ch⟩|⟨a,b,ch⟩
  · exact ⟨preStage,finish,hold,select,op,f,d,d.b0,WW,PH ▸ P408,PH ▸ ret,
      .inl ⟨a,b,c,rfl⟩,descHalf,bitEq,YY ▸ FH.2.trans ch⟩
  · exact ⟨preStage,finish,hold,select,op,f,d,pick d f,WW,PH ▸ P408,PH ▸ ret,
      .inr ⟨a,b,rfl⟩,descHalf,bitEq,YY ▸ FH.2.trans ch⟩

open BStarLongClaims BStarLongEvents BStarCommitLineage BStarCommitPayload

/-- The receipt choice is now tied to the old selected physical
COMMIT at the actual publication mark, not just to its source bytes. -/
theorem physical_commit_from_receipt {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (now : Current hp base (fun j => S.getD j fall) len (run x w) m)
    (early : pc x (S.getD 0 fall).1<6)
    (j : Nat) (hj : j≤len) (e : Fin n) (idx : S.getD j fall=(e,1)) (pub : Publication) :
    let state := run x w
    let g := oldPair B state e
    let raw := ((state e).long,(state (rightNeighbor e)).long)
    pub∈(longTrace g raw).publications →
    ∃ (sourceTape tour before408 beforePick afterPick : List (Fin n))
      (door selecting : Fin n) (op : Nat) (f : Payload) (d : Desc) (K : CommandClaim) (payload : Payload),
      w=sourceTape++door::tour ∧ sourceTape=before408++beforePick++selecting::afterPick ∧
      let root := (S.getD 0 fall).1
      let old := run x sourceTape
      let y := run (run x before408) beforePick
      door=RearTrace.predecessor root ∧
      BStarClearanceSource.Launch (old root).long (step old door root).long ∧
      pc old root=411 ∧ pc (run x before408) root=408 ∧
      bind (longGeometry B (y root)) 0 (atSite (y root).long 0)=.reply f ∧
      ReceiptBank op d f pub.bank ∧
      BStarLongPublication.decode (sourceDescriptor.read ((run x before408) root).long)=some d ∧
      sourceDescriptor.read (old root).long=sourceDescriptor.read ((run x before408) root).long ∧
      (K,.advance payload)∈actualOffers g raw ∧
      LiteralCommit (BStarLongCommand.geometry g K.source.side) K.source (atOld raw K.source) payload pub.bank ∧
      BStarLongPublication.decode (descriptorBits payload)=some d := by
  dsimp only
  intro on
  obtain ⟨_,pre,post,door,desc,W,doorEq,launch,PC,DD,_,bankEq,_,_,K,q,sel,lit,L⟩ :=
    BStarCommitOwnerOrigin.publication_from_generated hp C sep T now j hj e idx pub on
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  have full : GeneratedOwner hp base addr len x .idle (pre++door::post) m := W ▸ T
  obtain ⟨mode,tape,mark⟩ := BStarGeneratedTapeCuts.split hp pre (door::post) full
  have M := idle_of_issue hp (at_start hp mark) launch.1
  subst mode
  obtain ⟨before408,beforePick,afterPick,selecting,op,f,d,bank,Spl,Cut,reply,receipt,D,Bits,Choice⟩ :=
    at_ready_commit hp C Q I fiber closed sep tape early PC
  have code : BStarLongPublication.decode (sourceDescriptor.read ((run x pre) root).long)=some d :=
    (congrArg BStarLongPublication.decode Bits).trans D
  have same : desc=d := Option.some.inj (DD.symm.trans code)
  have ch := congrArg BitVec.toNat Choice
  have inRange : bank.val<2^2 := Nat.lt_trans bank.isLt (by decide)
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt inRange] at ch
  have bankSame : pub.bank=bank := Fin.ext (bankEq.symm.trans ch)
  exact ⟨pre,post,before408,beforePick,afterPick,door,selecting,op,f,d,K,q,W,Spl,doorEq,
    launch,PC,Cut,reply,bankSame.symm ▸ receipt,D,Bits,sel,lit,same ▸ L⟩

end L4.BStarCommitReceiptAuth
