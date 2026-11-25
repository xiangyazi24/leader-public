import Leader.L4.BStarNativeCommitHandoff
import Leader.L4.BStarBitParity

namespace L4.BStarBitSelectingTrace
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongDoor BStarLongLayout
open BStarLongCommand BStarLongEvents BStarLongClaims BStarCommitIssue
open BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarNativeActualLoadAccepted BStarCommitTailScan BStarCommitReceiptAuth
open BStarCommitGeneratedTail
open BStarH6WordChart BStarOwnerLaunchOrigin BStarGeneratedOwner
open BStarGeneratedTapeCuts BStarResetMarkAdapter BStarSeparatingRail
open BStarAcquireForwardTrace BStarLongTransport BStarClearanceSource

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- The bank choice used by the actual publication is certified by
the actual selecting receipt on this very post-407 tail. -/
theorem selecting_with_route {base old x : X} {addr : Nat→Pos n} {len : Nat}
    {rem rest : List (Fin n)} {mark center : Fin n}
    (H : CommitHandoff hp base old x addr len rem rest mark center)
    (K : (addr 0).2=0) (sep : ∀ e : Fin n,e≠rightNeighbor e) :
    ∃ pre e post op f, rem=pre++e::post ∧
      BStarLongPublication.decode (sourceDescriptor.read (x (addr 0).1).long)=some H.descriptor ∧
      bind (longGeometry B (run x pre (addr 0).1)) 0
        (atSite (run x pre (addr 0).1).long 0)=.reply f ∧
      ReceiptBank op H.descriptor f H.bank ∧ f.fault=0 ∧ f.opcode.toNat=op ∧
      GeneratedOwner hp base addr len x .idle pre (.busy op (.back 0)) ∧
      Event hp addr len (run x pre) e (.busy op (.back 0)) .idle := by
  let root := (addr 0).1
  have hlt : pc x root<411 := by have E : pc x root=408 := H.hit408; rw [E]; decide
  obtain ⟨pre,e,post,op,W,P,_,current,event,postPc,G⟩ :=
    first_411 hp K sep H.tail H.band hlt H.issue411
  have oldH : oldH6 B (run x pre) root=true := (H.band pre (e::post) W).1
  obtain ⟨d,D⟩ := selecting_has_descriptor hp K oldH (sep e) current event postPc
  have after : TailBand hp (step (run x pre) e) root post := by
    intro u v E
    have F : rem=(pre++e::u)++v := by rw [W,E,List.append_assoc]; rfl
    have J := H.band (pre++e::u) v F
    rw [BStarResetSchedule.run_append] at J
    exact J
  have foreign := ready_411_foreign hp K sep G after rfl rfl postPc
  have frame := BStarCommitChoiceHistory.foreign_word hp (step (run x pre) e) root post foreign
    (fun u a v E=>(after u (a::v) E).1)
  have join : run x rem=run (step (run x pre) e) post := by
    rw [W,BStarResetSchedule.run_append]
    rfl
  have result := selected_tail_result hp K oldH (sep e) current event d D (.inr (.inr postPc))
  obtain ⟨desc,f,reply,select⟩ := result
  have before := before_choice_bytes hp K P
  have descEnd : sourceDescriptor.read (run x rem root).long=
      sourceDescriptor.read (run x pre root).long := by
    rw [join]
    exact frame.1.trans desc
  have authDesc : BStarLongPublication.decode (sourceDescriptor.read (run x pre root).long)=some H.descriptor :=
    (congrArg BStarLongPublication.decode descEnd).symm.trans H.decoded
  have same : d=H.descriptor := Option.some.inj (D.symm.trans authDesc)
  subst d
  have Decode0 : BStarLongPublication.decode (sourceDescriptor.read (x root).long)=some H.descriptor :=
    (congrArg BStarLongPublication.decode before).symm.trans D
  obtain ⟨mode,Gpre,_⟩ := BStarGeneratedTapeCuts.split hp pre (e::post) (W ▸ H.tail)
  have modeEq : mode=.busy op (.back 0) := by
    have cm := at_end hp Gpre
    cases mode with
    | idle => exact ((by decide : (2:Nat)≠1) (current.1.2.2.1.symm.trans cm.1.2)).elim
    | busy a j =>
      have sameOp : a=op := cm.1.2.2.2.symm.trans current.1.2.2.2
      subst a
      cases j with
      | out j =>
        exact (BStarOwnerControlHistory.pointed_backward_no_forward _ len 0 current.2.1 j
          cm.2.1.1 cm.2.1.2.1).elim
      | back j =>
        cases j with
        | zero => rfl
        | succ j =>
          have ra := cm.2.1.2.2.1 0 (Nat.zero_lt_succ _)
          obtain ⟨q,F⟩ := current.2.1.2.1
          exact Token.noConfusion (ra.symm.trans F)
  subst mode
  obtain ⟨_,g,Gr,Gh,Go,_⟩ := consume_tail hp K oldH (sep e) current event (.inr (.inr postPc))
  have samePayload : g=f := Token.reply.inj (Gr.symm.trans reply)
  refine ⟨pre,e,post,op,f,W,Decode0,reply,?_,samePayload ▸ Gh,samePayload ▸ Go,Gpre,event⟩
  have choiceEq (b : Fin 3)
      (E : choice.read (step (run x pre) e root).long=BitVec.ofNat 2 b.val) : H.bank=b := by
    have Q := frame.2.trans E
    rw [←join] at Q
    have V := congrArg BitVec.toNat Q
    change _=b.val%4 at V
    rw [H.choice,Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide : 3<4))] at V
    exact Fin.ext V
  rcases select postPc with ⟨o,n,k,L⟩|⟨o,n,L⟩
  · exact .inl ⟨o,n,k,choiceEq _ L⟩
  · exact .inr ⟨o,n,choiceEq _ L⟩


/-- Literal launch does not start the race. The source begins with
race zero; the first race state is installed by gate arrival. -/
theorem bit_launch_race_zero {x y : X} {addr : Nat→Pos n}
    (K : (addr 0).2=0)
    (L : Launch (x (addr 0).1).long (y (addr 0).1).long)
    (O : (ctrlOp.read (x (addr 0).1).long).toNat=bitOp) :
    ∃ f, project addr y 0=.forward f ∧ f.fault=0 ∧ f.opcode.toNat=bitOp ∧ f.race=0 := by
  obtain ⟨a,args,P⟩ := L.2
  let bytes : BitVec LW := (x (addr 0).1).long
  change (ctrlOp.read bytes).toNat=bitOp at O
  have R := congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.1.1) P
  change atSite (y (addr 0).1).long 0=forward (ctrlOp.read bytes).toNat a at R
  rw [O] at R
  refine ⟨⟨0,BitVec.ofNat 9 bitOp,0,0,BitVec.ofNat 34 a⟩,?_,rfl,rfl,rfl⟩
  change atCursor y (addr 0)=_
  unfold atCursor
  rw [K]
  exact R

/-- In the NEED=true arm, the selecting receipt is reached through
the literal BIT issue, complete outward and return walks, and the
actual selecting consume of the same CommitHandoff word. -/
theorem needed_bit_route {base old x : X} {addr : Nat→Pos n} {len : Nat}
    {rem rest : List (Fin n)} {mark center : Fin n}
    (H : CommitHandoff hp base old x addr len rem rest mark center)
    (K : (addr 0).2=0) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (need : H.descriptor.need=true) :
    ∃ (start out back after : List (Fin n)) (issue turn ack : Fin n) (f q : Payload),
      rem=start++issue::(out++turn::(back++ack::after)) ∧
      let issued := step (run x start) issue
      let atTurn := run issued out
      let atAck := run (step atTurn turn) back
      Launch (run x start (addr 0).1).long (issued (addr 0).1).long ∧
      project addr issued 0=.forward q ∧ q.fault=0 ∧ q.opcode.toNat=bitOp ∧ q.race=0 ∧
      BusyOnly hp base addr len bitOp issued (.out 0) out (.out len) ∧
      Event hp addr len atTurn turn (.busy bitOp (.out len)) (.busy bitOp (.back len)) ∧
      BusyOnly hp base addr len bitOp (step atTurn turn) (.back len) back (.back 0) ∧
      Event hp addr len atAck ack (.busy bitOp (.back 0)) .idle ∧
      bind (longGeometry B (atAck (addr 0).1)) 0 (atSite (atAck (addr 0).1).long 0)=.reply f ∧
      f.fault=0 ∧ f.opcode.toNat=bitOp ∧ ReceiptBank bitOp H.descriptor f H.bank := by
  obtain ⟨pre,ack,post,op,f,W,_,reply,auth,healthyReply,opcReply,G,E⟩ := selecting_with_route hp H K sep
  have opBit : op=bitOp := by
    rcases auth with A|A
    · exact (by decide : (false : Bool) ≠ true) (A.2.1.symm.trans need) |>.elim
    · exact A.1
  rw [opBit] at auth opcReply G E
  have receipt := auth
  obtain ⟨lead,turn,back,V,found,T,Bk⟩ :=
    BStarAcquireAckAncestry.found_split_turn hp (from_idle hp G)
  obtain ⟨start,out,issue,W0,_,L,opc,Out⟩ := found
  have S : run x lead=run (step (run x start) issue) out := by
    rw [W0,BStarResetSchedule.run_append]
    rfl
  have P : run x pre=run (step (run (step (run x start) issue) out) turn) back := by
    rw [V,BStarResetSchedule.run_append,S]
    rfl
  obtain ⟨q,F,healthy,op0,race⟩ := bit_launch_race_zero
    (x:=run x start) (y:=step (run x start) issue) K L opc
  refine ⟨start,out,back,post,issue,turn,ack,f,q,?_,L,F,healthy,op0,race,
    Out,S ▸ T,S ▸ Bk,P ▸ E,P ▸ reply,healthyReply,opcReply,receipt⟩
  rw [W,V,W0]
  simp only [List.append_assoc,List.cons_append]

#print axioms needed_bit_route
end L4.BStarBitSelectingTrace
