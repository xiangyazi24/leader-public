import Leader.L4.BStarCapturedCompilerInputs
import Leader.L4.BStarNativeAttemptReceipts

namespace L4.BStarNativeCompilerEntry
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongDoor BStarLongCommand BStarLongLayout BStarLongRegisters
open BStarLongArithmetic BStarLongPackets BStarGeneratedOwner
open BStarGeneratedBandScan BStarNativeReceiptTape BStarCapturedCompilerInputs
open BStarResetChartService BStarAliasFold BStarAliasRoster BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open L4.Compiler.Native

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- Genuine physical ACK12: the real source becomes ISSUE13 with
zero scalar file and unchanged acquired header and selector bits.
The distributed numeric slots are not presumed zero. -/
theorem physical_ack12 {base x : X} {slot : Nat→Pos n} {len : Nat} {e : Fin n}
    (sep : e≠rightNeighbor e) (H : oldH6 B x (slot 0).1=true)
    (receipt : Hit hp base slot len x e 12) :
    let i := (slot 0).1
    let y := (step x e i).long
    BStarResetControllerEntry.snapshot y=((.empty,1),BitVec.ofNat 9 13) ∧
      scalarFile.read y=0 ∧ capturedHeaders.read y=capturedHeaders.read (x i).long ∧
      captures.read y=captures.read (x i).long ∧ WellRep y [] [] literalCmp := by
  dsimp only
  let i := (slot 0).1
  obtain ⟨cur,_,P,_,own,f,R,F,O⟩ := receipt
  have eq : rightNeighbor e=i := own ▸ RearTrace.right_predecessor i
  let pair := (x e,x (rightNeighbor e))
  have hdr : (oldHeaders B pair.2).h6=true := by
    change oldH6 B x (rightNeighbor e)=true
    rwa [eq]
  have raw : pair.2.long=(x i).long := congrArg (fun j=>(x j).long) eq
  have state : step x e i=(largePair B pair).2 := by
    rw [←eq]
    simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
  have J := joined_ack12 hp pair f hdr (by rw [raw]; exact cur.1.2.1)
    (by rw [raw]; exact cur.1.2.2.1) (by rw [raw]; exact P)
    (by change bind (longGeometry B (x (rightNeighbor e))) 0 (atSite pair.2.long 0)=.reply f
        rw [eq,raw]; exact R) F O
  rw [raw] at J
  rw [state]
  exact ⟨J.1,J.2.1,J.2.2.1,J.2.2.2,by intro j J; simp at J⟩

/-- The native center bank nibble is exactly the corresponding
left-to-right nibble of its packed physical 36-bit bank. -/
theorem packed_nibble (x : BitVec LW) (b : Fin 3) (f : Fin 9) :
    (Digit9.data ((bankPart b 9 36 (by decide)).read x)).nibble f =
      some ((bankDigit b f).read x) := by
  change some (((bankPart b 9 36 (by decide)).read x).extractLsb' (4*(8-f.val)) 4)=_
  apply congrArg some
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have in36 : 4*(8-f.val)+k<36 := by omega
  simp only [Field.read,bankDigit,bankPart]
  simp only [BitVec.getLsbD_extractLsb',hk,in36,decide_true,Bool.true_and]
  congr 1
  omega

/-- Exact numeric input decoder: LD for port 0, the captured
center bank for port 1, RD for port 2. No side consults the
current center selector or uses the numeric payload's bank field. -/
theorem literal_input (x : BitVec LW) (b : Fin 3) (f : Fin 9)
    (l center r : BitVec 36)
    (L : (readLane 1 x).retained=.data l)
    (M : (bankPart b 9 36 (by decide)).read x=center)
    (R : (readLane 3 x).retained=.data r) :
    digitLoad x 0 f b.val=((Digit9.data l).nibble f).map BitVec.toNat ∧
      digitLoad x 1 f b.val=((Digit9.data center).nibble f).map BitVec.toNat ∧
      digitLoad x 2 f b.val=((Digit9.data r).nibble f).map BitVec.toNat := by
  refine ⟨?_,?_,?_⟩
  · change ((readLane 1 x).retained.nibble f).map BitVec.toNat=_
    rw [L]
  · rw [←M,packed_nibble]
    simp [digitLoad,b.isLt]
  · change ((readLane 3 x).retained.nibble f).map BitVec.toNat=_
    rw [R]


/-- The start of the actual 395-receipt compiler on the successful
original attempt, including its empty scalar representation. The
first real numeric sweep is opcode 13, not opcode 12. -/
theorem original_entry {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop) (I : Q x)
    (fiber : ∀ y,Q y→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w .idle)
    (A : BStarPostCutAttempt.AttemptPrefix hp base x (fun j=>S.getD j fall) len w) :
    ∃ (pre compiler tail : List (Fin n)) (ack : Fin n),
      w=pre++ack::(compiler++tail) ∧
      let addr := fun j=>S.getD j fall
      let root := (addr 0).1
      let old := BStarResetSchedule.run step x pre
      let y := step old ack
      let wire := (y root).long
      Hit hp base addr len old ack 12 ∧
      BStarResetControllerEntry.snapshot wire=((.empty,1),BitVec.ofNat 9 13) ∧
      scalarFile.read wire=0 ∧
      capturedHeaders.read wire=capturedHeaders.read (old root).long ∧
      captures.read wire=captures.read (old root).long ∧
      WellRep wire [] [] literalCmp ∧
      GeneratedOwner hp base addr len y .idle compiler .idle ∧
      pc (BStarResetSchedule.run step y compiler) root=408 ∧
      NativeTape hp base addr len y 13 compiler 395 := by
  obtain ⟨pre,compiler,tail,ack,W,H,G,P,N,_⟩ :=
    BStarNativeAttemptReceipts.from_chart_attempt hp C Q I fiber closed sep T A
  have header := (BStarGeneratedTapeCuts.root_cuts hp C Q I closed fiber pre).1
  obtain ⟨snap,zero,Hd,Bk,Rep⟩ := physical_ack12 hp (base:=base)
    (x:=BStarResetSchedule.run step x pre) (slot:=fun j=>S.getD j fall) (len:=len)
    (e:=ack) (sep ack) header H
  refine ⟨pre,compiler,tail,ack,W,?_⟩
  exact ⟨H,snap,zero,Hd,Bk,Rep,G,P,N⟩

#print axioms physical_ack12
#print axioms packed_nibble
#print axioms literal_input
#print axioms original_entry
end L4.BStarNativeCompilerEntry
