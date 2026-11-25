import Leader.L4.BStarSealPositiveTerminal
import Leader.L4.BStarReplyService
import Leader.L4.BStarSealBitDescriptor
import Leader.L4.BStarFirstDoorService

namespace L4.BStarSealAckService
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarLongDoor BStarLongLayout BStarCommitIssue BStarResetChartService BStarClearanceSource
open BStarSealPositiveTerminal BStarSealHealthyHop BStarSealParity BStarFirstDoorService

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- The exact accepted NEED SEAL packet beyond its own center reaches
the matching ACK under the fixed outward/turn/return/source sequence
despite arbitrary other physical marks. The actual consume schedules
legal 410 with the same descriptor. -/
theorem seal_ack_of_sublist {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (k : Nat) (K : k<len) (slot : (S.getD k fall).2=1)
    (head : oldH6 B base (S.getD k fall).1=true)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy sealOp (.out (k+1))))
    (pay : Payload) (well : Well pay) (old : project (fun j=>S.getD j fall) x (k+1)=.forward pay)
    (d : Desc) (need : d.need=true) (par : parity pay=d.need.toNat)
    (desc : BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d)
    (t : Fin n) (turn : ∀ y : X,Q y→onTerminal hp y t (fun j=>S.getD j fall) len)
    {out back w : List (Fin n)}
    (sub : ((out++[t])++(back++[RearTrace.predecessor (S.getD 0 fall).1])).Sublist w)
    (outSize : k+1+out.length=len) (backSize : len≤back.length)
    (outNom : ∀ j (J : j<out.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y out[j] (fun a=>S.getD a fall) len (k+1+j))
    (backNom : ∀ j (J : j<back.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y back[j] (fun a=>S.getD a fall) len (back.length-(j+1))) :
    ∃ sealTail tail, w=sealTail++RearTrace.predecessor (S.getD 0 fall).1::tail ∧
      BusyOnly hp base (fun j=>S.getD j fall) len sealOp x (.out (k+1)) sealTail (.back 0) ∧
      let y := play x sealTail
      let door := RearTrace.predecessor (S.getD 0 fall).1
      let fresh := (step y door (S.getD 0 fall).1).long
      Event hp (fun j=>S.getD j fall) len y door (.busy sealOp (.back 0)) .idle ∧
      Current hp base (fun j=>S.getD j fall) len (step y door) .idle ∧
      (ctrlOp.read fresh).toNat=bitOp ∧
      BStarLongPublication.decode (sourceDescriptor.read fresh)=some d := by
  obtain ⟨outWord,retWord,W,outSub,retSub⟩ := List.append_sublist_iff.mp sub
  obtain ⟨walk,wait,e,unused,U,_,T,reply,norm⟩ := turns_of_sublist hp C Q fiber closed sep
    k K slot head (k+1) (by omega) (by omega) qx pay well cur old t outSub outSize outNom turn
  let pre := walk++wait++[e]
  let middle := play x pre
  let r := sealReply pay
  obtain ⟨ret,tail,J,B',bound,I,ack,I'⟩ :=
    BStarReplyService.reaches_consume hp C Q fiber closed sep (stable_word hp Q closed x pre qx)
      sealOp len r norm (BStarAcquireHistoryReturn.busy_end hp T) reply
      (List.sublist_append_of_sublist_right retSub) backSize backNom
  have full := BStarReplyService.join_busy hp T B'
  have atAck : play x (pre++ret)=play middle ret := BStarResetSchedule.run_append step x pre ret
  have oldDesc := (BStarSealBitDescriptor.busy_preserves_descriptor hp C sep full (by decide)).1
  rw [atAck] at oldDesc
  have D := (congrArg BStarLongPublication.decode oldDesc).trans desc
  have root := root_header hp C I.1.1
  have low : r.argument.toNat%2=1 := by
    change ((pay.argument.toNat%2)%(2^34))%2=1
    rw [Nat.mod_mod_of_dvd _ (by decide : 2∣2^34),Nat.mod_mod]
    change parity pay=1
    rw [par,need]
    rfl
  obtain ⟨PC,DescR,_⟩ := BStarSealAckLegal.actual_seal_ack_allows_bit hp
    (base:=base) (x:=play middle ret) (addr:=fun j=>S.getD j fall) root.2 root.1 (sep _) I ack
    d r well.fault well.opcode bound D need low
  refine ⟨pre++ret,tail,?_,full,?_⟩
  · change w=((walk++wait++[e])++ret)++RearTrace.predecessor (S.getD 0 fall).1::tail
    rw [W,U,List.append_assoc,List.cons_append,J]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  · dsimp only
    rw [atAck]
    exact ⟨ack,I',PC,DescR⟩

end L4.BStarSealAckService
