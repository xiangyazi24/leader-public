import Leader.L4.BStarFirstDoorService
import Leader.L4.Height.StageScopedTurns
import Leader.L4.Height.StagePositiveAck

namespace L4.Height.StageScopedFlight
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarLongDoor BStarLongLayout BStarCommitIssue BStarResetChartService BStarClearanceSource
open BStarLongTransport BStarSealBitDescriptor BStarGeneratedPCAncestry BStarSealPositiveTerminal BStarSealHealthyHop BStarSealParity BStarFirstDoorService BStarCommitGeneratedTail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Actual initiated STAGE reaches the same-source ISSUE409 on an arbitrary
replay containing the nominated outward, turn, reverse and door subsequence. -/
theorem stage_ack_of_sublist {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (source : BitVec LW) (d : Desc)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    (src : sourceDescriptor.read (x (S.getD 0 fall).1).long=sourceDescriptor.read source)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy stageOp (.out 0)))
    (old : project (fun j=>S.getD j fall) x 0=.forward (BStarStageIssue.payload source))
    (t : Fin n) (turn : ∀ y : X,Q y→onTerminal hp y t (fun j=>S.getD j fall) len)
    {out back w : List (Fin n)}
    (sub : ((out++[t])++(back++[RearTrace.predecessor (S.getD 0 fall).1])).Sublist w)
    (auth : StageScopedReplay.PrefixAuth hp base x (fun j=>S.getD j fall) len 0 source d w)
    (outSize : out.length=len) (backSize : len≤back.length)
    (outNom : ∀ j (J : j<out.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y out[j] (fun a=>S.getD a fall) len j)
    (backNom : ∀ j (J : j<back.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y back[j] (fun a=>S.getD a fall) len (back.length-(j+1))) :
    ∃ sealTail tail, w=sealTail++RearTrace.predecessor (S.getD 0 fall).1::tail ∧
      BusyOnly hp base (fun j=>S.getD j fall) len stageOp x (.out 0) sealTail (.back 0) ∧
      let y := play x sealTail
      let door := RearTrace.predecessor (S.getD 0 fall).1
      let fresh := (step y door (S.getD 0 fall).1).long
      Event hp (fun j=>S.getD j fall) len y door (.busy stageOp (.back 0)) .idle ∧
      Current hp base (fun j=>S.getD j fall) len (step y door) .idle ∧
      (ctrlOp.read fresh).toNat=sealOp ∧
      BStarLongPublication.decode (sourceDescriptor.read fresh)=some d ∧
      BStarLongCommand.bind (longGeometry B (y (S.getD 0 fall).1)) 0
        (atSite (y (S.getD 0 fall).1).long 0)=.reply StageReplyForm.reply := by
  obtain ⟨outWord,retWord,W,outSub,retSub⟩ := List.append_sublist_iff.mp sub
  obtain ⟨walk,wait,e,unused,U,_,T,reply,norm⟩ := StageScopedTurns.turns_of_sublist hp C Q fiber closed sep
    0 (Nat.zero_le _) qx source d D cur old t outSub (by simpa using outSize) (auth.take hp outWord retWord W) (by simpa using outNom) turn
  let pre := walk++wait++[e]
  let middle := play x pre
  let r := StageReplyForm.reply
  obtain ⟨ret,tail,J,B',bound,I,ack,I'⟩ :=
    BStarReplyService.reaches_consume hp C Q fiber closed sep (stable_word hp Q closed x pre qx)
      stageOp len r norm (BStarAcquireHistoryReturn.busy_end hp T) reply
      (List.sublist_append_of_sublist_right retSub) backSize backNom
  have full := BStarReplyService.join_busy hp T B'
  have atAck : play x (pre++ret)=play middle ret := BStarResetSchedule.run_append step x pre ret
  have oldDesc := (BStarSealBitDescriptor.busy_preserves_descriptor hp C sep full (by decide)).1
  rw [atAck] at oldDesc
  have dec := (congrArg BStarLongPublication.decode (oldDesc.trans src)).trans D
  have root := root_header hp C I.1.1
  obtain ⟨PC,_,DescR⟩ := StageAckToSeal.stage_ack_seal_issue hp (addr:=fun j=>S.getD j fall)
    root.2 root.1 (sep _) I ack StageReplyForm.reply rfl rfl bound d dec
  refine ⟨pre++ret,tail,?_,full,?_⟩
  · change w=((walk++wait++[e])++ret)++RearTrace.predecessor (S.getD 0 fall).1::tail
    rw [W,U,List.append_assoc,List.cons_append,J]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  · dsimp only
    rw [atAck]
    exact ⟨ack,I',PC,DescR,bound⟩

end L4.Height.StageScopedFlight
