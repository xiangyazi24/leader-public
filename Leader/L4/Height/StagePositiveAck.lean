import Leader.L4.Height.StagePositiveTerminal
import Leader.L4.Height.StageAckToSeal
import Leader.L4.BStarReplyService
import Leader.L4.BStarSealBitDescriptor

namespace L4.Height.StagePositiveAck
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarLongFixedRouting BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetChartService
open BStarSealBitDescriptor BStarAcquireHistoryReturn
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- From a canonical STAGE at its nominated terminal, the prescribed
return subsequence forces an actual canonical ACK and ISSUE409. -/
theorem ack_of_terminal {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (t : Fin n) (source : BitVec LW) (d : Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    (src : sourceDescriptor.read (x (S.getD 0 fall).1).long=sourceDescriptor.read source)
    (I : Current hp base (fun j=>S.getD j fall) len x (.busy stageOp (.out len)))
    (F : project (fun j=>S.getD j fall) x len=.forward (BStarStageIssue.payload source))
    (turn : onTerminal hp x t (fun j=>S.getD j fall) len)
    {ls w : List (Fin n)} (sub : (ls++[RearTrace.predecessor (S.getD 0 fall).1]).Sublist w)
    (size : len≤ls.length)
    (nom : ∀ k (K : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y ls[k] (fun j=>S.getD j fall) len (ls.length-(k+1))) :
    ∃ pre tail, w=pre++RearTrace.predecessor (S.getD 0 fall).1::tail ∧
      BusyOnly hp base (fun j=>S.getD j fall) len stageOp x (.out len) (t::pre) (.back 0) ∧
      let y := play x (t::pre)
      let door := RearTrace.predecessor (S.getD 0 fall).1
      let fresh := (step y door (S.getD 0 fall).1).long
      Event hp (fun j=>S.getD j fall) len y door (.busy stageOp (.back 0)) .idle ∧
      Current hp base (fun j=>S.getD j fall) len (step y door) .idle ∧
      (ctrlOp.read fresh).toNat=sealOp ∧
      BStarLongPublication.decode (sourceDescriptor.read fresh)=some d := by
  obtain ⟨E,J,R⟩ := StagePositiveTerminal.nominated_turn hp C Q fiber closed sep qx t source d D I F turn
  obtain ⟨pre,tail,W,L,reply,cur,ack,fresh⟩ :=
    BStarReplyService.reaches_consume hp C Q fiber closed sep (closed _ qx t)
      stageOp len StageReplyForm.reply (by rfl) J R sub size nom
  have full : BusyOnly hp base (fun j=>S.getD j fall) len stageOp x (.out len) (t::pre) (.back 0) :=
    .cons I E L
  have frame := (busy_preserves_descriptor hp C sep full (by decide)).1.trans src
  have root := root_header hp C cur.1.1
  obtain ⟨pc,_,desc⟩ := StageAckToSeal.stage_ack_seal_issue hp (addr:=fun j=>S.getD j fall)
    root.2 root.1 (sep _) cur ack StageReplyForm.reply rfl rfl reply d
    ((congrArg BStarLongPublication.decode frame).trans D)
  exact ⟨pre,tail,W,full,ack,fresh,pc,desc⟩

end L4.Height.StagePositiveAck
