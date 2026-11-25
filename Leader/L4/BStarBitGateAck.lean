import Leader.L4.BStarBitGateService
import Leader.L4.BStarBitPostGateAck

namespace L4.BStarBitGateAck
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace BStarAcquireHistorySample
open BStarBitHealthyService BStarLongDoor BStarLongLayout BStarCommitChoiceHistory
open BStarH6Ordinal BStarClearanceOffset BStarAcquireRailCoverage BStarBitDepart BStarBitParity
open BStarClearanceRaceMark BStarStageCandidateWrite

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

theorem pick_first (d : BStarLongPublication.Descriptor) (v : Payload) (s : Side) :
    pick d (cleanBit v s)=candidate d (firstBit s) := by
  cases s <;> rfl

/-- Positive first-side-to-ISSUE411 on a prescribed three-mark gate
service window followed by arbitrary outward/return interleaving.
Unlike retrospective authentication this has no successful ACK or
COMMIT premise. Arbitrary interleaving inside the gate window is
not claimed here. -/
theorem gate_window_acks {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (i : Fin n) (g : Nat) (G : g<len) (idx : S.getD g fall=(i,1))
    (O : oldOrdinal B base hh i=4) (qx : Q x) (ready : correct (oldH6 B base) hh 5 x)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out g)))
    (v : Payload) (old : atSite (x i).long 1=.forward v)
    (F : v.fault=0) (Op : v.opcode.toNat=bitOp) (out : v.outcome=0)
    (arg : v.argument=0) (race : v.race=1) (s t : Side) (opp : t≠s)
    (turnMark : Fin n) (turn : ∀ y : X,Q y→onTerminal hp y turnMark (fun j=>S.getD j fall) len)
    (d : BStarLongPublication.Descriptor) (need : d.need=true)
    (desc : BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d)
    {ls back w : List (Fin n)}
    (sub : (ls++turnMark::(back++[RearTrace.predecessor (S.getD 0 fall).1])).Sublist w)
    (size : g+1+ls.length=len) (backSize : len≤back.length)
    (nom : ∀ k (K : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y ls[k] (fun a=>S.getD a fall) len (g+1+k))
    (backNom : ∀ k (K : k<back.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y back[k] (fun a=>S.getD a fall) len (back.length-(k+1))) :
    ∃ pre tail, w=pre++RearTrace.predecessor (S.getD 0 fall).1::tail ∧
      let front := [incident i s,incident i t,i]++pre
      BusyOnly hp base (fun j=>S.getD j fall) len bitOp x (.out g) front (.back 0) ∧
      let y := play x front
      let ack := RearTrace.predecessor (S.getD 0 fall).1
      let fresh := (step y ack (S.getD 0 fall).1).long
      Event hp (fun j=>S.getD j fall) len y ack (.busy bitOp (.back 0)) .idle ∧
      Current hp base (fun j=>S.getD j fall) len (step y ack) .idle ∧
      (ctrlOp.read fresh).toNat=commitOp ∧
      BStarLongPublication.decode (sourceDescriptor.read fresh)=some d ∧
      choice.read fresh=BitVec.ofNat 2 (candidate d (firstBit s)).val := by
  obtain ⟨R,I,V,wire⟩ := BStarBitGateService.handshake hp C Q fiber closed sep head cont
    i g G idx O qx ready cur v old F Op out arg race s t opp
  let front := [incident i s,incident i t,i]
  let y := play x front
  have preserved (x : X) (u : List (Fin n)) (H : Q x) (offset : correct (oldH6 B base) hh 5 x) :
      Q (play x u) ∧ correct (oldH6 B base) hh 5 (play x u) := by
    induction u generalizing x with
    | nil => exact ⟨H,offset⟩
    | cons a u ih =>
      exact ih (step x a) (closed _ H a) (BStarClearanceOffset.stable hp _ hh x a (sep a)
        (fun j=>(congrArg Prod.fst (fiber x H j)).symm) (BStarClearanceOffsetMask.leftFrame hp x a) offset)
  have ok := preserved x front qx ready
  have D := (BStarSealBitDescriptor.busy_preserves_descriptor hp C sep R (by decide)).1
  have yDesc := (congrArg BStarLongPublication.decode D).trans desc
  have H₁ := congrArg Prod.snd idx
  have H₂ : oldOrdinal B base hh (S.getD g fall).1=4 := by rw [idx]; exact O
  obtain ⟨pre,tail,W,B' ,U⟩ := BStarBitPostGateAck.after_gate_acks_of_sublist hp
    C Q fiber closed sep ok.1 ok.2 g G H₁ H₂ (cleanBit v s) wire I V turnMark turn d need yDesc
    sub size backSize nom backNom
  refine ⟨pre,tail,W,BStarReplyService.join_busy hp R B',?_⟩
  dsimp only
  rw [BStarResetSchedule.run_append]
  rw [pick_first d v s] at U
  exact U

#print axioms gate_window_acks
end L4.BStarBitGateAck
