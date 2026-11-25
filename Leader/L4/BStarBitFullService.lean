import Leader.L4.BStarBitGatePositive
import Leader.L4.BStarBitHealthyReplay
import Leader.L4.BStarBitGateAck

namespace L4.BStarBitFullService
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace BStarAcquireHistorySample
open BStarBitHealthyService BStarLongDoor BStarLongLayout BStarCommitChoiceHistory
open BStarH6Ordinal BStarClearanceOffset BStarAcquireRailCoverage BStarBitDepart BStarBitParity
open BStarClearanceRaceMark BStarStageCandidateWrite BStarBitSegment BStarBitGateGeometry BStarClearanceSource

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem carry_layout {base : X} (hh : ∃ i,oldH6 B base i=true)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (u : List (Fin n)) (H : Q x) (offset : correct (oldH6 B base) hh 5 x) :
    Q (play x u) ∧ correct (oldH6 B base) hh 5 (play x u) := by
  induction u generalizing x with
  | nil => exact ⟨H,offset⟩
  | cons a u ih =>
    exact ih (step x a) (closed _ H a) (BStarClearanceOffset.stable hp _ hh x a (sep a)
      (fun j=>(congrArg Prod.fst (fiber x H j)).symm) (BStarClearanceOffsetMask.leftFrame hp x a) offset)

/-- A genuine canonical BIT launch and one fixed ordered service
subsequence suffice for the actual ACK, even with arbitrary raw
interleaving inside the gate. The ACK result records the actual first
incident side, not a side chosen by the nominations. -/
theorem launched_bit_acks_of_sublist {base old : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (g : Nat) (G : 0<g ∧ g<len) (idx : S.getD g fall=(i,1)) (O : oldOrdinal B base hh i=4)
    (door : Fin n) (op : (ctrlOp.read (old (S.getD 0 fall).1).long).toNat=bitOp)
    (launch : Launch (old (S.getD 0 fall).1).long ((step old door) (S.getD 0 fall).1).long)
    (qx : Q (step old door)) (ready : correct (oldH6 B base) hh 5 (step old door))
    (cur : Current hp base (fun j=>S.getD j fall) len (step old door) (.busy bitOp (.out 0)))
    (turnMark : Fin n) (turn : ∀ y : X,Q y→onTerminal hp y turnMark (fun j=>S.getD j fall) len)
    (d : BStarLongPublication.Descriptor) (need : d.need=true)
    (desc : BStarLongPublication.decode (sourceDescriptor.read ((step old door) (S.getD 0 fall).1).long)=some d)
    {before after back w : List (Fin n)}
    (sub : (before++([incident i .left,incident i .right,incident i .left]++
      (after++turnMark::(back++[RearTrace.predecessor (S.getD 0 fall).1])))).Sublist w)
    (beforeSize : before.length=g) (afterSize : g+1+after.length=len) (backSize : len≤back.length)
    (beforeNom : ∀ j (J : j<before.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y before[j] (fun a=>S.getD a fall) len j)
    (afterNom : ∀ j (J : j<after.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y after[j] (fun a=>S.getD a fall) len (g+1+j))
    (backNom : ∀ j (J : j<back.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y back[j] (fun a=>S.getD a fall) len (back.length-(j+1))) :
    ∃ (toGate gate toAck tail : List (Fin n)) (s : Side),
      w=toGate++(gate++(toAck++RearTrace.predecessor (S.getD 0 fall).1::tail)) ∧
      (∃ u v, gate=u++incident i s::v ∧ ∀ e∈u,e≠incident i .left ∧ e≠incident i .right) ∧
      readSegment i .fresh gate=some s ∧
      let start := step old door
      let pre := toGate++(gate++toAck)
      let y := play start pre
      let ack := RearTrace.predecessor (S.getD 0 fall).1
      let fresh := (step y ack (S.getD 0 fall).1).long
      BusyOnly hp base (fun j=>S.getD j fall) len bitOp start (.out 0) pre (.back 0) ∧
      Event hp (fun j=>S.getD j fall) len y ack (.busy bitOp (.back 0)) .idle ∧
      Current hp base (fun j=>S.getD j fall) len (step y ack) .idle ∧
      (ctrlOp.read fresh).toNat=commitOp ∧
      BStarLongPublication.decode (sourceDescriptor.read fresh)=some d ∧
      choice.read fresh=BitVec.ofNat 2 (candidate d (firstBit s)).val := by
  let start := step old door
  obtain ⟨preWord,suffix,W,beforeSub,rest⟩ := List.append_sublist_iff.mp sub
  obtain ⟨gateWord,replyWord,restW,gateSub,replySub⟩ := List.append_sublist_iff.mp rest
  obtain ⟨toGate,extra,v,A,preBusy,land,F,Op,U,R,arg⟩ :=
    BStarBitHealthyReplay.launch_replay_to_gate hp C Q fiber closed sep i g G idx O door op launch
      qx ready cur beforeSub beforeSize beforeNom
  let xG := play start toGate
  have haveGate := carry_layout hp hh Q fiber closed sep start toGate qx ready
  have G0 : atSite (xG i).long 1=.forward {v with race:=1} := by
    rw [show {v with race:=1}=v by cases v; simp_all]
    exact land
  obtain ⟨gate,unused,s,H,read,gateBusy,pay,wire⟩ :=
    BStarBitGatePositive.gate_exits_of_sublist hp C Q fiber closed sep i g G.2 idx O v F Op U arg
      (extra++gateWord) (List.sublist_append_of_sublist_right gateSub)
      haveGate.1 haveGate.2 (BStarAcquireHistoryReturn.busy_end hp preBusy) G0
  have afterGate := carry_layout hp hh Q fiber closed sep xG gate haveGate.1 haveGate.2
  have sameD₁ := (BStarSealBitDescriptor.busy_preserves_descriptor hp C sep preBusy (by decide)).1
  have sameD₂ := (BStarSealBitDescriptor.busy_preserves_descriptor hp C sep gateBusy (by decide)).1
  have yDesc := (congrArg BStarLongPublication.decode (sameD₂.trans sameD₁)).trans desc
  have gateK : (S.getD g fall).2=1 := congrArg Prod.snd idx
  have gateH : oldOrdinal B base hh (S.getD g fall).1=4 := by rw [idx]; exact O
  obtain ⟨toAck,tail,J,ackBusy,P⟩ :=
    BStarBitPostGateAck.after_gate_acks_of_sublist hp C Q fiber closed sep afterGate.1 afterGate.2
      g G.2 gateK gateH (cleanBit v s) wire (BStarAcquireHistoryReturn.busy_end hp gateBusy) pay
      turnMark turn d need yDesc (List.sublist_append_of_sublist_right replySub) afterSize backSize afterNom backNom
  have diff : incident i .left≠incident i .right := by
    intro E
    exact Side.noConfusion (incident_injective (oldH6 B base) hh i i O O .left .right E).2
  have labels := scanner_labels i diff gate .fresh s read
  refine ⟨toGate,gate,toAck,tail,s,?_,labels_bit labels,read,?_⟩
  · rw [W,A,restW,List.append_assoc,←List.append_assoc extra,H,List.append_assoc,J]
  · dsimp only
    refine ⟨BStarReplyService.join_busy hp preBusy (BStarReplyService.join_busy hp gateBusy ackBusy),?_⟩
    rw [BStarResetSchedule.run_append,BStarResetSchedule.run_append]
    rw [BStarBitGateAck.pick_first d v s] at P
    exact P

open BStarResetChartNomination BStarSeparatingProgress

theorem nominate_forward {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (m : Nat) :
    ∀ a,a+m≤len → ∃ ls : List (Fin n), ls.length=m ∧
      ∀ k (K : k<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
        linkAt hp y ls[k] (fun j=>S.getD j fall) len (a+k) := by
  induction m with
  | zero =>
    intro a _
    refine ⟨[],rfl,?_⟩
    intro k K; exact (Nat.not_lt_zero _ K).elim
  | succ m ih =>
    intro a A
    have L : a<len := by omega
    obtain ⟨e,N⟩ := nominate hp C head cont a (Nat.le_of_lt L)
    obtain ⟨ls,sz,T⟩ := ih (a+1) (by omega)
    refine ⟨e::ls,by simp [sz],?_⟩
    intro k K y H
    cases k with
    | zero =>
      have W := (mem_link hp y e _ len a).mp (by simpa only [if_pos L] using N y H)
      simpa only [List.getElem_cons_zero,Nat.add_zero] using W
    | succ k =>
      have K' : k<ls.length := by simpa using K
      have edgeService := T k K' y H
      have idx : a+(k+1)=(a+1)+k := by omega
      simpa only [List.getElem_cons_succ,idx] using edgeService

/-- Layout-only nominal service word for a launched BIT, of length
two chart lengths plus four raw marks. This is a deterministic cover
and does not assert a stochastic horizon or unique lifted key. -/
theorem bit_service_word {base old : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (g : Nat) (G : 0<g ∧ g<len) (idx : S.getD g fall=(i,1)) (O : oldOrdinal B base hh i=4)
    (door : Fin n) (op : (ctrlOp.read (old (S.getD 0 fall).1).long).toNat=bitOp)
    (launch : Launch (old (S.getD 0 fall).1).long ((step old door) (S.getD 0 fall).1).long)
    (qx : Q (step old door)) (ready : correct (oldH6 B base) hh 5 (step old door))
    (cur : Current hp base (fun j=>S.getD j fall) len (step old door) (.busy bitOp (.out 0)))
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (d : BStarLongPublication.Descriptor) (need : d.need=true)
    (desc : BStarLongPublication.decode (sourceDescriptor.read ((step old door) (S.getD 0 fall).1).long)=some d) :
    ∃ service : List (Fin n), service.length=2*len+4 ∧ ∀ w : List (Fin n), service.Sublist w →
    ∃ (toGate gate toAck tail : List (Fin n)) (s : Side),
      w=toGate++(gate++(toAck++RearTrace.predecessor (S.getD 0 fall).1::tail)) ∧
      (∃ u v, gate=u++incident i s::v ∧ ∀ e∈u,e≠incident i .left ∧ e≠incident i .right) ∧
      readSegment i .fresh gate=some s ∧
      let start := step old door
      let pre := toGate++(gate++toAck)
      let y := play start pre
      let ack := RearTrace.predecessor (S.getD 0 fall).1
      let fresh := (step y ack (S.getD 0 fall).1).long
      BusyOnly hp base (fun j=>S.getD j fall) len bitOp start (.out 0) pre (.back 0) ∧
      Event hp (fun j=>S.getD j fall) len y ack (.busy bitOp (.back 0)) .idle ∧
      Current hp base (fun j=>S.getD j fall) len (step y ack) .idle ∧
      (ctrlOp.read fresh).toNat=commitOp ∧
      BStarLongPublication.decode (sourceDescriptor.read fresh)=some d ∧
      choice.read fresh=BitVec.ofNat 2 (candidate d (firstBit s)).val := by
  obtain ⟨before,M,N₀⟩ := nominate_forward hp C head cont g 0 (by omega)
  obtain ⟨after,J,N₁⟩ := nominate_forward hp C head cont (len-(g+1)) (g+1) (by omega)
  obtain ⟨back,K,N₂⟩ := BStarReplyService.nominate_back hp C head cont len (Nat.le_refl _)
  obtain ⟨term,T⟩ := BStarBitPositiveTerminal.nominate_terminal hp C head cont
  let marks := before++([incident i .left,incident i .right,incident i .left]++
      (after++term::(back++[RearTrace.predecessor (S.getD 0 fall).1])))
  refine ⟨marks,?_,?_⟩
  · dsimp [marks]
    simp only [List.length_append,List.length_cons,List.length_nil,M,J,K]
    omega
  · intro w sub
    exact launched_bit_acks_of_sublist hp C Q fiber closed sep i g G idx O door op launch qx ready cur
      term (fun y H=>T y (fiber y H)) d need desc sub M (by omega) (by omega)
      (fun k h y H=>by simpa only [Nat.zero_add] using N₀ k h y H) N₁ N₂

#print axioms launched_bit_acks_of_sublist
#print axioms bit_service_word
end L4.BStarBitFullService
