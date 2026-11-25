import Leader.L4.BStarNeedServicePlan
import Leader.L4.BStarSealAckService
import Leader.L4.BStarIssueBitService
import Leader.L4.BStarIssueToCenter
import Leader.L4.BStarSealCenterAdvance
import Leader.L4.BStarSealTailReplay
import Leader.L4.BStarNeedTrace

namespace L4.BStarNeedTailService
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarLongDoor BStarLongLayout BStarCommitIssue BStarResetChartService BStarClearanceSource
open BStarFirstDoorService BStarH6Ordinal BStarClearanceOffset BStarBitSegment BStarBitParity
open BStarClearanceRaceMark BStarStageCandidateWrite BStarLongLiteral BStarLongPublication
open BStarBitNoAbort BStarLongLandingFrame BStarSealHealthyHop BStarAcquireAnchors BStarNeedServicePlan

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem keep_offsets {base : X} (hh : ∃ i,oldH6 B base i=true)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e) :
    ∀ (x : X) (w : List (Fin n)), Q x → correct (oldH6 B base) hh 5 x →
      correct (oldH6 B base) hh 5 (play x w) := by
  intro x w q r
  induction w generalizing x with
  | nil => exact r
  | cons e w ih =>
    exact ih (step x e) (closed _ q e) (BStarClearanceOffset.stable hp _ hh x e (sep e)
      (fun j=>(congrArg Prod.fst (fiber x q j)).symm) (BStarClearanceOffsetMask.leftFrame hp x e) r)

private theorem settle_mark {x : X} {a : Fin n} {u v : List (Fin n)} :
    play x (u++a::v)=play (step (play x u) a) v :=
  BStarResetSchedule.run_append step x u (a::v)

/-- End-to-end deterministic service from the genuine accepted NEED
SEAL at its own center. The service subsequence tolerates arbitrary
other marks all the way to the actual COMMIT. The same tape proves
custody; there is no terminal SEAL/writer or success premise. -/
theorem need_tail_sealed_trace {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len)
    (gateIdx : S.getD g fall=(bSite,1)) (ord : oldOrdinal B base hh bSite=4)
    (lead : List (Fin n))
    (history : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy sealOp (.out k)))
    (pay : Payload) (well : Well pay) (d : Descriptor) (need : d.need=true)
    (oldFacts : let x := play origin lead
      Q x ∧ correct (oldH6 B base) hh 5 x ∧ BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false ∧
      BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (x i).long d=true ∧ readOptional (stage.read (x i).long)=some d ∧
      (centerLink (oldPair B x i),.advance pay)∈actualOffers (oldPair B x i)
        ((x i).long,(x (rightNeighbor i)).long))
    (P : Plan hp base (fun j=>S.getD j fall) len k g)
    (w : List (Fin n)) (sub : (service hp P i bSite).Sublist w) :
    ∃ (pre tail gate : List (Fin n)) (s : Side),
      w=pre++i::tail ∧ gate.Sublist pre ∧ readSegment bSite .fresh gate=some s ∧
      BStarGrantWriterHistory.BeforePublication hp (step (play origin lead) i) i pre ∧
      BStarNeedTrace.Matched hp base (fun j=>S.getD j fall) len k (step (play origin lead) i) pre ∧
      let y := play (step (play origin lead) i) pre
      let b := candidate d (firstBit s)
      SealedCenter d (y i).long ∧
      (longTrace (oldPair B y i) ((y i).long,(y (rightNeighbor i)).long)).publications=[⟨.left,b⟩] ∧
      readPublication (step y i i).long=(BitVec.ofNat 2 b.val,0,0) := by
  let x0 := play origin lead
  let x := step x0 i
  let door := RearTrace.predecessor (S.getD 0 fall).1
  obtain ⟨q0,offset0,coh,sourceDesc,packedDesc,auth,stageEq,sel⟩ := oldFacts
  have cur := BStarGeneratedTapeCuts.at_end hp history
  obtain ⟨v,seedMark,seedCur,seedWire,seedWell,bit⟩ := BStarSealCenterAdvance.accepted_step hp
    C Q fiber closed sep q0 i k K idx head cur pay well d sel packedDesc auth stageEq
  have seedHistory : BusyOnly hp base (fun j=>S.getD j fall) len sealOp x0 (.out k) [i] (.out (k+1)) :=
    .cons cur seedMark (.nil seedCur)
  have Dseed := (congrArg BStarLongPublication.decode
    (BStarSealBitDescriptor.busy_preserves_descriptor hp C sep seedHistory (by decide)).1).trans sourceDesc
  have qx : Q x := closed _ q0 i
  have offX : correct (oldH6 B base) hh 5 x := keep_offsets hp hh Q fiber closed sep x0 [i] q0 offset0
  obtain ⟨a,bc,W,sealSub,bitCommit⟩ := List.append_sublist_iff.mp sub
  obtain ⟨b,c,V,bitSub,commitSub⟩ := List.append_sublist_iff.mp bitCommit
  have term : ∀ y : X,Q y→onTerminal hp y P.turn (fun j=>S.getD j fall) len :=
    fun y H=>P.nomTurn y (fiber y H)
  have baseK : oldH6 B base (S.getD k fall).1=true := by rw [idx]; exact head
  obtain ⟨sealFlight,aTail,A,Seal,sealAck,readyBit,pcBit,descBit⟩ := BStarSealAckService.seal_ack_of_sublist hp
    C Q fiber closed sep qx k K (congrArg Prod.snd idx) baseK seedCur v seedWell seedWire d need bit
    Dseed P.turn term sealSub P.size409 (by rw [P.sizeBack]; exact Nat.le_refl _) P.nom409 P.nomBack
  let xBit := step (play x sealFlight) door
  have qb : Q xBit := closed _ (stable_word hp Q closed x sealFlight qx) door
  have rb : correct (oldH6 B base) hh 5 xBit :=
    keep_offsets hp hh Q fiber closed sep (play x sealFlight) [door]
      (stable_word hp Q closed x sealFlight qx) (keep_offsets hp hh Q fiber closed sep x sealFlight qx offX)
  have bitRemainder : (bitWord hp P bSite).Sublist (aTail++b) := List.sublist_append_of_sublist_right bitSub
  obtain ⟨wait1,toGate,gate,toAck,bTail,s,Z,away1,Idle1,read,bitStart,Bit,bitAck,readyCommit,
      pcCommit,descCommit,choiceCommit,legalCommit⟩ := BStarIssueBitService.ready_bit_service hp
    C Q fiber closed sep qb rb readyBit pcBit d need descBit bSite g G gateIdx ord P.turn term
    bitRemainder P.sizeBefore P.sizeAfter (by rw [P.sizeBack]; exact Nat.le_refl _)
    (fun j J y H=>by simpa only [Nat.zero_add] using P.nomBefore j J y H) P.nomAfter P.nomBack
  let bitFlight := toGate++(gate++toAck)
  let bitLaunched := step (play xBit wait1) door
  let xCommit := step (play bitLaunched bitFlight) door
  have qc : Q xCommit := closed _ (stable_word hp Q closed bitLaunched bitFlight
    (closed _ (stable_word hp Q closed xBit wait1 qb) door)) door
  have commitRemainder : (commitWord hp P i).Sublist (bTail++c) := List.sublist_append_of_sublist_right commitSub
  obtain ⟨wait2,commitFlight,tail,Y,away2,Idle2,pcIssue,launch,Com,descIssue,choiceIssue⟩ :=
    BStarIssueToCenter.ready_commit_service hp C Q fiber closed sep qc readyCommit pcCommit d descCommit
      legalCommit i k K idx head commitRemainder P.size411
      (fun j J y H=>by simpa only [Nat.zero_add] using P.nom411 j J y H)
  let pre := sealFlight++door::(wait1++door::(bitFlight++door::(wait2++door::commitFlight)))
  have R := BStarSealTailReplay.tail_replay hp C sep i k K idx head door door door door
    sealFlight wait1 bitFlight wait2 commitFlight Seal sealAck ⟨.idle,Idle1⟩ away1 bitStart Bit bitAck
    ⟨.idle,Idle2⟩ away2 rfl ⟨pcIssue,launch,Com⟩
  have centerOld (u : List (Fin n)) : oldH6 B (play x u) i=true :=
    (congrArg Prod.fst (fiber _ (stable_word hp Q closed x u qx) i)).symm.trans head
  have rootHead : oldH6 B x0 i=true := (congrArg Prod.fst (fiber x0 q0 i)).symm.trans head
  have custody := BStarSealTailReplay.seeded_tail_custody hp C sep i own k (Nat.le_of_lt K) idx
    lead pre pay d history ⟨rootHead,coh,well.fault,well.opcode,packedDesc,auth,stageEq,sel⟩ seedMark R
    (fun u _ _ _=>centerOld u)
  let z := play xCommit wait2
  have time : play x pre=play (step z door) commitFlight := by
    dsimp only [pre,z,xCommit,bitLaunched,xBit]
    rw [settle_mark hp,settle_mark hp,settle_mark hp,settle_mark hp]
  have sealCut : SealedCenter d (play (step z door) commitFlight i).long := by
    change SealedCenter d (play x pre i).long at custody
    rwa [time] at custody
  have chosen := choiceIssue.trans choiceCommit
  have valid := (congrArg BStarLongPublication.decode descIssue).trans descCommit
  have legal : candidate d (firstBit s)=d.b0 ∨ (d.need=true ∧ candidate d (firstBit s)=d.b1) := by
    cases s <;> simp [candidate,firstBit,need]
  have publish := BStarIssueToCenter.publication_on_service_cut hp C sep i k K idx head door commitFlight
    d (candidate d (firstBit s)) pcIssue launch Com valid chosen legal sealCut
  have seedEvent : GeneratedOwner hp base (fun j=>S.getD j fall) len x0
      (.busy sealOp (.out k)) [i] (.busy sealOp (.out (k+1))) :=
    .next cur seedMark (.endpoint seedCur)
  have fullLead := BStarNeedPrefix.generated_append hp history seedEvent
  have landed : play origin (lead++[i])=x := by
    rw [BStarResetSchedule.run_append]
    rfl
  have noEarly := BStarNeedPrefix.no_earlier_publication hp C sep i own k (Nat.le_of_lt K) idx
    (lead++[i]) pre landed _ _ fullLead R
  have issueCommit : Event hp (fun j=>S.getD j fall) len z door .idle (.busy commitOp (.out 0)) :=
    pcIssue ▸ Event.launch rfl launch
  have trace : BStarNeedTrace.Matched hp base (fun j=>S.getD j fall) len k x pre :=
    ⟨sealFlight,wait1,bitFlight,wait2,commitFlight,rfl,
      ⟨Seal,sealAck,Idle1,away1,bitStart,Bit,bitAck,Idle2,away2,issueCommit,Com⟩⟩
  refine ⟨pre,tail,gate,s,?_,?_,read,noEarly,trace,?_⟩
  · change w=pre++i::tail
    have W' : w=sealFlight++door::((aTail++b)++c) := by
      rw [W,V,A]
      simp only [door,List.append_assoc,List.cons_append]
    have Z' : (aTail++b)++c=wait1++door::(bitFlight++door::(bTail++c)) := by
      rw [Z]
      simp only [door,bitFlight,List.append_assoc,List.cons_append]
    rw [W',Z',Y]
    simp only [door,pre,List.append_assoc,List.cons_append]
  · have mid : gate.Sublist bitFlight :=
      List.sublist_append_of_sublist_right (List.sublist_append_left gate toAck)
    have H₀ : gate.Sublist (bitFlight++door::(wait2++door::commitFlight)) :=
      List.sublist_append_of_sublist_left mid
    have H₁ : gate.Sublist (wait1++door::(bitFlight++door::(wait2++door::commitFlight))) :=
      List.sublist_append_of_sublist_right (H₀.cons door)
    exact List.sublist_append_of_sublist_right (H₁.cons door)
  · refine ⟨custody,?_⟩
    change (longTrace (oldPair B (play x pre) i)
      (((play x pre) i).long,((play x pre) (rightNeighbor i)).long)).publications=[⟨.left,candidate d (firstBit s)⟩] ∧ _
    rw [time]
    exact publish

theorem need_tail_publishes_trace {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len)
    (gateIdx : S.getD g fall=(bSite,1)) (ord : oldOrdinal B base hh bSite=4)
    (lead : List (Fin n))
    (history : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy sealOp (.out k)))
    (pay : Payload) (well : Well pay) (d : Descriptor) (need : d.need=true)
    (oldFacts : let x := play origin lead
      Q x ∧ correct (oldH6 B base) hh 5 x ∧ BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false ∧
      BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (x i).long d=true ∧ readOptional (stage.read (x i).long)=some d ∧
      (centerLink (oldPair B x i),.advance pay)∈actualOffers (oldPair B x i)
        ((x i).long,(x (rightNeighbor i)).long))
    (P : Plan hp base (fun j=>S.getD j fall) len k g)
    (w : List (Fin n)) (sub : (service hp P i bSite).Sublist w) :
    ∃ (pre tail gate : List (Fin n)) (s : Side),
      w=pre++i::tail ∧ gate.Sublist pre ∧ readSegment bSite .fresh gate=some s ∧
      BStarGrantWriterHistory.BeforePublication hp (step (play origin lead) i) i pre ∧
      BStarNeedTrace.Matched hp base (fun j=>S.getD j fall) len k (step (play origin lead) i) pre ∧
      let y := play (step (play origin lead) i) pre
      let b := candidate d (firstBit s)
      (longTrace (oldPair B y i) ((y i).long,(y (rightNeighbor i)).long)).publications=[⟨.left,b⟩] ∧
      readPublication (step y i i).long=(BitVec.ofNat 2 b.val,0,0) := by
  obtain ⟨pre,tail,gate,s,W,U,R,E,T,_,pub⟩ := need_tail_sealed_trace
    hp C Q fiber closed sep i k K idx head own bSite g G gateIdx ord lead history
      pay well d need oldFacts P w sub
  exact ⟨pre,tail,gate,s,W,U,R,E,T,pub⟩

/-- Backward-compatible projection of the exact certified itinerary. -/
theorem need_tail_publishes {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len)
    (gateIdx : S.getD g fall=(bSite,1)) (ord : oldOrdinal B base hh bSite=4)
    (lead : List (Fin n))
    (history : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy sealOp (.out k)))
    (pay : Payload) (well : Well pay) (d : Descriptor) (need : d.need=true)
    (oldFacts : let x := play origin lead
      Q x ∧ correct (oldH6 B base) hh 5 x ∧ BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false ∧
      BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (x i).long d=true ∧ readOptional (stage.read (x i).long)=some d ∧
      (centerLink (oldPair B x i),.advance pay)∈actualOffers (oldPair B x i)
        ((x i).long,(x (rightNeighbor i)).long))
    (P : Plan hp base (fun j=>S.getD j fall) len k g)
    (w : List (Fin n)) (sub : (service hp P i bSite).Sublist w) :
    ∃ (pre tail gate : List (Fin n)) (s : Side),
      w=pre++i::tail ∧ gate.Sublist pre ∧ readSegment bSite .fresh gate=some s ∧
      let y := play (step (play origin lead) i) pre
      let b := candidate d (firstBit s)
      (longTrace (oldPair B y i) ((y i).long,(y (rightNeighbor i)).long)).publications=[⟨.left,b⟩] ∧
      readPublication (step y i i).long=(BitVec.ofNat 2 b.val,0,0) := by
  obtain ⟨pre,tail,gate,s,W,U,R,_,_,pub⟩ := need_tail_publishes_trace
    hp C Q fiber closed sep i k K idx head own bSite g G gateIdx ord lead history
      pay well d need oldFacts P w sub
  exact ⟨pre,tail,gate,s,W,U,R,pub⟩

open BStarAcquireRailCoverage

/-- Construct the 4ℓ+8 cover from the chart and the accepted SEAL.
Its occurrence as a subsequence forces the actual publication with
the bit from the original physical replay. No probabilistic claim. -/
theorem need_tail_service_word {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len)
    (gateIdx : S.getD g fall=(bSite,1)) (ord : oldOrdinal B base hh bSite=4)
    (lead : List (Fin n))
    (history : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy sealOp (.out k)))
    (pay : Payload) (well : Well pay) (d : Descriptor) (need : d.need=true)
    (oldFacts : let x := play origin lead
      Q x ∧ correct (oldH6 B base) hh 5 x ∧ BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false ∧
      BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (x i).long d=true ∧ readOptional (stage.read (x i).long)=some d ∧
      (centerLink (oldPair B x i),.advance pay)∈actualOffers (oldPair B x i)
        ((x i).long,(x (rightNeighbor i)).long))
    (ch : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (ct : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true) :
    ∃ labels : List (Fin n), labels.length=4*len+8 ∧
      ∀ w : List (Fin n), labels.Sublist w →
    ∃ (pre tail gate : List (Fin n)) (s : Side),
      w=pre++i::tail ∧ gate.Sublist pre ∧ readSegment bSite .fresh gate=some s ∧
      let y := play (step (play origin lead) i) pre
      let b := candidate d (firstBit s)
      (longTrace (oldPair B y i) ((y i).long,(y (rightNeighbor i)).long)).publications=[⟨.left,b⟩] ∧
      readPublication (step y i i).long=(BitVec.ofNat 2 b.val,0,0) := by
  obtain ⟨P⟩ := plan_exists hp C ch ct k g K G.2
  exact ⟨service hp P i bSite,service_length hp P i bSite,fun w sub=>
    need_tail_publishes hp C Q fiber closed sep i k K idx head own bSite g G gateIdx ord
      lead history pay well d need oldFacts P w sub⟩

#print axioms need_tail_sealed_trace
#print axioms need_tail_publishes_trace
#print axioms need_tail_publishes
#print axioms need_tail_service_word
end L4.BStarNeedTailService
