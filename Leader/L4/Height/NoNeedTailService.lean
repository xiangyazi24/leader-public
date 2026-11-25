import Leader.L4.Height.FreshNeedPrefixBand
import Leader.L4.Height.SealAckBoth
import Leader.L4.Height.SealNoNeedAck
import Leader.L4.BStarNeedServicePlan
import Leader.L4.BStarSealAckService
import Leader.L4.BStarIssueBitService
import Leader.L4.BStarIssueToCenter
import Leader.L4.BStarSealCenterAdvance
import Leader.L4.BStarSealTailReplay
import Leader.L4.BStarNeedTrace

namespace L4.Height.NoNeedTailService
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

open BStarSealSafeReplay BStarCommitChoiceHistory BStarSealPositiveTerminal BStarSealModes

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

theorem no_need_tail_trace {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (g : Nat)
    (lead : List (Fin n))
    (history : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy sealOp (.out k)))
    (pay : Payload) (well : Well pay) (d : Descriptor) (need : d.need=false)
    (oldFacts : let x := play origin lead
      Q x ∧ correct (oldH6 B base) hh 5 x ∧ BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false ∧
      BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (x i).long d=true ∧ readOptional (stage.read (x i).long)=some d ∧
      (centerLink (oldPair B x i),.advance pay)∈actualOffers (oldPair B x i)
        ((x i).long,(x (rightNeighbor i)).long))
    (P : Plan hp base (fun j=>S.getD j fall) len k g)
    (w : List (Fin n)) (sub : (sealWord hp P ++ commitWord hp P i).Sublist w) :
    ∃ sf wait flight tail : List (Fin n),
      let x := step (play origin lead) i
      let door := RearTrace.predecessor (S.getD 0 fall).1
      let postSeal := step (play x sf) door
      let commit := play postSeal wait
      w=sf++door::(wait++door::(flight++i::tail)) ∧
      BusyOnly hp base (fun j=>S.getD j fall) len sealOp x (.out (k+1)) sf (.back 0) ∧
      (ctrlOp.read (postSeal (S.getD 0 fall).1).long).toNat=commitOp ∧
      (∀ e∈wait,rightNeighbor e≠(S.getD 0 fall).1) ∧
      (ctrlOp.read (commit (S.getD 0 fall).1).long).toNat=commitOp ∧
      BusyOnly hp base (fun j=>S.getD j fall) len commitOp (step commit door) (.out 0) flight (.out k) ∧
      let y := play (step commit door) flight
      (longTrace (oldPair B y i) ((y i).long,(y (rightNeighbor i)).long)).publications=[⟨.left,d.b0⟩] := by
  let x0 := play origin lead
  let x := step x0 i
  let door := RearTrace.predecessor (S.getD 0 fall).1
  obtain ⟨q0,_,coh,sourceDesc,packedDesc,auth,stageEq,sel⟩ := oldFacts
  have cur := BStarGeneratedTapeCuts.at_end hp history
  obtain ⟨v,seedMark,seedCur,seedWire,seedWell,bit⟩ := BStarSealCenterAdvance.accepted_step hp
    C Q fiber closed sep q0 i k K idx head cur pay well d sel packedDesc auth stageEq
  have seedHistory : BusyOnly hp base (fun j=>S.getD j fall) len sealOp x0 (.out k) [i] (.out (k+1)) :=
    .cons cur seedMark (.nil seedCur)
  have Dseed := (congrArg BStarLongPublication.decode
    (BStarSealBitDescriptor.busy_preserves_descriptor hp C sep seedHistory (by decide)).1).trans sourceDesc
  have qx : Q x := closed _ q0 i
  obtain ⟨a,b,W,sealSub,commitSub⟩ := List.append_sublist_iff.mp sub
  have term : ∀ y : X,Q y→onTerminal hp y P.turn (fun j=>S.getD j fall) len :=
    fun y H=>P.nomTurn y (fiber y H)
  have baseK : oldH6 B base (S.getD k fall).1=true := by rw [idx]; exact head
  obtain ⟨sf,aTail,A,Seal,sealAck,ready,_,_,reply,low⟩ := SealAckBoth.seal_ack_of_sublist hp
    C Q fiber closed sep qx k K (congrArg Prod.snd idx) baseK seedCur v seedWell seedWire d bit
    Dseed P.turn term sealSub P.size409 (by rw [P.sizeBack]; exact Nat.le_refl _) P.nom409 P.nomBack
  let z := play x sf
  let xCommit := step z door
  have qz : Q z := stable_word hp Q closed x sf qx
  have qc : Q xCommit := closed _ qz door
  have curAt := BStarAcquireHistoryReturn.busy_end hp Seal
  have oldDesc := (congrArg BStarLongPublication.decode
    (BStarSealBitDescriptor.busy_preserves_descriptor hp C sep Seal (by decide)).1).trans Dseed
  have root := root_header hp C curAt.1.1
  have parity0 : (sealReply v).argument.toNat%2=0 := low.trans (by rw [need]; rfl)
  obtain ⟨pcCommit,descCommit,choiceCommit,legalCommit,_⟩ := SealNoNeedAck.ready_commit hp
    (addr:=fun j=>S.getD j fall) root.2 root.1 (sep door) curAt sealAck d need (sealReply v)
    seedWell.fault seedWell.opcode parity0 reply oldDesc
  have commitRemainder : (commitWord hp P i).Sublist (aTail++b) :=
    List.sublist_append_of_sublist_right commitSub
  obtain ⟨wait,flight,tail,Y,away,Idle,pcIssue,launch,Com,descIssue,choiceIssue⟩ :=
    BStarIssueToCenter.ready_commit_service hp C Q fiber closed sep qc ready pcCommit d descCommit
      legalCommit i k K idx head commitRemainder P.size411
      (fun j J y H=>by simpa only [Nat.zero_add] using P.nom411 j J y H)
  let pre := sf++door::(wait++door::flight)
  let atCommit := play xCommit wait
  have RSeal := seal_replay hp (i:=i) (k:=k) Seal (by
    intro j J
    have E := Cursor.out.inj J
    omega)
  have WSeal := seal_after_center_safe k (.back 0) (by intro _ H; contradiction)
  have RIdle := foreign_idle_replay hp (i:=i) (k:=k) Idle away
  have RCommit := precenter_commit_replay hp C sep door i flight k K idx head pcIssue launch Com
  have replay : Replay hp base (fun j=>S.getD j fall) len i k x
      (.busy sealOp (.out (k+1))) pre (.busy commitOp (.out k)) := by
    apply append hp RSeal
    apply Replay.cons curAt sealAck ⟨WSeal.2,fun _=>WSeal.1⟩
    apply append hp RIdle
    exact .cons (BStarGeneratedTapeCuts.at_end hp Idle) (pcIssue ▸ Event.launch rfl launch)
      (idle_safe_step i door k) RCommit
  have centerOld (u : List (Fin n)) : oldH6 B (play x u) i=true :=
    (congrArg Prod.fst (fiber _ (stable_word hp Q closed x u qx) i)).symm.trans head
  have rootHead : oldH6 B x0 i=true := (congrArg Prod.fst (fiber x0 q0 i)).symm.trans head
  have center := BStarSealTailReplay.seeded_tail_custody hp C sep i own k (Nat.le_of_lt K) idx
    lead pre pay d history ⟨rootHead,coh,well.fault,well.opcode,packedDesc,auth,stageEq,sel⟩ seedMark replay
    (fun u _ _ _=>centerOld u)
  have time : play x pre=play (step atCommit door) flight := by
    dsimp only [pre,atCommit,xCommit,z]
    rw [BStarResetSchedule.run_append step x sf (door::(wait++door::flight))]
    change play xCommit (wait++door::flight)=_
    exact BStarResetSchedule.run_append step xCommit wait (door::flight)
  have sealed : SealedCenter d (play (step atCommit door) flight i).long := by
    change SealedCenter d (play x pre i).long at center
    rwa [time] at center
  have chosen := choiceIssue.trans choiceCommit
  have valid := (congrArg BStarLongPublication.decode descIssue).trans descCommit
  have publish := BStarIssueToCenter.publication_on_service_cut hp C sep i k K idx head door flight
    d d.b0 pcIssue launch Com valid chosen (.inl rfl) sealed
  refine ⟨sf,wait,flight,tail,?_,Seal,pcCommit,away,pcIssue,Com,publish.1⟩
  change w=sf++door::(wait++door::(flight++i::tail))
  rw [W,A,List.append_assoc,List.cons_append,Y]

open FreshNeedPrefixBand BStarAcquireRailCoverage BStarGrantWriterHistory BStarPhysicalPhase BStarGeneratedTapeCuts

/-- The appended service word proves a deterministic safety fact about
the original miss, not a time or probability estimate. -/
theorem accepted_no_need_seal_on_miss {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (g : Nat) (G : 0<g ∧ g<len)
    (lead : List (Fin n))
    (history : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy sealOp (.out k)))
    (pay : Payload) (well : Well pay) (d : Descriptor) (need : d.need=false)
    (oldFacts : let x := play origin lead
      Q x ∧ correct (oldH6 B base) hh 5 x ∧ BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false ∧
      BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (x i).long d=true ∧ readOptional (stage.read (x i).long)=some d ∧
      (centerLink (oldPair B x i),.advance pay)∈actualOffers (oldPair B x i)
        ((x i).long,(x (rightNeighbor i)).long))
    (ch : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (ct : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (w : List (Fin n))
    (miss : ∀ pre post, w=pre++i::post → NoPublication hp (play (step (play origin lead) i) pre) i i) :
    ∀ u, u<+:w → BStarGeneratedBandScan.pc (play (step (play origin lead) i) u) (S.getD 0 fall).1≠2 := by
  let x := step (play origin lead) i
  let door := RearTrace.predecessor (S.getD 0 fall).1
  let root := (S.getD 0 fall).1
  obtain ⟨P⟩ := plan_exists hp C ch ct k g K G.2
  let labels := sealWord hp P ++ commitWord hp P i
  have sub : labels.Sublist (w++labels) :=
    List.sublist_append_of_sublist_right (List.Sublist.refl labels)
  obtain ⟨sf,wait,flight,tail,Spl,SF,_,away,pcIssue,CF,pub⟩ :=
    no_need_tail_trace hp C Q fiber closed sep i k K idx head own g
      lead history pay well d need oldFacts P (w++labels) sub
  let pre := sf++door::(wait++door::flight)
  let z := step (play x sf) door
  let y := step (play z wait) door
  have time : play x pre=play y flight := by
    dsimp only [pre]
    rw [BStarResetSchedule.run_append step x sf (door::(wait++door::flight))]
    change play z (wait++door::flight)=_
    exact BStarResetSchedule.run_append step z wait (door::flight)
  have pub' : ¬NoPublication hp (play x pre) i i := by
    rw [time]
    intro N
    exact N .left rfl ⟨.left,d.b0⟩ (by rw [pub]; exact List.mem_cons_self) rfl
  have E : w++labels=pre++i::tail := by
    rw [Spl]
    simp only [pre,door,List.append_assoc,List.cons_append]
  have before : BeforePublication hp x i w := by
    intro a e b H
    apply Classical.byContradiction
    intro N
    have equal := BStarNeedPrefix.publication_is_outgoing hp (play x a) e i N
    subst e
    exact N (miss a b H)
  have W := BStarNeedPrefix.prefix_before_first_publish hp x i w labels pre tail E pub' before
  have qx : Q x := closed _ oldFacts.1 i
  have qz : Q z := closed _ (stable_word hp Q closed x sf qx) door
  have headWait (u : List (Fin n)) (_ : u<+:wait) : oldH6 B (play z u) root=true :=
    (root_cuts hp C Q qz (fun y e Y => closed y Y e) fiber u).1
  have X₁ := before_busy hp SF (by decide)
  have X₂ := before_idle hp (i:=root) headWait away (by
    change BStarGeneratedBandScan.pc (play z wait) root≠2
    change BStarGeneratedBandScan.pc (play z wait) root=commitOp at pcIssue
    rw [pcIssue]; decide)
  have X₃ := before_busy hp CF (by decide)
  let Good : X → Prop := fun y => BStarGeneratedBandScan.pc y root≠2
  have all : ∀ u, u<+:pre → Good (play x u) :=
    prefix_append hp (P:=Good) X₁
      (prefix_cons hp (X₁ sf ⟨[],List.append_nil sf⟩)
        (prefix_append hp X₂
          (prefix_cons hp (X₂ wait ⟨[],List.append_nil wait⟩) X₃)))
  exact fun u H => all u (H.trans W)

#print axioms no_need_tail_trace
#print axioms accepted_no_need_seal_on_miss
end L4.Height.NoNeedTailService
