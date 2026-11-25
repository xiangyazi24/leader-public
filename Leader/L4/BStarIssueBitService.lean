import Leader.L4.BStarFirstDoorService
import Leader.L4.BStarBitFullService

namespace L4.BStarIssueBitService
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarLongDoor BStarLongLayout BStarCommitIssue BStarResetChartService BStarClearanceSource
open BStarFirstDoorService BStarH6Ordinal BStarClearanceOffset BStarBitSegment BStarBitParity
open BStarClearanceRaceMark BStarStageCandidateWrite

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem allows_candidate (x : BitVec LW) (d : BStarLongPublication.Descriptor)
    (need : d.need=true) (s : Side)
    (choiceEq : choice.read x=BitVec.ofNat 2 (candidate d (firstBit s)).val) :
    Allows x d=true := by
  have le : (candidate d (firstBit s)).val < 2^2 :=
    Nat.lt_trans (candidate d (firstBit s)).isLt (by decide)
  unfold Allows
  rw [choiceEq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt le]
  cases s <;> simp [candidate,firstBit,need]

/-- Prepend the actual first owner door to the BIT cover. From the
ready state produced by the matched SEAL ACK, any containing raw
word carries the actual legal ISSUE410 and the positive 411 result. -/
theorem ready_bit_service {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (ready : correct (oldH6 B base) hh 5 x)
    (cur : Current hp base (fun j=>S.getD j fall) len x .idle)
    (pc : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=bitOp)
    (d : Desc) (need : d.need=true)
    (D : BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d)
    (i : Fin n) (g : Nat) (G : 0<g ∧ g<len) (idx : S.getD g fall=(i,1)) (O : oldOrdinal B base hh i=4)
    (t : Fin n) (turn : ∀ y : X,Q y→onTerminal hp y t (fun j=>S.getD j fall) len)
    {preGate postGate back w : List (Fin n)}
    (sub : (RearTrace.predecessor (S.getD 0 fall).1 ::
      (preGate++([incident i .left,incident i .right,incident i .left]++
        (postGate++t::(back++[RearTrace.predecessor (S.getD 0 fall).1]))))).Sublist w)
    (preSize : preGate.length=g) (postSize : g+1+postGate.length=len) (backSize : len≤back.length)
    (preNom : ∀ j (J : j<preGate.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y preGate[j] (fun a=>S.getD a fall) len j)
    (postNom : ∀ j (J : j<postGate.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y postGate[j] (fun a=>S.getD a fall) len (g+1+j))
    (backNom : ∀ j (J : j<back.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y back[j] (fun a=>S.getD a fall) len (back.length-(j+1))) :
    ∃ (wait toGate gate toAck tail : List (Fin n)) (s : Side),
      let door := RearTrace.predecessor (S.getD 0 fall).1
      let flight := toGate++(gate++toAck)
      w=wait++door::(flight++door::tail) ∧
      (∀ e∈wait,rightNeighbor e≠(S.getD 0 fall).1) ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle wait .idle ∧
      readSegment i .fresh gate=some s ∧
      let u := play x wait
      let start := step u door
      let y := play start flight
      let fresh := (step y door (S.getD 0 fall).1).long
      Event hp (fun j=>S.getD j fall) len u door .idle (.busy bitOp (.out 0)) ∧
      BusyOnly hp base (fun j=>S.getD j fall) len bitOp start (.out 0) flight (.back 0) ∧
      Event hp (fun j=>S.getD j fall) len y door (.busy bitOp (.back 0)) .idle ∧
      Current hp base (fun j=>S.getD j fall) len (step y door) .idle ∧
      (ctrlOp.read fresh).toNat=commitOp ∧
      BStarLongPublication.decode (sourceDescriptor.read fresh)=some d ∧
      choice.read fresh=BitVec.ofNat 2 (candidate d (firstBit s)).val ∧
      Allows fresh d=true := by
  let door := RearTrace.predecessor (S.getD 0 fall).1
  obtain ⟨first,rest,cut,hit,suffix⟩ := List.cons_sublist_iff.mp sub
  obtain ⟨wait,unused,W,away,idle,qs,I,pcKeep,DKeep,_⟩ :=
    first_door_cut hp C Q fiber closed sep qx cur first hit
  let u := play x wait
  let start := step u door
  have pc' : (ctrlOp.read (u (S.getD 0 fall).1).long).toNat=bitOp :=
    (congrArg BitVec.toNat pcKeep).trans pc
  obtain ⟨Evt,alive,Launch⟩ := legal_issue_at_door hp C Q fiber closed sep qs I bitOp door rfl pc'
    ⟨0,rfl⟩
  have roots := root_header hp C (fiber u qs)
  have newDesc := (BStarCommitGeneratedTail.generated_flight hp (base:=base) (x:=u)
    (addr:=fun j=>S.getD j fall) roots.2 roots.1 (sep door) I Evt (pc' ▸ (by decide : bitOp≠1))
    (fun H=>by cases H.2.1) (fun _=>.inl (by intro H; cases H))).2
  have launchD : BStarLongPublication.decode (sourceDescriptor.read (start (S.getD 0 fall).1).long)=some d :=
    (congrArg BStarLongPublication.decode (newDesc.trans DKeep)).trans D
  have offset (z : X) (w : List (Fin n)) (q : Q z) (r : correct (oldH6 B base) hh 5 z) :
      correct (oldH6 B base) hh 5 (play z w) := by
    induction w generalizing z with
    | nil => exact r
    | cons e w ih =>
      exact ih (step z e) (closed _ q e) (BStarClearanceOffset.stable hp _ hh z e (sep e)
        (fun j=>(congrArg Prod.fst (fiber z q j)).symm) (BStarClearanceOffsetMask.leftFrame hp z e) r)
  have launchReady : correct (oldH6 B base) hh 5 start :=
    offset u [door] qs (offset x wait qx ready)
  obtain ⟨toGate,gate,toAck,tail,s,R,_,trace,F,ack,ready',pc411,valid,choose⟩ :=
    BStarBitFullService.launched_bit_acks_of_sublist hp C Q fiber closed sep i g G idx O door pc'
      Launch (closed _ qs door) launchReady alive t turn d need launchD
      (List.sublist_append_of_sublist_right suffix) preSize postSize backSize preNom postNom backNom
  refine ⟨wait,toGate,gate,toAck,tail,s,?_,away,idle,trace,Evt,F,ack,ready',pc411,valid,choose,
    allows_candidate _ d need s choose⟩
  rw [cut,W,List.append_assoc,List.cons_append,R]
  simp only [List.append_assoc]

#print axioms ready_bit_service
end L4.BStarIssueBitService
