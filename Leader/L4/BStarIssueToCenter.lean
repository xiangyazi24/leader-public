import Leader.L4.BStarFirstDoorService
import Leader.L4.BStarCommitServiceCenter
import Leader.L4.BStarBitCommitFlight

namespace L4.BStarIssueToCenter
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarLongDoor BStarLongLayout BStarCommitIssue BStarResetChartService BStarClearanceSource
open BStarFirstDoorService BStarCommitHealthyHop

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- A parity-selected ready COMMIT issues at the first actual source
door, then reaches the first actual outgoing center mark under the
fixed physical subsequence. This guarantees the literal itinerary,
not successful publication on an unmatched center seal. -/
theorem ready_commit_service {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (cur : Current hp base (fun j=>S.getD j fall) len x .idle)
    (pc : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=commitOp)
    (d : Desc) (D : BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d)
    (A : Allows (x (S.getD 0 fall).1).long d=true)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    {ls w : List (Fin n)}
    (sub : (RearTrace.predecessor (S.getD 0 fall).1::(ls++[i])).Sublist w) (size : ls.length=k)
    (nom : ∀ j (J : j<ls.length) (y : X), (∀ i,Layout B base i=Layout B y i) →
      linkAt hp y ls[j] (fun t=>S.getD t fall) len j) :
    ∃ wait flight tail, w=wait++RearTrace.predecessor (S.getD 0 fall).1::(flight++i::tail) ∧
      (∀ e∈wait,rightNeighbor e≠(S.getD 0 fall).1) ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle wait .idle ∧
      let door := RearTrace.predecessor (S.getD 0 fall).1
      let s := play x wait
      (ctrlOp.read (s (S.getD 0 fall).1).long).toNat=commitOp ∧
      Launch (s (S.getD 0 fall).1).long ((step s door) (S.getD 0 fall).1).long ∧
      BusyOnly hp base (fun j=>S.getD j fall) len commitOp (step s door) (.out 0) flight (.out k) ∧
      sourceDescriptor.read (s (S.getD 0 fall).1).long=sourceDescriptor.read (x (S.getD 0 fall).1).long ∧
      choice.read (s (S.getD 0 fall).1).long=choice.read (x (S.getD 0 fall).1).long := by
  let door := RearTrace.predecessor (S.getD 0 fall).1
  let root := (S.getD 0 fall).1
  obtain ⟨first,rest,split,hit,after⟩ := List.cons_sublist_iff.mp sub
  obtain ⟨wait,unused,W,away,idle,qs,I,keep,desc,choiceKeep⟩ :=
    first_door_cut hp C Q fiber closed sep qx cur first hit
  let s := play x wait
  let raw : BitVec LW := (s root).long
  have pc' : (ctrlOp.read raw).toNat=commitOp := (congrArg BitVec.toNat keep).trans pc
  have D' : BStarLongPublication.decode (sourceDescriptor.read raw)=some d :=
    (congrArg BStarLongPublication.decode desc).trans D
  have A' : Allows raw d=true := by
    unfold Allows
    rw [show choice.read raw=choice.read (x root).long from choiceKeep]
    exact A
  have legal : initial commitOp raw=some (argument raw) := by
    rw [commit_initial,D']
    simp [A']
  obtain ⟨_,out,launch⟩ := legal_issue_at_door hp C Q fiber closed sep qs I commitOp door rfl pc'
    ⟨_,legal⟩
  obtain ⟨p,P,well⟩ := BStarCommitHealthyFlight.launched_well _ _ pc' launch
  have root0 : (S.getD 0 fall).2=0 := congrArg Prod.snd C.root
  have F : project (fun j=>S.getD j fall) (step s door) 0=.forward p := by
    change atSite (step s door root).long (S.getD 0 fall).2=_
    rwa [root0]
  have afterSub : (ls++[i]).Sublist (unused++rest) := List.sublist_append_of_sublist_right after
  obtain ⟨reach,pause,tail,V,_,_,flight,_⟩ := BStarCommitServiceCenter.center_mark_of_sublist hp
    C Q fiber closed sep k K i idx head p well 0 (Nat.zero_le _) afterSub (by simpa using size)
    (closed _ qs door) out F (fun j h y H=>by simpa only [Nat.zero_add] using nom j h y H)
  refine ⟨wait,reach++pause,tail,?_,away,idle,pc',launch,flight,desc,choiceKeep⟩
  rw [split,W,List.append_assoc,List.cons_append,V,List.append_assoc]

open BStarBitNoAbort BStarLongLandingFrame
open BStarLongLiteral

/-- Supply custody at the actual service cut and publish its exact
ready-source bank. This is decoupled from which code produced readiness. -/
theorem publication_on_service_cut {base s : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (door : Fin n) (flight : List (Fin n)) (d : Desc) (b : Fin 3)
    (pc : (ctrlOp.read (s (S.getD 0 fall).1).long).toNat=commitOp)
    (launch : Launch (s (S.getD 0 fall).1).long ((step s door) (S.getD 0 fall).1).long)
    (T : BusyOnly hp base (fun j=>S.getD j fall) len commitOp (step s door) (.out 0) flight (.out k))
    (D : BStarLongPublication.decode (sourceDescriptor.read (s (S.getD 0 fall).1).long)=some d)
    (choiceEq : choice.read (s (S.getD 0 fall).1).long=BitVec.ofNat 2 b.val)
    (legal : b=d.b0 ∨ (d.need=true ∧ b=d.b1))
    (sealed : SealedCenter d (play (step s door) flight i).long) :
    let y := play (step s door) flight
    (longTrace (oldPair B y i) ((y i).long,(y (rightNeighbor i)).long)).publications=[⟨.left,b⟩] ∧
      readPublication (step y i i).long=(BitVec.ofNat 2 b.val,0,0) := by
  let y := play (step s door) flight
  let g := oldPair B y i
  obtain ⟨p,W,selected⟩ := BStarCommitHealthyFlight.selected_at_center hp C sep door i flight k K
    idx head pc launch T
  have src : S.getD k fall=address i (centerLink g).source := idx
  obtain ⟨D',B'⟩ := BStarBitCommitFlight.offer_from_launch hp C sep door i flight k (Nat.le_of_lt K)
    (centerLink g) p launch T src ⟨W.fault,W.opcode⟩ selected
  have goodD : BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/4))=some d :=
    (congrArg BStarLongPublication.decode D'.symm).trans D
  have bank : p.argument.toNat%4=b.val := B'.symm.trans ((congrArg BitVec.toNat choiceEq).trans (by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]; exact Nat.lt_trans b.isLt (by decide)))
  have h : oldH6 B y i=true :=
    (congrArg Prod.fst ((BStarAcquireHistoryReturn.busy_end hp T).1.1 i)).symm.trans head
  have result := BStarBitCommitPublishes.selected_center_publishes hp y i (centerLink g) p d b h rfl
    selected W.fault W.opcode goodD bank legal sealed.1 sealed.2.1 sealed.2.2.1 sealed.2.2.2
  exact ⟨result.1,result.2.2⟩

end L4.BStarIssueToCenter
