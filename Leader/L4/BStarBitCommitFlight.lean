import Leader.L4.BStarBitCommitLegal
import Leader.L4.BStarCommitOwnerOrigin

namespace L4.BStarBitCommitFlight
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims BStarLongLayout
open BStarLongDoor BStarLongCommand BStarLongEvents BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarCommitIssue BStarCommitChoiceHistory
open BStarResetMarkAdapter BStarResetRailRing BStarAcquireForwardTrace

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- A selected healthy offered packet on the actual uninterrupted COMMIT
flight has the descriptor and bank of the launch source. No eventual
publication or center guard is used. -/
theorem offer_from_launch {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (door e : Fin n) (w : List (Fin n)) (i : Nat) (hi : i≤len)
    (K : CommandClaim) (p : Payload)
    (launch : BStarClearanceSource.Launch (x (S.getD 0 fall).1).long ((step x door) (S.getD 0 fall).1).long)
    (flight : BusyOnly hp base (fun j=>S.getD j fall) len commitOp
      (step x door) (.out 0) w (.out i))
    (idx : S.getD i fall=address e K.source)
    (good : BStarCommitPayload.Commit p)
    (sel : let y := play (step x door) w
      (K,.advance p)∈actualOffers (oldPair B y e) ((y e).long,(y (rightNeighbor e)).long)) :
    let src := (x (S.getD 0 fall).1).long
    sourceDescriptor.read src=BStarCommitPayload.descriptorBits p ∧
      (choice.read src).toNat=p.argument.toNat%4 := by
  dsimp only at sel ⊢
  let y := play (step x door) w
  obtain ⟨q,Q,H,E⟩ := BStarCommitPayload.offer_origin _ _ K p sel good
  have F : project (fun j=>S.getD j fall) y i=.forward q :=
    (congrArg (atCursor y) idx).trans ((old_read y e K.source).symm.trans Q)
  obtain ⟨j,J,v,V,hv,A⟩ := BStarCommitOwnerOrigin.busy_origin hp C sep flight i hi q F H
  have cur := busy_start hp flight
  have zero : j=0 := (BStarOwnerControlHistory.pointed_unique_forward _ len 0 cur.2.1 cur.2.2 j J).mp ⟨v,V⟩
  subst j
  obtain ⟨_,a,init,snap⟩ := launch
  have k0 : (S.getD 0 fall).2=0 := congrArg Prod.snd C.root
  let src : BitVec LW := (x (S.getD 0 fall).1).long
  let new : BitVec LW := ((step x door) (S.getD 0 fall).1).long
  change atSite new (S.getD 0 fall).2=.forward v at V
  rw [k0] at V
  have eq : forward (ctrlOp.read src).toNat a=.forward v :=
    (congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.1.1) snap).symm.trans V
  injection eq with E'
  have op : (ctrlOp.read src).toNat=commitOp := by
    have W := congrArg (fun q : Payload => q.opcode.toNat) E'
    change (BitVec.ofNat 9 (ctrlOp.read src).toNat).toNat=v.opcode.toNat at W
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show (ctrlOp.read src).toNat<2^9 from (ctrlOp.read src).isLt)] at W
    exact W.trans hv.2
  have IA : initial commitOp src=some a := op ▸ init
  have argv : low a 9=BStarCommitPayload.arg v := by
    have W : BitVec.ofNat 34 a=v.argument := congrArg Payload.argument E'
    unfold BStarCommitPayload.arg
    rw [←W]
    exact (Nat.mod_mod_of_dvd a (by decide : 2^9 ∣ 2^34)).symm
  have S' := BStarCommitOwnerOrigin.source_choice src a p IA (argv.trans (A.trans E))
  exact ⟨S'.1,S'.2.1⟩

open BStarResetControllerEntry BStarClearanceSource

private theorem foreign_controller_word (x : X) (i : Fin n) (w : List (Fin n))
    (away : ∀ e∈w,rightNeighbor e≠i)
    (head : ∀ u e v,w=u++e::v → oldH6 B (play x u) i=true) :
    let y := play x w
    (ctrlPhase.read (y i).long,ctrlOp.read (y i).long)=
      (ctrlPhase.read (x i).long,ctrlOp.read (x i).long) := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    have off := away e List.mem_cons_self
    have first : (ctrlPhase.read (step x e i).long,ctrlOp.read (step x e i).long)=
        (ctrlPhase.read (x i).long,ctrlOp.read (x i).long) := by
      by_cases is : i=e
      · subst i
        have H := BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
          (x e,x (rightNeighbor e)) (head [] e w rfl)
        simp only [AllSizeS1Geometry.step,if_true]
        exact H
      · simp only [AllSizeS1Geometry.step,if_neg is,if_neg (Ne.symm off)]
    exact (ih (step x e) (fun a H => away a (List.mem_cons_of_mem _ H))
      (fun u a v E => head (e::u) a v (congrArg (List.cons e) E))).trans first

/-- The first next mark entering an ISSUE411 header produces the exact
physical launch, after arbitrary non-owner-door marks. Choice and
descriptor remain the validated ones before that mark. -/
theorem next_door_launch (x : X) (i : Fin n) (wait : List (Fin n)) (door : Fin n)
    (sep : door≠rightNeighbor door) (D : rightNeighbor door=i)
    (away : ∀ e∈wait,rightNeighbor e≠i)
    (head : ∀ u e v,wait=u++e::v → oldH6 B (play x u) i=true)
    (lastHead : oldH6 B (play x wait) i=true)
    (ready : Issue (x i).long) (pc : (ctrlOp.read (x i).long).toNat=commitOp)
    (d : BStarCommitIssue.Desc) (C : BStarLongPublication.decode (sourceDescriptor.read (x i).long)=some d)
    (allowed : Allows (x i).long d=true) :
    let y := play x wait
    Launch (y i).long ((step y door) i).long ∧
      sourceDescriptor.read (y i).long=sourceDescriptor.read (x i).long ∧
      choice.read (y i).long=choice.read (x i).long := by
  dsimp only
  let y := play x wait
  let old : BitVec LW := (x i).long
  let src : BitVec LW := (y i).long
  have ctrl := foreign_controller_word hp x i wait away head
  obtain ⟨ds,cs⟩ := foreign_word hp x i wait away head
  have P : (ctrlPhase.read src).toNat=1 := (congrArg (fun z => z.1.toNat) ctrl).trans ready.2
  have op : (ctrlOp.read src).toNat=commitOp := (congrArg (fun z => z.2.toNat) ctrl).trans pc
  have V : LongDoorGuard.valid manifest src=true := by
    change ((((ctrlPhase.read src).toNat==1) || ((ctrlPhase.read src).toNat==2)) &&
      decide ((ctrlOp.read src).toNat<manifest.opcodes))=true
    simp [P,op,commitOp]
    decide
  have dc : BStarLongPublication.decode (sourceDescriptor.read src)=some d :=
    (congrArg BStarLongPublication.decode ds).trans C
  have A : Allows src d=true := by
    unfold Allows
    rw [show choice.read src=choice.read old from cs]
    exact allowed
  have init : initial (ctrlOp.read src).toNat src=some (argument src) := by
    rw [op,commit_initial,dc]
    simp [A]
  have H := exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (y door,y (rightNeighbor door))
  have join := H (D.symm ▸ lastHead) (D.symm ▸ V) (D.symm ▸ P)
  have actual : (step y door) i=(largePair B (y door,y (rightNeighbor door))).2 := by
    rw [←D]
    simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true]
  have E := congrArg (fun v => snapshot v.long) actual
  refine ⟨⟨⟨V,P⟩,argument src,init,?_⟩,ds,cs⟩
  rw [E,join]
  change (match initial (ctrlOp.read (y (rightNeighbor door)).long).toNat (y (rightNeighbor door)).long with
    | none => ((Token.empty,(1 : BitVec 2)),0)
    | some a => ((forward (ctrlOp.read (y (rightNeighbor door)).long).toNat a,2),
      ctrlOp.read (y (rightNeighbor door)).long))=_
  rw [D]
  rw [show initial (ctrlOp.read (y i).long).toNat (y i).long=some (argument src) from init]

/-- An actual healthy BIT consume, its first subsequent own door, and a
selected healthy advancing COMMIT on that uninterrupted flight carry one
descriptor and the same parity-selected bank. No publication is assumed. -/
theorem selected_after_bit_ack {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (ack door e : Fin n) (wait flight : List (Fin n)) (j : Nat) (J : j≤len)
    (K : CommandClaim) (p f : Payload) (d : BStarCommitIssue.Desc)
    (head : oldH6 B x (S.getD 0 fall).1=true)
    (current : Current hp base (fun k=>S.getD k fall) len x (.busy bitOp (.back 0)))
    (evt : Event hp (fun k=>S.getD k fall) len x ack (.busy bitOp (.back 0)) .idle)
    (ready : Current hp base (fun k=>S.getD k fall) len (step x ack) .idle)
    (F : f.fault=0) (op : f.opcode.toNat=bitOp)
    (R : BStarLongCommand.bind (longGeometry B (x (S.getD 0 fall).1)) 0
      (atSite (x (S.getD 0 fall).1).long 0)=.reply f)
    (D : BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d)
    (need : d.need=true)
    (enters : rightNeighbor door=(S.getD 0 fall).1)
    (away : ∀ a∈wait,rightNeighbor a≠(S.getD 0 fall).1)
    (headers : ∀ u v,wait=u++v → oldH6 B (play (step x ack) u) (S.getD 0 fall).1=true)
    (walk : BusyOnly hp base (fun k=>S.getD k fall) len commitOp
      (step (play (step x ack) wait) door) (.out 0) flight (.out j))
    (idx : S.getD j fall=address e K.source)
    (good : BStarCommitPayload.Commit p)
    (sel : let y := play (step (play (step x ack) wait) door) flight
      (K,.advance p)∈actualOffers (oldPair B y e) ((y e).long,(y (rightNeighbor e)).long)) :
    BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/4))=some d ∧
    p.argument.toNat%4=(pick d f).val := by
  have rootK : (S.getD 0 fall).2=0 := congrArg Prod.snd C.root
  obtain ⟨PC,desc,choiceEq,allowed,_⟩ :=
    BStarBitCommitLegal.actual_bit_ack_allows hp (base:=base) (x:=x) (addr:=fun k=>S.getD k fall) rootK head (sep ack) current evt d f F op R D need
  obtain ⟨launched,descFrame,choiceFrame⟩ := next_door_launch hp (step x ack) (S.getD 0 fall).1 wait door
    (sep door) enters away (fun u a v E => headers u (a::v) E)
    (headers wait [] (List.append_nil _).symm) ready.1 PC d desc allowed
  obtain ⟨bodyDesc,bodyChoice⟩ := offer_from_launch hp C sep door e flight j J K p launched walk idx good sel
  have bodyD := (congrArg BStarLongPublication.decode (bodyDesc.symm.trans descFrame)).trans desc
  have choose := bodyChoice.symm.trans ((congrArg BitVec.toNat choiceFrame).trans (congrArg BitVec.toNat choiceEq))
  exact ⟨bodyD,choose.trans (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]; exact Nat.lt_trans (pick d f).isLt (by decide))⟩

end L4.BStarBitCommitFlight
