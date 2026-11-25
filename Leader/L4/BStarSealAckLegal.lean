import Leader.L4.BStarCommitGeneratedTail

namespace L4.BStarSealAckLegal
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongLayout
open BStarLongDoor BStarLongCommand BStarCommitIssue BStarCommitChoiceHistory
open BStarGeneratedOwner BStarGeneratedPCAncestry BStarH6WordChart
open BStarAcquireVisitOrder BStarCommitGeneratedTail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- A healthy matching SEAL ACK opens BIT only when the low bit authorizes
NEED on the same decoded descriptor. The literal successful branch preserves
that descriptor and gives the legal zero-argument BIT launch. -/
theorem actual_seal_ack_allows_bit {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy sealOp (.back 0)))
    (evt : Event hp addr len x e (.busy sealOp (.back 0)) .idle)
    (d : Desc) (f : Payload) (F : f.fault=0) (O : f.opcode.toNat=sealOp)
    (R : BStarLongCommand.bind (longGeometry B (x (addr 0).1)) 0
      (atSite (x (addr 0).1).long 0)=.reply f)
    (D : BStarLongPublication.decode (sourceDescriptor.read (x (addr 0).1).long)=some d)
    (need : d.need=true) (sign : f.argument.toNat%2=1) :
    let fresh := (step x e (addr 0).1).long
    (ctrlOp.read fresh).toNat=bitOp ∧
      BStarLongPublication.decode (sourceDescriptor.read fresh)=some d ∧
      initial bitOp fresh=some 0 := by
  dsimp only
  obtain ⟨q,Q,PC⟩ := consume_pc hp H hh sep cur evt
  have eq := Token.reply.inj (Q.symm.trans R)
  subst q
  have pc := seal_pc _ f d cur.1.2.2.2 F O D
  have P : (ctrlOp.read (step x e (addr 0).1).long).toNat=410 :=
    PC.trans (by simpa [need,sign] using pc)
  obtain ⟨desc,_,_,_⟩ := selected_tail_result hp H hh sep cur evt d D (.inr (.inl P))
  have decoded : BStarLongPublication.decode (sourceDescriptor.read (step x e (addr 0).1).long)=some d :=
    (congrArg BStarLongPublication.decode desc).trans D
  exact ⟨P,decoded,rfl⟩

open BStarResetControllerEntry BStarClearanceSource

local notation "play" => BStarResetSchedule.run step

theorem away_controller (x : X) (i : Fin n) (w : List (Fin n))
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

/-- The first incoming mark at an ISSUE410 header really launches the
zero-argument BIT tour. The descriptor is the same one already in the
source at the start, both through the preceding wait and on launch. -/
theorem first_door_launches_bit (x : X) (i : Fin n) (wait : List (Fin n)) (door : Fin n)
    (sep : door≠rightNeighbor door) (D : rightNeighbor door=i)
    (away : ∀ e∈wait,rightNeighbor e≠i)
    (head : ∀ u e v,wait=u++e::v → oldH6 B (play x u) i=true)
    (lastHead : oldH6 B (play x wait) i=true)
    (ready : Issue (x i).long) (pc : (ctrlOp.read (x i).long).toNat=bitOp)
    (d : Desc) (C : BStarLongPublication.decode (sourceDescriptor.read (x i).long)=some d) :
    let y := play x wait
    Launch (y i).long ((step y door) i).long ∧
      atSite ((step y door) i).long 0=forward bitOp 0 ∧
      BStarLongPublication.decode (sourceDescriptor.read ((step y door) i).long)=some d := by
  dsimp only
  let y := play x wait
  let src : BitVec LW := (y i).long
  have ctrl := away_controller hp x i wait away head
  obtain ⟨ds,_⟩ := foreign_word hp x i wait away head
  have P : (ctrlPhase.read src).toNat=1 := (congrArg (fun z => z.1.toNat) ctrl).trans ready.2
  have op : (ctrlOp.read src).toNat=bitOp := (congrArg (fun z => z.2.toNat) ctrl).trans pc
  have V : LongDoorGuard.valid manifest src=true := by
    change ((((ctrlPhase.read src).toNat==1) || ((ctrlPhase.read src).toNat==2)) &&
      decide ((ctrlOp.read src).toNat<manifest.opcodes))=true
    simp [P,op,bitOp]
    decide
  have init : initial (ctrlOp.read src).toNat src=some 0 := by rw [op]; rfl
  let pair := (y door,y (rightNeighbor door))
  have H := exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair
  have headPair : (oldHeaders B pair.2).h6=true := by
    change oldH6 B y (rightNeighbor door)=true
    rwa [D]
  have valPair : LongDoorGuard.valid manifest pair.2.long=true := by
    change LongDoorGuard.valid manifest (y (rightNeighbor door)).long=true
    rwa [D]
  have phasePair : (ctrlPhase.read pair.2.long).toNat=1 :=
    (congrArg (fun j => (ctrlPhase.read (y j).long).toNat) D).trans P
  have opPair : (ctrlOp.read pair.2.long).toNat=bitOp :=
    (congrArg (fun j => (ctrlOp.read (y j).long).toNat) D).trans op
  have join := H headPair valPair phasePair
  have actual : (step y door) i=(largePair B pair).2 := by
    rw [←D]
    simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
  have E := congrArg (fun v => snapshot v.long) actual
  have L : snapshot ((step y door) i).long=
      ((forward (ctrlOp.read src).toNat 0,2),ctrlOp.read src) := by
    rw [E,join]
    change (match initial (ctrlOp.read (y (rightNeighbor door)).long).toNat (y (rightNeighbor door)).long with
      | none => ((Token.empty,(1 : BitVec 2)),0)
      | some a => ((forward (ctrlOp.read (y (rightNeighbor door)).long).toNat a,2),
        ctrlOp.read (y (rightNeighbor door)).long))=_
    rw [D]
    rw [show initial (ctrlOp.read (y i).long).toNat (y i).long=some 0 from init]
  have frame := source_flight hp pair headPair valPair bitOp (by decide)
    opPair (Or.inl ⟨phasePair,0,by rfl⟩)
  have descFrame : sourceDescriptor.read ((step y door) i).long=sourceDescriptor.read src := by
    rw [actual]
    exact frame.2.trans (congrArg (fun j => sourceDescriptor.read (y j).long) D)
  refine ⟨⟨⟨V,P⟩,0,init,L⟩,?_,(congrArg BStarLongPublication.decode (descFrame.trans ds)).trans C⟩
  have out : atSite ((step y door) i).long 0=forward (ctrlOp.read src).toNat 0 :=
    congrArg (fun v : (Token × BitVec 2) × BitVec 9 => v.1.1) L
  rwa [op] at out

end L4.BStarSealAckLegal
