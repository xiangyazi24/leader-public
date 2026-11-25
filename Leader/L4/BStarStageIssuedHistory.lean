import Leader.L4.BStarStageSourceFrame
import Leader.L4.BStarLiteralPC
import Leader.L4.BStarStageProvenance
import Leader.L4.BStarClearanceSource

namespace L4.BStarStageIssuedHistory
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongTransport BStarLongToken
open BStarH6WordChart BStarLongLayout BStarFinalCandidate BStarLongDoor BStarLongCommand
open BStarStageDescriptorHistory BStarClearanceSource BStarLiteralPC
open BStarResetControllerEntry BStarArithmeticControllerReturn

private theorem next_from_final (x : BitVec LW) (f : Payload)
    (op : (ctrlOp.read x).toNat=lastOp) (F : f.fault=0) (O : f.opcode.toNat=lastOp)
    (h : ((capturedSelector 1).read x).toNat<3) :
    pcNext x f=stageOp := by
  have T : (arithKind lastOp).isSome=true := by decide
  simp only [pcNext,op,F,O,bne_self_eq_false,Bool.false_or,Bool.false_eq_true,if_false,T,if_true]
  unfold successor
  rw [last_node]
  dsimp only
  rw [last_code]
  simp only [show ¬lastOp<407 by decide,if_false,if_pos h]

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- On the actual joined receipt, the center capture is retained and
the controller schedules numerical STAGE, with the descriptor made
from that old capture. -/
theorem final_arrival (x : X) (e : Fin n) (sep : e≠rightNeighbor e) (f : Payload)
    (hdr : oldH6 B x (rightNeighbor e)=true)
    (V : LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true)
    (ph : (ctrlPhase.read (x (rightNeighbor e)).long).toNat=2)
    (op : (ctrlOp.read (x (rightNeighbor e)).long).toNat=lastOp)
    (R : bind (longGeometry B (x (rightNeighbor e))) 0
      (atSite (x (rightNeighbor e)).long 0)=.reply f)
    (F : f.fault=0) (O : f.opcode.toNat=lastOp)
    (h : ((capturedSelector 1).read (x (rightNeighbor e)).long).toNat<3) :
    let i := rightNeighbor e
    let old := (x i).long
    let fresh := (step x e i).long
    snapshot fresh=((.empty,1),BitVec.ofNat 9 stageOp) ∧
    sourceDescriptor.read fresh=BStarLongPublication.encode (finalDesc old h) ∧
    (capturedSelector 1).read fresh=(capturedSelector 1).read old := by
  dsimp only
  let pair := (x e,x (rightNeighbor e))
  have Y : step x e (rightNeighbor e)=(largePair B pair).2 := by
    simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
  rw [Y]
  have A := BStarLiteralPC.joined_reply_PC k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair f hdr V ph R
  have P := next_from_final _ f op F O h
  refine ⟨?_,BStarStageSourceFrame.joined_final_receipt hp pair f hdr V ph op R F O h⟩
  change snapshot (largePair B pair).2.long=
    ((.empty,1),BitVec.ofNat 9 (pcNext (x (rightNeighbor e)).long f)) at A
  rwa [P] at A

/-- Finish the bridge from the actual final receipt through any
foreign tape to the actual STAGE issue. Returning payload equality
is not assumed; the old selected seven bits are framed and decoded. -/
theorem final_to_issue (x : X) (e : Fin n) (sep : e≠rightNeighbor e) (f : Payload)
    (hdr : oldH6 B x (rightNeighbor e)=true)
    (V : LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true)
    (ph : (ctrlPhase.read (x (rightNeighbor e)).long).toNat=2)
    (op : (ctrlOp.read (x (rightNeighbor e)).long).toNat=lastOp)
    (R : bind (longGeometry B (x (rightNeighbor e))) 0
      (atSite (x (rightNeighbor e)).long 0)=.reply f)
    (F : f.fault=0) (O : f.opcode.toNat=lastOp)
    (h : ((capturedSelector 1).read (x (rightNeighbor e)).long).toNat<3)
    (w : List (Fin n))
    (foreign : ∀ m∈w, rightNeighbor m≠rightNeighbor e)
    (header : ∀ u m v, w=u++m::v →
      oldH6 B (run (step x e) u) (rightNeighbor e)=true) :
    let i := rightNeighbor e
    let old := (x i).long
    let z := run (step x e) w
    let wx := (z i).long
    (ctrlOp.read wx).toNat=stageOp →
    Launch wx (step z e i).long →
    ∃ p, atSite (step z e i).long 0=.forward p ∧
      descOfStage p=some (finalDesc old h) ∧ (finalDesc old h).old.val=((capturedSelector 1).read old).toNat := by
  dsimp only
  intro pc L
  let i := rightNeighbor e
  let z := run (step x e) w
  let wx := (z i).long
  have K := (final_arrival hp x e sep f hdr V ph op R F O h).2.1
  have M := (BStarStageSourceFrame.foreign_word hp (step x e) i w foreign header).1
  obtain ⟨arg,args,P⟩ := L.2
  rw [pc] at args P
  let p := (⟨0,BitVec.ofNat 9 stageOp,0,0,BitVec.ofNat 34 arg⟩ : Payload)
  refine ⟨p,congrArg (fun q => q.1.1) P,?_,rfl⟩
  rw [stage_packet wx arg args (show forward stageOp arg=.forward p from rfl),M,K]
  exact decode_final _ h

#print axioms final_arrival
#print axioms final_to_issue
end L4.BStarStageIssuedHistory
