import Leader.L4.BStarCommitGeneratedTail

namespace L4.Height.StageAckToSeal
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication
open BStarH6WordChart BStarAcquireVisitOrder BStarGeneratedOwner
open BStarGeneratedPCAncestry BStarCommitGeneratedTail BStarLiteralPC
open BStarResetControllerProgress
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- A matching healthy STAGE receipt actually advances the same source
to ISSUE409, retaining exactly the old decoded descriptor. -/
theorem stage_ack_seal_issue {base x : X} {addr : Nat→Pos n} {len : Nat} {e : Fin n}
    (slot : (addr 0).2=0) (head : oldH6 B x (addr 0).1=true) (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x (.busy stageOp (.back 0)))
    (E : Event hp addr len x e (.busy stageOp (.back 0)) .idle)
    (f : Payload) (ok : f.fault=0) (op : f.opcode.toNat=stageOp)
    (reply : bind (longGeometry B (x (addr 0).1)) 0 (atSite (x (addr 0).1).long 0)=.reply f)
    (d : Descriptor) (D : BStarLongPublication.decode (sourceDescriptor.read (x (addr 0).1).long)=some d) :
    let fresh := (step x e (addr 0).1).long
    (ctrlOp.read fresh).toNat=sealOp ∧
    sourceDescriptor.read fresh=sourceDescriptor.read (x (addr 0).1).long ∧
    BStarLongPublication.decode (sourceDescriptor.read fresh)=some d := by
  dsimp only
  obtain ⟨q,Q,pc⟩ := consume_pc hp slot head sep I E
  have eq := Token.reply.inj (Q.symm.trans reply)
  subst q
  have old := I.1.2.2.2
  have none : arithKind 408 = none := by decide +kernel
  have PC : (ctrlOp.read (step x e (addr 0).1).long).toNat=409 := pc.trans (by
    simp [pcNext,old,ok,op,stageOp,none,nextOrdinary])
  obtain ⟨A,_⟩ := selected_tail_result hp slot head sep I E d D (.inl PC)
  exact ⟨PC,A,(congrArg BStarLongPublication.decode A).trans D⟩

#print axioms stage_ack_seal_issue
end L4.Height.StageAckToSeal
