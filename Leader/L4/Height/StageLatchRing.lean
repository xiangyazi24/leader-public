import Leader.L4.Height.StageLatchWrite

namespace L4.Height.StageLatchRing
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongPublication BStarLongLayout BStarLongLiteral BStarLongEvents
open BStarCaptureInterval BStarH6WordChart

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem stage_at_mark (x : X) (i : Fin n) (d : Descriptor) (pay : Payload)
    (head : oldH6 B x i=true)
    (offered : (centerLink (oldPair B x i),.advance pay)∈
      actualOffers (oldPair B x i) ((x i).long,(x (rightNeighbor i)).long))
    (healthy : pay.fault=0) (op : pay.opcode.toNat=stageOp)
    (decoded : BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2^18))=some d)
    (auth : BStarLongOutgoing.actual (x i).long d=true) :
    stage.read (AllSizeS1Geometry.step B x i i).long=packOptional (some d) := by
  simp only [AllSizeS1Geometry.step,if_true]
  have h : (largePair B (x i,x (rightNeighbor i))).1.long = joinedRead (oldPair B x i)
      ((x i).long,(x (rightNeighbor i)).long) .left :=
    joined_read k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x i,x (rightNeighbor i)) .left
  rw [h]
  exact L4.Height.StageLatchWrite.joined_stage_latch _ _ _ pay d head rfl offered healthy op decoded auth

#print axioms stage_at_mark
end L4.Height.StageLatchRing
