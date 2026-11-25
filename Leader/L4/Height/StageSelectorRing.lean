import Leader.L4.Height.StageSelectorWrite

namespace L4.Height.StageSelectorRing
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongPublication BStarLongLayout BStarLongLiteral BStarLongEvents
open BStarCaptureInterval BStarH6WordChart

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem selector_at_stage (x : X) (i : Fin n) (d : Descriptor) (pay : Payload)
    (head : oldH6 B x i=true)
    (offered : (centerLink (oldPair B x i),.advance pay)∈
      actualOffers (oldPair B x i) ((x i).long,(x (rightNeighbor i)).long))
    (healthy : pay.fault=0) (op : pay.opcode.toNat=stageOp)
    (decoded : BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2^18))=some d)
    (auth : BStarLongOutgoing.actual (x i).long d=true) :
    selector.read (AllSizeS1Geometry.step B x i i).long=selector.read (x i).long := by
  simp only [AllSizeS1Geometry.step,if_true]
  have h : (largePair B (x i,x (rightNeighbor i))).1.long = joinedRead (oldPair B x i)
      ((x i).long,(x (rightNeighbor i)).long) .left :=
    joined_read k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x i,x (rightNeighbor i)) .left
  rw [h]
  exact L4.Height.StageSelectorWrite.joined_stage_selector _ _ _ pay d head rfl offered healthy op decoded auth

#print axioms selector_at_stage
end L4.Height.StageSelectorRing
