import Leader.L4.Height.StageLatchRing
import Leader.L4.BStarSealPackedFrame
import Leader.L4.BStarStageIssue

namespace L4.Height.StageSealPreserve
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongPublication BStarLongLayout BStarLongLiteral BStarLongEvents
open BStarH6WordChart BStarClearanceSource

/-- Every real accepted ISSUE408 with a decoded original source descriptor
emits the canonical healthy stage payload, which binds exactly at any slot. -/
theorem actual_stage_launch (old new : BitVec LW) (op : (ctrlOp.read old).toNat=stageOp)
    (L : Launch old new) (d : Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read old)=some d) :
    atSite new 0=.forward (BStarStageIssue.payload old) ∧
      BStarLongPublication.decode (BitVec.ofNat 7 ((BStarStageIssue.payload old).argument.toNat/2^18))=some d ∧
      (∀ g j, bind g j (.forward (BStarStageIssue.payload old))=.forward (BStarStageIssue.payload old)) := by
  obtain ⟨_,a,I,S⟩ := L
  rw [op,BStarStageIssue.stage_initial,D] at I
  have A : a=BStarStageIssue.argument old := (Option.some.inj I).symm
  have T := congrArg (fun z : (Token × BitVec 2) × BitVec 9 => z.1.1) S
  change atSite new 0=forward (ctrlOp.read old).toNat a at T
  rw [op,A] at T
  exact ⟨T,(BStarStageIssue.issued_descriptor old).trans D,
    fun g j => BStarStageIssue.bound_forward_exact g j old d D⟩

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- A genuine STAGE firing seeds the exact center latch at every cut of
the subsequent old-pair word, provided the center rows are latch-safe
up to (excluding) the next SEAL mark. No validity of the final bytes is assumed. -/
theorem staged_until_seal (x : X) (i : Fin n) (d : Descriptor) (pay : Payload)
    (head : oldH6 B x i=true)
    (offered : (centerLink (oldPair B x i),.advance pay)∈
      actualOffers (oldPair B x i) ((x i).long,(x (rightNeighbor i)).long))
    (healthy : pay.fault=0) (op : pay.opcode.toNat=stageOp)
    (decoded : BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2^18))=some d)
    (auth : BStarLongOutgoing.actual (x i).long d=true)
    (w : List (Fin n)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (safe : ∀ u e v,w=u++e::v →
      oldH6 B (play (step x i) u) i=true ∧
      BStarSealPackedFrame.RingNoLatch hp (play (step x i) u) e i) :
    ∀ a b,w=a++b → stage.read (play (step x i) a i).long=packOptional (some d) := by
  intro a b F
  have frame := BStarSealPackedFrame.word_frame hp (step x i) a i sep (by
    intro u e v G
    exact safe u e (v++b) (by rw [F,G,List.append_assoc,List.cons_append]))
  exact (congrArg (fun z : BitVec 2 × BitVec 8 × BitVec 8=>z.2.1) frame).trans
    (StageLatchRing.stage_at_mark hp x i d pay head offered healthy op decoded auth)

end L4.Height.StageSealPreserve
