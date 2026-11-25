import Leader.L4.BStarCopyRightWrappedBank
import Leader.L4.BStarCopyRightAckRetention
import Leader.L4.BStarCopyRightAcquireBank
import Leader.L4.BStarGeneratedBandScan

namespace L4.BStarCopyRightWrappedAck
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedBandScan BStarGeneratedOwner BStarCaptureDoorHistory
open BStarLongDoor BStarLongLayout BStarLongFixedRouting

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run ring

open BStarCopyRightWrappedGeometry BStarCopyRightAckRetention
open BStarLongFiberOwner BStarCaptureInterval BStarLongCommandData BStarCopyRightStrip BStarCommitOperands BStarPostCutOperands BStarClearanceDataChart

/-- The exact controller trace in the post-ACK band supplies the
live-capture mark requirements automatically. A second matching
ACQUIRE installation cannot occur while the old PC is in band. -/

theorem packed_after_actual_ack {base x : X} {cut whole : List (Fin n)}
    (hh : ∃ v,oldH6 B base v=true)
    (owner : Owners (oldH6 B base)) {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh owner S len fall)
    (a : Fin n) (seam tail : Nat) (strip : WrappedStrip B base a seam tail)
    (ownerHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=owner.val)
    (width : seam+r-1≤tail)
    (A : Acquisition hp x cut whole (endpoint (oldH6 B base) hh owner 2).1 2)
    (common : ∃ v,whole=cut++v)
    (ackLead beforeIssue loadTrail after : List (Fin n)) (ack issue : Fin n) (m : Mode)
    (birthBeforeAck : ∃ t,ackLead=A.lead++A.mark::t)
    (loadPrefix : whole=((((ackLead++[ack])++beforeIssue)++issue::loadTrail)++after))
    (history : GeneratedOwner hp base (fun t => S.getD t fall) len
      (ring (play x ackLead) ack) .idle beforeIssue m)
    (region : ∀ p q,beforeIssue=p++q →
      let y := play x ((ackLead++[ack])++p)
      Band y (S.getD 0 fall).1 ∧ (∀ i,Layout B base i=Layout B y i))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ w,oldH6 B (play x (cut++w))=oldH6 B base)
    (auth : ∀ w e z, BStarBodyStageProvenance.BodyAuthority hp (play x (cut++w)) e z
      (endpoint (oldH6 B base) hh owner 2).1)
    (bank : Fin 3)
    (bank8 : bank.val=(captures.read (play x ((ackLead++[ack])++beforeIssue) (S.getD 0 fall).1).long).toNat%4)
    (ack2 : ((capturedSelector 2).read (ring (play x ackLead) ack (S.getD 0 fall).1).long).toNat=
      (BStarLongPublication.readSel ((play x A.lead) (endpoint (oldH6 B base) hh owner 2).1).long).val) :
    ∀ digit : Fin r,
      let i := addr a (seam+digit.val)
      let old := play x (((ackLead++[ack])++beforeIssue)++issue::loadTrail)
      let captured := play x A.lead
      let header := (endpoint (oldH6 B base) hh owner 2).1
      oldBankPacket (old i).long bank =
        oldBankPacket (captured i).long (BStarLongPublication.readSel (captured header).long) := by
  let loadLead := ((ackLead++[ack])++beforeIssue)++issue::loadTrail
  have ackBefore : ∃ t,loadLead=ackLead++ack::t := by
    refine ⟨beforeIssue++issue::loadTrail,?_⟩
    simp [loadLead,List.append_assoc]
  obtain ⟨p,u,P,U,V⟩ := cut_after_matching_ack hp A common ackLead loadLead after ack
    birthBeforeAck ackBefore loadPrefix
  have kept := captures_on_original_cut hp chart sep ackLead beforeIssue ack m history region
  intro d
  dsimp only
  change oldBankPacket ((play x loadLead) (addr a (seam+d.val))).long bank=_
  rw [P]
  exact BStarCopyRightWrappedBank.packed_before_load hp hh owner a seam tail strip ownerHead width A u after p V
    (P.symm.trans U) sep layout auth _ _ bank bank8 kept ack2 d

#print axioms packed_after_actual_ack
end L4.BStarCopyRightWrappedAck
