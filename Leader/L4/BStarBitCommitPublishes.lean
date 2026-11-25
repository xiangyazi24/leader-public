import Leader.L4.BStarLongLanding
import Leader.L4.BStarGrantWriterHistory
import Leader.L4.BStarBankCapture

namespace L4.BStarBitCommitPublishes
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongClaims
open BStarLongCommand BStarLongEvents BStarLongLayout BStarLongPublication
open BStarLongLanding BStarLongLandingCore BStarLongLiteral BStarGrantWriterHistory
open BStarH6WordChart BStarLongFixedRouting BStarLongLandingFrame

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- A real selected center COMMIT on the sealed header publishes and
lands its bank selector, regardless of which permitted parity branch
was transmitted. No retrospective publication assumption is used. -/
theorem selected_center_publishes (x : X) (e : Fin n) (C : CommandClaim)
    (f : Payload) (d : Descriptor) (b : Fin 3)
    (hh : oldH6 B x e=true) (center : C.source.occurrence.val=1)
    (selected : (C,.advance f)∈actualOffers (oldPair B x e)
      ((x e).long,(x (rightNeighbor e)).long))
    (F : f.fault=0) (op : f.opcode.toNat=commitOp)
    (decoded : BStarLongPublication.decode (BitVec.ofNat 7 (f.argument.toNat/4))=some d)
    (bank : f.argument.toNat%4=b.val)
    (legal : b=d.b0 ∨ (d.need=true ∧ b=d.b1))
    (writer : ((grant 1).read (x e).long).getLsbD 0=true)
    (sel : readSel (x e).long=d.old)
    (staged : readOptional (stage.read (x e).long)=some d)
    (sealed : readOptional (sealField.read (x e).long)=some d) :
    let g := oldPair B x e
    let raw := ((x e).long,(x (rightNeighbor e)).long)
    (longTrace g raw).publications=[⟨.left,b⟩] ∧
      ¬NoPublication hp x e e ∧
      readPublication (step x e e).long=(BitVec.ofNat 2 b.val,0,0) := by
  dsimp only
  let g := oldPair B x e
  let raw := ((x e).long,(x (rightNeighbor e)).long)
  have mem : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,selected,rfl⟩
  have E := center_of g C mem center
  subst C
  let pub : Publication := ⟨.left,b⟩
  have cand : (b==d.b0 || (d.need && b==d.b1))=true := by
    rcases legal with rfl|⟨N,rfl⟩ <;> simp [*]
  have valid := BStarBankCapture.decode_valid decoded
  have G : BStarLongPublication.guard true 1 (x e).long d b=true := by
    simp [BStarLongPublication.guard,typedGuard,writer,sel,staged,sealed,valid,cand]
  have H : LiteralCommit (geometry g (centerLink g).source.side)
      (centerLink g).source (atOld raw (centerLink g).source) f b :=
    ⟨rfl,hh,F,op,d,decoded,bank,G⟩
  have M : pub∈(longTrace g raw).publications :=
    (literal_event_iff g raw pub).mpr ⟨_,f,selected,rfl,H⟩
  have single : (longTrace g raw).publications=[pub] := by
    obtain ⟨pre,post,Q,_⟩ := List.eq_append_cons_of_mem M
    have L := at_most_one_literal_publication g raw
    rw [Q,List.length_append,List.length_cons] at L
    have a : pre=[] := List.length_eq_zero_iff.mp (by omega)
    have b : post=[] := List.length_eq_zero_iff.mp (by omega)
    simp [Q,a,b]
  refine ⟨single,?_,?_⟩
  · intro N
    exact N .left rfl pub M rfl
  · simp only [AllSizeS1Geometry.step,if_true]
    change readPublication (largePair B (x e,x (rightNeighbor e))).1.long=_
    exact bStar_literal_lands k₁ k₂ t₂ J₁ J₂ r c p c₁ hp _ pub M

#print axioms selected_center_publishes
end L4.BStarBitCommitPublishes
