import Leader.L4.BStarCommitGeneratedTail

namespace L4.Height.SealNoNeedAck
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongLayout
open BStarLongDoor BStarLongCommand BStarCommitIssue BStarCommitChoiceHistory
open BStarGeneratedOwner BStarGeneratedPCAncestry BStarH6WordChart
open BStarAcquireVisitOrder BStarCommitGeneratedTail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- A real no-NEED SEAL reply takes the deterministic bank b0, preserves
the descriptor, and has a defined COMMIT rather than fault reset. -/
theorem ready_commit {base x : X} {addr : Nat→Pos n} {len : Nat} {e : Fin n}
    (H : (addr 0).2=0) (hh : oldH6 B x (addr 0).1=true) (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy sealOp (.back 0)))
    (evt : Event hp addr len x e (.busy sealOp (.back 0)) .idle)
    (d : Desc) (need : d.need=false) (f : Payload) (F : f.fault=0)
    (O : f.opcode.toNat=sealOp) (sign : f.argument.toNat%2=0)
    (R : BStarLongCommand.bind (longGeometry B (x (addr 0).1)) 0
      (atSite (x (addr 0).1).long 0)=.reply f)
    (D : BStarLongPublication.decode (sourceDescriptor.read (x (addr 0).1).long)=some d) :
    let z := (step x e (addr 0).1).long
    (ctrlOp.read z).toNat=commitOp ∧
      BStarLongPublication.decode (sourceDescriptor.read z)=some d ∧
      choice.read z=BitVec.ofNat 2 d.b0.val ∧
      Allows z d=true ∧ initial commitOp z=some (argument z) := by
  dsimp only
  let old : BitVec LW := (x (addr 0).1).long
  let new : BitVec LW := (step x e (addr 0).1).long
  obtain ⟨q,Q,PC⟩ := consume_pc hp H hh sep cur evt
  have eq := Token.reply.inj (Q.symm.trans R)
  subst q
  have shape := seal_pc old f d cur.1.2.2.2 F O D
  have goodPC : (ctrlOp.read new).toNat=411 :=
    PC.trans (by simpa [need,sign] using shape)
  obtain ⟨same,reply,_,select⟩ := selected_tail_result hp H hh sep cur evt d D (.inr (.inr goodPC))
  obtain ⟨_,_,_,bank⟩ := (select goodPC).resolve_right (fun impossible=>by
    have clash : sealOp=bitOp := impossible.1
    exact (by decide : sealOp ≠ bitOp) clash)
  have desc := (congrArg BStarLongPublication.decode same).trans D
  change choice.read new=BitVec.ofNat 2 d.b0.val at bank
  have A : Allows new d=true := by
    unfold Allows
    rw [bank]
    have val : (BitVec.ofNat 2 d.b0.val).toNat = d.b0.val := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      exact Nat.lt_trans d.b0.isLt (by decide)
    simp [val]
  refine ⟨goodPC,desc,bank,A,?_⟩
  change initial commitOp new=some (argument new)
  rw [commit_initial,desc]
  simp [A]

#print axioms ready_commit
end L4.Height.SealNoNeedAck
