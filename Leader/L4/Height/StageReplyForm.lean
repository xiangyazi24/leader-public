import Leader.L4.BStarStageIssue

namespace L4.Height.StageReplyForm
open BStarLongToken BStarLongCommand

/-- A healthy STAGE has an empty-argument canonical ACK, which the
literal reply binder preserves at every geometry and occurrence. -/
def reply : Payload := ⟨0,BitVec.ofNat 9 stageOp,0,0,0⟩

theorem finish_exact (p : Payload) (F : p.fault=0) (O : p.opcode.toNat=stageOp) :
    finish p=.reply reply := by
  have none : arithKind 408 = none := by decide +kernel
  have pc : p.opcode=BitVec.ofNat 9 stageOp := BitVec.eq_of_toNat_eq (O.trans (by decide : (408:Nat)=(BitVec.ofNat 9 stageOp).toNat))
  simp [finish,F,replyWidth,stageOp,acquire,admit,bitOp,sealOp,none,cropped,low,reply,pc,Nat.mod_one]

theorem bind_exact (g : AllSizeProtocol.LongGeometry) (j : Fin 11) :
    bind g j (.reply reply)=.reply reply := by
  rfl

#print axioms finish_exact
#print axioms bind_exact
end L4.Height.StageReplyForm
