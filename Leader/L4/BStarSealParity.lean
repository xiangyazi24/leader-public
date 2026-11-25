import Leader.L4.BStarSealLanding

namespace L4.BStarSealParity
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongCommand
open BStarLongPublication BStarLongOutgoing

def parity (p : Payload) := p.argument.toNat % 2

/-- A literal accepted SEAL sets the outgoing low bit from precisely the
descriptor it actually installed, not an independent reply bit. -/
theorem accepted_center_polarity (g : LongGeometry) (x : BitVec LW) (p : Payload) (d : Descriptor)
    (head : g.axes.h6=true) (F : p.fault=0) (op : p.opcode.toNat=sealOp)
    (D : BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2))=some d)
    (A : actual x d=true) (stageEq : readOptional (stage.read x)=some d) :
    ∃ q : Payload, (execute g 1 x p).carried=.forward q ∧ q.fault=0 ∧
      q.opcode.toNat=sealOp ∧ parity q=d.need.toNat := by
  refine ⟨{p with argument:=BitVec.ofNat 34 (2*(p.argument.toNat/2)+d.need.toNat)},?_,F,op,?_⟩
  · simp [execute,head,F,op,D,A,stageEq,stageOp,sealOp]
  · change ((2*(p.argument.toNat/2)+d.need.toNat)%(2^34))%2=d.need.toNat
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2^34)]
    cases d.need <;> simp [Nat.add_mod]

/-- The outgoing SEAL parity survives terminal narrowing. This is the
exact local finish function; the physical return flight is separate. -/
theorem finish_keeps_polarity (p : Payload) (F : p.fault=0) (op : p.opcode.toNat=sealOp) :
    ∃ q : Payload, finish p=.reply q ∧ q.fault=0 ∧ q.opcode.toNat=sealOp ∧ q.race=0 ∧ q.outcome=0 ∧
      parity q=parity p := by
  refine ⟨{p with race:=0,outcome:=0,argument:=BitVec.ofNat 34 (parity p)},?_,F,op,rfl,rfl,?_⟩
  · simp [finish,F,op,replyWidth,sealOp,admit,bitOp,acquire,cropped,low,parity]
  · change (p.argument.toNat%2%(2^34))%2=p.argument.toNat%2
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2^34),Nat.mod_mod]

/-- An already healthy normalized SEAL reply remains healthy and keeps
its low bit when bound to any return occurrence. -/
theorem bind_keeps_reply_polarity (g : LongGeometry) (j : Fin 11) (p : Payload)
    (F : p.fault=0) (op : p.opcode.toNat=sealOp) (race : p.race=0) (out : p.outcome=0) :
    ∃ q : Payload, bind g j (.reply p)=.reply q ∧ q.fault=0 ∧ q.opcode.toNat=sealOp ∧
      q.race=0 ∧ q.outcome=0 ∧ parity q=parity p := by
  refine ⟨{p with argument:=BitVec.ofNat 34 (parity p)},?_,F,op,race,out,?_⟩
  · simp [BStarLongCommand.bind,F,op,race,out,replyWidth,sealOp,admit,bitOp,acquire,cropped,low,parity]
  · change (p.argument.toNat%2%(2^34))%2=p.argument.toNat%2
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2^34),Nat.mod_mod]

#print axioms accepted_center_polarity
#print axioms finish_keeps_polarity
#print axioms bind_keeps_reply_polarity
end L4.BStarSealParity
