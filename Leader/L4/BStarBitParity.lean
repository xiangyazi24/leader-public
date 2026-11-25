import Leader.L4.BStarCommitChoiceHistory
import Leader.L4.BStarStageCandidateWrite

namespace L4.BStarBitParity
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongPublication BStarCommitChoiceHistory BStarStageCandidateWrite

/-- A false bit means the gate was first observed as responder
(incoming edge); true means first observed as initiator (outgoing).
These are deterministic local observations, not a probability law. -/
def firstCode (s : Side) : BitVec 3 := if s=.left then 3 else 2
def finalCode (s : Side) : BitVec 3 := if s=.left then 5 else 4
def firstBit (s : Side) : Bool := s==.left

theorem arrival (g : LongGeometry) (p : Payload)
    (H : gate bitOp 1 g=true) (clear : p.fault=0) (op : p.opcode.toNat=bitOp) :
    arrive g 1 p=.forward {p with race:=1,argument:=0} := by
  simp [arrive,clear,op,H]

theorem observe_first (g : LongGeometry) (p : Payload) (s : Side)
    (H : gate bitOp 1 g=true) (clear : p.fault=0) (op : p.opcode.toNat=bitOp) (initial : p.race=1) :
    observe ⟨s,1⟩ g p=some {p with race:=firstCode s} := by
  cases s <;> simp [observe,clear,op,H,initial,firstCode]

theorem observe_follow (g : LongGeometry) (p : Payload) (s u : Side)
    (H : gate bitOp 1 g=true) (clear : p.fault=0) (op : p.opcode.toNat=bitOp)
    (first : p.race=firstCode s) :
    observe ⟨u,1⟩ g p=if u=s then none else some {p with race:=finalCode s} := by
  cases s <;> cases u <;> simp [observe,clear,op,H,first,firstCode,finalCode]

theorem depart_final (g : LongGeometry) (p : Payload) (s : Side)
    (H : gate bitOp 1 g=true) (clear : p.fault=0) (op : p.opcode.toNat=bitOp)
    (done : p.race=finalCode s) :
    depart g 1 p=some {p with race:=0,argument:=BitVec.ofBool (firstBit s) |>.zeroExtend 34} := by
  cases s <;> simp [depart,clear,op,H,done,finalCode,firstBit] <;> rfl

/-- The terminal BIT finish preserves the race argument's low bit. -/
theorem finish_bit (p : Payload) (clear : p.fault=0) (op : p.opcode.toNat=bitOp) :
    finish p=.reply {p with race:=0, outcome:=0, argument:=BitVec.ofNat 34 (p.argument.toNat%2)} := by
  simp [finish,clear,op,replyWidth,bitOp,acquire,admit,low,cropped]

theorem finish_parity (p f : Payload) (clear : p.fault=0) (op : p.opcode.toNat=bitOp)
    (step : finish p=.reply f) : f.argument.toNat%2=p.argument.toNat%2 := by
  rw [finish_bit p clear op] at step
  cases step
  simp only [BitVec.toNat_ofNat]
  have h : p.argument.toNat%2<2 := Nat.mod_lt _ (by decide)
  rw [Nat.mod_eq_of_lt (by omega : p.argument.toNat%2<2^34),Nat.mod_eq_of_lt h]

/-- The matching receipt chooses exactly the published candidate
indexed by the accepted BIT argument's parity; no-NEED uses false. -/
theorem choice_index {op : Nat} {f : Payload} {d : Descriptor} {b}
    (receipt : ChoiceReply op f d b) :
    b=candidate d (d.need && decide (f.argument.toNat%2=1)) := by
  cases receipt with
  | sealCase _ N _ => simp [candidate,N]
  | bit _ N => by_cases P : f.argument.toNat%2=1 <;> simp [candidate,pick,N,P]

#print axioms observe_follow
#print axioms depart_final
#print axioms choice_index
#print axioms finish_parity
end L4.BStarBitParity
