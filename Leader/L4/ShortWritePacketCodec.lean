import Leader.L4.ShortOwnerSourceTable

namespace L4.ShortWritePacketCodec
open AllSizeProtocol MISByteCodec

def writeFwd (op : Nat) (d : Fin 8) (applied : Bool) : Token :=
  {tag:=2,opcode:=op,payload:=d.val,applied:=applied}

def writeAck (op : Nat) : Token := {tag:=3,opcode:=op}

private theorem fwd_codec_finite :
    ∀ (g : Bool) (op d : Fin 8) (applied : Bool),
      4≤op.val → op.val≤6 → descValid d.val=true →
      decode g (encode (writeFwd op.val d applied)) =
        writeFwd op.val d (op.val==6 && applied) := by decide

theorem decode_write_forward (g : Bool) (op : Nat) (d : Fin 8) (applied : Bool)
    (P : 4≤op) (L : op≤6) (V : descValid d.val=true) :
    decode g (encode (writeFwd op d applied))=writeFwd op d (op==6 && applied) :=
  fwd_codec_finite g ⟨op,by omega⟩ d applied P L V

private theorem ack_codec_finite : ∀ (g : Bool) (o : Fin 8),
    4≤o.val → o.val≤6 → decode g (encode (writeAck o.val))=writeAck o.val := by decide

theorem decode_write_ack (g : Bool) (op : Nat) (P : 4≤op) (L : op≤6) :
    decode g (encode (writeAck op))=writeAck op := ack_codec_finite g ⟨op,by omega⟩ P L

theorem decode_write_faults : ∀ (g : Bool),
    decode g (encode (faultToken 2))=faultToken 2 ∧
      decode g (encode (faultToken 3))=faultToken 3 := by decide

/-- Every literal descriptor from an issued write is one of the four
valid three-bit descriptors, including dirty old file bytes. -/
theorem issued_descriptor_valid (u : BitVec 96) :
    issuedDescriptor u<8 ∧ descValid (issuedDescriptor u)=true := by
  let ix := get u 76 1 (by decide)
  have B : ix<2 := (lane 76 1 (by decide)).read u |>.isLt
  have D : ix=0 ∨ ix=1 := by omega
  let Y := !(u.getLsbD 74 || u.getLsbD 72)
  change 4*ix+2*(1-ix)+Y.toNat<8 ∧ descValid (4*ix+2*(1-ix)+Y.toNat)=true
  rcases D with P|P <;> rw [P] <;> cases Y <;> decide

end L4.ShortWritePacketCodec
