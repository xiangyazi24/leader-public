import Leader.L4.ReportOwnerForwardLocations

/-! Literal raw adapter for WRITE and opcode-preserving forward hops. -/
namespace L4.ReportOwnerWriteTransport
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ReportResetBarrier
open ReportResetRawHooks ReportPrelaunchK1Geometry ReportOwnerResetDrain ReportByteRows
open ReportOwnerProvenanceTransport

variable {s n : Nat} {h : Fin n→Bool}

theorem write_hop (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (i : Nat) (I : i+1<C.L) (R : readyAt d C x i=true)
    (H : (tok d C x i).fault=false)
    (L : writeOp (params d s)≤(tok d C x i).opcode)
    (U : (tok d C x i).opcode<sealOp (params d s)) :
    let z := tok d C (rawNext s x (out C i)) (i+1)
    z=tok d C x i ∨ (h (out C i)=true ∧ z=MISByteCodec.faultToken 2) := by
  dsimp only
  rw [predecessor_projection] at H L U
  rw [predecessor_projection d C x i]
  have W := raw_pair_wire d C x N mask i
  rw [tok_wire,W.2]
  exact rank_write_hop_token (params d s) (h (out C i)) (h (rightNeighbor (out C i)))
    (bytesL d x (out C i)) (bytesR d x (out C i)) _ _ (internal_dest C i I) R _ H L U

theorem healthy_hop_opcode (d : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i,lower d (oldHeaders (rows s) (x i))=h i)
    (i : Nat) (I : i+1<C.L) (R : readyAt d C x i=true)
    (H : (tok d C (rawNext s x (out C i)) (i+1)).fault=false) :
    (tok d C (rawNext s x (out C i)) (i+1)).opcode=(tok d C x i).opcode := by
  have W := raw_pair_wire d C x N mask i
  rw [tok_wire,W.2] at H
  rw [tok_wire d C (rawNext s x (out C i)),W.2,predecessor_projection]
  exact rank_healthy_hop_opcode (params d s) (h (out C i)) (h (rightNeighbor (out C i)))
    (bytesL d x (out C i)) (bytesR d x (out C i)) _ _ (internal_dest C i I) R _ H

end L4.ReportOwnerWriteTransport
