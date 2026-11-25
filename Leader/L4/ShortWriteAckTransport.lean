import Leader.L4.ShortResetMIS1Ring

namespace L4.ShortWriteAckTransport
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow

/-- Exact joined raw step of a STAGE4/SEAL5 forward outside its one
centre effect, or of a sticky fault anywhere. -/
theorem write_ack_forward_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e ≠ rightNeighbor e) (j k : Fin 3) (t : Token)
    (dst : destination (header x (rightNeighbor e)) j = some k)
    (old : oldK (header x e) (x e).mis1 j = t) (tag : t.tag = 2)
    (kind : ((t.opcode = 4 ∨ t.opcode = 5) ∧ (header x e = false ∨ j ≠ 1)) ∨ t.fault = true) :
    (kField j).read (rawNext s x e e).mis1 = encode T ∧
      (kField k).read (rawNext s x e (rightNeighbor e)).mis1 = encode t := by
  have H := write_ack_forward_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j k t dst old tag kind
  exact ⟨(work_to_raw x e sep j).1.trans H.1, (work_to_raw x e sep k).2.trans H.2⟩

/-- Exact joined terminal step: ordinary positive D4/D5 has matching
opcode and zero descriptor payload; a faulty F returns a fault D. -/
theorem write_ack_turn_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e ≠ rightNeighbor e) (j : Fin 3) (t : Token)
    (dst : destination (header x (rightNeighbor e)) j = none)
    (old : oldK (header x e) (x e).mis1 j = t) (tag : t.tag = 2)
    (kind : t.opcode = 4 ∨ t.opcode = 5 ∨ t.fault = true) :
    (kField j).read (rawNext s x e e).mis1 =
      encode (if t.fault then faultToken 3 else {tag := 3, opcode := t.opcode}) := by
  exact (work_to_raw x e sep j).1.trans (write_ack_turn_pair _ _ _ _ j t dst old tag kind)

/-- Exact return step for positive D4/D5 or fault D: neither payload
nor fault is recomputed, and the previous return occurrence is erased. -/
theorem write_ack_back_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e ≠ rightNeighbor e) (j k : Fin 3) (t : Token)
    (dst : destination (header x (rightNeighbor e)) j = some k)
    (trail : oldK (header x e) (x e).mis1 j = T)
    (old : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k = t)
    (tag : t.tag = 3) :
    (kField j).read (rawNext s x e e).mis1 = encode t ∧
      (kField k).read (rawNext s x e (rightNeighbor e)).mis1 = encode E := by
  have N : (oldK (header x e) (x e).mis1 j).tag ≠ 2 := by rw [trail]; decide
  have D : (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag = 3 := by
    rw [old, tag]
  have H := dirty_nonforward_reply_pair _ _ _ _ j k dst N D
  rw [old] at H
  exact ⟨(work_to_raw x e sep j).1.trans H.1, (work_to_raw x e sep k).2.trans H.2⟩

end L4.ShortWriteAckTransport
