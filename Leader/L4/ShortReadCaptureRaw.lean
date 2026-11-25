import Leader.L4.ShortResetMIS1Ring

namespace L4.ShortReadCaptureRaw
open AllSizeProtocol MISByteCodec ShortResetFlow PhysicalCustody
open ShortResetMIS1Ring ShortResetRow

/-- A live READ advances with the exact payload in read_forwardPacket, not
merely one with forward tag. No other owner's bytes are assumed clean. -/
theorem read_out_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (link : destination (header x (rightNeighbor e)) j=some k)
    (F : (oldK (header x e) (x e).mis1 j).tag=2)
    (op : (oldK (header x e) (x e).mis1 j).opcode=3) :
    let y := rawNext s x e
    (kField j).read (y e).mis1=encode T ∧
    (kField k).read (y (rightNeighbor e)).mis1=
      encode (forwardPacket (header x e) (header x (rightNeighbor e))
        (x e).mis1 (x (rightNeighbor e)).mis1 j k) := by
  have P := forward_ready_out_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j k link (read_is_ready _ _ _ F op)
  exact ⟨(work_to_raw x e sep j).1.trans P.1,(work_to_raw x e sep k).2.trans P.2⟩

/-- The terminal carries the exact opcode-3 success or denial bytes. -/
theorem read_turn_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j : Fin 3)
    (link : destination (header x (rightNeighbor e)) j=none)
    (F : (oldK (header x e) (x e).mis1 j).tag=2)
    (op : (oldK (header x e) (x e).mis1 j).opcode=3) :
    (kField j).read (rawNext s x e e).mis1=
      encode (turnPacket (header x e) (header x (rightNeighbor e))
        (x e).mis1 (x (rightNeighbor e)).mis1 j) := by
  have P := forward_ready_turn_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j link (read_is_ready _ _ _ F op)
  exact (work_to_raw x e sep j).1.trans P

#print axioms read_out_raw
#print axioms read_turn_raw
end L4.ShortReadCaptureRaw
