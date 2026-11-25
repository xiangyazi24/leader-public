import Leader.L4.ShortAdmitMIS1Ring

namespace L4.ShortAdmitReturn
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow

/-- On the actual joined row, an ungated forward ADMIT2 propagates its
chosen payload; only an actual gate initializes the race on arrival. -/
theorem admit_ungated_out_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e ≠ rightNeighbor e) (j k : Fin 3) (t : Token)
    (dst : destination (header x (rightNeighbor e)) j = some k)
    (old : oldK (header x e) (x e).mis1 j = t)
    (tag : t.tag = 2) (op : t.opcode = 2) (live : t.fault = false)
    (gate : atGate (header x e) (x e).mis1 j = false) :
    (kField j).read (rawNext s x e e).mis1 = encode T ∧
      (kField k).read (rawNext s x e (rightNeighbor e)).mis1 =
        encode (if atGate (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k then
          {t with race := 1} else t) := by
  have H := admit_ungated_out_pair (header x e) (header x (rightNeighbor e)) (x e).mis1
    (x (rightNeighbor e)).mis1 j k t dst old tag op live gate
  exact ⟨(work_to_raw x e sep j).1.trans H.1, (work_to_raw x e sep k).2.trans H.2⟩

/-- The actual terminal D2 packet contains exactly the won/denied payload
carried by the input, with cleared race, fault, outcome, and applied. -/
theorem admit_turn_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e ≠ rightNeighbor e) (j : Fin 3) (t : Token)
    (dst : destination (header x (rightNeighbor e)) j = none)
    (old : oldK (header x e) (x e).mis1 j = t)
    (tag : t.tag = 2) (op : t.opcode = 2) (live : t.fault = false) :
    (kField j).read (rawNext s x e e).mis1 =
      encode {tag := 3, opcode := 2, payload := t.payload} := by
  exact (work_to_raw x e sep j).1.trans
    (admit_ungated_turn_pair _ _ _ _ j t dst old tag op live (admit_terminal_ungated _ _ _ j dst))

/-- D2 returns over a trail without consulting a new gate decision; the
consumer's port receives the same payload and the old port is cleared. -/
theorem admit_back_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e ≠ rightNeighbor e) (j k : Fin 3) (p : Nat)
    (dst : destination (header x (rightNeighbor e)) j = some k)
    (trail : oldK (header x e) (x e).mis1 j = T)
    (ret : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k =
      {tag := 3, opcode := 2, payload := p}) :
    (kField j).read (rawNext s x e e).mis1 =
      encode {tag := 3, opcode := 2, payload := p} ∧
      (kField k).read (rawNext s x e (rightNeighbor e)).mis1 = encode E := by
  have H := dirty_nonforward_reply_pair _ _ _ _ j k dst
    (show (oldK (header x e) (x e).mis1 j).tag ≠ 2 by rw [trail]; decide)
    (show (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag = 3 by rw [ret])
  rw [ret] at H
  exact ⟨(work_to_raw x e sep j).1.trans H.1, (work_to_raw x e sep k).2.trans H.2⟩

end L4.ShortAdmitReturn
