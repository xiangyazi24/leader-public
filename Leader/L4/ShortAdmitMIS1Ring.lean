import Leader.L4.ShortResetMIS1Ring

namespace L4.ShortAdmitMIS1Ring
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow

/-- The chosen outgoing mark updates the actual MIS1 ADMIT race without
moving the cursor on that same physical mark. -/
theorem parked_admit_left_raw {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (j : Fin 3) (t : Token) (old : oldK (header x e) (x e).mis1 j=t)
    (tag : t.tag=2) (opcode : t.opcode=2) (live : t.fault=false)
    (gate : atGate (header x e) (x e).mis1 j=true)
    (race : t.race=1 ∨ t.race=2) :
    (kField j).read (rawNext s x e e).mis1=
      encode {t with race := if t.race=1 then 3 else 4} := by
  exact (work_to_raw x e sep j).1.trans
    (parked_admit_left_pair _ _ _ _ j t old tag opcode live gate race)

/-- The chosen incoming mark counts for the actual ADMIT only if the
unique supplier's old lane is not forward. -/
theorem parked_admit_right_raw {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (j k : Fin 3)
    (link : destination (header x (rightNeighbor e)) j=some k)
    (upstream : (oldK (header x e) (x e).mis1 j).tag≠2)
    (t : Token) (old : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=t)
    (tag : t.tag=2) (opcode : t.opcode=2) (live : t.fault=false)
    (gate : atGate (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=true)
    (race : t.race=1 ∨ t.race=3) :
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      encode {t with race := if t.race=1 then 2 else 5} := by
  exact (work_to_raw x e sep k).2.trans
    (parked_admit_right_pair _ _ _ _ j k link upstream t old tag opcode live gate race)

theorem ready_admit_out_raw {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (j k : Fin 3)
    (link : destination (header x (rightNeighbor e)) j=some k) (t : Token)
    (old : oldK (header x e) (x e).mis1 j=t)
    (tag : t.tag=2) (opcode : t.opcode=2) (live : t.fault=false)
    (gate : atGate (header x e) (x e).mis1 j=true)
    (race : t.race=4 ∨ t.race=5) :
    (kField j).read (rawNext s x e e).mis1=encode T ∧
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      encode {t with race := if atGate (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k then 1 else 0, payload := t.race-4} := by
  have H := ready_admit_out_pair (header x e) (header x (rightNeighbor e)) (x e).mis1 (x (rightNeighbor e)).mis1 j k link t old tag opcode live gate race
  exact ⟨(work_to_raw x e sep j).1.trans H.1,(work_to_raw x e sep k).2.trans H.2⟩

end L4.ShortAdmitMIS1Ring
