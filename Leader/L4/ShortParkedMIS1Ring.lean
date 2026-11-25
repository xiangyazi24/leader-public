import Leader.L4.ShortResetMIS1Ring

namespace L4.ShortParkedMIS1Ring
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow

/-- Sampling the incoming parked observation does not change the
non-forward supplying slot's kind. This uses the actual raw row. -/
theorem parked_incoming_predecessor_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (link : destination (header x (rightNeighbor e)) j=some k)
    (no : (oldK (header x e) (x e).mis1 j).tag≠2)
    (target : (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag=2) :
    (kField j).read (rawNext s x e e).mis1=normalizedNoForward (header x e) (x e).mis1 j := by
  exact (work_to_raw x e sep j).1.trans
    (parked_incoming_predecessor_pair _ _ _ _ _ _ link no target)

/-- Sampling the outgoing parked observation does not transport to
the successor; that successor still performs its own normalization. -/
theorem parked_outgoing_successor_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (link : destination (header x (rightNeighbor e)) j=some k)
    (tag : (oldK (header x e) (x e).mis1 j).tag=2)
    (unready : forwardReady (header x e) (x e).mis1 j=false) :
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      parkedNeighborBits (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k := by
  exact (work_to_raw x e sep k).2.trans
    (parked_outgoing_successor_pair _ _ _ _ _ _ link tag unready)

theorem parked_incoming_predecessor_tag_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (link : destination (header x (rightNeighbor e)) j=some k)
    (no : (oldK (header x e) (x e).mis1 j).tag≠2)
    (target : (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag=2) :
    (oldK (header (rawNext s x e) e) (rawNext s x e e).mis1 j).tag=
      (oldK (header x e) (x e).mis1 j).tag := by
  unfold oldK
  rw [parked_incoming_predecessor_raw _ _ sep _ _ link no target]
  exact normalizedNoForward_tag _ _ _ _

theorem parked_outgoing_successor_tag_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (link : destination (header x (rightNeighbor e)) j=some k)
    (tag : (oldK (header x e) (x e).mis1 j).tag=2)
    (unready : forwardReady (header x e) (x e).mis1 j=false) :
    let r := rightNeighbor e
    (oldK (header (rawNext s x e) r) (rawNext s x e r).mis1 k).tag=
      (oldK (header x r) (x r).mis1 k).tag := by
  dsimp only
  unfold oldK
  rw [parked_outgoing_successor_raw _ _ sep _ _ link tag unready]
  exact parkedNeighborBits_tag _ _ _ _

#print axioms parked_incoming_predecessor_raw
#print axioms parked_outgoing_successor_raw
#print axioms parked_incoming_predecessor_tag_raw
#print axioms parked_outgoing_successor_tag_raw
end L4.ShortParkedMIS1Ring
