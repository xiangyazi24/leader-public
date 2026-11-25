import Leader.L4.ShortResetMIS1Ring

namespace L4.ShortDirtyMIS1Ring
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow

/-- Exact terminal update of inherited no-forward bytes on the raw MIS1 sheet. -/
theorem dirty_nonforward_terminal_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j : Fin 3)
    (terminal : destination (header x (rightNeighbor e)) j=none)
    (no : (oldK (header x e) (x e).mis1 j).tag≠2) :
    (kField j).read (rawNext s x e e).mis1=
      if (oldK (header x e) (x e).mis1 j).tag=1 then encode E else
        normalizedNoForward (header x e) (x e).mis1 j := by
  exact (work_to_raw x e sep j).1.trans
    (dirty_nonforward_terminal_pair _ _ _ (x (rightNeighbor e)).mis1 j terminal no)

/-- Exact incoming old reply push over the raw MIS1 link, including fault
reply normalization at the preceding tracked slot. -/
theorem dirty_nonforward_reply_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (link : destination (header x (rightNeighbor e)) j=some k)
    (no : (oldK (header x e) (x e).mis1 j).tag≠2)
    (reply : (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag=3) :
    (kField j).read (rawNext s x e e).mis1=
        encode (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k) ∧
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=encode E := by
  have H := dirty_nonforward_reply_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j k link no reply
  exact ⟨(work_to_raw x e sep j).1.trans H.1,(work_to_raw x e sep k).2.trans H.2⟩

/-- Exact inherited no-forward and old-empty update of the raw MIS1 link. -/
theorem dirty_nonforward_empty_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (link : destination (header x (rightNeighbor e)) j=some k)
    (no : (oldK (header x e) (x e).mis1 j).tag≠2)
    (empty : (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag=0) :
    ((kField j).read (rawNext s x e e).mis1=
      (if (oldK (header x e) (x e).mis1 j).tag=1 then encode E else
        normalizedNoForward (header x e) (x e).mis1 j)) ∧
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      normalizedNoForward (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k := by
  have H := dirty_nonforward_empty_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j k link no empty
  exact ⟨(work_to_raw x e sep j).1.trans H.1,(work_to_raw x e sep k).2.trans H.2⟩

#print axioms dirty_nonforward_terminal_raw
#print axioms dirty_nonforward_reply_raw
#print axioms dirty_nonforward_empty_raw
/-- Exact inherited no-forward and old-trail update of the raw MIS1 link. -/
theorem dirty_nonforward_trail_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (link : destination (header x (rightNeighbor e)) j=some k)
    (no : (oldK (header x e) (x e).mis1 j).tag≠2)
    (trail : (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag=1) :
    ((kField j).read (rawNext s x e e).mis1=
      normalizedNoForward (header x e) (x e).mis1 j) ∧
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      normalizedNoForward (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k := by
  have H := dirty_nonforward_trail_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j k link no trail
  exact ⟨(work_to_raw x e sep j).1.trans H.1,(work_to_raw x e sep k).2.trans H.2⟩


#print axioms dirty_nonforward_trail_raw
end L4.ShortDirtyMIS1Ring
