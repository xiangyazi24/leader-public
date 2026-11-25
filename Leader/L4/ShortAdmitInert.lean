import Leader.L4.ShortResetMIS1Ring

namespace L4.ShortAdmitInert
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow

theorem outgoing_race3 {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (j : Fin 3) (t : Token) (old : oldK (header x e) (x e).mis1 j=t)
    (tag : t.tag=2) (op : t.opcode=2) (live : t.fault=false)
    (gate : atGate (header x e) (x e).mis1 j=true) (R : t.race=3) :
    (kField j).read (rawNext s x e e).mis1=(kField j).read (x e).mis1 :=
  (work_to_raw x e sep j).1.trans
    (parked_admit_inert_left_pair _ _ _ _ j t old tag op live gate R)

theorem incoming_race245 {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (src : (oldK (header x e) (x e).mis1 j).tag≠2)
    (t : Token) (old : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=t)
    (tag : t.tag=2) (op : t.opcode=2) (live : t.fault=false)
    (gate : atGate (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=true)
    (R : t.race≠1 ∧ t.race≠3) :
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField k).read (x (rightNeighbor e)).mis1 :=
  (work_to_raw x e sep k).2.trans
    (parked_admit_inert_right_pair _ _ _ _ j k dst src t old tag op live gate R)

theorem trail_before_live {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (j k : Fin 3) (dst : destination (header x (rightNeighbor e)) j=some k)
    (L : oldK (header x e) (x e).mis1 j=T)
    (R : (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag=1 ∨
         (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag=2) :
    (kField j).read (rawNext s x e e).mis1=(kField j).read (x e).mis1 :=
  (work_to_raw x e sep j).1.trans (live_prefix_trail_frame_pair _ _ _ _ j k dst L R)

theorem incoming_ungated {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (src : (oldK (header x e) (x e).mis1 j).tag≠2)
    (t : Token) (old : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=t)
    (tag : t.tag=2) (op : t.opcode=2) (live : t.fault=false)
    (gate : atGate (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=false) :
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField k).read (x (rightNeighbor e)).mis1 :=
  (work_to_raw x e sep k).2.trans
    (ungated_admit_inbound_frame_pair _ _ _ _ j k dst src t old tag op live gate)

theorem root_incoming_wait2 {s n : Nat} (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (head : header x (rightNeighbor e)=true)
    (wait : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (op : get (x (rightNeighbor e)).mis1 78 3 (by decide)<7)
    (live : (oldK true (x (rightNeighbor e)).mis1 0).tag=1 ∨
            (oldK true (x (rightNeighbor e)).mis1 0).tag=2)
    (healthy : (oldK true (x (rightNeighbor e)).mis1 0).fault=false) :
    (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField 0).read (x (rightNeighbor e)).mis1 := by
  have H := (work_to_raw x e sep 0).2
  simp only [pairHeader,pairIn,head] at H
  exact H.trans (live_root_inbound_frame_pair _ _ _ wait op live healthy)

theorem parked_outgoing_right_empty {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (t : Token) (old : oldK (header x e) (x e).mis1 j=t)
    (tag : t.tag=2) (op : t.opcode=2) (live : t.fault=false)
    (gate : atGate (header x e) (x e).mis1 j=true) (race : t.race<4)
    (right : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=E)
    (wire : (kField k).read (x (rightNeighbor e)).mis1=encode E) :
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=encode E :=
  (work_to_raw x e sep k).2.trans
    (parked_outgoing_empty_pair _ _ _ _ j k dst t old tag op live gate race right wire)

#print axioms parked_outgoing_right_empty
#print axioms trail_before_live
#print axioms incoming_ungated
#print axioms root_incoming_wait2
#print axioms outgoing_race3
#print axioms incoming_race245
end L4.ShortAdmitInert
