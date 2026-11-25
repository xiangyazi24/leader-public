import Leader.L4.ShortResetMIS1Ring
import Leader.L4.ShortResetRow

namespace L4.ShortInboundFrame
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetRow ShortResetFlow
theorem inbound_frame_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (trail : oldK (header x e) (x e).mis1 j=T)
    (safe : InboundToken (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k))
    (wire : (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).fault=true →
      encode (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k)=
        (kField k).read (x (rightNeighbor e)).mis1) :
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField k).read (x (rightNeighbor e)).mis1 :=
  (work_to_raw x e sep k).2.trans (nonparked_inbound_frame_pair _ _ _ _ _ _ dst trail safe wire)

theorem prefix_frame_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (trail : oldK (header x e) (x e).mis1 j=T)
    (safe : InboundToken (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k)) :
    (kField j).read (rawNext s x e e).mis1=(kField j).read (x e).mis1 :=
  (work_to_raw x e sep j).1.trans (nonparked_prefix_trail_frame_pair _ _ _ _ _ _ dst trail safe)

theorem root_frame_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (wait : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (op : get (x (rightNeighbor e)).mis1 78 3 (by decide) < 7)
    (safe : InboundToken (oldK true (x (rightNeighbor e)).mis1 0))
    (wire : (oldK true (x (rightNeighbor e)).mis1 0).fault=true →
      encode (oldK true (x (rightNeighbor e)).mis1 0)=(kField 0).read (x (rightNeighbor e)).mis1) :
    (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField 0).read (x (rightNeighbor e)).mis1 := by
  have H := (work_to_raw x e sep 0).2
  simp only [pairHeader,head] at H
  exact H.trans (nonparked_root_inbound_frame_pair _ _ _ wait op safe wire)

#print axioms inbound_frame_raw
#print axioms prefix_frame_raw
#print axioms root_frame_raw
end L4.ShortInboundFrame
