import Leader.L4.ShortResetMIS1Ring
import Leader.L4.ShortPacketTag

namespace L4.ShortForwardMIS1Ring
open AllSizeProtocol MISByteCodec ShortResetFlow PhysicalCustody
open ShortResetMIS1Ring ShortResetRow ShortPacketTag

/-- Chosen mark from an arbitrary forward-ready byte leaves a trail
and a forwarded old-row token, independent of off-lane work. -/
theorem inherited_ready_out_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (link : destination (header x (rightNeighbor e)) j=some k)
    (fr : forwardReady (header x e) (x e).mis1 j=true) :
    let y := rawNext s x e
    (kField j).read (y e).mis1=encode T ∧
    (oldK (header y (rightNeighbor e)) (y (rightNeighbor e)).mis1 k).tag=2 := by
  let y := rawNext s x e
  have P := forward_ready_out_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j k link fr
  refine ⟨(work_to_raw x e sep j).1.trans P.1,?_⟩
  have R := (work_to_raw x e sep k).2.trans P.2
  unfold oldK
  rw [R]
  exact forwardPacket_tag _ _ _ _ _ _ fr _

/-- Every chosen ready terminal mark leaves a reply, even when genuine
effect/source validity fails and the encoded reply is a fault. -/
theorem inherited_ready_turn_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j : Fin 3)
    (link : destination (header x (rightNeighbor e)) j=none)
    (fr : forwardReady (header x e) (x e).mis1 j=true) :
    let y := rawNext s x e
    (oldK (header y e) (y e).mis1 j).tag=3 := by
  have P := forward_ready_turn_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j link fr
  have R := (work_to_raw x e sep j).1.trans P
  dsimp only
  unfold oldK
  rw [R]
  exact turnPacket_tag _ _ _ _ _ fr _

end L4.ShortForwardMIS1Ring
