import Leader.L4.ShortReadResult
import Leader.L4.ShortDirtyMIS1Ring
import Leader.L4.ShortResetCycle

namespace L4.ShortReadReturnHop
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetChart ShortResetCycle ShortResetForwardH2 ShortResetFlow

/-- Canonical non-fault READ response; success retains six bits,
whereas denial certifies failure and retains no capture data. -/
def readReply (ok : Bool) (d : Fin 64) : Token :=
  { tag := 3, opcode := 3, payload := if ok then d.val else 0,
    outcome := if ok then 0 else 1 }

theorem decode_readReply :
    ∀ (g ok : Bool) (d : Fin 64), decode g (encode (readReply ok d))=readReply ok d := by
  decide

theorem read_reply_gate_independent (ok : Bool) (d : Fin 64) (g g' : Bool) :
    decode g (encode (readReply ok d))=decode g' (encode (readReply ok d)) :=
  (decode_readReply g ok d).trans (decode_readReply g' ok d).symm

theorem oldK_readReply (h : Bool) (x : BitVec 96) (k : Fin 3)
    (ok : Bool) (d : Fin 64) (D : (kField k).read x=encode (readReply ok d)) :
    oldK h x k=readReply ok d := by
  unfold oldK
  rw [D,decode_readReply]

/-- The literal one-hop reverse row copies exactly the canonical READ
reply to the predecessor and clears the supplying old slot. It uses
only old inputs; foreign lanes may do arbitrary simultaneous work. -/
theorem read_reverse_one_hop {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (link : ShortResetRow.destination (header x (rightNeighbor e)) j=some k)
    (no : (oldK (header x e) (x e).mis1 j).tag≠2)
    (ok : Bool) (d : Fin 64)
    (D : (kField k).read (x (rightNeighbor e)).mis1=encode (readReply ok d)) :
    let y := rawNext s x e
    (kField j).read (y e).mis1=encode (readReply ok d) ∧
      (kField k).read (y (rightNeighbor e)).mis1=encode E ∧
      oldK (header y e) (y e).mis1 j=readReply ok d := by
  have V := oldK_readReply (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k ok d D
  have F : (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag=3 := by
    rw [V]
    rfl
  obtain ⟨L,R⟩ := ShortDirtyMIS1Ring.dirty_nonforward_reply_raw x e sep j k link no F
  rw [V] at L
  exact ⟨L,R,oldK_readReply _ _ _ ok d L⟩

/-- Lift the literal hop to the frozen owner chart's real predecessor.
The returned datum is the same finite six-bit value, not just the
same tag or opcode. -/
theorem read_reverse_route_hop {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (heads : ∀ q,header x q=h q)
    (i : Nat) (I : i+1<C.L) (trail : bits C.route x i=encode T)
    (ok : Bool) (d : Fin 64) (D : bits C.route x (i+1)=encode (readReply ok d)) :
    let y := rawNext s x (nextAt C.root i)
    bits C.route y i=encode (readReply ok d) ∧
      bits C.route y (i+1)=encode E := by
  let e := nextAt C.root i
  have N := C.length_lt
  have L := C.route.live i I
  change ShortResetRow.destination (h (rightNeighbor e)) (C.route.port i)=some (C.route.port (i+1)) at L
  have V := slot_of_bits C.route x i T trail_decode trail
  have J : (oldK (header x e) (x e).mis1 (C.route.port i)).tag≠2 := by
    change (slot C.route x i).tag≠2
    rw [V]
    decide
  have U := read_reverse_one_hop x e (edge_sep (by omega) e) _ _
    (by rw [heads]; exact L) J ok d D
  exact ⟨U.1,U.2.1⟩

/-- Once the intact successful reply is at K0, the real WAIT3 door
mark stores that very six-bit payload, and clears K0 on the same mark.
The theorem is deliberately not an origin certificate for old K0. -/
theorem read_consume_exact {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (phase : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (cmd : get (x (rightNeighbor e)).mis1 78 3 (by decide)=3)
    (d : Fin 64) (D : (kField 0).read (x (rightNeighbor e)).mis1=encode (readReply true d)) :
    let y := (rawNext s x e (rightNeighbor e)).mis1
    (kField 0).read y=encode E ∧ ShortReadResult.fileField.read y=BitVec.ofNat 6 d.val := by
  have V := oldK_readReply true (x (rightNeighbor e)).mis1 0 true d D
  obtain ⟨K,F⟩ := ShortReadResult.successful_read_store x e sep head phase cmd
    (by rw [V]; rfl) (by rw [V]; rfl) (by rw [V]; rfl) (by rw [V]; rfl)
  rw [V] at F
  exact ⟨K,F⟩

end L4.ShortReadReturnHop
