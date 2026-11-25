import Leader.L4.ShortResetMIS1Ring
import Leader.L4.ShortWritePacketCodec

namespace L4.ShortCommitRowsRaw
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow

/-- Physical center-arrival branch. Success consumes the unapplied
packet into an applied successor; rejection creates the exact fault. -/
theorem centre_out {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (front : (oldK (header x e) (x e).mis1 0).tag=2)
    (op : (oldK (header x e) (x e).mis1 0).opcode=6)
    (live : (oldK (header x e) (x e).mis1 0).fault=false) :
    let y := rawNext s x e
    let t := oldK (header x e) (x e).mis1 0
    (kField 0).read (y e).mis1=encode T ∧
      (kField 1).read (y (rightNeighbor e)).mis1=
        encode (if commitAccept (x (rightNeighbor e)).mis1 t then {t with applied:=true} else faultToken 2) := by
  have A := commit_centre_out_pair (header x e) (x e).mis1 (x (rightNeighbor e)).mis1 front op live
  have L := (work_to_raw x e sep 0).1
  have R := (work_to_raw x e sep 1).2
  simp only [pairHeader,pairIn,head] at L R
  exact ⟨L.trans A.1,R.trans A.2⟩

theorem relay_out {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (front : (oldK (header x e) (x e).mis1 j).tag=2)
    (op : (oldK (header x e) (x e).mis1 j).opcode=6)
    (notCentre : ¬(header x (rightNeighbor e)=true ∧ j=0 ∧ k=1)) :
    let y := rawNext s x e
    (kField j).read (y e).mis1=encode T ∧
      (kField k).read (y (rightNeighbor e)).mis1=encode (oldK (header x e) (x e).mis1 j) := by
  have A := commit_relay_out_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j k dst front op notCentre
  exact ⟨(work_to_raw x e sep j).1.trans A.1,(work_to_raw x e sep k).2.trans A.2⟩

theorem terminal {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=none)
    (front : (oldK (header x e) (x e).mis1 j).tag=2)
    (op : (oldK (header x e) (x e).mis1 j).opcode=6) :
    let t := oldK (header x e) (x e).mis1 j
    (kField j).read (rawNext s x e e).mis1=
        encode (if t.fault || !t.applied then faultToken 3 else ShortWritePacketCodec.writeAck 6) := by
  exact (work_to_raw x e sep j).1.trans
    (commit_terminal_pair (header x e) (header x (rightNeighbor e))
      (x e).mis1 (x (rightNeighbor e)).mis1 j dst front op)

#print axioms centre_out
#print axioms relay_out
#print axioms terminal
end L4.ShortCommitRowsRaw
