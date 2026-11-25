import Leader.L4.ShortCommitRowsRaw

namespace L4.ShortCommitFlightRaw
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow ShortWritePacketCodec

theorem fault_relay_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (F : oldK (header x e) (x e).mis1 j=faultToken 2) :
    let y := rawNext s x e
    (kField j).read (y e).mis1=encode T ∧
      (kField k).read (y (rightNeighbor e)).mis1=encode (faultToken 2) := by
  have R := faultToken2_relay_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j k dst F
  exact ⟨(work_to_raw x e sep j).1.trans R.1,(work_to_raw x e sep k).2.trans R.2⟩

theorem fault_turn_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=none)
    (F : oldK (header x e) (x e).mis1 j=faultToken 2) :
    (kField j).read (rawNext s x e e).mis1=encode (faultToken 3) := by
  exact (work_to_raw x e sep j).1.trans (faultToken2_terminal_pair
    (header x e) (header x (rightNeighbor e)) (x e).mis1 (x (rightNeighbor e)).mis1 j dst F)

private theorem decode_commit (g : Bool) (d : Fin 8) (A : Bool)
    (V : descValid d.val=true) :
    decode g (encode (writeFwd 6 d A))=writeFwd 6 d A := by
  simpa using decode_write_forward g 6 d A (by decide) (by decide) V

/-- Outside the centre crossing, both the old descriptor and the applied
bit are preserved literally. The destination decoder is gate-independent. -/
theorem canonical_relay_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (notCentre : ¬(header x (rightNeighbor e)=true ∧ j=0 ∧ k=1))
    (d : Fin 8) (A : Bool) (V : descValid d.val=true)
    (F : (kField j).read (x e).mis1=encode (writeFwd 6 d A)) :
    let y := rawNext s x e
    (kField j).read (y e).mis1=encode T ∧
      (kField k).read (y (rightNeighbor e)).mis1=encode (writeFwd 6 d A) ∧
      oldK (header y (rightNeighbor e)) (y (rightNeighbor e)).mis1 k=writeFwd 6 d A := by
  have O : oldK (header x e) (x e).mis1 j=writeFwd 6 d A := by
    unfold oldK
    rw [F]
    apply decode_commit _ _ _ V
  have R := ShortCommitRowsRaw.relay_out x e sep j k dst
    (congrArg Token.tag O) (congrArg Token.opcode O) notCentre
  rw [O] at R
  refine ⟨R.1,R.2,?_⟩
  unfold oldK
  rw [R.2]
  apply decode_commit _ _ _ V

/-- A successful canonical centre crossing exhibits the publication on
the very same raw mark, not an inferred event at some later reply. -/
theorem canonical_centre_publication_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (d : Fin 8) (V : descValid d.val=true)
    (F : (kField 0).read (x e).mis1=encode (writeFwd 6 d false))
    (G : commitAccept (x (rightNeighbor e)).mis1 (writeFwd 6 d false)=true) :
    let y := rawNext s x e
    (kField 0).read (y e).mis1=encode T ∧
      (kField 1).read (y (rightNeighbor e)).mis1=encode (writeFwd 6 d true) ∧
      oldK (header y (rightNeighbor e)) (y (rightNeighbor e)).mis1 1=writeFwd 6 d true ∧
      (y (rightNeighbor e)).mis1.getLsbD 92=(d.val/2%2==1) := by
  have O : oldK (header x e) (x e).mis1 0=writeFwd 6 d false := by
    unfold oldK
    rw [F]
    apply decode_commit _ _ _ V
  have L := ShortCommitRowsRaw.centre_out x e sep head
    (congrArg Token.tag O) (congrArg Token.opcode O) (congrArg Token.fault O)
  dsimp only at L
  rw [O,if_pos G] at L
  have guard : selectorGuard (header x e) (x e).mis1 (x (rightNeighbor e)).mis1 := by
    apply (selectorGuard_iff_commitAccept _ _ _).2
    rw [O]
    exact ⟨rfl,rfl,rfl,G⟩
  have H := selector_right_pair_publish _ _ _ guard
  rw [O] at H
  have J := selector_right_projection_raw x e sep
  simp only [pairHeader,pairIn,head] at J
  refine ⟨L.1,L.2,?_,J.trans H⟩
  unfold oldK
  rw [L.2]
  apply decode_commit _ _ _ V

/-- A failed canonical centre attempt returns a canonical forward fault,
and leaves the selector unchanged.  This includes duplicate attempts
whose incoming packet already carries the applied bit. -/
theorem canonical_centre_rejected_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (d : Fin 8) (A : Bool) (V : descValid d.val=true)
    (F : (kField 0).read (x e).mis1=encode (writeFwd 6 d A))
    (G : commitAccept (x (rightNeighbor e)).mis1 (writeFwd 6 d A)=false) :
    let y := rawNext s x e
    (kField 0).read (y e).mis1=encode T ∧
      (kField 1).read (y (rightNeighbor e)).mis1=encode (faultToken 2) ∧
      oldK (header y (rightNeighbor e)) (y (rightNeighbor e)).mis1 1=faultToken 2 ∧
      (y (rightNeighbor e)).mis1.getLsbD 92=(x (rightNeighbor e)).mis1.getLsbD 92 := by
  have O : oldK (header x e) (x e).mis1 0=writeFwd 6 d A := by
    unfold oldK
    rw [F]
    apply decode_commit _ _ _ V
  have L := ShortCommitRowsRaw.centre_out x e sep head
    (congrArg Token.tag O) (congrArg Token.opcode O) (congrArg Token.fault O)
  dsimp only at L
  rw [O,G] at L
  have guard : ¬ selectorGuard (header x e) (x e).mis1 (x (rightNeighbor e)).mis1 := by
    intro H
    have B := (selectorGuard_iff_commitAccept _ _ _).1 H
    rw [O,G] at B
    exact Bool.noConfusion B.2.2.2
  have H := selector_right_pair_no_guard _ true _ _ guard
  have J := selector_right_projection_raw x e sep
  simp only [pairHeader,pairIn,head] at J
  refine ⟨L.1,L.2,?_,J.trans H⟩
  unfold oldK
  rw [show (kField 1).read (rawNext s x e (rightNeighbor e)).mis1=encode (faultToken 2) from L.2]
  exact (decode_write_faults _).1

theorem canonical_terminal_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=none)
    (d : Fin 8) (A : Bool) (V : descValid d.val=true)
    (F : (kField j).read (x e).mis1=encode (writeFwd 6 d A)) :
    (kField j).read (rawNext s x e e).mis1=
      encode (if A then writeAck 6 else faultToken 3) := by
  have O : oldK (header x e) (x e).mis1 j=writeFwd 6 d A := by
    unfold oldK
    rw [F]
    apply decode_commit _ _ _ V
  have L := ShortCommitRowsRaw.terminal x e sep j dst
    (congrArg Token.tag O) (congrArg Token.opcode O)
  dsimp only at L
  rw [O] at L
  cases A <;> exact L

#print axioms fault_relay_raw
#print axioms fault_turn_raw
#print axioms canonical_relay_raw
#print axioms canonical_centre_publication_raw
#print axioms canonical_terminal_raw
#print axioms canonical_centre_rejected_raw
end L4.ShortCommitFlightRaw
