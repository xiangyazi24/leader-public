import Leader.L4.ShortCommitFlightRaw
import Leader.L4.ShortGuardedNOR

namespace L4.ShortCommitGenerationEvent
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow
open ShortWritePacketCodec ShortPublicationClassifier ShortGuardedNOR

theorem old_commit_token {s n : Nat} (x : Raw s n) (e : Fin n)
    (d : Fin 8) (V : descValid d.val=true) (a : Bool)
    (W : (kField 0).read (x e).mis1=encode (writeFwd 6 d a)) :
    oldK (header x e) (x e).mis1 0=writeFwd 6 d a := by
  unfold oldK
  rw [W]
  exact decode_write_forward _ 6 d a (by decide) (by decide) V

/-- At an actual owner center crossing, the checked native classifier
agrees with the old guarded acceptance, even for an identity data write.
Neither a returned ACK nor a general source restart is a publication. -/
theorem classify_center {s n : Nat} {h : Fin n→Bool} (x : Raw s n) (e : Fin n)
    (i : Sites h) (R : rightNeighbor e=i.val)
    (S : e≠rightNeighbor e) (H : header x i.val=true)
    (d : Fin 8) (V : descValid d.val=true) (a : Bool)
    (W : (kField 0).read (x e).mis1=encode (writeFwd 6 d a)) :
    classifyFixed h x e=some i ↔ commitAccept (x i.val).mis1 (writeFwd 6 d a)=true := by
  have O := old_commit_token x e d V a W
  constructor
  · intro C
    have G := (recorded_guard x e i.val ((fixed_some x e i).mp C)).2.2
    have Q := (selectorGuard_iff_commitAccept _ _ _).mp G
    rw [O] at Q
    exact Q.2.2.2
  · intro G
    apply (fixed_some x e i).mpr
    have H' : header x (rightNeighbor e)=true := R.symm ▸ H
    have K : selectorGuard (header x e) (x e).mis1 (x (rightNeighbor e)).mis1 := by
      apply (selectorGuard_iff_commitAccept _ _ _).mpr
      rw [O,R]
      exact ⟨rfl,rfl,rfl,G⟩
    exact (guard_recorded x e S H' K).trans (congrArg some R)

/-- An already-applied token at the guarded incoming crossing never
earns a second event at that target. -/
theorem applied_center_not_counted {s n : Nat} {h : Fin n→Bool}
    (x : Raw s n) (e : Fin n) (i : Sites h) (R : rightNeighbor e=i.val)
    (S : e≠rightNeighbor e) (H : header x i.val=true)
    (d : Fin 8) (V : descValid d.val=true)
    (W : (kField 0).read (x e).mis1=encode (writeFwd 6 d true)) :
    classifyFixed h x e≠some i := by
  intro C
  have G := (classify_center x e i R S H d V true W).mp C
  simp [commitAccept,writeFwd] at G

/-- Last logical handoff for E5, from the *actual saved* READ file.
The flight supplies the descriptor equality; the lease induction supplies
the bit equalities at this old mark. -/
theorem protected_bits_of_actual_saved {s n : Nat} {h : Fin n→Bool}
    (r : ShortNORCover.Ring (Sites h)) (x : Raw s n) (e : Fin n) (i : Sites h)
    (d : Fin 8) (V : descValid d.val=true)
    (W : (kField 0).read (x e).mis1=encode (writeFwd 6 d false))
    (saved : BitVec 96) (D : issuedDescriptor saved=d.val)
    (L : saved.getLsbD 74=observe x (r.left i))
    (P : saved.getLsbD 72=observe x (r.right i)) :
    FromProtectedBits (observe x (r.left i)) (observe x (r.right i))
      (oldK (header x e) (x e).mis1 0).payload := by
  exact ⟨saved,L,P,D.trans (congrArg Token.payload (old_commit_token x e d V false W)).symm⟩

end L4.ShortCommitGenerationEvent
