import Leader.L4.ShortResetMIS1Ring

namespace L4.ShortResetAuthority
open AllSizeProtocol MISByteCodec ShortResetFlow ShortResetRow PhysicalCustody
open ShortResetMIS1Ring (header pairHeader pairIn)

/-- At each bit below the layout cache, the actual initiator equals the
work patch with the short wrapper's exact support correction. -/
private theorem work_bit {s n : Nat} (x : Raw s n) (e : Fin n) (i : Nat) (hi : i<93) :
    (rawNext s x e e).mis1.getLsbD i =
      (((BStarShort.shortMIS (pairHeader x e) (pairIn x e)).1.apply (x e).mis1)).getLsbD i := by
  have ho : ¬ ShortGeo.mis.owned i := fun H => by have E := H.1; change 93≤i at E; omega
  rw [show rawNext s x e e=(largePair (rows s) (x e,x (rightNeighbor e))).1 by
      simp [rawNext,AllSizeS1Geometry.step]]
  exact (ShortGeo.work_agrees_outside _ 3 (pairHeader x e) (pairIn x e)
    (BStarShort.shortMIS (pairHeader x e) (pairIn x e)) _ ho).1

/-- Each selected RESET0 departure from a lower header clears the owner's
grant at that header, in exactly its own lane; unrelated grants are not
asserted clear. No future frame is presumed. -/
theorem reset_release_grant_raw {s n : Nat} (x : Raw s n) (e : Fin n) (j : Fin 3)
    (eligible : header x e=true) (forward : oldK true (x e).mis1 j=resetForward) :
    (rawNext s x e e).mis1.getLsbD (91-j.val)=false := by
  rw [work_bit x e (91-j.val) (by omega)]
  simpa only [pairHeader,pairIn,eligible] using
    reset_release_grant_pair (header x (rightNeighbor e)) (x e).mis1 (x (rightNeighbor e)).mis1 j forward

/-- The selected RESET0 departure from the center clears all four seal
bits in the actual old-pair join. -/
theorem reset_clear_seal_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (eligible : header x e=true) (forward : oldK true (x e).mis1 1=resetForward) :
    (lane 83 4 (by decide)).read (rawNext s x e e).mis1=0 := by
  have P := reset_clear_seal_pair (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 forward
  have F : (lane 83 4 (by decide)).read (rawNext s x e e).mis1 =
    (lane 83 4 (by decide)).read
      ((BStarShort.shortMIS (pairHeader x e) (pairIn x e)).1.apply (x e).mis1) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [lane,Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    exact work_bit x e (83+i) (by omega)
  exact F.trans (by simpa only [pairHeader,pairIn,eligible] using P)

end L4.ShortResetAuthority
