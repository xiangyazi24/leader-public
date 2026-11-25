import Leader.L4.ShortResetMIS1Ring
import Leader.L4.ShortSelectorParity

namespace L4.ShortSelectorFlip
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open AllSizeProtocol MISByteCodec PhysicalCustody
open ShortResetMIS1Ring (header pairIn pairHeader)
open ShortResetRow (selectorGuard selector_right_pair_publish)

theorem selector_responder_raw_publish {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x (rightNeighbor e)=true)
    (G : selectorGuard (header x e) (x e).mis1 (x (rightNeighbor e)).mis1) :
    (rawNext s x e (rightNeighbor e)).mis1.getLsbD 92=
      (((oldK (header x e) (x e).mis1 0).payload/2)%2==1) := by
  have ho : ¬ ShortGeo.mis.owned 92 := fun H => by have E := H.1; change 93≤92 at E; omega
  rw [show rawNext s x e (rightNeighbor e)=(largePair (rows s) (x e,x (rightNeighbor e))).2 by
      simp [rawNext,AllSizeS1Geometry.step,Ne.symm sep]]
  have A := (ShortGeo.work_agrees_outside _ 3 (pairHeader x e) (pairIn x e)
    (BStarShort.shortMIS (pairHeader x e) (pairIn x e)) 92 ho).2
  have B : pairHeader x e=(header x e,true) := by simp [pairHeader,eligible]
  refine A.trans ?_
  rw [B]
  exact selector_right_pair_publish (header x e)
    (x e).mis1 (x (rightNeighbor e)).mis1 G

/-- A real publication flips bit 92, independently of whether the
Boolean stored in the old selected bank is equal to the published Boolean. -/
theorem guarded_commit_flips {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x (rightNeighbor e)=true)
    (G : selectorGuard (header x e) (x e).mis1 (x (rightNeighbor e)).mis1) :
    (rawNext s x e (rightNeighbor e)).mis1.getLsbD 92=
      !((x (rightNeighbor e)).mis1.getLsbD 92) := by
  rw [selector_responder_raw_publish x e sep eligible G]
  rcases G with ⟨_,_,_,_,_,sel,hs,_⟩
  exact ShortSelectorParity.seal_selector_complement _ _ hs sel

end L4.ShortSelectorFlip
