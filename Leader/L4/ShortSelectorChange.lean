import Leader.L4.ShortResetMIS1Ring

namespace L4.ShortSelectorChange
open AllSizeProtocol MISByteCodec PhysicalCustody
open ShortResetMIS1Ring (header pairIn pairHeader reset_remote_frame_raw)
open ShortResetRow (selectorGuard selector_left_pair selector_right_pair_no_guard)

theorem selector_initiator_raw {s n : Nat} (x : Raw s n) (e : Fin n) :
    (rawNext s x e e).mis1.getLsbD 92=(x e).mis1.getLsbD 92 := by
  have ho : ¬ ShortGeo.mis.owned 92 := fun H => by have E := H.1; change 93≤92 at E; omega
  rw [show rawNext s x e e=(largePair (rows s) (x e,x (rightNeighbor e))).1 by
      simp [rawNext,AllSizeS1Geometry.step]]
  have A := (ShortGeo.work_agrees_outside _ 3 (pairHeader x e) (pairIn x e)
    (BStarShort.shortMIS (pairHeader x e) (pairIn x e)) 92 ho).1
  have B := BStarShort.mis_apply_outside (pairHeader x e) (pairIn x e) 92 (.inr (by decide))
  exact A.trans (B.trans (selector_left_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1))

theorem selector_responder_raw_no_guard {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e)
    (G : ¬selectorGuard (header x e) (x e).mis1 (x (rightNeighbor e)).mis1) :
    (rawNext s x e (rightNeighbor e)).mis1.getLsbD 92=
      (x (rightNeighbor e)).mis1.getLsbD 92 := by
  have ho : ¬ ShortGeo.mis.owned 92 := fun H => by have E := H.1; change 93≤92 at E; omega
  rw [show rawNext s x e (rightNeighbor e)=(largePair (rows s) (x e,x (rightNeighbor e))).2 by
      simp [rawNext,AllSizeS1Geometry.step,Ne.symm sep]]
  have A := (ShortGeo.work_agrees_outside _ 3 (pairHeader x e) (pairIn x e)
    (BStarShort.shortMIS (pairHeader x e) (pairIn x e)) 92 ho).2
  exact A.trans (selector_right_pair_no_guard (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 G)

/-- Circulating stale traffic cannot write a selector merely by
touching the victim. Any actual selector change is on the incoming
edge and has an old guarded live unapplied COMMIT in initiator K0. -/
theorem selector_change_incoming_guard {s n : Nat} (x : Raw s n) (e i : Fin n)
    (changed : (rawNext s x e i).mis1.getLsbD 92≠(x i).mis1.getLsbD 92) :
    rightNeighbor e=i ∧ selectorGuard (header x e) (x e).mis1 (x i).mis1 := by
  classical
  have N : i≠e := by
    intro E
    subst i
    exact changed (selector_initiator_raw x e)
  have R : i=rightNeighbor e := by
    by_cases H : i=rightNeighbor e
    · exact H
    · exact False.elim (changed (congrArg (fun b : BitVec 96=>b.getLsbD 92)
        (reset_remote_frame_raw x e i N H)))
  subst i
  refine ⟨rfl,?_⟩
  by_cases H : selectorGuard (header x e) (x e).mis1 (x (rightNeighbor e)).mis1
  · exact H
  · exact False.elim (changed (selector_responder_raw_no_guard x e (Ne.symm N) H))

end L4.ShortSelectorChange
