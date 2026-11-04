import Leader.Wu.Splice.OrphanToFence
import Leader.Wu.Splice.PhysicalHoldNoBirthSafe
set_option autoImplicit false

/-! Row MOVE-ACQUIRE-ABORT: the left pending victim loses its ticket. -/

namespace B9SpliceV10cRowMoveAcquireAbort
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence
variable {n psi kappa tau : Nat}

def moveAcquireAbortAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  fun i => if i = e then clearTicketV6 (C i) else C i

theorem ab_at_e (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    moveAcquireAbortAt ring C e e = clearTicketV6 (C e) := by simp [moveAcquireAbortAt]

theorem ab_at_other (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (h : i ≠ e) : moveAcquireAbortAt ring C e i = C i := by simp [moveAcquireAbortAt, h]

theorem ab_carrier (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    (moveAcquireAbortAt ring C e i).carrier = (C i).carrier := by
  unfold moveAcquireAbortAt
  split <;> rfl

theorem ab_dangerAt_iff (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e i : Fin n) :
    PreparedDangerAt hpsi ring (projectV6 (moveAcquireAbortAt ring C e)) i ↔
      PreparedDangerAt hpsi ring (projectV6 C) i := by
  unfold PreparedDangerAt PreparedBarrierAt projectSpliceConfig projectV6
  dsimp only
  rw [ab_carrier, ab_carrier]

theorem ab_v3_iff (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    R1ProtectedSpliceEdgeV3 ring (projectV6 (moveAcquireAbortAt ring C e)) i ↔
      R1ProtectedSpliceEdgeV3 ring (projectV6 C) i := by
  unfold R1ProtectedSpliceEdgeV3 projectV6
  dsimp only
  rw [ab_carrier, ab_carrier]

theorem moveAcquireAbort_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hS : SpliceSafeV7 hpsi ring C)
    (hG : MoveAcquireAbortGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7 hpsi ring (moveAcquireAbortAt ring C e) := by
  have hvictim : role (C e).carrier = .victimArmed := hG.1
  refine ⟨?_, ?_, ?_⟩
  · intro i hd
    have hd0 := (ab_dangerAt_iff hpsi ring C e i).1 hd
    have hp := hS.1 i hd0
    unfold ProtectedSpliceEdgeV7 at hp ⊢
    rcases hp with hv | hf
    · exact Or.inl ((ab_v3_iff ring C e i).2 hv)
    · by_cases hi : i = e
      · exfalso
        rw [hi] at hf
        exact absurd hf.1 (by rw [hvictim]; decide)
      · right
        rw [ab_at_other ring C e i hi]
        exact hf
  · intro i
    by_cases hi : i = e
    · rw [hi, ab_at_e]
      intro ht
      have hf : (clearTicketV6 (C e)).acquireTicket = false := rfl
      rw [hf] at ht
      exact absurd ht (by decide)
    · rw [ab_at_other ring C e i hi]
      exact hS.2.1 i
  · intro i hr hp
    rw [ab_carrier] at hr hp
    have hold := hS.2.2 i hr hp
    constructor
    · rw [ab_carrier]; exact hold.1
    · by_cases hj : ring.rightNeighbor i = e
      · rw [hj, ab_at_e]; rfl
      · rw [ab_at_other ring C e _ hj]; exact hold.2

end B9SpliceV10cRowMoveAcquireAbort
