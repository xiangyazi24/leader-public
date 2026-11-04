import Leader.Wu.Splice.OrphanToFence
import Leader.Wu.Splice.PhysicalHoldNoBirthSafe
set_option autoImplicit false

/-! Row PENDING-OWNER-ABORT (V6): only the ticket of the right endpoint is cleared. -/

namespace B9SpliceV10cRowPendingOwnerAbort
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence
variable {n psi kappa tau : Nat}

def pendingOwnerAbortAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  fun i => if i = ring.rightNeighbor e then clearTicketV6 (C i) else C i

theorem poa_at_j (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    pendingOwnerAbortAt ring C e (ring.rightNeighbor e) = clearTicketV6 (C (ring.rightNeighbor e)) := by
  simp [pendingOwnerAbortAt]

theorem poa_at_other (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (h : i ≠ ring.rightNeighbor e) : pendingOwnerAbortAt ring C e i = C i := by
  simp [pendingOwnerAbortAt, h]

theorem poa_carrier (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    (pendingOwnerAbortAt ring C e i).carrier = (C i).carrier := by
  unfold pendingOwnerAbortAt
  split <;> rfl

theorem poa_dangerAt_iff (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e i : Fin n) :
    PreparedDangerAt hpsi ring (projectV6 (pendingOwnerAbortAt ring C e)) i ↔
      PreparedDangerAt hpsi ring (projectV6 C) i := by
  unfold PreparedDangerAt PreparedBarrierAt projectSpliceConfig projectV6
  dsimp only
  rw [poa_carrier, poa_carrier]

theorem poa_v3_iff (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    R1ProtectedSpliceEdgeV3 ring (projectV6 (pendingOwnerAbortAt ring C e)) i ↔
      R1ProtectedSpliceEdgeV3 ring (projectV6 C) i := by
  unfold R1ProtectedSpliceEdgeV3 projectV6
  dsimp only
  rw [poa_carrier, poa_carrier]

theorem pendingOwnerAbort_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hS : SpliceSafeV7 hpsi ring C)
    (hG : PendingOwnerAbortGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7 hpsi ring (pendingOwnerAbortAt ring C e) := by
  have hpredJ : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed := hG.1
  refine ⟨?_, ?_, ?_⟩
  · intro i hd
    have hd0 := (poa_dangerAt_iff hpsi ring C e i).1 hd
    have hp := hS.1 i hd0
    unfold ProtectedSpliceEdgeV7 at hp ⊢
    rcases hp with hv | hf
    · exact Or.inl ((poa_v3_iff ring C e i).2 hv)
    · by_cases hi : i = ring.rightNeighbor e
      · -- the right endpoint is a predecessor, never a fence
        exfalso
        rw [hi] at hf
        exact absurd hf.1 (by rw [hpredJ]; decide)
      · right
        rw [poa_at_other ring C e i hi]
        exact hf
  · intro i
    by_cases hi : i = ring.rightNeighbor e
    · rw [hi, poa_at_j]
      intro ht
      have hf : (clearTicketV6 (C (ring.rightNeighbor e))).acquireTicket = false := rfl
      rw [hf] at ht
      exact absurd ht (by decide)
    · rw [poa_at_other ring C e i hi]
      exact hS.2.1 i
  · intro i hr hp
    rw [poa_carrier] at hr hp
    have hold := hS.2.2 i hr hp
    constructor
    · rw [poa_carrier]; exact hold.1
    · by_cases hj : ring.rightNeighbor i = ring.rightNeighbor e
      · rw [hj, poa_at_j]; rfl
      · rw [poa_at_other ring C e _ hj]; exact hold.2

end B9SpliceV10cRowPendingOwnerAbort
