import Leader.Wu.Splice.OrphanToFence
import Leader.Wu.Splice.PhysicalHoldNoBirthSafe
set_option autoImplicit false

/-! Row MOVE-SEEK: the reserved front on the right receives the provenance ticket. -/

namespace B9SpliceV10cRowMoveSeek
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence
variable {n psi kappa tau : Nat}

def moveSeekAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  fun i => if i = ring.rightNeighbor e then setTicketV6 (C i) true else C i

theorem sk_at_j (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    moveSeekAt ring C e (ring.rightNeighbor e) = setTicketV6 (C (ring.rightNeighbor e)) true := by
  simp [moveSeekAt]

theorem sk_at_other (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (h : i ≠ ring.rightNeighbor e) : moveSeekAt ring C e i = C i := by
  simp [moveSeekAt, h]

theorem sk_carrier (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    (moveSeekAt ring C e i).carrier = (C i).carrier := by
  unfold moveSeekAt
  split <;> rfl

theorem sk_dangerAt_iff (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e i : Fin n) :
    PreparedDangerAt hpsi ring (projectV6 (moveSeekAt ring C e)) i ↔
      PreparedDangerAt hpsi ring (projectV6 C) i := by
  unfold PreparedDangerAt PreparedBarrierAt projectSpliceConfig projectV6
  dsimp only
  rw [sk_carrier, sk_carrier]

theorem sk_v3_iff (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    R1ProtectedSpliceEdgeV3 ring (projectV6 (moveSeekAt ring C e)) i ↔
      R1ProtectedSpliceEdgeV3 ring (projectV6 C) i := by
  unfold R1ProtectedSpliceEdgeV3 projectV6
  dsimp only
  rw [sk_carrier, sk_carrier]

theorem moveSeek_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hS : SpliceSafeV7 hpsi ring C)
    (hG : MoveSeekGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7 hpsi ring (moveSeekAt ring C e) := by
  have hset : (C e).carrier.repairPending = false := hG.2.1
  have hfront : ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier := hG.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro i hd
    have hd0 := (sk_dangerAt_iff hpsi ring C e i).1 hd
    have hp := hS.1 i hd0
    unfold ProtectedSpliceEdgeV7 at hp ⊢
    rcases hp with hv | hf
    · exact Or.inl ((sk_v3_iff ring C e i).2 hv)
    · by_cases hi : i = ring.rightNeighbor e
      · exfalso
        rw [hi] at hf
        exact absurd hf.1 (by rw [hfront.1]; decide)
      · right
        rw [sk_at_other ring C e i hi]
        exact hf
  · intro i
    by_cases hi : i = ring.rightNeighbor e
    · rw [hi, sk_at_j]
      intro _
      left
      exact hfront
    · rw [sk_at_other ring C e i hi]
      exact hS.2.1 i
  · intro i hr hp
    rw [sk_carrier] at hr hp
    have hold := hS.2.2 i hr hp
    constructor
    · rw [sk_carrier]; exact hold.1
    · by_cases hj : ring.rightNeighbor i = ring.rightNeighbor e
      · -- the only predecessor pointing at the served front is the settled one
        have hie : i = e := rightNeighbor_inj ring hj
        rw [hie] at hp
        rw [hset] at hp
        cases hp
      · rw [sk_at_other ring C e _ hj]; exact hold.2

end B9SpliceV10cRowMoveSeek
