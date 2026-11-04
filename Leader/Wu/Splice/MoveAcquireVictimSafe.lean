import Leader.Wu.Splice.OrphanToFence
import Leader.Wu.Splice.PhysicalHoldNoBirthSafe
set_option autoImplicit false

/-! Row MOVE-ACQUIRE (legacy): the left pending victim becomes a pending predecessor. -/

namespace B9SpliceV10cRowMoveAcquireLegacy
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence
variable {n psi kappa tau : Nat}

def moveAcquireLegacyAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  fun i => if i = e then setControlV6 (C e) .predecessorArmed true else C i

theorem ma_at_e (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    moveAcquireLegacyAt ring C e e = setControlV6 (C e) .predecessorArmed true := by
  simp [moveAcquireLegacyAt]

theorem ma_at_other (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (h : i ≠ e) : moveAcquireLegacyAt ring C e i = C i := by
  simp [moveAcquireLegacyAt, h]

theorem ma_base_eq (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    (moveAcquireLegacyAt ring C e i).carrier.splice.base = (C i).carrier.splice.base := by
  unfold moveAcquireLegacyAt
  split
  · rename_i h; subst h; rfl
  · rfl

theorem ma_dangerAt_iff (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e x : Fin n) :
    PreparedDangerAt hpsi ring (projectV6 (moveAcquireLegacyAt ring C e)) x ↔
      PreparedDangerAt hpsi ring (projectV6 C) x := by
  unfold PreparedDangerAt PreparedBarrierAt preparedR1 prepared projectSpliceConfig projectV6
  dsimp only
  rw [ma_base_eq, ma_base_eq]

theorem ma_role (u : R1AgentStateV6 psi kappa tau) :
    role (setControlV6 u .predecessorArmed true).carrier = .predecessorArmed := rfl
theorem ma_pending (u : R1AgentStateV6 psi kappa tau) :
    (setControlV6 u .predecessorArmed true).carrier.repairPending = true := rfl
theorem ma_ticket (u : R1AgentStateV6 psi kappa tau) :
    (setControlV6 u .predecessorArmed true).acquireTicket = false := rfl

theorem moveAcquireLegacy_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7 hpsi ring C)
    (hG : MoveAcquireLegacyGuardV6 (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7 hpsi ring (moveAcquireLegacyAt ring C e) := by
  have hvictim : role (C e).carrier = .victimArmed := hG.1.1
  have hvpend : (C e).carrier.repairPending = true := hG.1.2.1
  have hfront : ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier := hG.1.2.2.2
  have hjticket : (C (ring.rightNeighbor e)).acquireTicket = false := hG.2
  refine ⟨?_, ?_, ?_⟩
  · intro x hd
    have hd0 := (ma_dangerAt_iff hpsi ring C e x).1 hd
    have hp := hS.1 x hd0
    by_cases hx : x = e
    · -- the served edge: a pending victim and a reserved front certify nothing here
      subst hx
      exfalso
      rcases hp with hv | hf
      · unfold R1ProtectedSpliceEdgeV3 at hv
        simp only [projectV6] at hv
        rcases hv with h1 | h2 | h3
        · exact absurd h1.1 (by rw [hvictim]; decide)
        · exact absurd h2.1 (by rw [hfront.1]; decide)
        · exact absurd h3.1 (by rw [hvictim]; decide)
      · exact absurd hf.1 (by rw [hvictim]; decide)
    · by_cases hr : ring.rightNeighbor x = e
      · -- the edge into e: a pending victim there is replaced by a pending predecessor
        rcases hp with hv | hf
        · left
          unfold R1ProtectedSpliceEdgeV3 at hv ⊢
          simp only [projectV6] at hv ⊢
          rw [ma_at_other ring C e x hx, hr, ma_at_e]
          rw [hr] at hv
          rcases hv with h1 | h2 | h3
          · exact Or.inl h1
          · exact absurd h2.1 (by rw [hvictim]; decide)
          · exact Or.inr (Or.inr ⟨h3.1, h3.2.1, Or.inr (Or.inr ⟨ma_role _, ma_pending _⟩)⟩)
        · right
          rw [ma_at_other ring C e x hx]
          exact hf
      · unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 at hp ⊢
        simp only [projectV6] at hp ⊢
        rw [ma_at_other ring C e x hx, ma_at_other ring C e _ hr]
        exact hp
  · intro i
    by_cases hi : i = e
    · rw [hi, ma_at_e]
      intro ht
      rw [ma_ticket] at ht
      exact absurd ht (by decide)
    · rw [ma_at_other ring C e i hi]
      exact hS.2.1 i
  · intro i hr hp
    by_cases hi : i = e
    · subst hi
      have hie : ring.rightNeighbor i ≠ i := hne
      rw [ma_at_other ring C i _ hie]
      exact ⟨hfront, hjticket⟩
    · rw [ma_at_other ring C e i hi] at hr hp
      have hold := hS.2.2 i hr hp
      by_cases hj : ring.rightNeighbor i = e
      · rw [hj] at hold
        exact absurd hold.1.1 (by rw [hvictim]; decide)
      · rw [ma_at_other ring C e _ hj]
        exact hold

end B9SpliceV10cRowMoveAcquireLegacy
