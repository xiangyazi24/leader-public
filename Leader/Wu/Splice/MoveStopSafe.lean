import Leader.Wu.Splice.OrphanToFence
import Leader.Wu.Splice.PhysicalHoldNoBirthSafe
set_option autoImplicit false

/-! Row MOVE-STOP on a leaderless pair: the settled predecessor is cleared and the reserved
front loses its ticket. -/

namespace B9SpliceV10cRowMoveStop
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence
variable {n psi kappa tau : Nat}

def moveStopAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  fun i => if i = e then clearControlV6 (C e)
    else if i = ring.rightNeighbor e then clearTicketV6 (C (ring.rightNeighbor e)) else C i

theorem ms_at_e (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    moveStopAt ring C e e = clearControlV6 (C e) := by simp [moveStopAt]

theorem ms_at_j (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    moveStopAt ring C e (ring.rightNeighbor e) = clearTicketV6 (C (ring.rightNeighbor e)) := by
  simp [moveStopAt, hne]

theorem ms_at_other (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (h1 : i ≠ e) (h2 : i ≠ ring.rightNeighbor e) : moveStopAt ring C e i = C i := by
  simp [moveStopAt, h1, h2]

theorem ms_base_eq (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    (moveStopAt ring C e i).carrier.splice.base = (C i).carrier.splice.base := by
  unfold moveStopAt
  split
  · rename_i h; subst h; rfl
  · split
    · rename_i h; subst h; rfl
    · rfl

theorem ms_dangerAt_iff (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e x : Fin n) :
    PreparedDangerAt hpsi ring (projectV6 (moveStopAt ring C e)) x ↔
      PreparedDangerAt hpsi ring (projectV6 C) x := by
  unfold PreparedDangerAt PreparedBarrierAt preparedR1 prepared projectSpliceConfig projectV6
  dsimp only
  rw [ms_base_eq, ms_base_eq]

theorem ms_role_j (u : R1AgentStateV6 psi kappa tau) : role (clearTicketV6 u).carrier = role u.carrier := rfl
theorem ms_pending_j (u : R1AgentStateV6 psi kappa tau) :
    (clearTicketV6 u).carrier.repairPending = u.carrier.repairPending := rfl
theorem ms_ticket_j (u : R1AgentStateV6 psi kappa tau) : (clearTicketV6 u).acquireTicket = false := rfl

/-- A prepared danger on the served edge is a local prepared barrier. -/
theorem danger_e_barrier (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n) (hd : PreparedDangerAt hpsi ring (projectV6 C) e) :
    LocalPreparedBarrier hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6 projectSpliceConfig at hd
  unfold LocalPreparedBarrier preparedR1
  dsimp only at hd ⊢
  exact hd.2

theorem moveStop_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7 hpsi ring C)
    (hG : MoveStopGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7 hpsi ring (moveStopAt ring C e) := by
  have hpred : role (C e).carrier = .predecessorArmed := hG.1
  have hset : (C e).carrier.repairPending = false := hG.2.1
  have hfront : ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier := hG.2.2.1
  have hnob : ¬ LocalPreparedBarrier hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier := hG.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro x hd
    have hd0 := (ms_dangerAt_iff hpsi ring C e x).1 hd
    have hp := hS.1 x hd0
    by_cases hx : x = e
    · subst hx
      exact absurd (danger_e_barrier hpsi ring C x hd0) hnob
    · by_cases hxj : x = ring.rightNeighbor e
      · -- the reserved front keeps its certificate
        subst hxj
        left
        unfold R1ProtectedSpliceEdgeV3
        simp only [projectV6]
        left
        rw [ms_at_j ring C e hne]
        unfold ReservedFrontHoldGuard at hfront ⊢
        rw [ms_role_j, ms_pending_j]
        exact hfront
      · by_cases hr : ring.rightNeighbor x = e
        · -- the edge into the cleared predecessor: it certified nothing as a right endpoint
          rcases hp with hv | hf
          · left
            unfold R1ProtectedSpliceEdgeV3 at hv ⊢
            simp only [projectV6] at hv ⊢
            rw [ms_at_other ring C e x hx hxj, hr, ms_at_e]
            rw [hr] at hv
            rcases hv with h1 | h2 | h3
            · exact Or.inl h1
            · exact absurd h2.2 (by rw [hset]; decide)
            · rcases h3.2.2 with h4 | h4 | h4
              · exact absurd h4.1 (by rw [hpred]; decide)
              · exact absurd h4.1 (by rw [hpred]; decide)
              · exact absurd h4.2 (by rw [hset]; decide)
          · right
            rw [ms_at_other ring C e x hx hxj]
            exact hf
        · by_cases hrj : ring.rightNeighbor x = ring.rightNeighbor e
          · exact absurd (rightNeighbor_inj ring hrj) hx
          · unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 at hp ⊢
            simp only [projectV6] at hp ⊢
            rw [ms_at_other ring C e x hx hxj, ms_at_other ring C e _ hr hrj]
            exact hp
  · intro i
    by_cases hi : i = e
    · rw [hi, ms_at_e]
      intro ht
      rw [clearControl_ticket] at ht
      exact absurd ht (by decide)
    · by_cases hj : i = ring.rightNeighbor e
      · rw [hj, ms_at_j ring C e hne]
        intro ht
        rw [ms_ticket_j] at ht
        exact absurd ht (by decide)
      · rw [ms_at_other ring C e i hi hj]
        exact hS.2.1 i
  · intro i hr hp
    by_cases hi : i = e
    · rw [hi, ms_at_e, clearControl_role] at hr
      exact absurd hr (by decide)
    · by_cases hj : i = ring.rightNeighbor e
      · rw [hj, ms_at_j ring C e hne, ms_role_j] at hr
        exact absurd hr (by rw [hfront.1]; decide)
      · rw [ms_at_other ring C e i hi hj] at hr hp
        have hold := hS.2.2 i hr hp
        by_cases h1 : ring.rightNeighbor i = e
        · rw [h1] at hold
          exact absurd hold.1.1 (by rw [hpred]; decide)
        · by_cases h2 : ring.rightNeighbor i = ring.rightNeighbor e
          · rw [h2, ms_at_j ring C e hne]
            rw [h2] at hold
            constructor
            · unfold ReservedFrontHoldGuard at hold ⊢
              rw [ms_role_j, ms_pending_j]
              exact hold.1
            · rfl
          · rw [ms_at_other ring C e _ h1 h2]
            exact hold

end B9SpliceV10cRowMoveStop
