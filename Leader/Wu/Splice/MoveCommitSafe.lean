import Leader.Wu.Splice.OrphanToFence
import Leader.Wu.Splice.PhysicalHoldNoBirthSafe
set_option autoImplicit false

/-! Row MOVE-COMMIT: the settled predecessor is cleared and the pending predecessor on its right
is relabelled (repairResponder) and settled. -/

namespace B9SpliceV10cRowMoveCommit
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence B9SpliceV10ePhysicalHoldNoBirth
variable {n psi kappa tau : Nat}

def moveCommitAt (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  let q := moveCommitWriteV6 hpsi (C e) (C (ring.rightNeighbor e))
  fun i => if i = e then q.1 else if i = ring.rightNeighbor e then q.2 else C i

theorem mc_at_e (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    moveCommitAt hpsi ring C e e = clearControlV6 (C e) := by
  simp [moveCommitAt, moveCommitWriteV6]

theorem mc_at_j (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    moveCommitAt hpsi ring C e (ring.rightNeighbor e) =
      withCarrierClearTicketV6 (C (ring.rightNeighbor e))
        (setControl (repairResponder hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier)
          .predecessorArmed false) := by
  simp [moveCommitAt, moveCommitWriteV6, hne]

theorem mc_at_other (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (h1 : i ≠ e) (h2 : i ≠ ring.rightNeighbor e) : moveCommitAt hpsi ring C e i = C i := by
  simp [moveCommitAt, h1, h2]

/-- Field facts about the committed responder. -/
theorem mc_j_role (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    role (withCarrierClearTicketV6 r (setControl (repairResponder hpsi l.carrier r.carrier)
      .predecessorArmed false)).carrier = .predecessorArmed := rfl
theorem mc_j_pending (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    (withCarrierClearTicketV6 r (setControl (repairResponder hpsi l.carrier r.carrier)
      .predecessorArmed false)).carrier.repairPending = false := rfl
theorem mc_j_ticket (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    (withCarrierClearTicketV6 r (setControl (repairResponder hpsi l.carrier r.carrier)
      .predecessorArmed false)).acquireTicket = false := rfl
theorem mc_j_label (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    (withCarrierClearTicketV6 r (setControl (repairResponder hpsi l.carrier r.carrier)
      .predecessorArmed false)).carrier.splice.base.core.core.label =
      ⟨(l.carrier.splice.base.core.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := rfl
theorem mc_j_leader (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) :
    (withCarrierClearTicketV6 r (setControl (repairResponder hpsi l.carrier r.carrier)
      .predecessorArmed false)).carrier.splice.base.core.core.leader =
      r.carrier.splice.base.core.core.leader := rfl
theorem mc_e_base (u : R1AgentStateV6 psi kappa tau) :
    (clearControlV6 u).carrier.splice.base = u.carrier.splice.base := rfl

theorem moveCommit_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7 hpsi ring C)
    (hG : MoveCommitGuard (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7 hpsi ring (moveCommitAt hpsi ring C e) := by
  have hpred : role (C e).carrier = .predecessorArmed := hG.1
  have hset : (C e).carrier.repairPending = false := hG.2.1
  have hjpred : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed := hG.2.2.1
  have hjpend : (C (ring.rightNeighbor e)).carrier.repairPending = true := hG.2.2.2.1
  -- the pending predecessor's reserved front
  have hfrontK := hS.2.2 (ring.rightNeighbor e) hjpred hjpend
  have hkne : ring.rightNeighbor (ring.rightNeighbor e) ≠ e := by
    intro hk
    rw [hk] at hfrontK
    exact absurd hfrontK.1.1 (by rw [hpred]; decide)
  have hknj : ring.rightNeighbor (ring.rightNeighbor e) ≠ ring.rightNeighbor e := by
    intro hk
    exact hne (rightNeighbor_inj ring hk)
  have hDe : (moveCommitAt hpsi ring C e) e = clearControlV6 (C e) := mc_at_e hpsi ring C e
  have hDj := mc_at_j hpsi ring C e hne
  refine ⟨?_, ?_, ?_⟩
  · intro x hd
    have hdp := (danger_iff_physical hpsi ring (moveCommitAt hpsi ring C e) x).1 hd
    by_cases hx : x = e
    · -- served edge aligned by the commit relabel
      subst hx
      exfalso
      apply hdp.2.2
      rw [hDj, hDe, mc_j_label, mc_e_base]
    · by_cases hxj : x = ring.rightNeighbor e
      · -- outgoing edge of the committed responder: settled predecessor with its reserved front
        subst hxj
        left
        unfold R1ProtectedSpliceEdgeV3
        simp only [projectV6]
        right; right
        refine ⟨?_, ?_, Or.inl ?_⟩
        · rw [hDj]; exact mc_j_role hpsi _ _
        · rw [hDj]; exact mc_j_pending hpsi _ _
        · rw [mc_at_other hpsi ring C e _ hkne hknj]
          exact hfrontK.1
      · by_cases hr : ring.rightNeighbor x = e
        · -- edge into the cleared predecessor: same danger as before, protected from x
          have hd0 : PreparedDangerAt hpsi ring (projectV6 C) x := by
            refine (danger_iff_physical hpsi ring C x).2 ⟨?_, ?_, ?_⟩
            · have := hdp.1; rwa [mc_at_other hpsi ring C e x hx hxj] at this
            · have := hdp.2.1; rw [hr, hDe, mc_e_base] at this; rw [hr]; exact this
            · have := hdp.2.2; rw [hr, hDe, mc_e_base, mc_at_other hpsi ring C e x hx hxj] at this
              rw [hr]; exact this
          have hp := hS.1 x hd0
          rcases hp with hv | hf
          · left
            unfold R1ProtectedSpliceEdgeV3 at hv ⊢
            simp only [projectV6] at hv ⊢
            rw [mc_at_other hpsi ring C e x hx hxj, hr, hDe]
            rw [hr] at hv
            rcases hv with h1 | h2 | h3
            · exact Or.inl h1
            · exact absurd h2.2 (by rw [hset]; decide)
            · rcases h3.2.2 with h4 | h4 | h4
              · exact absurd h4.1 (by rw [hpred]; decide)
              · exact absurd h4.1 (by rw [hpred]; decide)
              · exact absurd h4.2 (by rw [hset]; decide)
          · right
            rw [mc_at_other hpsi ring C e x hx hxj]
            exact hf
        · by_cases hrj : ring.rightNeighbor x = ring.rightNeighbor e
          · exact absurd (rightNeighbor_inj ring hrj) hx
          · have hd0 : PreparedDangerAt hpsi ring (projectV6 C) x := by
              have h1 := mc_at_other hpsi ring C e x hx hxj
              have h2 := mc_at_other hpsi ring C e _ hr hrj
              unfold PreparedDangerAt PreparedBarrierAt projectV6 projectSpliceConfig at hd ⊢
              dsimp only at hd ⊢
              rw [h1, h2] at hd
              exact hd
            have hp := hS.1 x hd0
            unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 at hp ⊢
            simp only [projectV6] at hp ⊢
            rw [mc_at_other hpsi ring C e x hx hxj, mc_at_other hpsi ring C e _ hr hrj]
            exact hp
  · intro i
    by_cases hi : i = e
    · rw [hi, hDe]
      intro ht
      rw [clearControl_ticket] at ht
      exact absurd ht (by decide)
    · by_cases hj : i = ring.rightNeighbor e
      · rw [hj, hDj]
        intro ht
        rw [mc_j_ticket] at ht
        exact absurd ht (by decide)
      · rw [mc_at_other hpsi ring C e i hi hj]
        exact hS.2.1 i
  · intro i hr hp
    by_cases hi : i = e
    · rw [hi, hDe, clearControl_role] at hr
      exact absurd hr (by decide)
    · by_cases hj : i = ring.rightNeighbor e
      · rw [hj, hDj, mc_j_pending] at hp
        exact absurd hp (by decide)
      · rw [mc_at_other hpsi ring C e i hi hj] at hr hp
        have hold := hS.2.2 i hr hp
        by_cases h1 : ring.rightNeighbor i = e
        · rw [h1] at hold
          exact absurd hold.1.1 (by rw [hpred]; decide)
        · by_cases h2 : ring.rightNeighbor i = ring.rightNeighbor e
          · rw [h2] at hold
            exact absurd hold.1.1 (by rw [hjpred]; decide)
          · rw [mc_at_other hpsi ring C e _ h1 h2]
            exact hold

end B9SpliceV10cRowMoveCommit
