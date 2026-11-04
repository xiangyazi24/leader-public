import Leader.Wu.Splice.MoveCommitSafe
import Leader.Wu.Splice.CertifiedDeleteSafe

set_option autoImplicit false

/-! # MOVE-COMMIT preserves `SpliceSafeV7g`

MOVE-COMMIT clears a settled predecessor at `e` and relabels and settles the pending predecessor at
`j = rightNeighbor e` (`moveCommitAt`).  It consumes the fourth protected shape: the pending predecessor
at `j` stops being pending.  `moveCommitAt_preserves_spliceSafeV7g`: from a `SpliceSafeV7g` configuration
satisfying the MOVE-COMMIT guard, the result is `SpliceSafeV7g`, with or without leaders elsewhere.

Instance of `B9SpliceCertifiedDelete.local_preservation`: the served edge is aligned by the relabel, so it
is no danger; the outgoing edge is protected by the settled predecessor before the reserved front that
backed the pending predecessor; the incoming edge keeps its left cell, and its old protection cannot have
used `e` (a settled predecessor is neither a reserved front nor pending). -/

namespace B9SpliceMoveCommitSafeV7g

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence B9SpliceV10ePhysicalHoldNoBirth B9SpliceV10cRowMoveCommit
  B9SpliceTableV10g B9SpliceCertifiedDelete

variable {n psi kappa tau : Nat}

theorem moveCommitAt_preserves_spliceSafeV7g
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hG : MoveCommitGuard (C e).carrier (C (ring.rightNeighbor e)).carrier) :
    SpliceSafeV7g hpsi ring (moveCommitAt hpsi ring C e) := by
  have hpred : role (C e).carrier = .predecessorArmed := hG.1
  have hset : (C e).carrier.repairPending = false := hG.2.1
  have hjpred : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed := hG.2.2.1
  have hjpend : (C (ring.rightNeighbor e)).carrier.repairPending = true := hG.2.2.2.1
  have hfrontK := hS.2.2 (ring.rightNeighbor e) hjpred hjpend
  have hkne : ring.rightNeighbor (ring.rightNeighbor e) ≠ e := by
    intro hk
    rw [hk] at hfrontK
    exact absurd hfrontK.1.1 (by rw [hpred]; decide)
  have hknj : ring.rightNeighbor (ring.rightNeighbor e) ≠ ring.rightNeighbor e :=
    fun hk => hne (rightNeighbor_inj ring hk)
  have hDe : (moveCommitAt hpsi ring C e) e = clearControlV6 (C e) := mc_at_e hpsi ring C e
  have hDj := mc_at_j hpsi ring C e hne
  refine local_preservation hpsi ring C (moveCommitAt hpsi ring C e) e hne
    (fun i hie hij => mc_at_other hpsi ring C e i hie hij) hS ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- incoming edge
    intro x hr hd
    have hxj : x ≠ ring.rightNeighbor e := by
      intro h
      rw [h] at hr
      exact hkne hr
    have hx : x ≠ e := by
      intro h; rw [h] at hr; exact hne hr
    have hdp := (danger_iff_physical hpsi ring (moveCommitAt hpsi ring C e) x).1 hd
    have hd0 : PreparedDangerAt hpsi ring (projectV6 C) x := by
      refine (danger_iff_physical hpsi ring C x).2 ⟨?_, ?_, ?_⟩
      · have := hdp.1; rwa [mc_at_other hpsi ring C e x hx hxj] at this
      · have := hdp.2.1; rw [hr, hDe, mc_e_base] at this; rw [hr]; exact this
      · have := hdp.2.2; rw [hr, hDe, mc_e_base, mc_at_other hpsi ring C e x hx hxj] at this
        rw [hr]; exact this
    rcases hS.1 x hd0 with hv | hpoh
    · rcases hv with hv3 | hf
      · left; left
        unfold R1ProtectedSpliceEdgeV3 at hv3 ⊢
        simp only [projectV6] at hv3 ⊢
        rw [mc_at_other hpsi ring C e x hx hxj, hr, hDe]
        rw [hr] at hv3
        rcases hv3 with h1 | h2 | h3
        · exact Or.inl h1
        · exact absurd h2.2 (by rw [hset]; decide)
        · rcases h3.2.2 with h4 | h4 | h4
          · exact absurd h4.1 (by rw [hpred]; decide)
          · exact absurd h4.1 (by rw [hpred]; decide)
          · exact absurd h4.2 (by rw [hset]; decide)
      · left; right
        rw [mc_at_other hpsi ring C e x hx hxj]
        exact hf
    · have := hpoh.2.2.1.1
      rw [hr, hpred] at this
      exact absurd this (by decide)
  · -- served edge: aligned by the relabel, so no danger
    intro hd
    exfalso
    have hdp := (danger_iff_physical hpsi ring (moveCommitAt hpsi ring C e) e).1 hd
    apply hdp.2.2
    rw [hDj, hDe, mc_j_label, mc_e_base]
  · -- outgoing edge: settled predecessor before the backing reserved front
    intro _
    left; left
    unfold R1ProtectedSpliceEdgeV3
    simp only [projectV6]
    right; right
    refine ⟨?_, ?_, Or.inl ?_⟩
    · rw [hDj]; exact mc_j_role hpsi _ _
    · rw [hDj]; exact mc_j_pending hpsi _ _
    · rw [mc_at_other hpsi ring C e _ hkne hknj]
      exact hfrontK.1
  · -- ticket shape at e: cleared control
    rw [hDe]
    intro ht
    have h0 : (clearControlV6 (C e)).acquireTicket = false := rfl
    rw [h0] at ht
    exact absurd ht (by decide)
  · -- ticket shape at j: cleared
    rw [hDj]
    intro ht
    exact absurd ht (by rw [mc_j_ticket]; decide)
  · -- a pending predecessor entering e would need e to be a reserved front
    intro x hr _ hrole hpend
    have hb := hS.2.2 x hrole hpend
    rw [hr] at hb
    exact absurd hb.1.1 (by rw [hpred]; decide)
  · -- e is cleared
    intro hrole _
    rw [hDe] at hrole
    have h0 : role (clearControlV6 (C e)).carrier = .none := rfl
    rw [h0] at hrole
    exact absurd hrole (by decide)
  · -- j is settled
    intro _ hpend
    rw [hDj, mc_j_pending] at hpend
    exact absurd hpend (by decide)

end B9SpliceMoveCommitSafeV7g
