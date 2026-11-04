import Leader.Wu.Splice.OrphanToFence
set_option autoImplicit false

/-! A pending predecessor whose left neighbour is a reserved front can be cleared: it certifies
only its incoming edge, which the reserved front certifies as well. -/

namespace B9SpliceFrontPendingPredClear
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence
variable {n psi kappa tau : Nat}

def FrontOwnedPendingPredGuard (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  ReservedFrontHoldGuard l.carrier ∧ role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = true

theorem frontOwnedPendingPredClear_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hS : SpliceSafeV7 hpsi ring C)
    (hG : FrontOwnedPendingPredGuard (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7 hpsi ring (orphanVictimClearAt ring C e) := by
  obtain ⟨hfront, hpred, hpend⟩ := hG
  refine ⟨?_, ?_, ?_⟩
  · intro e' hd
    have hd0 := (vc_dangerAt_iff hpsi ring C e e').1 hd
    have hp := hS.1 e' hd0
    by_cases h1 : e' = ring.rightNeighbor e
    · -- outgoing edge of the cleared predecessor: it certified nothing there
      subst h1
      rcases hp with hv | hf
      · unfold R1ProtectedSpliceEdgeV3 at hv
        simp only [projectV6] at hv
        rcases hv with h1' | h2' | h3'
        · exact absurd h1'.1 (by rw [hpred]; decide)
        · left
          unfold R1ProtectedSpliceEdgeV3
          simp only [projectV6]
          rw [vc_at_j]
          by_cases hself : ring.rightNeighbor (ring.rightNeighbor e) = ring.rightNeighbor e
          · rw [hself] at h2'
            rw [hself, vc_at_j]
            -- the cleared cell is its own successor: contradiction with the ring (it would be e)
            exfalso
            have := rightNeighbor_inj ring hself
            rw [this] at hpred
            exact absurd hfront.1 (by rw [hpred]; decide)
          · rw [vc_at_other ring C e _ hself]
            exact Or.inr (Or.inl h2')
        · exact absurd h3'.2.1 (by rw [hpend]; decide)
      · exact absurd hf.1 (by rw [hpred]; decide)
    · by_cases h2 : ring.rightNeighbor e' = ring.rightNeighbor e
      · -- the served edge: the reserved front certifies it
        have hee : e' = e := rightNeighbor_inj ring h2
        subst hee
        left
        unfold R1ProtectedSpliceEdgeV3
        simp only [projectV6]
        left
        rw [vc_at_other ring C e' e' h1]
        exact hfront
      · unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 at hp ⊢
        simp only [projectV6] at hp ⊢
        rw [vc_at_other ring C e e' h1, vc_at_other ring C e _ h2]
        exact hp
  · intro i
    by_cases h1 : i = ring.rightNeighbor e
    · rw [h1, vc_at_j]
      intro ht
      rw [clearControl_ticket] at ht
      exact absurd ht (by decide)
    · rw [vc_at_other ring C e i h1]
      exact hS.2.1 i
  · intro i hr hp
    by_cases h1 : i = ring.rightNeighbor e
    · rw [h1, vc_at_j, clearControl_role] at hr
      exact absurd hr (by decide)
    · rw [vc_at_other ring C e i h1] at hr hp
      by_cases h2 : ring.rightNeighbor i = ring.rightNeighbor e
      · have hb := hS.2.2 i hr hp
        rw [h2] at hb
        exact absurd hb.1.1 (by rw [hpred]; decide)
      · rw [vc_at_other ring C e _ h2]
        exact hS.2.2 i hr hp

end B9SpliceFrontPendingPredClear
