import Leader.Wu.Splice.PhysicalHoldNoBirthSafe
import Leader.Wu.Splice.PhysicalHoldDeletionSafe
import Leader.Wu.Splice.PhysicalHoldBirthSafe

set_option autoImplicit false
set_option Elab.async false

/-! # Fencing a settled predecessor, and the physical-then-fence identity

Fencing a settled predecessor is safe on every configuration, and the V10e writer
"physical step, then fence the relabelled settled predecessor" equals the physical hold of the
configuration in which the predecessor was fenced first. -/

namespace B9SpliceV10eFenceIdentity

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceV8LabelFrame B9OrphanToFence
  B9SpliceTableV10d B9SpliceTableV10e B9SpliceV10ePhysicalHoldNoBirth
  B9SpliceV10ePhysicalHoldDeletion B9SpliceV10ePhysicalHoldBirth

variable {n psi width kappa tau : Nat}

/-! ## A. Fencing a settled predecessor is safe on every configuration -/

theorem settledPredFence_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hS : SpliceSafeV7 hpsi ring C)
    (hpred : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed)
    (hset : (C (ring.rightNeighbor e)).carrier.repairPending = false) :
    SpliceSafeV7 hpsi ring (orphanToFenceAt ring C e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e' hd
    by_cases h1 : e' = ring.rightNeighbor e
    · right
      rw [h1, at_j]
      exact fence_shape _
    · have hd0 := (dangerAt_iff hpsi ring C e e').1 hd
      have hp := hS.1 e' hd0
      by_cases h2 : ring.rightNeighbor e' = ring.rightNeighbor e
      · have hee : e' = e := rightNeighbor_inj ring h2
        subst hee
        rcases hp with hv | hf
        · left
          unfold R1ProtectedSpliceEdgeV3 at hv ⊢
          simp only [projectV6] at hv ⊢
          rw [at_other ring C e' e' h1, at_j]
          rcases hv with h1' | h2' | h3'
          · exact Or.inl h1'
          · exact absurd h2'.2 (by rw [hset]; decide)
          · rcases h3'.2.2 with h4 | h4 | h4
            · exact absurd h4.1 (by rw [hpred]; decide)
            · exact absurd h4.1 (by rw [hpred]; decide)
            · exact absurd h4.2 (by rw [hset]; decide)
        · right
          rw [at_other ring C e' e' h1]
          exact hf
      · unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 at hp ⊢
        simp only [projectV6] at hp ⊢
        rw [at_other ring C e e' h1, at_other ring C e _ h2]
        exact hp
  · intro i
    by_cases h1 : i = ring.rightNeighbor e
    · rw [h1, at_j]
      intro _
      exact Or.inr (fence_shape _)
    · rw [at_other ring C e i h1]
      exact hS.2.1 i
  · intro i hr hp
    by_cases h1 : i = ring.rightNeighbor e
    · rw [h1, at_j] at hr
      have hnone : role (fenceV6 (C (ring.rightNeighbor e))).carrier = .none := rfl
      rw [hnone] at hr
      exact absurd hr (by decide)
    · rw [at_other ring C e i h1] at hr hp
      by_cases h2 : ring.rightNeighbor i = ring.rightNeighbor e
      · have hb := hS.2.2 i hr hp
        rw [h2] at hb
        exact absurd hb.1.1 (by rw [hpred]; decide)
      · rw [at_other ring C e _ h2]
        exact hS.2.2 i hr hp

/-! ## B. The physical-then-fence writer is the physical hold of the fenced configuration -/

private theorem v6_ext {u v : R1AgentStateV6 psi kappa tau}
    (h1 : u.carrier = v.carrier) (h2 : u.acquireTicket = v.acquireTicket) : u = v := by
  cases u; cases v
  simp only at h1 h2
  subst h1; subst h2; rfl

theorem physicalFenceAt_eq_hold_of_fence
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) :
    physicalFenceAt hpsi hwidth hle ring C e =
      physicalHoldAt hpsi hwidth hle ring (orphanToFenceAt ring C e) e := by
  funext i
  have hCe : orphanToFenceAt ring C e e = C e := at_other ring C e e (Ne.symm hself)
  have hCj : orphanToFenceAt ring C e (ring.rightNeighbor e) = fenceV6 (C (ring.rightNeighbor e)) :=
    at_j ring C e
  by_cases hi : i = e
  · subst hi
    simp only [physicalFenceAt, physicalHoldAt, if_pos rfl]
    rw [hCe, hCj]
    apply v6_ext
    · rw [physicalHold_left_carrier, physicalHold_left_carrier]
      unfold ordinaryRow
      rw [fence_base]
    · rw [physicalHold_left_ticket, physicalHold_left_ticket]
  · by_cases hj : i = ring.rightNeighbor e
    · subst hj
      simp only [physicalFenceAt, physicalHoldAt, if_neg hself, if_pos rfl, if_true]
      rw [hCe, hCj]
      apply v6_ext
      · have hfc : ∀ u : R1AgentStateV6 psi kappa tau,
            (fenceV6 u).carrier = setControl u.carrier .none false := fun _ => rfl
        rw [hfc, physicalHold_right_carrier, physicalHold_right_carrier]
        unfold ordinaryRow
        rw [fence_base]
        dsimp only
        simp only [setControl, setPhysical, fenceV6, setTicketV6, setControlV6, withCarrierClearTicketV6]
      · rw [physicalHold_right_ticket]
        by_cases hc : rightFollowerRelabelledV7 (fenceV6 (C (ring.rightNeighbor e))).carrier
            (ordinaryRow hpsi hwidth hle (C e).carrier (fenceV6 (C (ring.rightNeighbor e))).carrier).2 = true
        · rw [if_pos hc]; rfl
        · rw [if_neg hc]; rfl
    · simp only [physicalFenceAt, physicalHoldAt, if_neg hi, if_neg hj]
      exact (at_other ring C e i hj).symm

end B9SpliceV10eFenceIdentity
