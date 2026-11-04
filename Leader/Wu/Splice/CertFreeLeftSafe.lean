import Leader.Wu.Splice.OrphanToFence
import Leader.Wu.Splice.PhysicalHoldNoBirthSafe
set_option autoImplicit false

/-! Clearing a certificate-free LEFT endpoint preserves SpliceSafeV7: covers the V6 rows
VictimLeftScrub, MalformedLeftPending and PredecessorLeftScrub. -/

namespace B9SpliceV10cRowCertFreeLeft
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence
variable {n psi kappa tau : Nat}

def CertFreeLeftV7 (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  ¬ ReservedFrontHoldGuard l.carrier ∧
  ¬ (role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true) ∧
  ¬ (role l.carrier = .victimArmed ∧ l.carrier.repairPending = true) ∧
  ¬ HostFenceShapeV7 l ∧
  ¬ (role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = false ∧
      (ReservedFrontHoldGuard r.carrier ∨
        (role r.carrier = .victimArmed ∧ r.carrier.repairPending = true) ∨
        (role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = true)))

def clearLeftAt (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau :=
  fun i => if i = e then clearControlV6 (C e) else C i

theorem cl_at_e (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    clearLeftAt ring C e e = clearControlV6 (C e) := by simp [clearLeftAt]

theorem cl_at_other (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n)
    (h : i ≠ e) : clearLeftAt ring C e i = C i := by simp [clearLeftAt, h]

theorem cl_base_eq (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e i : Fin n) :
    (clearLeftAt ring C e i).carrier.splice.base = (C i).carrier.splice.base := by
  unfold clearLeftAt
  split
  · rename_i h; subst h; rfl
  · rfl

theorem cl_dangerAt_iff (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e e' : Fin n) :
    PreparedDangerAt hpsi ring (projectV6 (clearLeftAt ring C e)) e' ↔
      PreparedDangerAt hpsi ring (projectV6 C) e' := by
  unfold PreparedDangerAt PreparedBarrierAt preparedR1 prepared projectSpliceConfig projectV6
  dsimp only
  rw [cl_base_eq, cl_base_eq]

theorem certFreeLeftClear_preserves_spliceSafeV7
    (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hS : SpliceSafeV7 hpsi ring C)
    (hF : CertFreeLeftV7 (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7 hpsi ring (clearLeftAt ring C e) := by
  obtain ⟨hnf, hnpp, hnv, hnfence, hnsettled⟩ := hF
  refine ⟨?_, ?_, ?_⟩
  · intro e' hd
    have hd0 := (cl_dangerAt_iff hpsi ring C e e').1 hd
    have hp := hS.1 e' hd0
    by_cases h1 : e' = e
    · -- the cleared cell is the left endpoint: it certified nothing there
      subst h1
      rcases hp with hv | hf
      · unfold R1ProtectedSpliceEdgeV3 at hv
        simp only [projectV6] at hv
        rcases hv with h1' | h2' | h3'
        · exact absurd h1' hnf
        · by_cases hself : ring.rightNeighbor e' = e'
          · rw [hself] at h2'
            exact absurd h2' hnpp
          · left
            unfold R1ProtectedSpliceEdgeV3
            simp only [projectV6]
            rw [cl_at_other ring C e' _ hself]
            exact Or.inr (Or.inl h2')
        · exact absurd ⟨h3'.1, h3'.2.1, h3'.2.2⟩ hnsettled
      · exact absurd hf hnfence
    · by_cases h2 : ring.rightNeighbor e' = e
      · -- the cleared cell is the right endpoint: it certified nothing there either
        rcases hp with hv | hf
        · left
          unfold R1ProtectedSpliceEdgeV3 at hv ⊢
          simp only [projectV6] at hv ⊢
          rw [cl_at_other ring C e e' h1, h2, cl_at_e]
          rw [h2] at hv
          rcases hv with h1' | h2' | h3'
          · exact Or.inl h1'
          · exact absurd h2' hnpp
          · rcases h3'.2.2 with h4 | h4 | h4
            · exact absurd h4 hnf
            · exact absurd h4 hnv
            · exact absurd h4 hnpp
        · right
          rw [cl_at_other ring C e e' h1]
          exact hf
      · unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 at hp ⊢
        simp only [projectV6] at hp ⊢
        rw [cl_at_other ring C e e' h1, cl_at_other ring C e _ h2]
        exact hp
  · intro i
    by_cases h1 : i = e
    · rw [h1, cl_at_e]
      intro ht
      rw [clearControl_ticket] at ht
      exact absurd ht (by decide)
    · rw [cl_at_other ring C e i h1]
      exact hS.2.1 i
  · intro i hr hp
    by_cases h1 : i = e
    · rw [h1, cl_at_e, clearControl_role] at hr
      exact absurd hr (by decide)
    · rw [cl_at_other ring C e i h1] at hr hp
      have hold := hS.2.2 i hr hp
      by_cases h2 : ring.rightNeighbor i = e
      · rw [h2] at hold
        exact absurd hold.1 hnf
      · rw [cl_at_other ring C e _ h2]
        exact hold

/-- The three left scrub rows are instances. -/
theorem victimLeftScrub_certFree (l r : R1AgentStateV6 psi kappa tau)
    (h : VictimLeftScrubGuardV6 l) : CertFreeLeftV7 l r := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hf; exact absurd hf.1 (by rw [h.1]; decide)
  · intro hp; exact absurd hp.1 (by rw [h.1]; decide)
  · intro hv; exact absurd hv.2 (by rw [h.2]; decide)
  · intro hf; exact absurd hf.1 (by rw [h.1]; decide)
  · intro hs; exact absurd hs.1 (by rw [h.1]; decide)

theorem malformedLeft_certFree (l r : R1AgentStateV6 psi kappa tau)
    (h : MalformedLeftPendingGuardV6 l) : CertFreeLeftV7 l r := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hf; exact h.2.2.1 hf.1
  · intro hp; exact h.2.1 hp.1
  · intro hv; exact h.2.2.2 hv.1
  · intro hf; exact absurd hf.2.1 (by rw [h.1]; decide)
  · intro hs; exact h.2.1 hs.1

theorem predecessorLeftScrub_certFree (l r : R1AgentStateV6 psi kappa tau)
    (h1 : role l.carrier = .predecessorArmed) (h2 : l.carrier.repairPending = false)
    (h3 : ¬ ReservedFrontHoldGuard r.carrier)
    (h4 : ¬ (role r.carrier = .victimArmed ∧ r.carrier.repairPending = true))
    (h5 : ¬ (role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = true)) :
    CertFreeLeftV7 l r := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hf; exact absurd hf.1 (by rw [h1]; decide)
  · intro hp; exact absurd hp.2 (by rw [h2]; decide)
  · intro hv; exact absurd hv.1 (by rw [h1]; decide)
  · intro hf; exact absurd hf.1 (by rw [h1]; decide)
  · intro hs
    rcases hs.2.2 with h | h | h
    · exact h3 h
    · exact h4 h
    · exact h5 h

/-- For a role-none cell, clearing the pending bit is clearing the control. -/
theorem clearPending_eq_clearControl (u : R1AgentStateV6 psi kappa tau)
    (h : role u.carrier = .none) : clearPendingV6 u = clearControlV6 u := by
  unfold clearPendingV6 clearControlV6 setControlV6 withCarrierClearTicketV6 setControl
  unfold role at h
  cases hu : u.carrier with
  | mk sp pend =>
      cases hs : sp with
      | mk base r =>
          simp only [hu, hs] at h ⊢
          subst h
          rfl

end B9SpliceV10cRowCertFreeLeft
