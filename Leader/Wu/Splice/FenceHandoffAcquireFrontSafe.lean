import Leader.Wu.Splice.FenceHandoffWholeRow

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV10bMoveAcquireFront

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2 B9SpliceControllerR1TableV3
open B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
open B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b B9SpliceV10bWholeRow
variable {n psi width kappa tau : Nat}

private def acquireOut (C : R1ConfigV6 n psi kappa tau) (e : Fin n) : R1ConfigV6 n psi kappa tau :=
  fun i => if i = e then setControlV6 (C e) .predecessorArmed true else C i

private theorem selected_nonself (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (h : MoveAcquireFrontSelectedV10b hpsi (C e) (C (ring.rightNeighbor e))) : ring.rightNeighbor e ≠ e := by
  have hg := h.2.2.2.2.2
  intro he
  have hr := hg.2.2.2.2.2.1
  rw [he] at hr
  have hb : (true : Bool) = false := hg.2.2.1.symm.trans hr
  cases hb

private theorem step_eq_acquireOut (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (h : MoveAcquireFrontSelectedV10b hpsi (C e) (C (ring.rightNeighbor e))) :
    stepV10b hpsi hwidth hle ring C e = acquireOut C e := by
  have hn := selected_nonself hpsi ring C e h
  rcases h with ⟨ha, hb, hs, hl, hr, hg⟩
  have hw : rowV10b hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
      moveAcquireFrontWriteV6 (C e) (C (ring.rightNeighbor e)) := by
    simp [rowV10b, ha, rowV9, hb, rowV8, hs, rowV7, hl, hr, hg]
  funext i
  by_cases hi : i = e
  · subst i; simp [stepV10b, hn, hw, acquireOut, moveAcquireFrontWriteV6]
  · by_cases hj : i = ring.rightNeighbor e
    · subst i; simp [stepV10b, hn, hw, acquireOut, moveAcquireFrontWriteV6]
    · simp [stepV10b, hn, hw, acquireOut, moveAcquireFrontWriteV6, hi, hj]

private theorem danger_before_of_after_ne (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e x : Fin n) (hx : x ≠ e)
    (hd : PreparedDangerAt hpsi ring (projectV6 (acquireOut C e)) x) : PreparedDangerAt hpsi ring (projectV6 C) x := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6 projectSpliceConfig at hd ⊢
  dsimp only at hd ⊢
  unfold preparedR1 prepared at hd ⊢
  simp only [acquireOut] at hd
  by_cases hr : ring.rightNeighbor x = e
  · simpa [hx, hr, setControlV6, withCarrierClearTicketV6, setControl] using hd
  · simpa [hx, hr] using hd

private theorem danger_left_implies_local (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hn : ring.rightNeighbor e ≠ e)
    (hd : PreparedDangerAt hpsi ring (projectV6 (acquireOut C e)) e) :
    LocalPreparedBarrier hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier := by
  have hb : LocalPreparedBarrier hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier := by
    simpa [PreparedBarrierAt, LocalPreparedBarrier, projectSpliceConfig, projectV6, preparedR1,
      prepared, acquireOut, hn, setControlV6, withCarrierClearTicketV6, setControl] using hd.2
  exact hb

private theorem protected_frame (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e x : Fin n)
    (hx : x ≠ e) (hr : ring.rightNeighbor x ≠ e) (hp : ProtectedSpliceEdgeV7 ring C x) :
    ProtectedSpliceEdgeV7 ring (acquireOut C e) x := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 projectV6 at hp ⊢
  dsimp only at hp ⊢
  simpa [acquireOut, hx, hr] using hp

theorem moveAcquireFront_preserves_dangerCoverageV10b (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hs : SpliceSafeV7 hpsi ring C)
    (h : MoveAcquireFrontSelectedV10b hpsi (C e) (C (ring.rightNeighbor e))) :
    ∀ x, PreparedDangerAt hpsi ring (projectV6 (stepV10b hpsi hwidth hle ring C e)) x →
      ProtectedSpliceEdgeV7 ring (stepV10b hpsi hwidth hle ring C e) x := by
  rw [step_eq_acquireOut hpsi hwidth hle ring C e h]
  have hn := selected_nonself hpsi ring C e h
  have hg := h.2.2.2.2.2
  intro x hd
  by_cases hx : x = e
  · subst x
    exact (hg.2.2.2.2.2.2 (danger_left_implies_local hpsi ring C e hn hd)).elim
  · have hd0 := danger_before_of_after_ne hpsi ring C e x hx hd
    by_cases hr : ring.rightNeighbor x = e
    · unfold ProtectedSpliceEdgeV7
      left
      unfold R1ProtectedSpliceEdgeV3 projectV6
      dsimp only
      right; left
      simp [acquireOut, hx, hr, setControlV6, withCarrierClearTicketV6, setControl, role]
    · exact protected_frame ring C e x hx hr (hs.1 x hd0)

theorem moveAcquireFront_preserves_ticketShapeV10b (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hs : SpliceSafeV7 hpsi ring C)
    (h : MoveAcquireFrontSelectedV10b hpsi (C e) (C (ring.rightNeighbor e))) :
    ∀ i, TicketShapeV7 (stepV10b hpsi hwidth hle ring C e i) := by
  rw [step_eq_acquireOut hpsi hwidth hle ring C e h]
  intro i
  by_cases hi : i = e
  · subst i; simp [acquireOut, TicketShapeV7, setControlV6, withCarrierClearTicketV6]
  · simpa [acquireOut, hi] using hs.2.1 i

theorem moveAcquireFront_preserves_backingV10b (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hs : SpliceSafeV7 hpsi ring C)
    (h : MoveAcquireFrontSelectedV10b hpsi (C e) (C (ring.rightNeighbor e))) :
    ∀ i, role (stepV10b hpsi hwidth hle ring C e i).carrier = .predecessorArmed →
      (stepV10b hpsi hwidth hle ring C e i).carrier.repairPending = true →
      ReservedFrontHoldGuard (stepV10b hpsi hwidth hle ring C e (ring.rightNeighbor i)).carrier ∧
        (stepV10b hpsi hwidth hle ring C e (ring.rightNeighbor i)).acquireTicket = false := by
  rw [step_eq_acquireOut hpsi hwidth hle ring C e h]
  have hn := selected_nonself hpsi ring C e h
  have hg := h.2.2.2.2.2
  intro i hr hp
  by_cases hi : i = e
  · subst i
    have he := moveAcquireFront_preserves_edgeProvenanceV6 hpsi (C e) (C (ring.rightNeighbor e)) hg
    have hrole : role (moveAcquireFrontWriteV6 (C e) (C (ring.rightNeighbor e))).1.carrier = .predecessorArmed := by rfl
    have hpending : (moveAcquireFrontWriteV6 (C e) (C (ring.rightNeighbor e))).1.carrier.repairPending = true := by rfl
    have hb : ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier ∧
        (C (ring.rightNeighbor e)).acquireTicket = false := by
      simpa only [moveAcquireFrontWriteV6] using he.2.2 hrole hpending
    simpa only [acquireOut, if_neg hn] using hb
  · have hr0 : role (C i).carrier = .predecessorArmed := by simpa [acquireOut, hi] using hr
    have hp0 : (C i).carrier.repairPending = true := by simpa [acquireOut, hi] using hp
    have hb := hs.2.2 i hr0 hp0
    by_cases hre : ring.rightNeighbor i = e
    · rw [hre] at hb
      have hbad : (true : Bool) = false := hg.2.2.1.symm.trans hb.2
      cases hbad
    · simpa [acquireOut, hre] using hb

theorem moveAcquireFrontBranch_v10b (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : MoveAcquireFrontBranchStatementV10b (kappa := kappa) (tau := tau) hpsi hwidth hle ring := by
  intro C e hs h
  unfold SpliceSafeV7 ProvenanceSafeV7
  constructor
  · exact moveAcquireFront_preserves_dangerCoverageV10b (kappa := kappa) (tau := tau) hpsi hwidth hle ring C e hs h
  constructor
  · exact moveAcquireFront_preserves_ticketShapeV10b (kappa := kappa) (tau := tau) hpsi hwidth hle ring C e hs h
  · exact moveAcquireFront_preserves_backingV10b (kappa := kappa) (tau := tau) hpsi hwidth hle ring C e hs h

end B9SpliceV10bMoveAcquireFront

#print axioms B9SpliceV10bMoveAcquireFront.moveAcquireFrontBranch_v10b
