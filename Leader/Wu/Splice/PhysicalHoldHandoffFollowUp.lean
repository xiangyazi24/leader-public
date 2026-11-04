import Leader.Wu.Splice.PhysicalHoldProgressStatement
import Leader.Wu.Splice.ZeroRefreshChain

set_option autoImplicit false
set_option Elab.async false

/-! # After a handoff the same edge reaches a physical service within two more services

On a fence-left edge with a prepared barrier and a clear target the V10e service is the V10b
handoff (fence, clear) -> (settled predecessor, reserved front); the next service is MOVE-SEEK
(the front receives the ticket); the third service stutters on every controller row and is
therefore the physical hold. -/

namespace B9SpliceV10eHandoffFollowUp

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10d B9SpliceTableV10e
  B9SpliceV10eTransparency B9SpliceV10cChainShapes B9SpliceV10cLeaderlessExclusion
  B9SpliceV10ePhysicalHoldNoBirth B9SpliceV10eGlobalProgress

variable {n psi width kappa tau : Nat}

/-! ## Row facts at the V10b level -/

theorem rowV10b_of_handoff (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) (hG : HostFenceAdvanceGuardV10b hpsi l r) :
    rowV10b hpsi hwidth hle l r = hostFenceHandoffWriteV10b l r := by
  simp [rowV10b, hG]

/-- The ordinary host keeps the role of the left endpoint. -/
theorem ordinaryHost_left_role (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    role (ordinaryHostWriteV7 hpsi hwidth hle l r).1.carrier = role l.carrier := by
  rw [← (physicalHold_carriers_eq_ordinaryHost hpsi hwidth hle l r).1]
  exact (physicalHold_role_frame hpsi hwidth hle l r).1

/-- The ordinary host does not ticket a right endpoint that carries a role. -/
theorem ordinaryHost_right_ticket_of_role (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) (hr : role r.carrier ≠ .none) :
    (ordinaryHostWriteV7 hpsi hwidth hle l r).2.acquireTicket = false := by
  unfold ordinaryHostWriteV7
  dsimp only
  split
  · rename_i hrel
    exfalso
    apply hr
    have h := of_decide_eq_true hrel
    have hrole : role (ordinaryRow hpsi hwidth hle l.carrier r.carrier).2 = role r.carrier := by
      simp [ordinaryRow, setPhysical, role]
    exact hrole.symm.trans h.1
  · rfl

theorem notZeroRefresh_of_left_role (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (h : role (rowV10b hpsi hwidth hle l r).1.carrier ≠ role l.carrier) :
    ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r := by
  intro hz
  apply h
  have h1 := hz.1
  rw [h1]
  exact ordinaryHost_left_role hpsi hwidth hle l r

theorem notZeroRefresh_of_right_ticket (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) (hr : role r.carrier ≠ .none)
    (h : (rowV10b hpsi hwidth hle l r).2.acquireTicket = true) :
    ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r := by
  intro hz
  have h1 := hz.1
  rw [h1, ordinaryHost_right_ticket_of_role hpsi hwidth hle l r hr] at h
  cases h

/-- rowV10d falls through to rowV10c when none of the four garbage guards holds. -/
theorem rowV10d_of_none (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (h1 : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier) (h2 : ¬ OrphanVictimGuard l r)
    (h3 : ¬ OwnedPendingVictimGuard l r) (h4 : ¬ OwnerlessPendingPredGuard l r) :
    rowV10d hpsi hwidth hle l r = rowV10c hpsi hwidth hle l r := by
  simp only [rowV10d, h1, h2, h3, h4, if_false]

theorem rowV10c_of_notZero (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) (hz : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r) :
    rowV10c hpsi hwidth hle l r = rowV10b hpsi hwidth hle l r := by
  simp only [rowV10c, hz, if_false]

/-- MOVE-SEEK is selected on (settled predecessor, reserved front) with a barrier, no tickets on
the left, leaderless bases. -/
theorem rowV10b_of_moveSeek (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hl : role l.carrier = .predecessorArmed) (hlp : l.carrier.repairPending = false)
    (hlt : l.acquireTicket = false)
    (hr : ReservedFrontHoldGuard r.carrier)
    (hbar : LocalPreparedBarrier hpsi l.carrier r.carrier)
    (hlead : l.carrier.splice.base.core.core.leader = false)
    (hrlead : r.carrier.splice.base.core.core.leader = false) :
    rowV10b hpsi hwidth hle l r = moveSeekWriteV6 l r := by
  have hfL : ¬ HostFenceShapeV7 l := fun h => by have := h.1; rw [hl] at this; cases this
  have hfR : ¬ HostFenceShapeV7 r := fun h => by have := h.1; rw [hr.1] at this; cases this
  have hh : ¬ HostFenceAdvanceGuardV10b hpsi l r := fun h => hfL h.1
  have hb : ¬ HostFenceBusyFrontGuardV9 hpsi l r := fun h => hfL h.1
  have hst : ¬ RightStalePredecessorHoldGuardV8 l r := fun h => by
    have := h.2.2.2.1; rw [hr.1] at this; cases this
  have hmaf : ¬ MoveAcquireFrontGuardV6 hpsi l r := fun h => by have := h.1.1; rw [hl] at this; cases this
  have harmA := armA_needs_leader hpsi hwidth hle l.carrier r.carrier hlead
  have harmB := armB_needs_leader l.carrier r.carrier hrlead
  have hdel := delete_needs_leader hpsi hwidth hle l.carrier r.carrier hlead
  have hph := pendingHold_needs_leader hpsi hwidth hle l.carrier r.carrier hlead
  have hpa := pendingAbort_needs_leader hpsi hwidth hle l.carrier r.carrier hlead
  have hmc : ¬ MoveCommitGuard l.carrier r.carrier := fun h => by
    have := h.2.2.1; rw [hr.1] at this; cases this
  have hms : ¬ MoveStopGuardV3 hpsi l.carrier r.carrier := fun h => h.2.2.2 hbar
  have hsk : MoveSeekGuardV3 hpsi l.carrier r.carrier := ⟨hl, hlp, hr, hbar⟩
  unfold rowV10b rowV9 rowV8 rowV7
  rw [if_neg hh, if_neg hb, if_neg hst, if_neg hfL, if_neg hfR, if_neg hmaf, if_neg harmA,
    if_neg harmB, if_neg hdel, if_neg hph, if_neg hpa, if_neg hmc, if_neg hms, if_pos hsk]

/-! ## Physical facts preserved by control writes -/

theorem barrier_of_control (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau)
    (a b : SpliceRole) (p q : Bool) (hbar : LocalPreparedBarrier hpsi l.carrier r.carrier) :
    LocalPreparedBarrier hpsi (setControlV6 l a p).carrier (setControlV6 r b q).carrier := hbar

theorem barrier_of_ticket (hpsi : 0 < psi) (l r : R1AgentStateV6 psi kappa tau) (b : Bool)
    (hbar : LocalPreparedBarrier hpsi l.carrier r.carrier) :
    LocalPreparedBarrier hpsi l.carrier (setTicketV6 r b).carrier := hbar

/-! ## The follow-up -/

theorem handoff_then_seek_then_physical
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hl : (C e).carrier.splice.base.core.core.leader = false)
    (hr : (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = false)
    (hG : HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e))) :
    PhysicalServiceAt hpsi hwidth hle ring
      (serveIter hpsi hwidth hle ring e 2 C) (serveIter hpsi hwidth hle ring e 3 C) e := by
  -- first service: the handoff
  have hfence : HostFenceShapeV7 (C e) := hG.1
  have hbar : LocalPreparedBarrier hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier := hG.2.1
  have htgt : HostFenceTargetClearV7 (C (ring.rightNeighbor e)) := hG.2.2
  have hnf0 : ¬ OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier := by
    intro h; have := h.1.1; rw [htgt.1] at this; cases this
  have hov0 : ¬ OrphanVictimGuard (C e) (C (ring.rightNeighbor e)) := by
    intro h; have := h.1; rw [htgt.1] at this; cases this
  have how0 : ¬ OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e)) := by
    intro h; have := h.2.2.1; rw [htgt.1] at this; cases this
  have hop0 : ¬ OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e)) := by
    intro h; have := h.2.1; rw [htgt.1] at this; cases this
  have hz0 : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) := by
    apply notZeroRefresh_of_left_role
    rw [rowV10b_of_handoff hpsi hwidth hle _ _ hG, hfence.1]
    intro h
    have h' : SpliceRole.predecessorArmed = SpliceRole.none := h
    cases h'
  have hrow0 : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
      hostFenceHandoffWriteV10b (C e) (C (ring.rightNeighbor e)) := by
    rw [rowV10d_of_none hpsi hwidth hle _ _ hnf0 hov0 how0 hop0, rowV10c_of_notZero hpsi hwidth hle _ _ hz0,
      rowV10b_of_handoff hpsi hwidth hle _ _ hG]
  have hchange0 : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) ≠ (C e, C (ring.rightNeighbor e)) := by
    intro h
    rw [hrow0] at h
    have := congrArg (fun z : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau => role z.1.carrier) h
    simp only [hostFenceHandoffWriteV10b] at this
    rw [hfence.1] at this
    cases this
  -- the configuration after the handoff
  let D1 := serveIter hpsi hwidth hle ring e 1 C
  have hD1 : D1 = fun i => if i = e then setControlV6 (C e) .predecessorArmed false
      else if i = ring.rightNeighbor e then setControlV6 (C (ring.rightNeighbor e)) .front true else C i := by
    show stepV10e hpsi hwidth hle ring C e = _
    rw [stepV10e_of_change hpsi hwidth hle ring C e hne hchange0]
    funext i
    simp only [stepV10d, hne, if_false, hrow0, hostFenceHandoffWriteV10b]
  have hD1e : D1 e = setControlV6 (C e) .predecessorArmed false := by rw [hD1]; simp
  have hD1j : D1 (ring.rightNeighbor e) = setControlV6 (C (ring.rightNeighbor e)) .front true := by
    rw [hD1]; simp [hne]
  -- second service: MOVE-SEEK
  have hl1 : role (D1 e).carrier = .predecessorArmed := by rw [hD1e]; rfl
  have hlp1 : (D1 e).carrier.repairPending = false := by rw [hD1e]; rfl
  have hlt1 : (D1 e).acquireTicket = false := by rw [hD1e]; rfl
  have hr1 : ReservedFrontHoldGuard (D1 (ring.rightNeighbor e)).carrier := by rw [hD1j]; exact ⟨rfl, rfl⟩
  have hbar1 : LocalPreparedBarrier hpsi (D1 e).carrier (D1 (ring.rightNeighbor e)).carrier := by
    rw [hD1e, hD1j]; exact barrier_of_control hpsi _ _ _ _ _ _ hbar
  have hlead1 : (D1 e).carrier.splice.base.core.core.leader = false := by rw [hD1e]; exact hl
  have hrlead1 : (D1 (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = false := by
    rw [hD1j]; exact hr
  have hrowb1 := rowV10b_of_moveSeek hpsi hwidth hle (D1 e) (D1 (ring.rightNeighbor e))
    hl1 hlp1 hlt1 hr1 hbar1 hlead1 hrlead1
  have hnf1 : ¬ OrphanReservedFrontGuardV3 (D1 e).carrier (D1 (ring.rightNeighbor e)).carrier :=
    fun h => h.2 hl1
  have hov1 : ¬ OrphanVictimGuard (D1 e) (D1 (ring.rightNeighbor e)) := by
    intro h; have := h.1; rw [hr1.1] at this; cases this
  have how1 : ¬ OwnedPendingVictimGuard (D1 e) (D1 (ring.rightNeighbor e)) := by
    intro h; have := h.2.2.1; rw [hr1.1] at this; cases this
  have hop1 : ¬ OwnerlessPendingPredGuard (D1 e) (D1 (ring.rightNeighbor e)) := by
    intro h; have := h.1; rw [hl1] at this; cases this
  have hz1 : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle (D1 e) (D1 (ring.rightNeighbor e)) := by
    apply notZeroRefresh_of_right_ticket hpsi hwidth hle _ _ (by rw [hr1.1]; decide)
    rw [hrowb1]; rfl
  have hrow1 : rowV10d hpsi hwidth hle (D1 e) (D1 (ring.rightNeighbor e)) =
      moveSeekWriteV6 (D1 e) (D1 (ring.rightNeighbor e)) := by
    rw [rowV10d_of_none hpsi hwidth hle _ _ hnf1 hov1 how1 hop1, rowV10c_of_notZero hpsi hwidth hle _ _ hz1, hrowb1]
  have hchange1 : rowV10d hpsi hwidth hle (D1 e) (D1 (ring.rightNeighbor e)) ≠ (D1 e, D1 (ring.rightNeighbor e)) := by
    intro h
    rw [hrow1] at h
    have := congrArg (fun z : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau => z.2.acquireTicket) h
    simp only [moveSeekWriteV6, setTicketV6] at this
    rw [hD1j] at this
    cases this
  let D2 := serveIter hpsi hwidth hle ring e 2 C
  have hD2 : D2 = fun i => if i = e then D1 e
      else if i = ring.rightNeighbor e then setTicketV6 (D1 (ring.rightNeighbor e)) true else D1 i := by
    show stepV10e hpsi hwidth hle ring D1 e = _
    rw [stepV10e_of_change hpsi hwidth hle ring D1 e hne hchange1]
    funext i
    simp only [stepV10d, hne, if_false, hrow1, moveSeekWriteV6]
  have hD2e : D2 e = D1 e := by rw [hD2]; simp
  have hD2j : D2 (ring.rightNeighbor e) = setTicketV6 (D1 (ring.rightNeighbor e)) true := by
    rw [hD2]; simp [hne]
  -- third service: every controller row stutters, so the physical hold runs
  have hl2 : role (D2 e).carrier = .predecessorArmed := by rw [hD2e]; exact hl1
  have hlp2 : (D2 e).carrier.repairPending = false := by rw [hD2e]; exact hlp1
  have hlt2 : (D2 e).acquireTicket = false := by rw [hD2e]; exact hlt1
  have hr2 : ReservedFrontHoldGuard (D2 (ring.rightNeighbor e)).carrier := by rw [hD2j]; exact hr1
  have hbar2 : LocalPreparedBarrier hpsi (D2 e).carrier (D2 (ring.rightNeighbor e)).carrier := by
    rw [hD2e, hD2j]; exact barrier_of_ticket hpsi _ _ _ hbar1
  have hlead2 : (D2 e).carrier.splice.base.core.core.leader = false := by rw [hD2e]; exact hlead1
  have hrlead2 : (D2 (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = false := by
    rw [hD2j]; exact hrlead1
  have hrowb2 := rowV10b_of_moveSeek hpsi hwidth hle (D2 e) (D2 (ring.rightNeighbor e))
    hl2 hlp2 hlt2 hr2 hbar2 hlead2 hrlead2
  have hnf2 : ¬ OrphanReservedFrontGuardV3 (D2 e).carrier (D2 (ring.rightNeighbor e)).carrier :=
    fun h => h.2 hl2
  have hov2 : ¬ OrphanVictimGuard (D2 e) (D2 (ring.rightNeighbor e)) := by
    intro h; have := h.1; rw [hr2.1] at this; cases this
  have how2 : ¬ OwnedPendingVictimGuard (D2 e) (D2 (ring.rightNeighbor e)) := by
    intro h; have := h.2.2.1; rw [hr2.1] at this; cases this
  have hop2 : ¬ OwnerlessPendingPredGuard (D2 e) (D2 (ring.rightNeighbor e)) := by
    intro h; have := h.1; rw [hl2] at this; cases this
  have hz2 : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle (D2 e) (D2 (ring.rightNeighbor e)) := by
    apply notZeroRefresh_of_right_ticket hpsi hwidth hle _ _ (by rw [hr2.1]; decide)
    rw [hrowb2]; rfl
  have hstutter2 : rowV10d hpsi hwidth hle (D2 e) (D2 (ring.rightNeighbor e)) = (D2 e, D2 (ring.rightNeighbor e)) := by
    rw [rowV10d_of_none hpsi hwidth hle _ _ hnf2 hov2 how2 hop2, rowV10c_of_notZero hpsi hwidth hle _ _ hz2, hrowb2]
    unfold moveSeekWriteV6
    rw [hD2j]
    rfl
  have hvr2 : ¬ VictimRightScrubGuardV6 (D2 (ring.rightNeighbor e)) := by
    intro h; have := h.1; rw [hr2.1] at this; cases this
  have hfr2 : ¬ FrontRightScrubGuardV6 (D2 (ring.rightNeighbor e)) := by
    intro h; have := h.2; rw [hr2.2] at this; cases this
  have hmr2 : ¬ MalformedRightPendingGuardV6 (D2 (ring.rightNeighbor e)) := by
    intro h; exact h.2.2.1 hr2.1
  have hpr2 : ¬ role (D2 (ring.rightNeighbor e)).carrier = .predecessorArmed := by
    rw [hr2.1]; decide
  show PhysicalServiceAt hpsi hwidth hle ring D2 (stepV10e hpsi hwidth hle ring D2 e) e
  rw [stepV10e_of_physical hpsi hwidth hle ring D2 e hne hstutter2 hvr2 hfr2 hmr2 hpr2]
  exact physicalHold_is_physical hpsi hwidth hle ring D2 e hne

end B9SpliceV10eHandoffFollowUp
