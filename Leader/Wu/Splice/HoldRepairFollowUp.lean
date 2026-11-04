import Leader.Wu.Splice.HoldRepairFirstRow

set_option autoImplicit false
set_option Elab.async false

/-! # V10j: the three follow-up cases progress within three services, and the row theorem

`iterRow m (l, r)` is the served pair after `m` consecutive V10j services of the same edge.
* handoff: the third service is the physical hold (`handoff_progress`);
* ownerless pending predecessor behind a neutral unticketed cell: the second service is physical or drops the
  pair weight below its start (`ownerless_progress`);
* ARM-B: the third service drops the pair weight below its start (`armB_progress`).
`row_progress_or_hold`: every served pair with ticket-shaped cells progresses within three services or is a
stall shape. -/

namespace B9SpliceV10jFollowUp

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10j
  B9SpliceV10jHoldRing B9SpliceV10eRowPotential B9SpliceV10eHandoffFollowUp B9SpliceV10ePhysicalHoldNoBirth
  B9SpliceV10jRowProgress B9SpliceV10jFirstRow

variable {psi width kappa tau : Nat}

/-- The pair after `m` consecutive services of the same edge. -/
noncomputable def iterRow (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) :
    Nat → R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau →
      R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau
  | 0, p => p
  | m + 1, p => rowV10j hpsi hwidth hle (iterRow hpsi hwidth hle m p).1 (iterRow hpsi hwidth hle m p).2

theorem iterRow_zero (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (p : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) : iterRow hpsi hwidth hle 0 p = p := rfl

theorem iterRow_succ (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (m : Nat)
    (p : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) :
    iterRow hpsi hwidth hle (m + 1) p =
      rowV10j hpsi hwidth hle (iterRow hpsi hwidth hle m p).1 (iterRow hpsi hwidth hle m p).2 := rfl

/-- Progress of a served pair within three services. -/
def RowProgress (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  ∃ m, m < 3 ∧
    (PhysRow hpsi hwidth hle (iterRow hpsi hwidth hle m (l, r)).1 (iterRow hpsi hwidth hle m (l, r)).2
        (iterRow hpsi hwidth hle (m + 1) (l, r)) ∨
      wsum (iterRow hpsi hwidth hle (m + 1) (l, r)) < wsum (l, r))

/-! ## Base invariance of the deletion test -/

theorem ldc_congr (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r a b : R1AgentStateV6 psi kappa tau)
    (ha : a.carrier.splice.base = l.carrier.splice.base) (hb : b.carrier.splice.base = r.carrier.splice.base) :
    LeftDeletionCandidate hpsi hwidth hle a.carrier.splice b.carrier.splice ↔
      LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice := by
  unfold LeftDeletionCandidate
  rw [ha, hb]

/-- `rowV10dg` reduces to `rowV7` when no garbage row, handoff, busy front, stale predecessor or zero refresh
fires. -/
theorem rowV10dg_eq_rowV7 (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hD1 : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier) (hD2 : ¬ OrphanVictimGuard l r)
    (hD3 : ¬ OwnedPendingVictimGuard l r) (hD4 : ¬ OwnerlessPendingPredGuard l r)
    (hHO : ¬ HostFenceAdvanceGuardV10b hpsi l r) (hBF : ¬ HostFenceBusyFrontGuardV9 hpsi l r)
    (hSP8 : ¬ RightStalePredecessorHoldGuardV8 l r)
    (hZR : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r) :
    rowV10dg hpsi hwidth hle l r = rowV7 hpsi hwidth hle l r := by
  rw [rowV10dg.eq_1, if_neg hD1, if_neg hD2, if_neg hD3, if_neg hD4, rowV10c.eq_1, if_neg hZR,
    rowV10b.eq_1, if_neg hHO, rowV9.eq_1, if_neg hBF, rowV8.eq_1, if_neg hSP8]

theorem rowV10b_eq_rowV7 (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hHO : ¬ HostFenceAdvanceGuardV10b hpsi l r) (hBF : ¬ HostFenceBusyFrontGuardV9 hpsi l r)
    (hSP8 : ¬ RightStalePredecessorHoldGuardV8 l r) :
    rowV10b hpsi hwidth hle l r = rowV7 hpsi hwidth hle l r := by
  rw [rowV10b.eq_1, if_neg hHO, rowV9.eq_1, if_neg hBF, rowV8.eq_1, if_neg hSP8]

/-! ## Handoff -/

theorem handoff_progress (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hdel : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice)
    (hG : HostFenceAdvanceGuardV10b hpsi l r) :
    RowProgress hpsi hwidth hle l r := by
  classical
  have hfence : HostFenceShapeV7 l := hG.1
  have hbar : LocalPreparedBarrier hpsi l.carrier r.carrier := hG.2.1
  have htgt : HostFenceTargetClearV7 r := hG.2.2
  -- first service: the handoff
  have hD1 : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier := by
    intro h; have := h.1.1; rw [htgt.1] at this; exact absurd this (by decide)
  have hD2 : ¬ OrphanVictimGuard l r := by intro h; have := h.1; rw [htgt.1] at this; exact absurd this (by decide)
  have hD3 : ¬ OwnedPendingVictimGuard l r := by
    intro h; have := h.2.2.1; rw [htgt.1] at this; exact absurd this (by decide)
  have hD4 : ¬ OwnerlessPendingPredGuard l r := by
    intro h; have := h.2.1; rw [htgt.1] at this; exact absurd this (by decide)
  have hz0 : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r := by
    apply notZeroRefresh_of_left_role
    rw [rowV10b_of_handoff hpsi hwidth hle _ _ hG, hfence.1]
    have hrr : role (hostFenceHandoffWriteV10b l r).1.carrier = .predecessorArmed := rfl
    rw [hrr]; decide
  have hrow1dg : rowV10dg hpsi hwidth hle l r = hostFenceHandoffWriteV10b l r := by
    rw [rowV10dg.eq_1, if_neg hD1, if_neg hD2, if_neg hD3, if_neg hD4, rowV10c.eq_1, if_neg hz0,
      rowV10b_of_handoff hpsi hwidth hle _ _ hG]
  have hchange1 : rowV10dg hpsi hwidth hle l r ≠ (l, r) := by
    intro h
    rw [hrow1dg] at h
    have := congrArg (fun z : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau => role z.1.carrier) h
    have hrr : role (hostFenceHandoffWriteV10b l r).1.carrier = .predecessorArmed := rfl
    rw [hrr, hfence.1] at this
    exact absurd this (by decide)
  let a := setControlV6 l .predecessorArmed false
  let b := setControlV6 r .front true
  have h1 : iterRow hpsi hwidth hle 1 (l, r) = (a, b) := by
    rw [iterRow_succ, iterRow_zero]
    dsimp only
    rw [rowV10j_of_notLDC hpsi hwidth hle _ _ hdel, rowV10g_of_change hpsi hwidth hle _ _ hchange1, hrow1dg]
    rfl
  -- second service: MOVE-SEEK
  have hdel1 : ¬ LeftDeletionCandidate hpsi hwidth hle a.carrier.splice b.carrier.splice :=
    fun h => hdel ((ldc_congr hpsi hwidth hle l r a b rfl rfl).1 h)
  have ha1 : role a.carrier = .predecessorArmed := rfl
  have ha2 : a.carrier.repairPending = false := rfl
  have hbRF : ReservedFrontHoldGuard b.carrier := ⟨rfl, rfl⟩
  have hbar1 : LocalPreparedBarrier hpsi a.carrier b.carrier := barrier_of_control hpsi _ _ _ _ _ _ hbar
  have hE1 : ¬ OrphanReservedFrontGuardV3 a.carrier b.carrier := fun h => h.2 ha1
  have hE2 : ¬ OrphanVictimGuard a b := by intro h; have := h.1; rw [hbRF.1] at this; exact absurd this (by decide)
  have hE3 : ¬ OwnedPendingVictimGuard a b := by
    intro h; have := h.2.2.1; rw [hbRF.1] at this; exact absurd this (by decide)
  have hE4 : ¬ OwnerlessPendingPredGuard a b := by intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hfa : ¬ HostFenceShapeV7 a := by intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hfb : ¬ HostFenceShapeV7 b := by intro h; have := h.1; rw [hbRF.1] at this; exact absurd this (by decide)
  have hHOa : ¬ HostFenceAdvanceGuardV10b hpsi a b := fun h => hfa h.1
  have hBFa : ¬ HostFenceBusyFrontGuardV9 hpsi a b := fun h => hfa h.1
  have hSPa : ¬ RightStalePredecessorHoldGuardV8 a b := by
    intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hmafa : ¬ MoveAcquireFrontGuardV6 hpsi a b := by
    intro h; have := h.1.1; rw [ha1] at this; exact absurd this (by decide)
  have hAa : ¬ ArmAGuard hpsi hwidth hle a.carrier b.carrier := by
    intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hBa : ¬ ArmBGuard a.carrier b.carrier := by
    intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hDela : ¬ DeleteGuard hpsi hwidth hle a.carrier b.carrier := by
    intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hPHa : ¬ PendingHoldGuard hpsi hwidth hle a.carrier b.carrier := by
    intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hPAa : ¬ PendingAbortGuard hpsi hwidth hle a.carrier b.carrier := by
    intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hMCa : ¬ MoveCommitGuard a.carrier b.carrier := by
    intro h; have := h.2.2.1; rw [hbRF.1] at this; exact absurd this (by decide)
  have hMSa : ¬ MoveStopGuardV3 hpsi a.carrier b.carrier := fun h => h.2.2.2 hbar1
  have hSKa : MoveSeekGuardV3 hpsi a.carrier b.carrier := ⟨ha1, ha2, hbRF, hbar1⟩
  have hrow7a : rowV7 hpsi hwidth hle a b = (a, setTicketV6 b true) := by
    rw [rowV7.eq_1, if_neg hfa, if_neg hfb, if_neg hmafa, if_neg hAa, if_neg hBa, if_neg hDela, if_neg hPHa,
      if_neg hPAa, if_neg hMCa, if_neg hMSa, if_pos hSKa]
    rfl
  have hzA : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle a b := by
    apply notZeroRefresh_of_right_ticket hpsi hwidth hle a b (by rw [hbRF.1]; decide)
    rw [rowV10b_eq_rowV7 hpsi hwidth hle a b hHOa hBFa hSPa, hrow7a]
    rfl
  have hrow2dg : rowV10dg hpsi hwidth hle a b = (a, setTicketV6 b true) := by
    rw [rowV10dg_eq_rowV7 hpsi hwidth hle a b hE1 hE2 hE3 hE4 hHOa hBFa hSPa hzA, hrow7a]
  have hchange2 : rowV10dg hpsi hwidth hle a b ≠ (a, b) := by
    intro h
    rw [hrow2dg] at h
    have := congrArg (fun z : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau => z.2.acquireTicket) h
    have hbt : b.acquireTicket = false := rfl
    simp only [setTicketV6] at this
    rw [hbt] at this
    exact absurd this (by decide)
  let b' := setTicketV6 b true
  have h2 : iterRow hpsi hwidth hle 2 (l, r) = (a, b') := by
    rw [iterRow_succ, h1]
    dsimp only
    rw [rowV10j_of_notLDC hpsi hwidth hle _ _ hdel1, rowV10g_of_change hpsi hwidth hle _ _ hchange2, hrow2dg]
  -- third service: every controller row stutters, so the physical hold runs
  have hdel2 : ¬ LeftDeletionCandidate hpsi hwidth hle a.carrier.splice b'.carrier.splice :=
    fun h => hdel ((ldc_congr hpsi hwidth hle l r a b' rfl rfl).1 h)
  have hb'RF : ReservedFrontHoldGuard b'.carrier := hbRF
  have hbar2 : LocalPreparedBarrier hpsi a.carrier b'.carrier := barrier_of_ticket hpsi _ _ _ hbar1
  have hF1 : ¬ OrphanReservedFrontGuardV3 a.carrier b'.carrier := fun h => h.2 ha1
  have hF2 : ¬ OrphanVictimGuard a b' := by intro h; have := h.1; rw [hb'RF.1] at this; exact absurd this (by decide)
  have hF3 : ¬ OwnedPendingVictimGuard a b' := by
    intro h; have := h.2.2.1; rw [hb'RF.1] at this; exact absurd this (by decide)
  have hF4 : ¬ OwnerlessPendingPredGuard a b' := by intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hfb' : ¬ HostFenceShapeV7 b' := by intro h; have := h.1; rw [hb'RF.1] at this; exact absurd this (by decide)
  have hHOb : ¬ HostFenceAdvanceGuardV10b hpsi a b' := fun h => hfa h.1
  have hBFb : ¬ HostFenceBusyFrontGuardV9 hpsi a b' := fun h => hfa h.1
  have hSPb : ¬ RightStalePredecessorHoldGuardV8 a b' := by
    intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hmafb : ¬ MoveAcquireFrontGuardV6 hpsi a b' := by
    intro h; have := h.1.1; rw [ha1] at this; exact absurd this (by decide)
  have hAb : ¬ ArmAGuard hpsi hwidth hle a.carrier b'.carrier := by
    intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hBb : ¬ ArmBGuard a.carrier b'.carrier := by
    intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hDelb : ¬ DeleteGuard hpsi hwidth hle a.carrier b'.carrier := by
    intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hPHb : ¬ PendingHoldGuard hpsi hwidth hle a.carrier b'.carrier := by
    intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hPAb : ¬ PendingAbortGuard hpsi hwidth hle a.carrier b'.carrier := by
    intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hMCb : ¬ MoveCommitGuard a.carrier b'.carrier := by
    intro h; have := h.2.2.1; rw [hb'RF.1] at this; exact absurd this (by decide)
  have hMSb : ¬ MoveStopGuardV3 hpsi a.carrier b'.carrier := fun h => h.2.2.2 hbar2
  have hSKb : MoveSeekGuardV3 hpsi a.carrier b'.carrier := ⟨ha1, ha2, hb'RF, hbar2⟩
  have hrow7b : rowV7 hpsi hwidth hle a b' = (a, b') := by
    rw [rowV7.eq_1, if_neg hfa, if_neg hfb', if_neg hmafb, if_neg hAb, if_neg hBb, if_neg hDelb, if_neg hPHb,
      if_neg hPAb, if_neg hMCb, if_neg hMSb, if_pos hSKb]
    show (a, setTicketV6 b' true) = (a, b')
    rw [setTicket_self b' rfl]
  have hrow3dg : rowV10dg hpsi hwidth hle a b' = (a, b') := by
    rw [rowV10dg.eq_1, if_neg hF1, if_neg hF2, if_neg hF3, if_neg hF4, rowV10c.eq_1]
    by_cases hz : ZeroRefreshOnlyGuardV10c hpsi hwidth hle a b'
    · rw [if_pos hz]
    · rw [if_neg hz, rowV10b_eq_rowV7 hpsi hwidth hle a b' hHOb hBFb hSPb, hrow7b]
  have hphys : rowV10g hpsi hwidth hle a b' = physicalHoldV6 hpsi hwidth hle a b' := by
    have hw := rowV10g.eq_1 hpsi hwidth hle a b'
    dsimp only at hw
    rw [hw, if_pos hrow3dg]
    have s0 : ¬ (role a.carrier = .predecessorArmed ∧ a.carrier.repairPending = true) := by
      intro h; rw [ha2] at h; exact absurd h.2 (by decide)
    have s1 : ¬ VictimRightScrubGuardV6 b' := by intro h; have := h.1; rw [hb'RF.1] at this; exact absurd this (by decide)
    have s2 : ¬ FrontRightScrubGuardV6 b' := by intro h; have := h.2; rw [hb'RF.2] at this; exact absurd this (by decide)
    have s3 : ¬ MalformedRightPendingGuardV6 b' := fun h => h.2.2.1 hb'RF.1
    have s4 : ¬ role b'.carrier = .predecessorArmed := by rw [hb'RF.1]; decide
    rw [if_neg s0, if_neg s1, if_neg s2, if_neg s3, if_neg s4]
  refine ⟨2, by decide, Or.inl ?_⟩
  have h3 : iterRow hpsi hwidth hle 3 (l, r) = physicalHoldV6 hpsi hwidth hle a b' := by
    rw [iterRow_succ, h2]
    dsimp only
    rw [rowV10j_of_notLDC hpsi hwidth hle _ _ hdel2, hphys]
  rw [h3, h2]
  exact phys_hold hpsi hwidth hle a b'

/-! ## Ownerless pending predecessor behind a neutral unticketed cell -/

theorem ownerless_progress (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (htr : TicketShapeV7 r)
    (hdel : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice)
    (hl1 : role l.carrier = .none) (hl2 : l.carrier.repairPending = false) (hl3 : l.acquireTicket = false)
    (hr1 : role r.carrier = .predecessorArmed) (hr2 : r.carrier.repairPending = true) :
    RowProgress hpsi hwidth hle l r := by
  classical
  have hrt : r.acquireTicket = false := ticket_false_of_shape r htr (by rw [hr1]; decide) (by rw [hr1]; decide)
  have hwl : controllerWeightV6 l = 0 := by unfold controllerWeightV6; rw [hl1, hl2, hl3]
  have hwr : controllerWeightV6 r = 4 := by unfold controllerWeightV6; rw [hr1, hr2, hrt]
  have hD1 : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier := by
    intro h; have := h.1.1; rw [hr1] at this; exact absurd this (by decide)
  have hD2 : ¬ OrphanVictimGuard l r := by intro h; have := h.1; rw [hr1] at this; exact absurd this (by decide)
  have hD3 : ¬ OwnedPendingVictimGuard l r := by
    intro h; have := h.1; rw [hl1] at this; exact absurd this (by decide)
  have hD4 : OwnerlessPendingPredGuard l r := ⟨hl1, hr1, hr2⟩
  have hrow1 : rowV10dg hpsi hwidth hle l r = (fenceV6 l, settleV6 r) := by
    rw [rowV10dg.eq_1, if_neg hD1, if_neg hD2, if_neg hD3, if_pos hD4]
  have hchange1 : rowV10dg hpsi hwidth hle l r ≠ (l, r) := by
    intro h
    rw [hrow1] at h
    have := congrArg (fun z : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau => z.2.carrier.repairPending) h
    have hs : (settleV6 r).carrier.repairPending = false := rfl
    simp only at this
    rw [hs, hr2] at this
    exact absurd this (by decide)
  let a := fenceV6 l
  let b := settleV6 r
  have h1 : iterRow hpsi hwidth hle 1 (l, r) = (a, b) := by
    rw [iterRow_succ, iterRow_zero]
    dsimp only
    rw [rowV10j_of_notLDC hpsi hwidth hle _ _ hdel, rowV10g_of_change hpsi hwidth hle _ _ hchange1, hrow1]
  have hdel1 : ¬ LeftDeletionCandidate hpsi hwidth hle a.carrier.splice b.carrier.splice :=
    fun h => hdel ((ldc_congr hpsi hwidth hle l r a b rfl rfl).1 h)
  have hfa : HostFenceShapeV7 a := fence_shape l
  have hb1 : role b.carrier = .predecessorArmed := rfl
  have hb2 : b.carrier.repairPending = false := rfl
  have hE1 : ¬ OrphanReservedFrontGuardV3 a.carrier b.carrier := by
    intro h; have := h.1.1; rw [hb1] at this; exact absurd this (by decide)
  have hE2 : ¬ OrphanVictimGuard a b := by intro h; have := h.1; rw [hb1] at this; exact absurd this (by decide)
  have hE3 : ¬ OwnedPendingVictimGuard a b := by
    intro h; have := h.1; rw [hfa.1] at this; exact absurd this (by decide)
  have hE4 : ¬ OwnerlessPendingPredGuard a b := by
    intro h; have := h.2.2; rw [hb2] at this; exact absurd this (by decide)
  have htc : ¬ HostFenceTargetClearV7 b := by intro h; have := h.1; rw [hb1] at this; exact absurd this (by decide)
  have hHO : ¬ HostFenceAdvanceGuardV10b hpsi a b := fun h => htc h.2.2
  have hBF : ¬ HostFenceBusyFrontGuardV9 hpsi a b := by
    intro h; have := h.2.2.1; rw [hb1] at this; exact absurd this (by decide)
  have hSP : ¬ RightStalePredecessorHoldGuardV8 a b := by
    intro h; have := h.2.2.1; rw [hfa.2.2] at this; exact absurd this (by decide)
  have hz : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle a b := notZeroRefresh_of_left_ticket hpsi hwidth hle a b hfa.2.2
  have hw7 := rowV7.eq_1 hpsi hwidth hle a b
  rw [if_pos hfa] at hw7
  by_cases hbar : LocalPreparedBarrier hpsi a.carrier b.carrier
  · -- the fence holds on a busy target; the stutter branch runs physical-then-fence
    rw [if_pos hbar, if_neg htc] at hw7
    have hrow2dg : rowV10dg hpsi hwidth hle a b = (a, b) := by
      rw [rowV10dg_eq_rowV7 hpsi hwidth hle a b hE1 hE2 hE3 hE4 hHO hBF hSP hz, hw7]
      rfl
    have hg : rowV10g hpsi hwidth hle a b =
        ((physicalHoldV6 hpsi hwidth hle a b).1, fenceV6 (physicalHoldV6 hpsi hwidth hle a b).2) := by
      have hw := rowV10g.eq_1 hpsi hwidth hle a b
      dsimp only at hw
      rw [hw, if_pos hrow2dg]
      have s0 : ¬ (role a.carrier = .predecessorArmed ∧ a.carrier.repairPending = true) := by
        intro h; have := h.1; rw [hfa.1] at this; exact absurd this (by decide)
      have s1 : ¬ VictimRightScrubGuardV6 b := by intro h; have := h.1; rw [hb1] at this; exact absurd this (by decide)
      have s2 : ¬ FrontRightScrubGuardV6 b := by intro h; have := h.1; rw [hb1] at this; exact absurd this (by decide)
      have s3 : ¬ MalformedRightPendingGuardV6 b := fun h => h.2.1 hb1
      have s5 : ¬ b.carrier.repairPending = true := by rw [hb2]; decide
      rw [if_neg s0, if_neg s1, if_neg s2, if_neg s3, if_pos hb1, if_neg s5]
    refine ⟨1, by decide, Or.inl ?_⟩
    have h2 : iterRow hpsi hwidth hle 2 (l, r) =
        ((physicalHoldV6 hpsi hwidth hle a b).1, fenceV6 (physicalHoldV6 hpsi hwidth hle a b).2) := by
      rw [iterRow_succ, h1]
      dsimp only
      rw [rowV10j_of_notLDC hpsi hwidth hle _ _ hdel1, hg]
    rw [h2, h1]
    exact phys_fence hpsi hwidth hle a b
  · -- no barrier: the fence is consumed, the pair weight falls below its start
    rw [if_neg hbar] at hw7
    have hrow2dg : rowV10dg hpsi hwidth hle a b = (clearTicketV6 a, b) := by
      rw [rowV10dg_eq_rowV7 hpsi hwidth hle a b hE1 hE2 hE3 hE4 hHO hBF hSP hz, hw7]
      rfl
    have hchange2 : rowV10dg hpsi hwidth hle a b ≠ (a, b) := by
      intro h
      rw [hrow2dg] at h
      have := congrArg (fun z : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau => z.1.acquireTicket) h
      have hc : (clearTicketV6 a).acquireTicket = false := rfl
      simp only at this
      rw [hc, hfa.2.2] at this
      exact absurd this (by decide)
    refine ⟨1, by decide, Or.inr ?_⟩
    have h2 : iterRow hpsi hwidth hle 2 (l, r) = (clearTicketV6 a, b) := by
      rw [iterRow_succ, h1]
      dsimp only
      rw [rowV10j_of_notLDC hpsi hwidth hle _ _ hdel1, rowV10g_of_change hpsi hwidth hle _ _ hchange2, hrow2dg]
    rw [h2]
    unfold wsum
    dsimp only
    rw [weight_hostFence_clearTicket a hfa, weight_settle, hwl, hwr]
    decide

/-! ## ARM-B -/

theorem armB_progress (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hdel : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice)
    (hG : ArmBGuard l.carrier r.carrier) (hlt : l.acquireTicket = false) :
    RowProgress hpsi hwidth hle l r := by
  classical
  have hl1 : role l.carrier = .none := hG.1
  have hl2 : l.carrier.repairPending = false := hG.2.1
  have hr1 : role r.carrier = .victimArmed := hG.2.2.1
  have hr2 : r.carrier.repairPending = false := hG.2.2.2.1
  have hwr : 2 ≤ controllerWeightV6 r := weight_victim_ge r hr1
  -- first service: ARM-B
  have hfl : ¬ HostFenceShapeV7 l := by intro h; have := h.2.2; rw [hlt] at this; exact absurd this (by decide)
  have hfr : ¬ HostFenceShapeV7 r := by intro h; have := h.1; rw [hr1] at this; exact absurd this (by decide)
  have hD1 : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier := by
    intro h; have := h.1.1; rw [hr1] at this; exact absurd this (by decide)
  have hD2 : ¬ OrphanVictimGuard l r := by intro h; have := h.2.1; rw [hr2] at this; exact absurd this (by decide)
  have hD3 : ¬ OwnedPendingVictimGuard l r := by intro h; have := h.1; rw [hl1] at this; exact absurd this (by decide)
  have hD4 : ¬ OwnerlessPendingPredGuard l r := by
    intro h; have := h.2.1; rw [hr1] at this; exact absurd this (by decide)
  have hHO : ¬ HostFenceAdvanceGuardV10b hpsi l r := fun h => hfl h.1
  have hBF : ¬ HostFenceBusyFrontGuardV9 hpsi l r := fun h => hfl h.1
  have hSP : ¬ RightStalePredecessorHoldGuardV8 l r := by
    intro h; have := h.2.2.2.1; rw [hr1] at this; exact absurd this (by decide)
  have hmaf : ¬ MoveAcquireFrontGuardV6 hpsi l r := by
    intro h; have := h.1.1; rw [hl1] at this; exact absurd this (by decide)
  have hA : ¬ ArmAGuard hpsi hwidth hle l.carrier r.carrier := by
    intro h; have := h.2.1; rw [hr1] at this; exact absurd this (by decide)
  have hrow7 : rowV7 hpsi hwidth hle l r = armBWriteV6 l r := by
    rw [rowV7.eq_1, if_neg hfl, if_neg hfr, if_neg hmaf, if_neg hA, if_pos hG]
  have hz : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r := by
    apply notZeroRefresh_of_left_role
    rw [rowV10b_eq_rowV7 hpsi hwidth hle l r hHO hBF hSP, hrow7, hl1]
    show SpliceRole.predecessorArmed ≠ SpliceRole.none
    decide
  have hrow1 : rowV10dg hpsi hwidth hle l r = armBWriteV6 l r := by
    rw [rowV10dg_eq_rowV7 hpsi hwidth hle l r hD1 hD2 hD3 hD4 hHO hBF hSP hz, hrow7]
  have hchange1 : rowV10dg hpsi hwidth hle l r ≠ (l, r) := by
    intro h
    rw [hrow1] at h
    have := congrArg (fun z : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau => role z.1.carrier) h
    have hrr : role (armBWriteV6 l r).1.carrier = .predecessorArmed := rfl
    rw [hrr, hl1] at this
    exact absurd this (by decide)
  let a := setControlV6 l .predecessorArmed false
  let b := setControlV6 r .front false
  have h1 : iterRow hpsi hwidth hle 1 (l, r) = (a, b) := by
    rw [iterRow_succ, iterRow_zero]
    dsimp only
    rw [rowV10j_of_notLDC hpsi hwidth hle _ _ hdel, rowV10g_of_change hpsi hwidth hle _ _ hchange1, hrow1]
    rfl
  -- second service: the right front scrub
  have hdel1 : ¬ LeftDeletionCandidate hpsi hwidth hle a.carrier.splice b.carrier.splice :=
    fun h => hdel ((ldc_congr hpsi hwidth hle l r a b rfl rfl).1 h)
  have ha1 : role a.carrier = .predecessorArmed := rfl
  have ha2 : a.carrier.repairPending = false := rfl
  have hb1 : role b.carrier = .front := rfl
  have hb2 : b.carrier.repairPending = false := rfl
  have hfa : ¬ HostFenceShapeV7 a := by intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hfb : ¬ HostFenceShapeV7 b := by intro h; have := h.1; rw [hb1] at this; exact absurd this (by decide)
  have hnRFb : ¬ ReservedFrontHoldGuard b.carrier := by
    intro h; have := h.2; rw [hb2] at this; exact absurd this (by decide)
  have hE1 : ¬ OrphanReservedFrontGuardV3 a.carrier b.carrier := fun h => hnRFb h.1
  have hE2 : ¬ OrphanVictimGuard a b := by intro h; have := h.1; rw [hb1] at this; exact absurd this (by decide)
  have hE3 : ¬ OwnedPendingVictimGuard a b := by
    intro h; have := h.2.2.1; rw [hb1] at this; exact absurd this (by decide)
  have hE4 : ¬ OwnerlessPendingPredGuard a b := by intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hHOa : ¬ HostFenceAdvanceGuardV10b hpsi a b := fun h => hfa h.1
  have hBFa : ¬ HostFenceBusyFrontGuardV9 hpsi a b := fun h => hfa h.1
  have hSPa : ¬ RightStalePredecessorHoldGuardV8 a b := by
    intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hrow7a : rowV7 hpsi hwidth hle a b = (a, clearControlV6 b) := by
    have hmaf : ¬ MoveAcquireFrontGuardV6 hpsi a b := by
      intro h; have := h.1.1; rw [ha1] at this; exact absurd this (by decide)
    have hA : ¬ ArmAGuard hpsi hwidth hle a.carrier b.carrier := by
      intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hB : ¬ ArmBGuard a.carrier b.carrier := by intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hDel : ¬ DeleteGuard hpsi hwidth hle a.carrier b.carrier := by
      intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hPH : ¬ PendingHoldGuard hpsi hwidth hle a.carrier b.carrier := by
      intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hPA : ¬ PendingAbortGuard hpsi hwidth hle a.carrier b.carrier := by
      intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hMC : ¬ MoveCommitGuard a.carrier b.carrier := by
      intro h; have := h.2.2.1; rw [hb1] at this; exact absurd this (by decide)
    have hMS : ¬ MoveStopGuardV3 hpsi a.carrier b.carrier := fun h => hnRFb h.2.2.1
    have hSK : ¬ MoveSeekGuardV3 hpsi a.carrier b.carrier := fun h => hnRFb h.2.2.1
    have hSKH : ¬ MoveSeekHoldGuardV3 a.carrier b.carrier := by
      intro h; have := h.2.2.1; rw [hb1] at this; exact absurd this (by decide)
    have hPOA : ¬ PendingOwnerAbortGuardV3 a.carrier b.carrier := by
      intro h; have := h.1; rw [hb1] at this; exact absurd this (by decide)
    have hPP : ¬ (role a.carrier = .predecessorArmed ∧ a.carrier.repairPending = true) := by
      intro h; have := h.2; rw [ha2] at this; exact absurd this (by decide)
    have hMAL : ¬ MoveAcquireLegacyGuardV6 a b := by
      intro h; have := h.1.1; rw [ha1] at this; exact absurd this (by decide)
    have hMAA : ¬ MoveAcquireAbortGuardV3 a.carrier b.carrier := by
      intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hRFH : ¬ ReservedFrontHoldGuard a.carrier := by
      intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hVR : ¬ VictimRightScrubGuardV6 b := by intro h; have := h.1; rw [hb1] at this; exact absurd this (by decide)
    have hVL : ¬ VictimLeftScrubGuardV6 a := by intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hFR : FrontRightScrubGuardV6 b := ⟨hb1, hb2⟩
    rw [rowV7.eq_1, if_neg hfa, if_neg hfb, if_neg hmaf, if_neg hA, if_neg hB, if_neg hDel, if_neg hPH, if_neg hPA,
      if_neg hMC, if_neg hMS, if_neg hSK, if_neg hSKH, if_neg hPOA, if_neg hPP, if_neg hMAL, if_neg hMAA, if_neg hE1,
      if_neg hRFH, if_neg hVR, if_neg hVL, if_pos hFR]
    rfl
  have hzA : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle a b := by
    apply notZeroRefresh_of_right_role
    rw [rowV10b_eq_rowV7 hpsi hwidth hle a b hHOa hBFa hSPa, hrow7a, hb1]
    show SpliceRole.none ≠ SpliceRole.front
    decide
  have hrow2 : rowV10dg hpsi hwidth hle a b = (a, clearControlV6 b) := by
    rw [rowV10dg_eq_rowV7 hpsi hwidth hle a b hE1 hE2 hE3 hE4 hHOa hBFa hSPa hzA, hrow7a]
  have hchange2 : rowV10dg hpsi hwidth hle a b ≠ (a, b) := by
    intro h
    rw [hrow2] at h
    have := congrArg (fun z : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau => role z.2.carrier) h
    have hc : role (clearControlV6 b).carrier = .none := rfl
    simp only at this
    rw [hc, hb1] at this
    exact absurd this (by decide)
  let c := clearControlV6 b
  have h2 : iterRow hpsi hwidth hle 2 (l, r) = (a, c) := by
    rw [iterRow_succ, h1]
    dsimp only
    rw [rowV10j_of_notLDC hpsi hwidth hle _ _ hdel1, rowV10g_of_change hpsi hwidth hle _ _ hchange2, hrow2]
  -- third service: the predecessor-left scrub
  have hdel2 : ¬ LeftDeletionCandidate hpsi hwidth hle a.carrier.splice c.carrier.splice :=
    fun h => hdel ((ldc_congr hpsi hwidth hle l r a c rfl rfl).1 h)
  have hc1 : role c.carrier = .none := rfl
  have hc2 : c.carrier.repairPending = false := rfl
  have hc3 : c.acquireTicket = false := rfl
  have hfc : ¬ HostFenceShapeV7 c := by intro h; have := h.2.2; rw [hc3] at this; exact absurd this (by decide)
  have hF1 : ¬ OrphanReservedFrontGuardV3 a.carrier c.carrier := by
    intro h; have := h.1.1; rw [hc1] at this; exact absurd this (by decide)
  have hF2 : ¬ OrphanVictimGuard a c := by intro h; have := h.1; rw [hc1] at this; exact absurd this (by decide)
  have hF3 : ¬ OwnedPendingVictimGuard a c := by
    intro h; have := h.2.2.1; rw [hc1] at this; exact absurd this (by decide)
  have hF4 : ¬ OwnerlessPendingPredGuard a c := by intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hHOc : ¬ HostFenceAdvanceGuardV10b hpsi a c := fun h => hfa h.1
  have hBFc : ¬ HostFenceBusyFrontGuardV9 hpsi a c := fun h => hfa h.1
  have hSPc : ¬ RightStalePredecessorHoldGuardV8 a c := by
    intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
  have hrow7c : rowV7 hpsi hwidth hle a c = (clearControlV6 a, c) := by
    have hmaf : ¬ MoveAcquireFrontGuardV6 hpsi a c := by
      intro h; have := h.1.1; rw [ha1] at this; exact absurd this (by decide)
    have hA : ¬ ArmAGuard hpsi hwidth hle a.carrier c.carrier := by
      intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hB : ¬ ArmBGuard a.carrier c.carrier := by intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hDel : ¬ DeleteGuard hpsi hwidth hle a.carrier c.carrier := by
      intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hPH : ¬ PendingHoldGuard hpsi hwidth hle a.carrier c.carrier := by
      intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hPA : ¬ PendingAbortGuard hpsi hwidth hle a.carrier c.carrier := by
      intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hMC : ¬ MoveCommitGuard a.carrier c.carrier := by
      intro h; have := h.2.2.1; rw [hc1] at this; exact absurd this (by decide)
    have hnRFc : ¬ ReservedFrontHoldGuard c.carrier := by
      intro h; have := h.1; rw [hc1] at this; exact absurd this (by decide)
    have hMS : ¬ MoveStopGuardV3 hpsi a.carrier c.carrier := fun h => hnRFc h.2.2.1
    have hSK : ¬ MoveSeekGuardV3 hpsi a.carrier c.carrier := fun h => hnRFc h.2.2.1
    have hSKH : ¬ MoveSeekHoldGuardV3 a.carrier c.carrier := by
      intro h; have := h.2.2.1; rw [hc1] at this; exact absurd this (by decide)
    have hPOA : ¬ PendingOwnerAbortGuardV3 a.carrier c.carrier := by
      intro h; have := h.1; rw [hc1] at this; exact absurd this (by decide)
    have hPP : ¬ (role a.carrier = .predecessorArmed ∧ a.carrier.repairPending = true) := by
      intro h; have := h.2; rw [ha2] at this; exact absurd this (by decide)
    have hMAL : ¬ MoveAcquireLegacyGuardV6 a c := by
      intro h; have := h.1.1; rw [ha1] at this; exact absurd this (by decide)
    have hMAA : ¬ MoveAcquireAbortGuardV3 a.carrier c.carrier := by
      intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hRFH : ¬ ReservedFrontHoldGuard a.carrier := by
      intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hVR : ¬ VictimRightScrubGuardV6 c := by intro h; have := h.1; rw [hc1] at this; exact absurd this (by decide)
    have hVL : ¬ VictimLeftScrubGuardV6 a := by intro h; have := h.1; rw [ha1] at this; exact absurd this (by decide)
    have hFR : ¬ FrontRightScrubGuardV6 c := by intro h; have := h.1; rw [hc1] at this; exact absurd this (by decide)
    have hML : ¬ MalformedLeftPendingGuardV6 a := by
      intro h; have := h.1; rw [ha2] at this; exact absurd this (by decide)
    have hMR : ¬ MalformedRightPendingGuardV6 c := by
      intro h; have := h.1; rw [hc2] at this; exact absurd this (by decide)
    rw [rowV7.eq_1, if_neg hfa, if_neg hfc, if_neg hmaf, if_neg hA, if_neg hB, if_neg hDel, if_neg hPH, if_neg hPA,
      if_neg hMC, if_neg hMS, if_neg hSK, if_neg hSKH, if_neg hPOA, if_neg hPP, if_neg hMAL, if_neg hMAA, if_neg hF1,
      if_neg hRFH, if_neg hVR, if_neg hVL, if_neg hFR, if_neg hML, if_neg hMR, if_pos ha1]
    rfl
  have hzC : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle a c := by
    apply notZeroRefresh_of_left_role
    rw [rowV10b_eq_rowV7 hpsi hwidth hle a c hHOc hBFc hSPc, hrow7c, ha1]
    show SpliceRole.none ≠ SpliceRole.predecessorArmed
    decide
  have hrow3 : rowV10dg hpsi hwidth hle a c = (clearControlV6 a, c) := by
    rw [rowV10dg_eq_rowV7 hpsi hwidth hle a c hF1 hF2 hF3 hF4 hHOc hBFc hSPc hzC, hrow7c]
  have hchange3 : rowV10dg hpsi hwidth hle a c ≠ (a, c) := by
    intro h
    rw [hrow3] at h
    have := congrArg (fun z : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau => role z.1.carrier) h
    have hc0 : role (clearControlV6 a).carrier = .none := rfl
    simp only at this
    rw [hc0, ha1] at this
    exact absurd this (by decide)
  refine ⟨2, by decide, Or.inr ?_⟩
  have h3 : iterRow hpsi hwidth hle 3 (l, r) = (clearControlV6 a, c) := by
    rw [iterRow_succ, h2]
    dsimp only
    rw [rowV10j_of_notLDC hpsi hwidth hle _ _ hdel2, rowV10g_of_change hpsi hwidth hle _ _ hchange3, hrow3]
  rw [h3]
  unfold wsum
  dsimp only
  rw [weight_clear, weight_clear]
  omega

/-! ## The row theorem -/

theorem row_progress_or_hold (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (htl : TicketShapeV7 l) (htr : TicketShapeV7 r) :
    RowProgress hpsi hwidth hle l r ∨ HoldShapeJ l r := by
  rcases first_row_classified hpsi hwidth hle l r htl htr with hp | hd | hh | hs
  · left; exact ⟨0, by decide, Or.inl hp⟩
  · left; exact ⟨0, by decide, Or.inr hd⟩
  · right; exact hh
  · left
    rcases hs with ⟨hdel, hG | ⟨h1, h2, h3, h4, h5⟩ | ⟨hB, hlt⟩⟩
    · exact handoff_progress hpsi hwidth hle l r hdel hG
    · exact ownerless_progress hpsi hwidth hle l r htr hdel h1 h2 h3 h4 h5
    · exact armB_progress hpsi hwidth hle l r hdel hB hlt

end B9SpliceV10jFollowUp
