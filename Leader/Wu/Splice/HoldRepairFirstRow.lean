import Leader.Wu.Splice.HoldRepairRowVocabulary

set_option autoImplicit false
set_option Elab.async false

/-! # V10j first-service classification

`first_row_classified`: for a served pair whose cells satisfy the ticket shape, the V10j row is physical, strictly
lowers the pair weight, is a stall shape, or is one of the three follow-up cases. -/

namespace B9SpliceV10jFirstRow

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10j
  B9SpliceV10jHoldRing B9SpliceV10eRowPotential B9SpliceV10eHandoffFollowUp B9SpliceV10ePhysicalHoldNoBirth
  B9SpliceV10jRowProgress

variable {psi width kappa tau : Nat}

/-- The classification outcome for a candidate write `w` of the pair `(l, r)`. -/
def FirstOut (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (w : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) : Prop :=
  PhysRow hpsi hwidth hle l r w ∨ wsum w < wsum (l, r) ∨ HoldShapeJ l r ∨ SpecialJ hpsi hwidth hle l r

theorem drop_right (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r b : R1AgentStateV6 psi kappa tau) (h : controllerWeightV6 b < controllerWeightV6 r) :
    FirstOut hpsi hwidth hle l r (l, b) := by
  right; left; unfold wsum; dsimp only; omega

theorem drop_left (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r a : R1AgentStateV6 psi kappa tau) (h : controllerWeightV6 a < controllerWeightV6 l) :
    FirstOut hpsi hwidth hle l r (a, r) := by
  right; left; unfold wsum; dsimp only; omega

theorem drop_pair (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r a b : R1AgentStateV6 psi kappa tau)
    (h : controllerWeightV6 a + controllerWeightV6 b < controllerWeightV6 l + controllerWeightV6 r) :
    FirstOut hpsi hwidth hle l r (a, b) := by
  right; left; unfold wsum; dsimp only; omega

/-- On a settled predecessor facing a pending predecessor, V10dg clears the left controller. -/
theorem rowV10dg_left_none_of_SP_PP (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hl : role l.carrier = .predecessorArmed) (hlp : l.carrier.repairPending = false)
    (hr : role r.carrier = .predecessorArmed) (hrp : r.carrier.repairPending = true) :
    role (rowV10dg hpsi hwidth hle l r).1.carrier = .none := by
  classical
  have hD1 : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier := by
    intro h; have := h.1.1; rw [hr] at this; exact absurd this (by decide)
  have hD2 : ¬ OrphanVictimGuard l r := by intro h; have := h.1; rw [hr] at this; exact absurd this (by decide)
  have hD3 : ¬ OwnedPendingVictimGuard l r := by
    intro h; have := h.2.2.1; rw [hr] at this; exact absurd this (by decide)
  have hD4 : ¬ OwnerlessPendingPredGuard l r := by
    intro h; have := h.1; rw [hl] at this; exact absurd this (by decide)
  have hfL : ¬ HostFenceShapeV7 l := by intro h; have := h.1; rw [hl] at this; exact absurd this (by decide)
  have hfR : ¬ HostFenceShapeV7 r := by intro h; have := h.1; rw [hr] at this; exact absurd this (by decide)
  have hh : ¬ HostFenceAdvanceGuardV10b hpsi l r := fun h => hfL h.1
  have hb : ¬ HostFenceBusyFrontGuardV9 hpsi l r := fun h => hfL h.1
  have hst : ¬ RightStalePredecessorHoldGuardV8 l r := by
    intro h; have := h.1; rw [hl] at this; exact absurd this (by decide)
  have hmaf : ¬ MoveAcquireFrontGuardV6 hpsi l r := by
    intro h; have := h.1.1; rw [hl] at this; exact absurd this (by decide)
  have hA : ¬ ArmAGuard hpsi hwidth hle l.carrier r.carrier := by
    intro h; have := h.1; rw [hl] at this; exact absurd this (by decide)
  have hB : ¬ ArmBGuard l.carrier r.carrier := by
    intro h; have := h.1; rw [hl] at this; exact absurd this (by decide)
  have hDel : ¬ DeleteGuard hpsi hwidth hle l.carrier r.carrier := by
    intro h; have := h.1; rw [hl] at this; exact absurd this (by decide)
  have hPH : ¬ PendingHoldGuard hpsi hwidth hle l.carrier r.carrier := by
    intro h; have := h.1; rw [hl] at this; exact absurd this (by decide)
  have hPA : ¬ PendingAbortGuard hpsi hwidth hle l.carrier r.carrier := by
    intro h; have := h.1; rw [hl] at this; exact absurd this (by decide)
  have h7 : role (rowV7 hpsi hwidth hle l r).1.carrier = .none := by
    rw [rowV7.eq_1, if_neg hfL, if_neg hfR, if_neg hmaf, if_neg hA, if_neg hB, if_neg hDel, if_neg hPH, if_neg hPA]
    by_cases hMC : MoveCommitGuard l.carrier r.carrier
    · rw [if_pos hMC]; rfl
    rw [if_neg hMC]
    have hMS : ¬ MoveStopGuardV3 hpsi l.carrier r.carrier := by
      intro h; have := h.2.2.1.1; rw [hr] at this; exact absurd this (by decide)
    have hSK : ¬ MoveSeekGuardV3 hpsi l.carrier r.carrier := by
      intro h; have := h.2.2.1.1; rw [hr] at this; exact absurd this (by decide)
    have hSKH : ¬ MoveSeekHoldGuardV3 l.carrier r.carrier := by
      intro h; have := h.2.2.1; rw [hr] at this; exact absurd this (by decide)
    have hPOA : ¬ PendingOwnerAbortGuardV3 l.carrier r.carrier := fun h => h.2.2 ⟨hl, hlp⟩
    have hPP : ¬ (role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true) := by
      intro h; rw [hlp] at h; exact absurd h.2 (by decide)
    have hMAL : ¬ MoveAcquireLegacyGuardV6 l r := by
      intro h; have := h.1.1; rw [hl] at this; exact absurd this (by decide)
    have hMAA : ¬ MoveAcquireAbortGuardV3 l.carrier r.carrier := by
      intro h; have := h.1; rw [hl] at this; exact absurd this (by decide)
    have hRFH : ¬ ReservedFrontHoldGuard l.carrier := by
      intro h; have := h.1; rw [hl] at this; exact absurd this (by decide)
    have hVR : ¬ VictimRightScrubGuardV6 r := by intro h; have := h.1; rw [hr] at this; exact absurd this (by decide)
    have hVL : ¬ VictimLeftScrubGuardV6 l := by intro h; have := h.1; rw [hl] at this; exact absurd this (by decide)
    have hFR : ¬ FrontRightScrubGuardV6 r := by intro h; have := h.1; rw [hr] at this; exact absurd this (by decide)
    have hML : ¬ MalformedLeftPendingGuardV6 l := by intro h; have h1 := h.1; rw [hlp] at h1; exact absurd h1 (by decide)
    have hMR : ¬ MalformedRightPendingGuardV6 r := fun h => h.2.1 hr
    rw [if_neg hMS, if_neg hSK, if_neg hSKH, if_neg hPOA, if_neg hPP, if_neg hMAL, if_neg hMAA, if_neg hD1,
      if_neg hRFH, if_neg hVR, if_neg hVL, if_neg hFR, if_neg hML, if_neg hMR, if_pos hl]
    rfl
  have hb7 : rowV10b hpsi hwidth hle l r = rowV7 hpsi hwidth hle l r := by
    rw [rowV10b.eq_1, if_neg hh, rowV9.eq_1, if_neg hb, rowV8.eq_1, if_neg hst]
  have hz : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r := by
    apply notZeroRefresh_of_left_role
    rw [hb7, h7, hl]
    decide
  rw [rowV10dg.eq_1, if_neg hD1, if_neg hD2, if_neg hD3, if_neg hD4, rowV10c.eq_1, if_neg hz, hb7]
  exact h7

theorem stutter_classified (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hq : rowV10dg hpsi hwidth hle l r = (l, r)) :
    FirstOut hpsi hwidth hle l r (rowV10g hpsi hwidth hle l r) := by
  classical
  have hw := rowV10g.eq_1 hpsi hwidth hle l r
  dsimp only at hw
  rw [if_pos hq] at hw
  rw [hw]
  by_cases h0 : role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true
  · rw [if_pos h0]; right; right; left; exact Or.inl h0
  rw [if_neg h0]
  by_cases h1 : VictimRightScrubGuardV6 r
  · rw [if_pos h1]
    exact drop_right hpsi hwidth hle l r _ (by rw [weight_clear]; exact weight_pos_of_role r (by rw [h1.1]; decide))
  rw [if_neg h1]
  by_cases h2 : FrontRightScrubGuardV6 r
  · rw [if_pos h2]
    exact drop_right hpsi hwidth hle l r _ (by rw [weight_clear]; exact weight_pos_of_role r (by rw [h2.1]; decide))
  rw [if_neg h2]
  by_cases h3 : MalformedRightPendingGuardV6 r
  · rw [if_pos h3]
    exact drop_right hpsi hwidth hle l r _ (by rw [weight_clear]; exact weight_pos_of_pending r h3.1)
  rw [if_neg h3]
  by_cases h4 : role r.carrier = .predecessorArmed
  · rw [if_pos h4]
    by_cases h5 : r.carrier.repairPending = true
    · rw [if_pos h5]
      by_cases h6 : ReservedFrontHoldGuard l.carrier
      · rw [if_pos h6]
        exact drop_right hpsi hwidth hle l r _ (by rw [weight_settle]; have := weight_pendingPred_ge r h4 h5; omega)
      rw [if_neg h6]
      by_cases h7 : LeftScrubGuardV10e l
      · rw [if_pos h7]
        refine drop_left hpsi hwidth hle l r _ ?_
        rw [weight_clear]
        rcases h7 with hv | hf | hm
        · exact weight_pos_of_role l (by rw [hv.1]; decide)
        · exact weight_pos_of_role l (by rw [hf.1]; decide)
        · exact weight_pos_of_pending l hm.1
      rw [if_neg h7]
      -- the hold: the left cell is a pending victim
      right; right; left; right; left
      cases hrole : role l.carrier with
      | none =>
          exfalso
          have hD1 : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier := by
            intro h; have := h.1.1; rw [h4] at this; exact absurd this (by decide)
          have hD2 : ¬ OrphanVictimGuard l r := by intro h; have := h.1; rw [h4] at this; exact absurd this (by decide)
          have hD3 : ¬ OwnedPendingVictimGuard l r := by
            intro h; have := h.2.2.1; rw [h4] at this; exact absurd this (by decide)
          have hD4 : OwnerlessPendingPredGuard l r := ⟨hrole, h4, h5⟩
          have hrow : rowV10dg hpsi hwidth hle l r = (fenceV6 l, settleV6 r) := by
            rw [rowV10dg.eq_1, if_neg hD1, if_neg hD2, if_neg hD3, if_pos hD4]
          rw [hrow] at hq
          have hp := congrArg (fun z : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau =>
            z.2.carrier.repairPending) hq
          have hs : (settleV6 r).carrier.repairPending = false := rfl
          simp only at hp
          rw [hs, h5] at hp
          exact absurd hp (by decide)
      | front =>
          exfalso
          cases hp : l.carrier.repairPending
          · exact h7 (Or.inr (Or.inl ⟨hrole, hp⟩))
          · exact h6 ⟨hrole, hp⟩
      | victimArmed =>
          cases hp : l.carrier.repairPending
          · exact absurd (Or.inl ⟨hrole, hp⟩) h7
          · exact ⟨rfl, rfl, h4, h5⟩
      | predecessorArmed =>
          exfalso
          cases hp : l.carrier.repairPending
          · have hn := rowV10dg_left_none_of_SP_PP hpsi hwidth hle l r hrole hp h4 h5
            rw [hq] at hn
            simp only at hn
            rw [hrole] at hn
            exact absurd hn (by decide)
          · exact h0 ⟨hrole, hp⟩
    · rw [if_neg h5]
      left
      exact phys_fence hpsi hwidth hle l r
  · rw [if_neg h4]
    left
    exact phys_hold hpsi hwidth hle l r

theorem rowV7_classified (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (htl : TicketShapeV7 l) (htr : TicketShapeV7 r)
    (hdel : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice)
    (hD1 : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier)
    (hHO : ¬ HostFenceAdvanceGuardV10b hpsi l r)
    (hne : rowV7 hpsi hwidth hle l r ≠ (l, r)) :
    FirstOut hpsi hwidth hle l r (rowV7 hpsi hwidth hle l r) := by
  classical
  have hw := rowV7.eq_1 hpsi hwidth hle l r
  rw [hw]
  rw [hw] at hne
  by_cases hfL : HostFenceShapeV7 l
  · rw [if_pos hfL] at hne ⊢
    by_cases hbar : LocalPreparedBarrier hpsi l.carrier r.carrier
    · rw [if_pos hbar] at hne ⊢
      by_cases htc : HostFenceTargetClearV7 r
      · exact absurd ⟨hfL, hbar, htc⟩ hHO
      · rw [if_neg htc] at hne; exact (hne rfl).elim
    · rw [if_neg hbar]
      show FirstOut hpsi hwidth hle l r (clearTicketV6 l, r)
      exact drop_left hpsi hwidth hle l r _ (by rw [weight_hostFence_clearTicket _ hfL, weight_hostFence _ hfL]; decide)
  rw [if_neg hfL] at hne ⊢
  by_cases hfR : HostFenceShapeV7 r
  · rw [if_pos hfR] at hne; exact (hne rfl).elim
  rw [if_neg hfR] at hne ⊢
  by_cases hmaf : MoveAcquireFrontGuardV6 hpsi l r
  · exact absurd ⟨hmaf.2.2.2.1, by rw [hmaf.1.1]; decide⟩ hD1
  rw [if_neg hmaf] at hne ⊢
  by_cases hA : ArmAGuard hpsi hwidth hle l.carrier r.carrier
  · exact absurd hA.2.2.2.2 hdel
  rw [if_neg hA] at hne ⊢
  by_cases hB : ArmBGuard l.carrier r.carrier
  · right; right; right
    refine ⟨hdel, Or.inr (Or.inr ⟨hB, ?_⟩)⟩
    cases ht : l.acquireTicket
    · rfl
    · exact absurd ⟨hB.1, hB.2.1, ht⟩ hfL
  rw [if_neg hB] at hne ⊢
  by_cases hDel : DeleteGuard hpsi hwidth hle l.carrier r.carrier
  · exact absurd hDel.2.2.2.2 hdel
  rw [if_neg hDel] at hne ⊢
  by_cases hPH : PendingHoldGuard hpsi hwidth hle l.carrier r.carrier
  · exact absurd hPH.2.2.2.2 hdel
  rw [if_neg hPH] at hne ⊢
  by_cases hPA : PendingAbortGuard hpsi hwidth hle l.carrier r.carrier
  · rw [if_pos hPA]
    show FirstOut hpsi hwidth hle l r (clearControlV6 l, clearControlV6 r)
    refine drop_pair hpsi hwidth hle l r _ _ ?_
    rw [weight_clear, weight_clear]
    have := weight_pos_of_role l (by rw [hPA.1]; decide)
    omega
  rw [if_neg hPA] at hne ⊢
  by_cases hMC : MoveCommitGuard l.carrier r.carrier
  · rw [if_pos hMC]
    show FirstOut hpsi hwidth hle l r (clearControlV6 l,
      withCarrierClearTicketV6 r (setControl (repairResponder hpsi l.carrier r.carrier) .predecessorArmed false))
    refine drop_pair hpsi hwidth hle l r _ _ ?_
    rw [weight_clear]
    have hw3 : controllerWeightV6 (withCarrierClearTicketV6 r
        (setControl (repairResponder hpsi l.carrier r.carrier) .predecessorArmed false)) = 3 := rfl
    rw [hw3]
    have h1 := weight_settledPred l hMC.1 hMC.2.1
    have h2 := weight_pendingPred_ge r hMC.2.2.1 hMC.2.2.2.1
    omega
  rw [if_neg hMC] at hne ⊢
  by_cases hMS : MoveStopGuardV3 hpsi l.carrier r.carrier
  · rw [if_pos hMS]
    have h1 := weight_settledPred l hMS.1 hMS.2.1
    have h2 := weight_RFHG_ge r hMS.2.2.1
    by_cases hjl : r.carrier.splice.base.core.core.leader = true
    · have hmw : moveStopWriteV6 l r = (clearControlV6 l, clearControlV6 r) := by
        unfold moveStopWriteV6; rw [if_pos hjl]
      rw [hmw]
      refine drop_pair hpsi hwidth hle l r _ _ ?_
      rw [weight_clear, weight_clear]
      omega
    · have hmw : moveStopWriteV6 l r = (clearControlV6 l, clearTicketV6 r) := by
        unfold moveStopWriteV6; rw [if_neg hjl]
      rw [hmw]
      refine drop_pair hpsi hwidth hle l r _ _ ?_
      rw [weight_clear, weight_RFHG_clearTicket r hMS.2.2.1]
      omega
  rw [if_neg hMS] at hne ⊢
  by_cases hSK : MoveSeekGuardV3 hpsi l.carrier r.carrier
  · rw [if_pos hSK] at hne ⊢
    cases ht : r.acquireTicket
    · show FirstOut hpsi hwidth hle l r (l, setTicketV6 r true)
      refine drop_right hpsi hwidth hle l r _ ?_
      rw [weight_RFHG_setTicket r hSK.2.2.1, weight_RFHG_unticketed r hSK.2.2.1 ht]
      decide
    · exfalso; apply hne
      show (l, setTicketV6 r true) = (l, r)
      rw [setTicket_self r ht]
  rw [if_neg hSK] at hne ⊢
  by_cases hSKH : MoveSeekHoldGuardV3 l.carrier r.carrier
  · rw [if_pos hSKH] at hne; exact (hne rfl).elim
  rw [if_neg hSKH] at hne ⊢
  by_cases hPOA : PendingOwnerAbortGuardV3 l.carrier r.carrier
  · rw [if_pos hPOA] at hne
    exfalso; apply hne
    show (l, clearTicketV6 r) = (l, r)
    rw [clearTicket_self r (ticket_false_of_shape r htr (by rw [hPOA.1]; decide) (by rw [hPOA.1]; decide))]
  rw [if_neg hPOA] at hne ⊢
  by_cases hPP : role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = true
  · rw [if_pos hPP] at hne; exact (hne rfl).elim
  rw [if_neg hPP] at hne ⊢
  by_cases hMAL : MoveAcquireLegacyGuardV6 l r
  · exact absurd ⟨hMAL.1.2.2.2, by rw [hMAL.1.1]; decide⟩ hD1
  rw [if_neg hMAL] at hne ⊢
  by_cases hMAA : MoveAcquireAbortGuardV3 l.carrier r.carrier
  · rw [if_pos hMAA] at hne
    exfalso; apply hne
    show (clearTicketV6 l, r) = (l, r)
    rw [clearTicket_self l (ticket_false_of_shape l htl (by rw [hMAA.1]; decide) (by rw [hMAA.1]; decide))]
  rw [if_neg hMAA] at hne ⊢
  by_cases hORF : OrphanReservedFrontGuardV3 l.carrier r.carrier
  · exact absurd hORF hD1
  rw [if_neg hORF] at hne ⊢
  by_cases hRFH : ReservedFrontHoldGuard l.carrier
  · rw [if_pos hRFH] at hne; exact (hne rfl).elim
  rw [if_neg hRFH] at hne ⊢
  by_cases hVR : VictimRightScrubGuardV6 r
  · rw [if_pos hVR]
    show FirstOut hpsi hwidth hle l r (l, clearControlV6 r)
    exact drop_right hpsi hwidth hle l r _ (by rw [weight_clear]; exact weight_pos_of_role r (by rw [hVR.1]; decide))
  rw [if_neg hVR] at hne ⊢
  by_cases hVL : VictimLeftScrubGuardV6 l
  · rw [if_pos hVL]
    show FirstOut hpsi hwidth hle l r (clearControlV6 l, r)
    exact drop_left hpsi hwidth hle l r _ (by rw [weight_clear]; exact weight_pos_of_role l (by rw [hVL.1]; decide))
  rw [if_neg hVL] at hne ⊢
  by_cases hFR : FrontRightScrubGuardV6 r
  · rw [if_pos hFR]
    show FirstOut hpsi hwidth hle l r (l, clearControlV6 r)
    exact drop_right hpsi hwidth hle l r _ (by rw [weight_clear]; exact weight_pos_of_role r (by rw [hFR.1]; decide))
  rw [if_neg hFR] at hne ⊢
  by_cases hML : MalformedLeftPendingGuardV6 l
  · rw [if_pos hML]
    show FirstOut hpsi hwidth hle l r (clearPendingV6 l, r)
    refine drop_left hpsi hwidth hle l r _ ?_
    have hnone : role l.carrier = .none :=
      B9SpliceV10cWholeStepLeaderless.role_none_of_not _ hML.2.1 hML.2.2.1 hML.2.2.2
    rw [B9SpliceV10cRowCertFreeLeft.clearPending_eq_clearControl l hnone, weight_clear]
    exact weight_pos_of_pending l hML.1
  rw [if_neg hML] at hne ⊢
  by_cases hMR : MalformedRightPendingGuardV6 r
  · rw [if_pos hMR]
    show FirstOut hpsi hwidth hle l r (l, clearPendingV6 r)
    refine drop_right hpsi hwidth hle l r _ ?_
    have hnone : role r.carrier = .none :=
      B9SpliceV10cWholeStepLeaderless.role_none_of_not _ hMR.2.1 hMR.2.2.1 hMR.2.2.2
    rw [B9SpliceV10cRowCertFreeLeft.clearPending_eq_clearControl r hnone, weight_clear]
    exact weight_pos_of_pending r hMR.1
  rw [if_neg hMR] at hne ⊢
  by_cases hpl : role l.carrier = .predecessorArmed
  · rw [if_pos hpl]
    show FirstOut hpsi hwidth hle l r (clearControlV6 l, r)
    exact drop_left hpsi hwidth hle l r _ (by rw [weight_clear]; exact weight_pos_of_role l (by rw [hpl]; decide))
  rw [if_neg hpl] at hne ⊢
  by_cases hlf : role l.carrier = .front
  · rw [if_pos hlf] at hne; exact (hne rfl).elim
  rw [if_neg hlf] at hne ⊢
  by_cases hmk : MarkedHoldGuardV6 l r
  · rw [if_pos hmk] at hne; exact (hne rfl).elim
  rw [if_neg hmk]
  left
  exact phys_ordinary hpsi hwidth hle l r

theorem nonstutter_classified (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (htl : TicketShapeV7 l) (htr : TicketShapeV7 r)
    (hdel : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice)
    (hq : rowV10dg hpsi hwidth hle l r ≠ (l, r)) :
    FirstOut hpsi hwidth hle l r (rowV10dg hpsi hwidth hle l r) := by
  classical
  have hd := rowV10dg.eq_1 hpsi hwidth hle l r
  by_cases hD1 : OrphanReservedFrontGuardV3 l.carrier r.carrier
  · rw [hd, if_pos hD1]
    exact drop_right hpsi hwidth hle l r _ (by rw [weight_fence]; have := weight_RFHG_ge r hD1.1; omega)
  rw [if_neg hD1] at hd
  by_cases hD2 : OrphanVictimGuard l r
  · rw [hd, if_pos hD2]
    exact drop_right hpsi hwidth hle l r _ (by rw [weight_clear]; exact weight_pos_of_role r (by rw [hD2.1]; decide))
  rw [if_neg hD2] at hd
  by_cases hD3 : OwnedPendingVictimGuard l r
  · rw [hd, if_pos hD3]
    refine drop_pair hpsi hwidth hle l r _ _ ?_
    rw [weight_fence, weight_fence]
    have h1 := weight_settledPred l hD3.1 hD3.2.1
    have h2 := weight_pendingVictim_ge r hD3.2.2.1 hD3.2.2.2
    omega
  rw [if_neg hD3] at hd
  by_cases hD4 : OwnerlessPendingPredGuard l r
  · rw [hd, if_pos hD4]
    by_cases hlq : l.carrier.repairPending = true ∨ l.acquireTicket = true
    · refine drop_pair hpsi hwidth hle l r _ _ ?_
      rw [weight_fence, weight_settle]
      have h1 := weight_none_pos l hD4.1 hlq
      have h2 := weight_pendingPred_ge r hD4.2.1 hD4.2.2
      omega
    · right; right; right
      refine ⟨hdel, Or.inr (Or.inl ⟨hD4.1, ?_, ?_, hD4.2.1, hD4.2.2⟩)⟩
      · cases hp : l.carrier.repairPending
        · rfl
        · exact absurd (Or.inl hp) hlq
      · cases ht : l.acquireTicket
        · rfl
        · exact absurd (Or.inr ht) hlq
  rw [if_neg hD4] at hd
  rw [hd]
  rw [hd] at hq
  have hc := rowV10c.eq_1 hpsi hwidth hle l r
  by_cases hZR : ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r
  · rw [if_pos hZR] at hc; exact absurd hc hq
  rw [if_neg hZR] at hc
  rw [hc]
  rw [hc] at hq
  have hb := rowV10b.eq_1 hpsi hwidth hle l r
  by_cases hHO : HostFenceAdvanceGuardV10b hpsi l r
  · right; right; right; exact ⟨hdel, Or.inl hHO⟩
  rw [if_neg hHO] at hb
  rw [hb]
  rw [hb] at hq
  have h9 := rowV9.eq_1 hpsi hwidth hle l r
  by_cases hBF : HostFenceBusyFrontGuardV9 hpsi l r
  · exact absurd ⟨hBF.2.2, by rw [hBF.1.1]; decide⟩ hD1
  rw [if_neg hBF] at h9
  rw [h9]
  rw [h9] at hq
  have h8 := rowV8.eq_1 hpsi hwidth hle l r
  by_cases hSP8 : RightStalePredecessorHoldGuardV8 l r
  · rw [if_pos hSP8] at h8; exact absurd h8 hq
  rw [if_neg hSP8] at h8
  rw [h8]
  rw [h8] at hq
  exact rowV7_classified hpsi hwidth hle l r htl htr hdel hD1 hHO hq

theorem first_row_classified (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (htl : TicketShapeV7 l) (htr : TicketShapeV7 r) :
    FirstOut hpsi hwidth hle l r (rowV10j hpsi hwidth hle l r) := by
  classical
  rw [rowV10j.eq_1]
  by_cases hd : LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice
  · rw [if_pos hd]
    by_cases hrf : ReservedFrontHoldGuard l.carrier
    · rw [if_pos hrf, holdRepairV10j.eq_1]
      by_cases h1 : ReservedFrontHoldGuard r.carrier
      · rw [if_pos h1]
        exact drop_right hpsi hwidth hle l r _ (by rw [weight_fence]; have := weight_RFHG_ge r h1; omega)
      rw [if_neg h1]
      by_cases h2 : role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = true
      · rw [if_pos h2]
        exact drop_right hpsi hwidth hle l r _ (by rw [weight_settle]; have := weight_pendingPred_ge r h2.1 h2.2; omega)
      rw [if_neg h2]
      by_cases h3 : role r.carrier = .victimArmed ∧ r.carrier.repairPending = true
      · rw [if_pos h3]
        exact drop_right hpsi hwidth hle l r _ (by rw [weight_clear]; exact weight_pos_of_role r (by rw [h3.1]; decide))
      rw [if_neg h3]
      by_cases h4 : VictimRightScrubGuardV6 r ∨ FrontRightScrubGuardV6 r ∨ MalformedRightPendingGuardV6 r
      · rw [if_pos h4]
        refine drop_right hpsi hwidth hle l r _ ?_
        rw [weight_clear]
        rcases h4 with hv | hf | hm
        · exact weight_pos_of_role r (by rw [hv.1]; decide)
        · exact weight_pos_of_role r (by rw [hf.1]; decide)
        · exact weight_pos_of_pending r hm.1
      rw [if_neg h4]
      right; right; left; right; right
      refine ⟨hrf, ?_⟩
      cases hrole : role r.carrier with
      | none =>
          left; refine ⟨rfl, ?_⟩
          cases hp : r.carrier.repairPending
          · rfl
          · exact absurd (Or.inr (Or.inr ⟨hp, by rw [hrole]; decide, by rw [hrole]; decide, by rw [hrole]; decide⟩)) h4
      | predecessorArmed =>
          right; refine ⟨rfl, ?_⟩
          cases hp : r.carrier.repairPending
          · rfl
          · exact absurd ⟨hrole, hp⟩ h2
      | front =>
          exfalso
          cases hp : r.carrier.repairPending
          · exact h4 (Or.inr (Or.inl ⟨hrole, hp⟩))
          · exact h1 ⟨hrole, hp⟩
      | victimArmed =>
          exfalso
          cases hp : r.carrier.repairPending
          · exact h4 (Or.inl ⟨hrole, hp⟩)
          · exact h3 ⟨hrole, hp⟩
    · rw [if_neg hrf]
      left
      exact phys_delete hpsi hwidth hle l r
  · rw [if_neg hd]
    by_cases hq : rowV10dg hpsi hwidth hle l r = (l, r)
    · exact stutter_classified hpsi hwidth hle l r hq
    · rw [rowV10g_of_change hpsi hwidth hle l r hq]
      exact nonstutter_classified hpsi hwidth hle l r htl htr hd hq

end B9SpliceV10jFirstRow
