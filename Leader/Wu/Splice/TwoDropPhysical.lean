import Leader.Wu.Splice.ComposedEvents
import Leader.Wu.Splice.PhysicalHoldTransparency
import Leader.Wu.Splice.PhysicalHoldFirstService
import Leader.Wu.Splice.PhysicalHoldHandoffFollowUp
import Leader.Wu.Splice.PhysicalHoldRowPotential
import Leader.Wu.Splice.PhysicalHoldPairWeight

set_option autoImplicit false
set_option Elab.async false

namespace B9SpliceTwoDropPhysical

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10d B9SpliceTableV10e
  B9SpliceV10eTransparency B9SpliceV10cChainShapes B9SpliceV10cLeaderlessExclusion
  B9SpliceV10ePhysicalHoldNoBirth B9SpliceV10eRowPotential B9SpliceV10eHandoffFollowUp
  B9SpliceV10eClassification B9SpliceComposedEvents

variable {n psi width kappa tau : Nat}

theorem two_consecutive_drop_shapeClear_next_physical
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (C0 C1 C2 : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (h01 : C1 = stepV10e hpsi hwidth hle ring C0 e)
    (h12 : C2 = stepV10e hpsi hwidth hle ring C1 e)
    (hlead0 : ∀ i, (C0 i).carrier.splice.base.core.core.leader = false)
    (hlead1 : ∀ i, (C1 i).carrier.splice.base.core.core.leader = false)
    (hlead2 : ∀ i, (C2 i).carrier.splice.base.core.core.leader = false)
    (hS0 : SpliceSafeV7 hpsi ring C0)
    (hS1 : SpliceSafeV7 hpsi ring C1)
    (hS2 : SpliceSafeV7 hpsi ring C2)
    (hclear0 : ShapeClear C0)
    (hclear1 : ShapeClear C1)
    (hclear2 : ShapeClear C2)
    (hnphys0 : ¬ PhysicalServiceAt hpsi hwidth hle ring C0 C1 e)
    (hnphys1 : ¬ PhysicalServiceAt hpsi hwidth hle ring C1 C2 e)
    (hdrop0 : controllerPotentialV6 C1 < controllerPotentialV6 C0)
    (hdrop1 : controllerPotentialV6 C2 < controllerPotentialV6 C1) :
    PhysicalServiceAt hpsi hwidth hle ring C2
      (stepV10e hpsi hwidth hle ring C2 e) e := by
  let Clear : R1AgentStateV6 psi kappa tau → Prop := fun u =>
    role u.carrier = .none ∧
      u.carrier.repairPending = false ∧
      u.acquireTicket = false

  have ticket_false_of_not_shapes :
      ∀ (D : R1ConfigV6 n psi kappa tau) (i : Fin n),
        SpliceSafeV7 hpsi ring D →
        (¬ ReservedFrontHoldGuard (D i).carrier) →
        (¬ HostFenceShapeV7 (D i)) →
        (D i).acquireTicket = false := by
    intro D i hS hrf hhf
    cases ht : (D i).acquireTicket with
    | false => rfl
    | true =>
        have hs := hS.2.1 i ht
        rcases hs with hs | hs
        · exact (hrf hs).elim
        · exact (hhf hs).elim

  have pair_drop_of_step :
      ∀ (D E : R1ConfigV6 n psi kappa tau),
        E = stepV10e hpsi hwidth hle ring D e →
        controllerPotentialV6 E < controllerPotentialV6 D →
        pairPotentialV6 (E e) (E (ring.rightNeighbor e)) <
          pairPotentialV6 (D e) (D (ring.rightNeighbor e)) := by
    intro D E hDE hdrop
    have hother : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → E i = D i := by
      intro i hie hij
      rw [hDE]
      simp [stepV10e, hne, hie, hij]
    have hid := B9SpliceV10ePairWeight.potential_pair_identity ring D E e hne hother
    unfold B9SpliceV10ePairWeight.pairWeight at hid
    unfold pairPotentialV6
    omega

  have handoff_not_pair_drop :
      ∀ (D : R1ConfigV6 n psi kappa tau),
        HostFenceAdvanceGuardV10b hpsi (D e) (D (ring.rightNeighbor e)) →
        ¬ pairPotentialV6
            ((stepV10e hpsi hwidth hle ring D e) e)
            ((stepV10e hpsi hwidth hle ring D e) (ring.rightNeighbor e)) <
          pairPotentialV6 (D e) (D (ring.rightNeighbor e)) := by
    intro D hG hlt
    have hfence : HostFenceShapeV7 (D e) := hG.1
    have hbar : LocalPreparedBarrier hpsi
        (D e).carrier (D (ring.rightNeighbor e)).carrier := hG.2.1
    have htgt : HostFenceTargetClearV7 (D (ring.rightNeighbor e)) := hG.2.2
    have hnf : ¬ OrphanReservedFrontGuardV3
        (D e).carrier (D (ring.rightNeighbor e)).carrier := by
      intro h
      have hx := h.1.1
      rw [htgt.1] at hx
      cases hx
    have hov : ¬ OrphanVictimGuard (D e) (D (ring.rightNeighbor e)) := by
      intro h
      have hx := h.1
      rw [htgt.1] at hx
      cases hx
    have how : ¬ OwnedPendingVictimGuard (D e) (D (ring.rightNeighbor e)) := by
      intro h
      have hx := h.2.2.1
      rw [htgt.1] at hx
      cases hx
    have hop : ¬ OwnerlessPendingPredGuard (D e) (D (ring.rightNeighbor e)) := by
      intro h
      have hx := h.2.1
      rw [htgt.1] at hx
      cases hx
    have hz : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle
        (D e) (D (ring.rightNeighbor e)) := by
      apply notZeroRefresh_of_left_role
      rw [rowV10b_of_handoff hpsi hwidth hle _ _ hG, hfence.1]
      intro hx
      have hx' : SpliceRole.predecessorArmed = SpliceRole.none := hx
      cases hx'
    have hrow : rowV10d hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) =
        hostFenceHandoffWriteV10b (D e) (D (ring.rightNeighbor e)) := by
      rw [B9SpliceV10eHandoffFollowUp.rowV10d_of_none
            hpsi hwidth hle _ _ hnf hov how hop,
          rowV10c_of_notZero hpsi hwidth hle _ _ hz,
          rowV10b_of_handoff hpsi hwidth hle _ _ hG]
    have hchange : rowV10d hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) ≠
        (D e, D (ring.rightNeighbor e)) := by
      intro hx
      rw [hrow] at hx
      have hy := congrArg
        (fun z : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau =>
          role z.1.carrier) hx
      simp only [hostFenceHandoffWriteV10b] at hy
      rw [hfence.1] at hy
      cases hy
    have hstep : stepV10e hpsi hwidth hle ring D e = fun i =>
        if i = e then setControlV6 (D e) .predecessorArmed false
        else if i = ring.rightNeighbor e then
          setControlV6 (D (ring.rightNeighbor e)) .front true
        else D i := by
      rw [stepV10e_of_change hpsi hwidth hle ring D e hne hchange]
      funext i
      simp only [stepV10d, hne, if_false, hrow, hostFenceHandoffWriteV10b]
    unfold pairPotentialV6 at hlt
    rw [hstep] at hlt
    simp only [if_pos rfl, if_neg hne, if_true] at hlt
    rw [weight_setControl_pred_settled, weight_hostFence _ hfence] at hlt
    have hw8 : controllerWeightV6
        (setControlV6 (D (ring.rightNeighbor e)) .front true) = 8 := rfl
    rw [hw8] at hlt
    have hwR : controllerWeightV6 (D (ring.rightNeighbor e)) ≤ 1 := by
      unfold controllerWeightV6
      rw [htgt.1, htgt.2]
      cases (D (ring.rightNeighbor e)).acquireTicket <;> decide
    omega

  have seek_post_physical :
      ∀ (D : R1ConfigV6 n psi kappa tau),
        role (D e).carrier = .predecessorArmed →
        (D e).carrier.repairPending = false →
        (D e).acquireTicket = false →
        ReservedFrontHoldGuard (D (ring.rightNeighbor e)).carrier →
        (D (ring.rightNeighbor e)).acquireTicket = true →
        LocalPreparedBarrier hpsi
          (D e).carrier (D (ring.rightNeighbor e)).carrier →
        (D e).carrier.splice.base.core.core.leader = false →
        (D (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = false →
        PhysicalServiceAt hpsi hwidth hle ring D
          (stepV10e hpsi hwidth hle ring D e) e := by
    intro D hl hlp hlt hr hrt hbar hlLead hrLead
    have hrowb := rowV10b_of_moveSeek hpsi hwidth hle
      (D e) (D (ring.rightNeighbor e)) hl hlp hlt hr hbar hlLead hrLead
    have hnf : ¬ OrphanReservedFrontGuardV3
        (D e).carrier (D (ring.rightNeighbor e)).carrier :=
      fun h => h.2 hl
    have hov : ¬ OrphanVictimGuard (D e) (D (ring.rightNeighbor e)) := by
      intro h
      have hx := h.1
      rw [hr.1] at hx
      cases hx
    have how : ¬ OwnedPendingVictimGuard (D e) (D (ring.rightNeighbor e)) := by
      intro h
      have hx := h.2.2.1
      rw [hr.1] at hx
      cases hx
    have hop : ¬ OwnerlessPendingPredGuard (D e) (D (ring.rightNeighbor e)) := by
      intro h
      have hx := h.2.1
      rw [hr.1] at hx
      cases hx
    have hz : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle
        (D e) (D (ring.rightNeighbor e)) := by
      apply notZeroRefresh_of_right_ticket hpsi hwidth hle _ _
      · rw [hr.1]
        decide
      · rw [hrowb]
        rfl
    have hsame : setTicketV6 (D (ring.rightNeighbor e)) true =
        D (ring.rightNeighbor e) := by
      have hc := hrt
      cases hj : D (ring.rightNeighbor e) with
      | mk c t =>
          rw [hj] at hc
          simp only at hc
          subst hc
          rfl
    have hrowd : rowV10d hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) =
        (D e, D (ring.rightNeighbor e)) := by
      rw [B9SpliceV10eHandoffFollowUp.rowV10d_of_none
            hpsi hwidth hle _ _ hnf hov how hop,
          rowV10c_of_notZero hpsi hwidth hle _ _ hz,
          hrowb]
      unfold moveSeekWriteV6
      rw [hsame]
    have hvr : ¬ VictimRightScrubGuardV6 (D (ring.rightNeighbor e)) := by
      intro h
      have hx := h.1
      rw [hr.1] at hx
      cases hx
    have hfr : ¬ FrontRightScrubGuardV6 (D (ring.rightNeighbor e)) := by
      intro h
      have hx := h.2
      rw [hr.2] at hx
      cases hx
    have hmr : ¬ MalformedRightPendingGuardV6 (D (ring.rightNeighbor e)) := by
      intro h
      exact h.2.2.1 hr.1
    have hpr : ¬ role (D (ring.rightNeighbor e)).carrier = .predecessorArmed := by
      rw [hr.1]
      decide
    rw [stepV10e_of_physical hpsi hwidth hle ring D e hne hrowd hvr hfr hmr hpr]
    exact physicalHold_is_physical hpsi hwidth hle ring D e hne

  have physical_of_terminal :
      ∀ (D : R1ConfigV6 n psi kappa tau),
        (∀ i, (D i).carrier.splice.base.core.core.leader = false) →
        SpliceSafeV7 hpsi ring D →
        Clear (D e) →
        (Clear (D (ring.rightNeighbor e)) ∨
          HostFenceShapeV7 (D (ring.rightNeighbor e))) →
        PhysicalServiceAt hpsi hwidth hle ring D
          (stepV10e hpsi hwidth hle ring D e) e := by
    intro D hlead hS hL hR
    change role (D e).carrier = .none ∧
      (D e).carrier.repairPending = false ∧
      (D e).acquireTicket = false at hL
    rcases hR with hR | hR
    · change role (D (ring.rightNeighbor e)).carrier = .none ∧
        (D (ring.rightNeighbor e)).carrier.repairPending = false ∧
        (D (ring.rightNeighbor e)).acquireTicket = false at hR
      rcases first_service_classified hpsi hwidth hle ring D e hne hlead hS with
        hphys | hdrop | hhand | hvp
      · exact hphys
      · have hp := pair_drop_of_step D
          (stepV10e hpsi hwidth hle ring D e) rfl hdrop
        have hwL : controllerWeightV6 (D e) = 0 := by
          unfold controllerWeightV6
          rw [hL.1, hL.2.1, hL.2.2]
        have hwR : controllerWeightV6 (D (ring.rightNeighbor e)) = 0 := by
          unfold controllerWeightV6
          rw [hR.1, hR.2.1, hR.2.2]
        unfold pairPotentialV6 at hp
        rw [hwL, hwR] at hp
        omega
      · have hx := hhand.1.2.2
        rw [hL.2.2] at hx
        cases hx
      · have hx := hvp.1
        rw [hL.1] at hx
        cases hx
    · have hnf : ¬ OrphanReservedFrontGuardV3
          (D e).carrier (D (ring.rightNeighbor e)).carrier := by
        intro h
        have hx := h.1.1
        rw [hR.1] at hx
        cases hx
      have hov : ¬ OrphanVictimGuard (D e) (D (ring.rightNeighbor e)) := by
        intro h
        have hx := h.1
        rw [hR.1] at hx
        cases hx
      have how : ¬ OwnedPendingVictimGuard (D e) (D (ring.rightNeighbor e)) := by
        intro h
        have hx := h.2.2.1
        rw [hR.1] at hx
        cases hx
      have hop : ¬ OwnerlessPendingPredGuard (D e) (D (ring.rightNeighbor e)) := by
        intro h
        have hx := h.2.1
        rw [hR.1] at hx
        cases hx
      have hfL : ¬ HostFenceShapeV7 (D e) := by
        intro h
        have hx := h.2.2
        rw [hL.2.2] at hx
        cases hx
      have hh : ¬ HostFenceAdvanceGuardV10b hpsi
          (D e) (D (ring.rightNeighbor e)) := fun h => hfL h.1
      have hb : ¬ HostFenceBusyFrontGuardV9 hpsi
          (D e) (D (ring.rightNeighbor e)) := fun h => hfL h.1
      have hst : ¬ RightStalePredecessorHoldGuardV8
          (D e) (D (ring.rightNeighbor e)) := by
        intro h
        have hx := h.2.2.2.1
        rw [hR.1] at hx
        cases hx
      have hrowb : rowV10b hpsi hwidth hle
          (D e) (D (ring.rightNeighbor e)) =
          (D e, D (ring.rightNeighbor e)) := by
        unfold rowV10b rowV9 rowV8 rowV7
        rw [if_neg hh, if_neg hb, if_neg hst, if_neg hfL, if_pos hR]
        rfl
      have hrowc : rowV10c hpsi hwidth hle
          (D e) (D (ring.rightNeighbor e)) =
          (D e, D (ring.rightNeighbor e)) := by
        unfold rowV10c
        split
        · rfl
        · exact hrowb
      have hrowd : rowV10d hpsi hwidth hle
          (D e) (D (ring.rightNeighbor e)) =
          (D e, D (ring.rightNeighbor e)) := by
        rw [B9SpliceV10eHandoffFollowUp.rowV10d_of_none
          hpsi hwidth hle _ _ hnf hov how hop]
        exact hrowc
      have hvr : ¬ VictimRightScrubGuardV6 (D (ring.rightNeighbor e)) := by
        intro h
        have hx := h.1
        rw [hR.1] at hx
        cases hx
      have hfr : ¬ FrontRightScrubGuardV6 (D (ring.rightNeighbor e)) := by
        intro h
        have hx := h.1
        rw [hR.1] at hx
        cases hx
      have hmr : ¬ MalformedRightPendingGuardV6 (D (ring.rightNeighbor e)) := by
        intro h
        have hx := h.1
        rw [hR.2.1] at hx
        cases hx
      have hpr : ¬ role (D (ring.rightNeighbor e)).carrier = .predecessorArmed := by
        rw [hR.1]
        decide
      rw [stepV10e_of_physical hpsi hwidth hle ring D e hne hrowd hvr hfr hmr hpr]
      exact physicalHold_is_physical hpsi hwidth hle ring D e hne

  have hpair01 := pair_drop_of_step C0 C1 h01 hdrop0
  have hpair12 := pair_drop_of_step C1 C2 h12 hdrop1

  have hnphys1' : ¬ PhysicalServiceAt hpsi hwidth hle ring C1
      (stepV10e hpsi hwidth hle ring C1 e) e := by
    intro h
    apply hnphys1
    rw [h12]
    exact h

  have hpost1 :
      Clear (C1 e) ∨
      Clear (C1 (ring.rightNeighbor e)) ∨
      HostFenceShapeV7 (C1 (ring.rightNeighbor e)) := by
    rcases Classical.em
        (rowV10d hpsi hwidth hle (C0 e) (C0 (ring.rightNeighbor e)) =
          (C0 e, C0 (ring.rightNeighbor e))) with h | h
    · by_cases h1 : VictimRightScrubGuardV6 (C0 (ring.rightNeighbor e))
      · exact (hclear0.1 _ h1.1).elim
      by_cases h2 : FrontRightScrubGuardV6 (C0 (ring.rightNeighbor e))
      · right; left
        have hj : C1 (ring.rightNeighbor e) =
            clearControlV6 (C0 (ring.rightNeighbor e)) := by
          rw [h01, stepV10e_of_frontScrub hpsi hwidth hle ring C0 e hne h h1 h2]
          simp [orphanVictimClearAt]
        simp [Clear, hj]
      by_cases h3 : MalformedRightPendingGuardV6 (C0 (ring.rightNeighbor e))
      · right; left
        have hj : C1 (ring.rightNeighbor e) =
            clearControlV6 (C0 (ring.rightNeighbor e)) := by
          rw [h01, stepV10e_of_malformedScrub hpsi hwidth hle ring C0 e hne h h1 h2 h3]
          simp [orphanVictimClearAt]
        simp [Clear, hj]
      by_cases h4 : role (C0 (ring.rightNeighbor e)).carrier = .predecessorArmed
      · have h5 := hclear0.2 (ring.rightNeighbor e) h4
        exfalso
        apply hnphys0
        rw [h01, stepV10e_of_settledPredFence hpsi hwidth hle ring C0 e hne h h1 h2 h3 h4 h5]
        exact physicalFence_is_physical hpsi hwidth hle ring C0 e hne
      · exfalso
        apply hnphys0
        rw [h01, stepV10e_of_physical hpsi hwidth hle ring C0 e hne h h1 h2 h3 h4]
        exact physicalHold_is_physical hpsi hwidth hle ring C0 e hne
    · by_cases g1 : OrphanReservedFrontGuardV3
          (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier
      · right; right
        have hC : C1 = orphanToFenceAt ring C0 e := by
          rw [h01, stepV10e_of_change hpsi hwidth hle ring C0 e hne h,
            stepV10d_of_orphanFront hpsi hwidth hle ring C0 e hne g1]
        rw [hC, at_j]
        exact fence_shape _
      by_cases g2 : OrphanVictimGuard (C0 e) (C0 (ring.rightNeighbor e))
      · exact (hclear0.1 _ g2.1).elim
      by_cases g3 : OwnedPendingVictimGuard (C0 e) (C0 (ring.rightNeighbor e))
      · exact (hclear0.1 _ g3.2.2.1).elim
      by_cases g4 : OwnerlessPendingPredGuard (C0 e) (C0 (ring.rightNeighbor e))
      · have hx := hclear0.2 (ring.rightNeighbor e) g4.2.1
        have hbad : (false : Bool) = true := hx.symm.trans g4.2.2
        cases hbad
      have hrowd := B9SpliceV10eHandoffFollowUp.rowV10d_of_none
        hpsi hwidth hle (C0 e) (C0 (ring.rightNeighbor e)) g1 g2 g3 g4
      by_cases hz : ZeroRefreshOnlyGuardV10c hpsi hwidth hle
          (C0 e) (C0 (ring.rightNeighbor e))
      · exfalso
        apply h
        rw [hrowd]
        simp [rowV10c, hz]
      have hrowc := rowV10c_of_notZero hpsi hwidth hle
        (C0 e) (C0 (ring.rightNeighbor e)) hz
      by_cases hh : HostFenceAdvanceGuardV10b hpsi
          (C0 e) (C0 (ring.rightNeighbor e))
      · have hp := hpair01
        rw [h01] at hp
        exact (handoff_not_pair_drop C0 hh hp).elim
      by_cases hb : HostFenceBusyFrontGuardV9 hpsi
          (C0 e) (C0 (ring.rightNeighbor e))
      · exfalso
        apply g1
        refine ⟨hb.2.2, ?_⟩
        have hx := hb.1.1
        rw [hx]
        decide
      by_cases hst : RightStalePredecessorHoldGuardV8
          (C0 e) (C0 (ring.rightNeighbor e))
      · exfalso
        apply h
        rw [hrowd, hrowc]
        simp [rowV10b, hh, rowV9, hb, rowV8, hst]
      have hrow7 : rowV10d hpsi hwidth hle
          (C0 e) (C0 (ring.rightNeighbor e)) =
          rowV7 hpsi hwidth hle (C0 e) (C0 (ring.rightNeighbor e)) := by
        rw [hrowd, hrowc]
        simp only [rowV10b, hh, if_false, rowV9, hb, rowV8, hst]
      have hC1V7 : C1 = stepV7 hpsi hwidth hle ring C0 e := by
        rw [h01, stepV10e_of_change hpsi hwidth hle ring C0 e hne h,
          stepV10d_of_none hpsi hwidth hle ring C0 e hne g1 g2 g3 g4,
          stepV10c_eq_stepV10b hpsi hwidth hle ring C0 e hne hz,
          stepV10b_eq_stepV9 hpsi hwidth hle ring C0 e hne hh,
          stepV9_eq_stepV8 hpsi hwidth hle ring C0 e hne hb,
          stepV8_eq_stepV7 hpsi hwidth hle ring C0 e hne hst]
      have hid : rowV7 hpsi hwidth hle (C0 e) (C0 (ring.rightNeighbor e)) =
          (C0 e, C0 (ring.rightNeighbor e)) → False := by
        intro hi
        apply h
        rw [hrow7]
        exact hi
      by_cases hfL : HostFenceShapeV7 (C0 e)
      · by_cases hbar : LocalPreparedBarrier hpsi
            (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier
        · by_cases htg : HostFenceTargetClearV7 (C0 (ring.rightNeighbor e))
          · exact (hh ⟨hfL, hbar, htg⟩).elim
          · exfalso
            apply hid
            unfold rowV7
            rw [if_pos hfL, if_pos hbar, if_neg htg]
            rfl
        · left
          have hrowS : rowV7 hpsi hwidth hle
              (C0 e) (C0 (ring.rightNeighbor e)) =
              (clearTicketV6 (C0 e), C0 (ring.rightNeighbor e)) := by
            unfold rowV7
            rw [if_pos hfL, if_neg hbar]
            rfl
          have he : C1 e = clearTicketV6 (C0 e) := by
            rw [hC1V7, stepV7_of_left hpsi hwidth hle ring C0 e hne clearTicketV6 hrowS]
            simp
          simp [Clear, he, hfL.1, hfL.2.1]
      by_cases hfR : HostFenceShapeV7 (C0 (ring.rightNeighbor e))
      · exfalso
        apply hid
        unfold rowV7
        rw [if_neg hfL, if_pos hfR]
        rfl
      by_cases hmaf : MoveAcquireFrontGuardV6 hpsi
          (C0 e) (C0 (ring.rightNeighbor e))
      · have hrowM : rowV7 hpsi hwidth hle
            (C0 e) (C0 (ring.rightNeighbor e)) =
            (setControlV6 (C0 e) .predecessorArmed true,
              C0 (ring.rightNeighbor e)) := by
          unfold rowV7
          rw [if_neg hfL, if_neg hfR, if_pos hmaf]
          rfl
        have he : C1 e = setControlV6 (C0 e) .predecessorArmed true := by
          rw [hC1V7,
            stepV7_of_left' hpsi hwidth hle ring C0 e hne
              (fun u => setControlV6 u .predecessorArmed true) hrowM]
          simp
        have hr1 : role (C1 e).carrier = .predecessorArmed := by
          rw [he]
          rfl
        have hp0 := hclear1.2 e hr1
        have hp1 : (C1 e).carrier.repairPending = true := by
          rw [he]
          rfl
        have hbad : (false : Bool) = true := hp0.symm.trans hp1
        cases hbad
      have harmA := armA_needs_leader hpsi hwidth hle
        (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier (hlead0 e)
      have harmB := armB_needs_leader
        (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier
        (hlead0 (ring.rightNeighbor e))
      have hdel := delete_needs_leader hpsi hwidth hle
        (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier (hlead0 e)
      have hph := pendingHold_needs_leader hpsi hwidth hle
        (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier (hlead0 e)
      have hpa := pendingAbort_needs_leader hpsi hwidth hle
        (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier (hlead0 e)
      have hpre : rowV7 hpsi hwidth hle (C0 e) (C0 (ring.rightNeighbor e)) =
          (if MoveCommitGuard (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier then
            moveCommitWriteV6 hpsi (C0 e) (C0 (ring.rightNeighbor e))
          else if MoveStopGuardV3 hpsi (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier then
            moveStopWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if MoveSeekGuardV3 hpsi (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier then
            moveSeekWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if MoveSeekHoldGuardV3 (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier then
            moveSeekHoldWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if PendingOwnerAbortGuardV3 (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier then
            pendingOwnerAbortWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if role (C0 e).carrier = .predecessorArmed ∧ (C0 e).carrier.repairPending = true then
            pendingOwnerHoldWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if MoveAcquireLegacyGuardV6 (C0 e) (C0 (ring.rightNeighbor e)) then
            moveAcquireLegacyWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if MoveAcquireAbortGuardV3 (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier then
            moveAcquireAbortWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if OrphanReservedFrontGuardV3 (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier then
            orphanReservedFrontWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if ReservedFrontHoldGuard (C0 e).carrier then
            reservedFrontHoldWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if VictimRightScrubGuardV6 (C0 (ring.rightNeighbor e)) then
            victimRightScrubWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if VictimLeftScrubGuardV6 (C0 e) then
            victimLeftScrubWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if FrontRightScrubGuardV6 (C0 (ring.rightNeighbor e)) then
            frontRightScrubWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if MalformedLeftPendingGuardV6 (C0 e) then
            malformedLeftPendingWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if MalformedRightPendingGuardV6 (C0 (ring.rightNeighbor e)) then
            malformedRightPendingWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if role (C0 e).carrier = .predecessorArmed then
            predecessorLeftScrubWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if role (C0 e).carrier = .front then
            leftFrontHoldWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else if MarkedHoldGuardV6 (C0 e) (C0 (ring.rightNeighbor e)) then
            markedHoldWriteV6 (C0 e) (C0 (ring.rightNeighbor e))
          else ordinaryHostWriteV7 hpsi hwidth hle
            (C0 e) (C0 (ring.rightNeighbor e))) := by
        unfold rowV7
        rw [if_neg hfL, if_neg hfR, if_neg hmaf, if_neg harmA,
          if_neg harmB, if_neg hdel, if_neg hph, if_neg hpa]
      by_cases hmc : MoveCommitGuard (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier
      · have hp := hclear0.2 (ring.rightNeighbor e) hmc.2.2.1
        have hbad : (false : Bool) = true := hp.symm.trans hmc.2.2.2.1
        cases hbad
      rw [if_neg hmc] at hpre
      by_cases hms : MoveStopGuardV3 hpsi (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier
      · left
        rw [if_pos hms] at hpre
        have hw : moveStopWriteV6 (C0 e) (C0 (ring.rightNeighbor e)) =
            (clearControlV6 (C0 e), clearTicketV6 (C0 (ring.rightNeighbor e))) := by
          simp [moveStopWriteV6, hlead0 (ring.rightNeighbor e)]
        rw [hw] at hpre
        have he : C1 e = clearControlV6 (C0 e) := by
          rw [hC1V7, stepV7_of_row hpsi hwidth hle ring C0 e hne _ hpre]
          simp
        simp [Clear, he]
      rw [if_neg hms] at hpre
      by_cases hsk : MoveSeekGuardV3 hpsi (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier
      · rw [if_pos hsk] at hpre
        cases ht : (C0 (ring.rightNeighbor e)).acquireTicket with
        | false =>
            have he : C1 e = C0 e := by
              rw [hC1V7, stepV7_of_row hpsi hwidth hle ring C0 e hne _ hpre]
              simp [moveSeekWriteV6]
            have hj : C1 (ring.rightNeighbor e) =
                setTicketV6 (C0 (ring.rightNeighbor e)) true := by
              rw [hC1V7, stepV7_of_row hpsi hwidth hle ring C0 e hne _ hpre]
              simp [moveSeekWriteV6, hne]
            have hnotRF : ¬ ReservedFrontHoldGuard (C0 e).carrier := by
              intro hx
              have hy := hx.1
              rw [hsk.1] at hy
              cases hy
            have hnotHF : ¬ HostFenceShapeV7 (C0 e) := by
              intro hx
              have hy := hx.1
              rw [hsk.1] at hy
              cases hy
            have hlt := ticket_false_of_not_shapes C0 e hS0 hnotRF hnotHF
            have hl1 : role (C1 e).carrier = .predecessorArmed := by
              rw [he]
              exact hsk.1
            have hlp1 : (C1 e).carrier.repairPending = false := by
              rw [he]
              exact hsk.2.1
            have hlt1 : (C1 e).acquireTicket = false := by
              rw [he]
              exact hlt
            have hr1 : ReservedFrontHoldGuard (C1 (ring.rightNeighbor e)).carrier := by
              rw [hj]
              exact hsk.2.2.1
            have hrt1 : (C1 (ring.rightNeighbor e)).acquireTicket = true := by
              rw [hj]
              rfl
            have hbar1 : LocalPreparedBarrier hpsi
                (C1 e).carrier (C1 (ring.rightNeighbor e)).carrier := by
              rw [he, hj]
              exact barrier_of_ticket hpsi _ _ true hsk.2.2.2
            have hpnext := seek_post_physical C1 hl1 hlp1 hlt1 hr1 hrt1 hbar1
              (hlead1 e) (hlead1 (ring.rightNeighbor e))
            exact (hnphys1' hpnext).elim
        | true =>
            exfalso
            apply hid
            rw [hpre]
            unfold moveSeekWriteV6
            have hs : setTicketV6 (C0 (ring.rightNeighbor e)) true =
                C0 (ring.rightNeighbor e) := by
              have hc := ht
              cases hj : C0 (ring.rightNeighbor e) with
              | mk c t =>
                  rw [hj] at hc
                  simp only at hc
                  subst hc
                  rfl
            rw [hs]
      rw [if_neg hsk] at hpre
      by_cases hskh : MoveSeekHoldGuardV3
          (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier
      · exact (hclear0.1 _ hskh.2.2.1).elim
      rw [if_neg hskh] at hpre
      by_cases hpoa : PendingOwnerAbortGuardV3
          (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier
      · have hp := hclear0.2 (ring.rightNeighbor e) hpoa.1
        have hbad : (false : Bool) = true := hp.symm.trans hpoa.2.1
        cases hbad
      rw [if_neg hpoa] at hpre
      by_cases hpoh : role (C0 e).carrier = .predecessorArmed ∧
          (C0 e).carrier.repairPending = true
      · have hp := hclear0.2 e hpoh.1
        have hbad : (false : Bool) = true := hp.symm.trans hpoh.2
        cases hbad
      rw [if_neg hpoh] at hpre
      by_cases hmal : MoveAcquireLegacyGuardV6 (C0 e) (C0 (ring.rightNeighbor e))
      · exact (hclear0.1 e hmal.1.1).elim
      rw [if_neg hmal] at hpre
      by_cases hmaa : MoveAcquireAbortGuardV3
          (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier
      · exact (hclear0.1 e hmaa.1).elim
      rw [if_neg hmaa] at hpre
      by_cases horf : OrphanReservedFrontGuardV3
          (C0 e).carrier (C0 (ring.rightNeighbor e)).carrier
      · exact (g1 horf).elim
      rw [if_neg horf] at hpre
      by_cases hrfh : ReservedFrontHoldGuard (C0 e).carrier
      · exfalso
        apply hid
        rw [if_pos hrfh] at hpre
        exact hpre
      rw [if_neg hrfh] at hpre
      by_cases hvr : VictimRightScrubGuardV6 (C0 (ring.rightNeighbor e))
      · exact (hclear0.1 _ hvr.1).elim
      rw [if_neg hvr] at hpre
      by_cases hvl : VictimLeftScrubGuardV6 (C0 e)
      · exact (hclear0.1 e hvl.1).elim
      rw [if_neg hvl] at hpre
      by_cases hfr : FrontRightScrubGuardV6 (C0 (ring.rightNeighbor e))
      · right; left
        rw [if_pos hfr] at hpre
        have hj : C1 (ring.rightNeighbor e) =
            clearControlV6 (C0 (ring.rightNeighbor e)) := by
          rw [hC1V7, stepV7_of_row hpsi hwidth hle ring C0 e hne _ hpre]
          simp [frontRightScrubWriteV6, hne]
        simp [Clear, hj]
      rw [if_neg hfr] at hpre
      by_cases hml : MalformedLeftPendingGuardV6 (C0 e)
      · left
        rw [if_pos hml] at hpre
        have hnone : role (C0 e).carrier = .none :=
          B9SpliceV10cWholeStepLeaderless.role_none_of_not _
            hml.2.1 hml.2.2.1 hml.2.2.2
        have hw : malformedLeftPendingWriteV6 (C0 e) (C0 (ring.rightNeighbor e)) =
            (clearControlV6 (C0 e), C0 (ring.rightNeighbor e)) := by
          unfold malformedLeftPendingWriteV6
          rw [B9SpliceV10cRowCertFreeLeft.clearPending_eq_clearControl (C0 e) hnone]
        rw [hw] at hpre
        have he : C1 e = clearControlV6 (C0 e) := by
          rw [hC1V7, stepV7_of_row hpsi hwidth hle ring C0 e hne _ hpre]
          simp
        simp [Clear, he]
      rw [if_neg hml] at hpre
      by_cases hmr : MalformedRightPendingGuardV6 (C0 (ring.rightNeighbor e))
      · right; left
        rw [if_pos hmr] at hpre
        have hnone : role (C0 (ring.rightNeighbor e)).carrier = .none :=
          B9SpliceV10cWholeStepLeaderless.role_none_of_not _
            hmr.2.1 hmr.2.2.1 hmr.2.2.2
        have hw : malformedRightPendingWriteV6 (C0 e) (C0 (ring.rightNeighbor e)) =
            (C0 e, clearControlV6 (C0 (ring.rightNeighbor e))) := by
          unfold malformedRightPendingWriteV6
          rw [B9SpliceV10cRowCertFreeLeft.clearPending_eq_clearControl
            (C0 (ring.rightNeighbor e)) hnone]
        rw [hw] at hpre
        have hj : C1 (ring.rightNeighbor e) =
            clearControlV6 (C0 (ring.rightNeighbor e)) := by
          rw [hC1V7, stepV7_of_row hpsi hwidth hle ring C0 e hne _ hpre]
          simp [hne]
        simp [Clear, hj]
      rw [if_neg hmr] at hpre
      by_cases hpl : role (C0 e).carrier = .predecessorArmed
      · left
        rw [if_pos hpl] at hpre
        have he : C1 e = clearControlV6 (C0 e) := by
          rw [hC1V7, stepV7_of_row hpsi hwidth hle ring C0 e hne _ hpre]
          simp [predecessorLeftScrubWriteV6]
        simp [Clear, he]
      rw [if_neg hpl] at hpre
      by_cases hlf : role (C0 e).carrier = .front
      · exfalso
        apply hid
        rw [if_pos hlf] at hpre
        exact hpre
      rw [if_neg hlf] at hpre
      by_cases hmk : MarkedHoldGuardV6 (C0 e) (C0 (ring.rightNeighbor e))
      · exfalso
        apply hid
        rw [if_pos hmk] at hpre
        exact hpre
      rw [if_neg hmk] at hpre
      exfalso
      apply hnphys0
      rw [hC1V7, stepV7_of_row hpsi hwidth hle ring C0 e hne _ hpre]
      exact ordinaryHost_is_physical hpsi hwidth hle ring C0 e hne

  have post_drop_terminal :
      ∀ (D E : R1ConfigV6 n psi kappa tau),
        E = stepV10e hpsi hwidth hle ring D e →
        (∀ i, (D i).carrier.splice.base.core.core.leader = false) →
        SpliceSafeV7 hpsi ring D →
        ShapeClear D →
        ShapeClear E →
        (¬ PhysicalServiceAt hpsi hwidth hle ring D E e) →
        controllerPotentialV6 E < controllerPotentialV6 D →
        (Clear (D e) ∨ Clear (D (ring.rightNeighbor e)) ∨
          HostFenceShapeV7 (D (ring.rightNeighbor e))) →
        Clear (E e) ∧
          (Clear (E (ring.rightNeighbor e)) ∨
            HostFenceShapeV7 (E (ring.rightNeighbor e))) := by
    intro D E hDE hlead hS hclearD hclearE hnphys hdrop hpost
    have hpair := pair_drop_of_step D E hDE hdrop
    rcases hpost with hL | hR | hRF
    · change role (D e).carrier = .none ∧
        (D e).carrier.repairPending = false ∧
        (D e).acquireTicket = false at hL
      rcases Classical.em
          (rowV10d hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) =
            (D e, D (ring.rightNeighbor e))) with h | h
      · by_cases h1 : VictimRightScrubGuardV6 (D (ring.rightNeighbor e))
        · exact (hclearD.1 _ h1.1).elim
        by_cases h2 : FrontRightScrubGuardV6 (D (ring.rightNeighbor e))
        · have he : E e = D e := by
            rw [hDE, stepV10e_of_frontScrub hpsi hwidth hle ring D e hne h h1 h2]
            simp [orphanVictimClearAt, hne, Ne.symm hne]
          have hj : E (ring.rightNeighbor e) =
              clearControlV6 (D (ring.rightNeighbor e)) := by
            rw [hDE, stepV10e_of_frontScrub hpsi hwidth hle ring D e hne h h1 h2]
            simp [orphanVictimClearAt]
          refine ⟨by simpa [Clear, he] using hL, Or.inl ?_⟩
          simp [Clear, hj]
        by_cases h3 : MalformedRightPendingGuardV6 (D (ring.rightNeighbor e))
        · have he : E e = D e := by
            rw [hDE, stepV10e_of_malformedScrub hpsi hwidth hle ring D e hne h h1 h2 h3]
            simp [orphanVictimClearAt, hne, Ne.symm hne]
          have hj : E (ring.rightNeighbor e) =
              clearControlV6 (D (ring.rightNeighbor e)) := by
            rw [hDE, stepV10e_of_malformedScrub hpsi hwidth hle ring D e hne h h1 h2 h3]
            simp [orphanVictimClearAt]
          refine ⟨by simpa [Clear, he] using hL, Or.inl ?_⟩
          simp [Clear, hj]
        by_cases h4 : role (D (ring.rightNeighbor e)).carrier = .predecessorArmed
        · have h5 := hclearD.2 (ring.rightNeighbor e) h4
          exfalso
          apply hnphys
          rw [hDE, stepV10e_of_settledPredFence hpsi hwidth hle ring D e hne h h1 h2 h3 h4 h5]
          exact physicalFence_is_physical hpsi hwidth hle ring D e hne
        · exfalso
          apply hnphys
          rw [hDE, stepV10e_of_physical hpsi hwidth hle ring D e hne h h1 h2 h3 h4]
          exact physicalHold_is_physical hpsi hwidth hle ring D e hne
      · by_cases g1 : OrphanReservedFrontGuardV3
            (D e).carrier (D (ring.rightNeighbor e)).carrier
        · have hE : E = orphanToFenceAt ring D e := by
            rw [hDE, stepV10e_of_change hpsi hwidth hle ring D e hne h,
              stepV10d_of_orphanFront hpsi hwidth hle ring D e hne g1]
          refine ⟨?_, Or.inr ?_⟩
          · have he := at_other ring D e e (Ne.symm hne)
            rw [hE, he]
            exact hL
          · rw [hE, at_j]
            exact fence_shape _
        by_cases g2 : OrphanVictimGuard (D e) (D (ring.rightNeighbor e))
        · exact (hclearD.1 _ g2.1).elim
        by_cases g3 : OwnedPendingVictimGuard (D e) (D (ring.rightNeighbor e))
        · exact (hclearD.1 _ g3.2.2.1).elim
        by_cases g4 : OwnerlessPendingPredGuard (D e) (D (ring.rightNeighbor e))
        · have hx := hclearD.2 (ring.rightNeighbor e) g4.2.1
          have hbad : (false : Bool) = true := hx.symm.trans g4.2.2
          cases hbad
        have hrowd := B9SpliceV10eHandoffFollowUp.rowV10d_of_none
          hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) g1 g2 g3 g4
        by_cases hz : ZeroRefreshOnlyGuardV10c hpsi hwidth hle
            (D e) (D (ring.rightNeighbor e))
        · exfalso
          apply h
          rw [hrowd]
          simp [rowV10c, hz]
        have hrowc := rowV10c_of_notZero hpsi hwidth hle
          (D e) (D (ring.rightNeighbor e)) hz
        by_cases hh : HostFenceAdvanceGuardV10b hpsi
            (D e) (D (ring.rightNeighbor e))
        · have hx := hh.1.2.2
          rw [hL.2.2] at hx
          cases hx
        by_cases hb : HostFenceBusyFrontGuardV9 hpsi
            (D e) (D (ring.rightNeighbor e))
        · have hx := hb.1.2.2
          rw [hL.2.2] at hx
          cases hx
        by_cases hst : RightStalePredecessorHoldGuardV8
            (D e) (D (ring.rightNeighbor e))
        · exfalso
          apply h
          rw [hrowd, hrowc]
          simp [rowV10b, hh, rowV9, hb, rowV8, hst]
        have hrow7 : rowV10d hpsi hwidth hle
            (D e) (D (ring.rightNeighbor e)) =
            rowV7 hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) := by
          rw [hrowd, hrowc]
          simp only [rowV10b, hh, if_false, rowV9, hb, rowV8, hst]
        have hEV7 : E = stepV7 hpsi hwidth hle ring D e := by
          rw [hDE, stepV10e_of_change hpsi hwidth hle ring D e hne h,
            stepV10d_of_none hpsi hwidth hle ring D e hne g1 g2 g3 g4,
            stepV10c_eq_stepV10b hpsi hwidth hle ring D e hne hz,
            stepV10b_eq_stepV9 hpsi hwidth hle ring D e hne hh,
            stepV9_eq_stepV8 hpsi hwidth hle ring D e hne hb,
            stepV8_eq_stepV7 hpsi hwidth hle ring D e hne hst]
        have hid : rowV7 hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) =
            (D e, D (ring.rightNeighbor e)) → False := by
          intro hi
          apply h
          rw [hrow7]
          exact hi
        have hfL : ¬ HostFenceShapeV7 (D e) := by
          intro hx
          have hy := hx.2.2
          rw [hL.2.2] at hy
          cases hy
        by_cases hfR : HostFenceShapeV7 (D (ring.rightNeighbor e))
        · exfalso
          apply hid
          unfold rowV7
          rw [if_neg hfL, if_pos hfR]
          rfl
        have hmaf : ¬ MoveAcquireFrontGuardV6 hpsi (D e) (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.1.1
          rw [hL.1] at hy
          cases hy
        have harmA := armA_needs_leader hpsi hwidth hle
          (D e).carrier (D (ring.rightNeighbor e)).carrier (hlead e)
        have harmB := armB_needs_leader
          (D e).carrier (D (ring.rightNeighbor e)).carrier
          (hlead (ring.rightNeighbor e))
        have hdel := delete_needs_leader hpsi hwidth hle
          (D e).carrier (D (ring.rightNeighbor e)).carrier (hlead e)
        have hph := pendingHold_needs_leader hpsi hwidth hle
          (D e).carrier (D (ring.rightNeighbor e)).carrier (hlead e)
        have hpa := pendingAbort_needs_leader hpsi hwidth hle
          (D e).carrier (D (ring.rightNeighbor e)).carrier (hlead e)
        have hpre : rowV7 hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) =
            (if MoveCommitGuard (D e).carrier (D (ring.rightNeighbor e)).carrier then
              moveCommitWriteV6 hpsi (D e) (D (ring.rightNeighbor e))
            else if MoveStopGuardV3 hpsi (D e).carrier (D (ring.rightNeighbor e)).carrier then
              moveStopWriteV6 (D e) (D (ring.rightNeighbor e))
            else if MoveSeekGuardV3 hpsi (D e).carrier (D (ring.rightNeighbor e)).carrier then
              moveSeekWriteV6 (D e) (D (ring.rightNeighbor e))
            else if MoveSeekHoldGuardV3 (D e).carrier (D (ring.rightNeighbor e)).carrier then
              moveSeekHoldWriteV6 (D e) (D (ring.rightNeighbor e))
            else if PendingOwnerAbortGuardV3 (D e).carrier (D (ring.rightNeighbor e)).carrier then
              pendingOwnerAbortWriteV6 (D e) (D (ring.rightNeighbor e))
            else if role (D e).carrier = .predecessorArmed ∧ (D e).carrier.repairPending = true then
              pendingOwnerHoldWriteV6 (D e) (D (ring.rightNeighbor e))
            else if MoveAcquireLegacyGuardV6 (D e) (D (ring.rightNeighbor e)) then
              moveAcquireLegacyWriteV6 (D e) (D (ring.rightNeighbor e))
            else if MoveAcquireAbortGuardV3 (D e).carrier (D (ring.rightNeighbor e)).carrier then
              moveAcquireAbortWriteV6 (D e) (D (ring.rightNeighbor e))
            else if OrphanReservedFrontGuardV3 (D e).carrier (D (ring.rightNeighbor e)).carrier then
              orphanReservedFrontWriteV6 (D e) (D (ring.rightNeighbor e))
            else if ReservedFrontHoldGuard (D e).carrier then
              reservedFrontHoldWriteV6 (D e) (D (ring.rightNeighbor e))
            else if VictimRightScrubGuardV6 (D (ring.rightNeighbor e)) then
              victimRightScrubWriteV6 (D e) (D (ring.rightNeighbor e))
            else if VictimLeftScrubGuardV6 (D e) then
              victimLeftScrubWriteV6 (D e) (D (ring.rightNeighbor e))
            else if FrontRightScrubGuardV6 (D (ring.rightNeighbor e)) then
              frontRightScrubWriteV6 (D e) (D (ring.rightNeighbor e))
            else if MalformedLeftPendingGuardV6 (D e) then
              malformedLeftPendingWriteV6 (D e) (D (ring.rightNeighbor e))
            else if MalformedRightPendingGuardV6 (D (ring.rightNeighbor e)) then
              malformedRightPendingWriteV6 (D e) (D (ring.rightNeighbor e))
            else if role (D e).carrier = .predecessorArmed then
              predecessorLeftScrubWriteV6 (D e) (D (ring.rightNeighbor e))
            else if role (D e).carrier = .front then
              leftFrontHoldWriteV6 (D e) (D (ring.rightNeighbor e))
            else if MarkedHoldGuardV6 (D e) (D (ring.rightNeighbor e)) then
              markedHoldWriteV6 (D e) (D (ring.rightNeighbor e))
            else ordinaryHostWriteV7 hpsi hwidth hle (D e) (D (ring.rightNeighbor e))) := by
          unfold rowV7
          rw [if_neg hfL, if_neg hfR, if_neg hmaf, if_neg harmA,
            if_neg harmB, if_neg hdel, if_neg hph, if_neg hpa]
        have hmc : ¬ MoveCommitGuard (D e).carrier (D (ring.rightNeighbor e)).carrier := by
          intro hx
          have hy := hx.1
          rw [hL.1] at hy
          cases hy
        rw [if_neg hmc] at hpre
        have hms : ¬ MoveStopGuardV3 hpsi (D e).carrier (D (ring.rightNeighbor e)).carrier := by
          intro hx
          have hy := hx.1
          rw [hL.1] at hy
          cases hy
        rw [if_neg hms] at hpre
        have hsk : ¬ MoveSeekGuardV3 hpsi (D e).carrier (D (ring.rightNeighbor e)).carrier := by
          intro hx
          have hy := hx.1
          rw [hL.1] at hy
          cases hy
        rw [if_neg hsk] at hpre
        have hskh : ¬ MoveSeekHoldGuardV3 (D e).carrier (D (ring.rightNeighbor e)).carrier := by
          intro hx
          have hy := hx.1
          rw [hL.1] at hy
          cases hy
        rw [if_neg hskh] at hpre
        by_cases hpoa : PendingOwnerAbortGuardV3
            (D e).carrier (D (ring.rightNeighbor e)).carrier
        · have hp := hclearD.2 (ring.rightNeighbor e) hpoa.1
          have hbad : (false : Bool) = true := hp.symm.trans hpoa.2.1
          cases hbad
        rw [if_neg hpoa] at hpre
        have hpoh : ¬ (role (D e).carrier = .predecessorArmed ∧
            (D e).carrier.repairPending = true) := by
          intro hx
          rw [hL.1] at hx
          cases hx.1
        rw [if_neg hpoh] at hpre
        have hmal : ¬ MoveAcquireLegacyGuardV6 (D e) (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.1.1
          rw [hL.1] at hy
          cases hy
        rw [if_neg hmal] at hpre
        have hmaa : ¬ MoveAcquireAbortGuardV3 (D e).carrier (D (ring.rightNeighbor e)).carrier := by
          intro hx
          have hy := hx.1
          rw [hL.1] at hy
          cases hy
        rw [if_neg hmaa] at hpre
        by_cases horf : OrphanReservedFrontGuardV3
            (D e).carrier (D (ring.rightNeighbor e)).carrier
        · exact (g1 horf).elim
        rw [if_neg horf] at hpre
        have hrfh : ¬ ReservedFrontHoldGuard (D e).carrier := by
          intro hx
          have hy := hx.1
          rw [hL.1] at hy
          cases hy
        rw [if_neg hrfh] at hpre
        by_cases hvr : VictimRightScrubGuardV6 (D (ring.rightNeighbor e))
        · exact (hclearD.1 _ hvr.1).elim
        rw [if_neg hvr] at hpre
        have hvl : ¬ VictimLeftScrubGuardV6 (D e) := by
          intro hx
          have hy := hx.1
          rw [hL.1] at hy
          cases hy
        rw [if_neg hvl] at hpre
        by_cases hfr : FrontRightScrubGuardV6 (D (ring.rightNeighbor e))
        · rw [if_pos hfr] at hpre
          have he : E e = D e := by
            rw [hEV7, stepV7_of_row hpsi hwidth hle ring D e hne _ hpre]
            simp [frontRightScrubWriteV6]
          have hj : E (ring.rightNeighbor e) =
              clearControlV6 (D (ring.rightNeighbor e)) := by
            rw [hEV7, stepV7_of_row hpsi hwidth hle ring D e hne _ hpre]
            simp [frontRightScrubWriteV6, hne]
          refine ⟨by simpa [Clear, he] using hL, Or.inl ?_⟩
          simp [Clear, hj]
        rw [if_neg hfr] at hpre
        have hml : ¬ MalformedLeftPendingGuardV6 (D e) := by
          intro hx
          have hy := hx.1
          rw [hL.2.1] at hy
          cases hy
        rw [if_neg hml] at hpre
        by_cases hmr : MalformedRightPendingGuardV6 (D (ring.rightNeighbor e))
        · rw [if_pos hmr] at hpre
          have hnone : role (D (ring.rightNeighbor e)).carrier = .none :=
            B9SpliceV10cWholeStepLeaderless.role_none_of_not _
              hmr.2.1 hmr.2.2.1 hmr.2.2.2
          have hw : malformedRightPendingWriteV6 (D e) (D (ring.rightNeighbor e)) =
              (D e, clearControlV6 (D (ring.rightNeighbor e))) := by
            unfold malformedRightPendingWriteV6
            rw [B9SpliceV10cRowCertFreeLeft.clearPending_eq_clearControl
              (D (ring.rightNeighbor e)) hnone]
          rw [hw] at hpre
          have he : E e = D e := by
            rw [hEV7, stepV7_of_row hpsi hwidth hle ring D e hne _ hpre]
            simp
          have hj : E (ring.rightNeighbor e) =
              clearControlV6 (D (ring.rightNeighbor e)) := by
            rw [hEV7, stepV7_of_row hpsi hwidth hle ring D e hne _ hpre]
            simp [hne]
          refine ⟨by simpa [Clear, he] using hL, Or.inl ?_⟩
          simp [Clear, hj]
        rw [if_neg hmr] at hpre
        have hpl : ¬ role (D e).carrier = .predecessorArmed := by
          rw [hL.1]
          decide
        rw [if_neg hpl] at hpre
        have hlf : ¬ role (D e).carrier = .front := by
          rw [hL.1]
          decide
        rw [if_neg hlf] at hpre
        by_cases hmk : MarkedHoldGuardV6 (D e) (D (ring.rightNeighbor e))
        · exfalso
          apply hid
          rw [if_pos hmk] at hpre
          exact hpre
        rw [if_neg hmk] at hpre
        exfalso
        apply hnphys
        rw [hEV7, stepV7_of_row hpsi hwidth hle ring D e hne _ hpre]
        exact ordinaryHost_is_physical hpsi hwidth hle ring D e hne
    · change role (D (ring.rightNeighbor e)).carrier = .none ∧
        (D (ring.rightNeighbor e)).carrier.repairPending = false ∧
        (D (ring.rightNeighbor e)).acquireTicket = false at hR
      rcases Classical.em
          (rowV10d hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) =
            (D e, D (ring.rightNeighbor e))) with h | h
      · have h1 : ¬ VictimRightScrubGuardV6 (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.1
          rw [hR.1] at hy
          cases hy
        have h2 : ¬ FrontRightScrubGuardV6 (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.1
          rw [hR.1] at hy
          cases hy
        have h3 : ¬ MalformedRightPendingGuardV6 (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.1
          rw [hR.2.1] at hy
          cases hy
        have h4 : ¬ role (D (ring.rightNeighbor e)).carrier = .predecessorArmed := by
          rw [hR.1]
          decide
        exfalso
        apply hnphys
        rw [hDE, stepV10e_of_physical hpsi hwidth hle ring D e hne h h1 h2 h3 h4]
        exact physicalHold_is_physical hpsi hwidth hle ring D e hne
      · have g1 : ¬ OrphanReservedFrontGuardV3
            (D e).carrier (D (ring.rightNeighbor e)).carrier := by
          intro hx
          have hy := hx.1.1
          rw [hR.1] at hy
          cases hy
        have g2 : ¬ OrphanVictimGuard (D e) (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.1
          rw [hR.1] at hy
          cases hy
        have g3 : ¬ OwnedPendingVictimGuard (D e) (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.2.2.1
          rw [hR.1] at hy
          cases hy
        have g4 : ¬ OwnerlessPendingPredGuard (D e) (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.2.1
          rw [hR.1] at hy
          cases hy
        have hrowd := B9SpliceV10eHandoffFollowUp.rowV10d_of_none
          hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) g1 g2 g3 g4
        by_cases hz : ZeroRefreshOnlyGuardV10c hpsi hwidth hle
            (D e) (D (ring.rightNeighbor e))
        · exfalso
          apply h
          rw [hrowd]
          simp [rowV10c, hz]
        have hrowc := rowV10c_of_notZero hpsi hwidth hle
          (D e) (D (ring.rightNeighbor e)) hz
        by_cases hh : HostFenceAdvanceGuardV10b hpsi
            (D e) (D (ring.rightNeighbor e))
        · have hp := hpair
          rw [hDE] at hp
          exact (handoff_not_pair_drop D hh hp).elim
        by_cases hb : HostFenceBusyFrontGuardV9 hpsi
            (D e) (D (ring.rightNeighbor e))
        · have hy := hb.2.2.1
          rw [hR.1] at hy
          cases hy
        by_cases hst : RightStalePredecessorHoldGuardV8
            (D e) (D (ring.rightNeighbor e))
        · have hy := hst.2.2.2.1
          rw [hR.1] at hy
          cases hy
        have hrow7 : rowV10d hpsi hwidth hle
            (D e) (D (ring.rightNeighbor e)) =
            rowV7 hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) := by
          rw [hrowd, hrowc]
          simp only [rowV10b, hh, if_false, rowV9, hb, rowV8, hst]
        have hEV7 : E = stepV7 hpsi hwidth hle ring D e := by
          rw [hDE, stepV10e_of_change hpsi hwidth hle ring D e hne h,
            stepV10d_of_none hpsi hwidth hle ring D e hne g1 g2 g3 g4,
            stepV10c_eq_stepV10b hpsi hwidth hle ring D e hne hz,
            stepV10b_eq_stepV9 hpsi hwidth hle ring D e hne hh,
            stepV9_eq_stepV8 hpsi hwidth hle ring D e hne hb,
            stepV8_eq_stepV7 hpsi hwidth hle ring D e hne hst]
        have hid : rowV7 hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) =
            (D e, D (ring.rightNeighbor e)) → False := by
          intro hi
          apply h
          rw [hrow7]
          exact hi
        by_cases hfL : HostFenceShapeV7 (D e)
        · by_cases hbar : LocalPreparedBarrier hpsi
              (D e).carrier (D (ring.rightNeighbor e)).carrier
          · exact (hh ⟨hfL, hbar, ⟨hR.1, hR.2.1⟩⟩).elim
          · have hrowS : rowV7 hpsi hwidth hle
                (D e) (D (ring.rightNeighbor e)) =
                (clearTicketV6 (D e), D (ring.rightNeighbor e)) := by
              unfold rowV7
              rw [if_pos hfL, if_neg hbar]
              rfl
            have he : E e = clearTicketV6 (D e) := by
              rw [hEV7, stepV7_of_left hpsi hwidth hle ring D e hne clearTicketV6 hrowS]
              simp
            have hj : E (ring.rightNeighbor e) = D (ring.rightNeighbor e) := by
              rw [hEV7, stepV7_of_left hpsi hwidth hle ring D e hne clearTicketV6 hrowS]
              simp [hne]
            refine ⟨?_, Or.inl ?_⟩
            · simp [Clear, he, hfL.1, hfL.2.1]
            · simpa [Clear, hj] using hR
        have hfR : ¬ HostFenceShapeV7 (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.2.2
          rw [hR.2.2] at hy
          cases hy
        have hmaf : ¬ MoveAcquireFrontGuardV6 hpsi (D e) (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.2.2.2.1.1
          rw [hR.1] at hy
          cases hy
        have harmA := armA_needs_leader hpsi hwidth hle
          (D e).carrier (D (ring.rightNeighbor e)).carrier (hlead e)
        have harmB := armB_needs_leader
          (D e).carrier (D (ring.rightNeighbor e)).carrier
          (hlead (ring.rightNeighbor e))
        have hdel := delete_needs_leader hpsi hwidth hle
          (D e).carrier (D (ring.rightNeighbor e)).carrier (hlead e)
        have hph := pendingHold_needs_leader hpsi hwidth hle
          (D e).carrier (D (ring.rightNeighbor e)).carrier (hlead e)
        have hpa := pendingAbort_needs_leader hpsi hwidth hle
          (D e).carrier (D (ring.rightNeighbor e)).carrier (hlead e)
        have hpre : rowV7 hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) =
            (if MoveCommitGuard (D e).carrier (D (ring.rightNeighbor e)).carrier then
              moveCommitWriteV6 hpsi (D e) (D (ring.rightNeighbor e))
            else if MoveStopGuardV3 hpsi (D e).carrier (D (ring.rightNeighbor e)).carrier then
              moveStopWriteV6 (D e) (D (ring.rightNeighbor e))
            else if MoveSeekGuardV3 hpsi (D e).carrier (D (ring.rightNeighbor e)).carrier then
              moveSeekWriteV6 (D e) (D (ring.rightNeighbor e))
            else if MoveSeekHoldGuardV3 (D e).carrier (D (ring.rightNeighbor e)).carrier then
              moveSeekHoldWriteV6 (D e) (D (ring.rightNeighbor e))
            else if PendingOwnerAbortGuardV3 (D e).carrier (D (ring.rightNeighbor e)).carrier then
              pendingOwnerAbortWriteV6 (D e) (D (ring.rightNeighbor e))
            else if role (D e).carrier = .predecessorArmed ∧ (D e).carrier.repairPending = true then
              pendingOwnerHoldWriteV6 (D e) (D (ring.rightNeighbor e))
            else if MoveAcquireLegacyGuardV6 (D e) (D (ring.rightNeighbor e)) then
              moveAcquireLegacyWriteV6 (D e) (D (ring.rightNeighbor e))
            else if MoveAcquireAbortGuardV3 (D e).carrier (D (ring.rightNeighbor e)).carrier then
              moveAcquireAbortWriteV6 (D e) (D (ring.rightNeighbor e))
            else if OrphanReservedFrontGuardV3 (D e).carrier (D (ring.rightNeighbor e)).carrier then
              orphanReservedFrontWriteV6 (D e) (D (ring.rightNeighbor e))
            else if ReservedFrontHoldGuard (D e).carrier then
              reservedFrontHoldWriteV6 (D e) (D (ring.rightNeighbor e))
            else if VictimRightScrubGuardV6 (D (ring.rightNeighbor e)) then
              victimRightScrubWriteV6 (D e) (D (ring.rightNeighbor e))
            else if VictimLeftScrubGuardV6 (D e) then
              victimLeftScrubWriteV6 (D e) (D (ring.rightNeighbor e))
            else if FrontRightScrubGuardV6 (D (ring.rightNeighbor e)) then
              frontRightScrubWriteV6 (D e) (D (ring.rightNeighbor e))
            else if MalformedLeftPendingGuardV6 (D e) then
              malformedLeftPendingWriteV6 (D e) (D (ring.rightNeighbor e))
            else if MalformedRightPendingGuardV6 (D (ring.rightNeighbor e)) then
              malformedRightPendingWriteV6 (D e) (D (ring.rightNeighbor e))
            else if role (D e).carrier = .predecessorArmed then
              predecessorLeftScrubWriteV6 (D e) (D (ring.rightNeighbor e))
            else if role (D e).carrier = .front then
              leftFrontHoldWriteV6 (D e) (D (ring.rightNeighbor e))
            else if MarkedHoldGuardV6 (D e) (D (ring.rightNeighbor e)) then
              markedHoldWriteV6 (D e) (D (ring.rightNeighbor e))
            else ordinaryHostWriteV7 hpsi hwidth hle (D e) (D (ring.rightNeighbor e))) := by
          unfold rowV7
          rw [if_neg hfL, if_neg hfR, if_neg hmaf, if_neg harmA,
            if_neg harmB, if_neg hdel, if_neg hph, if_neg hpa]
        have hmc : ¬ MoveCommitGuard (D e).carrier (D (ring.rightNeighbor e)).carrier := by
          intro hx
          have hy := hx.2.2.1
          rw [hR.1] at hy
          cases hy
        rw [if_neg hmc] at hpre
        have hms : ¬ MoveStopGuardV3 hpsi (D e).carrier (D (ring.rightNeighbor e)).carrier := by
          intro hx
          have hy := hx.2.2.1.1
          rw [hR.1] at hy
          cases hy
        rw [if_neg hms] at hpre
        have hsk : ¬ MoveSeekGuardV3 hpsi (D e).carrier (D (ring.rightNeighbor e)).carrier := by
          intro hx
          have hy := hx.2.2.1.1
          rw [hR.1] at hy
          cases hy
        rw [if_neg hsk] at hpre
        have hskh : ¬ MoveSeekHoldGuardV3 (D e).carrier (D (ring.rightNeighbor e)).carrier := by
          intro hx
          have hy := hx.2.2.1
          rw [hR.1] at hy
          cases hy
        rw [if_neg hskh] at hpre
        have hpoa : ¬ PendingOwnerAbortGuardV3 (D e).carrier (D (ring.rightNeighbor e)).carrier := by
          intro hx
          have hy := hx.1
          rw [hR.1] at hy
          cases hy
        rw [if_neg hpoa] at hpre
        by_cases hpoh : role (D e).carrier = .predecessorArmed ∧
            (D e).carrier.repairPending = true
        · have hp := hclearD.2 e hpoh.1
          have hbad : (false : Bool) = true := hp.symm.trans hpoh.2
          cases hbad
        rw [if_neg hpoh] at hpre
        by_cases hmal : MoveAcquireLegacyGuardV6 (D e) (D (ring.rightNeighbor e))
        · exact (hclearD.1 e hmal.1.1).elim
        rw [if_neg hmal] at hpre
        by_cases hmaa : MoveAcquireAbortGuardV3 (D e).carrier (D (ring.rightNeighbor e)).carrier
        · exact (hclearD.1 e hmaa.1).elim
        rw [if_neg hmaa] at hpre
        have horf : ¬ OrphanReservedFrontGuardV3
            (D e).carrier (D (ring.rightNeighbor e)).carrier := g1
        rw [if_neg horf] at hpre
        by_cases hrfh : ReservedFrontHoldGuard (D e).carrier
        · exfalso
          apply hid
          rw [if_pos hrfh] at hpre
          exact hpre
        rw [if_neg hrfh] at hpre
        have hvr : ¬ VictimRightScrubGuardV6 (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.1
          rw [hR.1] at hy
          cases hy
        rw [if_neg hvr] at hpre
        by_cases hvl : VictimLeftScrubGuardV6 (D e)
        · exact (hclearD.1 e hvl.1).elim
        rw [if_neg hvl] at hpre
        have hfr : ¬ FrontRightScrubGuardV6 (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.1
          rw [hR.1] at hy
          cases hy
        rw [if_neg hfr] at hpre
        by_cases hml : MalformedLeftPendingGuardV6 (D e)
        · rw [if_pos hml] at hpre
          have hnone : role (D e).carrier = .none :=
            B9SpliceV10cWholeStepLeaderless.role_none_of_not _
              hml.2.1 hml.2.2.1 hml.2.2.2
          have hw : malformedLeftPendingWriteV6 (D e) (D (ring.rightNeighbor e)) =
              (clearControlV6 (D e), D (ring.rightNeighbor e)) := by
            unfold malformedLeftPendingWriteV6
            rw [B9SpliceV10cRowCertFreeLeft.clearPending_eq_clearControl (D e) hnone]
          rw [hw] at hpre
          have he : E e = clearControlV6 (D e) := by
            rw [hEV7, stepV7_of_row hpsi hwidth hle ring D e hne _ hpre]
            simp
          have hj : E (ring.rightNeighbor e) = D (ring.rightNeighbor e) := by
            rw [hEV7, stepV7_of_row hpsi hwidth hle ring D e hne _ hpre]
            simp [hne]
          refine ⟨by simp [Clear, he], Or.inl ?_⟩
          simpa [Clear, hj] using hR
        rw [if_neg hml] at hpre
        have hmr : ¬ MalformedRightPendingGuardV6 (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.1
          rw [hR.2.1] at hy
          cases hy
        rw [if_neg hmr] at hpre
        by_cases hpl : role (D e).carrier = .predecessorArmed
        · rw [if_pos hpl] at hpre
          have he : E e = clearControlV6 (D e) := by
            rw [hEV7, stepV7_of_row hpsi hwidth hle ring D e hne _ hpre]
            simp [predecessorLeftScrubWriteV6]
          have hj : E (ring.rightNeighbor e) = D (ring.rightNeighbor e) := by
            rw [hEV7, stepV7_of_row hpsi hwidth hle ring D e hne _ hpre]
            simp [predecessorLeftScrubWriteV6, hne]
          refine ⟨by simp [Clear, he], Or.inl ?_⟩
          simpa [Clear, hj] using hR
        rw [if_neg hpl] at hpre
        by_cases hlf : role (D e).carrier = .front
        · exfalso
          apply hid
          rw [if_pos hlf] at hpre
          exact hpre
        rw [if_neg hlf] at hpre
        by_cases hmk : MarkedHoldGuardV6 (D e) (D (ring.rightNeighbor e))
        · exfalso
          apply hid
          rw [if_pos hmk] at hpre
          exact hpre
        rw [if_neg hmk] at hpre
        exfalso
        apply hnphys
        rw [hEV7, stepV7_of_row hpsi hwidth hle ring D e hne _ hpre]
        exact ordinaryHost_is_physical hpsi hwidth hle ring D e hne
    · rcases Classical.em
          (rowV10d hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) =
            (D e, D (ring.rightNeighbor e))) with h | h
      · have h1 : ¬ VictimRightScrubGuardV6 (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.1
          rw [hRF.1] at hy
          cases hy
        have h2 : ¬ FrontRightScrubGuardV6 (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.1
          rw [hRF.1] at hy
          cases hy
        have h3 : ¬ MalformedRightPendingGuardV6 (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.1
          rw [hRF.2.1] at hy
          cases hy
        have h4 : ¬ role (D (ring.rightNeighbor e)).carrier = .predecessorArmed := by
          rw [hRF.1]
          decide
        exfalso
        apply hnphys
        rw [hDE, stepV10e_of_physical hpsi hwidth hle ring D e hne h h1 h2 h3 h4]
        exact physicalHold_is_physical hpsi hwidth hle ring D e hne
      · have g1 : ¬ OrphanReservedFrontGuardV3
            (D e).carrier (D (ring.rightNeighbor e)).carrier := by
          intro hx
          have hy := hx.1.1
          rw [hRF.1] at hy
          cases hy
        have g2 : ¬ OrphanVictimGuard (D e) (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.1
          rw [hRF.1] at hy
          cases hy
        have g3 : ¬ OwnedPendingVictimGuard (D e) (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.2.2.1
          rw [hRF.1] at hy
          cases hy
        have g4 : ¬ OwnerlessPendingPredGuard (D e) (D (ring.rightNeighbor e)) := by
          intro hx
          have hy := hx.2.1
          rw [hRF.1] at hy
          cases hy
        have hrowd := B9SpliceV10eHandoffFollowUp.rowV10d_of_none
          hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) g1 g2 g3 g4
        by_cases hz : ZeroRefreshOnlyGuardV10c hpsi hwidth hle
            (D e) (D (ring.rightNeighbor e))
        · exfalso
          apply h
          rw [hrowd]
          simp [rowV10c, hz]
        have hrowc := rowV10c_of_notZero hpsi hwidth hle
          (D e) (D (ring.rightNeighbor e)) hz
        by_cases hh : HostFenceAdvanceGuardV10b hpsi
            (D e) (D (ring.rightNeighbor e))
        · have hp := hpair
          rw [hDE] at hp
          exact (handoff_not_pair_drop D hh hp).elim
        by_cases hb : HostFenceBusyFrontGuardV9 hpsi
            (D e) (D (ring.rightNeighbor e))
        · have hy := hb.2.2.1
          rw [hRF.1] at hy
          cases hy
        by_cases hst : RightStalePredecessorHoldGuardV8
            (D e) (D (ring.rightNeighbor e))
        · have hy := hst.2.2.2.1
          rw [hRF.1] at hy
          cases hy
        have hrow7 : rowV10d hpsi hwidth hle
            (D e) (D (ring.rightNeighbor e)) =
            rowV7 hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) := by
          rw [hrowd, hrowc]
          simp only [rowV10b, hh, if_false, rowV9, hb, rowV8, hst]
        have hEV7 : E = stepV7 hpsi hwidth hle ring D e := by
          rw [hDE, stepV10e_of_change hpsi hwidth hle ring D e hne h,
            stepV10d_of_none hpsi hwidth hle ring D e hne g1 g2 g3 g4,
            stepV10c_eq_stepV10b hpsi hwidth hle ring D e hne hz,
            stepV10b_eq_stepV9 hpsi hwidth hle ring D e hne hh,
            stepV9_eq_stepV8 hpsi hwidth hle ring D e hne hb,
            stepV8_eq_stepV7 hpsi hwidth hle ring D e hne hst]
        have hid : rowV7 hpsi hwidth hle (D e) (D (ring.rightNeighbor e)) =
            (D e, D (ring.rightNeighbor e)) → False := by
          intro hi
          apply h
          rw [hrow7]
          exact hi
        by_cases hfL : HostFenceShapeV7 (D e)
        · by_cases hbar : LocalPreparedBarrier hpsi
              (D e).carrier (D (ring.rightNeighbor e)).carrier
          · exact (hh ⟨hfL, hbar, ⟨hRF.1, hRF.2.1⟩⟩).elim
          · have hrowS : rowV7 hpsi hwidth hle
                (D e) (D (ring.rightNeighbor e)) =
                (clearTicketV6 (D e), D (ring.rightNeighbor e)) := by
              unfold rowV7
              rw [if_pos hfL, if_neg hbar]
              rfl
            have he : E e = clearTicketV6 (D e) := by
              rw [hEV7, stepV7_of_left hpsi hwidth hle ring D e hne clearTicketV6 hrowS]
              simp
            have hj : E (ring.rightNeighbor e) = D (ring.rightNeighbor e) := by
              rw [hEV7, stepV7_of_left hpsi hwidth hle ring D e hne clearTicketV6 hrowS]
              simp [hne]
            refine ⟨?_, Or.inr ?_⟩
            · simp [Clear, he, hfL.1, hfL.2.1]
            · simpa [hj] using hRF
        · exfalso
          apply hid
          unfold rowV7
          rw [if_neg hfL, if_pos hRF]
          rfl

  have hterminal := post_drop_terminal C1 C2 h12 hlead1 hS1 hclear1 hclear2
    hnphys1 hdrop1 hpost1
  exact physical_of_terminal C2 hlead2 hS2 hterminal.1 hterminal.2

end B9SpliceTwoDropPhysical
