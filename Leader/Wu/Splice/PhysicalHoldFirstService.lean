import Leader.Wu.Splice.PhysicalHoldRowPotential
import Leader.Wu.Splice.PhysicalHoldHandoffFollowUp
import Leader.Wu.Splice.PhysicalHoldLeaderlessSafe

set_option autoImplicit false
set_option Elab.async false

/-! # Classification of the first V10e service on a leaderless safe configuration

Every service is physical, drops `controllerPotentialV6`, is the V10b handoff, or is the
(pending victim, pending predecessor) hold. -/

namespace B9SpliceV10eClassification

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10d B9SpliceTableV10e
  B9SpliceV10eTransparency B9SpliceV10cChainShapes B9SpliceV10cLeaderlessExclusion
  B9SpliceV10ePhysicalHoldNoBirth B9SpliceV10eRowPotential B9SpliceV10eHandoffFollowUp
  B9SpliceV10eAssembly

variable {n psi width kappa tau : Nat}

def VictimPredHold (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  role l.carrier = .victimArmed ∧ l.carrier.repairPending = true ∧
    role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = true

/-- Potential drop for a step of the shape `if i = e then a else if i = j then b else C i`. -/
theorem drop_of_pair (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) (a b : R1AgentStateV6 psi kappa tau)
    (hsum : controllerWeightV6 a + controllerWeightV6 b <
      controllerWeightV6 (C e) + controllerWeightV6 (C (ring.rightNeighbor e))) :
    controllerPotentialV6 (fun i => if i = e then a else if i = ring.rightNeighbor e then b else C i) <
      controllerPotentialV6 C := by
  apply potential_drop_two ring C _ e (ring.rightNeighbor e) (Ne.symm hne)
  · intro i hi hj; simp [hi, hj]
  · simp [hne]; exact hsum

/-- The ordinary host is a physical service. -/
theorem ordinaryHost_is_physical (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    PhysicalServiceAt hpsi hwidth hle ring C
      (fun i => if i = e then (ordinaryHostWriteV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).1
        else if i = ring.rightNeighbor e then (ordinaryHostWriteV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).2
        else C i) e := by
  unfold PhysicalServiceAt
  dsimp only
  have hc := physicalHold_carriers_eq_ordinaryHost hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  constructor
  · simp only [eq_self_iff_true, if_true]
    rw [← hc.1]
    exact physicalHold_base_left hpsi hwidth hle _ _
  · simp only [if_neg hne, eq_self_iff_true, if_true]
    rw [← hc.2]
    exact physicalHold_base_right hpsi hwidth hle _ _

theorem first_service_classified
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7 hpsi ring C) :
    PhysicalServiceAt hpsi hwidth hle ring C (stepV10e hpsi hwidth hle ring C e) e ∨
    controllerPotentialV6 (stepV10e hpsi hwidth hle ring C e) < controllerPotentialV6 C ∨
    HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e)) ∨
    VictimPredHold (C e) (C (ring.rightNeighbor e)) := by
  have hl := hlead e
  have hr := hlead (ring.rightNeighbor e)
  rcases Classical.em (rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e))) with h | h
  · -- V10d stutters: the V10e branches
    by_cases h1 : VictimRightScrubGuardV6 (C (ring.rightNeighbor e))
    · right; left
      rw [stepV10e_of_victimScrub hpsi hwidth hle ring C e hne h h1]
      apply potential_drop_one ring C _ (ring.rightNeighbor e)
      · intro i hi; simp [orphanVictimClearAt, hi]
      · simp only [orphanVictimClearAt, eq_self_iff_true, if_true]
        exact weight_clearControl_lt _ (by rw [h1.1]; decide)
    by_cases h2 : FrontRightScrubGuardV6 (C (ring.rightNeighbor e))
    · right; left
      rw [stepV10e_of_frontScrub hpsi hwidth hle ring C e hne h h1 h2]
      apply potential_drop_one ring C _ (ring.rightNeighbor e)
      · intro i hi; simp [orphanVictimClearAt, hi]
      · simp only [orphanVictimClearAt, eq_self_iff_true, if_true]
        exact weight_clearControl_lt _ (by rw [h2.1]; decide)
    by_cases h3 : MalformedRightPendingGuardV6 (C (ring.rightNeighbor e))
    · right; left
      rw [stepV10e_of_malformedScrub hpsi hwidth hle ring C e hne h h1 h2 h3]
      apply potential_drop_one ring C _ (ring.rightNeighbor e)
      · intro i hi; simp [orphanVictimClearAt, hi]
      · simp only [orphanVictimClearAt, eq_self_iff_true, if_true]
        rw [weight_clear]; exact weight_pos_of_pending _ h3.1
    by_cases h4 : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed
    · by_cases h5 : (C (ring.rightNeighbor e)).carrier.repairPending = true
      · by_cases h6 : ReservedFrontHoldGuard (C e).carrier
        · right; left
          rw [stepV10e_of_frontOwnedPredClear hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5 h6]
          apply potential_drop_one ring C _ (ring.rightNeighbor e)
          · intro i hi; simp [orphanVictimClearAt, hi]
          · simp only [orphanVictimClearAt, eq_self_iff_true, if_true]
            exact weight_clearControl_lt _ (by rw [h4]; decide)
        by_cases h7 : LeftScrubGuardV10e (C e)
        · right; left
          rw [stepV10e_of_leftScrub hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5 h6 h7]
          apply potential_drop_one ring C _ e
          · intro i hi; simp [clearLeftAtV10e, hi]
          · simp only [clearLeftAtV10e, eq_self_iff_true, if_true]
            rw [weight_clear]
            rcases h7 with hv | hf | hm
            · exact weight_pos_of_role _ (by rw [hv.1]; decide)
            · exact weight_pos_of_role _ (by rw [hf.1]; decide)
            · exact weight_pos_of_pending _ hm.1
        · -- the hold: the left cell must be a pending victim
          right; right; right
          have hnotnone : role (C e).carrier ≠ .none := by
            intro hnone
            have : OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e)) := ⟨hnone, h4, h5⟩
            have hrow : role (rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).2.carrier = .none := by
              unfold rowV10d
              have hnf : ¬ OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier := by
                intro ho; have := ho.1.1; rw [h4] at this; cases this
              have hov : ¬ OrphanVictimGuard (C e) (C (ring.rightNeighbor e)) := by
                intro ho; have := ho.1; rw [h4] at this; cases this
              have how : ¬ OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e)) := by
                intro ho; have := ho.2.2.1; rw [h4] at this; cases this
              rw [if_neg hnf, if_neg hov, if_neg how, if_pos this]
              rfl
            rw [h] at hrow
            simp only at hrow
            rw [h4] at hrow
            cases hrow
          cases hrole : role (C e).carrier with
          | none => exact absurd hrole hnotnone
          | front =>
              exfalso
              cases hp : (C e).carrier.repairPending
              · exact h7 (Or.inr (Or.inl ⟨hrole, hp⟩))
              · exact h6 ⟨hrole, hp⟩
          | predecessorArmed =>
              exfalso
              cases hp : (C e).carrier.repairPending
              · -- settled predecessor: MOVE-COMMIT would have changed the pair
                have hmc : MoveCommitGuard (C e).carrier (C (ring.rightNeighbor e)).carrier := ⟨hrole, hp, h4, h5, hr⟩
                have hnf : ¬ OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier := by
                  intro ho; have := ho.1.1; rw [h4] at this; cases this
                have hov : ¬ OrphanVictimGuard (C e) (C (ring.rightNeighbor e)) := by
                  intro ho; have := ho.1; rw [h4] at this; cases this
                have how : ¬ OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e)) := by
                  intro ho; have := ho.2.2.1; rw [h4] at this; cases this
                have hop : ¬ OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e)) := by
                  intro ho; have := ho.1; rw [hrole] at this; cases this
                have hfL : ¬ HostFenceShapeV7 (C e) := by intro hf; have := hf.1; rw [hrole] at this; cases this
                have hfR : ¬ HostFenceShapeV7 (C (ring.rightNeighbor e)) := by
                  intro hf; have := hf.1; rw [h4] at this; cases this
                have hh : ¬ HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e)) := fun hh => hfL hh.1
                have hb : ¬ HostFenceBusyFrontGuardV9 hpsi (C e) (C (ring.rightNeighbor e)) := fun hb => hfL hb.1
                have hst : ¬ RightStalePredecessorHoldGuardV8 (C e) (C (ring.rightNeighbor e)) := by
                  intro hs; have := hs.1; rw [hrole] at this; cases this
                have hmaf : ¬ MoveAcquireFrontGuardV6 hpsi (C e) (C (ring.rightNeighbor e)) := by
                  intro hm; have := hm.1.1; rw [hrole] at this; cases this
                have hrowb : rowV10b hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
                    moveCommitWriteV6 hpsi (C e) (C (ring.rightNeighbor e)) := by
                  unfold rowV10b rowV9 rowV8 rowV7
                  rw [if_neg hh, if_neg hb, if_neg hst, if_neg hfL, if_neg hfR, if_neg hmaf,
                    if_neg (armA_needs_leader hpsi hwidth hle _ _ hl), if_neg (armB_needs_leader _ _ hr),
                    if_neg (delete_needs_leader hpsi hwidth hle _ _ hl),
                    if_neg (pendingHold_needs_leader hpsi hwidth hle _ _ hl),
                    if_neg (pendingAbort_needs_leader hpsi hwidth hle _ _ hl), if_pos hmc]
                have hz : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) := by
                  apply notZeroRefresh_of_left_role
                  rw [hrowb, hrole]
                  intro hx
                  have hx' : SpliceRole.none = SpliceRole.predecessorArmed := hx
                  cases hx'
                have hrow : role (rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).1.carrier = .none := by
                  rw [rowV10d_of_none hpsi hwidth hle _ _ hnf hov how hop, rowV10c_of_notZero hpsi hwidth hle _ _ hz, hrowb]
                  rfl
                rw [h] at hrow
                simp only at hrow
                rw [hrole] at hrow
                cases hrow
              · -- pending predecessor on the left needs a reserved front on its right
                have hb := hS.2.2 e hrole hp
                have := hb.1.1
                rw [h4] at this
                cases this
          | victimArmed =>
              cases hp : (C e).carrier.repairPending
              · exact absurd (Or.inl ⟨hrole, hp⟩) h7
              · exact ⟨hrole, hp, h4, h5⟩
      · -- settled predecessor on the right: physical step then fence
        left
        have h5' : (C (ring.rightNeighbor e)).carrier.repairPending = false := by
          cases hp : (C (ring.rightNeighbor e)).carrier.repairPending
          · rfl
          · exact absurd hp h5
        rw [stepV10e_of_settledPredFence hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5']
        exact physicalFence_is_physical hpsi hwidth hle ring C e hne
    · left
      rw [stepV10e_of_physical hpsi hwidth hle ring C e hne h h1 h2 h3 h4]
      exact physicalHold_is_physical hpsi hwidth hle ring C e hne
  · -- V10d changes the pair
    rw [stepV10e_of_change hpsi hwidth hle ring C e hne h]
    by_cases g1 : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · right; left
      rw [stepV10d_of_orphanFront hpsi hwidth hle ring C e hne g1]
      have := orphanToFence_potential_drop ring C e g1; omega
    by_cases g2 : OrphanVictimGuard (C e) (C (ring.rightNeighbor e))
    · right; left
      rw [stepV10d_of_orphanVictim hpsi hwidth hle ring C e hne g1 g2]
      have := orphanVictimClear_potential_drop ring C e g2; omega
    by_cases g3 : OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e))
    · right; left
      rw [stepV10d_of_ownedVictim hpsi hwidth hle ring C e hne g1 g2 g3]
      have := fenceFence_potential_drop ring C e hne g3; omega
    by_cases g4 : OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e))
    · right; left
      rw [stepV10d_of_ownerless hpsi hwidth hle ring C e hne g1 g2 g3 g4]
      have := fenceClear_potential_drop ring C e hne g4; omega
    rw [stepV10d_of_none hpsi hwidth hle ring C e hne g1 g2 g3 g4]
    have hrowd := rowV10d_of_none hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) g1 g2 g3 g4
    -- the V10c chain
    by_cases hz : ZeroRefreshOnlyGuardV10c hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
    · exfalso; apply h; rw [hrowd]; simp [rowV10c, hz]
    rw [stepV10c_eq_stepV10b hpsi hwidth hle ring C e hne hz]
    have hrowc := rowV10c_of_notZero hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) hz
    by_cases hh : HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e))
    · right; right; left; exact hh
    rw [stepV10b_eq_stepV9 hpsi hwidth hle ring C e hne hh]
    by_cases hb : HostFenceBusyFrontGuardV9 hpsi (C e) (C (ring.rightNeighbor e))
    · exfalso
      apply g1
      refine ⟨hb.2.2, ?_⟩
      have := hb.1.1
      rw [this]; decide
    rw [stepV9_eq_stepV8 hpsi hwidth hle ring C e hne hb]
    by_cases hst : RightStalePredecessorHoldGuardV8 (C e) (C (ring.rightNeighbor e))
    · exfalso; apply h; rw [hrowd, hrowc]; simp [rowV10b, hh, rowV9, hb, rowV8, hst]
    rw [stepV8_eq_stepV7 hpsi hwidth hle ring C e hne hst]
    have hrow7 : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
        rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) := by
      rw [hrowd, hrowc]; simp only [rowV10b, hh, if_false, rowV9, hb, rowV8, hst]
    by_cases hfL : HostFenceShapeV7 (C e)
    · by_cases hbar : LocalPreparedBarrier hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
      · by_cases htg : HostFenceTargetClearV7 (C (ring.rightNeighbor e))
        · exact absurd ⟨hfL, hbar, htg⟩ hh
        · exfalso; apply h; rw [hrow7]; unfold rowV7; rw [if_pos hfL, if_pos hbar, if_neg htg]; rfl
      · -- fence stop: the fence loses its ticket
        right; left
        have hrowS : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
            (clearTicketV6 (C e), C (ring.rightNeighbor e)) := by
          unfold rowV7; rw [if_pos hfL, if_neg hbar]; rfl
        rw [stepV7_of_left hpsi hwidth hle ring C e hne clearTicketV6 hrowS]
        apply potential_drop_one ring C _ e
        · intro i hi; simp [hi]
        · simp only [eq_self_iff_true, if_true]
          rw [weight_hostFence_clearTicket _ hfL, weight_hostFence _ hfL]; decide
    by_cases hfR : HostFenceShapeV7 (C (ring.rightNeighbor e))
    · exfalso; apply h; rw [hrow7]; unfold rowV7; rw [if_neg hfL, if_pos hfR]; rfl
    by_cases hmaf : MoveAcquireFrontGuardV6 hpsi (C e) (C (ring.rightNeighbor e))
    · right; left
      have hrowM : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
          (setControlV6 (C e) .predecessorArmed true, C (ring.rightNeighbor e)) := by
        unfold rowV7; rw [if_neg hfL, if_neg hfR, if_pos hmaf]; rfl
      rw [stepV7_of_left' hpsi hwidth hle ring C e hne (fun u => setControlV6 u .predecessorArmed true) hrowM]
      apply potential_drop_one ring C _ e
      · intro i hi; simp [hi]
      · simp only [eq_self_iff_true, if_true]
        rw [weight_setControl_pred_pending]
        -- a ticketed reserved front weighs 6
        have h6 : controllerWeightV6 (C e) = 6 := by
          unfold controllerWeightV6; rw [hmaf.1.1, hmaf.1.2, hmaf.2.2.1]
        omega
    have harmA := armA_needs_leader hpsi hwidth hle (C e).carrier (C (ring.rightNeighbor e)).carrier hl
    have harmB := armB_needs_leader (C e).carrier (C (ring.rightNeighbor e)).carrier hr
    have hdel := delete_needs_leader hpsi hwidth hle (C e).carrier (C (ring.rightNeighbor e)).carrier hl
    have hph := pendingHold_needs_leader hpsi hwidth hle (C e).carrier (C (ring.rightNeighbor e)).carrier hl
    have hpa := pendingAbort_needs_leader hpsi hwidth hle (C e).carrier (C (ring.rightNeighbor e)).carrier hl
    have hpre : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
        (if MoveCommitGuard (C e).carrier (C (ring.rightNeighbor e)).carrier then
          moveCommitWriteV6 hpsi (C e) (C (ring.rightNeighbor e))
        else if MoveStopGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier then
          moveStopWriteV6 (C e) (C (ring.rightNeighbor e))
        else if MoveSeekGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier then
          moveSeekWriteV6 (C e) (C (ring.rightNeighbor e))
        else if MoveSeekHoldGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier then
          moveSeekHoldWriteV6 (C e) (C (ring.rightNeighbor e))
        else if PendingOwnerAbortGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier then
          pendingOwnerAbortWriteV6 (C e) (C (ring.rightNeighbor e))
        else if role (C e).carrier = .predecessorArmed /\ (C e).carrier.repairPending = true then
          pendingOwnerHoldWriteV6 (C e) (C (ring.rightNeighbor e))
        else if MoveAcquireLegacyGuardV6 (C e) (C (ring.rightNeighbor e)) then
          moveAcquireLegacyWriteV6 (C e) (C (ring.rightNeighbor e))
        else if MoveAcquireAbortGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier then
          moveAcquireAbortWriteV6 (C e) (C (ring.rightNeighbor e))
        else if OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier then
          orphanReservedFrontWriteV6 (C e) (C (ring.rightNeighbor e))
        else if ReservedFrontHoldGuard (C e).carrier then
          reservedFrontHoldWriteV6 (C e) (C (ring.rightNeighbor e))
        else if VictimRightScrubGuardV6 (C (ring.rightNeighbor e)) then
          victimRightScrubWriteV6 (C e) (C (ring.rightNeighbor e))
        else if VictimLeftScrubGuardV6 (C e) then
          victimLeftScrubWriteV6 (C e) (C (ring.rightNeighbor e))
        else if FrontRightScrubGuardV6 (C (ring.rightNeighbor e)) then
          frontRightScrubWriteV6 (C e) (C (ring.rightNeighbor e))
        else if MalformedLeftPendingGuardV6 (C e) then
          malformedLeftPendingWriteV6 (C e) (C (ring.rightNeighbor e))
        else if MalformedRightPendingGuardV6 (C (ring.rightNeighbor e)) then
          malformedRightPendingWriteV6 (C e) (C (ring.rightNeighbor e))
        else if role (C e).carrier = .predecessorArmed then
          predecessorLeftScrubWriteV6 (C e) (C (ring.rightNeighbor e))
        else if role (C e).carrier = .front then
          leftFrontHoldWriteV6 (C e) (C (ring.rightNeighbor e))
        else if MarkedHoldGuardV6 (C e) (C (ring.rightNeighbor e)) then
          markedHoldWriteV6 (C e) (C (ring.rightNeighbor e))
        else ordinaryHostWriteV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))) := by
      unfold rowV7
      rw [if_neg hfL, if_neg hfR, if_neg hmaf, if_neg harmA, if_neg harmB, if_neg hdel, if_neg hph, if_neg hpa]
    -- helper: an identity row contradicts the change
    have hid : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e)) → False := by
      intro hi; apply h; rw [hrow7]; exact hi
    by_cases hmc : MoveCommitGuard (C e).carrier (C (ring.rightNeighbor e)).carrier
    · right; left
      rw [if_pos hmc] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply drop_of_pair ring C e hne
      simp only [moveCommitWriteV6]
      rw [weight_clear]
      have hl3 := weight_settledPred (C e) hmc.1 hmc.2.1
      have hr4 : 4 ≤ controllerWeightV6 (C (ring.rightNeighbor e)) := by
        unfold controllerWeightV6; rw [hmc.2.2.1, hmc.2.2.2.1]; cases (C (ring.rightNeighbor e)).acquireTicket <;> decide
      have hw : controllerWeightV6 (withCarrierClearTicketV6 (C (ring.rightNeighbor e))
          (setControl (repairResponder hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier) .predecessorArmed false)) = 3 := rfl
      rw [hw]; omega
    rw [if_neg hmc] at hpre
    by_cases hms : MoveStopGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
    · right; left
      rw [if_pos hms] at hpre
      have hw : moveStopWriteV6 (C e) (C (ring.rightNeighbor e)) =
          (clearControlV6 (C e), clearTicketV6 (C (ring.rightNeighbor e))) := by simp [moveStopWriteV6, hr]
      rw [hw] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply drop_of_pair ring C e hne
      simp only
      rw [weight_clear, weight_RFHG_clearTicket _ hms.2.2.1]
      have hl3 := weight_settledPred (C e) hms.1 hms.2.1
      have hr6 := weight_RFHG_ge _ hms.2.2.1
      omega
    rw [if_neg hms] at hpre
    by_cases hsk : MoveSeekGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
    · rw [if_pos hsk] at hpre
      cases ht : (C (ring.rightNeighbor e)).acquireTicket
      · right; left
        rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
        apply drop_of_pair ring C e hne
        simp only [moveSeekWriteV6]
        rw [weight_RFHG_setTicket _ hsk.2.2.1, weight_RFHG_unticketed _ hsk.2.2.1 ht]
        omega
      · exfalso; apply hid; rw [hpre]; unfold moveSeekWriteV6
        have : setTicketV6 (C (ring.rightNeighbor e)) true = C (ring.rightNeighbor e) := by
          have hc := ht
          cases hj : C (ring.rightNeighbor e) with
          | mk c t =>
            rw [hj] at hc
            simp only at hc
            subst hc
            rfl
        rw [this]
    rw [if_neg hsk] at hpre
    by_cases hskh : MoveSeekHoldGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · exfalso; apply hid; rw [if_pos hskh] at hpre; exact hpre
    rw [if_neg hskh] at hpre
    by_cases hpoa : PendingOwnerAbortGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · rw [if_pos hpoa] at hpre
      cases ht : (C (ring.rightNeighbor e)).acquireTicket
      · exfalso; apply hid; rw [hpre]; unfold pendingOwnerAbortWriteV6
        have : clearTicketV6 (C (ring.rightNeighbor e)) = C (ring.rightNeighbor e) := by
          have hc := ht
          cases hj : C (ring.rightNeighbor e) with
          | mk c t =>
            rw [hj] at hc
            simp only at hc
            subst hc
            rfl
        rw [this]
      · right; left
        rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
        apply drop_of_pair ring C e hne
        simp only [pendingOwnerAbortWriteV6]
        rw [weight_pendingPred_clearTicket _ hpoa.1 hpoa.2.1, weight_pendingPred_ticketed _ hpoa.1 hpoa.2.1 ht]
        omega
    rw [if_neg hpoa] at hpre
    by_cases hpoh : role (C e).carrier = .predecessorArmed /\ (C e).carrier.repairPending = true
    · exfalso; apply hid; rw [if_pos hpoh] at hpre; exact hpre
    rw [if_neg hpoh] at hpre
    by_cases hmal : MoveAcquireLegacyGuardV6 (C e) (C (ring.rightNeighbor e))
    · right; left
      rw [if_pos hmal] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply drop_of_pair ring C e hne
      simp only [moveAcquireLegacyWriteV6]
      rw [weight_setControl_pred_pending]
      have := weight_pendingVictim_ge (C e) hmal.1.1 hmal.1.2.1
      omega
    rw [if_neg hmal] at hpre
    by_cases hmaa : MoveAcquireAbortGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · rw [if_pos hmaa] at hpre
      cases ht : (C e).acquireTicket
      · exfalso; apply hid; rw [hpre]; unfold moveAcquireAbortWriteV6
        have : clearTicketV6 (C e) = C e := by
          have hc := ht
          cases hj : C e with
          | mk c t =>
            rw [hj] at hc
            simp only at hc
            subst hc
            rfl
        rw [this]
      · right; left
        rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
        apply drop_of_pair ring C e hne
        simp only [moveAcquireAbortWriteV6]
        rw [weight_pendingVictim_clearTicket _ hmaa.1 hmaa.2.1, weight_pendingVictim_ticketed _ hmaa.1 hmaa.2.1 ht]
        omega
    rw [if_neg hmaa] at hpre
    by_cases horf : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · exact absurd horf g1
    rw [if_neg horf] at hpre
    by_cases hrfh : ReservedFrontHoldGuard (C e).carrier
    · exfalso; apply hid; rw [if_pos hrfh] at hpre; exact hpre
    rw [if_neg hrfh] at hpre
    by_cases hvr : VictimRightScrubGuardV6 (C (ring.rightNeighbor e))
    · right; left
      rw [if_pos hvr] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply drop_of_pair ring C e hne
      simp only [victimRightScrubWriteV6]
      rw [weight_clear]
      have := weight_pos_of_role (C (ring.rightNeighbor e)) (by rw [hvr.1]; decide)
      omega
    rw [if_neg hvr] at hpre
    by_cases hvl : VictimLeftScrubGuardV6 (C e)
    · right; left
      rw [if_pos hvl] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply drop_of_pair ring C e hne
      simp only [victimLeftScrubWriteV6]
      rw [weight_clear]
      have := weight_pos_of_role (C e) (by rw [hvl.1]; decide)
      omega
    rw [if_neg hvl] at hpre
    by_cases hfr : FrontRightScrubGuardV6 (C (ring.rightNeighbor e))
    · right; left
      rw [if_pos hfr] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply drop_of_pair ring C e hne
      simp only [frontRightScrubWriteV6]
      rw [weight_clear]
      have := weight_pos_of_role (C (ring.rightNeighbor e)) (by rw [hfr.1]; decide)
      omega
    rw [if_neg hfr] at hpre
    by_cases hml : MalformedLeftPendingGuardV6 (C e)
    · right; left
      rw [if_pos hml] at hpre
      have hnone : role (C e).carrier = .none :=
        B9SpliceV10cWholeStepLeaderless.role_none_of_not _ hml.2.1 hml.2.2.1 hml.2.2.2
      have hw : malformedLeftPendingWriteV6 (C e) (C (ring.rightNeighbor e)) =
          (clearControlV6 (C e), C (ring.rightNeighbor e)) := by
        unfold malformedLeftPendingWriteV6
        rw [B9SpliceV10cRowCertFreeLeft.clearPending_eq_clearControl (C e) hnone]
      rw [hw] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply drop_of_pair ring C e hne
      simp only
      rw [weight_clear]
      have := weight_pos_of_pending (C e) hml.1
      omega
    rw [if_neg hml] at hpre
    by_cases hmr : MalformedRightPendingGuardV6 (C (ring.rightNeighbor e))
    · right; left
      rw [if_pos hmr] at hpre
      have hnone : role (C (ring.rightNeighbor e)).carrier = .none :=
        B9SpliceV10cWholeStepLeaderless.role_none_of_not _ hmr.2.1 hmr.2.2.1 hmr.2.2.2
      have hw : malformedRightPendingWriteV6 (C e) (C (ring.rightNeighbor e)) =
          (C e, clearControlV6 (C (ring.rightNeighbor e))) := by
        unfold malformedRightPendingWriteV6
        rw [B9SpliceV10cRowCertFreeLeft.clearPending_eq_clearControl (C (ring.rightNeighbor e)) hnone]
      rw [hw] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply drop_of_pair ring C e hne
      simp only
      rw [weight_clear]
      have := weight_pos_of_pending (C (ring.rightNeighbor e)) hmr.1
      omega
    rw [if_neg hmr] at hpre
    by_cases hpl : role (C e).carrier = .predecessorArmed
    · right; left
      rw [if_pos hpl] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply drop_of_pair ring C e hne
      simp only [predecessorLeftScrubWriteV6]
      rw [weight_clear]
      have := weight_pos_of_role (C e) (by rw [hpl]; decide)
      omega
    rw [if_neg hpl] at hpre
    by_cases hlf : role (C e).carrier = .front
    · exfalso; apply hid; rw [if_pos hlf] at hpre; exact hpre
    rw [if_neg hlf] at hpre
    by_cases hmk : MarkedHoldGuardV6 (C e) (C (ring.rightNeighbor e))
    · exfalso; apply hid; rw [if_pos hmk] at hpre; exact hpre
    rw [if_neg hmk] at hpre
    -- ordinary host: physical
    left
    rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
    exact ordinaryHost_is_physical hpsi hwidth hle ring C e hne

end B9SpliceV10eClassification
