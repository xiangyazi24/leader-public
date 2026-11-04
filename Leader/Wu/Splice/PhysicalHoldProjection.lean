import Leader.Wu.Splice.PhysicalHoldFirstService
import Leader.Wu.Splice.PhysicalHoldHostStep

set_option autoImplicit false
set_option Elab.async false

/-! # The physical projection of a V10e service: stutter, host step, or commit relabel

On a leaderless safe configuration every V10e service, projected on the bases, is the identity
(a controller-only row), the physical host step at the served edge (a B7 interaction), or the
MOVE-COMMIT relabel of the responder. -/

namespace B9SpliceV10eProjection

open PPLL PPLLDomain PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10d B9SpliceTableV10e
  B9SpliceV10eTransparency B9SpliceV10cChainShapes B9SpliceV10cLeaderlessExclusion
  B9SpliceV10ePhysicalHoldNoBirth B9SpliceV10eHandoffFollowUp B9SpliceV10eClassification
  B9SpliceV10ePhysicalIsB7Step

variable {n psi width kappa tau : Nat}

/-- The MOVE-COMMIT relabel on the projection. -/
def commitProj (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Fin n → ExpiringAgentState psi kappa tau :=
  fun i => if i = ring.rightNeighbor e
    then (repairResponder hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier).splice.base
    else physicalProj C i

/-- A step of the pair shape whose two outputs keep the bases is a projection stutter. -/
theorem proj_id_of_pair (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (a b : R1AgentStateV6 psi kappa tau)
    (ha : a.carrier.splice.base = (C e).carrier.splice.base)
    (hb : b.carrier.splice.base = (C (ring.rightNeighbor e)).carrier.splice.base) :
    physicalProj (fun i => if i = e then a else if i = ring.rightNeighbor e then b else C i) =
      physicalProj C := by
  funext i
  unfold physicalProj
  by_cases hi : i = e
  · subst hi; simpa using ha
  · by_cases hj : i = ring.rightNeighbor e
    · subst hj; simp [hi]; exact hb
    · simp [hi, hj]

theorem proj_id_of_right (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (f : R1AgentStateV6 psi kappa tau → R1AgentStateV6 psi kappa tau)
    (hf : ∀ u, (f u).carrier.splice.base = u.carrier.splice.base) :
    physicalProj (fun i => if i = ring.rightNeighbor e then f (C i) else C i) = physicalProj C := by
  funext i
  unfold physicalProj
  by_cases hj : i = ring.rightNeighbor e
  · subst hj; simp [hf]
  · simp [hj]

/-- The `orphanVictimClearAt` shape (clear the fixed right cell) is a projection stutter. -/
theorem proj_id_vc (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    physicalProj (orphanVictimClearAt ring C e) = physicalProj C := by
  funext i
  unfold physicalProj
  exact vc_base_eq ring C e i

theorem proj_id_of_left (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (f : R1AgentStateV6 psi kappa tau → R1AgentStateV6 psi kappa tau)
    (hf : ∀ u, (f u).carrier.splice.base = u.carrier.splice.base) :
    physicalProj (fun i => if i = e then f (C i) else C i) = physicalProj C := by
  funext i
  unfold physicalProj
  by_cases hi : i = e
  · subst hi; simp [hf]
  · simp [hi]

theorem base_clearControl (u : R1AgentStateV6 psi kappa tau) :
    (clearControlV6 u).carrier.splice.base = u.carrier.splice.base := rfl
theorem base_clearTicket (u : R1AgentStateV6 psi kappa tau) :
    (clearTicketV6 u).carrier.splice.base = u.carrier.splice.base := rfl
theorem base_setTicket (u : R1AgentStateV6 psi kappa tau) (b : Bool) :
    (setTicketV6 u b).carrier.splice.base = u.carrier.splice.base := rfl
theorem base_setControl (u : R1AgentStateV6 psi kappa tau) (r : SpliceRole) (p : Bool) :
    (setControlV6 u r p).carrier.splice.base = u.carrier.splice.base := rfl
theorem base_fenceV6 (u : R1AgentStateV6 psi kappa tau) :
    (fenceV6 u).carrier.splice.base = u.carrier.splice.base := rfl

theorem projection_trichotomy
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7 hpsi ring C) :
    physicalProj (stepV10e hpsi hwidth hle ring C e) = physicalProj C ∨
    physicalProj (stepV10e hpsi hwidth hle ring C e) =
      BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring (physicalProj C) e ∨
    (MoveCommitGuard (C e).carrier (C (ring.rightNeighbor e)).carrier ∧
      physicalProj (stepV10e hpsi hwidth hle ring C e) = commitProj hpsi ring C e) := by
  have hl := hlead e
  have hr := hlead (ring.rightNeighbor e)
  rcases Classical.em (rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e))) with h | h
  · by_cases h1 : VictimRightScrubGuardV6 (C (ring.rightNeighbor e))
    · left; rw [stepV10e_of_victimScrub hpsi hwidth hle ring C e hne h h1]
      exact proj_id_vc ring C e
    by_cases h2 : FrontRightScrubGuardV6 (C (ring.rightNeighbor e))
    · left; rw [stepV10e_of_frontScrub hpsi hwidth hle ring C e hne h h1 h2]
      exact proj_id_vc ring C e
    by_cases h3 : MalformedRightPendingGuardV6 (C (ring.rightNeighbor e))
    · left; rw [stepV10e_of_malformedScrub hpsi hwidth hle ring C e hne h h1 h2 h3]
      exact proj_id_vc ring C e
    by_cases h4 : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed
    · by_cases h5 : (C (ring.rightNeighbor e)).carrier.repairPending = true
      · by_cases h6 : ReservedFrontHoldGuard (C e).carrier
        · left; rw [stepV10e_of_frontOwnedPredClear hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5 h6]
          exact proj_id_vc ring C e
        by_cases h7 : LeftScrubGuardV10e (C e)
        · left; rw [stepV10e_of_leftScrub hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5 h6 h7]
          unfold clearLeftAtV10e
          funext i
          unfold physicalProj
          by_cases hi : i = e
          · subst hi; simp [base_clearControl]
          · simp [hi]
        · left; rw [stepV10e_of_pendingPredHold hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5 h6 h7]
      · right; left
        have h5' : (C (ring.rightNeighbor e)).carrier.repairPending = false := by
          cases hp : (C (ring.rightNeighbor e)).carrier.repairPending
          · rfl
          · exact absurd hp h5
        rw [stepV10e_of_settledPredFence hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5']
        exact physicalFence_projects_to_hostStep hpsi hwidth hle ring C e hne
    · right; left
      rw [stepV10e_of_physical hpsi hwidth hle ring C e hne h h1 h2 h3 h4]
      exact physicalHold_projects_to_hostStep hpsi hwidth hle ring C e hne
  · rw [stepV10e_of_change hpsi hwidth hle ring C e hne h]
    by_cases g1 : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · left; rw [stepV10d_of_orphanFront hpsi hwidth hle ring C e hne g1]
      funext i; unfold physicalProj; exact base_eq ring C e i
    by_cases g2 : OrphanVictimGuard (C e) (C (ring.rightNeighbor e))
    · left; rw [stepV10d_of_orphanVictim hpsi hwidth hle ring C e hne g1 g2]
      funext i; unfold physicalProj; exact vc_base_eq ring C e i
    by_cases g3 : OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e))
    · left; rw [stepV10d_of_ownedVictim hpsi hwidth hle ring C e hne g1 g2 g3]
      funext i; unfold physicalProj; exact ff_base_eq ring C e i
    by_cases g4 : OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e))
    · left; rw [stepV10d_of_ownerless hpsi hwidth hle ring C e hne g1 g2 g3 g4]
      funext i; unfold physicalProj; exact fc_base_eq ring C e i
    rw [stepV10d_of_none hpsi hwidth hle ring C e hne g1 g2 g3 g4]
    have hrowd := rowV10d_of_none hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) g1 g2 g3 g4
    by_cases hz : ZeroRefreshOnlyGuardV10c hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
    · exfalso; apply h; rw [hrowd]; simp [rowV10c, hz]
    rw [stepV10c_eq_stepV10b hpsi hwidth hle ring C e hne hz]
    have hrowc := rowV10c_of_notZero hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) hz
    by_cases hh : HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e))
    · left
      have hrowb := rowV10b_of_handoff hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) hh
      have hshape : stepV10b hpsi hwidth hle ring C e = fun i =>
          if i = e then setControlV6 (C e) .predecessorArmed false
          else if i = ring.rightNeighbor e then setControlV6 (C (ring.rightNeighbor e)) .front true else C i := by
        funext i; simp only [stepV10b, hne, if_false, hrowb, hostFenceHandoffWriteV10b]
      rw [hshape]
      exact proj_id_of_pair ring C e _ _ (base_setControl _ _ _) (base_setControl _ _ _)
    rw [stepV10b_eq_stepV9 hpsi hwidth hle ring C e hne hh]
    by_cases hb : HostFenceBusyFrontGuardV9 hpsi (C e) (C (ring.rightNeighbor e))
    · exfalso; apply g1; refine ⟨hb.2.2, ?_⟩; have := hb.1.1; rw [this]; decide
    rw [stepV9_eq_stepV8 hpsi hwidth hle ring C e hne hb]
    by_cases hst : RightStalePredecessorHoldGuardV8 (C e) (C (ring.rightNeighbor e))
    · exfalso; apply h; rw [hrowd, hrowc]; simp [rowV10b, hh, rowV9, hb, rowV8, hst]
    rw [stepV8_eq_stepV7 hpsi hwidth hle ring C e hne hst]
    have hrow7 : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
        rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) := by
      rw [hrowd, hrowc]; simp only [rowV10b, hh, if_false, rowV9, hb, rowV8, hst]
    have hid : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e)) → False := by
      intro hi; apply h; rw [hrow7]; exact hi
    by_cases hfL : HostFenceShapeV7 (C e)
    · by_cases hbar : LocalPreparedBarrier hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
      · by_cases htg : HostFenceTargetClearV7 (C (ring.rightNeighbor e))
        · exact absurd ⟨hfL, hbar, htg⟩ hh
        · exfalso; apply hid; unfold rowV7; rw [if_pos hfL, if_pos hbar, if_neg htg]; rfl
      · left
        have hrowS : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
            (clearTicketV6 (C e), C (ring.rightNeighbor e)) := by
          unfold rowV7; rw [if_pos hfL, if_neg hbar]; rfl
        rw [stepV7_of_left hpsi hwidth hle ring C e hne clearTicketV6 hrowS]
        exact proj_id_of_left ring C e clearTicketV6 base_clearTicket
    by_cases hfR : HostFenceShapeV7 (C (ring.rightNeighbor e))
    · exfalso; apply hid; unfold rowV7; rw [if_neg hfL, if_pos hfR]; rfl
    by_cases hmaf : MoveAcquireFrontGuardV6 hpsi (C e) (C (ring.rightNeighbor e))
    · left
      have hrowM : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
          (setControlV6 (C e) .predecessorArmed true, C (ring.rightNeighbor e)) := by
        unfold rowV7; rw [if_neg hfL, if_neg hfR, if_pos hmaf]; rfl
      rw [stepV7_of_left' hpsi hwidth hle ring C e hne (fun u => setControlV6 u .predecessorArmed true) hrowM]
      funext i; unfold physicalProj
      by_cases hi : i = e
      · subst hi; simp only [eq_self_iff_true, if_true]; rfl
      · simp [hi]
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
    -- generic closer for control-only pairs
    have pairId : ∀ (a b : R1AgentStateV6 psi kappa tau),
        rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (a, b) →
        a.carrier.splice.base = (C e).carrier.splice.base →
        b.carrier.splice.base = (C (ring.rightNeighbor e)).carrier.splice.base →
        physicalProj (stepV7 hpsi hwidth hle ring C e) = physicalProj C := by
      intro a b hrow ha hb
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hrow]
      exact proj_id_of_pair ring C e a b ha hb
    by_cases hmc : MoveCommitGuard (C e).carrier (C (ring.rightNeighbor e)).carrier
    · right; right
      refine ⟨hmc, ?_⟩
      rw [if_pos hmc] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      funext i
      unfold physicalProj commitProj
      by_cases hi : i = e
      · subst hi
        simp only [eq_self_iff_true, if_true, moveCommitWriteV6]
        rw [if_neg (Ne.symm hne)]
        rfl
      · by_cases hj : i = ring.rightNeighbor e
        · subst hj; simp only [hi, if_false, eq_self_iff_true, if_true, moveCommitWriteV6]; rfl
        · simp [hi, hj, physicalProj]
    rw [if_neg hmc] at hpre
    by_cases hms : MoveStopGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
    · left; rw [if_pos hms] at hpre
      have hw : moveStopWriteV6 (C e) (C (ring.rightNeighbor e)) =
          (clearControlV6 (C e), clearTicketV6 (C (ring.rightNeighbor e))) := by simp [moveStopWriteV6, hr]
      rw [hw] at hpre
      exact pairId _ _ hpre rfl rfl
    rw [if_neg hms] at hpre
    by_cases hsk : MoveSeekGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
    · left; rw [if_pos hsk] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hsk] at hpre
    by_cases hskh : MoveSeekHoldGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · left; rw [if_pos hskh] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hskh] at hpre
    by_cases hpoa : PendingOwnerAbortGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · left; rw [if_pos hpoa] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hpoa] at hpre
    by_cases hpoh : role (C e).carrier = .predecessorArmed /\ (C e).carrier.repairPending = true
    · left; rw [if_pos hpoh] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hpoh] at hpre
    by_cases hmal : MoveAcquireLegacyGuardV6 (C e) (C (ring.rightNeighbor e))
    · left; rw [if_pos hmal] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hmal] at hpre
    by_cases hmaa : MoveAcquireAbortGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · left; rw [if_pos hmaa] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hmaa] at hpre
    by_cases horf : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · exact absurd horf g1
    rw [if_neg horf] at hpre
    by_cases hrfh : ReservedFrontHoldGuard (C e).carrier
    · left; rw [if_pos hrfh] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hrfh] at hpre
    by_cases hvr : VictimRightScrubGuardV6 (C (ring.rightNeighbor e))
    · left; rw [if_pos hvr] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hvr] at hpre
    by_cases hvl : VictimLeftScrubGuardV6 (C e)
    · left; rw [if_pos hvl] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hvl] at hpre
    by_cases hfr : FrontRightScrubGuardV6 (C (ring.rightNeighbor e))
    · left; rw [if_pos hfr] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hfr] at hpre
    by_cases hml : MalformedLeftPendingGuardV6 (C e)
    · left; rw [if_pos hml] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hml] at hpre
    by_cases hmr : MalformedRightPendingGuardV6 (C (ring.rightNeighbor e))
    · left; rw [if_pos hmr] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hmr] at hpre
    by_cases hpl : role (C e).carrier = .predecessorArmed
    · left; rw [if_pos hpl] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hpl] at hpre
    by_cases hlf : role (C e).carrier = .front
    · left; rw [if_pos hlf] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hlf] at hpre
    by_cases hmk : MarkedHoldGuardV6 (C e) (C (ring.rightNeighbor e))
    · left; rw [if_pos hmk] at hpre; exact pairId _ _ hpre rfl rfl
    rw [if_neg hmk] at hpre
    right; left
    rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
    exact physicalService_is_hostStep hpsi hwidth hle ring C _ e
      (ordinaryHost_is_physical hpsi hwidth hle ring C e hne)
      (fun i hi hj => by simp [hi, hj])

end B9SpliceV10eProjection
