import Leader.Wu.Splice.PhysicalHoldProjection
import Leader.Wu.Splice.ComposedEvents
import Leader.Wu.Splice.PhysicalHoldPairWeight


set_option autoImplicit false
set_option Elab.async false


namespace B9SpliceGarbageCount


open PPLL PPLLDomain PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10d B9SpliceTableV10e
  B9SpliceV10eTransparency B9SpliceV10cChainShapes B9SpliceV10cLeaderlessExclusion
  B9SpliceV10eHandoffFollowUp B9SpliceV10eProjection


variable {n psi width kappa tau : Nat}


def garbage (u : R1AgentStateV6 psi kappa tau) : Nat :=
  if role u.carrier = .victimArmed ∨
      (role u.carrier = .predecessorArmed ∧ u.carrier.repairPending = true)
  then 1 else 0


def garbageCount (C : R1ConfigV6 n psi kappa tau) : Nat :=
  (List.ofFn (fun i => garbage (C i))).sum



theorem role_setControl (u : R1AgentState psi kappa tau) (r : SpliceRole) (p : Bool) :
    role (setControl u r p) = r := rfl
theorem repairPending_setControl (u : R1AgentState psi kappa tau) (r : SpliceRole) (p : Bool) :
    (setControl u r p).repairPending = p := rfl
theorem carrier_setTicketV6 (u : R1AgentStateV6 psi kappa tau) (b : Bool) :
    (setTicketV6 u b).carrier = u.carrier := rfl
theorem carrier_setControlV6 (u : R1AgentStateV6 psi kappa tau) (r : SpliceRole) (p : Bool) :
    (setControlV6 u r p).carrier = setControl u.carrier r p := rfl

@[simp] theorem garbage_setTicketV6
    (u : R1AgentStateV6 psi kappa tau) (b : Bool) :
    garbage (setTicketV6 u b) = garbage u := by
  unfold garbage; rw [carrier_setTicketV6]


@[simp] theorem garbage_clearTicketV6
    (u : R1AgentStateV6 psi kappa tau) :
    garbage (clearTicketV6 u) = garbage u := by
  simp [clearTicketV6]


@[simp] theorem garbage_setControl_none
    (u : R1AgentStateV6 psi kappa tau) (b : Bool) :
    garbage (setControlV6 u .none b) = 0 := by
  unfold garbage; rw [carrier_setControlV6, role_setControl, repairPending_setControl]; simp


@[simp] theorem garbage_setControl_front
    (u : R1AgentStateV6 psi kappa tau) (b : Bool) :
    garbage (setControlV6 u .front b) = 0 := by
  unfold garbage; rw [carrier_setControlV6, role_setControl, repairPending_setControl]; simp


@[simp] theorem garbage_setControl_pred_false
    (u : R1AgentStateV6 psi kappa tau) :
    garbage (setControlV6 u .predecessorArmed false) = 0 := by
  unfold garbage; rw [carrier_setControlV6, role_setControl, repairPending_setControl]; simp


@[simp] theorem garbage_setControl_pred_true
    (u : R1AgentStateV6 psi kappa tau) :
    garbage (setControlV6 u .predecessorArmed true) = 1 := by
  unfold garbage; rw [carrier_setControlV6, role_setControl, repairPending_setControl]; simp


@[simp] theorem garbage_clearControlV6
    (u : R1AgentStateV6 psi kappa tau) :
    garbage (clearControlV6 u) = 0 := by
  simp [clearControlV6]


@[simp] theorem garbage_fenceV6
    (u : R1AgentStateV6 psi kappa tau) :
    garbage (fenceV6 u) = 0 := by
  simp [fenceV6]


@[simp] theorem garbage_withCarrier_pred_false
    (u : R1AgentStateV6 psi kappa tau)
    (v : R1AgentStateV4 psi kappa tau) :
    garbage (withCarrierClearTicketV6 u (setControl v .predecessorArmed false)) = 0 := by
  simp [garbage, withCarrierClearTicketV6, setControl, role]


theorem garbage_clearPending_le
    (u : R1AgentStateV6 psi kappa tau) :
    garbage (clearPendingV6 u) ≤ garbage u := by
  cases hrole : role u.carrier <;>
    cases hp : u.carrier.repairPending <;>
    simp [garbage, hrole, hp]


theorem garbage_victim
    (u : R1AgentStateV6 psi kappa tau)
    (h : role u.carrier = .victimArmed) : garbage u = 1 := by
  simp [garbage, h]


@[simp] theorem garbage_physicalHold_left
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    garbage (physicalHoldV6 hpsi hwidth hle l r).1 = garbage l := by
  unfold garbage
  rw [physicalHold_role_left hpsi hwidth hle l r,
    physicalHold_pending_left hpsi hwidth hle l r]


@[simp] theorem garbage_physicalHold_right
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    garbage (physicalHoldV6 hpsi hwidth hle l r).2 = garbage r := by
  unfold garbage
  rw [physicalHold_role_right hpsi hwidth hle l r,
    physicalHold_pending_right hpsi hwidth hle l r]


@[simp] theorem garbage_ordinaryHost_left
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    garbage (ordinaryHostWriteV7 hpsi hwidth hle l r).1 = garbage l := by
  have hc := physicalHold_carriers_eq_ordinaryHost hpsi hwidth hle l r
  have hr : role (ordinaryHostWriteV7 hpsi hwidth hle l r).1.carrier = role l.carrier := by
    rw [← hc.1]
    exact physicalHold_role_left hpsi hwidth hle l r
  have hp : (ordinaryHostWriteV7 hpsi hwidth hle l r).1.carrier.repairPending =
      l.carrier.repairPending := by
    rw [← hc.1]
    exact physicalHold_pending_left hpsi hwidth hle l r
  unfold garbage
  rw [hr, hp]


@[simp] theorem garbage_ordinaryHost_right
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    garbage (ordinaryHostWriteV7 hpsi hwidth hle l r).2 = garbage r := by
  have hc := physicalHold_carriers_eq_ordinaryHost hpsi hwidth hle l r
  have hr : role (ordinaryHostWriteV7 hpsi hwidth hle l r).2.carrier = role r.carrier := by
    rw [← hc.2]
    exact physicalHold_role_right hpsi hwidth hle l r
  have hp : (ordinaryHostWriteV7 hpsi hwidth hle l r).2.carrier.repairPending =
      r.carrier.repairPending := by
    rw [← hc.2]
    exact physicalHold_pending_right hpsi hwidth hle l r
  unfold garbage
  rw [hr, hp]


theorem ofFn_sum_two_cells
    (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (hother : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i) :
    garbageCount D + garbage (C e) + garbage (C (ring.rightNeighbor e)) =
      garbageCount C + garbage (D e) + garbage (D (ring.rightNeighbor e)) := by
  let M : R1ConfigV6 n psi kappa tau := fun i => if i = e then D e else C i
  have hs1 := B9SpliceV10ePairWeight.ofFn_sum_exchange
    (fun i => garbage (M i)) (fun i => garbage (C i)) e
    (fun i hi => by simp [M, hi])
  have hs2 := B9SpliceV10ePairWeight.ofFn_sum_exchange
    (fun i => garbage (D i)) (fun i => garbage (M i))
    (ring.rightNeighbor e) (fun i hi => by
      by_cases hie : i = e
      · subst hie; simp [M]
      · simp [M, hie, hother i hie hi])
  have hMe : M e = D e := by simp [M]
  have hMj : M (ring.rightNeighbor e) = C (ring.rightNeighbor e) := by
    simp [M, hne]
  unfold garbageCount
  simp only [hMe, hMj] at hs1 hs2
  omega


theorem garbageCount_le_of_pair
    (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (hother : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i)
    (hpair : garbage (D e) + garbage (D (ring.rightNeighbor e)) ≤
      garbage (C e) + garbage (C (ring.rightNeighbor e))) :
    garbageCount D ≤ garbageCount C := by
  have hsum := ofFn_sum_two_cells ring C D e hne hother
  omega


theorem garbageCount_pair_update_le
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (a b : R1AgentStateV6 psi kappa tau)
    (hab : garbage a + garbage b ≤
      garbage (C e) + garbage (C (ring.rightNeighbor e))) :
    garbageCount (fun i => if i = e then a
      else if i = ring.rightNeighbor e then b else C i) ≤ garbageCount C := by
  apply garbageCount_le_of_pair ring C _ e hne
  · intro i hi hj
    simp [hi, hj]
  · simpa [hne, Ne.symm hne] using hab


theorem garbageCount_left_update_le
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (a : R1AgentStateV6 psi kappa tau)
    (ha : garbage a ≤ garbage (C e)) :
    garbageCount (fun i => if i = e then a else C i) ≤ garbageCount C := by
  apply garbageCount_le_of_pair ring C _ e hne
  · intro i hi _hj
    simp [hi]
  · have hpair := Nat.add_le_add_right ha (garbage (C (ring.rightNeighbor e)))
    simpa [hne, Ne.symm hne] using hpair


theorem garbageCount_right_update_le
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (b : R1AgentStateV6 psi kappa tau)
    (hb : garbage b ≤ garbage (C (ring.rightNeighbor e))) :
    garbageCount (fun i => if i = ring.rightNeighbor e then b else C i) ≤ garbageCount C := by
  apply garbageCount_le_of_pair ring C _ e hne
  · intro i _hi hj
    simp [hj]
  · have hpair := Nat.add_le_add_left hb (garbage (C e))
    simpa [hne, Ne.symm hne] using hpair


theorem stepV10e_garbageCount_le
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7 hpsi ring C) :
    garbageCount (stepV10e hpsi hwidth hle ring C e) ≤ garbageCount C := by
  have hl := hlead e
  have hr := hlead (ring.rightNeighbor e)
  rcases Classical.em
      (rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
        (C e, C (ring.rightNeighbor e))) with h | h
  · by_cases h1 : VictimRightScrubGuardV6 (C (ring.rightNeighbor e))
    · rw [stepV10e_of_victimScrub hpsi hwidth hle ring C e hne h h1]
      unfold orphanVictimClearAt
      apply garbageCount_right_update_le ring C e hne
      simp
    by_cases h2 : FrontRightScrubGuardV6 (C (ring.rightNeighbor e))
    · rw [stepV10e_of_frontScrub hpsi hwidth hle ring C e hne h h1 h2]
      unfold orphanVictimClearAt
      apply garbageCount_right_update_le ring C e hne
      simp
    by_cases h3 : MalformedRightPendingGuardV6 (C (ring.rightNeighbor e))
    · rw [stepV10e_of_malformedScrub hpsi hwidth hle ring C e hne h h1 h2 h3]
      unfold orphanVictimClearAt
      apply garbageCount_right_update_le ring C e hne
      simp
    by_cases h4 : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed
    · by_cases h5 : (C (ring.rightNeighbor e)).carrier.repairPending = true
      · by_cases h6 : ReservedFrontHoldGuard (C e).carrier
        · rw [stepV10e_of_frontOwnedPredClear hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5 h6]
          unfold orphanVictimClearAt
          apply garbageCount_right_update_le ring C e hne
          simp
        by_cases h7 : LeftScrubGuardV10e (C e)
        · rw [stepV10e_of_leftScrub hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5 h6 h7]
          unfold clearLeftAtV10e
          apply garbageCount_left_update_le ring C e hne
          simp
        · rw [stepV10e_of_pendingPredHold hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5 h6 h7]
          exact Nat.le_refl _
      · have h5' : (C (ring.rightNeighbor e)).carrier.repairPending = false := by
          cases hp : (C (ring.rightNeighbor e)).carrier.repairPending
          · rfl
          · exact absurd hp h5
        rw [stepV10e_of_settledPredFence hpsi hwidth hle ring C e hne h h1 h2 h3 h4 h5']
        unfold physicalFenceAt
        dsimp only
        apply garbageCount_pair_update_le ring C e hne
        simp <;> omega
    · rw [stepV10e_of_physical hpsi hwidth hle ring C e hne h h1 h2 h3 h4]
      unfold physicalHoldAt
      dsimp only
      apply garbageCount_pair_update_le ring C e hne
      simp
  · rw [stepV10e_of_change hpsi hwidth hle ring C e hne h]
    by_cases g1 : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · rw [stepV10d_of_orphanFront hpsi hwidth hle ring C e hne g1]
      unfold orphanToFenceAt
      apply garbageCount_right_update_le ring C e hne
      simp
    by_cases g2 : OrphanVictimGuard (C e) (C (ring.rightNeighbor e))
    · rw [stepV10d_of_orphanVictim hpsi hwidth hle ring C e hne g1 g2]
      unfold orphanVictimClearAt
      apply garbageCount_right_update_le ring C e hne
      simp
    by_cases g3 : OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e))
    · rw [stepV10d_of_ownedVictim hpsi hwidth hle ring C e hne g1 g2 g3]
      unfold fenceFenceAt
      apply garbageCount_pair_update_le ring C e hne
      simp
    by_cases g4 : OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e))
    · rw [stepV10d_of_ownerless hpsi hwidth hle ring C e hne g1 g2 g3 g4]
      unfold fenceClearAt
      apply garbageCount_pair_update_le ring C e hne
      simp
    rw [stepV10d_of_none hpsi hwidth hle ring C e hne g1 g2 g3 g4]
    have hrowd := rowV10d_of_none hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) g1 g2 g3 g4
    by_cases hz : ZeroRefreshOnlyGuardV10c hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
    · exfalso
      apply h
      rw [hrowd]
      simp [rowV10c, hz]
    rw [stepV10c_eq_stepV10b hpsi hwidth hle ring C e hne hz]
    have hrowc := rowV10c_of_notZero hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) hz
    by_cases hh : HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e))
    · have hrowb := rowV10b_of_handoff hpsi hwidth hle
        (C e) (C (ring.rightNeighbor e)) hh
      have hshape : stepV10b hpsi hwidth hle ring C e = fun i =>
          if i = e then setControlV6 (C e) .predecessorArmed false
          else if i = ring.rightNeighbor e then
            setControlV6 (C (ring.rightNeighbor e)) .front true
          else C i := by
        funext i
        simp only [stepV10b, hne, if_false, hrowb, hostFenceHandoffWriteV10b]
      rw [hshape]
      apply garbageCount_pair_update_le ring C e hne
      simp
    rw [stepV10b_eq_stepV9 hpsi hwidth hle ring C e hne hh]
    by_cases hb : HostFenceBusyFrontGuardV9 hpsi (C e) (C (ring.rightNeighbor e))
    · exfalso
      apply g1
      refine ⟨hb.2.2, ?_⟩
      have ht := hb.1.1
      rw [ht]
      decide
    rw [stepV9_eq_stepV8 hpsi hwidth hle ring C e hne hb]
    by_cases hst : RightStalePredecessorHoldGuardV8 (C e) (C (ring.rightNeighbor e))
    · exfalso
      apply h
      rw [hrowd, hrowc]
      simp [rowV10b, hh, rowV9, hb, rowV8, hst]
    rw [stepV8_eq_stepV7 hpsi hwidth hle ring C e hne hst]
    have hrow7 : rowV10d hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
        rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) := by
      rw [hrowd, hrowc]
      simp only [rowV10b, hh, if_false, rowV9, hb, rowV8, hst]
    have hid : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
        (C e, C (ring.rightNeighbor e)) → False := by
      intro hi
      apply h
      rw [hrow7]
      exact hi
    by_cases hfL : HostFenceShapeV7 (C e)
    · by_cases hbar : LocalPreparedBarrier hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
      · by_cases htg : HostFenceTargetClearV7 (C (ring.rightNeighbor e))
        · exact absurd ⟨hfL, hbar, htg⟩ hh
        · exfalso
          apply hid
          unfold rowV7
          rw [if_pos hfL, if_pos hbar, if_neg htg]
          rfl
      · have hrowS : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
            (clearTicketV6 (C e), C (ring.rightNeighbor e)) := by
          unfold rowV7
          rw [if_pos hfL, if_neg hbar]
          rfl
        rw [stepV7_of_left hpsi hwidth hle ring C e hne clearTicketV6 hrowS]
        apply garbageCount_le_of_pair ring C _ e hne
        · intro i hi _hj
          simp [hi]
        · simp [hne, Ne.symm hne]
    by_cases hfR : HostFenceShapeV7 (C (ring.rightNeighbor e))
    · exfalso
      apply hid
      unfold rowV7
      rw [if_neg hfL, if_pos hfR]
      rfl
    by_cases hmaf : MoveAcquireFrontGuardV6 hpsi (C e) (C (ring.rightNeighbor e))
    · have hrowM : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
          (setControlV6 (C e) .predecessorArmed true, C (ring.rightNeighbor e)) := by
        unfold rowV7
        rw [if_neg hfL, if_neg hfR, if_pos hmaf]
        rfl
      rw [stepV7_of_left' hpsi hwidth hle ring C e hne
        (fun u => setControlV6 u .predecessorArmed true) hrowM]
      exfalso
      apply g1
      refine ⟨hmaf.2.2.2.1, ?_⟩
      intro hp
      have hf := hmaf.1.1
      rw [hp] at hf
      cases hf
    have harmA := armA_needs_leader hpsi hwidth hle
      (C e).carrier (C (ring.rightNeighbor e)).carrier hl
    have harmB := armB_needs_leader
      (C e).carrier (C (ring.rightNeighbor e)).carrier hr
    have hdel := delete_needs_leader hpsi hwidth hle
      (C e).carrier (C (ring.rightNeighbor e)).carrier hl
    have hph := pendingHold_needs_leader hpsi hwidth hle
      (C e).carrier (C (ring.rightNeighbor e)).carrier hl
    have hpa := pendingAbort_needs_leader hpsi hwidth hle
      (C e).carrier (C (ring.rightNeighbor e)).carrier hl
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
        else if role (C e).carrier = .predecessorArmed ∧ (C e).carrier.repairPending = true then
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
      rw [if_neg hfL, if_neg hfR, if_neg hmaf,
        if_neg harmA, if_neg harmB, if_neg hdel, if_neg hph, if_neg hpa]
    by_cases hmc : MoveCommitGuard (C e).carrier (C (ring.rightNeighbor e)).carrier
    · rw [if_pos hmc] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      simp only [moveCommitWriteV6, garbage_clearControlV6, garbage_withCarrier_pred_false]
      exact Nat.zero_le _
    rw [if_neg hmc] at hpre
    by_cases hms : MoveStopGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
    · rw [if_pos hms] at hpre
      have hw : moveStopWriteV6 (C e) (C (ring.rightNeighbor e)) =
          (clearControlV6 (C e), clearTicketV6 (C (ring.rightNeighbor e))) := by
        simp [moveStopWriteV6, hr]
      rw [hw] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      simp <;> omega
    rw [if_neg hms] at hpre
    by_cases hsk : MoveSeekGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
    · rw [if_pos hsk] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      simp [moveSeekWriteV6]
    rw [if_neg hsk] at hpre
    by_cases hskh : MoveSeekHoldGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · rw [if_pos hskh] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      simp [moveSeekHoldWriteV6]
    rw [if_neg hskh] at hpre
    by_cases hpoa : PendingOwnerAbortGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · rw [if_pos hpoa] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      simp [pendingOwnerAbortWriteV6]
    rw [if_neg hpoa] at hpre
    by_cases hpoh : role (C e).carrier = .predecessorArmed ∧ (C e).carrier.repairPending = true
    · rw [if_pos hpoh] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      simp [pendingOwnerHoldWriteV6]
    rw [if_neg hpoh] at hpre
    by_cases hmal : MoveAcquireLegacyGuardV6 (C e) (C (ring.rightNeighbor e))
    · rw [if_pos hmal] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      have hgv : garbage (C e) = 1 := garbage_victim (C e) hmal.1.1
      apply garbageCount_pair_update_le ring C e hne
      simp [moveAcquireLegacyWriteV6, hgv]
    rw [if_neg hmal] at hpre
    by_cases hmaa : MoveAcquireAbortGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · rw [if_pos hmaa] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      simp [moveAcquireAbortWriteV6]
    rw [if_neg hmaa] at hpre
    by_cases horf : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
    · exact absurd horf g1
    rw [if_neg horf] at hpre
    by_cases hrfh : ReservedFrontHoldGuard (C e).carrier
    · rw [if_pos hrfh] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      simp [reservedFrontHoldWriteV6]
    rw [if_neg hrfh] at hpre
    by_cases hvr : VictimRightScrubGuardV6 (C (ring.rightNeighbor e))
    · rw [if_pos hvr] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      simp [victimRightScrubWriteV6] <;> omega
    rw [if_neg hvr] at hpre
    by_cases hvl : VictimLeftScrubGuardV6 (C e)
    · rw [if_pos hvl] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      simp [victimLeftScrubWriteV6] <;> omega
    rw [if_neg hvl] at hpre
    by_cases hfr : FrontRightScrubGuardV6 (C (ring.rightNeighbor e))
    · rw [if_pos hfr] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      simp [frontRightScrubWriteV6] <;> omega
    rw [if_neg hfr] at hpre
    by_cases hml : MalformedLeftPendingGuardV6 (C e)
    · rw [if_pos hml] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      have hc := garbage_clearPending_le (C e)
      simp only [malformedLeftPendingWriteV6]
      omega
    rw [if_neg hml] at hpre
    by_cases hmr : MalformedRightPendingGuardV6 (C (ring.rightNeighbor e))
    · rw [if_pos hmr] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      have hc := garbage_clearPending_le (C (ring.rightNeighbor e))
      simp only [malformedRightPendingWriteV6]
      omega
    rw [if_neg hmr] at hpre
    by_cases hpl : role (C e).carrier = .predecessorArmed
    · rw [if_pos hpl] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      simp [predecessorLeftScrubWriteV6] <;> omega
    rw [if_neg hpl] at hpre
    by_cases hlf : role (C e).carrier = .front
    · rw [if_pos hlf] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      simp [leftFrontHoldWriteV6]
    rw [if_neg hlf] at hpre
    by_cases hmk : MarkedHoldGuardV6 (C e) (C (ring.rightNeighbor e))
    · rw [if_pos hmk] at hpre
      rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
      apply garbageCount_pair_update_le ring C e hne
      simp [markedHoldWriteV6]
    rw [if_neg hmk] at hpre
    rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
    apply garbageCount_pair_update_le ring C e hne
    simp


end B9SpliceGarbageCount
