import Leader.Wu.Splice.ZeroRefreshChain
import Leader.Wu.Splice.FenceHandoffAcquireFrontSafe
import Leader.Wu.Splice.OrdinaryHostBirthFollowerDischarged
import Leader.Wu.Splice.OrdinaryHostDeletionSafe

set_option autoImplicit false
set_option Elab.async false

/-! # V10c whole-step safety on leaderless configurations

Walk the V10c priority chain: every level reduces to the next when its guard fails, the
arming rows cannot fire without a leader, every remaining row has its own SpliceSafeV7
preservation theorem, and the final ordinary fallback is reached only on a neutral pair,
where the V8 ordinary-host theorems apply. -/

namespace B9SpliceV10cWholeStepLeaderless

open PPLL PPLLDomain PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceV10cChainShapes B9SpliceV10cLeaderlessExclusion
  B9SpliceV10cRowMoveCommit B9SpliceV10cRowMoveStop B9SpliceV10cRowMoveSeek
  B9SpliceV10cRowPendingOwnerAbort B9SpliceV10cRowMoveAcquireLegacy
  B9SpliceV10cRowMoveAcquireAbort B9SpliceV10cRowCertFreeLeft
  B9SpliceV8OrdinaryHost B9SpliceV10bWholeRow

variable {n psi width kappa tau : Nat}

/-- A role that is not predecessor, front or victim is none. -/
theorem role_none_of_not (r : SpliceRole) (h1 : r ≠ .predecessorArmed) (h2 : r ≠ .front)
    (h3 : r ≠ .victimArmed) : r = .none := by
  cases r with
  | none => rfl
  | predecessorArmed => exact absurd rfl h1
  | victimArmed => exact absurd rfl h3
  | front => exact absurd rfl h2

/-- The zero-refresh row is the identity (ported from B9SpliceV10bCycleCensus onto the
B9SpliceV10cLiveness step). -/
theorem zeroRefresh_step_identity
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hg : ZeroRefreshOnlyGuardV10c hpsi hwidth hle (C e) (C (ring.rightNeighbor e))) :
    stepV10c hpsi hwidth hle ring C e = C := by
  funext i
  by_cases hself : ring.rightNeighbor e = e
  · simp [stepV10c, hself]
  · by_cases hie : i = e
    · subst i; simp [stepV10c, hself, rowV10c, hg]
    · by_cases hij : i = ring.rightNeighbor e
      · subst i; simp [stepV10c, hself, rowV10c, hg, hie]
      · simp [stepV10c, hself, rowV10c, hg, hie, hij]

theorem stepV10c_preserves_spliceSafeV7_leaderless
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7 hpsi ring C) :
    SpliceSafeV7 hpsi ring (stepV10c hpsi hwidth hle ring C e) := by
  by_cases hne : ring.rightNeighbor e = e
  · rw [stepV10c_self hpsi hwidth hle ring C e hne]; exact hS
  have hl := hlead e
  have hr := hlead (ring.rightNeighbor e)
  by_cases hz : ZeroRefreshOnlyGuardV10c hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  · rw [zeroRefresh_step_identity hpsi hwidth hle ring C e hz]; exact hS
  rw [stepV10c_eq_stepV10b hpsi hwidth hle ring C e hne hz]
  by_cases hh : HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e))
  · exact corrected_handoff_preserves_spliceSafeV7 hpsi hwidth hle ring C e hS hh
  have h10 := stepV10b_eq_stepV9 hpsi hwidth hle ring C e hne hh
  rw [h10]
  by_cases hb9 : HostFenceBusyFrontGuardV9 hpsi (C e) (C (ring.rightNeighbor e))
  · exact hostFenceBusyFrontRepair_preserves_spliceSafeV7 hpsi hwidth hle ring C e hS hb9
  have h9 := stepV9_eq_stepV8 hpsi hwidth hle ring C e hne hb9
  rw [h9]
  by_cases hst : RightStalePredecessorHoldGuardV8 (C e) (C (ring.rightNeighbor e))
  · exact rightStalePredecessorHold_preserves_spliceSafeV7 hpsi hwidth hle ring C e hS hst
  have h87 := stepV8_eq_stepV7 hpsi hwidth hle ring C e hne hst
  -- V7 fence rows
  by_cases hfL : HostFenceShapeV7 (C e)
  · rw [h87]
    by_cases hbar : LocalPreparedBarrier hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
    · by_cases htg : HostFenceTargetClearV7 (C (ring.rightNeighbor e))
      · exact hostFenceLeftAdvance_preserves_spliceSafeV7 hpsi hwidth hle ring C e hS hfL hbar htg
      · exact hostFenceLeftHold_preserves_spliceSafeV7 hpsi hwidth hle ring C e hS hfL hbar htg
    · exact hostFenceLeftStop_preserves_spliceSafeV7 hpsi hwidth hle ring C e hS hfL hbar
  by_cases hfR : HostFenceShapeV7 (C (ring.rightNeighbor e))
  · rw [h87]
    exact hostFenceRightHold_preserves_spliceSafeV7 hpsi hwidth hle ring C e hS hfL hfR
  -- MOVE-ACQUIRE-FRONT is proved at the V10b level
  by_cases hmaf : MoveAcquireFrontGuardV6 hpsi (C e) (C (ring.rightNeighbor e))
  · rw [← h9, ← h10]
    exact B9SpliceV10bMoveAcquireFront.moveAcquireFrontBranch_v10b hpsi hwidth hle ring C e hS
      ⟨hh, hb9, hst, hfL, hfR, hmaf⟩
  -- arming rows need a leader
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
    rw [if_neg hfL, if_neg hfR, if_neg hmaf, if_neg harmA, if_neg harmB, if_neg hdel, if_neg hph,
      if_neg hpa]
  rw [h87]
  -- MOVE-COMMIT
  by_cases hmc : MoveCommitGuard (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos hmc] at hpre
    rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
    exact moveCommit_preserves_spliceSafeV7 hpsi ring C e hne hS hmc
  rw [if_neg hmc] at hpre
  -- MOVE-STOP
  by_cases hms : MoveStopGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos hms] at hpre
    have hw : moveStopWriteV6 (C e) (C (ring.rightNeighbor e)) =
        (clearControlV6 (C e), clearTicketV6 (C (ring.rightNeighbor e))) := by
      simp [moveStopWriteV6, hr]
    rw [hw] at hpre
    rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hpre]
    exact moveStop_preserves_spliceSafeV7 hpsi ring C e hne hS hms
  rw [if_neg hms] at hpre
  -- MOVE-SEEK
  by_cases hsk : MoveSeekGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos hsk] at hpre
    rw [stepV7_of_right hpsi hwidth hle ring C e hne (fun u => setTicketV6 u true) hpre]
    exact moveSeek_preserves_spliceSafeV7 hpsi ring C e hS hsk
  rw [if_neg hsk] at hpre
  -- MOVE-SEEK-HOLD (identity)
  by_cases hskh : MoveSeekHoldGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos hskh] at hpre
    rw [stepV7_of_identity hpsi hwidth hle ring C e hne hpre]; exact hS
  rw [if_neg hskh] at hpre
  -- PENDING-OWNER-ABORT
  by_cases hpoa : PendingOwnerAbortGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos hpoa] at hpre
    rw [stepV7_of_right hpsi hwidth hle ring C e hne clearTicketV6 hpre]
    exact pendingOwnerAbort_preserves_spliceSafeV7 hpsi ring C e hS hpoa
  rw [if_neg hpoa] at hpre
  -- PENDING-OWNER-HOLD (identity)
  by_cases hpoh : role (C e).carrier = .predecessorArmed /\ (C e).carrier.repairPending = true
  · rw [if_pos hpoh] at hpre
    rw [stepV7_of_identity hpsi hwidth hle ring C e hne hpre]; exact hS
  rw [if_neg hpoh] at hpre
  -- MOVE-ACQUIRE (legacy)
  by_cases hmal : MoveAcquireLegacyGuardV6 (C e) (C (ring.rightNeighbor e))
  · rw [if_pos hmal] at hpre
    rw [stepV7_of_left' hpsi hwidth hle ring C e hne (fun u => setControlV6 u .predecessorArmed true) hpre]
    exact moveAcquireLegacy_preserves_spliceSafeV7 hpsi ring C e hne hS hmal
  rw [if_neg hmal] at hpre
  -- MOVE-ACQUIRE-ABORT
  by_cases hmaa : MoveAcquireAbortGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos hmaa] at hpre
    rw [stepV7_of_left hpsi hwidth hle ring C e hne clearTicketV6 hpre]
    exact moveAcquireAbort_preserves_spliceSafeV7 hpsi ring C e hS hmaa
  rw [if_neg hmaa] at hpre
  -- ORPHAN-RESERVED-FRONT and RESERVED-FRONT holds (identity)
  by_cases horf : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos horf] at hpre
    rw [stepV7_of_identity hpsi hwidth hle ring C e hne hpre]; exact hS
  rw [if_neg horf] at hpre
  by_cases hrfh : ReservedFrontHoldGuard (C e).carrier
  · rw [if_pos hrfh] at hpre
    rw [stepV7_of_identity hpsi hwidth hle ring C e hne hpre]; exact hS
  rw [if_neg hrfh] at hpre
  -- VICTIM-RIGHT-SCRUB
  by_cases hvr : VictimRightScrubGuardV6 (C (ring.rightNeighbor e))
  · rw [if_pos hvr] at hpre
    rw [stepV7_of_right' hpsi hwidth hle ring C e hne clearControlV6 hpre]
    refine certFreeClear_preserves_spliceSafeV7 hpsi ring C e hS ⟨?_, ?_, ?_, ?_⟩
    · intro hf; exact absurd hf.1 (by rw [hvr.1]; decide)
    · rw [hvr.1]; decide
    · intro hv; exact absurd hv.2 (by rw [hvr.2]; decide)
    · intro hf; exact absurd hf.1 (by rw [hvr.1]; decide)
  rw [if_neg hvr] at hpre
  -- VICTIM-LEFT-SCRUB
  by_cases hvl : VictimLeftScrubGuardV6 (C e)
  · rw [if_pos hvl] at hpre
    rw [stepV7_of_left' hpsi hwidth hle ring C e hne clearControlV6 hpre]
    exact certFreeLeftClear_preserves_spliceSafeV7 hpsi ring C e hS
      (victimLeftScrub_certFree (C e) (C (ring.rightNeighbor e)) hvl)
  rw [if_neg hvl] at hpre
  -- FRONT-RIGHT-SCRUB
  by_cases hfr : FrontRightScrubGuardV6 (C (ring.rightNeighbor e))
  · rw [if_pos hfr] at hpre
    rw [stepV7_of_right' hpsi hwidth hle ring C e hne clearControlV6 hpre]
    refine certFreeClear_preserves_spliceSafeV7 hpsi ring C e hS ⟨?_, ?_, ?_, ?_⟩
    · intro hf; exact absurd hf.2 (by rw [hfr.2]; decide)
    · rw [hfr.1]; decide
    · intro hv; exact absurd hv.1 (by rw [hfr.1]; decide)
    · intro hf; exact absurd hf.1 (by rw [hfr.1]; decide)
  rw [if_neg hfr] at hpre
  -- MALFORMED-LEFT
  by_cases hml : MalformedLeftPendingGuardV6 (C e)
  · rw [if_pos hml] at hpre
    have hnone : role (C e).carrier = .none := role_none_of_not _ hml.2.1 hml.2.2.1 hml.2.2.2
    have hw : malformedLeftPendingWriteV6 (C e) (C (ring.rightNeighbor e)) =
        (clearControlV6 (C e), C (ring.rightNeighbor e)) := by
      unfold malformedLeftPendingWriteV6
      rw [clearPending_eq_clearControl (C e) hnone]
    rw [hw] at hpre
    rw [stepV7_of_left' hpsi hwidth hle ring C e hne clearControlV6 hpre]
    exact certFreeLeftClear_preserves_spliceSafeV7 hpsi ring C e hS
      (malformedLeft_certFree (C e) (C (ring.rightNeighbor e)) hml)
  rw [if_neg hml] at hpre
  -- MALFORMED-RIGHT
  by_cases hmr : MalformedRightPendingGuardV6 (C (ring.rightNeighbor e))
  · rw [if_pos hmr] at hpre
    have hnone : role (C (ring.rightNeighbor e)).carrier = .none :=
      role_none_of_not _ hmr.2.1 hmr.2.2.1 hmr.2.2.2
    have hw : malformedRightPendingWriteV6 (C e) (C (ring.rightNeighbor e)) =
        (C e, clearControlV6 (C (ring.rightNeighbor e))) := by
      unfold malformedRightPendingWriteV6
      rw [clearPending_eq_clearControl (C (ring.rightNeighbor e)) hnone]
    rw [hw] at hpre
    rw [stepV7_of_right' hpsi hwidth hle ring C e hne clearControlV6 hpre]
    refine certFreeClear_preserves_spliceSafeV7 hpsi ring C e hS ⟨?_, ?_, ?_, ?_⟩
    · intro hf; exact hmr.2.2.1 hf.1
    · exact hmr.2.1
    · intro hv; exact hmr.2.2.2 hv.1
    · intro hf; exact absurd hf.2.1 (by rw [hmr.1]; decide)
  rw [if_neg hmr] at hpre
  -- PREDECESSOR-LEFT-SCRUB
  by_cases hpl : role (C e).carrier = .predecessorArmed
  · rw [if_pos hpl] at hpre
    have hset : (C e).carrier.repairPending = false := by
      cases hp : (C e).carrier.repairPending
      · rfl
      · exact absurd ⟨hpl, hp⟩ hpoh
    rw [stepV7_of_left' hpsi hwidth hle ring C e hne clearControlV6 hpre]
    refine certFreeLeftClear_preserves_spliceSafeV7 hpsi ring C e hS
      (predecessorLeftScrub_certFree (C e) (C (ring.rightNeighbor e)) hpl hset ?_ ?_ ?_)
    · intro hrf
      by_cases hbar : LocalPreparedBarrier hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
      · exact hsk ⟨hpl, hset, hrf, hbar⟩
      · exact hms ⟨hpl, hset, hrf, hbar⟩
    · intro hv
      exact hskh ⟨hpl, hset, hv.1, hv.2, hr⟩
    · intro hp
      exact hmc ⟨hpl, hset, hp.1, hp.2, hr⟩
  rw [if_neg hpl] at hpre
  -- LEFT-FRONT-HOLD (identity)
  by_cases hlf : role (C e).carrier = .front
  · rw [if_pos hlf] at hpre
    rw [stepV7_of_identity hpsi hwidth hle ring C e hne hpre]; exact hS
  rw [if_neg hlf] at hpre
  -- MARKED-HOLD (identity)
  by_cases hmk : MarkedHoldGuardV6 (C e) (C (ring.rightNeighbor e))
  · rw [if_pos hmk] at hpre
    rw [stepV7_of_identity hpsi hwidth hle ring C e hne hpre]; exact hS
  rw [if_neg hmk] at hpre
  -- ORDINARY HOST on a neutral pair
  have hlnone : role (C e).carrier = .none :=
    Classical.byContradiction (fun h => hmk (Or.inl h))
  have hlpend : (C e).carrier.repairPending = false := by
    cases hp : (C e).carrier.repairPending
    · rfl
    · exact absurd ⟨hp, hpl, hlf, fun hv => hvl ⟨hv, by
        -- a pending victim on the left would be caught as VictimLeft? no: VictimLeftScrub needs
        -- pending false; use the role instead
        exact absurd hv (by rw [hlnone]; decide)⟩⟩ hml
  have hlticket : (C e).acquireTicket = false := by
    cases ht : (C e).acquireTicket
    · rfl
    · exact absurd ⟨hlnone, hlpend, ht⟩ hfL
  have hrnone : role (C (ring.rightNeighbor e)).carrier = .none := by
    cases hrr : role (C (ring.rightNeighbor e)).carrier with
    | none => rfl
    | front =>
        exfalso
        cases hp : (C (ring.rightNeighbor e)).carrier.repairPending
        · exact hfr ⟨hrr, hp⟩
        · exact hmk (Or.inr ⟨by rw [hrr]; decide, Or.inr hp⟩)
    | victimArmed =>
        exfalso
        cases hp : (C (ring.rightNeighbor e)).carrier.repairPending
        · exact hvr ⟨hrr, hp⟩
        · exact hmk (Or.inr ⟨by rw [hrr]; decide, Or.inr hp⟩)
    | predecessorArmed =>
        exfalso
        cases hp : (C (ring.rightNeighbor e)).carrier.repairPending
        · cases ht : (C (ring.rightNeighbor e)).acquireTicket
          · exact hst ⟨hlnone, hlpend, hlticket, hrr, hp, ht⟩
          · rcases hS.2.1 (ring.rightNeighbor e) ht with hres | hf
            · exact absurd hres.1 (by rw [hrr]; decide)
            · exact absurd hf.1 (by rw [hrr]; decide)
        · exact hmk (Or.inr ⟨by rw [hrr]; decide, Or.inr hp⟩)
  have hrpend : (C (ring.rightNeighbor e)).carrier.repairPending = false := by
    cases hp : (C (ring.rightNeighbor e)).carrier.repairPending
    · rfl
    · exact absurd ⟨hp, by rw [hrnone]; decide, by rw [hrnone]; decide, by rw [hrnone]; decide⟩ hmr
  have hrticket : (C (ring.rightNeighbor e)).acquireTicket = false := by
    cases ht : (C (ring.rightNeighbor e)).acquireTicket
    · rfl
    · exact absurd ⟨hrnone, hrpend, ht⟩ hfR
  have hneutral : OrdinaryNeutralPairV8 (C e) (C (ring.rightNeighbor e)) :=
    ⟨hlnone, hlpend, hlticket, hrnone, hrpend, hrticket⟩
  have hrow8 : rowV8 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
      ordinaryHostWriteV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) := by
    rw [rowV8_eq_rowV7 hpsi hwidth hle ring C e hst]
    exact hpre
  rw [← h87]
  by_cases hb : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base = true
  · exact B9SpliceV8BirthCaseUnconditional.ordinary_birth_preserves_spliceSafeV7_unconditional
      hpsi hwidth hle ring C e hS hneutral hrow8 hb
  · have hb' : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
        (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base = false := by
      cases hh' : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
        (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base
      · rfl
      · exact absurd hh' hb
    by_cases hr0 : deletionActive (normalizeDeletion
        (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e)).carrier.splice.base).core.erase) = true
    · exact B9SpliceV8DeletionCase.ordinary_deletion_priority_preserves_spliceSafeV7
        hpsi hwidth hle ring C e hS hneutral hrow8 (Or.inl hr0)
    · have hr0' : deletionActive (normalizeDeletion
          (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e)).carrier.splice.base).core.erase) = false := by
        cases hh' : deletionActive (normalizeDeletion
          (prepareExpiringDisposal hpsi (C (ring.rightNeighbor e)).carrier.splice.base).core.erase)
        · rfl
        · exact absurd hh' hr0
      by_cases hl0 : deletionActive (normalizeDeletion
          (prepareExpiringDisposal hpsi (C e).carrier.splice.base).core.erase) = true
      · exact B9SpliceV8DeletionCase.ordinary_deletion_priority_preserves_spliceSafeV7
          hpsi hwidth hle ring C e hS hneutral hrow8 (Or.inr ⟨hr0', hl0⟩)
      · have hl0' : deletionActive (normalizeDeletion
            (prepareExpiringDisposal hpsi (C e).carrier.splice.base).core.erase) = false := by
          cases hh' : deletionActive (normalizeDeletion
            (prepareExpiringDisposal hpsi (C e).carrier.splice.base).core.erase)
          · rfl
          · exact absurd hh' hl0
        exact ordinary_no_birth_preserves_spliceSafeV7 hpsi hwidth hle ring C e hS hneutral hrow8
          hl hr ⟨hr0', hl0'⟩ hb'

end B9SpliceV10cWholeStepLeaderless
