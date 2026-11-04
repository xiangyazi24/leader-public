import Leader.Wu.Splice.OwnerHoldControllerRowsSafe
import Leader.Wu.Splice.OwnerHoldPhysicalRowsSafe
import Leader.Wu.Splice.OwnerHoldSettleSafe
import Leader.Wu.Splice.OwnerHoldMoveCommitSafe

set_option autoImplicit false
set_option Elab.async false

/-! # V10h whole-step safety: `SpliceSafeV7g` is invariant, with or without leaders

`stepV10h_preserves_spliceSafeV7g`: for every ring, every configuration satisfying `SpliceSafeV7g` and
every served edge, the V10h step yields a configuration satisfying `SpliceSafeV7g`.  No leader-count,
leaderless or shape hypothesis.  `run_preserves_spliceSafeV7g` iterates it along any schedule.

The proof walks the V10h priority chain:
* a left-leader deletion candidate: hold or certified DELETE (`stepV10h_deletionCandidate_preserves`);
* otherwise V10g.  If `rowV10dg` stutters, the stutter branch: pending-left hold, the three right scrubs,
  settle (iii), the V10e left scrub, physical-then-fence, physical hold (`not_pv_of_stutter` supplies the
  right-cell shape);
* if `rowV10dg` writes: the four V10d garbage rows, the handoff, and the V7 table.  In the V7 table the
  rows ARM-A, DELETE and PendingHold need a deletion candidate; MoveAcquireFront, MoveAcquireLegacy and the
  V9 busy-front repair need an orphan reserved front, which the first V10d row consumed; the fence advance
  is the handoff guard; the identity rows (and PendingOwnerAbort and MoveAcquireAbort, which clear a ticket
  that the ticket shape already forces false) contradict the write. -/

namespace B9SpliceV10hWholeStepSafe

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10h
  B9SpliceCertifiedDelete B9SpliceV10hControllerRowsSafe B9SpliceV10hPhysicalRowsSafe
  B9SpliceV10dRowsSafeV7g B9SpliceSettleRepairSafe B9SpliceMoveCommitSafeV7g B9SpliceMoveRowsSafeV7g
  B9SpliceV10hPhysicalHoldLeaderSafe B9SpliceV10cRowCertFreeLeft

variable {n psi width kappa tau : Nat}

/-! ## Helpers -/

theorem writeAt_self (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    writeAt ring C e (C e, C (ring.rightNeighbor e)) = C := by
  funext i
  by_cases h1 : i = e
  · subst h1; simp [writeAt]
  · by_cases h2 : i = ring.rightNeighbor e
    · subst h2; simp [writeAt, h1]
    · simp [writeAt, h1, h2]

theorem eq_writeAt_of_points (ring : DirectedRing n) (C Z : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (w : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau) (hself : ring.rightNeighbor e ≠ e)
    (h1 : Z e = w.1) (h2 : Z (ring.rightNeighbor e) = w.2)
    (h3 : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → Z i = C i) : Z = writeAt ring C e w := by
  funext i
  by_cases hie : i = e
  · rw [hie, writeAt_e]; exact h1
  · by_cases hij : i = ring.rightNeighbor e
    · rw [hij, writeAt_j ring C e w hself]; exact h2
    · rw [writeAt_other ring C e w i hie hij]; exact h3 i hie hij

theorem stepV10h_eq_writeAt (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) :
    stepV10h hpsi hwidth hle ring C e =
      writeAt ring C e (rowV10h hpsi hwidth hle (C e) (C (ring.rightNeighbor e))) := by
  unfold stepV10h
  rw [if_neg hself]
  rfl

theorem rowV10h_eq_rowV10g_of_not_candidate (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hno : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice) :
    rowV10h hpsi hwidth hle l r = rowV10g hpsi hwidth hle l r := by
  unfold rowV10h
  rw [if_neg hno]

theorem clearTicketV6_of_false (u : R1AgentStateV6 psi kappa tau) (h : u.acquireTicket = false) :
    clearTicketV6 u = u := by
  cases u with
  | mk c t =>
    simp only at h
    subst h
    rfl

theorem ticket_false_of_role (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (hS : SpliceSafeV7g hpsi ring C) (i : Fin n)
    (hnf : role (C i).carrier ≠ .front) (hnn : role (C i).carrier ≠ .none) :
    (C i).acquireTicket = false := by
  cases ht : (C i).acquireTicket
  · rfl
  · rcases hS.2.1 i ht with hrf | hf
    · exact absurd hrf.1 hnf
    · exact absurd hf.1 hnn

theorem certFree_of_victimRight (r : R1AgentStateV6 psi kappa tau) (h : VictimRightScrubGuardV6 r) :
    CertFreeV7 r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hf; have h0 := hf.1; rw [h.1] at h0; exact absurd h0 (by decide)
  · rw [h.1]; decide
  · intro hv; have h0 := hv.2; rw [h.2] at h0; exact absurd h0 (by decide)
  · intro hf; have h0 := hf.1; rw [h.1] at h0; exact absurd h0 (by decide)

theorem certFree_of_frontRight (r : R1AgentStateV6 psi kappa tau) (h : FrontRightScrubGuardV6 r) :
    CertFreeV7 r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hf; have h0 := hf.2; rw [h.2] at h0; exact absurd h0 (by decide)
  · rw [h.1]; decide
  · intro hv; have h0 := hv.1; rw [h.1] at h0; exact absurd h0 (by decide)
  · intro hf; have h0 := hf.1; rw [h.1] at h0; exact absurd h0 (by decide)

theorem certFree_of_malformedRight (r : R1AgentStateV6 psi kappa tau) (h : MalformedRightPendingGuardV6 r) :
    CertFreeV7 r := by
  refine ⟨?_, h.2.1, ?_, ?_⟩
  · intro hf; exact h.2.2.1 hf.1
  · intro hv; exact h.2.2.2 hv.1
  · intro hf; have h0 := hf.2.1; rw [h.1] at h0; exact absurd h0 (by decide)

/-- Clearing a left cell that is not a predecessor and owns no certificate. -/
theorem clearLeft_of_inert (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C)
    (hnRF : ¬ ReservedFrontHoldGuard (C e).carrier)
    (hnPred : role (C e).carrier ≠ .predecessorArmed)
    (hnPV : ¬ (role (C e).carrier = .victimArmed ∧ (C e).carrier.repairPending = true))
    (hnF : ¬ HostFenceShapeV7 (C e)) :
    SpliceSafeV7g hpsi ring (writeAt ring C e (clearControlV6 (C e), C (ring.rightNeighbor e))) :=
  clearLeft_preserves_spliceSafeV7g hpsi ring C e hself hS hnRF (fun h => hnPred h.1) hnPV hnF
    (fun h => absurd h hnPred)

theorem clearLeft_of_victimLeft (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C) (h : VictimLeftScrubGuardV6 (C e)) :
    SpliceSafeV7g hpsi ring (writeAt ring C e (clearControlV6 (C e), C (ring.rightNeighbor e))) := by
  refine clearLeft_of_inert hpsi ring C e hself hS ?_ ?_ ?_ ?_
  · intro hf; have h0 := hf.1; rw [h.1] at h0; exact absurd h0 (by decide)
  · rw [h.1]; decide
  · intro hv; have h0 := hv.2; rw [h.2] at h0; exact absurd h0 (by decide)
  · intro hf; have h0 := hf.1; rw [h.1] at h0; exact absurd h0 (by decide)

theorem clearLeft_of_malformedLeft (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C) (h : MalformedLeftPendingGuardV6 (C e)) :
    SpliceSafeV7g hpsi ring (writeAt ring C e (clearControlV6 (C e), C (ring.rightNeighbor e))) := by
  refine clearLeft_of_inert hpsi ring C e hself hS ?_ h.2.1 ?_ ?_
  · intro hf; exact h.2.2.1 hf.1
  · intro hv; exact h.2.2.2 hv.1
  · intro hf; have h0 := hf.2.1; rw [h.1] at h0; exact absurd h0 (by decide)

theorem clearLeft_of_leftScrubV10e (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) (hself : ring.rightNeighbor e ≠ e)
    (hS : SpliceSafeV7g hpsi ring C) (h : LeftScrubGuardV10e (C e)) :
    SpliceSafeV7g hpsi ring (writeAt ring C e (clearControlV6 (C e), C (ring.rightNeighbor e))) := by
  rcases h with hv | hf | hm
  · exact clearLeft_of_victimLeft hpsi ring C e hself hS hv
  · refine clearLeft_of_inert hpsi ring C e hself hS ?_ ?_ ?_ ?_
    · intro hr; have h0 := hr.2; rw [hf.2] at h0; exact absurd h0 (by decide)
    · rw [hf.1]; decide
    · intro hv; have h0 := hv.1; rw [hf.1] at h0; exact absurd h0 (by decide)
    · intro hx; have h0 := hx.1; rw [hf.1] at h0; exact absurd h0 (by decide)
  · exact clearLeft_of_malformedLeft hpsi ring C e hself hS hm

/-- Under V10dg a pending victim never stutters on the right. -/
theorem not_pv_of_stutter (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hq : rowV10dg hpsi hwidth hle l r = (l, r)) :
    ¬ (role r.carrier = .victimArmed ∧ r.carrier.repairPending = true) := by
  intro hpv
  have hnf : ¬ OrphanReservedFrontGuardV3 l.carrier r.carrier := by
    intro ho
    have h0 := ho.1.1
    rw [hpv.1] at h0
    exact absurd h0 (by decide)
  have hkey : role (rowV10dg hpsi hwidth hle l r).2.carrier = .none := by
    by_cases hov : OrphanVictimGuard l r
    · have hrow : rowV10dg hpsi hwidth hle l r = (l, clearControlV6 r) := by
        unfold rowV10dg; rw [if_neg hnf, if_pos hov]
      rw [hrow]; rfl
    · have hls : role l.carrier = .predecessorArmed ∧ l.carrier.repairPending = false :=
        Classical.byContradiction (fun hc => hov ⟨hpv.1, hpv.2, hc⟩)
      have howned : OwnedPendingVictimGuard l r := ⟨hls.1, hls.2, hpv.1, hpv.2⟩
      have hrow : rowV10dg hpsi hwidth hle l r = (fenceV6 l, fenceV6 r) := by
        unfold rowV10dg; rw [if_neg hnf, if_neg hov, if_pos howned]
      rw [hrow]; rfl
  rw [hq] at hkey
  have h1 := hpv.1
  simp only at hkey
  rw [hkey] at h1
  exact absurd h1 (by decide)

/-! ## The stutter branch of V10g -/

theorem stutter_safe (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) (hS : SpliceSafeV7g hpsi ring C)
    (hdel : ¬ LeftDeletionCandidate hpsi hwidth hle (C e).carrier.splice
      (C (ring.rightNeighbor e)).carrier.splice)
    (hq : rowV10dg hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e))) :
    SpliceSafeV7g hpsi ring (writeAt ring C e (rowV10g hpsi hwidth hle (C e) (C (ring.rightNeighbor e)))) := by
  classical
  have hw := rowV10g.eq_1 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  dsimp only at hw
  rw [if_pos hq] at hw
  rw [hw]
  by_cases h0 : role (C e).carrier = .predecessorArmed ∧ (C e).carrier.repairPending = true
  · rw [if_pos h0, writeAt_self]; exact hS
  rw [if_neg h0]
  by_cases h1 : VictimRightScrubGuardV6 (C (ring.rightNeighbor e))
  · rw [if_pos h1]
    exact clearRight_preserves_spliceSafeV7g hpsi ring C e hself hS (certFree_of_victimRight _ h1)
  rw [if_neg h1]
  by_cases h2 : FrontRightScrubGuardV6 (C (ring.rightNeighbor e))
  · rw [if_pos h2]
    exact clearRight_preserves_spliceSafeV7g hpsi ring C e hself hS (certFree_of_frontRight _ h2)
  rw [if_neg h2]
  by_cases h3 : MalformedRightPendingGuardV6 (C (ring.rightNeighbor e))
  · rw [if_pos h3]
    exact clearRight_preserves_spliceSafeV7g hpsi ring C e hself hS (certFree_of_malformedRight _ h3)
  rw [if_neg h3]
  by_cases h4 : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed
  · rw [if_pos h4]
    by_cases h5 : (C (ring.rightNeighbor e)).carrier.repairPending = true
    · rw [if_pos h5]
      by_cases h6 : ReservedFrontHoldGuard (C e).carrier
      · rw [if_pos h6]
        have hZ : settleAt ring C e = writeAt ring C e (C e, settleV6 (C (ring.rightNeighbor e))) :=
          eq_writeAt_of_points ring C _ e _ hself (settleAt_other ring C e e (Ne.symm hself))
            (settleAt_j ring C e) (fun i _ h => settleAt_other ring C e i h)
        rw [← hZ]
        exact settleAt_preserves_spliceSafeV7g hpsi ring C e hself hS h6 h4 h5
      rw [if_neg h6]
      by_cases h7 : LeftScrubGuardV10e (C e)
      · rw [if_pos h7]
        exact clearLeft_of_leftScrubV10e hpsi ring C e hself hS h7
      · rw [if_neg h7, writeAt_self]; exact hS
    · rw [if_neg h5]
      have h5' : (C (ring.rightNeighbor e)).carrier.repairPending = false := by
        cases hh : (C (ring.rightNeighbor e)).carrier.repairPending
        · rfl
        · exact absurd hh h5
      exact physicalFence_preserves_spliceSafeV7g hpsi hwidth hle ring C e hS hself h4 h5' hdel
  rw [if_neg h4]
  have hpv := not_pv_of_stutter hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) hq
  have hrshape : (role (C (ring.rightNeighbor e)).carrier = .none ∧
      (C (ring.rightNeighbor e)).carrier.repairPending = false) ∨
      ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier := by
    cases hrole : role (C (ring.rightNeighbor e)).carrier with
    | none =>
        cases hpend : (C (ring.rightNeighbor e)).carrier.repairPending with
        | false => exact Or.inl ⟨rfl, rfl⟩
        | true =>
            exact absurd ⟨hpend, by rw [hrole]; decide, by rw [hrole]; decide, by rw [hrole]; decide⟩ h3
    | front =>
        cases hpend : (C (ring.rightNeighbor e)).carrier.repairPending with
        | false => exact absurd ⟨hrole, hpend⟩ h2
        | true => exact Or.inr ⟨hrole, hpend⟩
    | predecessorArmed => exact absurd hrole h4
    | victimArmed =>
        cases hpend : (C (ring.rightNeighbor e)).carrier.repairPending with
        | false => exact absurd ⟨hrole, hpend⟩ h1
        | true => exact absurd ⟨hrole, hpend⟩ hpv
  exact physicalHold_preserves_spliceSafeV7g hpsi hwidth hle ring C e hS hself hrshape hdel

/-! ## The V7 table below the V10d rows -/

theorem rowV7_safe (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) (hS : SpliceSafeV7g hpsi ring C)
    (hdel : ¬ LeftDeletionCandidate hpsi hwidth hle (C e).carrier.splice
      (C (ring.rightNeighbor e)).carrier.splice)
    (hD1 : ¬ OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier)
    (hD3 : ¬ OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e)))
    (hHO : ¬ HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e)))
    (hSP8 : ¬ RightStalePredecessorHoldGuardV8 (C e) (C (ring.rightNeighbor e)))
    (hne : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) ≠ (C e, C (ring.rightNeighbor e))) :
    SpliceSafeV7g hpsi ring (writeAt ring C e (rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)))) := by
  classical
  have hw := rowV7.eq_1 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  rw [hw]
  rw [hw] at hne
  -- host fence on the left
  by_cases hfL : HostFenceShapeV7 (C e)
  · rw [if_pos hfL] at hne ⊢
    by_cases hbar : LocalPreparedBarrier hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
    · rw [if_pos hbar] at hne ⊢
      by_cases htc : HostFenceTargetClearV7 (C (ring.rightNeighbor e))
      · exact absurd ⟨hfL, hbar, htc⟩ hHO
      · rw [if_neg htc] at hne; exact (hne rfl).elim
    · rw [if_neg hbar]
      exact fenceStop_preserves_spliceSafeV7g hpsi ring C e hself hS hfL hbar
  rw [if_neg hfL] at hne ⊢
  by_cases hfR : HostFenceShapeV7 (C (ring.rightNeighbor e))
  · rw [if_pos hfR] at hne; exact (hne rfl).elim
  rw [if_neg hfR] at hne ⊢
  by_cases hmaf : MoveAcquireFrontGuardV6 hpsi (C e) (C (ring.rightNeighbor e))
  · exact absurd ⟨hmaf.2.2.2.1, by rw [hmaf.1.1]; decide⟩ hD1
  rw [if_neg hmaf] at hne ⊢
  by_cases hA : ArmAGuard hpsi hwidth hle (C e).carrier (C (ring.rightNeighbor e)).carrier
  · exact absurd hA.2.2.2.2 hdel
  rw [if_neg hA] at hne ⊢
  by_cases hB : ArmBGuard (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos hB]
    exact armBAt_preserves_spliceSafeV7g hpsi ring C e hself hS hB
  rw [if_neg hB] at hne ⊢
  by_cases hDel : DeleteGuard hpsi hwidth hle (C e).carrier (C (ring.rightNeighbor e)).carrier
  · exact absurd hDel.2.2.2.2 hdel
  rw [if_neg hDel] at hne ⊢
  by_cases hPH : PendingHoldGuard hpsi hwidth hle (C e).carrier (C (ring.rightNeighbor e)).carrier
  · exact absurd hPH.2.2.2.2 hdel
  rw [if_neg hPH] at hne ⊢
  by_cases hPA : PendingAbortGuard hpsi hwidth hle (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos hPA]
    exact pendingAbort_preserves_spliceSafeV7g hpsi hwidth hle ring C e hself hS hPA
  rw [if_neg hPA] at hne ⊢
  by_cases hMC : MoveCommitGuard (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos hMC]
    exact moveCommitAt_preserves_spliceSafeV7g hpsi ring C e hself hS hMC
  rw [if_neg hMC] at hne ⊢
  by_cases hMS : MoveStopGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos hMS]
    by_cases hjl : (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader = true
    · have hmw : moveStopWriteV6 (C e) (C (ring.rightNeighbor e)) =
          (clearControlV6 (C e), clearControlV6 (C (ring.rightNeighbor e))) := by
        unfold moveStopWriteV6; rw [if_pos hjl]
      rw [hmw]
      exact moveStopLeaderAt_preserves_spliceSafeV7g hpsi ring C e hself hS hMS hjl
    · have hmw : moveStopWriteV6 (C e) (C (ring.rightNeighbor e)) =
          (clearControlV6 (C e), clearTicketV6 (C (ring.rightNeighbor e))) := by
        unfold moveStopWriteV6; rw [if_neg hjl]
      rw [hmw]
      exact moveStopAt_preserves_spliceSafeV7g hpsi ring C e hself hS hMS
  rw [if_neg hMS] at hne ⊢
  by_cases hSK : MoveSeekGuardV3 hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos hSK]
    have hZ : B9SpliceV10cRowMoveSeek.moveSeekAt ring C e =
        writeAt ring C e (moveSeekWriteV6 (C e) (C (ring.rightNeighbor e))) :=
      eq_writeAt_of_points ring C _ e _ hself (B9SpliceV10cRowMoveSeek.sk_at_other ring C e e (Ne.symm hself))
        (B9SpliceV10cRowMoveSeek.sk_at_j ring C e) (fun i _ h => B9SpliceV10cRowMoveSeek.sk_at_other ring C e i h)
    rw [← hZ]
    exact moveSeekAt_preserves_spliceSafeV7g hpsi ring C e hself hS hSK
  rw [if_neg hSK] at hne ⊢
  by_cases hSKH : MoveSeekHoldGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos hSKH] at hne; exact (hne rfl).elim
  rw [if_neg hSKH] at hne ⊢
  by_cases hPOA : PendingOwnerAbortGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos hPOA] at hne
    apply (hne _).elim
    have ht := ticket_false_of_role hpsi ring C hS (ring.rightNeighbor e)
      (by rw [hPOA.1]; decide) (by rw [hPOA.1]; decide)
    unfold pendingOwnerAbortWriteV6
    rw [clearTicketV6_of_false _ ht]
  rw [if_neg hPOA] at hne ⊢
  by_cases hPP : role (C e).carrier = .predecessorArmed ∧ (C e).carrier.repairPending = true
  · rw [if_pos hPP] at hne; exact (hne rfl).elim
  rw [if_neg hPP] at hne ⊢
  by_cases hMAL : MoveAcquireLegacyGuardV6 (C e) (C (ring.rightNeighbor e))
  · exact absurd ⟨hMAL.1.2.2.2, by rw [hMAL.1.1]; decide⟩ hD1
  rw [if_neg hMAL] at hne ⊢
  by_cases hMAA : MoveAcquireAbortGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [if_pos hMAA] at hne
    apply (hne _).elim
    have ht := ticket_false_of_role hpsi ring C hS e (by rw [hMAA.1]; decide) (by rw [hMAA.1]; decide)
    unfold moveAcquireAbortWriteV6
    rw [clearTicketV6_of_false _ ht]
  rw [if_neg hMAA] at hne ⊢
  by_cases hORF : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
  · exact absurd hORF hD1
  rw [if_neg hORF] at hne ⊢
  by_cases hRFH : ReservedFrontHoldGuard (C e).carrier
  · rw [if_pos hRFH] at hne; exact (hne rfl).elim
  rw [if_neg hRFH] at hne ⊢
  by_cases hVR : VictimRightScrubGuardV6 (C (ring.rightNeighbor e))
  · rw [if_pos hVR]
    exact clearRight_preserves_spliceSafeV7g hpsi ring C e hself hS (certFree_of_victimRight _ hVR)
  rw [if_neg hVR] at hne ⊢
  by_cases hVL : VictimLeftScrubGuardV6 (C e)
  · rw [if_pos hVL]
    exact clearLeft_of_victimLeft hpsi ring C e hself hS hVL
  rw [if_neg hVL] at hne ⊢
  by_cases hFR : FrontRightScrubGuardV6 (C (ring.rightNeighbor e))
  · rw [if_pos hFR]
    exact clearRight_preserves_spliceSafeV7g hpsi ring C e hself hS (certFree_of_frontRight _ hFR)
  rw [if_neg hFR] at hne ⊢
  by_cases hML : MalformedLeftPendingGuardV6 (C e)
  · rw [if_pos hML]
    have hnone : role (C e).carrier = .none :=
      B9SpliceV10cWholeStepLeaderless.role_none_of_not _ hML.2.1 hML.2.2.1 hML.2.2.2
    unfold malformedLeftPendingWriteV6
    rw [clearPending_eq_clearControl (C e) hnone]
    exact clearLeft_of_malformedLeft hpsi ring C e hself hS hML
  rw [if_neg hML] at hne ⊢
  by_cases hMR : MalformedRightPendingGuardV6 (C (ring.rightNeighbor e))
  · rw [if_pos hMR]
    have hnone : role (C (ring.rightNeighbor e)).carrier = .none :=
      B9SpliceV10cWholeStepLeaderless.role_none_of_not _ hMR.2.1 hMR.2.2.1 hMR.2.2.2
    unfold malformedRightPendingWriteV6
    rw [clearPending_eq_clearControl (C (ring.rightNeighbor e)) hnone]
    exact clearRight_preserves_spliceSafeV7g hpsi ring C e hself hS (certFree_of_malformedRight _ hMR)
  rw [if_neg hMR] at hne ⊢
  by_cases hpl : role (C e).carrier = .predecessorArmed
  · rw [if_pos hpl]
    have hset : (C e).carrier.repairPending = false := by
      cases hp : (C e).carrier.repairPending
      · rfl
      · exact absurd ⟨hpl, hp⟩ hPP
    refine clearLeft_preserves_spliceSafeV7g hpsi ring C e hself hS ?_ hPP ?_ ?_ ?_
    · intro hf; have h0 := hf.1; rw [hpl] at h0; exact absurd h0 (by decide)
    · intro hv; have h0 := hv.1; rw [hpl] at h0; exact absurd h0 (by decide)
    · intro hf; have h0 := hf.1; rw [hpl] at h0; exact absurd h0 (by decide)
    · intro _ _ hown
      rcases hown with hrf | hpv | hpp
      · by_cases hbar : LocalPreparedBarrier hpsi (C e).carrier (C (ring.rightNeighbor e)).carrier
        · exact absurd ⟨hpl, hset, hrf, hbar⟩ hSK
        · exact absurd ⟨hpl, hset, hrf, hbar⟩ hMS
      · exact absurd ⟨hpl, hset, hpv.1, hpv.2⟩ hD3
      · cases hlead : (C (ring.rightNeighbor e)).carrier.splice.base.core.core.leader
        · exact absurd ⟨hpl, hset, hpp.1, hpp.2, hlead⟩ hMC
        · rfl
  rw [if_neg hpl] at hne ⊢
  by_cases hlf : role (C e).carrier = .front
  · rw [if_pos hlf] at hne; exact (hne rfl).elim
  rw [if_neg hlf] at hne ⊢
  by_cases hmk : MarkedHoldGuardV6 (C e) (C (ring.rightNeighbor e))
  · rw [if_pos hmk] at hne; exact (hne rfl).elim
  rw [if_neg hmk]
  -- the ordinary host row on a neutral pair
  have hlnone : role (C e).carrier = .none :=
    Classical.byContradiction (fun h => hmk (Or.inl h))
  have hlpend : (C e).carrier.repairPending = false := by
    cases hp : (C e).carrier.repairPending
    · rfl
    · exact absurd ⟨hp, by rw [hlnone]; decide, by rw [hlnone]; decide, by rw [hlnone]; decide⟩ hML
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
        · exact hFR ⟨hrr, hp⟩
        · exact hmk (Or.inr ⟨by rw [hrr]; decide, Or.inr hp⟩)
    | victimArmed =>
        exfalso
        cases hp : (C (ring.rightNeighbor e)).carrier.repairPending
        · exact hVR ⟨hrr, hp⟩
        · exact hmk (Or.inr ⟨by rw [hrr]; decide, Or.inr hp⟩)
    | predecessorArmed =>
        exfalso
        cases hp : (C (ring.rightNeighbor e)).carrier.repairPending
        · cases ht : (C (ring.rightNeighbor e)).acquireTicket
          · exact hSP8 ⟨hlnone, hlpend, hlticket, hrr, hp, ht⟩
          · rcases hS.2.1 (ring.rightNeighbor e) ht with hres | hf
            · exact absurd hres.1 (by rw [hrr]; decide)
            · exact absurd hf.1 (by rw [hrr]; decide)
        · exact hmk (Or.inr ⟨by rw [hrr]; decide, Or.inr hp⟩)
  have hrpend : (C (ring.rightNeighbor e)).carrier.repairPending = false := by
    cases hp : (C (ring.rightNeighbor e)).carrier.repairPending
    · rfl
    · exact absurd ⟨hp, by rw [hrnone]; decide, by rw [hrnone]; decide, by rw [hrnone]; decide⟩ hMR
  have hrticket : (C (ring.rightNeighbor e)).acquireTicket = false := by
    cases ht : (C (ring.rightNeighbor e)).acquireTicket
    · rfl
    · exact absurd ⟨hrnone, hrpend, ht⟩ hfR
  exact ordinaryHost_preserves_spliceSafeV7g hpsi hwidth hle ring C e hS hself hlticket hrticket
    ⟨hrnone, hrpend⟩ hdel

/-! ## The writing branch of V10g -/

theorem nonstutter_safe (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) (hS : SpliceSafeV7g hpsi ring C)
    (hdel : ¬ LeftDeletionCandidate hpsi hwidth hle (C e).carrier.splice
      (C (ring.rightNeighbor e)).carrier.splice)
    (hq : rowV10dg hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) ≠ (C e, C (ring.rightNeighbor e))) :
    SpliceSafeV7g hpsi ring (writeAt ring C e (rowV10g hpsi hwidth hle (C e) (C (ring.rightNeighbor e)))) := by
  classical
  have hw := rowV10g.eq_1 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  dsimp only at hw
  rw [if_neg hq] at hw
  rw [hw]
  have hd := rowV10dg.eq_1 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  by_cases hD1 : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier
  · rw [hd, if_pos hD1]
    have hZ : orphanToFenceAt ring C e = writeAt ring C e (C e, fenceV6 (C (ring.rightNeighbor e))) :=
      eq_writeAt_of_points ring C _ e _ hself (B9OrphanToFence.at_other ring C e e (Ne.symm hself))
        (B9OrphanToFence.at_j ring C e) (fun i _ h => B9OrphanToFence.at_other ring C e i h)
    rw [← hZ]
    exact orphanToFenceAt_preserves_spliceSafeV7g hpsi ring C e hself hS hD1
  rw [if_neg hD1] at hd
  by_cases hD2 : OrphanVictimGuard (C e) (C (ring.rightNeighbor e))
  · rw [hd, if_pos hD2]
    have hZ : orphanVictimClearAt ring C e =
        writeAt ring C e (C e, clearControlV6 (C (ring.rightNeighbor e))) :=
      eq_writeAt_of_points ring C _ e _ hself (vc_at_other ring C e e (Ne.symm hself))
        (vc_at_j ring C e) (fun i _ h => vc_at_other ring C e i h)
    rw [← hZ]
    exact orphanVictimClearAt_preserves_spliceSafeV7g hpsi ring C e hself hS hD2
  rw [if_neg hD2] at hd
  by_cases hD3 : OwnedPendingVictimGuard (C e) (C (ring.rightNeighbor e))
  · rw [hd, if_pos hD3]
    exact fenceFenceAt_preserves_spliceSafeV7g hpsi ring C e hself hS hD3
  rw [if_neg hD3] at hd
  by_cases hD4 : OwnerlessPendingPredGuard (C e) (C (ring.rightNeighbor e))
  · rw [hd, if_pos hD4]
    exact fenceSettleAt_preserves_spliceSafeV7g hpsi ring C e hself hS hD4.1 hD4.2.1 hD4.2.2
  rw [if_neg hD4] at hd
  rw [hd]
  rw [hd] at hq
  have hc := B9SpliceV10cLiveness.rowV10c.eq_1 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  by_cases hZR : ZeroRefreshOnlyGuardV10c hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  · rw [if_pos hZR] at hc; exact absurd hc hq
  rw [if_neg hZR] at hc
  rw [hc]
  rw [hc] at hq
  have hb := rowV10b.eq_1 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  by_cases hHO : HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e))
  · rw [hb, if_pos hHO]
    exact handoff_preserves_spliceSafeV7g hpsi ring C e hself hS hHO
  rw [if_neg hHO] at hb
  rw [hb]
  rw [hb] at hq
  have h9 := rowV9.eq_1 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  by_cases hBF : HostFenceBusyFrontGuardV9 hpsi (C e) (C (ring.rightNeighbor e))
  · exact absurd ⟨hBF.2.2, by rw [hBF.1.1]; decide⟩ hD1
  rw [if_neg hBF] at h9
  rw [h9]
  rw [h9] at hq
  have h8 := rowV8.eq_1 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
  by_cases hSP8 : RightStalePredecessorHoldGuardV8 (C e) (C (ring.rightNeighbor e))
  · rw [if_pos hSP8] at h8; exact absurd h8 hq
  rw [if_neg hSP8] at h8
  rw [h8]
  rw [h8] at hq
  exact rowV7_safe hpsi hwidth hle ring C e hself hS hdel hD1 hD3 hHO hSP8 hq

/-! ## The theorem -/

theorem stepV10h_preserves_spliceSafeV7g (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hS : SpliceSafeV7g hpsi ring C) :
    SpliceSafeV7g hpsi ring (stepV10h hpsi hwidth hle ring C e) := by
  classical
  by_cases hself : ring.rightNeighbor e = e
  · unfold stepV10h
    rw [if_pos hself]
    exact hS
  by_cases hdel : LeftDeletionCandidate hpsi hwidth hle (C e).carrier.splice
      (C (ring.rightNeighbor e)).carrier.splice
  · exact stepV10h_deletionCandidate_preserves hpsi hwidth hle ring C e hS hdel
  rw [stepV10h_eq_writeAt hpsi hwidth hle ring C e hself,
    rowV10h_eq_rowV10g_of_not_candidate hpsi hwidth hle _ _ hdel]
  by_cases hq : rowV10dg hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e))
  · exact stutter_safe hpsi hwidth hle ring C e hself hS hdel hq
  · exact nonstutter_safe hpsi hwidth hle ring C e hself hS hdel hq

/-- Along any schedule. -/
theorem run_preserves_spliceSafeV7g (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (w : List (Fin n)) :
    ∀ C : R1ConfigV6 n psi kappa tau, SpliceSafeV7g hpsi ring C →
      SpliceSafeV7g hpsi ring (w.foldl (stepV10h hpsi hwidth hle ring) C) := by
  induction w with
  | nil => intro C hS; exact hS
  | cons e w ih =>
      intro C hS
      exact ih _ (stepV10h_preserves_spliceSafeV7g hpsi hwidth hle ring C e hS)

end B9SpliceV10hWholeStepSafe
