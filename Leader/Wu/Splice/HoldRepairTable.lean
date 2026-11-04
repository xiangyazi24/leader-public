import Leader.Wu.Splice.HoldFenceSettleTable

set_option autoImplicit false
set_option Elab.async false

/-! # V10j: the reserved-front hold performs every right-cell repair, and whole-step safety

V10h holds a left-deletion candidate whose left cell is a reserved front; V10i fenced a reserved front and
settled a pending predecessor on the right inside that hold, which still leaves a closed hold cycle on three
cells (pending predecessor follower, reserved-front leader deleting against a pending victim follower, pending
victim follower: `B9V10iCycleDeadlockNoGo`).  V10j performs inside the hold every controller-only repair of the
right cell that V10g would otherwise apply: fence a reserved front, settle a pending predecessor, clear an
orphan pending victim (the left cell is a front, not a settled predecessor), and the three right scrubs
(non-pending victim, non-pending front, malformed pending mark); only otherwise it holds.  Off that branch V10j
is V10h; on leaderless configurations it is V10g.

`stepV10j_preserves_spliceSafeV7g`: `SpliceSafeV7g` is invariant under every V10j step. -/

namespace B9SpliceTableV10j

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10h
  B9SpliceCertifiedDelete B9SpliceV10hControllerRowsSafe B9SpliceV10dRowsSafeV7g
  B9SpliceSettleRepairSafe B9SpliceV10hWholeStepSafe

variable {n psi width kappa tau : Nat}

/-- The right-cell repair performed inside the reserved-front hold. -/
noncomputable def holdRepairV10j (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau := by
  classical
  exact
    if ReservedFrontHoldGuard r.carrier then (l, fenceV6 r)
    else if role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = true then (l, settleV6 r)
    else if role r.carrier = .victimArmed ∧ r.carrier.repairPending = true then (l, clearControlV6 r)
    else if VictimRightScrubGuardV6 r ∨ FrontRightScrubGuardV6 r ∨ MalformedRightPendingGuardV6 r then
      (l, clearControlV6 r)
    else (l, r)

/-- V10j row. -/
noncomputable def rowV10j (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau := by
  classical
  exact
    if LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice then
      if ReservedFrontHoldGuard l.carrier then holdRepairV10j l r
      else deleteWriteV6 hpsi hwidth hle l r
    else rowV10g hpsi hwidth hle l r

/-- Pointwise ring step using `rowV10j`. -/
noncomputable def stepV10j (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau := by
  classical
  exact
    if ring.rightNeighbor e = e then C
    else writeAt ring C e (rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e)))

theorem rowV10j_eq_rowV10h_of_not_hold (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (h : ¬ (LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice ∧
      ReservedFrontHoldGuard l.carrier)) :
    rowV10j hpsi hwidth hle l r = rowV10h hpsi hwidth hle l r := by
  classical
  unfold rowV10j rowV10h
  by_cases hd : LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice
  · have hrf : ¬ ReservedFrontHoldGuard l.carrier := fun hh => h ⟨hd, hh⟩
    rw [if_pos hd, if_pos hd, if_neg hrf, if_neg hrf]
  · rw [if_neg hd, if_neg hd]

theorem rowV10j_eq_rowV10g_of_left_follower (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (hl : l.carrier.splice.base.core.core.leader = false) :
    rowV10j hpsi hwidth hle l r = rowV10g hpsi hwidth hle l r := by
  classical
  have hno : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice := by
    intro hh
    have := hh.1
    rw [hl] at this
    exact Bool.noConfusion this
  unfold rowV10j
  rw [if_neg hno]

theorem stepV10j_eq_stepV10g_of_leaderless (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false) (e : Fin n) :
    stepV10j hpsi hwidth hle ring C e = stepV10g hpsi hwidth hle ring C e := by
  classical
  unfold stepV10j stepV10g
  by_cases hself : ring.rightNeighbor e = e
  · simp only [if_pos hself]
  · rw [if_neg hself, if_neg hself, rowV10j_eq_rowV10g_of_left_follower hpsi hwidth hle _ _ (hlead e)]
    rfl

/-- The hold repair preserves `SpliceSafeV7g` whenever the left cell is a reserved front. -/
theorem holdRepair_safe (hpsi : 0 < psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hself : ring.rightNeighbor e ≠ e) (hS : SpliceSafeV7g hpsi ring C)
    (hRF : ReservedFrontHoldGuard (C e).carrier) :
    SpliceSafeV7g hpsi ring (writeAt ring C e (holdRepairV10j (C e) (C (ring.rightNeighbor e)))) := by
  classical
  have hw := holdRepairV10j.eq_1 (C e) (C (ring.rightNeighbor e))
  rw [hw]
  have hnSP : ¬ (role (C e).carrier = .predecessorArmed ∧ (C e).carrier.repairPending = false) := by
    intro h
    have h0 := hRF.1
    rw [h.1] at h0
    exact absurd h0 (by decide)
  by_cases h1 : ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier
  · rw [if_pos h1]
    have hO : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier :=
      ⟨h1, fun hp => hnSP ⟨hp, by have := hRF.1; rw [hp] at this; exact absurd this (by decide)⟩⟩
    have hZ : orphanToFenceAt ring C e = writeAt ring C e (C e, fenceV6 (C (ring.rightNeighbor e))) :=
      eq_writeAt_of_points ring C _ e _ hself (B9OrphanToFence.at_other ring C e e (Ne.symm hself))
        (B9OrphanToFence.at_j ring C e) (fun i _ h => B9OrphanToFence.at_other ring C e i h)
    rw [← hZ]
    exact orphanToFenceAt_preserves_spliceSafeV7g hpsi ring C e hself hS hO
  rw [if_neg h1]
  by_cases h2 : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed ∧
      (C (ring.rightNeighbor e)).carrier.repairPending = true
  · rw [if_pos h2]
    have hZ : settleAt ring C e = writeAt ring C e (C e, settleV6 (C (ring.rightNeighbor e))) :=
      eq_writeAt_of_points ring C _ e _ hself (settleAt_other ring C e e (Ne.symm hself))
        (settleAt_j ring C e) (fun i _ h => settleAt_other ring C e i h)
    rw [← hZ]
    exact settleAt_preserves_spliceSafeV7g hpsi ring C e hself hS hRF h2.1 h2.2
  rw [if_neg h2]
  by_cases h3 : role (C (ring.rightNeighbor e)).carrier = .victimArmed ∧
      (C (ring.rightNeighbor e)).carrier.repairPending = true
  · rw [if_pos h3]
    have hG : OrphanVictimGuard (C e) (C (ring.rightNeighbor e)) := ⟨h3.1, h3.2, hnSP⟩
    have hZ : orphanVictimClearAt ring C e =
        writeAt ring C e (C e, clearControlV6 (C (ring.rightNeighbor e))) :=
      eq_writeAt_of_points ring C _ e _ hself (vc_at_other ring C e e (Ne.symm hself))
        (vc_at_j ring C e) (fun i _ h => vc_at_other ring C e i h)
    rw [← hZ]
    exact orphanVictimClearAt_preserves_spliceSafeV7g hpsi ring C e hself hS hG
  rw [if_neg h3]
  by_cases h4 : VictimRightScrubGuardV6 (C (ring.rightNeighbor e)) ∨
      FrontRightScrubGuardV6 (C (ring.rightNeighbor e)) ∨
      MalformedRightPendingGuardV6 (C (ring.rightNeighbor e))
  · rw [if_pos h4]
    rcases h4 with hv | hf | hm
    · exact clearRight_preserves_spliceSafeV7g hpsi ring C e hself hS (certFree_of_victimRight _ hv)
    · exact clearRight_preserves_spliceSafeV7g hpsi ring C e hself hS (certFree_of_frontRight _ hf)
    · exact clearRight_preserves_spliceSafeV7g hpsi ring C e hself hS (certFree_of_malformedRight _ hm)
  · rw [if_neg h4, writeAt_self]
    exact hS

theorem stepV10j_preserves_spliceSafeV7g (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hS : SpliceSafeV7g hpsi ring C) :
    SpliceSafeV7g hpsi ring (stepV10j hpsi hwidth hle ring C e) := by
  classical
  by_cases hself : ring.rightNeighbor e = e
  · unfold stepV10j
    rw [if_pos hself]
    exact hS
  have hstep : stepV10j hpsi hwidth hle ring C e =
      writeAt ring C e (rowV10j hpsi hwidth hle (C e) (C (ring.rightNeighbor e))) := by
    unfold stepV10j
    rw [if_neg hself]
  by_cases hh : LeftDeletionCandidate hpsi hwidth hle (C e).carrier.splice
      (C (ring.rightNeighbor e)).carrier.splice ∧ ReservedFrontHoldGuard (C e).carrier
  · rw [hstep]
    have hrow := rowV10j.eq_1 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
    rw [hrow, if_pos hh.1, if_pos hh.2]
    exact holdRepair_safe hpsi ring C e hself hS hh.2
  · have hV := stepV10h_preserves_spliceSafeV7g hpsi hwidth hle ring C e hS
    rw [stepV10h_eq_writeAt hpsi hwidth hle ring C e hself] at hV
    rw [hstep, rowV10j_eq_rowV10h_of_not_hold hpsi hwidth hle _ _ hh]
    exact hV

/-- Along any schedule. -/
theorem run_preserves_spliceSafeV7g (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (w : List (Fin n)) :
    ∀ C : R1ConfigV6 n psi kappa tau, SpliceSafeV7g hpsi ring C →
      SpliceSafeV7g hpsi ring (w.foldl (stepV10j hpsi hwidth hle ring) C) := by
  induction w with
  | nil => intro C hS; exact hS
  | cons e w ih =>
      intro C hS
      exact ih _ (stepV10j_preserves_spliceSafeV7g hpsi hwidth hle ring C e hS)

end B9SpliceTableV10j
