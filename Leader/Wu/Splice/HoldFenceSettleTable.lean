import Leader.Wu.Splice.CertifiedDeleteWholeStepSafe

set_option autoImplicit false
set_option Elab.async false

/-! # V10i: release the reserved-front hold of V10h, and whole-step safety

V10h holds a deletion candidate whose left cell is a reserved front (the front may back a pending predecessor
on its left, so the certified DELETE must not overwrite it).  If every cell of a ring is a reserved-front
leader and every edge is a deletion candidate, all edges hold forever (sampled at n = 2 and 3,
run/verification/b9-v10h-liveness-probe.txt).  V10i keeps the hold but first performs, inside that branch, the
two controller-only repairs that V10g would have applied on the right cell: a reserved front on the right is an
orphan (its left cell is a front, not a predecessor) and becomes a host fence; a pending predecessor on the right
is settled (repair (iii)).  Off this branch V10i is V10h; on leaderless configurations it is V10g.

`stepV10i_preserves_spliceSafeV7g`: `SpliceSafeV7g` is invariant under every V10i step. -/

namespace B9SpliceTableV10i

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10h
  B9SpliceCertifiedDelete B9SpliceV10hControllerRowsSafe B9SpliceV10dRowsSafeV7g
  B9SpliceSettleRepairSafe B9SpliceV10hWholeStepSafe

variable {n psi width kappa tau : Nat}

/-- V10i row. -/
noncomputable def rowV10i (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau := by
  classical
  exact
    if LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice then
      if ReservedFrontHoldGuard l.carrier then
        if ReservedFrontHoldGuard r.carrier then (l, fenceV6 r)
        else if role r.carrier = .predecessorArmed ∧ r.carrier.repairPending = true then (l, settleV6 r)
        else (l, r)
      else deleteWriteV6 hpsi hwidth hle l r
    else rowV10g hpsi hwidth hle l r

/-- Pointwise ring step using `rowV10i`. -/
noncomputable def stepV10i (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau := by
  classical
  exact
    if ring.rightNeighbor e = e then C
    else writeAt ring C e (rowV10i hpsi hwidth hle (C e) (C (ring.rightNeighbor e)))

theorem rowV10i_eq_rowV10h_of_not_hold (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (h : ¬ (LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice ∧
      ReservedFrontHoldGuard l.carrier)) :
    rowV10i hpsi hwidth hle l r = rowV10h hpsi hwidth hle l r := by
  classical
  unfold rowV10i rowV10h
  by_cases hd : LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice
  · have hrf : ¬ ReservedFrontHoldGuard l.carrier := fun hh => h ⟨hd, hh⟩
    rw [if_pos hd, if_pos hd, if_neg hrf, if_neg hrf]
  · rw [if_neg hd, if_neg hd]

/-- Without a left leader V10i is V10g. -/
theorem rowV10i_eq_rowV10g_of_left_follower (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (hl : l.carrier.splice.base.core.core.leader = false) :
    rowV10i hpsi hwidth hle l r = rowV10g hpsi hwidth hle l r := by
  classical
  have hno : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice := by
    intro hh
    have := hh.1
    rw [hl] at this
    exact Bool.noConfusion this
  unfold rowV10i
  rw [if_neg hno]

theorem stepV10i_eq_stepV10g_of_leaderless (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false) (e : Fin n) :
    stepV10i hpsi hwidth hle ring C e = stepV10g hpsi hwidth hle ring C e := by
  classical
  unfold stepV10i stepV10g
  by_cases hself : ring.rightNeighbor e = e
  · simp only [if_pos hself]
  · rw [if_neg hself, if_neg hself, rowV10i_eq_rowV10g_of_left_follower hpsi hwidth hle _ _ (hlead e)]
    rfl

theorem stepV10i_preserves_spliceSafeV7g (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hS : SpliceSafeV7g hpsi ring C) :
    SpliceSafeV7g hpsi ring (stepV10i hpsi hwidth hle ring C e) := by
  classical
  by_cases hself : ring.rightNeighbor e = e
  · unfold stepV10i
    rw [if_pos hself]
    exact hS
  have hstep : stepV10i hpsi hwidth hle ring C e =
      writeAt ring C e (rowV10i hpsi hwidth hle (C e) (C (ring.rightNeighbor e))) := by
    unfold stepV10i
    rw [if_neg hself]
  by_cases hh : LeftDeletionCandidate hpsi hwidth hle (C e).carrier.splice
      (C (ring.rightNeighbor e)).carrier.splice ∧ ReservedFrontHoldGuard (C e).carrier
  · rw [hstep]
    have hrow := rowV10i.eq_1 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
    rw [hrow, if_pos hh.1, if_pos hh.2]
    by_cases hr : ReservedFrontHoldGuard (C (ring.rightNeighbor e)).carrier
    · rw [if_pos hr]
      have hO : OrphanReservedFrontGuardV3 (C e).carrier (C (ring.rightNeighbor e)).carrier := by
        refine ⟨hr, ?_⟩
        intro hp
        have h0 := hh.2.1
        rw [hp] at h0
        exact absurd h0 (by decide)
      have hZ : orphanToFenceAt ring C e = writeAt ring C e (C e, fenceV6 (C (ring.rightNeighbor e))) :=
        eq_writeAt_of_points ring C _ e _ hself (B9OrphanToFence.at_other ring C e e (Ne.symm hself))
          (B9OrphanToFence.at_j ring C e) (fun i _ h => B9OrphanToFence.at_other ring C e i h)
      rw [← hZ]
      exact orphanToFenceAt_preserves_spliceSafeV7g hpsi ring C e hself hS hO
    · rw [if_neg hr]
      by_cases hp : role (C (ring.rightNeighbor e)).carrier = .predecessorArmed ∧
          (C (ring.rightNeighbor e)).carrier.repairPending = true
      · rw [if_pos hp]
        have hZ : settleAt ring C e = writeAt ring C e (C e, settleV6 (C (ring.rightNeighbor e))) :=
          eq_writeAt_of_points ring C _ e _ hself (settleAt_other ring C e e (Ne.symm hself))
            (settleAt_j ring C e) (fun i _ h => settleAt_other ring C e i h)
        rw [← hZ]
        exact settleAt_preserves_spliceSafeV7g hpsi ring C e hself hS hh.2 hp.1 hp.2
      · rw [if_neg hp, writeAt_self]
        exact hS
  · have hV := stepV10h_preserves_spliceSafeV7g hpsi hwidth hle ring C e hS
    rw [stepV10h_eq_writeAt hpsi hwidth hle ring C e hself] at hV
    rw [hstep, rowV10i_eq_rowV10h_of_not_hold hpsi hwidth hle _ _ hh]
    exact hV

/-- Along any schedule. -/
theorem run_preserves_spliceSafeV7g (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (w : List (Fin n)) :
    ∀ C : R1ConfigV6 n psi kappa tau, SpliceSafeV7g hpsi ring C →
      SpliceSafeV7g hpsi ring (w.foldl (stepV10i hpsi hwidth hle ring) C) := by
  induction w with
  | nil => intro C hS; exact hS
  | cons e w ih =>
      intro C hS
      exact ih _ (stepV10i_preserves_spliceSafeV7g hpsi hwidth hle ring C e hS)

end B9SpliceTableV10i
