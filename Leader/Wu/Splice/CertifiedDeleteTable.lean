import Leader.Wu.Splice.OwnerHoldTable

set_option autoImplicit false

/-! # V10h: certified physical leader deletion (candidate table)

Repair of `B9V10eLeaderPhysicalDeletionNoGo` selected by the census `B9V10hDeletionCensus` and the core
sweep (run/verification/b9-v10h2-core-sweep.txt): when the physical row on the served pair would delete
the left leader (`LeftDeletionCandidate`), V10h performs the certified DELETE write `deleteWriteV6`
(left pending predecessor, right reserved front, tickets cleared), except that a left reserved front is
held (it may back a pending predecessor on its left); otherwise V10h is V10g.

This file gives the generic definitions and the agreement facts: without a left leader, V10h is V10g
(`rowV10h_eq_rowV10g_of_left_follower`), hence on leaderless configurations `stepV10h = stepV10g`
(`stepV10h_eq_stepV10g_of_leaderless`), and with `ShapeClear` the leaderless V10e results transfer. -/

namespace B9SpliceTableV10h

open Q11593SpliceControllerDesign
  B9SpliceControllerR1Table
  B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3
  B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7
  B9SpliceTableV10g

variable {n psi kappa tau width : Nat}

/-- V10h row. -/
noncomputable def rowV10h (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau := by
  classical
  exact
    if LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice then
      if ReservedFrontHoldGuard l.carrier then (l, r) else deleteWriteV6 hpsi hwidth hle l r
    else rowV10g hpsi hwidth hle l r

/-- Pointwise ring step using `rowV10h`. -/
noncomputable def stepV10h (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    R1ConfigV6 n psi kappa tau := by
  classical
  exact
    if ring.rightNeighbor e = e then C
    else
      let w := rowV10h hpsi hwidth hle (C e) (C (ring.rightNeighbor e))
      fun i =>
        if i = e then w.1
        else if i = ring.rightNeighbor e then w.2
        else C i

theorem rowV10h_eq_rowV10g_of_left_follower (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : R1AgentStateV6 psi kappa tau) (hl : l.carrier.splice.base.core.core.leader = false) :
    rowV10h hpsi hwidth hle l r = rowV10g hpsi hwidth hle l r := by
  classical
  have hno : ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice := by
    intro h
    have := h.1
    rw [hl] at this
    exact Bool.noConfusion this
  unfold rowV10h
  simp only [if_neg hno]

theorem stepV10h_eq_stepV10g_of_leaderless (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (hlead : B9SpliceV10eAssembly.Leaderless C) (e : Fin n) :
    stepV10h hpsi hwidth hle ring C e = stepV10g hpsi hwidth hle ring C e := by
  classical
  unfold stepV10h stepV10g
  by_cases hself : ring.rightNeighbor e = e
  · simp only [if_pos hself]
  · simp only [if_neg hself]
    rw [rowV10h_eq_rowV10g_of_left_follower hpsi hwidth hle _ _ (hlead e)]

/-- On a leaderless configuration where no cell is a pending predecessor, V10h is V10e. -/
theorem stepV10h_eq_stepV10e_of_leaderless_shapeClear (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width ≤ psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (hlead : B9SpliceV10eAssembly.Leaderless C) (hSC : B9SpliceComposedEvents.ShapeClear C) (e : Fin n) :
    stepV10h hpsi hwidth hle ring C e = B9SpliceTableV10e.stepV10e hpsi hwidth hle ring C e := by
  classical
  rw [stepV10h_eq_stepV10g_of_leaderless hpsi hwidth hle ring C hlead e]
  unfold stepV10g B9SpliceTableV10e.stepV10e
  by_cases hself : ring.rightNeighbor e = e
  · simp only [if_pos hself]
  · simp only [if_neg hself]
    rw [rowV10g_eq_rowV10e_of_no_pending_pred hpsi hwidth hle _ _ (hSC.2 e) (hSC.2 _)]

end B9SpliceTableV10h
