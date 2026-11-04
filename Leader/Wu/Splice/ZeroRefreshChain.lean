import Leader.Wu.Splice.MoveCommitSafe
import Leader.Wu.Splice.MoveStopSafe
import Leader.Wu.Splice.MoveSeekSafe
import Leader.Wu.Splice.PendingOwnerAbortSafe
import Leader.Wu.Splice.MoveAcquireVictimSafe
import Leader.Wu.Splice.MoveAcquireAbortSafe
import Leader.Wu.Splice.CertFreeLeftSafe
import Leader.Wu.Splice.ArmingNeedsLeader
import Leader.Wu.Splice.ZeroRefreshTable

set_option autoImplicit false
set_option Elab.async false

/-! # Shape lemmas for the V10c priority chain

Each level of the chain reduces to the next when its guard fails, and at the V7 level each
row equals the configuration-level writer proved safe in the row files. -/

namespace B9SpliceV10cChainShapes

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
  B9SpliceV10cLiveness B9OrphanToFence
  B9SpliceV10cRowMoveCommit B9SpliceV10cRowMoveStop B9SpliceV10cRowMoveSeek
  B9SpliceV10cRowPendingOwnerAbort B9SpliceV10cRowMoveAcquireLegacy
  B9SpliceV10cRowMoveAcquireAbort B9SpliceV10cRowCertFreeLeft

variable {n psi width kappa tau : Nat}

section Chain

variable (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
  (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)

theorem stepV10c_self (hne : ring.rightNeighbor e = e) :
    stepV10c hpsi hwidth hle ring C e = C := by
  simp [stepV10c, hne]

theorem stepV10c_eq_stepV10b (hne : ring.rightNeighbor e ≠ e)
    (hz : ¬ ZeroRefreshOnlyGuardV10c hpsi hwidth hle (C e) (C (ring.rightNeighbor e))) :
    stepV10c hpsi hwidth hle ring C e = stepV10b hpsi hwidth hle ring C e := by
  funext i
  simp only [stepV10c, stepV10b, rowV10c, hne, if_false, hz]

theorem stepV10b_eq_stepV9 (hne : ring.rightNeighbor e ≠ e)
    (hh : ¬ HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e))) :
    stepV10b hpsi hwidth hle ring C e = stepV9 hpsi hwidth hle ring C e := by
  funext i
  simp only [stepV10b, stepV9, rowV10b, hne, if_false, hh]

theorem stepV9_eq_stepV8 (hne : ring.rightNeighbor e ≠ e)
    (hb : ¬ HostFenceBusyFrontGuardV9 hpsi (C e) (C (ring.rightNeighbor e))) :
    stepV9 hpsi hwidth hle ring C e = stepV8 hpsi hwidth hle ring C e := by
  funext i
  simp only [stepV9, stepV8, rowV9, hne, if_false, hb]

theorem stepV8_eq_stepV7 (hne : ring.rightNeighbor e ≠ e)
    (hs : ¬ RightStalePredecessorHoldGuardV8 (C e) (C (ring.rightNeighbor e))) :
    stepV8 hpsi hwidth hle ring C e = stepV7 hpsi hwidth hle ring C e := by
  funext i
  simp only [stepV8, stepV7, rowV8, hne, if_false, hs]

theorem rowV8_eq_rowV7 (hs : ¬ RightStalePredecessorHoldGuardV8 (C e) (C (ring.rightNeighbor e))) :
    rowV8 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
      rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) := by
  simp only [rowV8, hs, if_false]

/-- The V7 step with an explicit row output. -/
theorem stepV7_of_row (hne : ring.rightNeighbor e ≠ e)
    (q : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau)
    (hrow : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = q) :
    stepV7 hpsi hwidth hle ring C e =
      fun i => if i = e then q.1 else if i = ring.rightNeighbor e then q.2 else C i := by
  funext i
  simp only [stepV7, hne, if_false, hrow]

theorem stepV7_of_identity (hne : ring.rightNeighbor e ≠ e)
    (hrow : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, C (ring.rightNeighbor e))) :
    stepV7 hpsi hwidth hle ring C e = C := by
  rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hrow]
  funext i
  by_cases hi : i = e
  · subst hi; simp
  · by_cases hj : i = ring.rightNeighbor e
    · subst hj; simp [hne]
    · simp [hi, hj]

/-- A row that changes only the right endpoint. -/
theorem stepV7_of_right (hne : ring.rightNeighbor e ≠ e)
    (f : R1AgentStateV6 psi kappa tau → R1AgentStateV6 psi kappa tau)
    (hrow : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, f (C (ring.rightNeighbor e)))) :
    stepV7 hpsi hwidth hle ring C e = fun i => if i = ring.rightNeighbor e then f (C i) else C i := by
  rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hrow]
  funext i
  by_cases hi : i = e
  · subst hi; simp [Ne.symm hne]
  · by_cases hj : i = ring.rightNeighbor e
    · subst hj; simp [hne]
    · simp [hi, hj]

/-- A row that changes only the left endpoint. -/
theorem stepV7_of_left (hne : ring.rightNeighbor e ≠ e)
    (f : R1AgentStateV6 psi kappa tau → R1AgentStateV6 psi kappa tau)
    (hrow : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (f (C e), C (ring.rightNeighbor e))) :
    stepV7 hpsi hwidth hle ring C e = fun i => if i = e then f (C i) else C i := by
  rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hrow]
  funext i
  by_cases hi : i = e
  · subst hi; simp
  · by_cases hj : i = ring.rightNeighbor e
    · subst hj; simp [hne]
    · simp [hi, hj]

/-- Right-endpoint writer expressed through the fixed right cell. -/
theorem stepV7_of_right' (hne : ring.rightNeighbor e ≠ e)
    (f : R1AgentStateV6 psi kappa tau → R1AgentStateV6 psi kappa tau)
    (hrow : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (C e, f (C (ring.rightNeighbor e)))) :
    stepV7 hpsi hwidth hle ring C e =
      fun i => if i = ring.rightNeighbor e then f (C (ring.rightNeighbor e)) else C i := by
  rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hrow]
  funext i
  by_cases hi : i = e
  · subst hi; simp [Ne.symm hne]
  · by_cases hj : i = ring.rightNeighbor e
    · subst hj; simp [hne]
    · simp [hi, hj]

/-- Left-endpoint writer expressed through the fixed left cell. -/
theorem stepV7_of_left' (hne : ring.rightNeighbor e ≠ e)
    (f : R1AgentStateV6 psi kappa tau → R1AgentStateV6 psi kappa tau)
    (hrow : rowV7 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = (f (C e), C (ring.rightNeighbor e))) :
    stepV7 hpsi hwidth hle ring C e = fun i => if i = e then f (C e) else C i := by
  rw [stepV7_of_row hpsi hwidth hle ring C e hne _ hrow]
  funext i
  by_cases hi : i = e
  · subst hi; simp
  · by_cases hj : i = ring.rightNeighbor e
    · subst hj; simp [hne]
    · simp [hi, hj]

end Chain

end B9SpliceV10cChainShapes
