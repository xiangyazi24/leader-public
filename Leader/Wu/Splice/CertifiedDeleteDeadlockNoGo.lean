import Leader.Wu.Splice.HoldFenceSettleTable
import Leader.Wu.Splice.CertifiedDeleteCensus

set_option autoImplicit false

/-! # No-go: the V10h reserved-front hold deadlocks; V10i moves

Fixture (n = 2, psi = 2, width 1, kappa = tau = 1): both cells are leaders with label 0 and every other physical
field at the `PeaceView.toState` defaults, both with the reserved-front role (`front`, pending) and no ticket.
The configuration satisfies `SpliceSafeV7g` (no follower danger, no pending predecessor, no ticket).  Both edges
are left-deletion candidates and both left cells are reserved fronts, so every V10h service holds
(`stepV10h_fixed`), hence the configuration is fixed along every schedule (`runV10h_fixed`): V10h is not live.
One V10i service of edge 0 fences the orphan reserved front at site 1 (`stepV10i_moves`). -/

namespace B9V10hHoldDeadlockNoGo

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10h B9SpliceTableV10i B9OrphanToFence
  B9SpliceV10hControllerRowsSafe B9SpliceV10hWholeStepSafe
open B9V10eLeaderPhysicalDeletionNoGo B9V10hDeletionCensus

def ring2 : DirectedRing 2 := ⟨hTwo⟩

def leaderView0 : PeaceView 2 := { leader := true, label := 0, shield := false, bullet := 0, signal_B := 0 }
def leaderRaw0 : AgentState 2 := PeaceView.toState leaderView0
theorem leaderDomain0 : leaderRaw0.inProtocolDomain 1 := by
  simp [leaderRaw0, leaderView0, PeaceView.toState, AgentState.inProtocolDomain]

/-- Both cells: leader, label 0, reserved front, no ticket. -/
def start : R1ConfigV6 2 2 1 1 := fun _ => mk (pack leaderRaw0 leaderDomain0) .front true false

instance instDecSafeG2 (ring : DirectedRing 2) (C : R1ConfigV6 2 2 1 1) :
    Decidable (SpliceSafeV7g hTwo ring C) := by
  unfold SpliceSafeV7g ProvenanceSafeV7 TicketShapeV7 HostFenceShapeV7 ReservedFrontHoldGuard
    ProtectedSpliceEdgeV7g ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 PendingOwnerHoldShapeV7 projectV6
  unfold PreparedDangerAt PreparedBarrierAt; dsimp only; unfold isBarrier
  infer_instance

theorem start_safe : SpliceSafeV7g hTwo ring2 start := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem start_candidates : ∀ e : Fin 2,
    LeftDeletionCandidate hTwo hOne hOneTwo (start e).carrier.splice
      (start (ring2.rightNeighbor e)).carrier.splice := by decide

theorem start_fronts : ∀ e : Fin 2, ReservedFrontHoldGuard (start e).carrier := by
  intro e; exact ⟨rfl, rfl⟩

theorem rightNeighbor_ne (e : Fin 2) : ring2.rightNeighbor e ≠ e := by
  revert e; decide

theorem stepV10h_fixed (e : Fin 2) : B9SpliceTableV10h.stepV10h hTwo hOne hOneTwo ring2 start e = start := by
  classical
  have hrow : B9SpliceTableV10h.rowV10h hTwo hOne hOneTwo (start e) (start (ring2.rightNeighbor e)) =
      (start e, start (ring2.rightNeighbor e)) := by
    unfold B9SpliceTableV10h.rowV10h
    rw [if_pos (start_candidates e), if_pos (start_fronts e)]
  rw [stepV10h_eq_writeAt hTwo hOne hOneTwo ring2 start e (rightNeighbor_ne e), hrow, writeAt_self]

/-- V10h leaves the start unchanged along every schedule. -/
theorem runV10h_fixed (w : List (Fin 2)) :
    w.foldl (B9SpliceTableV10h.stepV10h hTwo hOne hOneTwo ring2) start = start := by
  induction w with
  | nil => rfl
  | cons e w ih => simp only [List.foldl_cons, stepV10h_fixed e, ih]

theorem stepV10i_moves :
    stepV10i hTwo hOne hOneTwo ring2 start 0 1 = fenceV6 (start 1) ∧
    stepV10i hTwo hOne hOneTwo ring2 start 0 ≠ start := by
  classical
  have hj : ring2.rightNeighbor 0 = 1 := by decide
  have hrow : rowV10i hTwo hOne hOneTwo (start 0) (start (ring2.rightNeighbor 0)) =
      (start 0, fenceV6 (start (ring2.rightNeighbor 0))) := by
    unfold rowV10i
    rw [if_pos (start_candidates 0), if_pos (start_fronts 0), if_pos (start_fronts _)]
  have hstep : stepV10i hTwo hOne hOneTwo ring2 start 0 =
      writeAt ring2 start 0 (rowV10i hTwo hOne hOneTwo (start 0) (start (ring2.rightNeighbor 0))) := by
    unfold stepV10i
    rw [if_neg (rightNeighbor_ne 0)]
  have h1 : stepV10i hTwo hOne hOneTwo ring2 start 0 1 = fenceV6 (start 1) := by
    rw [hstep, hrow]
    have := writeAt_j ring2 start 0 (start 0, fenceV6 (start (ring2.rightNeighbor 0))) (rightNeighbor_ne 0)
    rw [hj] at this
    exact this
  refine ⟨h1, ?_⟩
  intro heq
  have h2 : role (stepV10i hTwo hOne hOneTwo ring2 start 0 1).carrier = role (start 1).carrier := by
    rw [heq]
  rw [h1] at h2
  exact absurd h2 (by decide)

end B9V10hHoldDeadlockNoGo
