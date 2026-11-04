import Leader.Wu.Splice.HoldRepairTable
import Leader.Wu.Splice.CertifiedDeleteCensus

set_option autoImplicit false

/-! # No-go: V10i still deadlocks on a three-cell hold cycle; V10j moves

Fixture (n = 3, psi = 2, width 1, kappa = tau = 1; physical fields at the `PeaceView.toState` defaults except
label, shield, bullet and signal as listed): site 0 a follower (label 1, shield, bullet 2, signal 1) with the
pending-predecessor role; site 1 a leader (label 1, bullet 2) with the reserved-front role; site 2 a follower
(label 1, shield, bullet 2, signal 1) with the pending-victim role; no tickets.  The start is `SpliceSafeV7g`.
Edge 0 is the pending-predecessor hold, edge 2 is the (pending victim, pending predecessor) hold, and edge 1 is a
left-deletion candidate whose left cell is a reserved front and whose right cell is a pending victim, which V10i
holds.  So every V10i service leaves the start unchanged (`stepV10i_fixed`, `runV10i_fixed`).  One V10j service
of edge 1 clears the orphan pending victim (`stepV10j_moves`).  Exhaustive n = 3 census
(run/verification/probes/V10jHoldCensus.lean): over 6 physical cores and all 13^3 controller-shape assignments,
3618 starts are SpliceSafeV7g; V10i has 4 fixed points and 4 starts with no physical service or potential drop
within three services of any edge, V10j has none. -/

namespace B9V10iCycleDeadlockNoGo

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10i B9SpliceTableV10j B9OrphanToFence
  B9SpliceV10hControllerRowsSafe B9SpliceV10hWholeStepSafe
open B9V10eLeaderPhysicalDeletionNoGo B9V10hDeletionCensus

def mkS (leader : Bool) (label : Fin 2) (shield : Bool) (bullet : Fin 3) (sb : Fin 2) : AgentState 2 :=
  PeaceView.toState ({ leader := leader, label := label, shield := shield, bullet := bullet, signal_B := sb } : PeaceView 2)
theorem mkS_domain (leader : Bool) (label : Fin 2) (shield : Bool) (bullet : Fin 3) (sb : Fin 2) :
    (mkS leader label shield bullet sb).inProtocolDomain 1 := by
  simp [mkS, PeaceView.toState, AgentState.inProtocolDomain]
def packS (leader : Bool) (label : Fin 2) (shield : Bool) (bullet : Fin 3) (sb : Fin 2) : ExpiringAgentState 2 1 1 :=
  pack (mkS leader label shield bullet sb) (mkS_domain leader label shield bullet sb)

def start : R1ConfigV6 3 2 1 1 := fun i =>
  if i = 0 then mk (packS false 1 true 2 1) .predecessorArmed true false
  else if i = 1 then mk (packS true 1 false 2 0) .front true false
  else mk (packS false 1 true 2 1) .victimArmed true false

theorem start_safe : SpliceSafeV7g hTwo ring3 start := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem edge1_candidate :
    LeftDeletionCandidate hTwo hOne hOneTwo (start 1).carrier.splice (start (ring3.rightNeighbor 1)).carrier.splice := by
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem row0_identity :
    rowV10g hTwo hOne hOneTwo (start 0) (start (ring3.rightNeighbor 0)) = (start 0, start (ring3.rightNeighbor 0)) := by
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem row2_identity :
    rowV10g hTwo hOne hOneTwo (start 2) (start (ring3.rightNeighbor 2)) = (start 2, start (ring3.rightNeighbor 2)) := by
  decide

theorem rowV10i_identity (e : Fin 3) :
    rowV10i hTwo hOne hOneTwo (start e) (start (ring3.rightNeighbor e)) = (start e, start (ring3.rightNeighbor e)) := by
  classical
  have h0 : e = 0 ∨ e = 1 ∨ e = 2 := by revert e; decide
  rcases h0 with rfl | rfl | rfl
  · rw [rowV10i_eq_rowV10g_of_left_follower hTwo hOne hOneTwo _ _ (by decide)]
    exact row0_identity
  · unfold rowV10i
    have hRF : ReservedFrontHoldGuard (start 1).carrier := ⟨rfl, rfl⟩
    have hnRF : ¬ ReservedFrontHoldGuard (start (ring3.rightNeighbor 1)).carrier := by decide
    have hnPP : ¬ (role (start (ring3.rightNeighbor 1)).carrier = .predecessorArmed ∧
        (start (ring3.rightNeighbor 1)).carrier.repairPending = true) := by decide
    rw [if_pos edge1_candidate, if_pos hRF, if_neg hnRF, if_neg hnPP]
  · rw [rowV10i_eq_rowV10g_of_left_follower hTwo hOne hOneTwo _ _ (by decide)]
    exact row2_identity

theorem rightNeighbor_ne (e : Fin 3) : ring3.rightNeighbor e ≠ e := by
  revert e; decide

theorem stepV10i_fixed (e : Fin 3) : stepV10i hTwo hOne hOneTwo ring3 start e = start := by
  classical
  unfold stepV10i
  rw [if_neg (rightNeighbor_ne e), rowV10i_identity e, writeAt_self]

theorem runV10i_fixed (w : List (Fin 3)) :
    w.foldl (stepV10i hTwo hOne hOneTwo ring3) start = start := by
  induction w with
  | nil => rfl
  | cons e w ih => simp only [List.foldl_cons, stepV10i_fixed e, ih]

theorem stepV10j_moves :
    stepV10j hTwo hOne hOneTwo ring3 start 1 2 = clearControlV6 (start 2) ∧
    stepV10j hTwo hOne hOneTwo ring3 start 1 ≠ start := by
  classical
  have hj : ring3.rightNeighbor 1 = 2 := by decide
  have hRF : ReservedFrontHoldGuard (start 1).carrier := ⟨rfl, rfl⟩
  have hnRF : ¬ ReservedFrontHoldGuard (start (ring3.rightNeighbor 1)).carrier := by decide
  have hnPP : ¬ (role (start (ring3.rightNeighbor 1)).carrier = .predecessorArmed ∧
      (start (ring3.rightNeighbor 1)).carrier.repairPending = true) := by decide
  have hPV : role (start (ring3.rightNeighbor 1)).carrier = .victimArmed ∧
      (start (ring3.rightNeighbor 1)).carrier.repairPending = true := by decide
  have hrow : rowV10j hTwo hOne hOneTwo (start 1) (start (ring3.rightNeighbor 1)) =
      (start 1, clearControlV6 (start (ring3.rightNeighbor 1))) := by
    unfold rowV10j holdRepairV10j
    rw [if_pos edge1_candidate, if_pos hRF, if_neg hnRF, if_neg hnPP, if_pos hPV]
  have h1 : stepV10j hTwo hOne hOneTwo ring3 start 1 2 = clearControlV6 (start 2) := by
    unfold stepV10j
    rw [if_neg (rightNeighbor_ne 1), hrow]
    have := writeAt_j ring3 start 1 (start 1, clearControlV6 (start (ring3.rightNeighbor 1))) (rightNeighbor_ne 1)
    rw [hj] at this
    exact this
  refine ⟨h1, ?_⟩
  intro heq
  have h2 : role (stepV10j hTwo hOne hOneTwo ring3 start 1 2).carrier = role (start 2).carrier := by rw [heq]
  rw [h1] at h2
  exact absurd h2 (by decide)

end B9V10iCycleDeadlockNoGo
