import Leader.Wu.Splice.PhysicalHoldLeaderDeletionNoGo
import Leader.Wu.Splice.CertifiedDeleteTable

set_option autoImplicit false

/-! # No-go: V10h creates a leader on a controller seam while a leader exists

Fixture (n = 3, psi = 2, width 1, kappa = tau = 1), every physical field at the `PeaceView.toState` defaults
except as stated: site 0 is a leader with label 0 and a neutral controller; site 1 is a follower with label 0
and the settled-predecessor role (`predecessorArmed`, not pending); site 2 is a follower with label 0 carrying
a probe, with the reserved-front role (`front`, pending) and the SEEK ticket.  The start satisfies
`SpliceSafeV7g` (the barrier on edge 1 is protected by the settled predecessor facing a reserved front).  On
edge 1 the MOVE-SEEK write is the identity (the ticket is already set), so V10g, and V10h since the left cell
is a follower, runs the literal physical hold there; the P'_psi barrier rule turns the probed right follower
into a leader.  So `SpliceSafeV7g` together with the V10h table does not prevent a birth while a leader
exists (`stepV10h_seam_birth_with_leader`); the invariant itself is preserved
(`B9SpliceV10hWholeStepSafe.stepV10h_preserves_spliceSafeV7g`). -/

namespace B9V10hSeamBirthNoGo

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10h
open B9V10eLeaderPhysicalDeletionNoGo

def leaderView : PeaceView 2 := { leader := true, label := 0, shield := false, bullet := 0, signal_B := 0 }
def followerView : PeaceView 2 := { leader := false, label := 0, shield := false, bullet := 0, signal_B := 0 }

def leaderRaw : AgentState 2 := PeaceView.toState leaderView
def midRaw : AgentState 2 := PeaceView.toState followerView
def probedRaw : AgentState 2 := { PeaceView.toState followerView with probe := true }

theorem leaderDomain : leaderRaw.inProtocolDomain 1 := by
  simp [leaderRaw, leaderView, PeaceView.toState, AgentState.inProtocolDomain]
theorem midDomain : midRaw.inProtocolDomain 1 := by
  simp [midRaw, followerView, PeaceView.toState, AgentState.inProtocolDomain]
theorem probedDomain : probedRaw.inProtocolDomain 1 := by
  simp [probedRaw, followerView, PeaceView.toState, AgentState.inProtocolDomain]

/-- The seam fixture. -/
def start : R1ConfigV6 3 2 1 1 := fun i =>
  if i = 0 then liftAgentV6 (carrier (pack leaderRaw leaderDomain) .none)
  else if i = 1 then liftAgentV6 (carrier (pack midRaw midDomain) .predecessorArmed)
  else setTicketV6 (liftAgentV6 { carrier (pack probedRaw probedDomain) .front with repairPending := true }) true

theorem start_safe : SpliceSafeV7g hTwo ring3 start := by decide

theorem start_shape :
    (start 0).carrier.splice.base.core.core.leader = true ∧
    (start 1).carrier.splice.base.core.core.leader = false ∧
    (start 2).carrier.splice.base.core.core.leader = false ∧
    role (start 1).carrier = .predecessorArmed ∧ (start 1).carrier.repairPending = false ∧
    ReservedFrontHoldGuard (start 2).carrier ∧ (start 2).acquireTicket = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- On edge 1 the V10dg table stutters and V10g runs the physical hold. -/
theorem row_is_physicalHold :
    rowV10dg hTwo hOne hOneTwo (start 1) (start (ring3.rightNeighbor 1)) =
      (start 1, start (ring3.rightNeighbor 1)) ∧
    rowV10g hTwo hOne hOneTwo (start 1) (start (ring3.rightNeighbor 1)) =
      physicalHoldV6 hTwo hOne hOneTwo (start 1) (start (ring3.rightNeighbor 1)) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem stepV10g_birth :
    (stepV10g hTwo hOne hOneTwo ring3 start 1 2).carrier.splice.base.core.core.leader = true ∧
    (stepV10g hTwo hOne hOneTwo ring3 start 1 0).carrier.splice.base.core.core.leader = true := by decide

theorem stepV10h_eq_stepV10g_here :
    stepV10h hTwo hOne hOneTwo ring3 start 1 = stepV10g hTwo hOne hOneTwo ring3 start 1 := by
  classical
  unfold stepV10h stepV10g
  by_cases hself : ring3.rightNeighbor 1 = 1
  · simp only [if_pos hself]
  · simp only [if_neg hself]
    rw [rowV10h_eq_rowV10g_of_left_follower hTwo hOne hOneTwo _ _ (by decide)]

/-- V10h creates a leader at a follower of the served seam while another leader exists. -/
theorem stepV10h_seam_birth_with_leader :
    SpliceSafeV7g hTwo ring3 start ∧
    (start 0).carrier.splice.base.core.core.leader = true ∧
    (start 2).carrier.splice.base.core.core.leader = false ∧
    (stepV10h hTwo hOne hOneTwo ring3 start 1 2).carrier.splice.base.core.core.leader = true ∧
    (stepV10h hTwo hOne hOneTwo ring3 start 1 0).carrier.splice.base.core.core.leader = true := by
  rw [stepV10h_eq_stepV10g_here]
  exact ⟨start_safe, start_shape.1, start_shape.2.2.1, stepV10g_birth.1, stepV10g_birth.2⟩

end B9V10hSeamBirthNoGo
