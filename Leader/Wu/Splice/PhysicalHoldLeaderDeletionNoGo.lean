import Leader.Wu.Splice.FenceHandoffDeleteCounterexample
import Leader.Wu.Splice.OwnerHoldTable

set_option autoImplicit false

/-! # No-go: the V10e/V10g physical row deletes a leader without a certificate

Fixture of `B9SpliceV10bDeleteBranch` (n = 3, psi = 2, width 1, kappa = tau = 1): site 0 is a leader
(label 1), site 1 a follower (label 0, bullet 2), site 2 a follower (label 1).  In the DELETE fixture both
sites 0 and 1 carry the `front` role, so the DELETE row fires.  Variant A gives site 1 the neutral role;
variant B makes site 0 neutral and site 1 a host fence.  In both variants no controller row claims edge 0,
so V10e (and V10g) run the physical hold there (`rowV10e = physicalHoldV6`), which performs the same terminal
deletion as DELETE: the leader at site 0 is removed, edge 0 becomes a prepared danger, and no disjunct of
danger coverage holds there, not even the V10g shape `PendingOwnerHoldShapeV7`.  Both starts are
`SpliceSafeV7`.  So with a leader present, `SpliceSafeV7` (resp. `SpliceSafeV7g`) is not preserved by
`stepV10e` (resp. `stepV10g`): the physical rows need a guard excluding uncertified leader deletion. -/

namespace B9V10eLeaderPhysicalDeletionNoGo

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b B9SpliceTableV10e B9SpliceTableV10g B9OrphanToFence

instance instDecPreparedDanger (hpsi : 0 < 2) (ring : DirectedRing 3)
    (C : R1ConfigV6 3 2 1 1) (e : Fin 3) :
    Decidable (PreparedDangerAt hpsi ring (projectV6 C) e) := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6; dsimp only; unfold isBarrier; infer_instance

instance instDecProtected (ring : DirectedRing 3) (C : R1ConfigV6 3 2 1 1) (e : Fin 3) :
    Decidable (ProtectedSpliceEdgeV7 ring C e) := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 HostFenceShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only; infer_instance

instance instDecTicketShape (u : R1AgentStateV6 2 1 1) : Decidable (TicketShapeV7 u) := by
  unfold TicketShapeV7 HostFenceShapeV7 ReservedFrontHoldGuard; infer_instance

instance instDecProvenance (ring : DirectedRing 3) (C : R1ConfigV6 3 2 1 1) :
    Decidable (ProvenanceSafeV7 ring C) := by unfold ProvenanceSafeV7; infer_instance

instance instDecSafe (hpsi : 0 < 2) (ring : DirectedRing 3) (C : R1ConfigV6 3 2 1 1) :
    Decidable (SpliceSafeV7 hpsi ring C) := by unfold SpliceSafeV7; infer_instance

instance instDecProtectedG (ring : DirectedRing 3) (C : R1ConfigV6 3 2 1 1) (e : Fin 3) :
    Decidable (ProtectedSpliceEdgeV7g ring C e) := by
  unfold ProtectedSpliceEdgeV7g; infer_instance

instance instDecSafeG (hpsi : 0 < 2) (ring : DirectedRing 3) (C : R1ConfigV6 3 2 1 1) :
    Decidable (SpliceSafeV7g hpsi ring C) := by unfold SpliceSafeV7g; infer_instance

theorem hOne : 0 < 1 := by decide
theorem hTwo : 0 < 2 := by decide
theorem hThree : 0 < 3 := by decide
theorem hOneTwo : 1 <= 2 := by decide
def ring3 : DirectedRing 3 := ⟨hThree⟩

def leftView : PeaceView 2 :=
  { leader := true, label := 1, shield := false, bullet := 0, signal_B := 0 }
def rightView : PeaceView 2 :=
  { leader := false, label := 0, shield := false, bullet := 2, signal_B := 0 }
def tailView : PeaceView 2 :=
  { leader := false, label := 1, shield := false, bullet := 0, signal_B := 0 }
def leftRaw : AgentState 2 := PeaceView.toState leftView
def rightRaw : AgentState 2 := PeaceView.toState rightView
def tailRaw : AgentState 2 := PeaceView.toState tailView
theorem leftDomain : leftRaw.inProtocolDomain 1 := by
  simp [leftRaw, leftView, PeaceView.toState, AgentState.inProtocolDomain]
theorem rightDomain : rightRaw.inProtocolDomain 1 := by
  simp [rightRaw, rightView, PeaceView.toState, AgentState.inProtocolDomain]
theorem tailDomain : tailRaw.inProtocolDomain 1 := by
  simp [tailRaw, tailView, PeaceView.toState, AgentState.inProtocolDomain]
def topStall : Fin 2 := ⟨1, by decide⟩
def pack (u : AgentState 2) (hu : u.inProtocolDomain 1) : ExpiringAgentState 2 1 1 :=
  ⟨⟨BoundedAgentState.ofDomain u hu, false⟩, topStall⟩
def carrier (b : ExpiringAgentState 2 1 1) (r : SpliceRole) : R1AgentStateV4 2 1 1 :=
  { splice := { base := b, spliceRole := r }, repairPending := false }

/-- Variant A: site 0 front (leader), site 1 neutral follower. -/
def startA : R1ConfigV6 3 2 1 1 := fun i =>
  if i = 0 then liftAgentV6 (carrier (pack leftRaw leftDomain) .front)
  else if i = 1 then liftAgentV6 (carrier (pack rightRaw rightDomain) .none)
  else liftAgentV6 (carrier (pack tailRaw tailDomain) .none)

/-- Variant B: site 0 neutral leader, site 1 a host fence. -/
def startB : R1ConfigV6 3 2 1 1 := fun i =>
  if i = 0 then liftAgentV6 (carrier (pack leftRaw leftDomain) .none)
  else if i = 1 then setTicketV6 (liftAgentV6 (carrier (pack rightRaw rightDomain) .none)) true
  else liftAgentV6 (carrier (pack tailRaw tailDomain) .none)

def afterAe : R1ConfigV6 3 2 1 1 := stepV10e hTwo hOne hOneTwo ring3 startA 0
def afterBe : R1ConfigV6 3 2 1 1 := stepV10e hTwo hOne hOneTwo ring3 startB 0
def afterAg : R1ConfigV6 3 2 1 1 := stepV10g hTwo hOne hOneTwo ring3 startA 0
def afterBg : R1ConfigV6 3 2 1 1 := stepV10g hTwo hOne hOneTwo ring3 startB 0

theorem startA_safe : SpliceSafeV7 hTwo ring3 startA := by decide
theorem startB_safe : SpliceSafeV7 hTwo ring3 startB := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- The served row is the physical hold in both variants. -/
theorem rowA_is_physicalHold :
    rowV10e hTwo hOne hOneTwo (startA 0) (startA (ring3.rightNeighbor 0)) =
      physicalHoldV6 hTwo hOne hOneTwo (startA 0) (startA (ring3.rightNeighbor 0)) := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem rowB_is_physicalHold :
    rowV10e hTwo hOne hOneTwo (startB 0) (startB (ring3.rightNeighbor 0)) =
      physicalHoldV6 hTwo hOne hOneTwo (startB 0) (startB (ring3.rightNeighbor 0)) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- The physical hold deletes the leader at site 0. -/
theorem leader_deleted :
    (startA 0).carrier.splice.base.core.core.leader = true ∧
      (afterAe 0).carrier.splice.base.core.core.leader = false ∧
      (startB 0).carrier.splice.base.core.core.leader = true ∧
      (afterBe 0).carrier.splice.base.core.core.leader = false := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem afterAe_unprotected_danger :
    PreparedDangerAt hTwo ring3 (projectV6 afterAe) 0 ∧ ¬ ProtectedSpliceEdgeV7 ring3 afterAe 0 := by
  decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem afterBe_unprotected_danger :
    PreparedDangerAt hTwo ring3 (projectV6 afterBe) 0 ∧ ¬ ProtectedSpliceEdgeV7 ring3 afterBe 0 := by
  decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem afterAg_unprotected_danger :
    PreparedDangerAt hTwo ring3 (projectV6 afterAg) 0 ∧ ¬ ProtectedSpliceEdgeV7g ring3 afterAg 0 := by
  decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem afterBg_unprotected_danger :
    PreparedDangerAt hTwo ring3 (projectV6 afterBg) 0 ∧ ¬ ProtectedSpliceEdgeV7g ring3 afterBg 0 := by
  decide

/-- `SpliceSafeV7` is not preserved by `stepV10e` with a leader present. -/
theorem stepV10e_not_safe_with_leader :
    SpliceSafeV7 hTwo ring3 startA ∧ ¬ SpliceSafeV7 hTwo ring3 (stepV10e hTwo hOne hOneTwo ring3 startA 0) :=
  ⟨startA_safe, fun h => afterAe_unprotected_danger.2 (h.1 0 afterAe_unprotected_danger.1)⟩

/-- `SpliceSafeV7g` is not preserved by `stepV10g` with a leader present, from a `SpliceSafeV7` start. -/
theorem stepV10g_not_safe_with_leader :
    SpliceSafeV7g hTwo ring3 startA ∧ ¬ SpliceSafeV7g hTwo ring3 (stepV10g hTwo hOne hOneTwo ring3 startA 0) :=
  ⟨spliceSafeV7g_of_spliceSafeV7 hTwo ring3 startA startA_safe,
    fun h => afterAg_unprotected_danger.2 (h.1 0 afterAg_unprotected_danger.1)⟩

end B9V10eLeaderPhysicalDeletionNoGo
