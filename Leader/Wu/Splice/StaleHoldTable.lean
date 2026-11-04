import Leader.Wu.Splice.HostFenceTable


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceControllerR1TableV8


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerV3Safety
  B9SpliceControllerR1TableV4 B9SpliceControllerV4Safety
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7


variable {n psi width kappa tau : Nat}


/-- The exact stale right-predecessor shape that must not reach the host. -/
def RightStalePredecessorHoldGuardV8
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  role l.carrier = .none /\
    l.carrier.repairPending = false /\
    l.acquireTicket = false /\
    role r.carrier = .predecessorArmed /\
    r.carrier.repairPending = false /\
    r.acquireTicket = false


private instance instDecidableRightStalePredecessorHoldGuardV8
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (RightStalePredecessorHoldGuardV8 l r) := by
  unfold RightStalePredecessorHoldGuardV8
  infer_instance


/-- V8 is V7 plus one certificate-preserving HOLD above the whole V7 table. -/
def rowV8
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  if RightStalePredecessorHoldGuardV8 l r then (l, r)
  else rowV7 hpsi hwidth hle l r


def stepV8
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n) : R1ConfigV6 n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then C
  else
    let q := rowV8 hpsi hwidth hle (C e) (C j)
    fun i => if i = e then q.1 else if i = j then q.2 else C i


def controllerStateFactorV8 : Nat := controllerStateFactorV7


theorem controllerStateFactorV8_eq : controllerStateFactorV8 = 16 := by
  simpa [controllerStateFactorV8] using controllerStateFactorV7_eq


private theorem stepV8_eq_self_of_row_self
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n)
    (hrow : rowV8 hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e))) :
    stepV8 hpsi hwidth hle ring C e = C := by
  funext i
  by_cases hself : ring.rightNeighbor e = e
  · simp [stepV8, hself]
  · by_cases hi : i = e
    · subst i
      simp [stepV8, hself, hrow]
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simp [stepV8, hself, hrow]
      · simp [stepV8, hself, hrow, hi, hj]


/-- The new row is literal stutter, so every V7 safety certificate survives. -/
theorem rightStalePredecessorHold_preserves_spliceSafeV7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e : Fin n) (hsafe : SpliceSafeV7 hpsi ring C)
    (hguard : RightStalePredecessorHoldGuardV8
      (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeV7 hpsi ring (stepV8 hpsi hwidth hle ring C e) := by
  have hrow : rowV8 hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e)) := by
    simp [rowV8, hguard]
  rw [stepV8_eq_self_of_row_self hpsi hwidth hle ring C e hrow]
  exact hsafe


/-! Closed decidability for the two direct safety rechecks below. -/
private instance instDecidableHostFenceShapeV8
    (u : R1AgentStateV6 psi kappa tau) : Decidable (HostFenceShapeV7 u) := by
  unfold HostFenceShapeV7
  infer_instance


private instance instDecidableTicketShapeV8
    (u : R1AgentStateV6 psi kappa tau) : Decidable (TicketShapeV7 u) := by
  unfold TicketShapeV7 HostFenceShapeV7 ReservedFrontHoldGuard
  infer_instance


private instance instDecidablePreparedDangerV8
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring (projectV6 C) e) := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6
  dsimp only
  unfold isBarrier
  infer_instance


private instance instDecidableProtectedSpliceEdgeV8
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (ProtectedSpliceEdgeV7 ring C e) := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3
    HostFenceShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only
  infer_instance


private instance instDecidableProvenanceSafeV8
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) :
    Decidable (ProvenanceSafeV7 ring C) := by
  unfold ProvenanceSafeV7
  infer_instance


private instance instDecidableSpliceSafeV8
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) : Decidable (SpliceSafeV7 hpsi ring C) := by
  unfold SpliceSafeV7
  infer_instance


/-- Exact-prefix replay checker: every V8 service must equal V7 before moving on. -/
def sameAlongV8V7
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) :
    R1ConfigV6 n psi kappa tau -> List (Fin n) -> Bool
  | _, [] => true
  | C, e :: es =>
      decide (forall i, stepV8 hpsi hwidth hle ring C e i =
        stepV7 hpsi hwidth hle ring C e i) &&
      sameAlongV8V7 hpsi hwidth hle ring
        (stepV8 hpsi hwidth hle ring C e) es


private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private theorem hOneThree : 1 <= 3 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private theorem hTwoThree : 2 <= 3 := by decide
private def ring2 : DirectedRing 2 := ⟨hTwo⟩
private def ring3 : DirectedRing 3 := ⟨hThree⟩
private def ring4 : DirectedRing 4 := ⟨by decide⟩
private def ring5 : DirectedRing 5 := ⟨by decide⟩


/-- The V7 counterexample now selects HOLD, stutters, and remains safe. -/
def ordinaryHostStalePredAfterV8 : R1ConfigV6 3 2 1 1 :=
  stepV8 hTwo hTwo hTwoLe ring3 ordinaryHostStalePredStartV7 (0 : Fin 3)


theorem ordinaryHost_stale_pred_held_safe_v8 :
    RightStalePredecessorHoldGuardV8
      (ordinaryHostStalePredStartV7 (0 : Fin 3))
      (ordinaryHostStalePredStartV7 (1 : Fin 3)) /\
    rowV8 hTwo hTwo hTwoLe
      (ordinaryHostStalePredStartV7 (0 : Fin 3))
      (ordinaryHostStalePredStartV7 (1 : Fin 3)) =
      (ordinaryHostStalePredStartV7 0, ordinaryHostStalePredStartV7 1) /\
    (forall i, ordinaryHostStalePredAfterV8 i = ordinaryHostStalePredStartV7 i) /\
    SpliceSafeV7 hTwo ring3 ordinaryHostStalePredAfterV8 := by
  decide


/-- The neutral row and both fence services are byte-for-byte V7. -/
def q11703ArmedAfterV8 : R1ConfigV6 3 2 1 1 :=
  stepV8 hTwo hTwo hTwoLe ring3 q11703StartV7 (0 : Fin 3)
def q11703Fence1V8 : R1ConfigV6 3 2 1 1 :=
  stepV8 hTwo hTwo hTwoLe ring3 q11703ArmedAfterV8 (1 : Fin 3)
def q11703Fence2V8 : R1ConfigV6 3 2 1 1 :=
  stepV8 hTwo hTwo hTwoLe ring3 q11703Fence1V8 (2 : Fin 3)


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem q11703_fence_run_rechecked_v8 :
    sameAlongV8V7 hTwo hTwo hTwoLe ring3 q11703StartV7 [0, 1, 2] = true /\
    SpliceSafeV7 hTwo ring3 q11703ArmedAfterV8 /\
    SpliceSafeV7 hTwo ring3 q11703Fence1V8 /\
    SpliceSafeV7 hTwo ring3 q11703Fence2V8 := by
  decide


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- Every old fixture word follows V7 at every prefix. -/
theorem v6_v7_fixture_census_replays_v8 :
    sameAlongV8V7 hTwo hTwo hTwoLe ring3 frontAcquireBackedStart3V6 [1] = true /\
    sameAlongV8V7 hTwo hTwo hTwoLe ring3 pendingOwnerAbortStart3V6 [0] = true /\
    sameAlongV8V7 hThree hOne hOneThree ring2 moveAcquireAbortStart2V6 [1] = true /\
    sameAlongV8V7 hThree hOne hOneThree ring2 orphanReservedFrontStart2V6 [0] = true /\
    sameAlongV8V7 hThree hOne hOneThree ring2 q11668Start2V6 [0] = true /\
    sameAlongV8V7 hThree hTwo hTwoThree ring4 protocolStopStart4V6 [0] = true /\
    sameAlongV8V7 hTwo hOne hOneTwo ring2 q11681Start2V6 [0] = true /\
    sameAlongV8V7 hTwo hTwo hTwoLe ring3
      (liftConfigV6 B9SpliceR2AttackRerun.loop3Start) [0, 1, 0] = true /\
    sameAlongV8V7 hTwo hTwo hTwoLe ring4
      (liftConfigV6 B9SpliceR2AttackRerun.loop4Start) [0, 2, 0, 2] = true /\
    sameAlongV8V7 hTwo hTwo hTwoLe ring5
      (liftConfigV6 B9SpliceR2AttackRerun.loop5Start) [0, 1, 0] = true /\
    sameAlongV8V7 hTwo hTwo hTwoLe ring4
      (liftConfigV6 B9SpliceR2AttackRerun.q11592Start4) [1, 1] = true /\
    sameAlongV8V7 hTwo hTwo hTwoLe ring5
      (liftConfigV6 B9SpliceR2AttackRerun.followerStart5) [0] = true /\
    sameAlongV8V7 hTwo hTwo hTwoLe ring3
      (liftConfigV6 B9SpliceR2AttackRerun.stagedStart3)
      B9SpliceR2AttackRerun.starvationWord3 = true /\
    sameAlongV8V7 hTwo hTwo hTwoLe ring5
      (liftConfigV6 B9SpliceControllerR1TableV3.followerStart5V3)
      B9SpliceControllerR1TableV3.followerWord5V3 = true := by
  decide


end B9SpliceControllerR1TableV8


#print axioms B9SpliceControllerR1TableV8.controllerStateFactorV8_eq
#print axioms B9SpliceControllerR1TableV8.rightStalePredecessorHold_preserves_spliceSafeV7
#print axioms B9SpliceControllerR1TableV8.ordinaryHost_stale_pred_held_safe_v8
#print axioms B9SpliceControllerR1TableV8.q11703_fence_run_rechecked_v8
#print axioms B9SpliceControllerR1TableV8.v6_v7_fixture_census_replays_v8
