import Leader.Wu.Splice.BusyFrontTable

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV9ProgressEnabled

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9

variable {n psi width kappa tau : Nat}

private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hOneTwo : 1 <= 2 := by decide

private def ring1 : DirectedRing 1 := ⟨hOne⟩

/-- Smallest live controller mark: a neutral host fence on the singleton ring. -/
def singletonFenceV9 : R1ConfigV6 1 2 0 0 := fun _ =>
  setTicketV6
    (liftAgentV6
      (B9SpliceR2AttackRerun.xcell
        true (0 : Fin 2) false .none false))
    true

private instance instDecidableHostFenceProgressV9
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (HostFenceShapeV7 u) := by
  unfold HostFenceShapeV7
  infer_instance

private instance instDecidableTicketShapeProgressV9
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (TicketShapeV7 u) := by
  unfold TicketShapeV7 HostFenceShapeV7 ReservedFrontHoldGuard
  infer_instance

private instance instDecidablePreparedDangerProgressV9
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring (projectV6 C) e) := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableProtectedProgressV9
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (ProtectedSpliceEdgeV7 ring C e) := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3
    HostFenceShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only
  infer_instance

private instance instDecidableProvenanceProgressV9
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) :
    Decidable (ProvenanceSafeV7 ring C) := by
  unfold ProvenanceSafeV7
  infer_instance

private instance instDecidableSpliceSafeProgressV9
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) :
    Decidable (SpliceSafeV7 hpsi ring C) := by
  unfold SpliceSafeV7
  infer_instance

private instance instDecidableRolesClearProgressV9
    (C : R1ConfigV6 n psi kappa tau) :
    Decidable (RolesClearV7 C) := by
  unfold RolesClearV7
  infer_instance

/-- Closed smallest counterexample.

The state is safe because its only ticket is a legal host fence; any geometric
danger is therefore fence-owned. It is live because the ticket is true. The
only scheduler edge is a self-loop, so `stepV9` returns the input literally. -/
theorem singletonFenceV9_literal :
    SpliceSafeV7 hTwo ring1 singletonFenceV9 /\
    not (RolesClearV7 singletonFenceV9) /\
    HostFenceShapeV7 (singletonFenceV9 (0 : Fin 1)) /\
    (forall e i : Fin 1,
      stepV9 hTwo hOne hOneTwo ring1 singletonFenceV9 e i =
        singletonFenceV9 i) := by
  decide

/-- Therefore the exact current `V9ProgressEnabled` proposition is false. -/
theorem v9ProgressEnabled_false :
    ¬ (V9ProgressEnabled
      (psi := 2) (width := 1) (kappa := 0) (tau := 0)
      hTwo hOne hOneTwo ring1) := by
  intro h
  rcases h singletonFenceV9
      singletonFenceV9_literal.1 singletonFenceV9_literal.2.1 with
    ⟨e, i, hchange⟩
  exact (bne_iff_ne.mp hchange) (singletonFenceV9_literal.2.2.2 e i)

end B9SpliceV9ProgressEnabled

#print axioms B9SpliceV9ProgressEnabled.singletonFenceV9_literal
#print axioms B9SpliceV9ProgressEnabled.v9ProgressEnabled_false
