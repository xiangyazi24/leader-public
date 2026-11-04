import Leader.Wu.Splice.GarbageDrainBlockMass

set_option autoImplicit false
set_option Elab.async false

/-! # The V10b handoff arm deadlocks under V10d on the n = 3 handoff fixture

After the handoff (fence, clear target) -> (predecessorArmed/false, front/true) and one MoveSeek
service that mints the front's ticket, the configuration is SpliceSafeV7, not roles-clear, still
carries the physical barrier on edge 0, and is a fixed point of every stepV10d service: no edge is
controller-productive and no edge performs any physical work.  This is not the h_field two-cycle
of the window-law fixture; every field is literally unchanged. -/

namespace B9HandoffDeadlockV10d

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2 B9SpliceControllerR1TableV3
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
  B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b B9SpliceV10cLiveness
  B9SpliceBlockDrainMass B9SpliceTableV10d

private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private def ring3 : DirectedRing 3 := ⟨hThree⟩

private instance instDecidableHostFenceShape (u : R1AgentStateV6 2 1 1) :
    Decidable (HostFenceShapeV7 u) := by unfold HostFenceShapeV7; infer_instance
private instance instDecidableTicketShape (u : R1AgentStateV6 2 1 1) :
    Decidable (TicketShapeV7 u) := by
  unfold TicketShapeV7 HostFenceShapeV7 ReservedFrontHoldGuard; infer_instance
private instance instDecidablePreparedDanger (C : R1ConfigV6 3 2 1 1) (e : Fin 3) :
    Decidable (PreparedDangerAt hTwo ring3 (projectV6 C) e) := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6; dsimp only; unfold isBarrier; infer_instance
private instance instDecidableProtected (C : R1ConfigV6 3 2 1 1) (e : Fin 3) :
    Decidable (ProtectedSpliceEdgeV7 ring3 C e) := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 HostFenceShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only; infer_instance
private instance instDecidableProvenance (C : R1ConfigV6 3 2 1 1) :
    Decidable (ProvenanceSafeV7 ring3 C) := by unfold ProvenanceSafeV7; infer_instance
private instance instDecidableSpliceSafe (C : R1ConfigV6 3 2 1 1) :
    Decidable (SpliceSafeV7 hTwo ring3 C) := by unfold SpliceSafeV7; infer_instance
private instance instDecidableRolesClear (C : R1ConfigV6 3 2 1 1) :
    Decidable (RolesClearV7 C) := by unfold RolesClearV7; infer_instance

def start : R1ConfigV6 3 2 1 1 := q11874StartV10b
def after1 : R1ConfigV6 3 2 1 1 := stepV10d hTwo hOne hOneTwo ring3 start 0
def after2 : R1ConfigV6 3 2 1 1 := stepV10d hTwo hOne hOneTwo ring3 after1 0

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem handoff_then_seek :
    controllerPotentialV6 start = 1 ∧ controllerPotentialV6 after1 = 11 ∧
    controllerPotentialV6 after2 = 9 := by
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem after2_live : LiveNonClearV10c hTwo ring3 after2 := by
  unfold LiveNonClearV10c; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
theorem after2_barrier :
    LocalPreparedBarrier hTwo (after2 0).carrier (after2 1).carrier := by
  unfold LocalPreparedBarrier; dsimp only; unfold isBarrier; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- Every V10d service is the literal identity on `after2`. -/
theorem after2_fixed_point :
    ∀ e i : Fin 3, stepV10d hTwo hOne hOneTwo ring3 after2 e i = after2 i := by
  decide

theorem after2_no_productive_edge :
    ∀ e : Fin 3, ¬ ControllerProductiveServiceV10d hTwo hOne hOneTwo ring3 after2 e := by
  intro e hprod
  have heq : stepV10d hTwo hOne hOneTwo ring3 after2 e = after2 :=
    funext (after2_fixed_point e)
  unfold ControllerProductiveServiceV10d at hprod
  rw [heq] at hprod
  rcases hprod with hdrop | hclear
  · exact absurd hdrop (Nat.lt_irrefl _)
  · exact after2_live.2 hclear

/-- Hence the V10d one-service bridge is false at these parameters. -/
theorem no_bridge_service_clause_V10d :
    ¬ B9SpliceBlockDrainMassV10d.OneServiceBlockBridgeV10d (kappa := 1) (tau := 1)
      hTwo hOne hOneTwo ring3 := by
  intro ⟨A, _, hserv, _⟩
  exact after2_no_productive_edge _ (hserv after2 after2_live)

end B9HandoffDeadlockV10d
