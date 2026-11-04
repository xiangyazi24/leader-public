import Leader.Wu.Splice.ZeroRefreshBlockMass

set_option autoImplicit false

namespace B9OrphanFenceFixture

open B9SpliceControllerR1Table B9SpliceControllerR1TableV2 B9SpliceControllerR1TableV3
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b B9SpliceV10cLiveness B9SpliceBlockDrainMass PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open PPLLExpiringComparisonRepair B9SpliceControllerR1TableV4 PPLL PPLLRepair PPLLDomain PPLLResearchFormulation PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair BirthShortDoneTerminalBirthSources B9SpliceControllerR1Table B9SpliceControllerR1TableV2 

private theorem hOne : 0 < 1 := by decide
private theorem hFour : 0 < 4 := by decide
private theorem hLe : 1 <= 1 := by decide
private def ring4 : DirectedRing 4 := ⟨hFour⟩
set_option linter.defProp false
private def peace1 : PeaceView 1 :=
  { leader := false, label := 0, shield := false, bullet := 0, signal_B := 0 }
private def rawL : AgentState 1 := PeaceView.toState peace1
private def rawR : AgentState 1 := { PeaceView.toState peace1 with write_state := .depart }
private theorem rawLDomain : rawL.inProtocolDomain 1 := by
  simp [rawL, peace1, PeaceView.toState, AgentState.inProtocolDomain]
private theorem rawRDomain : rawR.inProtocolDomain 1 := by
  simp [rawR, peace1, PeaceView.toState, AgentState.inProtocolDomain]
private def topStall : Fin 2 := ⟨1, by decide⟩
private def expL : ExpiringAgentState 1 1 1 :=
  ⟨⟨BoundedAgentState.ofDomain rawL rawLDomain, false⟩, topStall⟩
private def expR : ExpiringAgentState 1 1 1 :=
  ⟨⟨BoundedAgentState.ofDomain rawR rawRDomain, false⟩, topStall⟩
private def neutralCarrier (b : ExpiringAgentState 1 1 1) : R1AgentStateV4 1 1 1 :=
  { splice := { base := b, spliceRole := .none }, repairPending := false }

/-- Host fence: role none, no pending repair, ticket set. -/
private def fence : R1AgentStateV6 1 1 1 := setTicketV6 (liftAgentV6 (neutralCarrier expL)) true
/-- Orphan reserved front: role front, pending, no ticket (physical core with a departing write). -/
private def frontR : R1AgentStateV6 1 1 1 := liftAgentV6 (setControl (neutralCarrier expR) .front true)
private def frontL : R1AgentStateV6 1 1 1 := liftAgentV6 (setControl (neutralCarrier expL) .front true)
private def clearCell : R1AgentStateV6 1 1 1 := liftAgentV6 (neutralCarrier expL)

private def CA : R1ConfigV6 4 1 1 1 := fun i =>
  if i = (0 : Fin 4) then fence else if i = (1 : Fin 4) then frontR else clearCell
private def CB : R1ConfigV6 4 1 1 1 := fun i =>
  if i = (0 : Fin 4) then fence else if i = (1 : Fin 4) then frontL else clearCell

private def D0 := stepV10c hOne hOne hLe ring4 CA 0
private def cyc : List (Fin 4) := [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]
-- which V7 fence row fired on edge 0?
-- safety of the start and of the deadlocked state
-- which row consumed the fence on edge 0?
/-! ## Reachability: the table's own MoveStop manufactures the orphan. -/
private def settledPred : R1AgentStateV6 1 1 1 :=
  liftAgentV6 (setControl (neutralCarrier expL) .predecessorArmed false)
private def CA2 : R1ConfigV6 4 1 1 1 := fun i =>
  if i = (0 : Fin 4) then settledPred else if i = (1 : Fin 4) then frontR else clearCell
private def D2 := stepV10c hOne hOne hLe ring4 CA2 0

/-! ## The named B9 bridge is false: the deadlocked orphan state is live, safe and has no productive edge. -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
private theorem D0_live : LiveNonClearV10c hOne ring4 D0 := by
  unfold LiveNonClearV10c
  refine ⟨by decide, by decide⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
private theorem D0_flat (e : Fin 4) :
    controllerPotentialV6 (stepV10c hOne hOne hLe ring4 D0 e) = controllerPotentialV6 D0 := by
  revert e
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
private theorem D0_notClear (e : Fin 4) :
    ¬ RolesClearV7 (stepV10c hOne hOne hLe ring4 D0 e) := by
  revert e
  decide

theorem no_uniform_productive_port_adapter_ring4 :
    ¬ ∃ A : BirthB1DrainCoupling.PortBlockAdapter
        (R1ConfigV6 4 1 1 1) 4,
      ∀ C : R1ConfigV6 4 1 1 1,
        LiveNonClearV10c hOne ring4 C →
          ControllerProductiveServiceV10c
            hOne hOne hLe ring4 C (A.ports C).a := by
  rintro ⟨A, hport⟩
  have hprod := hport D0 D0_live
  unfold ControllerProductiveServiceV10c at hprod
  rcases hprod with hlt | hclear
  · rw [D0_flat] at hlt
    exact Nat.lt_irrefl _ hlt
  · exact D0_notClear _ hclear

#print axioms no_uniform_productive_port_adapter_ring4


/-! ## Candidate fix: an orphan reserved front becomes a host fence. -/

/-- Turn a cell into the V7 host fence: role none, no pending repair, ticket set. -/
def fenceV6 (u : R1AgentStateV6 1 1 1) : R1AgentStateV6 1 1 1 :=
  setTicketV6 (setControlV6 u .none false) true

def rowV10d (l r : R1AgentStateV6 1 1 1) : R1AgentStateV6 1 1 1 × R1AgentStateV6 1 1 1 :=
  if OrphanReservedFrontGuardV3 l.carrier r.carrier then (l, fenceV6 r)
  else rowV10c hOne hOne hLe l r

def stepV10d (C : R1ConfigV6 4 1 1 1) (e : Fin 4) : R1ConfigV6 4 1 1 1 :=
  let j := ring4.rightNeighbor e
  if j = e then C else
    let q := rowV10d (C e) (C j)
    fun i => if i = e then q.1 else if i = j then q.2 else C i

private def E1 := stepV10d D2 0
-- from the very start CA2 under the new row: full cycle potentials
-- the fence+orphan start under the new row
end B9OrphanFenceFixture
