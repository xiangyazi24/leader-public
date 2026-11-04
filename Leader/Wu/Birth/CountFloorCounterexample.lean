import Leader.Wu.Birth.NoUndoLaw

namespace BirthB1CountFloorAudit

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive
open BirthShortDoneTerminalPassiveR4

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

private theorem hpsi2 : 0 < 2 := by decide
private theorem h2 : 2 <= 2 := by decide

private def ring4 : DirectedRing 4 := ⟨by decide⟩
private def anchor4 : Fin 4 := 0
private def boundaryEdge4 : Fin 4 := 2
private def padEdge4 : Fin 4 := 3

private def regs (label : Fin 2) (count : Nat) : Registers 2 where
  label := label
  h := false
  carry := false
  reset := false
  count := count
  wait := true
  bit := false
  phase := false
  writer := .none

private def sourceRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell (regs 0 0)
  else if i = 1 then cell (regs 1 1)
  else if i = 2 then cell (regs 0 0)
  else { cell (regs 1 0) with reset_cmd := true }

private theorem sourceRaw_domain (i : Fin 4) :
    (sourceRaw i).inProtocolDomain 2 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [sourceRaw, regs, AgentState.inProtocolDomain, cell]

private def sourcePack (i : Fin 4) : ExpiringAgentState 2 2 0 :=
  ⟨⟨BoundedAgentState.ofDomain
      (sourceRaw i) (sourceRaw_domain i), false⟩, 0⟩

private def sourceC : BirthB1NoUndoLaw.FC 4 2 2 0 :=
  fun i => sourcePack i

private def afterBoundary : BirthB1NoUndoLaw.FC 4 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2 ring4 sourceC boundaryEdge4

/-- The extra edge moves the outside reset onto the physical anchor. -/
private def badStart : BirthB1NoUndoLaw.FC 4 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2 ring4 afterBoundary padEdge4

private def afterCurrent : BirthB1NoUndoLaw.FC 4 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2 ring4 badStart anchor4

private def afterFloor : BirthB1NoUndoLaw.FC 4 2 2 0 :=
  BirthB1NoUndoLaw.stepGuarded
    hpsi2 h2 ring4 badStart anchor4

set_option maxHeartbeats 0 in
set_option maxRecDepth 262144 in
/-- The current SUPPRESS cleanup really lowers the tracked clock, while the
proposed global floor restores the stale input value. -/
theorem literal_floor_blocks_terminal_reset :
    (badStart anchor4).core.erase.core.reset_cmd = true ∧
    RowPreCap2 hpsi2 h2 2 ring4 badStart anchor4 ∧
    BirthPhaseWait2BlockProgress.shortCountAt
      ring4 anchor4 badStart = 1 ∧
    BirthPhaseWait2BlockProgress.shortCountAt
      ring4 anchor4 afterCurrent = 0 ∧
    BirthPhaseWait2BlockProgress.shortCountAt
      ring4 anchor4 afterFloor = 1 := by
  unfold RowPreCap2 RowCap2
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 262144 in
/-- A leader guard does not separate this reset: the bad scheduled pair is
already leaderless. -/
theorem literal_reset_edge_is_leaderless :
    (badStart anchor4).core.erase.core.leader = false ∧
    (badStart (ring4.rightNeighbor anchor4)).core.erase.core.leader = false := by
  decide

#print axioms BirthB1CountFloorAudit.literal_floor_blocks_terminal_reset
#print axioms BirthB1CountFloorAudit.literal_reset_edge_is_leaderless

end BirthB1CountFloorAudit
