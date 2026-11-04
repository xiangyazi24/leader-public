import Leader.Wu.Birth.ShortDoneTerminalHandoffExpiry

namespace BirthShortDoneTerminalHandoffPendingCounterexample

open PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol
open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair BirthDisposalRouteInvariant BirthGenerationDone

open K2BirthDispatcher K2BirthLeaderNormalize
  BirthShortDoneTerminalHost BirthShortDoneTerminalEntryCut
  BirthShortDoneTerminalHandoffExpiry

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

private theorem psi_pos : 0 < 2 := by decide
private theorem width_pos : 0 < 1 := by decide
private theorem width_le : 1 ≤ 2 := by decide

private def peace2 (j : Fin 2) : PeaceView 2 :=
  { leader := false
    label := j
    shield := false
    bullet := 0
    signal_B := 0 }

private def rawBase (j : Fin 2) : AgentState 2 :=
  PeaceView.toState (peace2 j)

/-- Nonterminal resident carrying both the terminal-bound main component and
an action-4 control. It is not pending yet because its resident label is 0. -/
private def sourceRaw : AgentState 2 :=
  { rawBase (0 : Fin 2) with
      path := .some 1 0
      path2 := some ⟨0, 0, 0, 4⟩ }

/-- Empty terminal receiver. -/
private def receiverRaw : AgentState 2 :=
  rawBase (1 : Fin 2)

private theorem sourceRaw_domain : sourceRaw.inProtocolDomain 0 := by
  simp [sourceRaw, rawBase, peace2, PeaceView.toState,
    AgentState.inProtocolDomain]

private theorem receiverRaw_domain : receiverRaw.inProtocolDomain 0 := by
  simp [receiverRaw, rawBase, peace2, PeaceView.toState,
    AgentState.inProtocolDomain]

private def source : ExpiringAgentState 2 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain sourceRaw sourceRaw_domain, false⟩, 0⟩

private def receiver : ExpiringAgentState 2 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain receiverRaw receiverRaw_domain, false⟩, 0⟩

private def leftE : ExpiringAgentState 2 0 0 :=
  prepareExpiringDisposal psi_pos source

private def rightE : ExpiringAgentState 2 0 0 :=
  prepareExpiringDisposal psi_pos receiver

private def leftA : AuthorizedAgentState 2 :=
  normalizeDeletion leftE.core.erase

private def rightA : AuthorizedAgentState 2 :=
  normalizeDeletion rightE.core.erase

private def before : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  generationBeforeMoveEntryWidth psi_pos width_pos width_le 0 leftA rightA

private def moved : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedDoneMove psi_pos before.1 before.2

private def checked : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  doneThroughCheckEntryWidth psi_pos width_pos width_le 0 leftA rightA

private def out : ExpiringAgentState 2 0 0 :=
  (row psi_pos width_pos width_le source receiver).2

/-- Raw/prepared/normalized audit: action payload, permission and resident
labels are stated separately on both sides of normalization. -/
theorem prepared_audit :
    source.core.erase.core.label = (0 : Fin 2) ∧
    source.core.erase.core.path = .some 1 0 ∧
    source.core.erase.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
    source.core.erase.path0Crossed = false ∧
    pendingTerminalDisposal psi_pos source.core.erase.core = false ∧
    leftE.core.erase.core.label = (0 : Fin 2) ∧
    leftE.core.erase.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
    leftE.core.erase.path0Crossed = false ∧
    leftA.core.label = (0 : Fin 2) ∧
    leftA.core.path = .some 1 0 ∧
    leftA.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
    leftA.path0Crossed = false ∧
    deletionActive leftA = false ∧
    rightE.core.erase.core.label = (1 : Fin 2) ∧
    rightE.core.erase.path0Crossed = false ∧
    rightA.core.label = (1 : Fin 2) ∧
    rightA.core.path = .bot ∧
    rightA.core.path2 = none ∧
    rightA.path0Crossed = false := by
  decide

/-- The control application makes the moved receiver deleting, then the later
aligned CHECK re-arms only the state while retaining action 4 and false permit. -/
theorem move_then_check_audit :
    before.1.core.path = .some 1 0 ∧
    before.1.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
    before.2.core.label = (1 : Fin 2) ∧
    before.2.core.path = .bot ∧
    pathMovedRight before.1.core before.2.core
      moved.1.core moved.2.core = true ∧
    moved.2.core.label = (1 : Fin 2) ∧
    moved.2.core.path = .some 1 0 ∧
    moved.2.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
    moved.2.path0Crossed = false ∧
    moved.2.core.state = .eliminate_signal ∧
    checked.2.core.label = (1 : Fin 2) ∧
    checked.2.core.path = .some 1 0 ∧
    checked.2.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
    checked.2.path0Crossed = false ∧
    checked.2.core.state = .CHECK_ready := by
  decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 32768 in
/-- Counterexample to the proposed semantic strengthening of the inactive
handoff case. These are exactly the public handoff hypotheses, but the final
surviving receiver is both deletion-inactive and `DisposalDue`. -/
theorem inactive_surviving_handoff_can_be_disposal_due :
    deletionActive leftA = false ∧
    rightA.core.path = .bot ∧
    pathMovedRight before.1.core before.2.core
      moved.1.core moved.2.core = true ∧
    moved.2.core.path ≠ .bot ∧
    out.core.erase.core.label = (1 : Fin 2) ∧
    out.core.erase.core.path = .some 1 0 ∧
    out.core.erase.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
    out.core.erase.path0Crossed = false ∧
    out.core.erase.core.state = .CHECK_ready ∧
    deletionActive out.core.erase = false ∧
    pendingTerminalDisposal psi_pos out.core.erase.core = true ∧
    DisposalDue psi_pos out.core.erase := by
  have h :
      deletionActive leftA = false ∧
      rightA.core.path = .bot ∧
      pathMovedRight before.1.core before.2.core
        moved.1.core moved.2.core = true ∧
      moved.2.core.path ≠ .bot ∧
      out.core.erase.core.label = (1 : Fin 2) ∧
      out.core.erase.core.path = .some 1 0 ∧
      out.core.erase.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      out.core.erase.path0Crossed = false ∧
      out.core.erase.core.state = .CHECK_ready ∧
      deletionActive out.core.erase = false ∧
      pendingTerminalDisposal psi_pos out.core.erase.core = true := by
    decide
  rcases h with
    ⟨hleft, hright, hmove, hmoved, hlabel, hpath, hpath2,
      hpermit, hstate, hinactive, hpending⟩
  refine ⟨hleft, hright, hmove, hmoved, hlabel, hpath, hpath2,
    hpermit, hstate, hinactive, hpending, ?_⟩
  unfold DisposalDue
  constructor
  · rw [hpath]
    simp
  · exact Or.inr hpending

#print axioms BirthShortDoneTerminalHandoffPendingCounterexample.prepared_audit
#print axioms BirthShortDoneTerminalHandoffPendingCounterexample.move_then_check_audit
#print axioms BirthShortDoneTerminalHandoffPendingCounterexample.inactive_surviving_handoff_can_be_disposal_due

end BirthShortDoneTerminalHandoffPendingCounterexample
