import Leader.Wu.Birth.ShortDoneTerminalHandoffExpiry

namespace BirthShortDoneTerminalHandoffExpiryNonvacuity

open PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair BirthGenerationDone

open K2BirthDispatcher K2BirthLeaderNormalize
  BirthShortDoneTerminalHost BirthShortDoneTerminalEntryCut
  BirthShortDoneTerminalHandoffExpiry

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

private theorem psi_pos : 0 < 3 := by decide
private theorem width_pos : 0 < 2 := by decide
private theorem width_le : 2 ≤ 3 := by decide

/-- Quiet physical records; no WAIT, control, leader, comparison, or writer
material is preinstalled. -/
private def peace3 (j : Fin 3) : PeaceView 3 :=
  { leader := false
    label := j
    shield := false
    bullet := 0
    signal_B := 0 }

private def rawBase (j : Fin 3) : AgentState 3 :=
  PeaceView.toState (peace3 j)

/-- A bounded physical carrier ready to move right.  Its resident label agrees
with the payload label; the receiver below is deliberately label-misaligned so
CHECK does not manufacture a same-row equality fact. -/
private def moverRaw : AgentState 3 :=
  { rawBase (1 : Fin 3) with path := .some 1 0 }

private def liveRightRaw : AgentState 3 :=
  rawBase (0 : Fin 3)

/-- Same empty receiver, with only the existing reset command asserted. -/
private def endRightRaw : AgentState 3 :=
  { rawBase (0 : Fin 3) with reset_cmd := true }

private theorem moverRaw_domain : moverRaw.inProtocolDomain 0 := by
  simp [moverRaw, rawBase, peace3, PeaceView.toState,
    AgentState.inProtocolDomain]

private theorem liveRightRaw_domain : liveRightRaw.inProtocolDomain 0 := by
  simp [liveRightRaw, rawBase, peace3, PeaceView.toState,
    AgentState.inProtocolDomain]

private theorem endRightRaw_domain : endRightRaw.inProtocolDomain 0 := by
  simp [endRightRaw, rawBase, peace3, PeaceView.toState,
    AgentState.inProtocolDomain]

/-- `τ = 1`, but both input timers start at zero. -/
private def mover : ExpiringAgentState 3 0 1 :=
  ⟨⟨BoundedAgentState.ofDomain moverRaw moverRaw_domain, false⟩, 0⟩

private def liveRight : ExpiringAgentState 3 0 1 :=
  ⟨⟨BoundedAgentState.ofDomain liveRightRaw liveRightRaw_domain, false⟩, 0⟩

private def endRight : ExpiringAgentState 3 0 1 :=
  ⟨⟨BoundedAgentState.ofDomain endRightRaw endRightRaw_domain, false⟩, 0⟩

/-- Exact named cuts appearing in the public classification theorem. -/
private def leftA : AuthorizedAgentState 3 :=
  normalizeDeletion (prepareExpiringDisposal psi_pos mover).core.erase

private def rightA (r : ExpiringAgentState 3 0 1) : AuthorizedAgentState 3 :=
  normalizeDeletion (prepareExpiringDisposal psi_pos r).core.erase

private def before (r : ExpiringAgentState 3 0 1) :
    AuthorizedAgentState 3 × AuthorizedAgentState 3 :=
  generationBeforeMoveEntryWidth psi_pos width_pos width_le 0 leftA (rightA r)

private def moved (r : ExpiringAgentState 3 0 1) :
    AuthorizedAgentState 3 × AuthorizedAgentState 3 :=
  authorizedDoneMove psi_pos (before r).1 (before r).2

private def outR (r : ExpiringAgentState 3 0 1) : ExpiringAgentState 3 0 1 :=
  (row psi_pos width_pos width_le mover r).2

/-! Closed finite facts only.  These are not output assumptions supplied to the
public theorem; they compute the literal concrete inputs/cuts. -/

private theorem left_inactive : deletionActive leftA = false := by
  decide

private theorem live_right_empty : (rightA liveRight).core.path = .bot := by
  decide

private theorem live_moves :
    pathMovedRight (before liveRight).1.core (before liveRight).2.core
      (moved liveRight).1.core (moved liveRight).2.core = true := by
  decide

set_option maxRecDepth 32768 in
private theorem live_out_present :
    (outR liveRight).core.erase.core.path ≠ .bot := by
  decide

private theorem live_old_stall_not_fresh :
    liveRight.stall ≠ freshStall 1 := by
  decide

private theorem end_right_empty : (rightA endRight).core.path = .bot := by
  decide

private theorem end_moves :
    pathMovedRight (before endRight).1.core (before endRight).2.core
      (moved endRight).1.core (moved endRight).2.core = true := by
  decide

set_option maxRecDepth 32768 in
private theorem end_out_empty :
    (outR endRight).core.erase.core.path = .bot := by
  decide

/-- Nonvacuity of the live side of the actual full-row classification.
The initial right timer is not fresh; freshness is obtained from the public
handoff theorem after the concrete nonempty discriminator removes the end case. -/
theorem live_full_row_handoff_fresh :
    liveRight.stall ≠ freshStall 1 ∧
      deletionActive leftA = false ∧
      (rightA liveRight).core.path = .bot ∧
      pathMovedRight (before liveRight).1.core (before liveRight).2.core
        (moved liveRight).1.core (moved liveRight).2.core = true ∧
      (moved liveRight).2.core.path ≠ .bot ∧
      (outR liveRight).core.erase.core.path ≠ .bot ∧
      (outR liveRight).core.erase.core.path = (moved liveRight).2.core.path ∧
      (outR liveRight).stall = freshStall 1 := by
  have hc := row_right_handoff_or_end
    (κ := 0) (τ := 1) psi_pos width_pos width_le mover liveRight
  change deletionActive leftA = false →
    (rightA liveRight).core.path = .bot →
    pathMovedRight (before liveRight).1.core (before liveRight).2.core
      (moved liveRight).1.core (moved liveRight).2.core = true →
    (moved liveRight).2.core.path ≠ .bot ∧
      RightHandoffOutcome (moved liveRight).2.core.path (outR liveRight) at hc
  obtain ⟨hmne, ho⟩ := hc left_inactive live_right_empty live_moves
  have hkeep :
      (outR liveRight).core.erase.core.path = (moved liveRight).2.core.path ∧
        (outR liveRight).stall = freshStall 1 := by
    unfold RightHandoffOutcome at ho
    rcases ho with hend | hactive | hinactive
    · exact False.elim (live_out_present hend)
    · exact ⟨hactive.1, hactive.2.2⟩
    · exact ⟨hinactive.1, hinactive.2.2⟩
  exact ⟨live_old_stall_not_fresh, left_inactive, live_right_empty,
    live_moves, hmne, live_out_present, hkeep.1, hkeep.2⟩

/-- The end branch is also physically inhabited.  The same carrier first
moves right; changing only the receiver's existing `reset_cmd` makes the full
row finish pathless.  No deletion/disposal postcondition is asserted. -/
theorem reset_full_row_handoff_ends :
    deletionActive leftA = false ∧
      (rightA endRight).core.path = .bot ∧
      pathMovedRight (before endRight).1.core (before endRight).2.core
        (moved endRight).1.core (moved endRight).2.core = true ∧
      (moved endRight).2.core.path ≠ .bot ∧
      (outR endRight).core.erase.core.path = .bot ∧
      RightHandoffOutcome (moved endRight).2.core.path (outR endRight) := by
  have hc := row_right_handoff_or_end
    (κ := 0) (τ := 1) psi_pos width_pos width_le mover endRight
  change deletionActive leftA = false →
    (rightA endRight).core.path = .bot →
    pathMovedRight (before endRight).1.core (before endRight).2.core
      (moved endRight).1.core (moved endRight).2.core = true →
    (moved endRight).2.core.path ≠ .bot ∧
      RightHandoffOutcome (moved endRight).2.core.path (outR endRight) at hc
  obtain ⟨hmne, ho⟩ := hc left_inactive end_right_empty end_moves
  exact ⟨left_inactive, end_right_empty, end_moves, hmne, end_out_empty, ho⟩

#print axioms BirthShortDoneTerminalHandoffExpiryNonvacuity.live_full_row_handoff_fresh
#print axioms BirthShortDoneTerminalHandoffExpiryNonvacuity.reset_full_row_handoff_ends

end BirthShortDoneTerminalHandoffExpiryNonvacuity
