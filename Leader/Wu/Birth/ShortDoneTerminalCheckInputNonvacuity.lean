import Leader.Wu.Birth.ShortDoneTerminalCheckInputSufficiency
import Leader.Wu.Elimination.BirthDispatcherWriterInputObstruction
import Leader.Wu.Birth.GenerationDoneHost


namespace BirthShortDoneTerminalCheckInputNonvacuity


open PPLL PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  BirthSigMoveDisposalRepair BirthShortDoneTerminalEntryCut
open BirthShortDoneTerminalCheckInputSources
  BirthShortDoneTerminalCheckInputSufficiency
open PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
open BirthGenerationDone BirthSingleUseReleaseRepair


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


private theorem h2 : 0 < 2 := by decide


/-- Actual cached configuration at the input immediately before the accepted
    positive birth edge.  `C12_eq_source` below ties it to the public
    `positiveRun 12` execution from the clean family. -/
def actualL : ExpiringAgentState 2 2 16 :=
  K2BirthLeaderNormalizeWriterAudit.C12 2


def actualR : ExpiringAgentState 2 2 16 :=
  K2BirthLeaderNormalizeWriterAudit.C12 3


/-- Literal prepared/normalized TerminalHost inputs. -/
def l0 : AuthorizedAgentState 2 :=
  normalizeDeletion (prepareExpiringDisposal h2 actualL).core.erase


def r0 : AuthorizedAgentState 2 :=
  normalizeDeletion (prepareExpiringDisposal h2 actualR).core.erase


/-- Accepted old full-width sanitized cut, used only as a computation target
    after proving the current DONE/full-width bridge. -/
def singleCut : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  singleUseBeforeCheck h2 2 l0 r0


/-- The exact current TerminalHost pre-CHECK cut occurring in the physical
    theorem premise. -/
def terminalCut : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  doneBeforeCheckEntryWidth h2 h2 (Nat.le_refl 2) 2 l0 r0


/-- These are literally sites 2 and 3 of the accepted physical execution. -/
theorem source_pair :
    actualL = K2BirthDispatcher.Witnesses.positiveRun 12 2 ∧
      actualR = K2BirthDispatcher.Witnesses.positiveRun 12 3 := by
  have hs := K2BirthLeaderNormalizeWriterAudit.C12_eq_source
  constructor
  · simpa [actualL] using congrFun hs (2 : Fin 8)
  · simpa [actualR] using congrFun hs (3 : Fin 8)


set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
/-- Both original endpoints are followers.  The two literal prepared,
    normalized deletion-priority guards are false, and the normalized old
    responder is still a follower. -/
theorem actual_pair_and_prepared_premises :
    actualL.core.core.leader = false ∧
      actualR.core.core.leader = false ∧
      deletionActive r0 = false ∧
      deletionActive l0 = false ∧
      r0.core.leader = false := by
  decide


set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
/-- On this concrete row, the DONE-aware movement replacement takes its
    ordinary no-current-DONE Step1 branch.  This is the exact premise needed
    to compare the current DONE pre-CHECK computation with the accepted
    single-use pre-CHECK computation. -/
private theorem done_step1_clear :
    let g := BirthGenerationControlRepair.generationBeforeMove h2 2 l0 r0
    (sigMoveLeaderPreclear h2 g.1.core g.2.core).1.state ≠ .done := by
  decide


/-- Full width makes the terminal-entry WAIT cut identical to the accepted
    full DONE cut; the concrete no-DONE fact then reaches exactly the old
    sanitized `singleUseBeforeCheck`.  In particular sanitation is not
    bypassed by this witness. -/
theorem current_cut_eq_single : terminalCut = singleCut := by
  unfold terminalCut singleCut
  calc
    doneBeforeCheckEntryWidth h2 h2 (Nat.le_refl 2) 2 l0 r0 =
        BirthGenerationDone.doneBeforeCheck h2 2 l0 r0 :=
      doneBeforeCheckEntryWidth_full h2 2 l0 r0
    _ = singleUseBeforeCheck h2 2 l0 r0 :=
      BirthGenerationDone.doneBeforeCheck_eq_singleUse
        h2 2 l0 r0 done_step1_clear


set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
/-- Exact finite facts at the CURRENT sanitized pre-CHECK cut.  The explicit
    `state ≠ equal` clause proves that this example uses the live-path
    disjunct of `CheckFollowerBirthInput`, not the stale-equal escape hatch. -/
theorem sanitized_cut_snapshot :
    terminalCut.1.core.state ≠ .done ∧
      terminalCut.2.core.state ≠ .done ∧
      terminalCut.1.core.state ≠ .toss ∧
      terminalCut.2.core.state ≠ .toss ∧
      terminalCut.1.core.state ≠ .congest ∧
      terminalCut.2.core.state ≠ .congest ∧
      terminalCut.2.core.state ≠ .equal ∧
      terminalCut.2.core.leader = false ∧
      terminalCut.2.core.label = (1 : Fin 2) ∧
      terminalCut.2.core.path = .some 1 0 ∧
      ReadyInputAt terminalCut.2.core 1 ∧
      (checkSigCheckL h2
        (checkSigSetReady terminalCut.1.core)).label.val < 2 - 1 ∧
      (checkSigCheckL h2
        (checkSigSetReady terminalCut.1.core)).state = .equal ∧
      checkBit terminalCut.2.core.bit 0 = .equal := by
  rw [current_cut_eq_single]
  unfold ReadyInputAt
  decide


/-- Construct the exact input predicate from the real current cut;
    no CHECK output field occurs among the hypotheses. -/
theorem actual_check_input : ActualCheckBirthInput h2 terminalCut := by
  rcases sanitized_cut_snapshot with
    ⟨hdl, hdr, htl, htr, hcl, hcr, _hne,
      hfollower, hlabel, hpath, hready, hleftLabel, hleftEqual, hbit⟩
  refine ⟨hdl, hdr, htl, htr, hcl, hcr, ?_⟩
  refine ⟨hfollower, ?_, Or.inr ?_⟩
  · simpa using hlabel
  · exact ⟨1, 0, hpath, hready, hleftLabel, hleftEqual, hbit⟩


/-- The live CHECK source itself is visibly inhabited at the actual sanitized
    TerminalHost cut. -/
theorem live_path_branch_nonvacuous :
    terminalCut.2.core.state ≠ .equal ∧
      ∃ pathLabel pathBit : Nat,
        terminalCut.2.core.path = .some pathLabel pathBit ∧
        ReadyInputAt terminalCut.2.core pathLabel ∧
        (checkSigCheckL h2
          (checkSigSetReady terminalCut.1.core)).label.val < 2 - 1 ∧
        (checkSigCheckL h2
          (checkSigSetReady terminalCut.1.core)).state = .equal ∧
        checkBit terminalCut.2.core.bit pathBit = .equal := by
  rcases sanitized_cut_snapshot with
    ⟨_, _, _, _, _, _, hne, _, _, hpath, hready,
      hleftLabel, hleftEqual, hbit⟩
  exact ⟨hne,
    ⟨1, 0, hpath, hready, hleftLabel, hleftEqual, hbit⟩⟩


/-- All premises of the public physical theorem are now discharged
    from the actual expiring inputs, so the real TerminalHost physical row
    has a surviving leader. -/
theorem actual_full_terminal_physical_birth :
    (BirthShortDoneTerminalHost.row
      h2 h2 (Nat.le_refl 2) actualL actualR).1.core.core.leader = true ∨
      (BirthShortDoneTerminalHost.row
        h2 h2 (Nat.le_refl 2) actualL actualR).2.core.core.leader = true := by
  rcases actual_pair_and_prepared_premises with
    ⟨_hlOld, _hrOld, hrDeletion, hlDeletion, hrFollower⟩
  apply
    BirthShortDoneTerminalCheckInputSufficiency.physical_leader_of_prepared_ordinary_check_input
        h2 h2 (Nat.le_refl 2) actualL actualR
  · simpa [r0] using hrDeletion
  · simpa [l0] using hlDeletion
  · simpa [r0] using hrFollower
  · simpa [terminalCut, l0, r0] using actual_check_input


#print axioms BirthShortDoneTerminalCheckInputNonvacuity.source_pair
#print axioms BirthShortDoneTerminalCheckInputNonvacuity.actual_pair_and_prepared_premises
#print axioms BirthShortDoneTerminalCheckInputNonvacuity.current_cut_eq_single
#print axioms BirthShortDoneTerminalCheckInputNonvacuity.sanitized_cut_snapshot
#print axioms BirthShortDoneTerminalCheckInputNonvacuity.actual_check_input
#print axioms BirthShortDoneTerminalCheckInputNonvacuity.live_path_branch_nonvacuous
#print axioms BirthShortDoneTerminalCheckInputNonvacuity.actual_full_terminal_physical_birth


end BirthShortDoneTerminalCheckInputNonvacuity
