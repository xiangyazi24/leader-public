import Leader.Wu.Elimination.ControllerCompatibility
import Leader.Wu.Birth.ShortDoneTerminalConsumer
import Leader.Wu.Birth.ShortDoneTerminalCheckInputNonvacuity
import Leader.Wu.Elimination.BirthDispatcherWitnesses
import Leader.Wu.Elimination.BirthDispatcherWriterInputObstruction

namespace K2ControllerCompatibilityTerminalCensusR1

open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepFiniteCleanup PPLLWallSweepShieldCircuit
  BirthSigMoveDisposalRepair K2OutputSafety

open BirthGenerationDone
  BirthShortDoneTerminalEntryCut
  BirthShortDoneTerminalCheckInputSources
  BirthShortDoneTerminalCheckInputSufficiency

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ width κ τ : Nat}

/-! ## Width-aware current-host priority census -/

theorem doneMetadataAuthorizedEntryWidth_right_priority
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hr : deletionActive (normalizeDeletion r) = true) :
    BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
        hψ hwidth hle κ l r =
      authorizedEliminateSig hψ (normalizeDeletion l) (normalizeDeletion r) := by
  unfold BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
  simp only [hr, if_true]

theorem doneMetadataAuthorizedEntryWidth_left_priority
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hr : deletionActive (normalizeDeletion r) = false)
    (hl : deletionActive (normalizeDeletion l) = true) :
    BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
        hψ hwidth hle κ l r =
      (normalizeDeletion l, normalizeDeletion r) := by
  unfold BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
  simp only [hr, Bool.false_eq_true, if_false, hl, if_true]

theorem doneMetadataAuthorizedEntryWidth_ordinary
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hr : deletionActive (normalizeDeletion r) = false)
    (hl : deletionActive (normalizeDeletion l) = false) :
    BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
        hψ hwidth hle κ l r =
      BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
        hψ hwidth hle κ (normalizeDeletion l) (normalizeDeletion r) := by
  unfold BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
  simp only [hr, Bool.false_eq_true, if_false, hl]

theorem doneMetadataAuthorizedEntryWidth_branch_coverage
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ) :
    (deletionActive (normalizeDeletion r) = true ∧
      BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
          hψ hwidth hle κ l r =
        authorizedEliminateSig hψ
          (normalizeDeletion l) (normalizeDeletion r)) ∨
    (deletionActive (normalizeDeletion r) = false ∧
      deletionActive (normalizeDeletion l) = true ∧
      BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
          hψ hwidth hle κ l r =
        (normalizeDeletion l, normalizeDeletion r)) ∨
    (deletionActive (normalizeDeletion r) = false ∧
      deletionActive (normalizeDeletion l) = false ∧
      BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
          hψ hwidth hle κ l r =
        BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
          hψ hwidth hle κ
          (normalizeDeletion l) (normalizeDeletion r)) := by
  cases hr : deletionActive (normalizeDeletion r) with
  | true =>
      exact Or.inl ⟨rfl,
        doneMetadataAuthorizedEntryWidth_right_priority
          hψ hwidth hle κ l r hr⟩
  | false =>
      cases hl : deletionActive (normalizeDeletion l) with
      | true =>
          exact Or.inr (Or.inl ⟨rfl, rfl,
            doneMetadataAuthorizedEntryWidth_left_priority
              hψ hwidth hle κ l r hr hl⟩)
      | false =>
          exact Or.inr (Or.inr ⟨rfl, rfl,
            doneMetadataAuthorizedEntryWidth_ordinary
              hψ hwidth hle κ l r hr hl⟩)

theorem doneMetadataAuthorizedEntryWidth_ordinary_priority_open
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hr : deletionActive (normalizeDeletion r) = false)
    (hl : deletionActive (normalizeDeletion l) = false) :
    AuthorizedPriorityOpen l r := by
  unfold AuthorizedPriorityOpen
  exact ⟨hl, hr⟩

/-! ## Full-width output fact: normalization is later, not a writer premise -/

theorem terminalHost_full_row_leader_labels_zero
    (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    ((BirthShortDoneTerminalHost.row
        hψ hψ (Nat.le_refl ψ) l r).1.core.core.leader = true →
      (BirthShortDoneTerminalHost.row
        hψ hψ (Nat.le_refl ψ) l r).1.core.core.label = ⟨0, hψ⟩) ∧
    ((BirthShortDoneTerminalHost.row
        hψ hψ (Nat.le_refl ψ) l r).2.core.core.leader = true →
      (BirthShortDoneTerminalHost.row
        hψ hψ (Nat.le_refl ψ) l r).2.core.core.label = ⟨0, hψ⟩) := by
  rw [BirthShortDoneTerminalHost.row_full hψ l r]
  exact K2BirthDoneNormalize.row_leader_labels_zero hψ l r

/-! ## Smallest non-aliasing ring used to package local pair witnesses -/

private theorem h2 : 0 < 2 := by decide

def ring2 : DirectedRing 2 := ⟨by decide⟩

/-! ## Actual positive CHECK: safety and leader-frame are false -/

/-- These are complete finite physical states: the public constants are the
sites 2 and 3 of the tracked `positiveRun 12` execution, with ψ=2, κ=2,
τ=16.  The two-site function is only the smallest non-aliasing embedding of
that already certified local pair. -/
def actualBirthConfig2 (i : Fin 2) : ExpiringAgentState 2 2 16 :=
  if i = 0 then
    BirthShortDoneTerminalCheckInputNonvacuity.actualL
  else
    BirthShortDoneTerminalCheckInputNonvacuity.actualR

theorem actual_terminal_cut_not_check_safe :
    ¬ CheckResponderSafe h2
      BirthShortDoneTerminalCheckInputNonvacuity.terminalCut.2.core := by
  rcases
      BirthShortDoneTerminalCheckInputNonvacuity.sanitized_cut_snapshot with
    ⟨_hdl, _hdr, _htl, _htr, _hcl, _hcr, _hne,
      hfollower, hlabel, hpath, hready,
      _hleftLabel, _hleftEqual, _hbit⟩
  have hdepart :
      BirthShortDoneTerminalCheckInputNonvacuity.terminalCut.2.core.state ≠
        .depart := by
    rcases hready with hready | hguard
    · intro hd
      rw [hd] at hready
      cases hready
    · exact hguard.2.1
  intro hsafe
  rcases hsafe with hleader | hnotTerminal | hpathSafe | hdepartEq
  · rw [hfollower] at hleader
    cases hleader
  · apply hnotTerminal
    simpa using hlabel
  · have hbot := hpathSafe.1
    rw [hpath] at hbot
    cases hbot
  · exact hdepart hdepartEq

theorem actual_terminal_cut_checked_responder_not_frame :
    (authorizedCheckSig h2
      BirthShortDoneTerminalCheckInputNonvacuity.terminalCut.1
      BirthShortDoneTerminalCheckInputNonvacuity.terminalCut.2).2.core.leader ≠
    BirthShortDoneTerminalCheckInputNonvacuity.terminalCut.2.core.leader := by
  have hb := actualCheckBirth_of_input h2
    BirthShortDoneTerminalCheckInputNonvacuity.terminalCut
    BirthShortDoneTerminalCheckInputNonvacuity.actual_check_input
  rcases hb with
    ⟨_hdl, _hdr, _htl, _htr, _hcl, _hcr, hbefore, hafter⟩
  intro hframe
  rw [hafter, hbefore] at hframe
  cases hframe

theorem actual_terminal_cut_right_not_neutral :
    ¬ ComparisonNeutral
      BirthShortDoneTerminalCheckInputNonvacuity.terminalCut.2.core := by
  rcases
      BirthShortDoneTerminalCheckInputNonvacuity.sanitized_cut_snapshot with
    ⟨_, _, _, _, _, _, _, _, _, hpath, _, _, _, _⟩
  intro hneutral
  have hbot := hneutral.2.1
  rw [hpath] at hbot
  cases hbot

/-! ## Actual writer input: RowSafe is false before later normalization -/

def actualWriterConfig2 (i : Fin 2) : AgentState 2 :=
  if i = 0 then K2BirthLeaderNormalizeWriterAudit.w12.1.core
  else K2BirthLeaderNormalizeWriterAudit.w12.2.core

theorem actual_writer_config2_not_rowSafe :
    ¬ RowSafe h2 ring2 actualWriterConfig2 := by
  rcases K2BirthLeaderNormalizeWriterAudit.actual_writer_input_obstruction with
    ⟨_hsourceZero, _hdl, _hdr, _hcLeader, _hcLabel,
      hwLeader, _hwLabel, hwNonzero⟩
  intro hsafe
  have hleader : (actualWriterConfig2 (1 : Fin 2)).isLeader := by
    change (actualWriterConfig2 (1 : Fin 2)).leader = true
    simpa [actualWriterConfig2] using hwLeader
  have hzero := hsafe.2.1 (1 : Fin 2) hleader
  have hzero' :
      K2BirthLeaderNormalizeWriterAudit.w12.2.core.label = (0 : Fin 2) := by
    simpa [actualWriterConfig2] using hzero
  exact hwNonzero hzero'

/-! ## Concrete deletion-priority row: global priority openness is false -/

def disposalAuthL : AuthorizedAgentState 2 :=
  (prepareExpiringDisposal h2
    K2BirthDispatcher.Witnesses.disposalLeft).core.erase

def disposalAuthR : AuthorizedAgentState 2 :=
  (prepareExpiringDisposal h2
    K2BirthDispatcher.Witnesses.disposalRight).core.erase

theorem actual_disposal_pair_not_priority_open :
    ¬ AuthorizedPriorityOpen disposalAuthL disposalAuthR := by
  have h := K2BirthDispatcher.Witnesses.disposal_left_priority
  have hleft : deletionActive (normalizeDeletion disposalAuthL) = true := by
    simpa [disposalAuthL] using h.2.1
  intro hopen
  change
    deletionActive (normalizeDeletion disposalAuthL) = false ∧
      deletionActive (normalizeDeletion disposalAuthR) = false at hopen
  have hf := hopen.1
  rw [hleft] at hf
  cases hf

theorem actual_disposal_pair_not_aligned :
    (normalizeDeletion disposalAuthR).core.label ≠
      ⟨((normalizeDeletion disposalAuthL).core.label.val + 1) % 2,
        Nat.mod_lt _ h2⟩ := by
  decide

theorem actual_disposal_left_not_neutral :
    ¬ ComparisonNeutral (normalizeDeletion disposalAuthL).core := by
  unfold ComparisonNeutral
  decide

theorem actual_disposal_terminal_host_takes_left_priority :
    BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
        h2 h2 (Nat.le_refl 2) 2 disposalAuthL disposalAuthR =
      (normalizeDeletion disposalAuthL, normalizeDeletion disposalAuthR) := by
  have h := K2BirthDispatcher.Witnesses.disposal_left_priority
  have hl : deletionActive (normalizeDeletion disposalAuthL) = true := by
    simpa [disposalAuthL] using h.2.1
  have hr : deletionActive (normalizeDeletion disposalAuthR) = false := by
    simpa [disposalAuthR] using h.2.2.1
  exact doneMetadataAuthorizedEntryWidth_left_priority
    h2 h2 (Nat.le_refl 2) 2 disposalAuthL disposalAuthR hr hl

#print axioms K2ControllerCompatibilityTerminalCensusR1.doneMetadataAuthorizedEntryWidth_branch_coverage
#print axioms K2ControllerCompatibilityTerminalCensusR1.doneMetadataAuthorizedEntryWidth_ordinary_priority_open
#print axioms K2ControllerCompatibilityTerminalCensusR1.terminalHost_full_row_leader_labels_zero
#print axioms K2ControllerCompatibilityTerminalCensusR1.actual_terminal_cut_not_check_safe
#print axioms K2ControllerCompatibilityTerminalCensusR1.actual_terminal_cut_checked_responder_not_frame
#print axioms K2ControllerCompatibilityTerminalCensusR1.actual_terminal_cut_right_not_neutral
#print axioms K2ControllerCompatibilityTerminalCensusR1.actual_writer_config2_not_rowSafe
#print axioms K2ControllerCompatibilityTerminalCensusR1.actual_disposal_pair_not_priority_open
#print axioms K2ControllerCompatibilityTerminalCensusR1.actual_disposal_pair_not_aligned
#print axioms K2ControllerCompatibilityTerminalCensusR1.actual_disposal_left_not_neutral
#print axioms K2ControllerCompatibilityTerminalCensusR1.actual_disposal_terminal_host_takes_left_priority

end K2ControllerCompatibilityTerminalCensusR1
