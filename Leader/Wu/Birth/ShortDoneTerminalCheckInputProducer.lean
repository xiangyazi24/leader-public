import Leader.Wu.Birth.ShortDoneTerminalCheckInputSufficiency
import Leader.Wu.Birth.ShortDoneTerminalHandoffExpiry

namespace BirthShortDoneTerminalCheckInputProducer

open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
  BirthSigMoveDisposalRepair

open BirthArrivalCaptureRepair BirthGenerationDone
  BirthSingleUseReleaseRepair BirthShortDoneTerminalEntryCut
  BirthShortDoneTerminalCheckInputSources
  BirthShortDoneTerminalCheckInputSufficiency

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ width κ τ : Nat}

/-- Raw main states for which the current CHECK wrapper is not suppressed and
    SetReady is allowed to arm an aligned resident carrier. -/
def CheckOpenState (s : MainState) : Prop :=
  s ≠ .done ∧ s ≠ .toss ∧ s ≠ .congest ∧
  s ≠ .depart ∧ s ≠ .equal ∧ s ≠ .larger ∧ s ≠ .less

/-- A follower carrier already resident at its matching physical label, with
    no state-changing comparison control and a bit equal to its payload bit. -/
def MatchedOpenAt (u : AgentState ψ) (j : Fin ψ) : Prop :=
  u.leader = false ∧
  u.label = j ∧
  u.path2 = none ∧
  CheckOpenState u.state ∧
  ∃ bit : Nat,
    u.path = .some j.val bit ∧
    checkBit u.bit bit = .equal

/-- Source-side birth-row condition.  `b` is the actual current source prefix
    through P-prime / shortened WAIT+GEN / CLEAN / ELIMINATE, before DONE
    movement, reset sanitation or CHECK.  No CHECK-stage field is mentioned. -/
def CapturedMatchBirthRowSource
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ) : Prop :=
  let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
  b.1.core.reset_cmd = false ∧
  b.2.core.reset_cmd = false ∧
  MatchedOpenAt b.1.core ⟨0, hψ⟩ ∧
  MatchedOpenAt b.2.core ⟨ψ - 1, by omega⟩

/-- Literal expiring/prepared wrapper for the host branch. -/
def PreparedCapturedMatchBirthSource
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) : Prop :=
  let lA := normalizeDeletion (prepareExpiringDisposal hψ l).core.erase
  let rA := normalizeDeletion (prepareExpiringDisposal hψ r).core.erase
  deletionActive rA = false ∧
  deletionActive lA = false ∧
  rA.core.leader = false ∧
  CapturedMatchBirthRowSource hψ hwidth hle κ lA rA

private theorem doneCaptureSigMove_eq_of_matched_open
    (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : MatchedOpenAt l ⟨0, hψ⟩)
    (hr : MatchedOpenAt r ⟨ψ - 1, by omega⟩) :
    doneCaptureSigMove hψ l r = (l, r) := by
  rcases hl with
    ⟨hlLeader, hlLabel, hlP2, hlOpen, lbit, hlPath, hlBit⟩
  rcases hr with
    ⟨hrLeader, hrLabel, hrP2, hrOpen, rbit, hrPath, hrBit⟩
  rcases hlOpen with
    ⟨hlDone, hlToss, hlCongest, hlDepart, hlEqual, hlLarger, hlLess⟩
  rcases hrOpen with
    ⟨hrDone, hrToss, hrCongest, hrDepart, hrEqual, hrLarger, hrLess⟩

  have hp : sigMoveLeaderPreclear hψ l r = (l, r) := by
    simp [sigMoveLeaderPreclear, incompleteLeftLeaderBoundary,
      clearIfLeader, hlLeader, hrLeader]

  have hm : doneTransfers l r = (l, r) := by
    simp [doneTransfers, holdDoneStep1, hlDone,
      captureStep1, hlPath, hrPath,
      controlTransfers, sigMoveStep2, sigMoveStep3, sigMoveStep4,
      sigMoveStep5, hlP2, hrP2]

  have hw : comparisonLeaderWall l r = (l, r) := by
    simp [comparisonLeaderWall, hlLeader, hrLeader]

  have hc : singleUseControlTail hψ l r = (l, r) := by
    simp [singleUseControlTail, singleUseApplyControl,
      hlP2, hrP2, hrDepart]

  unfold doneCaptureSigMove
  rw [hp]
  dsimp only
  rw [hm]
  dsimp only
  rw [hw]
  exact hc

private theorem authorizedDoneMove_cores_of_matched_open
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hl : MatchedOpenAt l.core ⟨0, hψ⟩)
    (hr : MatchedOpenAt r.core ⟨ψ - 1, by omega⟩) :
    let q := authorizedDoneMove hψ l r
    q.1.core = l.core ∧ q.2.core = r.core := by
  have hc := authorizedDoneMove_core hψ l r
  change
    ((authorizedDoneMove hψ l r).1.core,
      (authorizedDoneMove hψ l r).2.core) =
      doneCaptureSigMove hψ l.core r.core at hc
  rw [doneCaptureSigMove_eq_of_matched_open hψ l.core r.core hl hr] at hc
  exact ⟨congrArg Prod.fst hc, congrArg Prod.snd hc⟩

/-- The current DONE move, reset wall and terminal sanitizer leave the two raw
    birth carriers intact at core level. -/
private theorem doneBeforeCheck_cores_of_source
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hsrc : CapturedMatchBirthRowSource hψ hwidth hle κ l r) :
    let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
    let d := doneBeforeCheckEntryWidth hψ hwidth hle κ l r
    d.1.core = b.1.core ∧ d.2.core = b.2.core := by
  let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
  let m := authorizedDoneMove hψ b.1 b.2
  let d := doneBeforeCheckEntryWidth hψ hwidth hle κ l r

  change
    b.1.core.reset_cmd = false ∧ b.2.core.reset_cmd = false ∧
      MatchedOpenAt b.1.core ⟨0, hψ⟩ ∧
      MatchedOpenAt b.2.core ⟨ψ - 1, by omega⟩ at hsrc
  rcases hsrc with ⟨hlReset, hrReset, hl, hr⟩

  have hm := authorizedDoneMove_cores_of_matched_open hψ b.1 b.2 hl hr
  change m.1.core = b.1.core ∧ m.2.core = b.2.core at hm

  rcases hl with
    ⟨hlLeader, hlLabel, hlP2, hlOpen, lbit, hlPath, hlBit⟩
  rcases hr with
    ⟨hrLeader, hrLabel, hrP2, hrOpen, rbit, hrPath, hrBit⟩
  rcases hlOpen with
    ⟨hlDone, hlToss, hlCongest, hlDepart, hlEqual, hlLarger, hlLess⟩
  rcases hrOpen with
    ⟨hrDone, hrToss, hrCongest, hrDepart, hrEqual, hrLarger, hrLess⟩

  have hmLLeader : m.1.core.leader = false :=
    (congrArg AgentState.leader hm.1).trans hlLeader
  have hmLReset : m.1.core.reset_cmd = false :=
    (congrArg AgentState.reset_cmd hm.1).trans hlReset
  have hmRReset : m.2.core.reset_cmd = false :=
    (congrArg AgentState.reset_cmd hm.2).trans hrReset
  have hmLEqual : m.1.core.state ≠ .equal := by
    intro h
    exact hlEqual ((congrArg AgentState.state hm.1).symm.trans h)
  have hmREqual : m.2.core.state ≠ .equal := by
    intro h
    exact hrEqual ((congrArg AgentState.state hm.2).symm.trans h)

  have hw : preCheckResetWall m.1 m.2 = (m.1, m.2) :=
    preCheckResetWall_eq_of_inactive
      m.1 m.2 hmLLeader hmLReset hmRReset

  have hsL : sanitizeAuthorizedTerminalEqual hψ m.1 = m.1 := by
    simp [sanitizeAuthorizedTerminalEqual, unsupportedTerminalEqual, hmLEqual]
  have hsR : sanitizeAuthorizedTerminalEqual hψ m.2 = m.2 := by
    simp [sanitizeAuthorizedTerminalEqual, unsupportedTerminalEqual, hmREqual]

  have hstage :
      d = sanitizeAuthorizedPair hψ (preCheckResetWall m.1 m.2) := by
    rfl
  change d.1.core = b.1.core ∧ d.2.core = b.2.core
  rw [hstage, hw]
  simp only [sanitizeAuthorizedPair, hsL, hsR]
  exact hm

private theorem zero_check_prefix_of_matched_open
    (hψ : 0 < ψ) (u : AgentState ψ)
    (h : MatchedOpenAt u ⟨0, hψ⟩) :
    (checkSigCheckL hψ (checkSigSetReady u)).label.val = 0 ∧
      (checkSigCheckL hψ (checkSigSetReady u)).state = .equal := by
  rcases h with
    ⟨huLeader, huLabel, huP2, huOpen, bit, huPath, huBit⟩
  rcases huOpen with
    ⟨huDone, huToss, huCongest, huDepart, huEqual, huLarger, huLess⟩
  simp [checkSigSetReady, checkSigCheckL,
    huPath, huLabel, huDepart, huEqual, huLarger, huLess, huBit]

/-- Main source producer.  This derives every DONE/TOSS/CONGEST guard, the
    live responder source, the left equal prefix and sanitation behavior from
    raw source fields before movement. -/
theorem actualCheckBirthInput_of_captured_match_source
    (hψ : 0 < ψ) (hψ2 : 1 < ψ)
    (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hsrc : CapturedMatchBirthRowSource hψ hwidth hle κ l r) :
    ActualCheckBirthInput hψ
      (doneBeforeCheckEntryWidth hψ hwidth hle κ l r) := by
  let b := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
  let d := doneBeforeCheckEntryWidth hψ hwidth hle κ l r

  have hc := doneBeforeCheck_cores_of_source
    hψ hwidth hle κ l r hsrc
  change d.1.core = b.1.core ∧ d.2.core = b.2.core at hc

  change
    b.1.core.reset_cmd = false ∧ b.2.core.reset_cmd = false ∧
      MatchedOpenAt b.1.core ⟨0, hψ⟩ ∧
      MatchedOpenAt b.2.core ⟨ψ - 1, by omega⟩ at hsrc
  rcases hsrc with ⟨hlReset, hrReset, hl, hr⟩

  rcases hl with
    ⟨hlLeader, hlLabel, hlP2, hlOpen, lbit, hlPath, hlBit⟩
  rcases hr with
    ⟨hrLeader, hrLabel, hrP2, hrOpen, rbit, hrPath, hrBit⟩
  rcases hlOpen with
    ⟨hlDone, hlToss, hlCongest, hlDepart, hlEqual, hlLarger, hlLess⟩
  rcases hrOpen with
    ⟨hrDone, hrToss, hrCongest, hrDepart, hrEqual, hrLarger, hrLess⟩

  change ActualCheckBirthInput hψ d
  unfold ActualCheckBirthInput
  rw [hc.1, hc.2]
  refine ⟨hlDone, hrDone, hlToss, hrToss, hlCongest, hrCongest, ?_⟩

  unfold CheckFollowerBirthInput
  refine ⟨hrLeader, hrLabel, Or.inr ?_⟩
  refine ⟨ψ - 1, rbit, hrPath, ?_, ?_, ?_, hrBit⟩
  · unfold ReadyInputAt
    right
    refine ⟨?_, hrDepart, hrEqual, hrLarger, hrLess⟩
    simpa [hrLabel]
  · have hz : (0 : Nat) < ψ - 1 := by omega
    have hp := zero_check_prefix_of_matched_open hψ b.1.core
      ⟨hlLeader, hlLabel, hlP2,
        ⟨hlDone, hlToss, hlCongest, hlDepart,
          hlEqual, hlLarger, hlLess⟩,
        lbit, hlPath, hlBit⟩
    simpa [hp.1] using hz
  · exact (zero_check_prefix_of_matched_open hψ b.1.core
      ⟨hlLeader, hlLabel, hlP2,
        ⟨hlDone, hlToss, hlCongest, hlDepart,
          hlEqual, hlLarger, hlLess⟩,
        lbit, hlPath, hlBit⟩).2

/-- Direct current-host birth event from the original expiring row input. -/
theorem birthEvent_true_of_prepared_captured_match_source
    (hψ : 0 < ψ) (hψ2 : 1 < ψ)
    (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hsrc : PreparedCapturedMatchBirthSource hψ hwidth hle l r) :
    BirthShortDoneTerminalObserver.birthEvent hψ hwidth hle l r = true := by
  let lA := normalizeDeletion (prepareExpiringDisposal hψ l).core.erase
  let rA := normalizeDeletion (prepareExpiringDisposal hψ r).core.erase
  change
    deletionActive rA = false ∧ deletionActive lA = false ∧
      rA.core.leader = false ∧
      CapturedMatchBirthRowSource hψ hwidth hle κ lA rA at hsrc
  rcases hsrc with ⟨hrDeletion, hlDeletion, hrFollower, hpair⟩

  have hcheck := actualCheckBirthInput_of_captured_match_source
    hψ hψ2 hwidth hle κ lA rA hpair

  exact birthEvent_true_of_prepared_ordinary_check_input
    hψ hwidth hle l r
    (by simpa [rA] using hrDeletion)
    (by simpa [lA] using hlDeletion)
    (by simpa [rA] using hrFollower)
    (by simpa [lA, rA] using hcheck)

#print axioms BirthShortDoneTerminalCheckInputProducer.actualCheckBirthInput_of_captured_match_source
#print axioms BirthShortDoneTerminalCheckInputProducer.birthEvent_true_of_prepared_captured_match_source

end BirthShortDoneTerminalCheckInputProducer
