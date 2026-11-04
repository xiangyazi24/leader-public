import Leader.Wu.Birth.ShortDoneTerminalOpenMatchedHandoffCounterexample


/-!
# Flag-one overwrite counterexample to the proposed open matched handoff

This leaf attacks the Part-A premise set on the literal current
`BirthShortDoneTerminalHost.row`.

The earlier witness used a flag-zero writer component and exposed the repaired
terminal increment.  The present witness instead uses a flag-one component
whose stored writer bit is below the responder bit.  It therefore satisfies
the proposed `hWriter`, but the current stationary persistent writer selects
`overwrite` and changes the responder bit after the matched terminal capture.

No protocol definition is changed here.
-/

namespace BirthShortDoneTerminalOpenMatchedHandoffFlagOneCounterexample

open PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair BirthGenerationDone
open K2BirthDispatcher K2BirthLeaderNormalize
  BirthArrivalCaptureRepair BirthShortDoneTerminalHost
  BirthShortDoneTerminalEntryCut BirthShortDoneTerminalHandoffExpiry
  BirthShortDoneTerminalOpenMatchedHandoffCounterexample

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ κ τ : Nat}

private theorem onePos : 0 < 1 := by decide
private theorem widthPos : 0 < 1 := by decide
private theorem widthLe : 1 ≤ 1 := by decide

private def peace1 (j : Fin 1) : PeaceView 1 :=
  { leader := false
    label := j
    shield := false
    bullet := 0
    signal_B := 0 }

private def rawBase (j : Fin 1) : AgentState 1 :=
  PeaceView.toState (peace1 j)

/-- The terminal payload to be captured carries bit `1`. -/
private def leftRaw : AgentState 1 :=
  { rawBase (0 : Fin 1) with path := .some 0 1 }

/-- The receiver bit already matches the incoming payload bit `1`, but its
pre-existing writer component stores bit `0` with flag `1`.  This satisfies
the proposed flag-zero-support exclusion. -/
private def rightRaw : AgentState 1 :=
  { rawBase (0 : Fin 1) with
    bit := true
    path3 := some ⟨0, 0, 1⟩ }

private theorem leftRawDomain : leftRaw.inProtocolDomain 0 := by
  simp [leftRaw, rawBase, peace1, PeaceView.toState,
    AgentState.inProtocolDomain]

private theorem rightRawDomain : rightRaw.inProtocolDomain 0 := by
  simp [rightRaw, rawBase, peace1, PeaceView.toState,
    AgentState.inProtocolDomain]

private def leftInput : ExpiringAgentState 1 0 1 :=
  ⟨⟨BoundedAgentState.ofDomain leftRaw leftRawDomain, false⟩,
    freshStall 1⟩

private def rightInput : ExpiringAgentState 1 0 1 :=
  ⟨⟨BoundedAgentState.ofDomain rightRaw rightRawDomain, false⟩,
    freshStall 1⟩

private def leftPrepared : AuthorizedAgentState 1 :=
  (prepareExpiringDisposal onePos leftInput).core.erase

private def rightPrepared : AuthorizedAgentState 1 :=
  (prepareExpiringDisposal onePos rightInput).core.erase

private def leftA : AuthorizedAgentState 1 :=
  normalizeDeletion leftPrepared

private def rightA : AuthorizedAgentState 1 :=
  normalizeDeletion rightPrepared

private def beforeMove : AuthorizedAgentState 1 × AuthorizedAgentState 1 :=
  generationBeforeMoveEntryWidth onePos widthPos widthLe 0 leftA rightA

private def step1Input : AgentState 1 × AgentState 1 :=
  PPLLWallSweepRepair.sigMoveLeaderPreclear
    onePos beforeMove.1.core beforeMove.2.core

private def moved : AuthorizedAgentState 1 × AuthorizedAgentState 1 :=
  authorizedDoneMove onePos beforeMove.1 beforeMove.2

private def outR : ExpiringAgentState 1 0 1 :=
  (BirthShortDoneTerminalHost.row
    onePos widthPos widthLe leftInput rightInput).2

/-- Exactly the Part-A prepared-input clauses: reset silence, path2
silence, the right probe silence, both deletion-open clauses, the weakened
DISAPPEAR blocker, and the proposed flag-zero writer-support exclusion. -/
def CorrectedPartAPreparedHypotheses
    (l r : AuthorizedAgentState ψ) : Prop :=
  l.core.reset_cmd = false ∧
  r.core.reset_cmd = false ∧
  l.core.path2 = none ∧
  r.core.path2 = none ∧
  deletionActive l = false ∧
  deletionActive r = false ∧
  r.core.probe = false ∧
  (l.core.p_carry = false ∨ r.core.p = false) ∧
  ¬ ∃ p3 : Path3Info, r.core.path3 = some p3 ∧ p3.flag = 0

/-- The concrete flag-one receiver satisfies every requested prepared-input
hypothesis, including `hDisappear` and `hWriter`. -/
theorem requested_prepared_hypotheses :
    CorrectedPartAPreparedHypotheses leftPrepared rightPrepared := by
  have hfinite :
      leftPrepared.core.reset_cmd = false ∧
      rightPrepared.core.reset_cmd = false ∧
      leftPrepared.core.path2 = none ∧
      rightPrepared.core.path2 = none ∧
      deletionActive leftPrepared = false ∧
      deletionActive rightPrepared = false ∧
      rightPrepared.core.probe = false ∧
      (leftPrepared.core.p_carry = false ∨
        rightPrepared.core.p = false) ∧
      rightPrepared.core.path3 =
        some (⟨0, 0, 1⟩ : Path3Info) := by
    decide
  rcases hfinite with
    ⟨hlReset, hrReset, hlP2, hrP2, hlDel, hrDel, hrProbe,
      hDisappear, hpath3⟩
  unfold CorrectedPartAPreparedHypotheses
  refine ⟨hlReset, hrReset, hlP2, hrP2, hlDel, hrDel, hrProbe,
    hDisappear, ?_⟩
  rintro ⟨p3, hp, hflag⟩
  rw [hpath3] at hp
  have hp3 : (⟨0, 0, 1⟩ : Path3Info) = p3 := Option.some.inj hp
  subst p3
  simp at hflag

/-- Literal terminal matched-capture source facts at the actual Step1
input.  This is stated directly because `TerminalMatchedCaptureSource` is not
an importable declaration on main. -/
private theorem matchedSource :
    step1Input.1.leader = false ∧
    step1Input.2.leader = false ∧
    step1Input.1.state ≠ .done ∧
    step1Input.1.state ≠ .lock ∧
    step1Input.1.state ≠ .compare1 ∧
    step1Input.1.state ≠ .CHECK_ready ∧
    step1Input.1.path = .some 0 1 ∧
    step1Input.1.path2 = none ∧
    step1Input.2.path = .bot ∧
    step1Input.2.state ≠ .produce ∧
    step1Input.2.label = (0 : Fin 1) ∧
    checkBit step1Input.2.bit 1 = .equal := by
  decide

/-- The actual first capture substep is a matched terminal capture of bit `1`. -/
theorem actual_matched_capture_flag_one :
    let q := captureStep1 step1Input.1 step1Input.2
    q.2.path = .some 0 1 ∧
      q.2.state = .CHECK_ready ∧
      q.2.path2 = none := by
  rcases matchedSource with
    ⟨_, _, _, hlock, hcompare1, hready, hlpath, _, hrpath,
      hrproduce, hrlabel, _⟩
  have halign : step1Input.2.label.val = 0 := by
    simpa using congrArg Fin.val hrlabel
  have h := captureStep1_matched
    step1Input.1 step1Input.2 0 1
    hlpath hrpath
    ⟨hlock, hcompare1, hready⟩
    (Or.inl hrproduce) halign
  dsimp only at h ⊢
  exact ⟨h.2.1.trans hlpath, h.2.2.1, h.2.2.2.1⟩

private theorem actualMove :
    pathMovedRight
        beforeMove.1.core beforeMove.2.core
        moved.1.core moved.2.core = true ∧
      moved.2.core.path = .some 0 1 := by
  decide

/-- The old path/deletion/timer theorem still applies to this witness. -/
theorem existing_handoff_classification_flag_one :
    moved.2.core.path ≠ .bot ∧
      RightHandoffOutcome moved.2.core.path outR := by
  have h :=
    BirthShortDoneTerminalHandoffExpiry.row_right_handoff_or_end
      onePos widthPos widthLe leftInput rightInput
  change
    deletionActive leftA = false →
      rightA.core.path = .bot →
      pathMovedRight
        beforeMove.1.core beforeMove.2.core
        moved.1.core moved.2.core = true →
      moved.2.core.path ≠ .bot ∧
        RightHandoffOutcome moved.2.core.path outR at h
  exact h (by decide) (by decide) actualMove.1

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 32768 in
/-- The complete physical-row image.  Main comparison state remains open, but
the flag-one writer has overwritten the responder bit from `true` to `false`. -/
theorem full_row_overwrite_facts :
    outR.core.erase.core.path = .some 0 1 ∧
    outR.core.erase.core.state = .CHECK_ready ∧
    outR.core.erase.core.path2 = none ∧
    outR.core.erase.core.leader = false ∧
    deletionActive outR.core.erase = false ∧
    CheckOpenState outR.core.erase.core.state ∧
    outR.core.erase.core.label = (0 : Fin 1) ∧
    outR.core.erase.core.bit = false ∧
    checkBit outR.core.erase.core.bit 1 = .less ∧
    outR.stall = freshStall 1 := by
  unfold CheckOpenState
  decide

private theorem noOpenMatchedHandoffOutcome_of_nonbot_not_equal
    {ψ κ τ bit : Nat} (hψ : 0 < ψ)
    (u : ExpiringAgentState ψ κ τ)
    (hnonbot : u.core.erase.core.path ≠ .bot)
    (hne : checkBit u.core.erase.core.bit bit ≠ .equal) :
    ¬ OpenMatchedHandoffOutcome hψ bit u := by
  intro h
  rcases h with hend | hlive
  · exact hnonbot hend
  · exact hne hlive.2.2.2.2.1

/-- First failed implication for Part A.

Every requested prepared-input clause holds and the actual DONE movement is a
matched terminal handoff.  `row_right_handoff_or_end` still gives its original
path/deletion/timer conclusion, and the final main state is even
`.CHECK_ready`; nevertheless the final bit no longer matches the retained
payload, so the requested `OpenMatchedHandoffOutcome` is false. -/
theorem flag_one_overwrite_counterexample :
    CorrectedPartAPreparedHypotheses leftPrepared rightPrepared ∧
    (let q := captureStep1 step1Input.1 step1Input.2;
      q.2.path = .some 0 1 ∧
        q.2.state = .CHECK_ready ∧
        q.2.path2 = none) ∧
    pathMovedRight
        beforeMove.1.core beforeMove.2.core
        moved.1.core moved.2.core = true ∧
    moved.2.core.path = .some 0 1 ∧
    outR.core.erase.core.path = .some 0 1 ∧
    outR.core.erase.core.state = .CHECK_ready ∧
    deletionActive outR.core.erase = false ∧
    CheckOpenState outR.core.erase.core.state ∧
    outR.core.erase.core.label = (0 : Fin 1) ∧
    outR.core.erase.core.bit = false ∧
    checkBit outR.core.erase.core.bit 1 = .less ∧
    outR.stall = freshStall 1 ∧
    RightHandoffOutcome moved.2.core.path outR ∧
    ¬ OpenMatchedHandoffOutcome onePos 1 outR := by
  rcases full_row_overwrite_facts with
    ⟨hpath, hstate, _hp2, _hleader, hdel, hopen, hlabel,
      hbit, hless, hstall⟩
  have hh := existing_handoff_classification_flag_one
  refine ⟨requested_prepared_hypotheses,
    actual_matched_capture_flag_one,
    actualMove.1, actualMove.2,
    hpath, hstate, hdel, hopen, hlabel, hbit, hless, hstall,
    hh.2, ?_⟩
  have hneq : checkBit outR.core.erase.core.bit 1 ≠ .equal := by
    rw [hless]
    decide
  have hnonbot : outR.core.erase.core.path ≠ .bot := by
    rw [hpath]
    decide
  exact noOpenMatchedHandoffOutcome_of_nonbot_not_equal
    onePos outR hnonbot hneq

end BirthShortDoneTerminalOpenMatchedHandoffFlagOneCounterexample

#print axioms BirthShortDoneTerminalOpenMatchedHandoffFlagOneCounterexample.requested_prepared_hypotheses
#print axioms BirthShortDoneTerminalOpenMatchedHandoffFlagOneCounterexample.actual_matched_capture_flag_one
#print axioms BirthShortDoneTerminalOpenMatchedHandoffFlagOneCounterexample.existing_handoff_classification_flag_one
#print axioms BirthShortDoneTerminalOpenMatchedHandoffFlagOneCounterexample.full_row_overwrite_facts
#print axioms BirthShortDoneTerminalOpenMatchedHandoffFlagOneCounterexample.flag_one_overwrite_counterexample
