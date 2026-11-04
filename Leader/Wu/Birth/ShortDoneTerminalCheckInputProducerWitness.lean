import Leader.Wu.Birth.ShortDoneTerminalCheckInputProducer
import Leader.Wu.Birth.ShortDoneTerminalCheckInputNonvacuity






/-!
# CHECK source-producer nonvacuity and strict-scope witness






Part 1 reuses the tracked reachable positive pair and proves that its literal
prepared pre-DONE row satisfies `PreparedCapturedMatchBirthSource`.  The birth
is then obtained only through the source producer.






Part 2 changes only one bounded left `path2` field.  Its raw erasure is the
inert action-2, position-0 control.  The actual pre-CHECK predicate remains
true, but the source producer fails exactly at the left `MatchedOpenAt.path2`
clause.
-/






namespace BirthShortDoneTerminalCheckInputProducerAudit






open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair






open BirthShortDoneTerminalEntryCut
  BirthShortDoneTerminalCheckInputSources
  BirthShortDoneTerminalCheckInputSufficiency
  BirthShortDoneTerminalCheckInputProducer






set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false






private theorem hpsi : 0 < 2 := by decide
private theorem hpsi2 : 1 < 2 := by decide
private theorem hwidth : 0 < 2 := by decide
private theorem hle : 2 ≤ 2 := by decide






/-! ## Part 1: the tracked actual pair satisfies the producer source -/






private def actualL0 : AuthorizedAgentState 2 :=
  normalizeDeletion
    (prepareExpiringDisposal hpsi
      BirthShortDoneTerminalCheckInputNonvacuity.actualL).core.erase






private def actualR0 : AuthorizedAgentState 2 :=
  normalizeDeletion
    (prepareExpiringDisposal hpsi
      BirthShortDoneTerminalCheckInputNonvacuity.actualR).core.erase






private def actualBefore : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  generationBeforeMoveEntryWidth hpsi hwidth hle 2 actualL0 actualR0






set_option maxHeartbeats 32000000 in
set_option maxRecDepth 32768 in
/-- Finite source snapshot of the actual positive pair.  The two existential
`MatchedOpenAt` payloads are made explicit as bit zero below rather than hidden
inside an unbounded `Exists Nat` decision. -/
theorem actual_before_source_snapshot :
    actualBefore.1.core.reset_cmd = false ∧
    actualBefore.2.core.reset_cmd = false ∧
    actualBefore.1.core.leader = false ∧
    actualBefore.1.core.label = (0 : Fin 2) ∧
    actualBefore.1.core.path2 = none ∧
    CheckOpenState actualBefore.1.core.state ∧
    actualBefore.1.core.path = .some 0 0 ∧
    checkBit actualBefore.1.core.bit 0 = .equal ∧
    actualBefore.2.core.leader = false ∧
    actualBefore.2.core.label = (1 : Fin 2) ∧
    actualBefore.2.core.path2 = none ∧
    CheckOpenState actualBefore.2.core.state ∧
    actualBefore.2.core.path = .some 1 0 ∧
    checkBit actualBefore.2.core.bit 0 = .equal := by
  unfold CheckOpenState
  decide






/-- The actual prepared pair has the exact captured-match pre-DONE source
required by the new producer. -/
theorem actual_captured_match_source :
    CapturedMatchBirthRowSource hpsi hwidth hle 2 actualL0 actualR0 := by
  change
    actualBefore.1.core.reset_cmd = false ∧
    actualBefore.2.core.reset_cmd = false ∧
    MatchedOpenAt actualBefore.1.core (0 : Fin 2) ∧
    MatchedOpenAt actualBefore.2.core (1 : Fin 2)
  rcases actual_before_source_snapshot with
    ⟨hlReset, hrReset,
      hlLeader, hlLabel, hlP2, hlOpen, hlPath, hlBit,
      hrLeader, hrLabel, hrP2, hrOpen, hrPath, hrBit⟩
  refine ⟨hlReset, hrReset, ?_, ?_⟩
  · unfold MatchedOpenAt
    refine ⟨hlLeader, hlLabel, hlP2, hlOpen, ?_⟩
    exact ⟨0, hlPath, hlBit⟩
  · unfold MatchedOpenAt
    refine ⟨hrLeader, hrLabel, hrP2, hrOpen, ?_⟩
    exact ⟨0, hrPath, hrBit⟩






set_option maxHeartbeats 32000000 in
set_option maxRecDepth 32768 in
/-- Nonvacuity on the tracked actual input pair. -/
theorem actual_pair_prepared_captured_match_source :
    PreparedCapturedMatchBirthSource hpsi hwidth hle
      BirthShortDoneTerminalCheckInputNonvacuity.actualL
      BirthShortDoneTerminalCheckInputNonvacuity.actualR := by
  rcases
      BirthShortDoneTerminalCheckInputNonvacuity.actual_pair_and_prepared_premises with
    ⟨_hlInput, _hrInput, hrDeletion, hlDeletion, hrFollower⟩
  unfold PreparedCapturedMatchBirthSource
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [actualR0, BirthShortDoneTerminalCheckInputNonvacuity.r0] using
      hrDeletion
  · simpa [actualL0, BirthShortDoneTerminalCheckInputNonvacuity.l0] using
      hlDeletion
  · simpa [actualR0, BirthShortDoneTerminalCheckInputNonvacuity.r0] using
      hrFollower
  · exact actual_captured_match_source






/-- Required route audit: this theorem deliberately calls the new source
producer rather than evaluating the complete row. -/
theorem actual_pair_birth_through_captured_match_producer :
    BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      BirthShortDoneTerminalCheckInputNonvacuity.actualL
      BirthShortDoneTerminalCheckInputNonvacuity.actualR = true := by
  exact
    BirthShortDoneTerminalCheckInputProducer.birthEvent_true_of_prepared_captured_match_source
      hpsi hpsi2 hwidth hle
      BirthShortDoneTerminalCheckInputNonvacuity.actualL
      BirthShortDoneTerminalCheckInputNonvacuity.actualR
      actual_pair_prepared_captured_match_source






/-! ## Part 2: strict scope of the source producer -/






/-- Bounded action value `1` erases to raw action `2`; position zero makes this
control inert in the current DONE movement on the left endpoint. -/
def scopeInertLeftControl : BoundedPath2Info 2 :=
  { label := 0
    bit := 0
    position := 0
    action := 1 }






/-- Concrete scope witness: the tracked left input with only the bounded
comparison-control field changed.  All other finite protocol fields, including
`psi=2`, `kappa=2`, `tau=16`, and the timer, are retained literally. -/
def scopeL : ExpiringAgentState 2 2 16 :=
  { BirthShortDoneTerminalCheckInputNonvacuity.actualL with
    core :=
      { BirthShortDoneTerminalCheckInputNonvacuity.actualL.core with
        core :=
          { BirthShortDoneTerminalCheckInputNonvacuity.actualL.core.core with
            path2 := some scopeInertLeftControl } } }






/-- The responder is exactly the tracked actual responder. -/
def scopeR : ExpiringAgentState 2 2 16 :=
  BirthShortDoneTerminalCheckInputNonvacuity.actualR






def scopeL0 : AuthorizedAgentState 2 :=
  normalizeDeletion (prepareExpiringDisposal hpsi scopeL).core.erase






def scopeR0 : AuthorizedAgentState 2 :=
  normalizeDeletion (prepareExpiringDisposal hpsi scopeR).core.erase






def scopeBefore : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  generationBeforeMoveEntryWidth hpsi hwidth hle 2 scopeL0 scopeR0






def scopeCut : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  doneBeforeCheckEntryWidth hpsi hwidth hle 2 scopeL0 scopeR0






set_option maxHeartbeats 32000000 in
set_option maxRecDepth 32768 in
/-- Exact failing source clause.  The bounded action index `1` has erased to
raw action `2`, and the generation prefix leaves this position-zero control in
place. -/
theorem scope_before_left_path2_is_inert_control :
    scopeBefore.1.core.path2 = some ⟨0, 0, 0, 2⟩ := by
  decide






private theorem scope_before_left_path2_not_none :
    scopeBefore.1.core.path2 ≠ none := by
  rw [scope_before_left_path2_is_inert_control]
  simp






set_option maxHeartbeats 32000000 in
set_option maxRecDepth 32768 in
/-- The actual sanitized pre-CHECK cut still has the complete live-path CHECK
input.  Again the Nat witnesses are stated explicitly rather than decided as
an unbounded existential. -/
theorem scope_cut_snapshot :
    scopeCut.1.core.state ≠ .done ∧
    scopeCut.2.core.state ≠ .done ∧
    scopeCut.1.core.state ≠ .toss ∧
    scopeCut.2.core.state ≠ .toss ∧
    scopeCut.1.core.state ≠ .congest ∧
    scopeCut.2.core.state ≠ .congest ∧
    scopeCut.2.core.state ≠ .equal ∧
    scopeCut.2.core.leader = false ∧
    scopeCut.2.core.label = (1 : Fin 2) ∧
    scopeCut.2.core.path = .some 1 0 ∧
    ReadyInputAt scopeCut.2.core 1 ∧
    (checkSigCheckL hpsi (checkSigSetReady scopeCut.1.core)).label.val < 2 - 1 ∧
    (checkSigCheckL hpsi (checkSigSetReady scopeCut.1.core)).state = .equal ∧
    checkBit scopeCut.2.core.bit 0 = .equal := by
  unfold ReadyInputAt
  decide






/-- The broader accepted CHECK predicate still holds at the literal current
`doneBeforeCheckEntryWidth` cut. -/
theorem scope_actual_check_input :
    ActualCheckBirthInput hpsi
      (doneBeforeCheckEntryWidth hpsi hwidth hle 2 scopeL0 scopeR0) := by
  change ActualCheckBirthInput hpsi scopeCut
  rcases scope_cut_snapshot with
    ⟨hdl, hdr, htl, htr, hcl, hcr, _hrNotEqual,
      hrLeader, hrLabel, hrPath, hrReady, hlLabel, hlEqual, hrBit⟩
  unfold ActualCheckBirthInput
  refine ⟨hdl, hdr, htl, htr, hcl, hcr, ?_⟩
  unfold CheckFollowerBirthInput
  refine ⟨hrLeader, ?_, Or.inr ?_⟩
  · simpa using hrLabel
  · exact ⟨1, 0, hrPath, hrReady, hlLabel, hlEqual, hrBit⟩






set_option maxHeartbeats 32000000 in
set_option maxRecDepth 32768 in
/-- The surrounding prepared ordinary-CHECK guards are also live for the
scope witness; the separation is genuinely inside the accepted CHECK branch. -/
theorem scope_prepared_ordinary_guards :
    deletionActive scopeR0 = false ∧
    deletionActive scopeL0 = false ∧
    scopeR0.core.leader = false := by
  decide






set_option maxHeartbeats 32000000 in
set_option maxRecDepth 32768 in
/-- Exact strictness: `ActualCheckBirthInput` does not imply this producer's
stronger pre-DONE `PreparedCapturedMatchBirthSource`.  Failure is specifically
left `MatchedOpenAt.path2 = none`. -/
theorem scope_not_prepared_captured_match_source :
    ¬ PreparedCapturedMatchBirthSource hpsi hwidth hle scopeL scopeR := by
  intro hsrc
  change
    deletionActive scopeR0 = false ∧
    deletionActive scopeL0 = false ∧
    scopeR0.core.leader = false ∧
    CapturedMatchBirthRowSource hpsi hwidth hle 2 scopeL0 scopeR0 at hsrc
  have hrow := hsrc.2.2.2
  change
    scopeBefore.1.core.reset_cmd = false ∧
    scopeBefore.2.core.reset_cmd = false ∧
    MatchedOpenAt scopeBefore.1.core (0 : Fin 2) ∧
    MatchedOpenAt scopeBefore.2.core (1 : Fin 2) at hrow
  have hleft := hrow.2.2.1
  unfold MatchedOpenAt at hleft
  exact scope_before_left_path2_not_none hleft.2.2.1






/-- Optional positive audit of the scope witness: although the stronger source
producer cannot apply, the already-proved general prepared ordinary-CHECK
sufficiency does apply and produces the same current birth event. -/
theorem scope_birth_through_general_check_sufficiency :
    BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle scopeL scopeR = true := by
  rcases scope_prepared_ordinary_guards with
    ⟨hrDeletion, hlDeletion, hrFollower⟩
  exact
    BirthShortDoneTerminalCheckInputSufficiency.birthEvent_true_of_prepared_ordinary_check_input
      hpsi hwidth hle scopeL scopeR
      (by simpa [scopeR0] using hrDeletion)
      (by simpa [scopeL0] using hlDeletion)
      (by simpa [scopeR0] using hrFollower)
      (by simpa [scopeL0, scopeR0] using scope_actual_check_input)






/-- Packaged scope statement requested by the audit. -/
theorem actual_check_input_strictly_broader_than_captured_match_source :
    ActualCheckBirthInput hpsi
        (doneBeforeCheckEntryWidth hpsi hwidth hle 2 scopeL0 scopeR0) ∧
      ¬ PreparedCapturedMatchBirthSource hpsi hwidth hle scopeL scopeR :=
  ⟨scope_actual_check_input, scope_not_prepared_captured_match_source⟩






end BirthShortDoneTerminalCheckInputProducerAudit
