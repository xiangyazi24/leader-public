import Leader.Wu.Birth.ShortDoneTerminalOpenMatchedHandoffCounterexample
import Leader.Wu.Birth.ShortDoneTerminalCheckInputProducer
import Leader.Wu.WriteSeq.StationaryWritePersistent


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B6WriterScopeAudit


open PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair BirthGenerationDone
open PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair
open K2BirthDispatcher K2BirthLeaderNormalize
  BirthArrivalCaptureRepair BirthShortDoneTerminalHost
  BirthShortDoneTerminalEntryCut BirthShortDoneCuts
open BirthShortDoneTerminalOpenMatchedHandoffCounterexample


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


/-- Matched terminal payload bit 1, ready for the actual DONE capture. -/
private def leftRaw : AgentState 1 :=
  { rawBase 0 with path := .some 0 1 }


/-- Flag-one path3, resident bit one, otherwise writer-idle.  On ψ=1 the
WRITE_SEQ comparison itself selects overwrite. -/
private def generatedOverwriteRightRaw : AgentState 1 :=
  { rawBase 0 with
      bit := true
      path3 := some ⟨0, 0, 1⟩ }


/-- Same physical data, but overwrite is already the active writer state. -/
private def activeOverwriteRightRaw : AgentState 1 :=
  { generatedOverwriteRightRaw with write_state := .overwrite }


/-- A queued overwrite command that prepare cannot replace because the writer
is already in the departure state. -/
private def queuedOverwriteRightRaw : AgentState 1 :=
  { generatedOverwriteRightRaw with
      write_state := .depart
      write := .overwrite }


/-- Dirty active increment.  This is not the flag-zero command: the
path3 flag is one and the active state already exists before the row. -/
private def activeIncrementRightRaw : AgentState 1 :=
  { generatedOverwriteRightRaw with write_state := .increment_group }


private theorem leftRawDomain : leftRaw.inProtocolDomain 0 := by
  simp [leftRaw, rawBase, peace1, PeaceView.toState,
    AgentState.inProtocolDomain]


private theorem generatedOverwriteRightRawDomain :
    generatedOverwriteRightRaw.inProtocolDomain 0 := by
  simp [generatedOverwriteRightRaw, rawBase, peace1, PeaceView.toState,
    AgentState.inProtocolDomain]


private theorem activeOverwriteRightRawDomain :
    activeOverwriteRightRaw.inProtocolDomain 0 := by
  simp [activeOverwriteRightRaw, generatedOverwriteRightRaw,
    rawBase, peace1, PeaceView.toState, AgentState.inProtocolDomain]


private theorem queuedOverwriteRightRawDomain :
    queuedOverwriteRightRaw.inProtocolDomain 0 := by
  simp [queuedOverwriteRightRaw, generatedOverwriteRightRaw,
    rawBase, peace1, PeaceView.toState, AgentState.inProtocolDomain]


private theorem activeIncrementRightRawDomain :
    activeIncrementRightRaw.inProtocolDomain 0 := by
  simp [activeIncrementRightRaw, generatedOverwriteRightRaw,
    rawBase, peace1, PeaceView.toState, AgentState.inProtocolDomain]


private def pack (u : AgentState 1) (hu : u.inProtocolDomain 0) :
    ExpiringAgentState 1 0 1 :=
  ⟨⟨BoundedAgentState.ofDomain u hu, false⟩, 0⟩


private def leftInput : ExpiringAgentState 1 0 1 :=
  pack leftRaw leftRawDomain


private def generatedOverwriteRightInput : ExpiringAgentState 1 0 1 :=
  pack generatedOverwriteRightRaw generatedOverwriteRightRawDomain


private def activeOverwriteRightInput : ExpiringAgentState 1 0 1 :=
  pack activeOverwriteRightRaw activeOverwriteRightRawDomain


private def queuedOverwriteRightInput : ExpiringAgentState 1 0 1 :=
  pack queuedOverwriteRightRaw queuedOverwriteRightRawDomain


private def activeIncrementRightInput : ExpiringAgentState 1 0 1 :=
  pack activeIncrementRightRaw activeIncrementRightRawDomain


private def prepared (u : ExpiringAgentState 1 0 1) : AuthorizedAgentState 1 :=
  (prepareExpiringDisposal onePos u).core.erase


private def normalized (u : ExpiringAgentState 1 0 1) : AuthorizedAgentState 1 :=
  normalizeDeletion (prepared u)


private def beforeMove
    (l r : ExpiringAgentState 1 0 1) :
    AuthorizedAgentState 1 × AuthorizedAgentState 1 :=
  generationBeforeMoveEntryWidth onePos widthPos widthLe 0
    (normalized l) (normalized r)


private def moved
    (l r : ExpiringAgentState 1 0 1) :
    AuthorizedAgentState 1 × AuthorizedAgentState 1 :=
  authorizedDoneMove onePos (beforeMove l r).1 (beforeMove l r).2


private def throughCheck
    (l r : ExpiringAgentState 1 0 1) :
    AuthorizedAgentState 1 × AuthorizedAgentState 1 :=
  doneThroughCheckEntryWidth onePos widthPos widthLe 0
    (normalized l) (normalized r)


private def writerInput
    (l r : ExpiringAgentState 1 0 1) :
    AuthorizedAgentState 1 × AuthorizedAgentState 1 :=
  BirthShortDoneCuts.beforeWriteWidth onePos widthPos widthLe
    (throughCheck l r).1 (throughCheck l r).2


private def writerPrepared
    (l r : ExpiringAgentState 1 0 1) : AgentState 1 × AgentState 1 :=
  BirthStationaryWrite.swPersistentThroughPrepare onePos
    (writerInput l r).1.core (writerInput l r).2.core


private def outR
    (l r : ExpiringAgentState 1 0 1) : ExpiringAgentState 1 0 1 :=
  (BirthShortDoneTerminalHost.row onePos widthPos widthLe l r).2


private def NoFlagZeroPath3 (u : AgentState 1) : Prop :=
  ¬ ∃ p3 : Path3Info, u.path3 = some p3 ∧ p3.flag = 0


private theorem noFlagZero_of_exact_flag_one
    (u : AgentState 1)
    (h : u.path3 = some ⟨0, 0, 1⟩) : NoFlagZeroPath3 u := by
  intro hex
  rcases hex with ⟨p3, hp, hf⟩
  rw [h] at hp
  have hp3 : p3 = ⟨0, 0, 1⟩ := (Option.some.inj hp).symm
  subst p3
  exact absurd hf (by decide)


set_option maxRecDepth 20000 in
/-- `hWriter` holds, the stronger quiet predicate holds, and the actual
matched move occurs; nevertheless flag one selects overwrite and changes the
responder bit on the literal full host row. -/
theorem flagOneGeneratedOverwrite_fullHost :
    NoFlagZeroPath3 (prepared generatedOverwriteRightInput).core ∧
    StrictRequestedQuiet
      (prepared leftInput) (prepared generatedOverwriteRightInput) ∧
    pathMovedRight
      (beforeMove leftInput generatedOverwriteRightInput).1.core
      (beforeMove leftInput generatedOverwriteRightInput).2.core
      (moved leftInput generatedOverwriteRightInput).1.core
      (moved leftInput generatedOverwriteRightInput).2.core = true ∧
    (writerPrepared leftInput generatedOverwriteRightInput).2.write = .overwrite ∧
    (outR leftInput generatedOverwriteRightInput).core.erase.core.path = .some 0 1 ∧
    (outR leftInput generatedOverwriteRightInput).core.erase.core.state = .CHECK_ready ∧
    (outR leftInput generatedOverwriteRightInput).core.erase.core.bit = false ∧
    ¬ OpenMatchedHandoffOutcome onePos 1
      (outR leftInput generatedOverwriteRightInput) := by
  constructor
  · apply noFlagZero_of_exact_flag_one
    decide
  · unfold StrictRequestedQuiet OpenMatchedHandoffOutcome CheckOpenState
    decide


set_option maxRecDepth 20000 in
/-- Dirty active overwrite survives prepare and changes the same matched
responder bit. -/
theorem activeOverwrite_fullHost :
    NoFlagZeroPath3 (prepared activeOverwriteRightInput).core ∧
    StrictRequestedQuiet
      (prepared leftInput) (prepared activeOverwriteRightInput) ∧
    pathMovedRight
      (beforeMove leftInput activeOverwriteRightInput).1.core
      (beforeMove leftInput activeOverwriteRightInput).2.core
      (moved leftInput activeOverwriteRightInput).1.core
      (moved leftInput activeOverwriteRightInput).2.core = true ∧
    (writerPrepared leftInput activeOverwriteRightInput).2.write_state = .overwrite ∧
    (outR leftInput activeOverwriteRightInput).core.erase.core.bit = false ∧
    ¬ OpenMatchedHandoffOutcome onePos 1
      (outR leftInput activeOverwriteRightInput) := by
  constructor
  · apply noFlagZero_of_exact_flag_one
    decide
  · unfold StrictRequestedQuiet OpenMatchedHandoffOutcome CheckOpenState
    decide


set_option maxRecDepth 20000 in
/-- A pre-existing overwrite command also survives through the literal writer
when carried in `.depart`, activates at the terminal label, and changes bit. -/
theorem queuedOverwriteCommand_fullHost :
    NoFlagZeroPath3 (prepared queuedOverwriteRightInput).core ∧
    StrictRequestedQuiet
      (prepared leftInput) (prepared queuedOverwriteRightInput) ∧
    pathMovedRight
      (beforeMove leftInput queuedOverwriteRightInput).1.core
      (beforeMove leftInput queuedOverwriteRightInput).2.core
      (moved leftInput queuedOverwriteRightInput).1.core
      (moved leftInput queuedOverwriteRightInput).2.core = true ∧
    (writerPrepared leftInput queuedOverwriteRightInput).2.write = .overwrite ∧
    (outR leftInput queuedOverwriteRightInput).core.erase.core.bit = false ∧
    ¬ OpenMatchedHandoffOutcome onePos 1
      (outR leftInput queuedOverwriteRightInput) := by
  constructor
  · apply noFlagZero_of_exact_flag_one
    decide
  · unfold StrictRequestedQuiet OpenMatchedHandoffOutcome CheckOpenState
    decide


set_option maxRecDepth 20000 in
/-- `clearInputIncrementPair` and `gatePreparedIncrement` do not sanitize an
already active `.increment_group` writer state.  With flag one this is outside
the hWriter exclusion, but Algorithm 19 still flips the responder bit. -/
theorem activeIncrementState_fullHost :
    NoFlagZeroPath3 (prepared activeIncrementRightInput).core ∧
    StrictRequestedQuiet
      (prepared leftInput) (prepared activeIncrementRightInput) ∧
    pathMovedRight
      (beforeMove leftInput activeIncrementRightInput).1.core
      (beforeMove leftInput activeIncrementRightInput).2.core
      (moved leftInput activeIncrementRightInput).1.core
      (moved leftInput activeIncrementRightInput).2.core = true ∧
    (writerPrepared leftInput activeIncrementRightInput).2.write_state =
      .increment_group ∧
    (outR leftInput activeIncrementRightInput).core.erase.core.bit = false ∧
    ¬ OpenMatchedHandoffOutcome onePos 1
      (outR leftInput activeIncrementRightInput) := by
  constructor
  · apply noFlagZero_of_exact_flag_one
    decide
  · unfold StrictRequestedQuiet OpenMatchedHandoffOutcome CheckOpenState
    decide


/-! ## Later-row composition shell -/


variable {ψ width τ : Nat}


/-- The temporal adapter the right physical handoff must establish at the
later row's actual pre-move prefix. -/
def RightResidentMatchProducer
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (laterL laterR : AuthorizedAgentState ψ) : Prop :=
  let b := generationBeforeMoveEntryWidth hψ hwidth hle κ laterL laterR
  b.2.core.reset_cmd = false ∧
    BirthShortDoneTerminalCheckInputProducer.MatchedOpenAt
      b.2.core ⟨ψ - 1, by omega⟩


/-- The still-missing left-side producer. -/
def LeftResidentMatchProducer
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (laterL laterR : AuthorizedAgentState ψ) : Prop :=
  let b := generationBeforeMoveEntryWidth hψ hwidth hle κ laterL laterR
  b.1.core.reset_cmd = false ∧
    BirthShortDoneTerminalCheckInputProducer.MatchedOpenAt
      b.1.core ⟨0, hψ⟩


/-- Exact proposition expressing the cross-row composition.  Part A supplies
`OpenMatchedHandoffOutcome`; a separate right-prefix transport theorem turns
that physical handoff into `RightResidentMatchProducer`; the remaining input is
`LeftResidentMatchProducer`.  The conclusion is precisely the existing later
birth-row source predicate. -/
def CorrectedHandoffToCapturedMatchBirthRow
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (bit : Nat) (priorOut : ExpiringAgentState ψ κ τ)
    (laterL laterR : AuthorizedAgentState ψ) : Prop :=
  (OpenMatchedHandoffOutcome hψ bit priorOut →
      RightResidentMatchProducer hψ hwidth hle κ laterL laterR) →
    LeftResidentMatchProducer hψ hwidth hle κ laterL laterR →
    OpenMatchedHandoffOutcome hψ bit priorOut →
    BirthShortDoneTerminalCheckInputProducer.CapturedMatchBirthRowSource
      hψ hwidth hle κ laterL laterR


#print axioms B6WriterScopeAudit.flagOneGeneratedOverwrite_fullHost
#print axioms B6WriterScopeAudit.activeOverwrite_fullHost
#print axioms B6WriterScopeAudit.queuedOverwriteCommand_fullHost
#print axioms B6WriterScopeAudit.activeIncrementState_fullHost
#print axioms B6WriterScopeAudit.RightResidentMatchProducer
#print axioms B6WriterScopeAudit.LeftResidentMatchProducer
#print axioms B6WriterScopeAudit.CorrectedHandoffToCapturedMatchBirthRow


end B6WriterScopeAudit
