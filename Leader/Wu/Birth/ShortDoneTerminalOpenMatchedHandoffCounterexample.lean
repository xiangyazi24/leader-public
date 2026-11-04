import Leader.Wu.Birth.ShortDoneTerminalHandoffExpiry





namespace BirthShortDoneTerminalOpenMatchedHandoffCounterexample




open PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair BirthGenerationDone
open K2BirthDispatcher K2BirthLeaderNormalize
  BirthArrivalCaptureRepair BirthShortDoneTerminalHost
  BirthShortDoneTerminalEntryCut BirthShortDoneTerminalHandoffExpiry




set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false




variable {ψ κ τ : Nat}




/-- Same open-state predicate as in the proposed handoff. -/
def CheckOpenState (s : MainState) : Prop :=
  s ≠ .done ∧ s ≠ .toss ∧ s ≠ .congest ∧
  s ≠ .depart ∧ s ≠ .equal ∧ s ≠ .larger ∧ s ≠ .less




/-- The proposed handoff conclusion, verbatim. -/
def OpenMatchedHandoffOutcome (hψ : 0 < ψ) (bit : Nat)
    (u : ExpiringAgentState ψ κ τ) : Prop :=
  u.core.erase.core.path = .bot ∨
  (u.core.erase.core.path = .some (ψ - 1) bit ∧
    deletionActive u.core.erase = false ∧
    CheckOpenState u.core.erase.core.state ∧
    u.core.erase.core.label = ⟨ψ - 1, by omega⟩ ∧
    checkBit u.core.erase.core.bit bit = .equal ∧
    u.stall = freshStall τ)




/-- Stronger than the requested reset/path2/deletion quietness.  In particular
    there is no DISAPPEAR carry source and no P-prime probe source.  The one
    thing intentionally not forbidden is writer `path3`. -/
def StrictRequestedQuiet (l r : AuthorizedAgentState ψ) : Prop :=
  l.core.leader = false ∧ r.core.leader = false ∧
  l.core.reset_cmd = false ∧ r.core.reset_cmd = false ∧
  l.core.path2 = none ∧ r.core.path2 = none ∧
  deletionActive l = false ∧ deletionActive r = false ∧
  l.core.p_carry = false ∧ r.core.p = false ∧
  r.core.probe = false




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




/-- Terminal payload bit 0, ready to move. -/
private def leftRaw : AgentState 1 :=
  { rawBase (0 : Fin 1) with path := .some 0 0 }




/-- Empty comparison receiver.  The only extra material is a writer component
    aligned at the unique physical label.  Its bit and flag are both zero. -/
private def rightRaw : AgentState 1 :=
  { rawBase (0 : Fin 1) with path3 := some ⟨0, 0, 0⟩ }




private theorem leftRawDomain : leftRaw.inProtocolDomain 0 := by
  simp [leftRaw, rawBase, peace1, PeaceView.toState,
    AgentState.inProtocolDomain]




private theorem rightRawDomain : rightRaw.inProtocolDomain 0 := by
  simp [rightRaw, rawBase, peace1, PeaceView.toState,
    AgentState.inProtocolDomain]




private def leftInput : ExpiringAgentState 1 0 1 :=
  ⟨⟨BoundedAgentState.ofDomain leftRaw leftRawDomain, false⟩, 0⟩




private def rightInput : ExpiringAgentState 1 0 1 :=
  ⟨⟨BoundedAgentState.ofDomain rightRaw rightRawDomain, false⟩, 0⟩




/-- Literal prepared inputs of the complete row, before orphan normalization. -/
private def leftPrepared : AuthorizedAgentState 1 :=
  (prepareExpiringDisposal onePos leftInput).core.erase




private def rightPrepared : AuthorizedAgentState 1 :=
  (prepareExpiringDisposal onePos rightInput).core.erase




private def leftA : AuthorizedAgentState 1 :=
  normalizeDeletion leftPrepared




private def rightA : AuthorizedAgentState 1 :=
  normalizeDeletion rightPrepared




private def beforeMove :
    AuthorizedAgentState 1 × AuthorizedAgentState 1 :=
  generationBeforeMoveEntryWidth onePos widthPos widthLe 0 leftA rightA




/-- This is exactly the first pair inside `doneCaptureSigMove`, i.e. the input
    to `holdDoneStep1` after `sigMoveLeaderPreclear`. -/
private def step1Input : AgentState 1 × AgentState 1 :=
  PPLLWallSweepRepair.sigMoveLeaderPreclear
    onePos beforeMove.1.core beforeMove.2.core




private def moved : AuthorizedAgentState 1 × AuthorizedAgentState 1 :=
  authorizedDoneMove onePos beforeMove.1 beforeMove.2




private def outR : ExpiringAgentState 1 0 1 :=
  (BirthShortDoneTerminalHost.row
    onePos widthPos widthLe leftInput rightInput).2




/-- Preparation itself introduces no deletion and the requested source-side
    reset/path2/deletion controls are all quiet. -/
private theorem preparedQuiet :
    StrictRequestedQuiet leftPrepared rightPrepared ∧
    leftA = leftPrepared ∧ rightA = rightPrepared ∧
    rightA.core.path = .bot := by
  unfold StrictRequestedQuiet
  decide




/-- Exact source facts for the actual matched Step1 branch. -/
private theorem matchedSource :
    step1Input.1.leader = false ∧
    step1Input.2.leader = false ∧
    step1Input.1.state ≠ .done ∧
    step1Input.1.state ≠ .lock ∧
    step1Input.1.state ≠ .compare1 ∧
    step1Input.1.state ≠ .CHECK_ready ∧
    step1Input.1.path = .some 0 0 ∧
    step1Input.1.path2 = none ∧
    step1Input.2.path = .bot ∧
    step1Input.2.state ≠ .produce ∧
    step1Input.2.label = ⟨0, onePos⟩ ∧
    checkBit step1Input.2.bit 0 = .equal := by
  decide




/-- `holdDoneStep1` really takes the ordinary capture branch in the current
    `authorizedDoneMove`; this is not an assumed future state. -/
private theorem doneGuardReachesCapture :
    holdDoneStep1 step1Input.1 step1Input.2 =
      captureStep1 step1Input.1 step1Input.2 := by
  rcases matchedSource with
    ⟨_, _, hdone, _, _, _, _, _, _, _, _, _⟩
  exact holdDoneStep1_of_no_done _ _ hdone




/-- The concrete Step1 is exactly the source theorem `captureStep1_matched`. -/
private theorem actualMatchedCapture :
    let q := captureStep1 step1Input.1 step1Input.2
    q.2.path = .some 0 0 ∧
      q.2.state = .CHECK_ready ∧
      q.2.path2 = none := by
  rcases matchedSource with
    ⟨_, _, _, hlock, hcompare1, hready, hlpath, _,
      hrpath, hrproduce, hrlabel, _⟩
  have halign : step1Input.2.label.val = 0 := by
    rw [hrlabel]
  have h := captureStep1_matched step1Input.1 step1Input.2 0 0
    hlpath hrpath ⟨hlock, hcompare1, hready⟩
    (Or.inl hrproduce) halign
  dsimp only at h ⊢
  exact ⟨h.2.1.trans hlpath, h.2.2.1, h.2.2.2.1⟩




/-- The matched payload also survives the current DONE movement wrapper. -/
private theorem actualMove :
    pathMovedRight beforeMove.1.core beforeMove.2.core
      moved.1.core moved.2.core = true ∧
    moved.2.core.path = .some 0 0 := by
  decide




set_option maxRecDepth 20000 in
/-- Full-row output: comparison state/path/path2 are still exactly the desired
    live handoff, deletion is inactive, and expiry refreshed the stall.  The
    stationary writer, however, flipped the physical bit. -/
private theorem fullRowFacts :
    outR.core.erase.core.path = .some 0 0 ∧
    outR.core.erase.core.state = .CHECK_ready ∧
    outR.core.erase.core.path2 = none ∧
    outR.core.erase.core.leader = false ∧
    deletionActive outR.core.erase = false ∧
    CheckOpenState outR.core.erase.core.state ∧
    outR.core.erase.core.label = ⟨0, onePos⟩ ∧
    outR.core.erase.core.bit = true ∧
    checkBit outR.core.erase.core.bit 0 = .larger ∧
    outR.stall = freshStall 1 := by
  unfold CheckOpenState
  decide




/-- Keep the outcome split away from the concrete `outR`: with `u` opaque,
    reducing the predicate exposes only the small logical disjunction and does
    not ask Lean to normalize the complete terminal-host row. -/
private theorem noOpenMatchedHandoffOutcome_of_nonbot_larger
    {bit : Nat} (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ)
    (hnonbot : u.core.erase.core.path ≠ .bot)
    (hlarge : checkBit u.core.erase.core.bit bit = .larger) :
    ¬ OpenMatchedHandoffOutcome hψ bit u := by
  intro h
  rcases h with hend | hlive
  · exact hnonbot hend
  · have heq : checkBit u.core.erase.core.bit bit = .equal :=
      hlive.2.2.2.2.1
    have hbad : (MainState.larger : MainState) = .equal :=
      hlarge.symm.trans heq
    cases hbad




/-- Therefore the exact proposed outcome is false. -/
theorem smallestFullHostCounterexample :
    StrictRequestedQuiet leftPrepared rightPrepared ∧
    pathMovedRight beforeMove.1.core beforeMove.2.core
      moved.1.core moved.2.core = true ∧
    outR.core.erase.core.path ≠ .bot ∧
    CheckOpenState outR.core.erase.core.state ∧
    ¬ OpenMatchedHandoffOutcome onePos 0 outR := by
  rcases fullRowFacts with
    ⟨hpath, _, _, _, _, hopen, _, _, hlarge, _⟩
  have hnonbot : outR.core.erase.core.path ≠ .bot := by
    intro hbot
    rw [hpath] at hbot
    cases hbot
  refine ⟨preparedQuiet.1, actualMove.1, hnonbot, hopen, ?_⟩
  exact noOpenMatchedHandoffOutcome_of_nonbot_larger
    onePos outR hnonbot hlarge




#print axioms BirthShortDoneTerminalOpenMatchedHandoffCounterexample.actualMatchedCapture
#print axioms BirthShortDoneTerminalOpenMatchedHandoffCounterexample.smallestFullHostCounterexample




end BirthShortDoneTerminalOpenMatchedHandoffCounterexample
