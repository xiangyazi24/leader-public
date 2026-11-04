import Leader.Wu.Birth.GenerationDoneFullPhase
import Leader.Wu.Safety.NoCheckBirthConditionTwoProtocol


set_option autoImplicit false


namespace BirthGenerationDoneAllWidthProducerPrimitives


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLLeaderCreationCleanupRepair PPLLCompleteMultiLeaderCleanup
  PPLLWallSweepNormalResetContract PPLLWriteIncrementGate
  BirthCheckCongestGuardRepair BirthGenerationControlRepair
  BirthSigMoveDisposalRepair BirthMismatchDisposalProducer
  BirthArrivalCaptureRepair BirthTossCheckPreservationRepair
  BirthSingleUseReleaseRepair BirthGenerationDone PPLLTerminalEqualSupportRepair


variable {psi kappa : Nat}


/-- Entire source group is follower/quiet; only label and resident bit vary. -/
def sourcePeace (j : Fin psi) : PeaceView psi :=
  { leader := false
    label := j
    shield := false
    bullet := 0
    signal_B := 0 }


def sourceBase (bits : Fin psi -> Bool) (j : Fin psi) : AgentState psi :=
  { PeaceView.toState (sourcePeace j) with bit := bits j }


def sourcePayload (bits : Fin psi -> Bool) (j : Fin psi) : PathInfo :=
  .some j.val (if bits j then 1 else 0)


/-- Nonterminal source cells are already producers; the cap is passive. -/
def preRaw (bits : Fin psi -> Bool) (j : Fin psi) : AgentState psi :=
  if j.val < psi - 1 then
    { sourceBase bits j with state := .produce }
  else sourceBase bits j


/-- Held backward acknowledgement after writing a positive label. -/
def ackRaw (bits : Fin psi -> Bool) (j : Fin psi) : AgentState psi :=
  { sourceBase bits j with
    state := .done
    path := sourcePayload bits j
    path2 := none
    path4 := if 0 < j.val then some (Int.ofNat j.val, 1) else none }


/-- Full-host completed source record.  Gated WRITE leaves every positive
responder in writer departure; the final label-zero initiator stays none. -/
def departRaw (bits : Fin psi -> Bool) (j : Fin psi) : AgentState psi :=
  { sourceBase bits j with
    state := .depart
    wait := true
    path := sourcePayload bits j
    path2 := none
    h_field := decide (j.val = 0)
    path5 := if 0 < j.val ∧ j.val < psi - 1 then
      some (Int.ofNat j.val, 1) else none
    write_state := if j.val = 0 then .none else .depart }


def authRaw (u : AgentState psi) : AuthorizedAgentState psi := ⟨u, false⟩


/-- Canonical source base is in the finite domain for every kappa. -/
theorem sourceBase_domain (bits : Fin psi -> Bool) (j : Fin psi) :
    (sourceBase bits j).inProtocolDomain kappa := by
  simp [sourceBase, sourcePeace, PeaceView.toState,
    AgentState.inProtocolDomain]


/-- Changing only the main phase to produce cannot enlarge the domain. -/
theorem preRaw_domain (bits : Fin psi -> Bool) (j : Fin psi) :
    (preRaw bits j).inProtocolDomain kappa := by
  by_cases hp : j.val < psi - 1 <;>
    simp [preRaw, hp, sourceBase, sourcePeace, PeaceView.toState,
      AgentState.inProtocolDomain]


/-- The ACK's path and path4 use the resident Fin bound directly. -/
theorem ackRaw_domain (bits : Fin psi -> Bool) (j : Fin psi) :
    (ackRaw bits j).inProtocolDomain kappa := by
  have hj := j.isLt
  cases hb : bits j <;>
    by_cases hp : 0 < j.val <;>
    simp_all [ackRaw, sourcePayload, sourceBase, sourcePeace,
      PeaceView.toState, AgentState.inProtocolDomain] <;> omega


private theorem permit_false (u : AgentState psi) :
    normalizePermit u false = false := by
  cases h : u.path with
  | bot => simp [normalizePermit, h]
  | some j b =>
      cases j <;> simp [normalizePermit, h]


private theorem reconcile_false (old out : AgentState psi) :
    reconcilePermit ⟨old, false⟩ out = false := by
  unfold reconcilePermit
  split
  · exact permit_false out
  · rfl



/-- The departure path5 branch is simplified *before* arithmetic.  `j.isLt`
also supplies positivity of psi in the zero-label branch. -/
theorem departRaw_domain (bits : Fin psi -> Bool) (j : Fin psi) :
    (departRaw bits j).inProtocolDomain kappa := by
  have hj : j.val < psi := j.isLt
  have hpsi : 0 < psi := by omega
  cases hb : bits j <;>
    by_cases hp : 0 < j.val ∧ j.val < psi - 1 <;>
    simp [departRaw, sourcePayload, sourceBase, sourcePeace,
      PeaceView.toState, AgentState.inProtocolDomain,
      hb, hp, hj, hpsi] <;> omega

/-- Exact post-GEN/pre-CLEAN left record. -/
private def ackBeforeClean (bits : Fin psi -> Bool) (j : Fin psi) :
    AgentState psi :=
  { ackRaw bits j with path4 := none }

/-- Exact terminal responder before the final WRITE sequence. -/
private def departBeforeWrite (bits : Fin psi -> Bool) (j : Fin psi) :
    AgentState psi :=
  { departRaw bits j with write_state := .none }

/-- False authorization remains false through an ordinary reconciled stage. -/
private theorem authorizedReconcile_authRaw
    (f : AgentState psi -> AgentState psi -> AgentState psi × AgentState psi)
    (a b a' b' : AgentState psi)
    (h : f a b = (a', b')) :
    authorizedReconcile f (authRaw a) (authRaw b) =
      (authRaw a', authRaw b') := by
  unfold authorizedReconcile authRaw
  rw [h]
  simp [reconcile_false]

/-- The terminal source edge is already P-prime aligned. -/
private theorem terminal_ppsi_raw (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    pPsiLeaderResetProbeWall (by omega) (preRaw bits l) (preRaw bits r) =
      (preRaw bits l, preRaw bits r) := by
  dsimp only
  have hl : psi - 2 < psi - 1 := by omega
  have hr : ¬ psi - 1 < psi - 1 := by omega
  have hmod : (psi - 2 + 1) % psi = psi - 1 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp [pPsiLeaderResetProbeWall, pPsi, preRaw,
    sourceBase, sourcePeace, PeaceView.toState, hl, hr, hmod] <;> omega

private theorem terminal_ppsi (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    authorizedPPsiLeaderResetProbeWall (by omega)
      (authRaw (preRaw bits l)) (authRaw (preRaw bits r)) =
      (authRaw (preRaw bits l), authRaw (preRaw bits r)) := by
  dsimp only
  unfold authorizedPPsiLeaderResetProbeWall
  dsimp only [authRaw]
  have h := terminal_ppsi_raw hwidth bits
  dsimp only at h
  rw [h]
  simp [authRaw, reconcile_false]

/-- WAIT on the terminal edge is uniform in kappa, including kappa=0. -/
private theorem terminal_wait (hwidth : 3 ≤ psi) (kappa : Nat)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    waitSaturated (by omega) kappa (preRaw bits l) (preRaw bits r) =
      (preRaw bits l, { sourceBase bits r with wait := true }) := by
  dsimp only
  have hl : psi - 2 < psi - 1 := by omega
  have hr : ¬ psi - 1 < psi - 1 := by omega
  have hl0 : psi - 2 ≠ 0 := by omega
  have hr0 : psi - 1 ≠ 0 := by omega
  have hlt : psi - 2 ≠ psi - 1 := by omega
  cases kappa with
  | zero =>
      simp [waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
        waitSaturatedReset, waitSaturatedFinish, preRaw,
        sourceBase, sourcePeace, PeaceView.toState,
        hl, hr, hl0, hr0, hlt]
  | succ k =>
      simp [waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
        waitSaturatedReset, waitSaturatedFinish, preRaw,
        sourceBase, sourcePeace, PeaceView.toState,
        hl, hr, hl0, hr0, hlt]

/-- Exact raw GEN output, before CLEAN connects the adjacent components. -/
private theorem terminal_gen_raw (hwidth : 3 ≤ psi) (kappa : Nat)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    genClean (by omega) kappa (preRaw bits l) (preRaw bits r) =
      (ackBeforeClean bits l, departBeforeWrite bits r) := by
  dsimp only
  have hl : psi - 2 < psi - 1 := by omega
  have hl0 : psi - 2 ≠ 0 := by omega
  have hr0 : psi - 1 ≠ 0 := by omega
  have hrpos : 0 < psi - 1 := by omega
  have hlt : psi - 2 ≠ psi - 1 := by omega
  unfold genClean
  have hw := terminal_wait hwidth kappa bits
  dsimp only at hw
  rw [hw]
  simp [genCleanAfterWait, genSigSaturatedStart, genCleanEmit,
    genCleanPropagate, genSigSaturatedFinish,
    ackBeforeClean, departBeforeWrite, ackRaw, departRaw,
    sourcePayload, preRaw, sourceBase, sourcePeace, PeaceView.toState,
    hl, hl0, hr0, hrpos, hlt]

private theorem terminal_gen (hwidth : 3 ≤ psi) (kappa : Nat)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    authorizedGenClean (by omega) kappa
      (authRaw (preRaw bits l)) (authRaw (preRaw bits r)) =
      (authRaw (ackBeforeClean bits l),
       authRaw (departBeforeWrite bits r)) := by
  dsimp only
  unfold authorizedGenClean
  apply authorizedReconcile_authRaw
  simpa only using (terminal_gen_raw hwidth kappa bits)

/-- CLEAN's two adjacent connectors match exactly: right path4 and left path5
are consumed, while the positive ACK keeps its own path4. -/
private theorem terminal_clean_raw (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    cleanSig (by omega) (ackBeforeClean bits l) (departBeforeWrite bits r) =
      (ackRaw bits l, departBeforeWrite bits r) := by
  dsimp only
  have hlpos : 0 < psi - 2 := by omega
  have hrpos : 0 < psi - 1 := by omega
  have hl0 : psi - 2 ≠ 0 := by omega
  have hr0 : psi - 1 ≠ 0 := by omega
  have hlt : psi - 2 ≠ psi - 1 := by omega
  have hplus : psi - 2 + 1 = psi - 1 := by omega
  have hpredNat : psi - 1 = psi - 2 + 1 := by omega
  have hclean : (↑(psi - 2) : Int) = ↑(psi - 1) - 1 := by
    rw [hpredNat]
    simp
  simp [cleanSig, cleanSigGenConnect, cleanSigStep3, cleanSigStep4,
    cleanSigStep5, cleanSigStep6, cleanSigCleanApply,
    ackBeforeClean, departBeforeWrite, ackRaw, departRaw, sourcePayload,
    sourceBase, sourcePeace, PeaceView.toState,
    hlpos, hrpos, hl0, hr0, hlt, hplus]
  all_goals
    rw [← hclean]
    simp


private theorem terminal_clean (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    authorizedCleanSig (by omega)
      (authRaw (ackBeforeClean bits l))
      (authRaw (departBeforeWrite bits r)) =
      (authRaw (ackRaw bits l), authRaw (departBeforeWrite bits r)) := by
  dsimp only
  unfold authorizedCleanSig
  apply authorizedReconcile_authRaw
  simpa only using (terminal_clean_raw hwidth bits)

private theorem terminal_eliminate_raw (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    eliminateSig (by omega) (ackRaw bits l) (departBeforeWrite bits r) =
      (ackRaw bits l, departBeforeWrite bits r) := by
  dsimp only
  simp [eliminateSig, departBeforeWrite, departRaw]

private theorem terminal_eliminate (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    authorizedEliminateSig (by omega)
      (authRaw (ackRaw bits l)) (authRaw (departBeforeWrite bits r)) =
      (authRaw (ackRaw bits l), authRaw (departBeforeWrite bits r)) := by
  dsimp only
  unfold authorizedEliminateSig
  apply authorizedReconcile_authRaw
  simpa only using (terminal_eliminate_raw hwidth bits)

/-- Complete actual prefix through GEN/CLEAN/ELIMINATE, but not movement. -/
private theorem terminal_before_move (hwidth : 3 ≤ psi) (kappa : Nat)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    generationBeforeMove (by omega) kappa
      (authRaw (preRaw bits l)) (authRaw (preRaw bits r)) =
      (authRaw (ackRaw bits l), authRaw (departBeforeWrite bits r)) := by
  dsimp only
  unfold generationBeforeMove
  dsimp only
  rw [terminal_ppsi hwidth bits]
  dsimp only
  rw [terminal_gen hwidth kappa bits]
  dsimp only
  rw [terminal_clean hwidth bits]
  dsimp only
  simpa only using (terminal_eliminate hwidth bits)

/-- DONE movement holds the ACK in place; path2 transport/control and the
single-use control tail are still executed and are all inert on this pair. -/
private theorem terminal_done_move_raw (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    doneCaptureSigMove (by omega) (ackRaw bits l) (departBeforeWrite bits r) =
      (ackRaw bits l, departBeforeWrite bits r) := by
  dsimp only
  simp [doneCaptureSigMove, sigMoveLeaderPreclear,
    incompleteLeftLeaderBoundary, clearIfLeader,
    doneTransfers, holdDoneStep1, controlTransfers,
    sigMoveStep2, sigMoveStep3, sigMoveStep4, sigMoveStep5,
    comparisonLeaderWall, singleUseControlTail, singleUseApplyControl,
    ackRaw, departBeforeWrite, departRaw, sourceBase, sourcePeace,
    PeaceView.toState] <;> omega

private theorem terminal_done_move (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    authorizedDoneMove (by omega)
      (authRaw (ackRaw bits l)) (authRaw (departBeforeWrite bits r)) =
      (authRaw (ackRaw bits l), authRaw (departBeforeWrite bits r)) := by
  dsimp only
  unfold authorizedDoneMove
  dsimp only [authRaw]
  have hm := terminal_done_move_raw hwidth bits
  dsimp only at hm
  rw [hm]
  simp [pathMovedRight, authRaw, reconcile_false,
    departBeforeWrite, departRaw, sourcePayload]

/-- The reset wall and terminal-equality sanitizer are both literally inert. -/
private theorem terminal_reset_sanitize (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    sanitizeAuthorizedPair (by omega)
      (preCheckResetWall (authRaw (ackRaw bits l))
        (authRaw (departBeforeWrite bits r))) =
      (authRaw (ackRaw bits l), authRaw (departBeforeWrite bits r)) := by
  dsimp only
  have hw := preCheckResetWall_eq_of_inactive
    (authRaw (ackRaw bits (⟨psi - 2, by omega⟩ : Fin psi)))
    (authRaw (departBeforeWrite bits (⟨psi - 1, by omega⟩ : Fin psi)))
    (by simp [authRaw, ackRaw, sourceBase, sourcePeace, PeaceView.toState])
    (by simp [authRaw, ackRaw, sourceBase, sourcePeace, PeaceView.toState])
    (by simp [authRaw, departBeforeWrite, departRaw,
      sourceBase, sourcePeace, PeaceView.toState])
  rw [hw]
  simp [sanitizeAuthorizedPair, sanitizeAuthorizedTerminalEqual,
    unsupportedTerminalEqual, authRaw, ackRaw, departBeforeWrite, departRaw,
    sourceBase, sourcePeace, PeaceView.toState] <;> omega

private theorem terminal_before_check (hwidth : 3 ≤ psi) (kappa : Nat)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    doneBeforeCheck (by omega) kappa
      (authRaw (preRaw bits l)) (authRaw (preRaw bits r)) =
      (authRaw (ackRaw bits l), authRaw (departBeforeWrite bits r)) := by
  dsimp only
  unfold doneBeforeCheck
  dsimp only
  rw [terminal_before_move hwidth kappa bits]
  dsimp only
  rw [terminal_done_move hwidth bits]
  dsimp only
  simpa only using (terminal_reset_sanitize hwidth bits)

/-- The actual CHECK replacement sees current `.done` and is exact identity. -/
private theorem terminal_check (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    preserveDoneCheck (by omega)
      (authRaw (ackRaw bits l)) (authRaw (departBeforeWrite bits r)) =
      (authRaw (ackRaw bits l), authRaw (departBeforeWrite bits r)) := by
  dsimp only
  apply preserveDoneCheck_of_done
  exact Or.inl rfl

private theorem terminal_birth_false (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    leaderBirthBeforeOrAtCheck
      (authRaw (preRaw bits l)) (authRaw (preRaw bits r))
      (authRaw (ackRaw bits l), authRaw (departBeforeWrite bits r))
      (authRaw (ackRaw bits l), authRaw (departBeforeWrite bits r)) = false := by
  dsimp only
  simp [leaderBirthBeforeOrAtCheck, endpointLeaderBorn, authRaw,
    preRaw, ackRaw, departBeforeWrite, departRaw,
    sourceBase, sourcePeace, PeaceView.toState] <;> omega

private theorem terminal_disappear_raw (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    disappear (by omega) (ackRaw bits l) (departBeforeWrite bits r) =
      (ackRaw bits l, departBeforeWrite bits r) := by
  dsimp only
  simp [disappear, ackRaw, departBeforeWrite, departRaw,
    sourceBase, sourcePeace, PeaceView.toState]

private theorem terminal_disappear (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    authorizedDisappear (by omega)
      (authRaw (ackRaw bits l)) (authRaw (departBeforeWrite bits r)) =
      (authRaw (ackRaw bits l), authRaw (departBeforeWrite bits r)) := by
  dsimp only
  unfold authorizedDisappear
  apply authorizedReconcile_authRaw
  simpa only using (terminal_disappear_raw hwidth bits)

/-- Action-one COMPARE executes, but false authorization plus a positive
nonzero ACK label leaves the complete pair unchanged. -/
private theorem terminal_compare (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    authorizedCompareSigActionOne (by omega)
      (authRaw (ackRaw bits l)) (authRaw (departBeforeWrite bits r)) =
      (authRaw (ackRaw bits l), authRaw (departBeforeWrite bits r)) := by
  dsimp only
  have hsucc : psi - 2 = Nat.succ (psi - 3) := by omega
  have hlpos : 0 < psi - 2 := by omega
  have hrpos : 0 < psi - 1 := by omega
  have hl0 : psi - 2 ≠ 0 := by omega
  have hr0 : psi - 1 ≠ 0 := by omega
  have hlt : psi - 2 ≠ psi - 1 := by omega
  simp [authorizedCompareSigActionOne, compareSigInit, authorizedCmpUpdate,
    freshComparisonStart, comparisonActive, cmpUpdateReturnPriority,
    cmpUpdateSetPath2, compareSigDispatchActionOne,
    authRaw, ackRaw, departBeforeWrite, departRaw, sourcePayload,
    sourceBase, sourcePeace, PeaceView.toState, normalizePermit,
    hsucc, hlpos, hrpos, hl0, hr0, hlt]

private theorem terminal_suppress_raw (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    suppressSigResetKill (by omega)
      (ackRaw bits l) (departBeforeWrite bits r) =
      (ackRaw bits l, departBeforeWrite bits r) := by
  dsimp only
  simp [suppressSigResetKill, suppressSigStart, resetKillComparison,
    suppressSigMoveReset, suppressSigTerminal, suppressSigEcho,
    suppressSigFinish, ackRaw, departBeforeWrite, departRaw,
    sourceBase, sourcePeace, PeaceView.toState]

private theorem terminal_suppress (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    authorizedReconcile (suppressSigResetKill (by omega))
      (authRaw (ackRaw bits l)) (authRaw (departBeforeWrite bits r)) =
      (authRaw (ackRaw bits l), authRaw (departBeforeWrite bits r)) := by
  dsimp only
  apply authorizedReconcile_authRaw
  simpa only using (terminal_suppress_raw hwidth bits)

/-- The actual retained leader-sink collision stage is inert on this
follower/follower, zero-bullet, zero-signal pair. -/
private theorem terminal_collision_raw (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    eliminateLeadersNoCollisionLeaderSink (by omega)
      (ackRaw bits l) (departBeforeWrite bits r) =
      (ackRaw bits l, departBeforeWrite bits r) := by
  dsimp only
  simp [eliminateLeadersNoCollisionLeaderSink,
    eliminateLeadersNoCollisionFire, eliminateLeadersNoCollisionMove,
    eliminateLeadersNoCollisionSignalLeaderSink,
    ackRaw, departBeforeWrite, departRaw,
    sourceBase, sourcePeace, PeaceView.toState] <;> try rfl
  all_goals intro _ <;> rfl

private theorem terminal_collision (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    authorizedReconcile (eliminateLeadersNoCollisionLeaderSink (by omega))
      (authRaw (ackRaw bits l)) (authRaw (departBeforeWrite bits r)) =
      (authRaw (ackRaw bits l), authRaw (departBeforeWrite bits r)) := by
  dsimp only
  apply authorizedReconcile_authRaw
  simpa only using (terminal_collision_raw hwidth bits)

/-- WRITE preparation is exact identity; neither endpoint has path3/write
control, and both are followers. -/
private theorem terminal_write_prepare (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    writeSeqThroughPrepare (by omega)
      (ackRaw bits l) (departBeforeWrite bits r) =
      (ackRaw bits l, departBeforeWrite bits r) := by
  dsimp only
  simp [writeSeqThroughPrepare, writeSeqLeaderMove, groupInfo,
    writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqSetWriteReady, writeSeqCompare, writeSeqCommands,
    writeSeqSetWriteAct, ackRaw, departBeforeWrite, departRaw,
    sourceBase, sourcePeace, PeaceView.toState] <;> omega

/-- Only the ascending WRITE-action branch changes the terminal pair: the
responder writer becomes depart.  MOVE_WSIG then frames every field. -/
private theorem terminal_write_raw (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    writeSeqIncrementGate (by omega)
      (ackRaw bits l) (departBeforeWrite bits r) =
      (ackRaw bits l, departRaw bits r) := by
  dsimp only
  have hlt : psi - 2 < psi - 1 := by omega
  have hr0 : psi - 1 ≠ 0 := by omega
  unfold writeSeqIncrementGate
  have hp := terminal_write_prepare hwidth bits
  dsimp only at hp
  rw [hp]
  simp [gatePreparedIncrement, clearIncrementAction, writeSeqAfterPrepare,
    writeAction, writeActionToState, moveWsig, moveWsigCheckLast,
    moveWsigTransfer, ackRaw, departBeforeWrite, departRaw,
    sourceBase, sourcePeace, PeaceView.toState, hlt, hr0] <;> omega

private theorem terminal_write (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    authorizedReconcile (writeSeqIncrementGate (by omega))
      (authRaw (ackRaw bits l)) (authRaw (departBeforeWrite bits r)) =
      (authRaw (ackRaw bits l), authRaw (departRaw bits r)) := by
  dsimp only
  apply authorizedReconcile_authRaw
  simpa only using (terminal_write_raw hwidth bits)

private theorem terminal_post (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    authorizedPostSuppressLeaderSink (by omega)
      (authRaw (ackRaw bits l)) (authRaw (departBeforeWrite bits r)) =
      (authRaw (ackRaw bits l), authRaw (departRaw bits r)) := by
  dsimp only
  unfold authorizedPostSuppressLeaderSink
  rw [terminal_collision hwidth bits]
  simpa only using (terminal_write hwidth bits)

/-- Exact complete post-CHECK suffix, including retained collision and WRITE. -/
private theorem terminal_suffix (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    actionOneAfterCheckSuffix (by omega)
      (authRaw (ackRaw bits l)) (authRaw (departBeforeWrite bits r)) =
      (authRaw (ackRaw bits l), authRaw (departRaw bits r)) := by
  dsimp only
  unfold actionOneAfterCheckSuffix
  dsimp only
  rw [terminal_disappear hwidth bits]
  dsimp only
  rw [terminal_compare hwidth bits]
  dsimp only
  rw [terminal_suppress hwidth bits]
  dsimp only
  simpa only using (terminal_post hwidth bits)

private theorem terminal_input_open (hwidth : 3 ≤ psi)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    normalizeDeletion (authRaw (preRaw bits l)) = authRaw (preRaw bits l) ∧
    normalizeDeletion (authRaw (preRaw bits r)) = authRaw (preRaw bits r) ∧
    deletionActive (authRaw (preRaw bits l)) = false ∧
    deletionActive (authRaw (preRaw bits r)) = false := by
  dsimp only
  have hl : psi - 2 < psi - 1 := by omega
  have hr : ¬ psi - 1 < psi - 1 := by omega
  simp [normalizeDeletion, deletionActive, pathPresent, authRaw, preRaw,
    sourceBase, sourcePeace, PeaceView.toState, hl, hr]

/-- Terminal bootstrap as a composition of the exact real stage cuts above. -/
theorem terminal_row (hwidth : 3 ≤ psi) (kappa : Nat)
    (bits : Fin psi -> Bool) :
    let l : Fin psi := ⟨psi - 2, by omega⟩
    let r : Fin psi := ⟨psi - 1, by omega⟩
    doneGuardedAuthorizedTransition (by omega) kappa
      (authRaw (preRaw bits l)) (authRaw (preRaw bits r)) =
      (authRaw (ackRaw bits l), authRaw (departRaw bits r)) := by
  classical
  dsimp only
  have ho := terminal_input_open hwidth bits
  have hb := terminal_before_check hwidth kappa bits
  have hc := terminal_check hwidth bits
  have hn := terminal_birth_false hwidth bits
  have hs := terminal_suffix hwidth bits
  dsimp only at ho hb hc hn hs
  unfold doneGuardedAuthorizedTransition
  dsimp only
  rw [ho.1, ho.2.1]
  simp only [ho.2.2.2, ho.2.2.1, Bool.false_eq_true, ↓reduceIte]
  rw [hb, hc, hn]
  simp only [markLeaderBirth, Bool.false_eq_true, ↓reduceIte]
  exact hs

#print axioms BirthGenerationDoneAllWidthProducerPrimitives.departRaw_domain
#print axioms BirthGenerationDoneAllWidthProducerPrimitives.terminal_row

#print axioms BirthGenerationDoneAllWidthProducerPrimitives.sourceBase_domain
#print axioms BirthGenerationDoneAllWidthProducerPrimitives.preRaw_domain
#print axioms BirthGenerationDoneAllWidthProducerPrimitives.ackRaw_domain

end BirthGenerationDoneAllWidthProducerPrimitives
