import Leader.Wu.Birth.ShortDoneDispatcher
import Leader.Wu.Safety.NoCheckBirthConditionTwoProtocol

namespace BirthShortDoneDispatcherTerminalSymbolic

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair PPLLCompleteMultiLeaderCleanup
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
  BirthGenerationControlRepair BirthGenerationDone BirthShortWait
  BirthShortDoneCuts BirthShortDoneDispatcher BirthSigMoveDisposalRepair
  BirthStationaryWrite ExpiringK2Projection K2OutputSafety
  PPLLWriteSeqPersistenceRepair PPLLWriteIncrementGate

set_option autoImplicit false
set_option pp.structureInstances false

variable {psi kappa tau : Nat}

def sourcePeace (j : Fin psi) : PeaceView psi :=
  { leader := false, label := j, shield := false, bullet := 0, signal_B := 0 }

def sourceBase (bits : Fin psi -> Bool) (j : Fin psi) : AgentState psi :=
  { PeaceView.toState (sourcePeace j) with bit := bits j }

def sourcePayload (bits : Fin psi -> Bool) (j : Fin psi) : PathInfo :=
  .some j.val (if bits j then 1 else 0)

def preRaw (bits : Fin psi -> Bool) (j : Fin psi) : AgentState psi :=
  if j.val < psi - 1 then { sourceBase bits j with state := .produce }
  else sourceBase bits j

def ackRaw (bits : Fin psi -> Bool) (j : Fin psi) : AgentState psi :=
  { sourceBase bits j with state := .done, path := sourcePayload bits j, path2 := none, path4 := if 0 < j.val then some (Int.ofNat j.val, 1) else none }

def departRaw (bits : Fin psi -> Bool) (j : Fin psi) : AgentState psi :=
  { sourceBase bits j with state := .depart, wait := true, path := sourcePayload bits j, path2 := none, h_field := decide (j.val = 0), path5 := if 0 < j.val /\ j.val < psi - 1 then some (Int.ofNat j.val, 1) else none, write_state := if j.val = 0 then .none else .depart }

def preWriterDepart (bits : Fin psi -> Bool) (j : Fin psi) : AgentState psi :=
  { departRaw bits j with write_state := .none }

def authRaw (u : AgentState psi) : AuthorizedAgentState psi := ⟨u, false⟩

private def tL (h4 : 4 <= psi) : Fin psi := ⟨psi - 2, by omega⟩
private def tR (h4 : 4 <= psi) : Fin psi := ⟨psi - 1, by omega⟩

private theorem terminal_next (h4 : 4 <= psi) :
    ((psi - 2 + 1) % psi) = psi - 1 := by
  rw [Nat.mod_eq_of_lt] <;> omega

/-! ### Guards on the terminal pair, decided once at `psi = m + 4`

Every proof below substitutes `psi = m + 4`.  The pair labels are then
`m + 2` and `m + 3`, so each stage guard (`label = 0`, `label = psi - 1`,
`psi - 2 < psi - 1`, ...) is a linear fact that `simp`'s arithmetic decides.
With `psi` left symbolic these guards stay open, every stage carries both
branches of each `if`, and the unfolded term grows exponentially (the
previous proofs ran for hours).  The only guards `simp` does not decide by
itself are the integer `path4`/`path5` comparisons, stated here once. -/

private theorem cast_three_ne_neg_one (m : Nat) :
    ((m : Int) + 3 = -1) = False := eq_false (by omega)

private theorem cast_two_ne_neg_one (m : Nat) :
    ((m : Int) + 2 = -1) = False := eq_false (by omega)

private theorem cast_three_eq_succ (m : Nat) :
    ((m : Int) + 3 = (m : Int) + 2 + 1) = True := eq_true (by omega)

private theorem cast_two_eq_pred (m : Nat) :
    ((m : Int) + 2 = (m : Int) + 3 - 1) = True := eq_true (by omega)

/-- A source row is not in deletion, so the deletion normalizer is the identity
and the deletion branch of the metadata dispatcher is not taken. -/
private theorem preRaw_no_deletion (bits : Fin psi -> Bool) (j : Fin psi) :
    normalizeDeletion (authRaw (preRaw bits j)) = authRaw (preRaw bits j) /\
      deletionActive (authRaw (preRaw bits j)) = false := by
  unfold preRaw
  split <;> simp [normalizeDeletion, deletionActive, pathPresent, authRaw,
    sourceBase, sourcePeace, PeaceView.toState]

/-- First changed cut plus CLEAN/ELIMINATE, proved from the actual short row. -/
theorem terminal_generation_exact (h4 : 4 <= psi) (kappa : Nat)
    (bits : Fin psi -> Bool) :
    generationBeforeMoveWidth (ψ := psi) (width := psi - 2)
      (by omega) (by omega) (by omega) kappa
      (authRaw (preRaw bits (tL h4))) (authRaw (preRaw bits (tR h4))) =
    (authRaw (ackRaw bits (tL h4)),
      authRaw (preWriterDepart bits (tR h4))) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, psi = m + 4 := ⟨psi - 4, by omega⟩
  simp [generationBeforeMoveWidth, authorizedPPsiLeaderResetProbeWall,
    pPsiLeaderResetProbeWall, pPsi, authorizedGenCleanWidth,
    genCleanWidth, waitWidth, waitSaturatedPrepare, waitWidthCarry,
    activePair, widthTerminal, waitWidthReset, waitWidthFinish,
    genCleanAfterWait, genSigSaturatedStart, genCleanEmit,
    genCleanPropagate, genSigSaturatedFinish, authorizedCleanSig,
    cleanSig, cleanSigGenConnect, cleanSigStep3, cleanSigStep4,
    cleanSigStep5, cleanSigStep6, cleanSigCleanApply,
    authorizedEliminateSig, eliminateSig, authorizedReconcile,
    reconcilePermit, normalizePermit, authRaw, preRaw, ackRaw,
    preWriterDepart, departRaw, sourcePayload, sourceBase, sourcePeace,
    PeaceView.toState, tL, tR, cast_three_ne_neg_one, cast_two_ne_neg_one,
    cast_three_eq_succ, cast_two_eq_pred]
  all_goals rfl

/-- Current DONE movement/pre-CHECK wall/CHECK preserve the generated ACK. -/
theorem terminal_through_check_exact (h4 : 4 <= psi) (kappa : Nat)
    (bits : Fin psi -> Bool) :
    doneThroughCheckWidth (ψ := psi) (width := psi - 2)
      (by omega) (by omega) (by omega) kappa
      (authRaw (preRaw bits (tL h4))) (authRaw (preRaw bits (tR h4))) =
    (authRaw (ackRaw bits (tL h4)),
      authRaw (preWriterDepart bits (tR h4))) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, psi = m + 4 := ⟨psi - 4, by omega⟩
  unfold doneThroughCheckWidth doneBeforeCheckWidth
  rw [terminal_generation_exact h4 kappa bits]
  simp [authorizedDoneMove, doneCaptureSigMove, sigMoveLeaderPreclear,
    incompleteLeftLeaderBoundary, clearIfLeader, doneTransfers, holdDoneStep1,
    controlTransfers, sigMoveStep2, sigMoveStep3, sigMoveStep4, sigMoveStep5,
    comparisonLeaderWall, BirthSingleUseReleaseRepair.singleUseControlTail,
    BirthSingleUseReleaseRepair.singleUseApplyControl,
    pathMovedRight, stableSuccessor, stableWrap, preCheckResetWall,
    sanitizeAuthorizedPair, sanitizeAuthorizedTerminalEqual,
    unsupportedTerminalEqual, preserveDoneCheck, authRaw, ackRaw,
    preWriterDepart, departRaw, sourcePayload, sourceBase, sourcePeace,
    PeaceView.toState, reconcilePermit, normalizePermit, tL, tR]

/-- The genuine new writer seam, independently symbolic. -/
theorem terminal_stationary_writer_exact (h4 : 4 <= psi)
    (bits : Fin psi -> Bool) :
    stationaryPersistentRaw (by omega)
      (ackRaw bits (tL h4)) (preWriterDepart bits (tR h4)) =
    (ackRaw bits (tL h4), departRaw bits (tR h4)) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, psi = m + 4 := ⟨psi - 4, by omega⟩
  simp [stationaryPersistentRaw, swPersistentThroughPrepare,
    clearInputIncrementPair, clearIncrementAction, groupInfo,
    writeSeqGenerate, writeSeqPrepareTransport, writeSeqReadyTransport,
    writeSeqSetWriteReadyTransport, writeSeqCompare, writeSeqCheckBit,
    writeSeqCommands, writeSeqSetWriteAct, writeSeqFinalR,
    gatePreparedIncrement, writeSeqAfterPrepareComparisonTransport,
    writeActionPreservingComparison, writeActionActivateNonempty,
    writeActionExecutePreservingComparison, writeActionExecutePreservingDepart,
    writeActionPropagateState, moveWsigStopAligned, moveWsigStart,
    moveWsigCheckLast, moveWsigTransferStopAligned,
    moveWsigMoveWritePreservingNonempty, moveWsigLeaderSignal,
    moveWsigSignalMove, moveWsigEchoMove,
    PPLLWriteSeqPersistenceRepair.moveWsigFinishPreservingCommand,
    ackRaw, preWriterDepart,
    departRaw, sourcePayload, sourceBase, sourcePeace, PeaceView.toState,
    tL, tR]

/-- Exact authorized metadata core before finite reification/expiry. -/
theorem terminal_metadata_exact (h4 : 4 <= psi) (kappa : Nat)
    (bits : Fin psi -> Bool) :
    doneMetadataAuthorizedWidth (ψ := psi) (width := psi - 2)
      (by omega) (by omega) (by omega) kappa
      (authRaw (preRaw bits (tL h4))) (authRaw (preRaw bits (tR h4))) =
    (authRaw (ackRaw bits (tL h4)), authRaw (departRaw bits (tR h4))) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, psi = m + 4 := ⟨psi - 4, by omega⟩
  have hl := preRaw_no_deletion bits (tL h4)
  have hr := preRaw_no_deletion bits (tR h4)
  unfold doneMetadataAuthorizedWidth
  simp only [hl.1, hr.1, hl.2, hr.2, Bool.false_eq_true, ↓reduceIte]
  unfold doneOrdinaryMetadataWidth
  rw [terminal_through_check_exact h4 kappa bits]
  -- The writer seam is used in the literal form the stage simp produces.
  have hw := terminal_stationary_writer_exact h4 bits
  simp [ackRaw, preWriterDepart, departRaw, sourcePayload, sourceBase,
    sourcePeace, PeaceView.toState, tL, tR] at hw
  unfold afterCheckMetadataWidth beforeWriteWidth
  simp [authorizedDisappear, disappear, authorizedCompareSigActionOne,
    compareSigInit, authorizedCmpUpdate, freshComparisonStart,
    cmpUpdateReturnPriority, cmpUpdateSetPath2, compareSigDispatchActionOne,
    compareBitActionOne, authorizedSuppressWidth, suppressSigResetKillWidth,
    suppressPrefix, suppressSigStart, resetKillComparison, suppressSigMoveReset,
    shortCountReset, suppressSigTerminal, suppressSigEcho, suppressSigFinish,
    stationaryPersistentAuthorizedRow, authorizedReconcile, reconcilePermit,
    normalizePermit, hw, K2BirthDispatcher.authBirth,
    endpointLeaderBorn, markLeaderBirth, authRaw, preRaw, ackRaw, preWriterDepart,
    departRaw, sourcePayload, sourceBase, sourcePeace, PeaceView.toState,
    tL, tR]

private theorem pre_domains (h4 : 4 <= psi) (bits : Fin psi -> Bool) :
    (preRaw bits (tL h4)).inProtocolDomain kappa /\
      (preRaw bits (tR h4)).inProtocolDomain kappa := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, psi = m + 4 := ⟨psi - 4, by omega⟩
  simp [preRaw, sourceBase, sourcePeace, PeaceView.toState,
    AgentState.inProtocolDomain, PayloadView.ofState, PayloadView.Valid,
    PayloadView.PathValid, PayloadView.Path2Valid,
    PayloadView.CleanPathValid, tL, tR]

private def pack (u : AgentState psi) (hu : u.inProtocolDomain kappa) :
    ExpiringAgentState psi kappa tau :=
  ⟨⟨BoundedAgentState.ofDomain u hu, false⟩, freshStall tau⟩

/-- A packed source row erases to its raw authorized row. -/
private theorem pack_erase (u : AgentState psi) (hu : u.inProtocolDomain kappa) :
    (pack (tau := tau) u hu).core.erase = authRaw u := by
  simp [pack, authRaw, AuthorizedBoundedAgentState.erase,
    BoundedAgentState.erase_ofDomain]

/-- The early terminal-disposal marker does not fire on a source row
(`path2 = none`), so disposal preparation is the identity. -/
private theorem prepare_pack (hpsi : 0 < psi) (bits : Fin psi -> Bool)
    (j : Fin psi) (hu : (preRaw bits j).inProtocolDomain kappa) :
    prepareExpiringDisposal hpsi (pack (tau := tau) (preRaw bits j) hu) =
      pack (preRaw bits j) hu := by
  have hclear : pendingTerminalDisposal hpsi (preRaw bits j) = false := by
    unfold preRaw
    split <;> simp [pendingTerminalDisposal, sourceBase, sourcePeace,
      PeaceView.toState]
  have hprep : prepareDisposal hpsi ⟨preRaw bits j, false⟩ =
      ⟨preRaw bits j, false⟩ :=
    prepareDisposal_eq_of_clear hpsi _ hclear
  unfold prepareExpiringDisposal prepareBoundedDisposal
  simp only [pack_erase, authRaw, hprep]
  rfl

/-- Source-row expiry: a row whose path location changed and that is not in
deletion gets a fresh stall budget and is otherwise kept. -/
private theorem expire_source (u v : AgentState psi)
    (hu : u.inProtocolDomain kappa) (hv : v.inProtocolDomain kappa)
    (s : Fin (tau + 1))
    (hdel : deletionActive (authRaw v) = false) (hpath : v.path ≠ u.path) :
    deletionPriorityExpireOne tau (pack u hu)
        ⟨⟨BoundedAgentState.ofDomain v hv, false⟩, s⟩ =
      ⟨⟨BoundedAgentState.ofDomain v hv, false⟩, freshStall tau⟩ := by
  have hne :
      PathProgressView.ofState
          (⟨BoundedAgentState.ofDomain v hv, false⟩ :
            AuthorizedBoundedAgentState psi kappa) ≠
        PathProgressView.ofState (pack (tau := tau) u hu).core := by
    intro h
    apply hpath
    have hp : (BoundedAgentState.ofDomain v hv).path =
        (BoundedAgentState.ofDomain (κ := kappa) u hu).path :=
      congrArg PathProgressView.path h
    have he : (BoundedAgentState.erase (BoundedAgentState.ofDomain v hv)).path =
        (BoundedAgentState.erase
          (BoundedAgentState.ofDomain (κ := kappa) u hu)).path := by
      simp only [BoundedAgentState.erase, hp]
    rw [BoundedAgentState.erase_ofDomain, BoundedAgentState.erase_ofDomain] at he
    exact he
  have hdel' : deletionActive
      (⟨BoundedAgentState.ofDomain v hv, false⟩ :
        AuthorizedBoundedAgentState psi kappa).erase = false := by
    simpa [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain,
      authRaw] using hdel
  unfold deletionPriorityExpireOne pathExpireOne
  simp only [hdel', hne, Bool.false_eq_true, ↓reduceIte, ne_eq,
    not_false_eq_true]

/-- The K2 view of a cell with no leader, shield, bullet or signal. -/
private def quietView : AgentState 1 :=
  PeaceView.toState ⟨false, 0, false, 0, 0⟩

/-- The K2 kernel fixes two quiet views (one closed evaluation on `AgentState 1`). -/
private theorem kernel_quiet :
    LDSinkKernelC.sinkKernelC (ψ := 1) (by decide) quietView quietView =
      (quietView, quietView) := by
  decide

private theorem observe_quiet (v : AgentState psi)
    (hv : v.inProtocolDomain kappa) (c : Bool) (s : Fin (tau + 1))
    (hl : v.leader = false) (hs : v.shield = false) (hb : v.bullet = 0)
    (hB : v.signal_B = 0) :
    ExpiringK2Projection.observeCell
        (⟨⟨BoundedAgentState.ofDomain v hv, c⟩, s⟩ :
          ExpiringAgentState psi kappa tau) = quietView := by
  unfold ExpiringK2Projection.observeCell K2OutputSafety.signalView quietView
  simp only [BoundedAgentState.erase_ofDomain, hl, hs, hb, hB]

private theorem leader_of_quiet (q : ExpiringAgentState psi kappa tau)
    (h : ExpiringK2Projection.observeCell q = quietView) :
    q.core.core.leader = false := by
  have hq := congrArg AgentState.leader h
  exact hq

/-- Quiet cells pass the K2 row unchanged: the kernel fixes their view and
restoring a cell's own view is the identity. -/
private theorem k2_row_quiet (hpsi : 0 < psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : ExpiringK2Projection.observeCell l = quietView)
    (hr : ExpiringK2Projection.observeCell r = quietView) :
    ExpiringK2Projection.row hpsi l r = (l, r) := by
  have h1 : ExpiringK2Projection.putSignals l quietView = l := by
    rw [← hl]
    exact ExpiringK2Projection.putSignals_self l
  have h2 : ExpiringK2Projection.putSignals r quietView = r := by
    rw [← hr]
    exact ExpiringK2Projection.putSignals_self r
  unfold ExpiringK2Projection.row
  simp only [hl, hr, kernel_quiet, h1, h2]

/-- With no birth and no leader, the final physical tail is the identity on
quiet metadata outputs. -/
private theorem final_quiet (hpsi : 0 < psi)
    (oldL oldR ml mr : ExpiringAgentState psi kappa tau)
    (hl : ExpiringK2Projection.observeCell ml = quietView)
    (hr : ExpiringK2Projection.observeCell mr = quietView) :
    K2BirthDispatcher.finalPhysical hpsi oldL oldR ml mr = (ml, mr) := by
  have hml := leader_of_quiet ml hl
  have hmr := leader_of_quiet mr hr
  rw [K2BirthDispatcher.finalPhysical_of_no_birth hpsi oldL oldR ml mr
      (by simp [K2BirthDispatcher.newborn, hml])
      (by simp [K2BirthDispatcher.newborn, hmr]),
    K2BirthDispatcher.collisionRow_of_not_both hpsi ml mr (by simp [hml]),
    k2_row_quiet hpsi ml mr hl hr]

private theorem normalize_quiet (hpsi : 0 < psi)
    (q : ExpiringAgentState psi kappa tau)
    (h : ExpiringK2Projection.observeCell q = quietView) :
    K2BirthLeaderNormalize.normalizeLeader hpsi q = q := by
  have hq := leader_of_quiet q h
  unfold K2BirthLeaderNormalize.normalizeLeader
  simp [hq]

/-- The whole physical tail on two quiet metadata outputs with fresh stalls:
leader normalization and the K2/collision row leave both cells unchanged. -/
private theorem tail_quiet (hpsi : 0 < psi)
    (oldL oldR : ExpiringAgentState psi kappa tau) (v w : AgentState psi)
    (hv : v.inProtocolDomain kappa) (hw : w.inProtocolDomain kappa)
    (hvl : v.leader = false) (hvs : v.shield = false) (hvb : v.bullet = 0)
    (hvB : v.signal_B = 0)
    (hwl : w.leader = false) (hws : w.shield = false) (hwb : w.bullet = 0)
    (hwB : w.signal_B = 0) :
    K2BirthDispatcher.finalPhysical hpsi oldL oldR
        (K2BirthLeaderNormalize.normalizeLeader hpsi
          ⟨⟨BoundedAgentState.ofDomain v hv, false⟩, freshStall tau⟩)
        (K2BirthLeaderNormalize.normalizeLeader hpsi
          ⟨⟨BoundedAgentState.ofDomain w hw, false⟩, freshStall tau⟩) =
      (⟨⟨BoundedAgentState.ofDomain v hv, false⟩, freshStall tau⟩,
        ⟨⟨BoundedAgentState.ofDomain w hw, false⟩, freshStall tau⟩) := by
  have ov := observe_quiet v hv false (freshStall tau) hvl hvs hvb hvB
  have ow := observe_quiet w hw false (freshStall tau) hwl hws hwb hwB
  rw [normalize_quiet hpsi _ ov, normalize_quiet hpsi _ ow,
    final_quiet hpsi oldL oldR _ _ ov ow]

/-- The terminal outputs carry no leader, shield, bullet or signal. -/
private theorem ackRaw_quiet (bits : Fin psi -> Bool) (j : Fin psi) :
    (ackRaw bits j).leader = false /\ (ackRaw bits j).shield = false /\
      (ackRaw bits j).bullet = 0 /\ (ackRaw bits j).signal_B = 0 := by
  simp [ackRaw, sourceBase, sourcePeace, PeaceView.toState]

private theorem departRaw_quiet (bits : Fin psi -> Bool) (j : Fin psi) :
    (departRaw bits j).leader = false /\ (departRaw bits j).shield = false /\
      (departRaw bits j).bullet = 0 /\ (departRaw bits j).signal_B = 0 := by
  simp [departRaw, sourceBase, sourcePeace, PeaceView.toState]

/-- Complete actual short dispatcher terminal row.  No no-birth or lifespan
premise: both are decided by these source records. -/
theorem terminal_actual_row (h4 : 4 <= psi) (kappa tau : Nat)
    (bits : Fin psi -> Bool) :
    let hd := pre_domains (kappa := kappa) h4 bits
    let l := pack (tau := tau) (preRaw bits (tL h4)) hd.1
    let r := pack (tau := tau) (preRaw bits (tR h4)) hd.2
    let q := BirthShortDoneDispatcher.row
      (ψ := psi) (width := psi - 2) (κ := kappa) (τ := tau)
      (by omega) (by omega) (by omega) l r
    q.1.core.erase = authRaw (ackRaw bits (tL h4)) /\
      q.1.stall = freshStall tau /\
      q.2.core.erase = authRaw (departRaw bits (tR h4)) /\
      q.2.stall = freshStall tau := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, psi = m + 4 := ⟨psi - 4, by omega⟩
  simp only [BirthShortDoneDispatcher.row, BirthShortDoneDispatcher.metadata,
    BirthShortDoneCuts.doneMetadataWidth,
    BirthShortDoneCuts.doneMetadataBoundedWidth, prepare_pack, pack_erase,
    terminal_metadata_exact h4 kappa bits]
  simp only [authRaw]
  have hpL : (ackRaw bits (tL h4)).path ≠ (preRaw bits (tL h4)).path := by
    simp [ackRaw, preRaw, sourcePayload, sourceBase, sourcePeace,
      PeaceView.toState, tL]
  have hpR : (departRaw bits (tR h4)).path ≠ (preRaw bits (tR h4)).path := by
    simp [departRaw, preRaw, sourcePayload, sourceBase, sourcePeace,
      PeaceView.toState, tR]
  have hdL : deletionActive (authRaw (ackRaw bits (tL h4))) = false := by
    simp [deletionActive, authRaw, ackRaw]
  have hdR : deletionActive (authRaw (departRaw bits (tR h4))) = false := by
    simp [deletionActive, authRaw, departRaw]
  rw [expire_source _ _ _ _ _ hdL hpL, expire_source _ _ _ _ _ hdR hpR]
  have qa := ackRaw_quiet bits (tL h4)
  have qd := departRaw_quiet bits (tR h4)
  rw [tail_quiet _ _ _ _ _ _ _ qa.1 qa.2.1 qa.2.2.1 qa.2.2.2
    qd.1 qd.2.1 qd.2.2.1 qd.2.2.2]
  simp [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]

#print axioms terminal_generation_exact
#print axioms terminal_through_check_exact
#print axioms terminal_stationary_writer_exact
#print axioms terminal_metadata_exact
#print axioms terminal_actual_row

end BirthShortDoneDispatcherTerminalSymbolic
