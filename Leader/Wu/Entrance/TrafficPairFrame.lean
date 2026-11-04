import Leader.Wu.Entrance.EnvelopeHostLaws

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6TrafficPairFrame

open PPLL PPLLRepair
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepNormalResetContract PPLLWallSweepPreCheckResetRepair
  PPLLCompleteMultiLeaderCleanup
open BirthShortWait BirthShortDoneCuts BirthShortDoneTerminalEntryCut
  BirthStationaryWrite K2BirthDispatcher K2BirthLeaderNormalize
  ExpiringK2Projection
open BirthCheckPermitRepair

variable {psi width kappa tau : Nat}

/-- Algorithm 14 cannot bootstrap reset/echo traffic from a follower initiator
and a pair whose reset/echo bits are all zero. -/
theorem suppressWidth_resetEcho_zero
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi)
    (hlLeader : l.leader = false)
    (hlReset : l.reset_cmd = false) (hlEcho : l.echo = false)
    (hrReset : r.reset_cmd = false) (hrEcho : r.echo = false) :
    let q := suppressSigResetKillWidth hpsi hwidth hle l r
    q.1.reset_cmd = false ∧ q.1.echo = false ∧
      q.2.reset_cmd = false ∧ q.2.echo = false := by
  simp [suppressSigResetKillWidth, suppressPrefix, suppressSigStart,
    resetKillComparison, suppressSigMoveReset, shortCountReset,
    suppressSigTerminal, suppressSigEcho, suppressSigFinish,
    hlLeader, hlReset, hlEcho, hrReset, hrEcho]

/-- Authorization reconciliation changes only the permit wrapper, so the raw
SUPPRESS result above lifts literally. -/
theorem authorizedSuppressWidth_resetEcho_zero
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = false)
    (hlReset : l.core.reset_cmd = false) (hlEcho : l.core.echo = false)
    (hrReset : r.core.reset_cmd = false) (hrEcho : r.core.echo = false) :
    let q := authorizedSuppressWidth hpsi hwidth hle l r
    q.1.core.reset_cmd = false ∧ q.1.core.echo = false ∧
      q.2.core.reset_cmd = false ∧ q.2.core.echo = false := by
  unfold authorizedSuppressWidth authorizedReconcile
  dsimp only
  exact suppressWidth_resetEcho_zero hpsi hwidth hle l.core r.core
    hlLeader hlReset hlEcho hrReset hrEcho

/-- `permitFix` changes only the authorization bit. -/
theorem permitFix_resetEcho_frame (c : AuthorizedAgentState psi) :
    (permitFix c).core.reset_cmd = c.core.reset_cmd ∧
      (permitFix c).core.echo = c.core.echo := by
  rw [permitFix_core]
  exact ⟨rfl, rfl⟩

/-- Existing CHECK projection, repackaged at the exact field family used here. -/
theorem check_resetEcho_frame
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedCheckSig hpsi l r) =
      authorizedResetEchoPair (l, r) :=
  PPLLWallSweepNormalResetContract.authorizedCheckSig_resetEchoPair hpsi l r

/-- Existing DISAPPEAR projection. -/
theorem disappear_resetEcho_frame
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedDisappear hpsi l r) =
      authorizedResetEchoPair (l, r) :=
  PPLLWallSweepNormalResetContract.authorizedDisappear_resetEchoPair hpsi l r

/-- Existing action-one COMPARE projection used by the real ordinary row. -/
theorem compareActionOne_resetEcho_frame
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair
        (authorizedCompareSigActionOne hpsi l r) =
      authorizedResetEchoPair (l, r) :=
  PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne_resetEchoPair
    hpsi l r

/-- The earlier deletion normalization does not move reset/echo traffic. -/
theorem normalizeDeletion_resetEcho_frame
    (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (normalizeDeletion l, normalizeDeletion r) =
      authorizedResetEchoPair (l, r) :=
  PPLLWallSweepNormalResetContract.normalizeDeletionPair_resetEcho l r

/-- The responder-deletion branch of `BirthCheckPermitRepair.authorized` also
frames reset/echo.  This is the private wall-contract proof specialized again
locally so this file does not depend on a private declaration. -/
theorem authorizedEliminate_resetEcho_frame
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (authorizedEliminateSig hpsi l r) =
      authorizedResetEchoPair (l, r) := by
  change resetEchoPair (eliminateSig hpsi l.core r.core) =
    resetEchoPair (l.core, r.core)
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold resetEchoPair resetEchoView eliminateSig
    try dsimp only
    repeat (first | rfl | split)

/-- Birth marking changes comparison state/permission only. -/
theorem markLeaderBirth_resetEcho_frame
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedResetEchoPair (markLeaderBirth born q) =
      authorizedResetEchoPair q := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold authorizedResetEchoPair resetEchoPair resetEchoView
      markLeaderBirth markComparisonForDeletion
    try dsimp only
    repeat (first | rfl | split)


open PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair

/-- Physical Algorithm-14 `echo` only; deliberately distinct from Algorithm-20
`ws_echo`. -/
private def writerEchoPair
    (q : AgentState psi × AgentState psi) : Bool × Bool :=
  (q.1.echo, q.2.echo)

private theorem writerEchoPair_fst
    (q : AgentState psi × AgentState psi) :
    (writerEchoPair q).1 = q.1.echo := rfl

private theorem writerEchoPair_snd
    (q : AgentState psi × AgentState psi) :
    (writerEchoPair q).2 = q.2.echo := rfl

/-! ## Persistent writer preparation -/

private theorem clearIncrementAction_echo_frame (u : AgentState psi) :
    (clearIncrementAction u).echo = u.echo := by
  unfold clearIncrementAction
  split <;> rfl

private theorem clearInputIncrementPair_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (clearInputIncrementPair l r) =
      writerEchoPair (l, r) := by
  unfold clearInputIncrementPair writerEchoPair
  exact Prod.ext (clearIncrementAction_echo_frame l)
    (clearIncrementAction_echo_frame r)

private theorem groupInfoStart_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (groupInfoStart hpsi l r) =
      writerEchoPair (l, r) := by
  apply Prod.ext
  all_goals
    unfold writerEchoPair groupInfoStart
    try dsimp only
    repeat (first | rfl | split)

private theorem groupInfoSet_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (groupInfoSet hpsi l r) =
      writerEchoPair (l, r) := by
  apply Prod.ext
  all_goals
    unfold writerEchoPair groupInfoSet
    try dsimp only
    repeat (first | rfl | split)

private theorem groupInfoUnset_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (groupInfoUnset l r) = writerEchoPair (l, r) := by
  apply Prod.ext
  all_goals
    unfold writerEchoPair groupInfoUnset
    try dsimp only
    repeat (first | rfl | split)

private theorem groupInfo_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (groupInfo hpsi l r) = writerEchoPair (l, r) := by
  rw [groupInfo_eq_staged]
  let q0 := groupInfoStart hpsi l r
  let q1 := groupInfoSet hpsi q0.1 q0.2
  exact (groupInfoUnset_echo_frame q1.1 q1.2).trans
    ((groupInfoSet_echo_frame hpsi q0.1 q0.2).trans
      (groupInfoStart_echo_frame hpsi l r))

private theorem gensigWriteseqStart_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (gensigWriteseqStart hpsi l r) =
      writerEchoPair (l, r) := by
  apply Prod.ext
  all_goals
    unfold writerEchoPair gensigWriteseqStart
    try dsimp only
    repeat (first | rfl | split)

private theorem gensigWriteseqEmit_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (gensigWriteseqEmit hpsi l r) =
      writerEchoPair (l, r) := by
  apply Prod.ext
  all_goals
    unfold writerEchoPair gensigWriteseqEmit
    try dsimp only
    repeat (first | rfl | split)

private theorem gensigWriteseqPropagate_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (gensigWriteseqPropagate hpsi l r) =
      writerEchoPair (l, r) := by
  apply Prod.ext
  all_goals
    unfold writerEchoPair gensigWriteseqPropagate
    try dsimp only
    repeat (first | rfl | split)

private theorem gensigWriteseqFinish_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (gensigWriteseqFinish hpsi l r) =
      writerEchoPair (l, r) := by
  apply Prod.ext
  all_goals
    unfold writerEchoPair gensigWriteseqFinish
    try dsimp only
    repeat (first | rfl | split)

private theorem gensigWriteseq_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (gensigWriteseq hpsi l r) = writerEchoPair (l, r) := by
  rw [gensigWriteseq_eq_staged]
  let q0 := gensigWriteseqStart hpsi l r
  let q1 := gensigWriteseqEmit hpsi q0.1 q0.2
  let q2 := gensigWriteseqPropagate hpsi q1.1 q1.2
  exact (gensigWriteseqFinish_echo_frame hpsi q2.1 q2.2).trans
    ((gensigWriteseqPropagate_echo_frame hpsi q1.1 q1.2).trans
      ((gensigWriteseqEmit_echo_frame hpsi q0.1 q0.2).trans
        (gensigWriteseqStart_echo_frame hpsi l r)))

private theorem writeSeqGenerate_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (writeSeqGenerate hpsi l r) = writerEchoPair (l, r) := by
  unfold writeSeqGenerate
  split
  · exact gensigWriteseq_echo_frame hpsi l r
  · rfl

private theorem writeSeqSetWriteReadyTransport_echo_frame
    (u : AgentState psi) :
    (writeSeqSetWriteReadyTransport u).echo = u.echo := by
  unfold writeSeqSetWriteReadyTransport
  try dsimp only
  repeat (first | rfl | split)

private theorem writeSeqReadyTransport_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (writeSeqReadyTransport l r) = writerEchoPair (l, r) := by
  unfold writeSeqReadyTransport writerEchoPair
  exact Prod.ext (writeSeqSetWriteReadyTransport_echo_frame l)
    (writeSeqSetWriteReadyTransport_echo_frame r)

private theorem writeSeqCompare_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (writeSeqCompare hpsi l r) = writerEchoPair (l, r) := by
  apply Prod.ext
  all_goals
    unfold writerEchoPair writeSeqCompare writeSeqCheckBit
    try dsimp only
    repeat (first | rfl | split)

private theorem writeSeqCommands_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (writeSeqCommands hpsi l r) = writerEchoPair (l, r) := by
  apply Prod.ext
  all_goals
    unfold writerEchoPair writeSeqCommands writeSeqSetWriteAct writeSeqFinalR
    try dsimp only
    repeat (first | rfl | split)

private theorem writeSeqPrepareTransport_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (writeSeqPrepareTransport hpsi l r) =
      writerEchoPair (l, r) := by
  let q0 := writeSeqReadyTransport l r
  let q1 := writeSeqCompare hpsi q0.1 q0.2
  exact (writeSeqCommands_echo_frame hpsi q1.1 q1.2).trans
    ((writeSeqCompare_echo_frame hpsi q0.1 q0.2).trans
      (writeSeqReadyTransport_echo_frame l r))

private theorem swPersistentThroughPrepare_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (swPersistentThroughPrepare hpsi l r) =
      writerEchoPair (l, r) := by
  let q0 := clearInputIncrementPair l r
  let q1 := groupInfo hpsi q0.1 q0.2
  let q2 := writeSeqGenerate hpsi q1.1 q1.2
  exact (writeSeqPrepareTransport_echo_frame hpsi q2.1 q2.2).trans
    ((writeSeqGenerate_echo_frame hpsi q1.1 q1.2).trans
      ((groupInfo_echo_frame hpsi q0.1 q0.2).trans
        (clearInputIncrementPair_echo_frame l r)))

private theorem gatePreparedIncrement_echo_frame (u : AgentState psi) :
    (gatePreparedIncrement u).echo = u.echo := by
  unfold gatePreparedIncrement
  repeat (first | exact clearIncrementAction_echo_frame u | rfl | split)

/-! ## Persistent Algorithm 19 action -/

private theorem writeActionActivateNonempty_echo_frame
    (hpsi : 0 < psi) (u : AgentState psi) :
    (writeActionActivateNonempty hpsi u).echo = u.echo := by
  unfold writeActionActivateNonempty
  split <;> rfl

private theorem writeActionApplyOverwrite_echo_frame (u : AgentState psi) :
    (writeActionApplyOverwrite u).echo = u.echo := by
  unfold writeActionApplyOverwrite
  cases u.path3 <;> rfl

private theorem writeActionApplyMoveFlip_echo_frame (u : AgentState psi) :
    (writeActionApplyMoveFlip u).echo = u.echo := by
  unfold writeActionApplyMoveFlip
  cases u.path3 <;> rfl

private theorem writeActionApplyIncrementAndFlip_echo_frame
    (u : AgentState psi) :
    (writeActionApplyIncrementAndFlip u).echo = u.echo := by
  unfold writeActionApplyIncrementAndFlip
  try dsimp only
  repeat (first | rfl | split)

private theorem writeActionPropagateState_echo_frame
    (u : AgentState psi) (s : WriteState) :
    (writeActionPropagateState u s).echo = u.echo := by
  cases s <;> rfl

private theorem writerEchoIte (p : Prop) [Decidable p]
    (u v : AgentState psi) :
    (if p then u else v).echo = if p then u.echo else v.echo := by
  split <;> rfl

private theorem setWriteState_echo (u : AgentState psi) (s : WriteState) :
    ({ u with write_state := s }).echo = u.echo := rfl

private theorem writeActionExecutePreservingDepart_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (writeActionExecutePreservingDepart hpsi l r) =
      writerEchoPair (l, r) := by
  unfold writeActionExecutePreservingDepart
  split
  · simp only [writerEchoPair, writerEchoIte, setWriteState_echo,
      writeActionApplyOverwrite_echo_frame,
      writeActionApplyMoveFlip_echo_frame,
      writeActionApplyIncrementAndFlip_echo_frame,
      writeActionPropagateState_echo_frame, ite_self]
  · rfl

private theorem writeActionExecutePreservingComparison_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (writeActionExecutePreservingComparison hpsi l r) =
      writerEchoPair (l, r) := by
  unfold writeActionExecutePreservingComparison
  split
  · rfl
  · exact writeActionExecutePreservingDepart_echo_frame hpsi l r

private theorem writeActionPreservingComparison_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (writeActionPreservingComparison hpsi l r) =
      writerEchoPair (l, r) := by
  exact
    (writeActionExecutePreservingComparison_echo_frame hpsi
      (writeActionActivateNonempty hpsi l)
      (writeActionActivateNonempty hpsi r)).trans
      (Prod.ext (writeActionActivateNonempty_echo_frame hpsi l)
        (writeActionActivateNonempty_echo_frame hpsi r))

/-! ## Persistent Algorithm 20 movement -/

private theorem moveWsigStart_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (moveWsigStart l r) = writerEchoPair (l, r) := by
  apply Prod.ext
  all_goals
    unfold writerEchoPair moveWsigStart moveWsigCheckGenWs
    try dsimp only
    repeat (first | rfl | split)

private theorem moveWsigCheckLast_echo_frame (u : AgentState psi) :
    (moveWsigCheckLast u).echo = u.echo := by
  unfold moveWsigCheckLast
  try dsimp only
  repeat (first | rfl | split)

private theorem moveWsigTransferStopAligned_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (moveWsigTransferStopAligned l r) =
      writerEchoPair (l, r) := by
  apply Prod.ext
  all_goals
    unfold writerEchoPair moveWsigTransferStopAligned
    try dsimp only
    repeat (first | rfl | split)

private theorem moveWsigMoveWritePreservingNonempty_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (moveWsigMoveWritePreservingNonempty l r) =
      writerEchoPair (l, r) := by
  unfold writerEchoPair moveWsigMoveWritePreservingNonempty
  split <;> rfl

private theorem moveWsigLeaderSignal_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (moveWsigLeaderSignal l r) = writerEchoPair (l, r) := by
  unfold writerEchoPair moveWsigLeaderSignal
  split <;> rfl

private theorem moveWsigSignalMove_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (moveWsigSignalMove l r) = writerEchoPair (l, r) := by
  apply Prod.ext
  all_goals
    unfold writerEchoPair moveWsigSignalMove
    try dsimp only
    repeat (first | rfl | split)

private theorem moveWsigEchoMove_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (moveWsigEchoMove l r) = writerEchoPair (l, r) := by
  apply Prod.ext
  all_goals
    unfold writerEchoPair moveWsigEchoMove
    try dsimp only
    repeat (first | rfl | split)

private theorem moveWsigStopAligned_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (moveWsigStopAligned hpsi l r) =
      writerEchoPair (l, r) := by
  let q0 := moveWsigStart l r
  let q1 := (moveWsigCheckLast q0.1, q0.2)
  let q2 := moveWsigTransferStopAligned q1.1 q1.2
  let q3 := moveWsigMoveWritePreservingNonempty q2.1 q2.2
  let q4 := moveWsigLeaderSignal q3.1 q3.2
  let q5 := moveWsigSignalMove q4.1 q4.2
  have h1 : writerEchoPair q1 = writerEchoPair q0 :=
    Prod.ext (moveWsigCheckLast_echo_frame q0.1) rfl
  exact (moveWsigEchoMove_echo_frame q5.1 q5.2).trans
    ((moveWsigSignalMove_echo_frame q4.1 q4.2).trans
      ((moveWsigLeaderSignal_echo_frame q3.1 q3.2).trans
        ((moveWsigMoveWritePreservingNonempty_echo_frame q2.1 q2.2).trans
          ((moveWsigTransferStopAligned_echo_frame q1.1 q1.2).trans
            (h1.trans (moveWsigStart_echo_frame l r))))))

private theorem writeSeqAfterPrepareComparisonTransport_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (writeSeqAfterPrepareComparisonTransport hpsi l r) =
      writerEchoPair (l, r) := by
  let q := writeActionPreservingComparison hpsi l r
  exact (moveWsigStopAligned_echo_frame hpsi q.1 q.2).trans
    (writeActionPreservingComparison_echo_frame hpsi l r)

private theorem stationaryPersistentRaw_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (stationaryPersistentRaw hpsi l r) =
      writerEchoPair (l, r) := by
  let q := swPersistentThroughPrepare hpsi l r
  let g := (gatePreparedIncrement q.1, gatePreparedIncrement q.2)
  have hg : writerEchoPair g = writerEchoPair q :=
    Prod.ext (gatePreparedIncrement_echo_frame q.1)
      (gatePreparedIncrement_echo_frame q.2)
  exact (writeSeqAfterPrepareComparisonTransport_echo_frame
      hpsi g.1 g.2).trans
    (hg.trans (swPersistentThroughPrepare_echo_frame hpsi l r))

/-- Missing seam: the stationary persistent writer never touches the
physical Algorithm-14 `echo` bit on either endpoint. -/
theorem stationaryPersistentAuthorizedRow_echo_frame
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    (stationaryPersistentAuthorizedRow hpsi l r).1.core.echo = l.core.echo ∧
      (stationaryPersistentAuthorizedRow hpsi l r).2.core.echo = r.core.echo := by
  have hc := stationaryPersistentAuthorizedRow_core hpsi l r
  have he := congrArg
    (fun q : AgentState psi × AgentState psi => writerEchoPair q) hc
  have hraw := stationaryPersistentRaw_echo_frame hpsi l.core r.core
  have h := he.trans hraw
  have hL := congrArg Prod.fst h
  have hR := congrArg Prod.snd h
  exact ⟨
    by simpa only [writerEchoPair_fst] using hL,
    by simpa only [writerEchoPair_snd] using hR⟩


open BirthGenerationDone BirthArrivalCaptureRepair
  BirthSingleUseReleaseRepair BirthTossCheckPreservationRepair
  BirthCheckCongestGuardRepair

private def authorizedEchoPair
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Bool × Bool :=
  (q.1.core.echo, q.2.core.echo)

private theorem authorizedEchoPair_fst
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (authorizedEchoPair q).1 = q.1.core.echo := rfl

private theorem authorizedEchoPair_snd
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (authorizedEchoPair q).2 = q.2.core.echo := rfl

private def authResetEchoZero
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop :=
  q.1.core.reset_cmd = false ∧ q.1.core.echo = false ∧
    q.2.core.reset_cmd = false ∧ q.2.core.echo = false

private def boundedResetEchoZero
    (q : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa) : Prop :=
  q.1.erase.core.reset_cmd = false ∧ q.1.erase.core.echo = false ∧
    q.2.erase.core.reset_cmd = false ∧ q.2.erase.core.echo = false

private def physResetEchoZero
    (q : ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau) : Prop :=
  q.1.core.erase.core.reset_cmd = false ∧
    q.1.core.erase.core.echo = false ∧
    q.2.core.erase.core.reset_cmd = false ∧
    q.2.core.erase.core.echo = false

private def echoE (q : ExpiringAgentState psi kappa tau) : Bool :=
  q.core.erase.core.echo

private theorem authorizedEchoPair_of_resetEchoPair_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedResetEchoPair a = authorizedResetEchoPair b) :
    authorizedEchoPair a = authorizedEchoPair b := by
  have hp := congrArg
    (fun z : (Bool × Bool) × (Bool × Bool) => (z.1.2, z.2.2)) h
  simpa only [authorizedEchoPair, authorizedResetEchoPair,
    resetEchoPair, resetEchoView] using hp

private theorem resetEcho_left_reset
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedResetEchoPair a = authorizedResetEchoPair b) :
    a.1.core.reset_cmd = b.1.core.reset_cmd := by
  have hp := congrArg
    (fun z : (Bool × Bool) × (Bool × Bool) => z.1.1) h
  simpa only [authorizedResetEchoPair, resetEchoPair, resetEchoView] using hp

private theorem resetEcho_left_echo
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedResetEchoPair a = authorizedResetEchoPair b) :
    a.1.core.echo = b.1.core.echo := by
  have hp := congrArg
    (fun z : (Bool × Bool) × (Bool × Bool) => z.1.2) h
  simpa only [authorizedResetEchoPair, resetEchoPair, resetEchoView] using hp

private theorem resetEcho_right_reset
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedResetEchoPair a = authorizedResetEchoPair b) :
    a.2.core.reset_cmd = b.2.core.reset_cmd := by
  have hp := congrArg
    (fun z : (Bool × Bool) × (Bool × Bool) => z.2.1) h
  simpa only [authorizedResetEchoPair, resetEchoPair, resetEchoView] using hp

private theorem resetEcho_right_echo
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedResetEchoPair a = authorizedResetEchoPair b) :
    a.2.core.echo = b.2.core.echo := by
  have hp := congrArg
    (fun z : (Bool × Bool) × (Bool × Bool) => z.2.2) h
  simpa only [authorizedResetEchoPair, resetEchoPair, resetEchoView] using hp

private theorem authorizedReconcile_echo_frame
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (hf : ∀ l r, writerEchoPair (f l r) = writerEchoPair (l, r))
    (l r : AuthorizedAgentState psi) :
    authorizedEchoPair (authorizedReconcile f l r) =
      authorizedEchoPair (l, r) := by
  have hc := BirthB1InnerCountFrames.authorizedReconcile_core f l r
  unfold authorizedEchoPair
  rw [hc.1, hc.2]
  simpa only [writerEchoPair] using hf l.core r.core

/-! The missing pre-CHECK echo leaf.  These are the same raw one-stage
projections used by the compiled scar-prefix proof, specialized to `echo`. -/

private theorem r1_pprimeRaw_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (pPsiLeaderResetProbeWall hpsi l r) =
      writerEchoPair (l, r) := by
  apply Prod.ext
  all_goals
    unfold writerEchoPair pPsiLeaderResetProbeWall pPsi
    try dsimp only
    repeat (first | rfl | split)


private theorem r1_waitPrepare_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (waitSaturatedPrepare hpsi l r) =
      writerEchoPair (l, r) := by
  unfold writerEchoPair waitSaturatedPrepare
  dsimp only
  repeat (first | rfl | split)

private theorem r1_waitClear_echo_frame
    (hwidth : 0 < width) (hle : width ≤ psi) (l r : AgentState psi) :
    writerEchoPair
        (BirthShortWaitTerminalEntryRepair.terminalInactiveClear
          hwidth hle l r) =
      writerEchoPair (l, r) := by
  unfold writerEchoPair
    BirthShortWaitTerminalEntryRepair.terminalInactiveClear
  repeat (first | rfl | split)

private theorem r1_waitCarry_echo_frame
    (hwidth : 0 < width) (hle : width ≤ psi) (kappa : Nat)
    (l r : AgentState psi) :
    writerEchoPair (waitWidthCarry hwidth hle kappa l r) =
      writerEchoPair (l, r) := by
  unfold writerEchoPair waitWidthCarry
  repeat (first | rfl | split)

private theorem r1_waitReset_echo_frame
    (hwidth : 0 < width) (hle : width ≤ psi) (l r : AgentState psi) :
    writerEchoPair (waitWidthReset hwidth hle l r) =
      writerEchoPair (l, r) := by
  unfold writerEchoPair waitWidthReset
  repeat (first | rfl | split)

private theorem r1_waitFinish_echo_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (l r : AgentState psi) :
    writerEchoPair (waitWidthFinish hpsi hwidth hle kappa l r) =
      writerEchoPair (l, r) := by
  unfold writerEchoPair waitWidthFinish
  dsimp only
  repeat (first | rfl | split)

private theorem r1_genStart_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (genSigSaturatedStart hpsi l r) =
      writerEchoPair (l, r) := by
  unfold writerEchoPair genSigSaturatedStart
  dsimp only
  repeat (first | rfl | split)

private theorem r1_genEmit_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (BirthGenerationControlRepair.genCleanEmit hpsi l r) =
      writerEchoPair (l, r) := by
  unfold writerEchoPair BirthGenerationControlRepair.genCleanEmit
  dsimp only
  repeat (first | rfl | split)

private theorem r1_genPropagate_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair
        (BirthGenerationControlRepair.genCleanPropagate hpsi l r) =
      writerEchoPair (l, r) := by
  unfold writerEchoPair BirthGenerationControlRepair.genCleanPropagate
  repeat (first | rfl | split)

private theorem r1_genFinish_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (genSigSaturatedFinish hpsi l r) =
      writerEchoPair (l, r) := by
  unfold writerEchoPair genSigSaturatedFinish
  dsimp only
  repeat (first | rfl | split)

private theorem r1_cleanConnect_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (cleanSigGenConnect l, cleanSigGenConnect r) =
      writerEchoPair (l, r) := by
  unfold writerEchoPair cleanSigGenConnect
  dsimp only
  repeat (first | rfl | split)

private theorem r1_clean3_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (cleanSigStep3 l r) = writerEchoPair (l, r) := by
  unfold writerEchoPair cleanSigStep3
  repeat (first | rfl | split)

private theorem r1_clean4_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (cleanSigStep4 l r) = writerEchoPair (l, r) := by
  unfold writerEchoPair cleanSigStep4
  repeat (first | rfl | split)

private theorem r1_clean5_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (cleanSigStep5 hpsi l r) = writerEchoPair (l, r) := by
  unfold writerEchoPair cleanSigStep5
  repeat (first | rfl | split)

private theorem r1_clean6_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (cleanSigStep6 hpsi l r) = writerEchoPair (l, r) := by
  unfold writerEchoPair cleanSigStep6
  repeat (first | rfl | split)

private theorem r1_cleanApply_left_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (cleanSigCleanApply l, r) = writerEchoPair (l, r) := by
  unfold writerEchoPair cleanSigCleanApply
  dsimp only
  repeat (first | rfl | split)

private theorem r1_cleanApply_right_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (l, cleanSigCleanApply r) = writerEchoPair (l, r) := by
  unfold writerEchoPair cleanSigCleanApply
  dsimp only
  repeat (first | rfl | split)

private theorem r1_cleanApply_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (cleanSigCleanApply l, cleanSigCleanApply r) =
      writerEchoPair (l, r) :=
  (r1_cleanApply_left_echo_frame l (cleanSigCleanApply r)).trans
    (r1_cleanApply_right_echo_frame l r)

private theorem r1_clearLeft_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (clearComparisonSignal l, r) = writerEchoPair (l, r) := by
  unfold writerEchoPair clearComparisonSignal
  rfl

private theorem r1_clearRight_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (l, clearComparisonSignal r) = writerEchoPair (l, r) := by
  unfold writerEchoPair clearComparisonSignal
  rfl

private theorem r1_clearIfLeader_right_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (l, clearIfLeader r) = writerEchoPair (l, r) := by
  unfold clearIfLeader
  split
  · exact r1_clearRight_echo_frame l r
  · rfl

private theorem r1_preclear_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (sigMoveLeaderPreclear hpsi l r) =
      writerEchoPair (l, r) := by
  unfold sigMoveLeaderPreclear
  dsimp only
  split
  · exact (r1_clearLeft_echo_frame l (clearIfLeader r)).trans
      (r1_clearIfLeader_right_echo_frame l r)
  · exact r1_clearIfLeader_right_echo_frame l r

private theorem r1_capture_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (captureStep1 l r) = writerEchoPair (l, r) := by
  unfold writerEchoPair captureStep1
  dsimp only
  repeat (first | rfl | split)

private theorem r1_step2_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (sigMoveStep2 l r) = writerEchoPair (l, r) := by
  unfold writerEchoPair sigMoveStep2
  repeat (first | rfl | split)

private theorem r1_step3_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (sigMoveStep3 l r) = writerEchoPair (l, r) := by
  unfold writerEchoPair sigMoveStep3
  repeat (first | rfl | split)

private theorem r1_step4_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (sigMoveStep4 l r) = writerEchoPair (l, r) := by
  unfold writerEchoPair sigMoveStep4
  repeat (first | rfl | split)

private theorem r1_step5_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (sigMoveStep5 l r) = writerEchoPair (l, r) := by
  unfold writerEchoPair sigMoveStep5
  repeat (first | rfl | split)

private theorem r1_holdDone_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (holdDoneStep1 l r) = writerEchoPair (l, r) := by
  unfold holdDoneStep1
  split
  · rfl
  · exact r1_capture_echo_frame l r

private theorem r1_controlTransfers_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (controlTransfers l r) = writerEchoPair (l, r) := by
  unfold controlTransfers
  dsimp only
  rw [r1_step5_echo_frame, r1_step4_echo_frame,
    r1_step3_echo_frame, r1_step2_echo_frame]

private theorem r1_doneTransfers_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (doneTransfers l r) = writerEchoPair (l, r) := by
  unfold doneTransfers
  dsimp only
  rw [r1_controlTransfers_echo_frame, r1_holdDone_echo_frame]

private theorem r1_leaderWall_echo_frame
    (l r : AgentState psi) :
    writerEchoPair (comparisonLeaderWall l r) = writerEchoPair (l, r) := by
  unfold comparisonLeaderWall
  dsimp only
  split
  · split
    · exact (r1_clearLeft_echo_frame l (clearComparisonSignal r)).trans
        (r1_clearRight_echo_frame l r)
    · exact r1_clearLeft_echo_frame l r
  · split
    · exact r1_clearRight_echo_frame l r
    · rfl

private theorem r1_applyControl_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair
        (singleUseApplyControl hpsi l, singleUseApplyControl hpsi r) =
      writerEchoPair (l, r) := by
  unfold writerEchoPair singleUseApplyControl
  dsimp only
  repeat (first | rfl | split)

private theorem r1_controlTail_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (singleUseControlTail hpsi l r) =
      writerEchoPair (l, r) := by
  unfold singleUseControlTail
  dsimp only
  split
  · split
    · simpa [writerEchoPair] using r1_applyControl_echo_frame hpsi l r
    · exact r1_applyControl_echo_frame hpsi l r
  · exact r1_applyControl_echo_frame hpsi l r

private theorem r1_pprimeAuthorized_echo_frame
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    authorizedEchoPair
        (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hpsi l r) =
      authorizedEchoPair (l, r) := by
  have hc := PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall_core
    hpsi l r
  have he := congrArg writerEchoPair hc
  have hr := r1_pprimeRaw_echo_frame hpsi l.core r.core
  unfold authorizedEchoPair
  simpa only [writerEchoPair] using he.trans hr

private theorem r1_waitEntry_echo_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (l r : AgentState psi) :
    writerEchoPair
        (BirthShortWaitTerminalEntryRepair.waitWidthEntry
          hpsi hwidth hle kappa l r) = writerEchoPair (l, r) := by
  let p := waitSaturatedPrepare hpsi l r
  let e := BirthShortWaitTerminalEntryRepair.terminalInactiveClear
    hwidth hle p.1 p.2
  let c := waitWidthCarry hwidth hle kappa e.1 e.2
  let t := waitWidthReset hwidth hle c.1 c.2
  show writerEchoPair (waitWidthFinish hpsi hwidth hle kappa t.1 t.2) =
    writerEchoPair (l, r)
  exact (r1_waitFinish_echo_frame hpsi hwidth hle kappa t.1 t.2).trans
    ((r1_waitReset_echo_frame hwidth hle c.1 c.2).trans
      ((r1_waitCarry_echo_frame hwidth hle kappa e.1 e.2).trans
        ((r1_waitClear_echo_frame hwidth hle p.1 p.2).trans
          (r1_waitPrepare_echo_frame hpsi l r))))


private theorem r1_genAfterWait_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair
        (BirthGenerationControlRepair.genCleanAfterWait hpsi l r) =
      writerEchoPair (l, r) := by
  let s := genSigSaturatedStart hpsi l r
  let e := BirthGenerationControlRepair.genCleanEmit hpsi s.1 s.2
  let p := BirthGenerationControlRepair.genCleanPropagate hpsi e.1 e.2
  show writerEchoPair (genSigSaturatedFinish hpsi p.1 p.2) =
    writerEchoPair (l, r)
  exact (r1_genFinish_echo_frame hpsi p.1 p.2).trans
    ((r1_genPropagate_echo_frame hpsi e.1 e.2).trans
      ((r1_genEmit_echo_frame hpsi s.1 s.2).trans
        (r1_genStart_echo_frame hpsi l r)))


private theorem r1_genEntryRaw_echo_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (l r : AgentState psi) :
    writerEchoPair
        (genCleanEntryWidth hpsi hwidth hle kappa l r) =
      writerEchoPair (l, r) := by
  let w := BirthShortWaitTerminalEntryRepair.waitWidthEntry
    hpsi hwidth hle kappa l r
  have hw := r1_waitEntry_echo_frame hpsi hwidth hle kappa l r
  have hg := r1_genAfterWait_echo_frame hpsi w.1 w.2
  have hs :
      genCleanEntryWidth hpsi hwidth hle kappa l r =
        BirthGenerationControlRepair.genCleanAfterWait hpsi w.1 w.2 := by
    rfl
  rw [hs]
  exact hg.trans hw

private theorem r1_genEntryAuthorized_echo_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi) :
    authorizedEchoPair
        (authorizedGenCleanEntryWidth hpsi hwidth hle kappa l r) =
      authorizedEchoPair (l, r) := by
  exact authorizedReconcile_echo_frame
    (genCleanEntryWidth hpsi hwidth hle kappa)
    (r1_genEntryRaw_echo_frame hpsi hwidth hle kappa) l r

private theorem r1_cleanRaw_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (cleanSig hpsi l r) = writerEchoPair (l, r) := by
  unfold cleanSig
  dsimp only
  rw [r1_cleanApply_echo_frame, r1_clean6_echo_frame,
    r1_clean5_echo_frame, r1_clean4_echo_frame,
    r1_clean3_echo_frame, r1_cleanConnect_echo_frame]


private theorem r1_cleanAuthorized_echo_frame
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    authorizedEchoPair (authorizedCleanSig hpsi l r) =
      authorizedEchoPair (l, r) := by
  exact authorizedReconcile_echo_frame (cleanSig hpsi)
    (r1_cleanRaw_echo_frame hpsi) l r

private theorem r1_doneRaw_echo_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    writerEchoPair (doneCaptureSigMove hpsi l r) = writerEchoPair (l, r) := by
  unfold doneCaptureSigMove
  dsimp only
  rw [r1_controlTail_echo_frame, r1_leaderWall_echo_frame,
    r1_doneTransfers_echo_frame, r1_preclear_echo_frame]


private theorem r1_doneAuthorized_echo_frame
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    authorizedEchoPair (authorizedDoneMove hpsi l r) =
      authorizedEchoPair (l, r) := by
  have hc := authorizedDoneMove_core hpsi l r
  have he := congrArg writerEchoPair hc
  have hr := r1_doneRaw_echo_frame hpsi l.core r.core
  unfold authorizedEchoPair
  simpa only [writerEchoPair] using he.trans hr

private theorem r1_congestGuardCheck_echo_frame
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    authorizedEchoPair (congestGuardCheck hpsi l r) =
      authorizedEchoPair (l, r) := by
  unfold congestGuardCheck
  split
  · rfl
  · exact authorizedEchoPair_of_resetEchoPair_eq
      (check_resetEcho_frame hpsi l r)

private theorem r1_preserveTossCheck_echo_frame
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    authorizedEchoPair (preserveTossCheck hpsi l r) =
      authorizedEchoPair (l, r) := by
  unfold preserveTossCheck
  split
  · rfl
  · exact r1_congestGuardCheck_echo_frame hpsi l r

private theorem r1_preserveDoneCheck_echo_frame
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    authorizedEchoPair (preserveDoneCheck hpsi l r) =
      authorizedEchoPair (l, r) := by
  unfold preserveDoneCheck
  split
  · rfl
  · exact r1_preserveTossCheck_echo_frame hpsi l r

private theorem generationBeforeMoveEntryWidth_echo_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi) :
    authorizedEchoPair
        (generationBeforeMoveEntryWidth hpsi hwidth hle kappa l r) =
      authorizedEchoPair (l, r) := by
  let q0 := PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hpsi l r
  let q1 := authorizedGenCleanEntryWidth hpsi hwidth hle kappa q0.1 q0.2
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  have h0 := r1_pprimeAuthorized_echo_frame hpsi l r
  have h1 := r1_genEntryAuthorized_echo_frame
    hpsi hwidth hle kappa q0.1 q0.2
  have h2 := r1_cleanAuthorized_echo_frame hpsi q1.1 q1.2
  have h3 := authorizedEchoPair_of_resetEchoPair_eq
    (authorizedEliminate_resetEcho_frame hpsi q2.1 q2.2)
  have hs : generationBeforeMoveEntryWidth hpsi hwidth hle kappa l r =
      authorizedEliminateSig hpsi q2.1 q2.2 := by
    rfl
  rw [hs]
  exact h3.trans (h2.trans (h1.trans h0))

private theorem doneBeforeCheckEntryWidth_echo_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi) :
    authorizedEchoPair
        (doneBeforeCheckEntryWidth hpsi hwidth hle kappa l r) =
      authorizedEchoPair (l, r) := by
  let b := generationBeforeMoveEntryWidth hpsi hwidth hle kappa l r
  let q := authorizedDoneMove hpsi b.1 b.2
  let qR := preCheckResetWall q.1 q.2
  have hb := generationBeforeMoveEntryWidth_echo_frame
    hpsi hwidth hle kappa l r
  have hq := r1_doneAuthorized_echo_frame hpsi b.1 b.2
  have hR := authorizedEchoPair_of_resetEchoPair_eq
    (preCheckResetWall_resetEchoPair q.1 q.2)
  have hs := authorizedEchoPair_of_resetEchoPair_eq
    (sanitizeAuthorizedPair_resetEchoPair hpsi qR)
  show authorizedEchoPair
      (PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair hpsi qR) =
    authorizedEchoPair (l, r)
  exact hs.trans (hR.trans (hq.trans hb))


private theorem doneThroughCheckEntryWidth_echo_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi) :
    authorizedEchoPair
        (doneThroughCheckEntryWidth hpsi hwidth hle kappa l r) =
      authorizedEchoPair (l, r) := by
  let b := doneBeforeCheckEntryWidth hpsi hwidth hle kappa l r
  have hb := doneBeforeCheckEntryWidth_echo_frame
    hpsi hwidth hle kappa l r
  have hc := r1_preserveDoneCheck_echo_frame hpsi b.1 b.2
  have hstage : doneThroughCheckEntryWidth hpsi hwidth hle kappa l r =
      preserveDoneCheck hpsi b.1 b.2 := by
    rfl
  rw [hstage]
  exact hc.trans hb

/-! Post-CHECK suffix and the three priority branches. -/

private theorem afterCheckMetadataWidth_resetEcho_zero
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = false)
    (hlReset : l.core.reset_cmd = false) (hlEcho : l.core.echo = false)
    (hrReset : r.core.reset_cmd = false) (hrEcho : r.core.echo = false) :
    authResetEchoZero (afterCheckMetadataWidth hpsi hwidth hle l r) := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedSuppressWidth hpsi hwidth hle q1.1 q1.2
  let q3 := stationaryPersistentAuthorizedRow hpsi q2.1 q2.2
  have h0 := disappear_resetEcho_frame hpsi l r
  have h1 := compareActionOne_resetEcho_frame hpsi q0.1 q0.2
  have hpre := h1.trans h0
  have h0Leaders := PPLLVerify.disappear_leaders_eq hpsi l.core r.core
  have h1Leaders := compareActionOne_leaders hpsi q0.1 q0.2
  have hq1Leader : q1.1.core.leader = false :=
    h1Leaders.1.trans (h0Leaders.1.trans hlLeader)
  have hs := authorizedSuppressWidth_resetEcho_zero hpsi hwidth hle
    q1.1 q1.2 hq1Leader
    ((resetEcho_left_reset hpre).trans hlReset)
    ((resetEcho_left_echo hpre).trans hlEcho)
    ((resetEcho_right_reset hpre).trans hrReset)
    ((resetEcho_right_echo hpre).trans hrEcho)
  have hwR := BirthB1InnerFieldFrames.stationaryPersistentAuthorizedRow_reset_cmd
    hpsi q2.1 q2.2
  have hwE := stationaryPersistentAuthorizedRow_echo_frame hpsi q2.1 q2.2
  have hstage : afterCheckMetadataWidth hpsi hwidth hle l r = q3 := by
    rfl
  rw [hstage]
  unfold authResetEchoZero
  exact ⟨hwR.1.trans hs.1,
    hwE.1.trans hs.2.1,
    hwR.2.trans hs.2.2.1,
    hwE.2.trans hs.2.2.2⟩

private theorem normalizeDeletion_leader_frame
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion
  split <;> rfl

private theorem normalized_state_ne_eliminate_of_not_active
    (u : AuthorizedAgentState psi)
    (h : deletionActive (normalizeDeletion u) ≠ true) :
    (normalizeDeletion u).core.state ≠ .eliminate_signal := by
  cases hp : u.core.path with
  | bot =>
      by_cases hs : u.core.state = .eliminate_signal <;>
        simp [normalizeDeletion, pathPresent, hp, hs]
  | some label bit =>
      have hn : normalizeDeletion u = u := by
        simp [normalizeDeletion, pathPresent, hp]
      rw [hn]
      intro hs
      apply h
      rw [hn]
      simp [deletionActive, pathPresent, hp, hs]

private theorem doneThroughCheckEntryWidth_left_echo
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi) :
    (doneThroughCheckEntryWidth hpsi hwidth hle kappa l r).1.core.echo =
      l.core.echo := by
  let g := generationBeforeMoveEntryWidth hpsi hwidth hle kappa l r
  let m := authorizedDoneMove hpsi g.1 g.2
  let qR := preCheckResetWall m.1 m.2
  let s := PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair hpsi qR
  let z := preserveDoneCheck hpsi s.1 s.2


  have hg := generationBeforeMoveEntryWidth_echo_frame
    hpsi hwidth hle kappa l r
  have hm := r1_doneAuthorized_echo_frame hpsi g.1 g.2
  have hR := authorizedEchoPair_of_resetEchoPair_eq
    (preCheckResetWall_resetEchoPair m.1 m.2)
  have hs := authorizedEchoPair_of_resetEchoPair_eq
    (sanitizeAuthorizedPair_resetEchoPair hpsi qR)
  have hz := r1_preserveDoneCheck_echo_frame hpsi s.1 s.2


  have hgL : g.1.core.echo = l.core.echo :=
    (authorizedEchoPair_fst g).symm.trans
      ((congrArg Prod.fst hg).trans (authorizedEchoPair_fst (l, r)))
  have hmL : m.1.core.echo = g.1.core.echo :=
    (authorizedEchoPair_fst m).symm.trans
      ((congrArg Prod.fst hm).trans
        (authorizedEchoPair_fst (g.1, g.2)))
  have hRL : qR.1.core.echo = m.1.core.echo :=
    (authorizedEchoPair_fst qR).symm.trans
      ((congrArg Prod.fst hR).trans
        (authorizedEchoPair_fst (m.1, m.2)))
  have hsL : s.1.core.echo = qR.1.core.echo :=
    (authorizedEchoPair_fst s).symm.trans
      ((congrArg Prod.fst hs).trans
        (authorizedEchoPair_fst qR))
  have hzL : z.1.core.echo = s.1.core.echo :=
    (authorizedEchoPair_fst z).symm.trans
      ((congrArg Prod.fst hz).trans
        (authorizedEchoPair_fst (s.1, s.2)))


  have hstage :
      doneThroughCheckEntryWidth hpsi hwidth hle kappa l r = z := by
    rfl
  rw [hstage]
  exact hzL.trans (hsL.trans (hRL.trans (hmL.trans hgL)))


private theorem doneThroughCheckEntryWidth_right_echo
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi) :
    (doneThroughCheckEntryWidth hpsi hwidth hle kappa l r).2.core.echo =
      r.core.echo := by
  let g := generationBeforeMoveEntryWidth hpsi hwidth hle kappa l r
  let m := authorizedDoneMove hpsi g.1 g.2
  let qR := preCheckResetWall m.1 m.2
  let s := PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair hpsi qR
  let z := preserveDoneCheck hpsi s.1 s.2


  have hg := generationBeforeMoveEntryWidth_echo_frame
    hpsi hwidth hle kappa l r
  have hm := r1_doneAuthorized_echo_frame hpsi g.1 g.2
  have hR := authorizedEchoPair_of_resetEchoPair_eq
    (preCheckResetWall_resetEchoPair m.1 m.2)
  have hs := authorizedEchoPair_of_resetEchoPair_eq
    (sanitizeAuthorizedPair_resetEchoPair hpsi qR)
  have hz := r1_preserveDoneCheck_echo_frame hpsi s.1 s.2


  have hgR : g.2.core.echo = r.core.echo :=
    (authorizedEchoPair_snd g).symm.trans
      ((congrArg Prod.snd hg).trans (authorizedEchoPair_snd (l, r)))
  have hmR : m.2.core.echo = g.2.core.echo :=
    (authorizedEchoPair_snd m).symm.trans
      ((congrArg Prod.snd hm).trans
        (authorizedEchoPair_snd (g.1, g.2)))
  have hRR : qR.2.core.echo = m.2.core.echo :=
    (authorizedEchoPair_snd qR).symm.trans
      ((congrArg Prod.snd hR).trans
        (authorizedEchoPair_snd (m.1, m.2)))
  have hsR : s.2.core.echo = qR.2.core.echo :=
    (authorizedEchoPair_snd s).symm.trans
      ((congrArg Prod.snd hs).trans
        (authorizedEchoPair_snd qR))
  have hzR : z.2.core.echo = s.2.core.echo :=
    (authorizedEchoPair_snd z).symm.trans
      ((congrArg Prod.snd hz).trans
        (authorizedEchoPair_snd (s.1, s.2)))


  have hstage :
      doneThroughCheckEntryWidth hpsi hwidth hle kappa l r = z := by
    rfl
  rw [hstage]
  exact hzR.trans (hsR.trans (hRR.trans (hmR.trans hgR)))

private theorem ordinary_resetEcho_zero
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlel : l.core.state ≠ .eliminate_signal)
    (hrel : r.core.state ≠ .eliminate_signal)
    (hlLeader : l.core.leader = false)
    (hlReset : l.core.reset_cmd = false) (hlEcho : l.core.echo = false)
    (hrReset : r.core.reset_cmd = false) (hrEcho : r.core.echo = false) :
    authResetEchoZero
      (BirthCheckPermitRepair.ordinary hpsi (by decide : 0 < 2) h2
        kappa l r) := by
  have hcR := BirthB1InnerCountMono.doneThroughCheckEntryWidth_reset_cmd
    hpsi (by decide : 0 < 2) h2 kappa l r
  have hcL := BirthCheckPermitRepairRowLift.doneThrough_left_leader
    hpsi h2 kappa l r hlel hrel
  have hcEL := doneThroughCheckEntryWidth_left_echo
    hpsi (by decide : 0 < 2) h2 kappa l r
  have hcER := doneThroughCheckEntryWidth_right_echo
    hpsi (by decide : 0 < 2) h2 kappa l r

  generalize hc :
      doneThroughCheckEntryWidth hpsi (by decide : 0 < 2) h2 kappa l r = c
    at hcR hcL hcEL hcER

  have permitFix_leader (u : AuthorizedAgentState psi) :
      (permitFix u).core.leader = u.core.leader := by
    rw [permitFix_core]
  have permitFix_reset_cmd (u : AuthorizedAgentState psi) :
      (permitFix u).core.reset_cmd = u.core.reset_cmd := by
    rw [permitFix_core]
  have permitFix_echo (u : AuthorizedAgentState psi) :
      (permitFix u).core.echo = u.core.echo := by
    rw [permitFix_core]

  let p := permitFix c.1
  let q := afterCheckMetadataWidth hpsi (by decide : 0 < 2) h2 p c.2

  have hpLeaderFalse : p.core.leader = false := by
    change (permitFix c.1).core.leader = false
    rw [permitFix_leader]
    exact hcL.trans hlLeader
  have hpResetFalse : p.core.reset_cmd = false := by
    change (permitFix c.1).core.reset_cmd = false
    rw [permitFix_reset_cmd]
    exact hcR.1.trans hlReset
  have hpEchoFalse : p.core.echo = false := by
    change (permitFix c.1).core.echo = false
    rw [permitFix_echo]
    exact hcEL.trans hlEcho
  have hcRResetFalse : c.2.core.reset_cmd = false :=
    hcR.2.trans hrReset
  have hcREchoFalse : c.2.core.echo = false :=
    hcER.trans hrEcho

  have hq : authResetEchoZero q := by
    exact afterCheckMetadataWidth_resetEcho_zero
      hpsi (by decide : 0 < 2) h2 p c.2
      hpLeaderFalse hpResetFalse hpEchoFalse hcRResetFalse hcREchoFalse
  have hm := markLeaderBirth_resetEcho_frame (authBirth l r q) q
  have hout : authResetEchoZero (markLeaderBirth (authBirth l r q) q) := by
    unfold authResetEchoZero
    exact ⟨(resetEcho_left_reset hm).trans hq.1,
      (resetEcho_left_echo hm).trans hq.2.1,
      (resetEcho_right_reset hm).trans hq.2.2.1,
      (resetEcho_right_echo hm).trans hq.2.2.2⟩

  unfold BirthCheckPermitRepair.ordinary
  rw [hc]
  change authResetEchoZero (markLeaderBirth (authBirth l r q) q)
  exact hout


private theorem authorized_resetEcho_zero
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false)
    (_hrFollower : r.core.leader = false)
    (hlReset : l.core.reset_cmd = false) (hlEcho : l.core.echo = false)
    (hrReset : r.core.reset_cmd = false) (hrEcho : r.core.echo = false) :
    authResetEchoZero
      (BirthCheckPermitRepair.authorized hpsi (by decide : 0 < 2) h2
        kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hn := normalizeDeletion_resetEcho_frame l r
  have hl0Leader : l0.core.leader = false :=
    (normalizeDeletion_leader_frame l).trans hlFollower
  have hl0Reset : l0.core.reset_cmd = false :=
    (resetEcho_left_reset hn).trans hlReset
  have hl0Echo : l0.core.echo = false :=
    (resetEcho_left_echo hn).trans hlEcho
  have hr0Reset : r0.core.reset_cmd = false :=
    (resetEcho_right_reset hn).trans hrReset
  have hr0Echo : r0.core.echo = false :=
    (resetEcho_right_echo hn).trans hrEcho
  have hstage :
      BirthCheckPermitRepair.authorized hpsi (by decide : 0 < 2) h2 kappa l r =
        (if deletionActive r0 then authorizedEliminateSig hpsi l0 r0
         else if deletionActive l0 then (l0, r0)
         else BirthCheckPermitRepair.ordinary hpsi (by decide : 0 < 2) h2
           kappa l0 r0) := by
    rfl
  rw [hstage]
  by_cases hR : deletionActive r0 = true
  · rw [if_pos hR]
    have he := authorizedEliminate_resetEcho_frame hpsi l0 r0
    unfold authResetEchoZero
    exact ⟨(resetEcho_left_reset he).trans hl0Reset,
      (resetEcho_left_echo he).trans hl0Echo,
      (resetEcho_right_reset he).trans hr0Reset,
      (resetEcho_right_echo he).trans hr0Echo⟩
  · rw [if_neg hR]
    by_cases hL : deletionActive l0 = true
    · rw [if_pos hL]
      exact ⟨hl0Reset, hl0Echo, hr0Reset, hr0Echo⟩
    · rw [if_neg hL]
      exact ordinary_resetEcho_zero hpsi h2 kappa l0 r0
        (normalized_state_ne_eliminate_of_not_active l hL)
        (normalized_state_ne_eliminate_of_not_active r hR)
        hl0Leader hl0Reset hl0Echo hr0Reset hr0Echo

/-! Outer bounded / expiry / normalization / final-physical wrappers. -/

private theorem prepareDisposal_echo_frame
    (hpsi : 0 < psi) (u : AuthorizedAgentState psi) :
    (BirthSigMoveDisposalRepair.prepareDisposal hpsi u).core.echo =
      u.core.echo := by
  unfold BirthSigMoveDisposalRepair.prepareDisposal markComparisonForDeletion
  repeat (first | rfl | split)

private theorem prepareExpiringDisposal_echo_frame
    (hpsi : 0 < psi) (u : ExpiringAgentState psi kappa tau) :
    echoE (BirthSigMoveDisposalRepair.prepareExpiringDisposal hpsi u) =
      echoE u := by
  have he := BirthSigMoveDisposalRepair.erase_prepareBoundedDisposal hpsi u.core
  have hp := congrArg (fun z : AuthorizedAgentState psi => z.core.echo) he
  have hd := prepareDisposal_echo_frame hpsi u.core.erase
  simpa only [echoE, BirthSigMoveDisposalRepair.prepareExpiringDisposal]
    using hp.trans hd

private theorem boundedResetEchoZero_of_erase_eq
    {q : AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa}
    {a : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (he : (q.1.erase, q.2.erase) = a)
    (ha : authResetEchoZero a) :
    boundedResetEchoZero q := by
  have hp := congrArg authorizedResetEchoPair he
  unfold authResetEchoZero at ha
  show q.1.erase.core.reset_cmd = false ∧
    q.1.erase.core.echo = false ∧
    q.2.erase.core.reset_cmd = false ∧
    q.2.erase.core.echo = false
  exact ⟨(resetEcho_left_reset hp).trans ha.1,
    (resetEcho_left_echo hp).trans ha.2.1,
    (resetEcho_right_reset hp).trans ha.2.2.1,
    (resetEcho_right_echo hp).trans ha.2.2.2⟩

private theorem bounded_resetEcho_zero
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hlFollower : l.erase.core.leader = false)
    (hrFollower : r.erase.core.leader = false)
    (hlReset : l.erase.core.reset_cmd = false)
    (hlEcho : l.erase.core.echo = false)
    (hrReset : r.erase.core.reset_cmd = false)
    (hrEcho : r.erase.core.echo = false) :
    boundedResetEchoZero
      (BirthCheckPermitRepair.bounded hpsi (by decide : 0 < 2) h2 l r) := by
  have ha := authorized_resetEcho_zero hpsi h2 kappa l.erase r.erase
    hlFollower hrFollower hlReset hlEcho hrReset hrEcho
  have he := BirthCheckPermitRepairBirth.r1_bounded_erase hpsi h2 l r
  exact boundedResetEchoZero_of_erase_eq
    (q := BirthCheckPermitRepair.bounded
      hpsi (by decide : 0 < 2) h2 l r)
    (a := BirthCheckPermitRepair.authorized
      hpsi (by decide : 0 < 2) h2 kappa l.erase r.erase)
    he ha


private theorem expireOne_echo_frame
    (old out : ExpiringAgentState psi kappa tau) :
    echoE (deletionPriorityExpireOne tau old out) = echoE out := by
  have h := PPLLWallSweepFiniteCleanup.deletionPriorityExpireOne_path_frame old out
  exact h.2.2.2.2.1

private theorem expiring_resetEcho_zero
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hlFollower : l.core.erase.core.leader = false)
    (hrFollower : r.core.erase.core.leader = false)
    (hlReset : l.core.erase.core.reset_cmd = false)
    (hlEcho : l.core.erase.core.echo = false)
    (hrReset : r.core.erase.core.reset_cmd = false)
    (hrEcho : r.core.erase.core.echo = false) :
    physResetEchoZero
      (BirthCheckPermitRepair.expiring hpsi (by decide : 0 < 2) h2 l r) := by
  let l0 := BirthSigMoveDisposalRepair.prepareExpiringDisposal hpsi l
  let r0 := BirthSigMoveDisposalRepair.prepareExpiringDisposal hpsi r
  let q := BirthCheckPermitRepair.bounded hpsi (by decide : 0 < 2) h2
    l0.core r0.core
  let oL : ExpiringAgentState psi kappa tau := ⟨q.1, l0.stall⟩
  let oR : ExpiringAgentState psi kappa tau := ⟨q.2, r0.stall⟩
  have hl0Echo : l0.core.erase.core.echo = false := by
    show echoE l0 = false
    exact (prepareExpiringDisposal_echo_frame hpsi l).trans hlEcho
  have hr0Echo : r0.core.erase.core.echo = false := by
    show echoE r0 = false
    exact (prepareExpiringDisposal_echo_frame hpsi r).trans hrEcho
  have hb : boundedResetEchoZero q := bounded_resetEcho_zero hpsi h2 l0.core r0.core
    ((BirthB1RowCountFrame.prepare_leader_eq hpsi l).trans hlFollower)
    ((BirthB1RowCountFrame.prepare_leader_eq hpsi r).trans hrFollower)
    ((BirthB1RowCountFrame.prepare_reset_eq hpsi l).trans hlReset)
    hl0Echo
    ((BirthB1RowCountFrame.prepare_reset_eq hpsi r).trans hrReset)
    hr0Echo
  have hxLR := BirthB1CountAlongNoBirth.expireOne_reset l0 oL
  have hxRR := BirthB1CountAlongNoBirth.expireOne_reset r0 oR
  have hxLE := expireOne_echo_frame l0 oL
  have hxRE := expireOne_echo_frame r0 oR
  have hstage :
      BirthCheckPermitRepair.expiring hpsi (by decide : 0 < 2) h2 l r =
        (deletionPriorityExpireOne tau l0 oL,
          deletionPriorityExpireOne tau r0 oR) := by
    rfl
  rw [hstage]
  unfold boundedResetEchoZero at hb
  unfold physResetEchoZero
  exact ⟨
    (by simpa only [BirthB1CountAlongNoBirth.resetE] using
      hxLR.trans hb.1),
    (by simpa only [echoE] using hxLE.trans hb.2.1),
    (by simpa only [BirthB1CountAlongNoBirth.resetE] using
      hxRR.trans hb.2.2.1),
    (by simpa only [echoE] using hxRE.trans hb.2.2.2)⟩


private theorem normalizeLeader_echo_frame
    (hpsi : 0 < psi) (q : ExpiringAgentState psi kappa tau) :
    echoE (normalizeLeader hpsi q) = echoE q := by
  unfold normalizeLeader echoE
  split <;> rfl

private theorem nonK2_echo_frame
    (q : ExpiringAgentState psi kappa tau) :
    echoE (ExpiringK2Projection.nonK2 q) = echoE q := rfl

private theorem finalPhysical_echo_frame
    (hpsi : 0 < psi)
    (oldL oldR metaL metaR : ExpiringAgentState psi kappa tau) :
    echoE (finalPhysical hpsi oldL oldR metaL metaR).1 = echoE metaL ∧
      echoE (finalPhysical hpsi oldL oldR metaL metaR).2 = echoE metaR := by
  have hf := finalPhysical_nonK2 hpsi oldL oldR metaL metaR
  constructor
  · have h := congrArg echoE hf.1
    rwa [nonK2_echo_frame, nonK2_echo_frame] at h
  · have h := congrArg echoE hf.2
    rwa [nonK2_echo_frame, nonK2_echo_frame] at h

private theorem row_resetEcho_zero
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hlFollower : l.core.erase.core.leader = false)
    (hrFollower : r.core.erase.core.leader = false)
    (hlReset : l.core.erase.core.reset_cmd = false)
    (hlEcho : l.core.erase.core.echo = false)
    (hrReset : r.core.erase.core.reset_cmd = false)
    (hrEcho : r.core.erase.core.echo = false) :
    physResetEchoZero
      (BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2 l r) := by
  let q := BirthCheckPermitRepair.expiring hpsi (by decide : 0 < 2) h2 l r
  let nL := normalizeLeader hpsi q.1
  let nR := normalizeLeader hpsi q.2
  have he := expiring_resetEcho_zero hpsi h2 l r
    hlFollower hrFollower hlReset hlEcho hrReset hrEcho
  have hnLR := BirthB1CountAlongNoBirth.normalizeLeader_reset hpsi q.1
  have hnRR := BirthB1CountAlongNoBirth.normalizeLeader_reset hpsi q.2
  have hnLE := normalizeLeader_echo_frame hpsi q.1
  have hnRE := normalizeLeader_echo_frame hpsi q.2
  have hfR := BirthB1CountAlongNoBirth.finalPhysical_reset
    hpsi l r nL nR
  have hfE := finalPhysical_echo_frame hpsi l r nL nR
  have hstage :
      BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2 l r =
        finalPhysical hpsi l r nL nR := by
    rfl
  rw [hstage]
  unfold physResetEchoZero at he ⊢
  exact ⟨
    (by simpa only [BirthB1CountAlongNoBirth.resetE] using
      hfR.1.trans (hnLR.trans he.1)),
    (by simpa only [echoE] using hfE.1.trans (hnLE.trans he.2.1)),
    (by simpa only [BirthB1CountAlongNoBirth.resetE] using
      hfR.2.trans (hnRR.trans he.2.2.1)),
    (by simpa only [echoE] using hfE.2.trans (hnRE.trans he.2.2.2))⟩

/-- One width-two R1 service cannot bootstrap physical Algorithm-14
reset/echo traffic from two follower endpoints whose reset/echo bits are zero. -/
theorem r1_follower_resetEcho_frame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : B9Host.Phys psi kappa tau)
    (hlFollower : (B6Sanitation.rawCell l).leader = false)
    (hrFollower : (B6Sanitation.rawCell r).leader = false)
    (hlReset : (B6Sanitation.rawCell l).reset_cmd = false)
    (hlEcho : (B6Sanitation.rawCell l).echo = false)
    (hrReset : (B6Sanitation.rawCell r).reset_cmd = false)
    (hrEcho : (B6Sanitation.rawCell r).echo = false) :
    let q := (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2).row l r
    let vl := B6Sanitation.rawCell q.1
    let vr := B6Sanitation.rawCell q.2
    vl.reset_cmd = false ∧ vl.echo = false ∧
      vr.reset_cmd = false ∧ vr.echo = false := by
  have hrow := row_resetEcho_zero
    (kappa := kappa) (tau := tau) hpsi h2 l r
    (by simpa only [B6Sanitation.rawCell] using hlFollower)
    (by simpa only [B6Sanitation.rawCell] using hrFollower)
    (by simpa only [B6Sanitation.rawCell] using hlReset)
    (by simpa only [B6Sanitation.rawCell] using hlEcho)
    (by simpa only [B6Sanitation.rawCell] using hrReset)
    (by simpa only [B6Sanitation.rawCell] using hrEcho)
  simpa only [B9Host.r1Host, B9Host.r1HostWidth,
    physResetEchoZero, B6Sanitation.rawCell] using hrow

end B6TrafficPairFrame
-- next seam; statement only, deliberately not installed as an axiom/theorem
-- BirthStationaryWrite.stationaryPersistentAuthorizedRow must preserve
-- both reset_cmd and echo on both cores.
