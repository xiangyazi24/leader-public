import Leader.Wu.Birth.ShortDoneTerminalCapCheckCut

namespace BirthShortDoneTerminalCapGeneralR4

open PPLL PPLLRepair PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLWallSweepRepair PPLLWallSweepNormalResetContract
  PPLLWallSweepPreCheckResetRepair
open PPLLWallSweepPreCheckResetContracts
open PPLLCompleteMultiLeaderCleanup
open PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair
open PPLLLeaderCreationCleanupRepair
open BirthGenerationDone BirthShortWait BirthShortDoneCuts
open BirthStationaryWrite BirthWaitPassive
open K2BirthDispatcher

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

private theorem h2 : 0 < 2 := by decide
private theorem hle2 : 2 <= 2 := by decide

/-- Exactly the three physical fields still needed by the cap endpoint. -/
private structure CapClock2 where
  label : Fin 2
  count : Nat
  wait : Bool

/-- Fieldwise equality for the local cap-clock observation. -/
private theorem capClock2_ext (a b : CapClock2)
    (hl : a.label = b.label) (hc : a.count = b.count)
    (hw : a.wait = b.wait) : a = b := by
  cases a
  cases b
  cases hl
  cases hc
  cases hw
  rfl

private def capClock2 (u : AgentState 2) : CapClock2 :=
  ⟨u.label, u.count, u.wait⟩

private def capClockPair2 (q : AgentState 2 × AgentState 2) :
    CapClock2 × CapClock2 :=
  (capClock2 q.1, capClock2 q.2)

private def authCapClockPair2
    (q : AuthorizedAgentState 2 × AuthorizedAgentState 2) :
    CapClock2 × CapClock2 :=
  capClockPair2 (q.1.core, q.2.core)

private theorem capClockIte (p : Prop) [Decidable p]
    (u v : AgentState 2) :
    capClock2 (if p then u else v) =
      if p then capClock2 u else capClock2 v := by
  split <;> rfl

private theorem capClockSetState (u : AgentState 2) (s : MainState) :
    capClock2 { u with state := s } = capClock2 u := rfl

/-! ## DISAPPEAR and action-one COMPARE -/

private theorem capClockSetWriteState (u : AgentState 2) (s : WriteState) :
    capClock2 { u with write_state := s } = capClock2 u := rfl

private theorem capClockSetWrite (u : AgentState 2) (w : WriteAction) :
    capClock2 { u with write := w } = capClock2 u := rfl

/-- Project a cap-clock equality only after both endpoints have been abstracted.
    This is the heartbeat-safe replacement for projecting a concrete computed
    CHECK cut five separate times. -/
private theorem authCapClockPair2_fields
    (q q' : AuthorizedAgentState 2 × AuthorizedAgentState 2)
    (h : authCapClockPair2 q = authCapClockPair2 q') :
    q.1.core.label = q'.1.core.label /\
      q.2.core.label = q'.2.core.label /\
      q.2.core.count = q'.2.core.count /\
      q.1.core.wait = q'.1.core.wait /\
      q.2.core.wait = q'.2.core.wait := by
  have hL := congrArg Prod.fst h
  have hR := congrArg Prod.snd h
  have hLL := congrArg CapClock2.label hL
  have hRL := congrArg CapClock2.label hR
  have hRC := congrArg CapClock2.count hR
  have hLW := congrArg CapClock2.wait hL
  have hRW := congrArg CapClock2.wait hR
  change q.1.core.label = q'.1.core.label at hLL
  change q.2.core.label = q'.2.core.label at hRL
  change q.2.core.count = q'.2.core.count at hRC
  change q.1.core.wait = q'.1.core.wait at hLW
  change q.2.core.wait = q'.2.core.wait at hRW
  exact ⟨hLL, hRL, hRC, hLW, hRW⟩

private theorem disappear_capClockPair2 (l r : AgentState 2) :
    capClockPair2 (disappear h2 l r) = capClockPair2 (l, r) := by
  unfold disappear capClockPair2 capClock2
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem authorizedDisappear_capClockPair2
    (l r : AuthorizedAgentState 2) :
    authCapClockPair2 (authorizedDisappear h2 l r) =
      authCapClockPair2 (l, r) := by
  change capClockPair2 (disappear h2 l.core r.core) =
    capClockPair2 (l.core, r.core)
  exact disappear_capClockPair2 l.core r.core

private theorem compareSigInit_capClock2 (u : AgentState 2) :
    capClock2 (compareSigInit u) = capClock2 u := by
  unfold compareSigInit capClock2
  split <;> rfl

private theorem cmpUpdateReturnPriority_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (cmpUpdateReturnPriority h2 l r) =
      capClockPair2 (l, r) := by
  unfold cmpUpdateReturnPriority capClockPair2 capClock2
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem cmpUpdateSetPath2_capClock2 (u : AgentState 2) :
    capClock2 (cmpUpdateSetPath2 h2 u) = capClock2 u := by
  unfold cmpUpdateSetPath2 capClock2
  repeat (first | rfl | split)

private theorem authorizedCmpUpdate_capClockPair2
    (l r : AuthorizedAgentState 2) :
    authCapClockPair2 (authorizedCmpUpdate h2 l r) =
      authCapClockPair2 (l, r) := by
  let allowed := freshComparisonStart h2 l
  let lCore := if allowed && !comparisonActive l.core.state then
    { l.core with state := MainState.congest }
  else l.core
  let q := cmpUpdateReturnPriority h2 lCore r.core

  have hlCore : capClock2 lCore = capClock2 l.core := by
    unfold lCore
    split <;> rfl
  have hq := cmpUpdateReturnPriority_capClockPair2 lCore r.core
  have hqL := congrArg Prod.fst hq
  have hqR := congrArg Prod.snd hq

  change
    capClockPair2 (cmpUpdateSetPath2 h2 q.1, q.2) =
      capClockPair2 (l.core, r.core)
  exact Prod.ext
    ((cmpUpdateSetPath2_capClock2 q.1).trans (hqL.trans hlCore))
    hqR

private theorem compareBitUpdateRActionOne_capClock2
    (u : AgentState 2) :
    capClock2 (compareBitUpdateRActionOne h2 u) = capClock2 u := by
  apply capClock2_ext
  all_goals
    unfold capClock2 compareBitUpdateRActionOne
    try dsimp only []
    repeat (first | rfl | split)

private theorem compareBitUpdateL_capClock2
    (u : AgentState 2) :
    capClock2 (compareBitUpdateL h2 u) = capClock2 u := by
  unfold compareBitUpdateL capClock2
  repeat (first | rfl | split)

private theorem compareBitActionOne_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (compareBitActionOne h2 l r) =
      capClockPair2 (l, r) := by
  exact Prod.ext (compareBitUpdateL_capClock2 l)
    (compareBitUpdateRActionOne_capClock2 r)

private theorem compareSigDispatchActionOne_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (compareSigDispatchActionOne h2 l r) =
      capClockPair2 (l, r) := by
  unfold compareSigDispatchActionOne
  repeat
    (first | exact compareBitActionOne_capClockPair2 l r | rfl | split)

private theorem authorizedCompareSigActionOne_capClockPair2
    (l r : AuthorizedAgentState 2) :
    authCapClockPair2 (authorizedCompareSigActionOne h2 l r) =
      authCapClockPair2 (l, r) := by
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState 2 :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  have hinit : capClock2 lCore = capClock2 l.core :=
    compareSigInit_capClock2 l.core

  unfold authorizedCompareSigActionOne
  dsimp only [authCapClockPair2, capClockPair2]
  split
  · exact Prod.ext hinit rfl
  · split
    · exact Prod.ext hinit rfl
    · let q := authorizedCmpUpdate h2 l0 r
      have hq := authorizedCmpUpdate_capClockPair2 l0 r
      have hout := compareSigDispatchActionOne_capClockPair2
        q.1.core q.2.core
      exact hout.trans (hq.trans (Prod.ext hinit rfl))

/-! ## The only dangerous count-reset boundary -/

private theorem suppressPrefix_eq_of_quiet
    (l r : AgentState 2)
    (hll : l.leader = false)
    (hlreset : l.reset_cmd = false)
    (hrreset : r.reset_cmd = false) :
    suppressPrefix l r = (l, r) := by
  simp [suppressPrefix, suppressSigStart, hll,
    resetKillComparison, suppressSigMoveReset, hlreset, hrreset]

private theorem suppressSigEcho_capClockPair2 (l r : AgentState 2) :
    capClockPair2 (suppressSigEcho l r) = capClockPair2 (l, r) := by
  unfold suppressSigEcho capClockPair2 capClock2
  repeat (first | rfl | split)

private theorem suppressSigFinish_capClockPair2 (l r : AgentState 2) :
    capClockPair2 (suppressSigFinish l r) = capClockPair2 (l, r) := by
  unfold suppressSigFinish capClockPair2 capClock2
  split <;> rfl

private theorem suppressWidth_quiet_capClockPair2
    (l r : AgentState 2)
    (hll : l.leader = false)
    (hlreset : l.reset_cmd = false)
    (hrreset : r.reset_cmd = false) :
    capClockPair2
        (suppressSigResetKillWidth h2 h2 hle2 l r) =
      capClockPair2 (l, r) := by
  have hp := suppressPrefix_eq_of_quiet l r hll hlreset hrreset
  have hc : shortCountReset h2 hle2 l r = (l, r) := by
    simp [shortCountReset, hrreset]
  have ht : suppressSigTerminal h2 l r = (l, r) := by
    simp [suppressSigTerminal, hrreset]

  unfold suppressSigResetKillWidth
  rw [hp]
  dsimp only
  rw [hc]
  dsimp only
  rw [ht]
  dsimp only
  exact (suppressSigFinish_capClockPair2
      (suppressSigEcho l r).1 (suppressSigEcho l r).2).trans
    (suppressSigEcho_capClockPair2 l r)

private theorem authorizedSuppressWidth_quiet_capClockPair2
    (l r : AuthorizedAgentState 2)
    (hll : l.core.leader = false)
    (hlreset : l.core.reset_cmd = false)
    (hrreset : r.core.reset_cmd = false) :
    authCapClockPair2
        (authorizedSuppressWidth h2 h2 hle2 l r) =
      authCapClockPair2 (l, r) := by
  change capClockPair2
      (suppressSigResetKillWidth h2 h2 hle2 l.core r.core) =
    capClockPair2 (l.core, r.core)
  exact suppressWidth_quiet_capClockPair2
    l.core r.core hll hlreset hrreset

/-! ## Stationary persistent WRITE: label/count/WAIT frame -/

private theorem persistentClear_capClock2 (u : AgentState 2) :
    capClock2 (clearIncrementAction u) = capClock2 u := by
  unfold clearIncrementAction capClock2
  split <;> rfl

private theorem persistentReady_capClock2 (u : AgentState 2) :
    capClock2 (writeSeqSetWriteReadyTransport u) = capClock2 u := by
  unfold writeSeqSetWriteReadyTransport capClock2
  repeat (first | rfl | split)

private theorem persistentReadyPair_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (writeSeqReadyTransport l r) =
      capClockPair2 (l, r) := by
  unfold writeSeqReadyTransport
  exact Prod.ext (persistentReady_capClock2 l)
    (persistentReady_capClock2 r)

private theorem persistentGroupStart_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (groupInfoStart h2 l r) = capClockPair2 (l, r) := by
  unfold capClockPair2 capClock2 groupInfoStart
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem persistentGroupSet_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (groupInfoSet h2 l r) = capClockPair2 (l, r) := by
  unfold capClockPair2 capClock2 groupInfoSet
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem persistentGroupUnset_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (groupInfoUnset l r) = capClockPair2 (l, r) := by
  unfold capClockPair2 capClock2 groupInfoUnset
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem persistentGroup_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (groupInfo h2 l r) = capClockPair2 (l, r) := by
  rw [groupInfo_eq_staged]
  let q0 := groupInfoStart h2 l r
  let q1 := groupInfoSet h2 q0.1 q0.2
  exact (persistentGroupUnset_capClockPair2 q1.1 q1.2).trans
    ((persistentGroupSet_capClockPair2 q0.1 q0.2).trans
      (persistentGroupStart_capClockPair2 l r))

private theorem persistentGenStart_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (gensigWriteseqStart h2 l r) =
      capClockPair2 (l, r) := by
  unfold capClockPair2 capClock2 gensigWriteseqStart
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem persistentGenEmit_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (gensigWriteseqEmit h2 l r) =
      capClockPair2 (l, r) := by
  unfold capClockPair2 capClock2 gensigWriteseqEmit
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem persistentGenPropagate_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (gensigWriteseqPropagate h2 l r) =
      capClockPair2 (l, r) := by
  unfold capClockPair2 capClock2 gensigWriteseqPropagate
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem persistentGenFinish_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (gensigWriteseqFinish h2 l r) =
      capClockPair2 (l, r) := by
  unfold capClockPair2 capClock2 gensigWriteseqFinish
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem persistentGenerate_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (writeSeqGenerate h2 l r) =
      capClockPair2 (l, r) := by
  unfold writeSeqGenerate
  split
  · rw [gensigWriteseq_eq_staged]
    let q0 := gensigWriteseqStart h2 l r
    let q1 := gensigWriteseqEmit h2 q0.1 q0.2
    let q2 := gensigWriteseqPropagate h2 q1.1 q1.2
    exact (persistentGenFinish_capClockPair2 q2.1 q2.2).trans
      ((persistentGenPropagate_capClockPair2 q1.1 q1.2).trans
        ((persistentGenEmit_capClockPair2 q0.1 q0.2).trans
          (persistentGenStart_capClockPair2 l r)))
  · rfl

private theorem persistentCheckBit_capClock2 (u : AgentState 2) :
    capClock2 (writeSeqCheckBit u) = capClock2 u := by
  unfold writeSeqCheckBit
  cases u.path3 <;> rfl

private theorem persistentCompare_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (writeSeqCompare h2 l r) = capClockPair2 (l, r) := by
  unfold writeSeqCompare
  simp only [capClockPair2, capClockIte,
    persistentCheckBit_capClock2, ite_self]

private theorem persistentSetWriteAct_capClock2 (u : AgentState 2) :
    capClock2 (writeSeqSetWriteAct u) = capClock2 u := by
  apply capClock2_ext
  all_goals
    unfold capClock2 writeSeqSetWriteAct
    try dsimp only []
    repeat (first | rfl | split)

private theorem persistentFinalR_capClock2 (u : AgentState 2) :
    capClock2 (writeSeqFinalR u) = capClock2 u := by
  apply capClock2_ext
  all_goals
    unfold capClock2 writeSeqFinalR
    try dsimp only []
    repeat (first | rfl | split)

private theorem persistentCommands_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (writeSeqCommands h2 l r) = capClockPair2 (l, r) := by
  unfold writeSeqCommands
  simp only [capClockPair2, capClockIte,
    persistentSetWriteAct_capClock2, persistentFinalR_capClock2, ite_self]


private theorem persistentPrepare_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (writeSeqPrepareTransport h2 l r) =
      capClockPair2 (l, r) := by
  let q0 := writeSeqReadyTransport l r
  let q1 := writeSeqCompare h2 q0.1 q0.2
  exact (persistentCommands_capClockPair2 q1.1 q1.2).trans
    ((persistentCompare_capClockPair2 q0.1 q0.2).trans
      (persistentReadyPair_capClockPair2 l r))

private theorem persistentThroughPrepare_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (swPersistentThroughPrepare h2 l r) =
      capClockPair2 (l, r) := by
  let q0 := clearInputIncrementPair l r
  let q1 := groupInfo h2 q0.1 q0.2
  let q2 := writeSeqGenerate h2 q1.1 q1.2
  have h0 : capClockPair2 q0 = capClockPair2 (l, r) :=
    Prod.ext (persistentClear_capClock2 l) (persistentClear_capClock2 r)
  exact (persistentPrepare_capClockPair2 q2.1 q2.2).trans
    ((persistentGenerate_capClockPair2 q1.1 q1.2).trans
      ((persistentGroup_capClockPair2 q0.1 q0.2).trans h0))

attribute [local irreducible] swPersistentThroughPrepare

private theorem persistentGate_capClock2 (u : AgentState 2) :
    capClock2 (gatePreparedIncrement u) = capClock2 u := by
  apply capClock2_ext
  all_goals
    unfold capClock2 gatePreparedIncrement clearIncrementAction
    try dsimp only []
    repeat (first | rfl | split)

private theorem persistentActivate_capClock2 (u : AgentState 2) :
    capClock2 (writeActionActivateNonempty h2 u) = capClock2 u := by
  unfold writeActionActivateNonempty capClock2
  split <;> rfl

private theorem persistentIncrement_capClock2 (u : AgentState 2) :
    capClock2 (writeActionApplyIncrementAndFlip u) = capClock2 u := by
  apply capClock2_ext
  all_goals
    unfold capClock2 writeActionApplyIncrementAndFlip
    try dsimp only []
    repeat (first | rfl | (split <;> try dsimp only []))

private theorem persistentPropagate_capClock2
    (u : AgentState 2) (s : WriteState) :
    capClock2 (writeActionPropagateState u s) = capClock2 u := by
  cases s <;> rfl

private theorem persistentOverwrite_capClock2 (u : AgentState 2) :
    capClock2 (writeActionApplyOverwrite u) = capClock2 u := by
  unfold writeActionApplyOverwrite
  cases u.path3 <;> rfl

private theorem persistentMoveFlip_capClock2 (u : AgentState 2) :
    capClock2 (writeActionApplyMoveFlip u) = capClock2 u := by
  unfold writeActionApplyMoveFlip
  cases u.path3 <;> rfl

attribute [local irreducible]
  writeActionApplyOverwrite writeActionApplyMoveFlip
  writeActionApplyIncrementAndFlip writeActionPropagateState

private theorem persistentExecute_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (writeActionExecutePreservingDepart h2 l r) =
      capClockPair2 (l, r) := by
  unfold writeActionExecutePreservingDepart
  split
  · simp only [capClockPair2, capClockIte, capClockSetWriteState,
      persistentPropagate_capClock2, persistentOverwrite_capClock2,
      persistentMoveFlip_capClock2, persistentIncrement_capClock2,
      ite_self]
  · rfl

private theorem persistentAction_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (writeActionPreservingComparison h2 l r) =
      capClockPair2 (l, r) := by
  let l0 := writeActionActivateNonempty h2 l
  let r0 := writeActionActivateNonempty h2 r
  have he :
      capClockPair2
          (writeActionExecutePreservingComparison h2 l0 r0) =
        capClockPair2 (l0, r0) := by
    unfold writeActionExecutePreservingComparison
    split
    · rfl
    · exact persistentExecute_capClockPair2 l0 r0
  exact he.trans
    (Prod.ext (persistentActivate_capClock2 l)
      (persistentActivate_capClock2 r))

private theorem persistentMoveStart_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (moveWsigStart l r) = capClockPair2 (l, r) := by
  unfold capClockPair2 capClock2 moveWsigStart moveWsigCheckGenWs
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem persistentMoveLast_capClock2 (u : AgentState 2) :
    capClock2 (moveWsigCheckLast u) = capClock2 u := by
  unfold capClock2 moveWsigCheckLast
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem persistentTransfer_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (moveWsigTransferStopAligned l r) =
      capClockPair2 (l, r) := by
  unfold capClockPair2 capClock2 moveWsigTransferStopAligned
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem persistentMoveWrite_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (moveWsigMoveWritePreservingNonempty l r) =
      capClockPair2 (l, r) := by
  unfold moveWsigMoveWritePreservingNonempty
  split <;> rfl

private theorem persistentLeaderSignal_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (moveWsigLeaderSignal l r) = capClockPair2 (l, r) := by
  unfold capClockPair2 capClock2 moveWsigLeaderSignal
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem persistentSignalMove_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (moveWsigSignalMove l r) = capClockPair2 (l, r) := by
  unfold capClockPair2 capClock2 moveWsigSignalMove
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem persistentEchoMove_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (moveWsigEchoMove l r) = capClockPair2 (l, r) := by
  unfold capClockPair2 capClock2 moveWsigEchoMove
  try dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem persistentMove_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (moveWsigStopAligned h2 l r) =
      capClockPair2 (l, r) := by
  let q0 := moveWsigStart l r
  let q1 := (moveWsigCheckLast q0.1, q0.2)
  let q2 := moveWsigTransferStopAligned q1.1 q1.2
  let q3 := moveWsigMoveWritePreservingNonempty q2.1 q2.2
  let q4 := moveWsigLeaderSignal q3.1 q3.2
  let q5 := moveWsigSignalMove q4.1 q4.2
  have hlast : capClockPair2 q1 = capClockPair2 q0 :=
    Prod.ext (persistentMoveLast_capClock2 q0.1) rfl
  exact (persistentEchoMove_capClockPair2 q5.1 q5.2).trans
    ((persistentSignalMove_capClockPair2 q4.1 q4.2).trans
      ((persistentLeaderSignal_capClockPair2 q3.1 q3.2).trans
        ((persistentMoveWrite_capClockPair2 q2.1 q2.2).trans
          ((persistentTransfer_capClockPair2 q1.1 q1.2).trans
            (hlast.trans (persistentMoveStart_capClockPair2 l r))))))

private theorem stationaryPersistentRaw_capClockPair2
    (l r : AgentState 2) :
    capClockPair2 (stationaryPersistentRaw h2 l r) =
      capClockPair2 (l, r) := by
  let q := swPersistentThroughPrepare h2 l r
  let g := (gatePreparedIncrement q.1, gatePreparedIncrement q.2)
  let w := writeActionPreservingComparison h2 g.1 g.2
  have hg : capClockPair2 g = capClockPair2 q :=
    Prod.ext (persistentGate_capClock2 q.1)
      (persistentGate_capClock2 q.2)
  exact (persistentMove_capClockPair2 w.1 w.2).trans
    ((persistentAction_capClockPair2 g.1 g.2).trans
      (hg.trans (persistentThroughPrepare_capClockPair2 l r)))

attribute [local irreducible] stationaryPersistentRaw

private theorem stationaryPersistentAuthorizedRow_capClockPair2
    (l r : AuthorizedAgentState 2) :
    authCapClockPair2 (stationaryPersistentAuthorizedRow h2 l r) =
      authCapClockPair2 (l, r) := by
  have hc := stationaryPersistentAuthorizedRow_core h2 l r
  have hraw := stationaryPersistentRaw_capClockPair2 l.core r.core
  exact (congrArg capClockPair2 hc).trans hraw

/-! ## The actual computed CHECK cut through afterCheckMetadataWidth -/

private theorem afterCheckMetadataWidth_quiet_capClockPair2
    (l r : AuthorizedAgentState 2)
    (hll : l.core.leader = false)
    (hlreset : l.core.reset_cmd = false)
    (hrreset : r.core.reset_cmd = false) :
    authCapClockPair2
        (afterCheckMetadataWidth h2 h2 hle2 l r) =
      authCapClockPair2 (l, r) := by
  let q0 := authorizedDisappear h2 l r
  let q1 := authorizedCompareSigActionOne h2 q0.1 q0.2
  let q2 := authorizedSuppressWidth h2 h2 hle2 q1.1 q1.2
  let q6 := stationaryPersistentAuthorizedRow h2 q2.1 q2.2

  have h0 := authorizedDisappear_capClockPair2 l r
  change authCapClockPair2 q0 = authCapClockPair2 (l, r) at h0
  have h1 := authorizedCompareSigActionOne_capClockPair2 q0.1 q0.2
  change authCapClockPair2 q1 = authCapClockPair2 q0 at h1

  have h0Leaders :=
    PPLLWallSweepPreCheckResetContracts.authorizedDisappear_leaders_eq
      h2 l r
  have h1Leaders :=
    PPLLCompleteMultiLeaderCleanup.compareActionOne_leaders
      h2 q0.1 q0.2
  have hq1LeftFollower : q1.1.core.leader = false :=
    h1Leaders.1.trans (h0Leaders.1.trans hll)

  have h0Reset :=
    PPLLWallSweepNormalResetContract.authorizedDisappear_resetEchoPair
      h2 l r
  have h1Reset :=
    PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne_resetEchoPair
      h2 q0.1 q0.2
  have hresetFields :=
    PPLLWallSweepNormalResetContract.resetEcho_fields_of_pair_eq
      (h1Reset.trans h0Reset)
  have hq1LeftReset : q1.1.core.reset_cmd = false :=
    hresetFields.1.trans hlreset
  have hq1RightReset : q1.2.core.reset_cmd = false :=
    hresetFields.2.2.1.trans hrreset

  have h2frame := authorizedSuppressWidth_quiet_capClockPair2
    q1.1 q1.2 hq1LeftFollower hq1LeftReset hq1RightReset
  change authCapClockPair2 q2 = authCapClockPair2 q1 at h2frame

  have h6frame := stationaryPersistentAuthorizedRow_capClockPair2
    q2.1 q2.2
  change authCapClockPair2 q6 = authCapClockPair2 q2 at h6frame

  change authCapClockPair2 q6 = authCapClockPair2 (l, r)
  exact h6frame.trans (h2frame.trans (h1.trans h0))

private theorem afterCheckMetadataWidth_cap_frame_of_input
    (ecount : Nat)
    (q5 : AuthorizedAgentState 2 × AuthorizedAgentState 2)
    (h5LL : q5.1.core.label = 0)
    (h5RL : q5.2.core.label = 1)
    (h5RC : q5.2.core.count = ecount)
    (h5LW : q5.1.core.wait = true)
    (h5RW : q5.2.core.wait = true)
    (h5LLeader : q5.1.core.leader = false)
    (h5LReset : q5.1.core.reset_cmd = false)
    (h5RReset : q5.2.core.reset_cmd = false) :
    let q6 := afterCheckMetadataWidth h2 h2 hle2 q5.1 q5.2
    q6.1.core.label = 0 /\
      q6.2.core.label = 1 /\
      q6.2.core.count = ecount /\
      q6.1.core.wait = true /\
      q6.2.core.wait = true := by
  let q6 := afterCheckMetadataWidth h2 h2 hle2 q5.1 q5.2
  have hf := afterCheckMetadataWidth_quiet_capClockPair2
    q5.1 q5.2 h5LLeader h5LReset h5RReset
  change authCapClockPair2 q6 = authCapClockPair2 q5 at hf
  have hv := authCapClockPair2_fields q6 q5 hf
  exact ⟨hv.1.trans h5LL,
    hv.2.1.trans h5RL,
    hv.2.2.1.trans h5RC,
    hv.2.2.2.1.trans h5LW,
    hv.2.2.2.2.trans h5RW⟩

/-- Actual R3 CHECK-cut consumer.  No assumption is made about responder leader
    or either post-CHECK path2 field. -/
theorem afterCheckMetadataWidth_checkCut_cap_frame
    (d e : Registers 2)
    (hd : d.label = 0) (he : e.label = 1)
    (hwd : d.wait = false) (hwe : e.wait = true) :
    let q5 := BirthShortDoneTerminalCapGeneralR3.postWaitDone2CheckCut d e
    let q6 := afterCheckMetadataWidth h2 h2 hle2 q5.1 q5.2
    q6.1.core.label = 0 /\
      q6.2.core.label = 1 /\
      q6.2.core.count = e.count /\
      q6.1.core.wait = true /\
      q6.2.core.wait = true := by
  have h5 :=
    BirthShortDoneTerminalCapGeneralR3.postWaitDone2CheckCut_cap_frame
      d e hd he hwd hwe
  rcases h5 with
    ⟨h5LL, h5RL, h5RC, h5LW, h5RW,
      h5LLeader, h5LReset, h5RReset⟩
  simpa only using
    (afterCheckMetadataWidth_cap_frame_of_input
      e.count
      (BirthShortDoneTerminalCapGeneralR3.postWaitDone2CheckCut d e)
      h5LL h5RL h5RC h5LW h5RW
      h5LLeader h5LReset h5RReset)

private def postWaitDone2AfterCheckCut (d e : Registers 2) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let q5 := BirthShortDoneTerminalCapGeneralR3.postWaitDone2CheckCut d e
  afterCheckMetadataWidth h2 h2 hle2 q5.1 q5.2

private theorem postWaitDone2AfterCheckCut_cap_frame
    (d e : Registers 2)
    (hd : d.label = 0) (he : e.label = 1)
    (hwd : d.wait = false) (hwe : e.wait = true) :
    let q6 := postWaitDone2AfterCheckCut d e
    q6.1.core.label = 0 /\
      q6.2.core.label = 1 /\
      q6.2.core.count = e.count /\
      q6.1.core.wait = true /\
      q6.2.core.wait = true := by
  simpa only [postWaitDone2AfterCheckCut] using
    afterCheckMetadataWidth_checkCut_cap_frame d e hd he hwd hwe

private theorem postWaitDone2_factor_afterCheckCut
    (a b d e : Registers 2) (pa pb : Bool) :
    BirthShortDoneTerminalCapGeneralR2.postWaitDone2 a b d e pa pb =
      let q6 := postWaitDone2AfterCheckCut d e
      markLeaderBirth
        (authBirth ⟨cell a, pa⟩ ⟨cell b, pb⟩ q6) q6 := by
  simpa only [postWaitDone2AfterCheckCut] using
    BirthShortDoneTerminalCapGeneralR3.postWaitDone2_factor_check_cut
      a b d e pa pb

attribute [local irreducible] postWaitDone2AfterCheckCut

private theorem markComparisonForDeletion_capClock2
    (u : AuthorizedAgentState 2) :
    capClock2 (markComparisonForDeletion u).core = capClock2 u.core := by
  unfold markComparisonForDeletion capClock2
  split <;> rfl

private theorem markLeaderBirth_capClockPair2
    (born : Bool)
    (q : AuthorizedAgentState 2 × AuthorizedAgentState 2) :
    authCapClockPair2 (markLeaderBirth born q) = authCapClockPair2 q := by
  unfold markLeaderBirth
  split
  · exact Prod.ext
      (markComparisonForDeletion_capClock2 q.1)
      (markComparisonForDeletion_capClock2 q.2)
  · rfl

private theorem markLeaderBirth_cap_frame_of_pair
    (ecount : Nat)
    (q : AuthorizedAgentState 2 × AuthorizedAgentState 2)
    (born : Bool)
    (h : q.1.core.label = 0 /\
      q.2.core.label = 1 /\
      q.2.core.count = ecount /\
      q.1.core.wait = true /\
      q.2.core.wait = true) :
    let out := markLeaderBirth born q
    out.1.core.label = 0 /\
      out.2.core.label = 1 /\
      out.2.core.count = ecount /\
      out.1.core.wait = true /\
      out.2.core.wait = true := by
  rcases h with ⟨hLL, hRL, hRC, hLW, hRW⟩
  have hm := markLeaderBirth_capClockPair2 born q
  have hv := authCapClockPair2_fields (markLeaderBirth born q) q hm
  exact ⟨hv.1.trans hLL,
    hv.2.1.trans hRL,
    hv.2.2.1.trans hRC,
    hv.2.2.2.1.trans hLW,
    hv.2.2.2.2.trans hRW⟩

/-- Strong final cap-clock frame for the unchanged R2 helper.  `authBirth` is
    evaluated normally; no no-birth branch is assumed. -/
theorem postWaitDone2_cap_clock_frame
    (a b d e : Registers 2) (pa pb : Bool)
    (hd : d.label = 0) (he : e.label = 1)
    (hwd : d.wait = false) (hwe : e.wait = true) :
    let out :=
      BirthShortDoneTerminalCapGeneralR2.postWaitDone2
        a b d e pa pb
    out.1.core.label = 0 /\
      out.2.core.label = 1 /\
      out.2.core.count = e.count /\
      out.1.core.wait = true /\
      out.2.core.wait = true := by
  let q6 := postWaitDone2AfterCheckCut d e
  have h6 := postWaitDone2AfterCheckCut_cap_frame
    d e hd he hwd hwe
  change q6.1.core.label = 0 /\
    q6.2.core.label = 1 /\
    q6.2.core.count = e.count /\
    q6.1.core.wait = true /\
    q6.2.core.wait = true at h6

  have hout := markLeaderBirth_cap_frame_of_pair
    e.count q6
      (authBirth ⟨cell a, pa⟩ ⟨cell b, pb⟩ q6) h6

  have hfactor := postWaitDone2_factor_afterCheckCut
    a b d e pa pb
  change
    BirthShortDoneTerminalCapGeneralR2.postWaitDone2 a b d e pa pb =
      markLeaderBirth
        (authBirth ⟨cell a, pa⟩ ⟨cell b, pb⟩ q6) q6 at hfactor
  rw [hfactor]
  exact hout

/-- Original endpoint shape, now reduced to the bounded R4 cap-clock frame. -/
theorem postWaitDone2_cap_frame
    (a b d e : Registers 2) (pa pb : Bool)
    (hd : d.label = 0) (he : e.label = 1)
    (hwd : d.wait = false) (hwe : e.wait = true) :
    let q :=
      BirthShortDoneTerminalCapGeneralR2.postWaitDone2
        a b d e pa pb
    q.2.core.count = e.count /\
      q.1.core.wait = true /\ q.2.core.wait = true := by
  have h := postWaitDone2_cap_clock_frame
    a b d e pa pb hd he hwd hwe
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

#print axioms BirthShortDoneTerminalCapGeneralR4.afterCheckMetadataWidth_checkCut_cap_frame
#print axioms BirthShortDoneTerminalCapGeneralR4.postWaitDone2_cap_clock_frame
#print axioms BirthShortDoneTerminalCapGeneralR4.postWaitDone2_cap_frame

end BirthShortDoneTerminalCapGeneralR4
