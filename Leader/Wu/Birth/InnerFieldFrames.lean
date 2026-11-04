import Leader.Wu.Birth.InnerCountFrames

set_option autoImplicit false

namespace BirthB1InnerFieldFrames

open PPLLWallSweepFinite PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair BirthCheckCongestGuardRepair PPLLCompleteMultiLeaderCleanup BirthShortDoneCuts BirthArrivalCaptureRepair BirthGenerationControlRepair BirthGenerationDone BirthShortWait BirthShortWaitTerminalEntryRepair BirthSingleUseReleaseRepair BirthStationaryWrite BirthTossCheckPreservationRepair PPLL PPLLLeaderCreationCleanupRepair PPLLRepair PPLLTerminalEqualSupportRepair PPLLWallSweepPreCheckResetRepair PPLLWallSweepRepair PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair

variable {ψ psi κ kappa τ tau width n : Nat}

/-- Authorization reconciliation keeps the raw pair. -/
theorem authorizedReconcile_core_leader_reset_cmd (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthorizedAgentState ψ) :
    (authorizedReconcile f l r).1.core = (f l.core r.core).1 ∧
      (authorizedReconcile f l r).2.core = (f l.core r.core).2 := ⟨rfl, rfl⟩

-- Repairs.lean:1085
theorem compareBitUpdateRActionOne_reset_cmd {ψ : Nat} (hψ : ψ > 0) (r : AgentState ψ) :
    (compareBitUpdateRActionOne hψ r).reset_cmd = r.reset_cmd := by
  unfold compareBitUpdateRActionOne
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- WriteSeqPersistenceRepair.lean:74
theorem writeSeqSetWriteReadyTransport_reset_cmd (u : AgentState ψ) :
    (writeSeqSetWriteReadyTransport u).reset_cmd = u.reset_cmd := by
  unfold writeSeqSetWriteReadyTransport
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:982
theorem writeSeqSetWriteAct_reset_cmd (u : AgentState ψ) :
    (writeSeqSetWriteAct u).reset_cmd = u.reset_cmd := by
  unfold writeSeqSetWriteAct
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:992
theorem writeSeqFinalR_reset_cmd (r : AgentState ψ) :
    (writeSeqFinalR r).reset_cmd = r.reset_cmd := by
  unfold writeSeqFinalR
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:977
theorem writeSeqCheckBit_reset_cmd (r : AgentState ψ) :
    (writeSeqCheckBit r).reset_cmd = r.reset_cmd := by
  unfold writeSeqCheckBit
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:785
theorem writeActionApplyOverwrite_reset_cmd (r : AgentState ψ) :
    (writeActionApplyOverwrite r).reset_cmd = r.reset_cmd := by
  unfold writeActionApplyOverwrite
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:792
theorem writeActionApplyMoveFlip_reset_cmd (r : AgentState ψ) :
    (writeActionApplyMoveFlip r).reset_cmd = r.reset_cmd := by
  unfold writeActionApplyMoveFlip
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Repairs.lean:153
theorem genSigSaturatedFinish_reset_cmd {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (genSigSaturatedFinish hψ l r).1.reset_cmd = l.reset_cmd ∧ (genSigSaturatedFinish hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold genSigSaturatedFinish
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- WallSweepRepair.lean:25
theorem clearComparisonSignal_reset_cmd (u : AgentState ψ) :
    (clearComparisonSignal u).reset_cmd = u.reset_cmd := by
  unfold clearComparisonSignal
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, ])

-- WallSweepRepair.lean:60
theorem resetKillComparison_reset_cmd (u : AgentState ψ) :
    (resetKillComparison u).reset_cmd = u.reset_cmd := by
  unfold resetKillComparison
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd])

-- WallSweepRepair.lean:429
theorem clearIfLeader_reset_cmd (u : AgentState ψ) :
    (clearIfLeader u).reset_cmd = u.reset_cmd := by
  unfold clearIfLeader
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd])

-- WriteIncrementGate.lean:28
theorem clearIncrementAction_reset_cmd (u : AgentState ψ) :
    (clearIncrementAction u).reset_cmd = u.reset_cmd := by
  unfold clearIncrementAction
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd])

-- Algorithm.lean:436
theorem compareSigInit_reset_cmd (l : AgentState ψ) :
    (compareSigInit l).reset_cmd = l.reset_cmd := by
  unfold compareSigInit
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd])

-- Algorithm.lean:121
theorem cleanSigGenConnect_reset_cmd (u : AgentState ψ) :
    (cleanSigGenConnect u).reset_cmd = u.reset_cmd := by
  unfold cleanSigGenConnect
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd])

-- Algorithm.lean:147
theorem cleanSigStep3_reset_cmd (l r : AgentState ψ) :
    (cleanSigStep3 l r).1.reset_cmd = l.reset_cmd ∧ (cleanSigStep3 l r).2.reset_cmd = r.reset_cmd := by
  unfold cleanSigStep3
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd])

-- Algorithm.lean:157
theorem cleanSigStep4_reset_cmd (l r : AgentState ψ) :
    (cleanSigStep4 l r).1.reset_cmd = l.reset_cmd ∧ (cleanSigStep4 l r).2.reset_cmd = r.reset_cmd := by
  unfold cleanSigStep4
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd])

-- Algorithm.lean:167
theorem cleanSigStep5_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).1.reset_cmd = l.reset_cmd ∧ (cleanSigStep5 hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold cleanSigStep5
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd])

-- Algorithm.lean:177
theorem cleanSigStep6_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).1.reset_cmd = l.reset_cmd ∧ (cleanSigStep6 hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold cleanSigStep6
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd])

-- Algorithm.lean:129
theorem cleanSigCleanApply_reset_cmd (u : AgentState ψ) :
    (cleanSigCleanApply u).reset_cmd = u.reset_cmd := by
  unfold cleanSigCleanApply
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd])

-- Algorithm.lean:226
theorem checkSigSetReady_reset_cmd (u : AgentState ψ) :
    (checkSigSetReady u).reset_cmd = u.reset_cmd := by
  unfold checkSigSetReady
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd])

-- Algorithm.lean:235
theorem checkSigCheckL_reset_cmd (hψ : ψ > 0) (u : AgentState ψ) :
    (checkSigCheckL hψ u).reset_cmd = u.reset_cmd := by
  unfold checkSigCheckL
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd])

-- Algorithm.lean:243
theorem checkSigCheckR_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).reset_cmd = r.reset_cmd := by
  unfold checkSigCheckR
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd])

-- Algorithm.lean:253
theorem checkSigSetResult_reset_cmd (u : AgentState ψ) :
    (checkSigSetResult u).reset_cmd = u.reset_cmd := by
  unfold checkSigSetResult
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd])

-- Algorithm.lean:262
theorem checkSigSetLeader_reset_cmd (hψ : ψ > 0) (r : AgentState ψ) :
    (checkSigSetLeader hψ r).reset_cmd = r.reset_cmd := by
  unfold checkSigSetLeader
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd])

-- Algorithm.lean:30
theorem pPsi_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (pPsi hψ l r).1.reset_cmd = l.reset_cmd ∧ (pPsi hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold pPsi
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd])

-- Algorithm.lean:201
theorem eliminateSig_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.reset_cmd = l.reset_cmd ∧ (eliminateSig hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold eliminateSig
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd])

-- Algorithm.lean:338
theorem disappear_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (disappear hψ l r).1.reset_cmd = l.reset_cmd ∧ (disappear hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold disappear
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd])

-- Algorithm.lean:403
theorem compareBitUpdateL_reset_cmd (hψ : ψ > 0) (l : AgentState ψ) :
    (compareBitUpdateL hψ l).reset_cmd = l.reset_cmd := by
  unfold compareBitUpdateL
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd])

-- Algorithm.lean:411
theorem compareBitUpdateR_reset_cmd (hψ : ψ > 0) (r : AgentState ψ) :
    (compareBitUpdateR hψ r).reset_cmd = r.reset_cmd := by
  unfold compareBitUpdateR
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd])

-- Algorithm.lean:428
theorem compareBit_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareBit hψ l r).1.reset_cmd = l.reset_cmd ∧ (compareBit hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold compareBit
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd])

-- MultiLeaderCleanup.lean:53
theorem compareBitActionOne_reset_cmd (hpsi : psi > 0) (l r : AgentState psi) :
    (compareBitActionOne hpsi l r).1.reset_cmd = l.reset_cmd ∧ (compareBitActionOne hpsi l r).2.reset_cmd = r.reset_cmd := by
  unfold compareBitActionOne
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd])

-- BirthArrivalCaptureRepair.lean:28
theorem captureStep1_reset_cmd (l r : AgentState psi) :
    (captureStep1 l r).1.reset_cmd = l.reset_cmd ∧ (captureStep1 l r).2.reset_cmd = r.reset_cmd := by
  unfold captureStep1
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd])

-- BirthGenerationDone.lean:66
theorem holdDoneStep1_reset_cmd (l r : AgentState psi) :
    (holdDoneStep1 l r).1.reset_cmd = l.reset_cmd ∧ (holdDoneStep1 l r).2.reset_cmd = r.reset_cmd := by
  unfold holdDoneStep1
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd])

-- Algorithm.lean:482
theorem sigMoveStep2_reset_cmd (l r : AgentState ψ) :
    (sigMoveStep2 l r).1.reset_cmd = l.reset_cmd ∧ (sigMoveStep2 l r).2.reset_cmd = r.reset_cmd := by
  unfold sigMoveStep2
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd])

-- Algorithm.lean:491
theorem sigMoveStep3_reset_cmd (l r : AgentState ψ) :
    (sigMoveStep3 l r).1.reset_cmd = l.reset_cmd ∧ (sigMoveStep3 l r).2.reset_cmd = r.reset_cmd := by
  unfold sigMoveStep3
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd])

-- Algorithm.lean:500
theorem sigMoveStep4_reset_cmd (l r : AgentState ψ) :
    (sigMoveStep4 l r).1.reset_cmd = l.reset_cmd ∧ (sigMoveStep4 l r).2.reset_cmd = r.reset_cmd := by
  unfold sigMoveStep4
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd])

-- Algorithm.lean:508
theorem sigMoveStep5_reset_cmd (l r : AgentState ψ) :
    (sigMoveStep5 l r).1.reset_cmd = l.reset_cmd ∧ (sigMoveStep5 l r).2.reset_cmd = r.reset_cmd := by
  unfold sigMoveStep5
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd])

-- BirthSingleUseReleaseRepair.lean:103
theorem singleUseApplyControl_reset_cmd (hpsi : psi > 0) (u : AgentState psi) :
    (singleUseApplyControl hpsi u).reset_cmd = u.reset_cmd := by
  unfold singleUseApplyControl
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd])

-- WriteIncrementGate.lean:33
theorem gatePreparedIncrement_reset_cmd (u : AgentState ψ) :
    (gatePreparedIncrement u).reset_cmd = u.reset_cmd := by
  unfold gatePreparedIncrement
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd])

-- WriteSeqPersistenceRepair.lean:215
theorem writeActionActivateNonempty_reset_cmd (hψ : ψ > 0) (u : AgentState ψ) :
    (writeActionActivateNonempty hψ u).reset_cmd = u.reset_cmd := by
  unfold writeActionActivateNonempty
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd])

-- WriteSeqPersistenceRepair.lean:177
theorem writeActionApplyIncrementAndFlip_reset_cmd (r : AgentState ψ) :
    (writeActionApplyIncrementAndFlip r).reset_cmd = r.reset_cmd := by
  unfold writeActionApplyIncrementAndFlip
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, writeActionApplyIncrementAndFlip_reset_cmd, writeActionPropagateState_reset_cmd])

-- WriteSeqPersistenceRepair.lean:225
theorem writeActionPropagateState_reset_cmd (l : AgentState ψ) (state : WriteState) :
    (writeActionPropagateState l state).reset_cmd = l.reset_cmd := by
  unfold writeActionPropagateState
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, writeActionApplyIncrementAndFlip_reset_cmd, writeActionPropagateState_reset_cmd])

-- WriteSeqPersistenceRepair.lean:245
theorem writeActionExecutePreservingDepart_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeActionExecutePreservingDepart hψ l r).1.reset_cmd = l.reset_cmd ∧ (writeActionExecutePreservingDepart hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold writeActionExecutePreservingDepart
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [writeActionApplyIncrementAndFlip_reset_cmd, writeActionPropagateState_reset_cmd, compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd])

-- WriteSeqPersistenceRepair.lean:263
theorem writeActionPreservingDepart_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeActionPreservingDepart hψ l r).1.reset_cmd = l.reset_cmd ∧ (writeActionPreservingDepart hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold writeActionPreservingDepart
  try simp only []
  have h := writeActionExecutePreservingDepart_reset_cmd hψ (writeActionActivateNonempty hψ l) (writeActionActivateNonempty hψ r)
  rw [h.1, h.2, writeActionActivateNonempty_reset_cmd, writeActionActivateNonempty_reset_cmd]
  exact ⟨rfl, rfl⟩

-- WriteSeqPersistenceRepair.lean:283
theorem writeActionExecutePreservingComparison_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeActionExecutePreservingComparison hψ l r).1.reset_cmd = l.reset_cmd ∧ (writeActionExecutePreservingComparison hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold writeActionExecutePreservingComparison
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd])

-- WriteSeqPersistenceRepair.lean:139
theorem writeSeqReadyTransport_reset_cmd (l r : AgentState ψ) :
    (writeSeqReadyTransport l r).1.reset_cmd = l.reset_cmd ∧ (writeSeqReadyTransport l r).2.reset_cmd = r.reset_cmd := by
  unfold writeSeqReadyTransport
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd])

-- Algorithm.lean:1018
theorem writeSeqCompare_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqCompare hψ l r).1.reset_cmd = l.reset_cmd ∧ (writeSeqCompare hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold writeSeqCompare
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd])

-- Algorithm.lean:1030
theorem writeSeqCommands_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqCommands hψ l r).1.reset_cmd = l.reset_cmd ∧ (writeSeqCommands hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold writeSeqCommands
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd])

-- WriteSeqPersistenceRepair.lean:144
theorem writeSeqPrepareTransport_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqPrepareTransport hψ l r).1.reset_cmd = l.reset_cmd ∧ (writeSeqPrepareTransport hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold writeSeqPrepareTransport
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd])

-- Algorithm.lean:749
theorem gensigWriteseq_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (gensigWriteseq hψ l r).1.reset_cmd = l.reset_cmd ∧ (gensigWriteseq hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold gensigWriteseq
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd])

-- Algorithm.lean:668
theorem groupInfo_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (groupInfo hψ l r).1.reset_cmd = l.reset_cmd ∧ (groupInfo hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold groupInfo
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd])

-- Repairs.lean:61
theorem waitSaturatedPrepare_reset_cmd {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (waitSaturatedPrepare hψ l r).1.reset_cmd = l.reset_cmd ∧ (waitSaturatedPrepare hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold waitSaturatedPrepare
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd])

-- BirthShortWaitTerminalEntryRepair.lean:31
theorem terminalInactiveClear_reset_cmd {psi width : Nat} (hwidth : 0 < width) (hle : width ≤ psi) (l r : AgentState psi) :
    (terminalInactiveClear hwidth hle l r).1.reset_cmd = l.reset_cmd ∧ (terminalInactiveClear hwidth hle l r).2.reset_cmd = r.reset_cmd := by
  unfold terminalInactiveClear
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd])

-- BirthShortWait.lean:46
theorem waitWidthReset_reset_cmd {psi width : Nat} (hwidth : 0 < width) (hle : width <= psi) (l r : AgentState psi) :
    (waitWidthReset hwidth hle l r).1.reset_cmd = l.reset_cmd ∧ (waitWidthReset hwidth hle l r).2.reset_cmd = r.reset_cmd := by
  unfold waitWidthReset
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd])

-- BirthShortWait.lean:59
theorem waitWidthFinish_reset_cmd {psi width : Nat} (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi) (kappa : Nat) (l r : AgentState psi) :
    (waitWidthFinish hpsi hwidth hle kappa l r).1.reset_cmd = l.reset_cmd ∧ (waitWidthFinish hpsi hwidth hle kappa l r).2.reset_cmd = r.reset_cmd := by
  unfold waitWidthFinish
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd])

-- Repairs.lean:119
theorem genSigSaturatedStart_reset_cmd {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (genSigSaturatedStart hψ l r).1.reset_cmd = l.reset_cmd ∧ (genSigSaturatedStart hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold genSigSaturatedStart
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd])

-- BirthGenerationControlRepair.lean:27
theorem genCleanEmit_reset_cmd (hpsi : psi > 0) (l r : AgentState psi) :
    (genCleanEmit hpsi l r).1.reset_cmd = l.reset_cmd ∧ (genCleanEmit hpsi l r).2.reset_cmd = r.reset_cmd := by
  unfold genCleanEmit
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd])

-- BirthGenerationControlRepair.lean:39
theorem genCleanPropagate_reset_cmd (hpsi : psi > 0) (l r : AgentState psi) :
    (genCleanPropagate hpsi l r).1.reset_cmd = l.reset_cmd ∧ (genCleanPropagate hpsi l r).2.reset_cmd = r.reset_cmd := by
  unfold genCleanPropagate
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd])

-- suppressSigStart_reset_cmd removed: this stage writes the field

-- suppressSigMoveReset_reset_cmd removed: this stage writes the field

-- suppressSigEcho_reset_cmd removed: this stage writes the field

-- Algorithm.lean:561
theorem suppressSigFinish_reset_cmd (l r : AgentState ψ) :
    (suppressSigFinish l r).1.reset_cmd = l.reset_cmd ∧ (suppressSigFinish l r).2.reset_cmd = r.reset_cmd := by
  unfold suppressSigFinish
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd])

-- LeaderCreationCleanupRepair.lean:42
theorem normalizeDeletion_reset_cmd (u : AuthorizedAgentState ψ) :
    (normalizeDeletion u).core.reset_cmd = u.core.reset_cmd := by
  unfold normalizeDeletion
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd])

-- LeaderCreationCleanupRepair.lean:49
theorem markComparisonForDeletion_reset_cmd (u : AuthorizedAgentState ψ) :
    (markComparisonForDeletion u).core.reset_cmd = u.core.reset_cmd := by
  unfold markComparisonForDeletion
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd])

-- TerminalEqualSupportRepair.lean:62
theorem sanitizeAuthorizedTerminalEqual_reset_cmd (hψ : ψ > 0) (u : AuthorizedAgentState ψ) :
    (sanitizeAuthorizedTerminalEqual hψ u).core.reset_cmd = u.core.reset_cmd := by
  unfold sanitizeAuthorizedTerminalEqual
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd])

-- WallSweepPreCheckResetRepair.lean:35
theorem clearAuthorizedComparison_reset_cmd (u : AuthorizedAgentState psi) :
    (clearAuthorizedComparison u).core.reset_cmd = u.core.reset_cmd := by
  unfold clearAuthorizedComparison
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd])

-- AuthorizedComparisonRepair.lean:151
theorem cmpUpdateReturnPriority_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (cmpUpdateReturnPriority hψ l r).1.reset_cmd = l.reset_cmd ∧ (cmpUpdateReturnPriority hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold cmpUpdateReturnPriority
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd])

-- Algorithm.lean:386
theorem cmpUpdateSetPath2_reset_cmd (hψ : ψ > 0) (l : AgentState ψ) :
    (cmpUpdateSetPath2 hψ l).reset_cmd = l.reset_cmd := by
  unfold cmpUpdateSetPath2
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd])

-- Algorithm.lean:187
theorem cleanSig_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSig hψ l r).1.reset_cmd = l.reset_cmd ∧ (cleanSig hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold cleanSig
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd]

-- Algorithm.lean:277
theorem checkSig_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (checkSig hψ l r).1.reset_cmd = l.reset_cmd ∧ (checkSig hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold checkSig
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd]

-- WallSweepRepair.lean:116
theorem pPsiLeaderResetProbeWall_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (pPsiLeaderResetProbeWall hψ l r).1.reset_cmd = l.reset_cmd ∧ (pPsiLeaderResetProbeWall hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold pPsiLeaderResetProbeWall
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd]

-- WallSweepRepair.lean:74
theorem comparisonLeaderWall_reset_cmd (l r : AgentState ψ) :
    (comparisonLeaderWall l r).1.reset_cmd = l.reset_cmd ∧ (comparisonLeaderWall l r).2.reset_cmd = r.reset_cmd := by
  unfold comparisonLeaderWall
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd]

-- WallSweepRepair.lean:456
theorem sigMoveLeaderPreclear_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (sigMoveLeaderPreclear hψ l r).1.reset_cmd = l.reset_cmd ∧ (sigMoveLeaderPreclear hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold sigMoveLeaderPreclear
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd]

-- BirthGenerationDone.lean:81
theorem controlTransfers_reset_cmd (l r : AgentState psi) :
    (controlTransfers l r).1.reset_cmd = l.reset_cmd ∧ (controlTransfers l r).2.reset_cmd = r.reset_cmd := by
  unfold controlTransfers
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd]

-- BirthGenerationDone.lean:88
theorem doneTransfers_reset_cmd (l r : AgentState psi) :
    (doneTransfers l r).1.reset_cmd = l.reset_cmd ∧ (doneTransfers l r).2.reset_cmd = r.reset_cmd := by
  unfold doneTransfers
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd]

-- BirthSingleUseReleaseRepair.lean:137
theorem singleUseControlTail_reset_cmd (hpsi : psi > 0) (l r : AgentState psi) :
    (singleUseControlTail hpsi l r).1.reset_cmd = l.reset_cmd ∧ (singleUseControlTail hpsi l r).2.reset_cmd = r.reset_cmd := by
  unfold singleUseControlTail
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd]

-- BirthGenerationDone.lean:178
theorem doneCaptureSigMove_reset_cmd (hpsi : psi > 0) (l r : AgentState psi) :
    (doneCaptureSigMove hpsi l r).1.reset_cmd = l.reset_cmd ∧ (doneCaptureSigMove hpsi l r).2.reset_cmd = r.reset_cmd := by
  unfold doneCaptureSigMove
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd, singleUseControlTail_reset_cmd]

-- Algorithm.lean:441
theorem compareSigDispatch_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareSigDispatch hψ l r).1.reset_cmd = l.reset_cmd ∧ (compareSigDispatch hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold compareSigDispatch
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd, singleUseControlTail_reset_cmd, doneCaptureSigMove_reset_cmd]

-- MultiLeaderCleanup.lean:62
theorem compareSigDispatchActionOne_reset_cmd (hpsi : psi > 0) (l r : AgentState psi) :
    (compareSigDispatchActionOne hpsi l r).1.reset_cmd = l.reset_cmd ∧ (compareSigDispatchActionOne hpsi l r).2.reset_cmd = r.reset_cmd := by
  unfold compareSigDispatchActionOne
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd, singleUseControlTail_reset_cmd, doneCaptureSigMove_reset_cmd, compareSigDispatch_reset_cmd]

-- AuthorizedComparisonRepair.lean:168
theorem authorizedCmpUpdate_reset_cmd (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedCmpUpdate hψ l r).1.core.reset_cmd = l.core.reset_cmd ∧ (authorizedCmpUpdate hψ l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold authorizedCmpUpdate
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd, singleUseControlTail_reset_cmd, doneCaptureSigMove_reset_cmd, compareSigDispatch_reset_cmd, compareSigDispatchActionOne_reset_cmd]

-- WriteSeqPersistenceRepair.lean:152
theorem clearInputIncrementPair_reset_cmd (l r : AgentState ψ) :
    (clearInputIncrementPair l r).1.reset_cmd = l.reset_cmd ∧ (clearInputIncrementPair l r).2.reset_cmd = r.reset_cmd := by
  unfold clearInputIncrementPair
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd, singleUseControlTail_reset_cmd, doneCaptureSigMove_reset_cmd, compareSigDispatch_reset_cmd, compareSigDispatchActionOne_reset_cmd, authorizedCmpUpdate_reset_cmd]

-- Algorithm.lean:1007
theorem writeSeqGenerate_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqGenerate hψ l r).1.reset_cmd = l.reset_cmd ∧ (writeSeqGenerate hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold writeSeqGenerate
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd, singleUseControlTail_reset_cmd, doneCaptureSigMove_reset_cmd, compareSigDispatch_reset_cmd, compareSigDispatchActionOne_reset_cmd, authorizedCmpUpdate_reset_cmd, clearInputIncrementPair_reset_cmd]

-- WriteSeqPersistenceRepair.lean:290
theorem writeActionPreservingComparison_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeActionPreservingComparison hψ l r).1.reset_cmd = l.reset_cmd ∧ (writeActionPreservingComparison hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold writeActionPreservingComparison
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd, singleUseControlTail_reset_cmd, doneCaptureSigMove_reset_cmd, compareSigDispatch_reset_cmd, compareSigDispatchActionOne_reset_cmd, authorizedCmpUpdate_reset_cmd, clearInputIncrementPair_reset_cmd, writeSeqGenerate_reset_cmd]

-- BirthStationaryWritePersistent.lean:24
theorem swPersistentThroughPrepare_reset_cmd (hψ : 0 < ψ) (l r : AgentState ψ) :
    (swPersistentThroughPrepare hψ l r).1.reset_cmd = l.reset_cmd ∧ (swPersistentThroughPrepare hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold swPersistentThroughPrepare
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd, singleUseControlTail_reset_cmd, doneCaptureSigMove_reset_cmd, compareSigDispatch_reset_cmd, compareSigDispatchActionOne_reset_cmd, authorizedCmpUpdate_reset_cmd, clearInputIncrementPair_reset_cmd, writeSeqGenerate_reset_cmd, writeActionPreservingComparison_reset_cmd]

-- Algorithm.lean:875
theorem moveWsigCheckGenWs_reset_cmd (l r : AgentState ψ) :
    (moveWsigCheckGenWs l r).reset_cmd = r.reset_cmd := by
  unfold moveWsigCheckGenWs
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [])

-- Algorithm.lean:891
theorem moveWsigStart_reset_cmd (l r : AgentState ψ) :
    (moveWsigStart l r).1.reset_cmd = l.reset_cmd ∧ (moveWsigStart l r).2.reset_cmd = r.reset_cmd := by
  unfold moveWsigStart
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_reset_cmd])

-- Algorithm.lean:882
theorem moveWsigCheckLast_reset_cmd (l : AgentState ψ) :
    (moveWsigCheckLast l).reset_cmd = l.reset_cmd := by
  unfold moveWsigCheckLast
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_reset_cmd, moveWsigStart_reset_cmd])

-- WriteSeqPersistenceRepair.lean:332
theorem moveWsigTransferStopAligned_reset_cmd (l r : AgentState ψ) :
    (moveWsigTransferStopAligned l r).1.reset_cmd = l.reset_cmd ∧ (moveWsigTransferStopAligned l r).2.reset_cmd = r.reset_cmd := by
  unfold moveWsigTransferStopAligned
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_reset_cmd, moveWsigStart_reset_cmd, moveWsigCheckLast_reset_cmd])

-- WriteSeqPersistenceRepair.lean:364
theorem moveWsigMoveWritePreservingNonempty_reset_cmd (l r : AgentState ψ) :
    (moveWsigMoveWritePreservingNonempty l r).1.reset_cmd = l.reset_cmd ∧ (moveWsigMoveWritePreservingNonempty l r).2.reset_cmd = r.reset_cmd := by
  unfold moveWsigMoveWritePreservingNonempty
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_reset_cmd, moveWsigStart_reset_cmd, moveWsigCheckLast_reset_cmd, moveWsigTransferStopAligned_reset_cmd])

-- Algorithm.lean:904
theorem moveWsigLeaderSignal_reset_cmd (l r : AgentState ψ) :
    (moveWsigLeaderSignal l r).1.reset_cmd = l.reset_cmd ∧ (moveWsigLeaderSignal l r).2.reset_cmd = r.reset_cmd := by
  unfold moveWsigLeaderSignal
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_reset_cmd, moveWsigStart_reset_cmd, moveWsigCheckLast_reset_cmd, moveWsigTransferStopAligned_reset_cmd, moveWsigMoveWritePreservingNonempty_reset_cmd])

-- Algorithm.lean:908
theorem moveWsigSignalMove_reset_cmd (l r : AgentState ψ) :
    (moveWsigSignalMove l r).1.reset_cmd = l.reset_cmd ∧ (moveWsigSignalMove l r).2.reset_cmd = r.reset_cmd := by
  unfold moveWsigSignalMove
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_reset_cmd, moveWsigStart_reset_cmd, moveWsigCheckLast_reset_cmd, moveWsigTransferStopAligned_reset_cmd, moveWsigMoveWritePreservingNonempty_reset_cmd, moveWsigLeaderSignal_reset_cmd])

-- Algorithm.lean:916
theorem moveWsigEchoMove_reset_cmd (l r : AgentState ψ) :
    (moveWsigEchoMove l r).1.reset_cmd = l.reset_cmd ∧ (moveWsigEchoMove l r).2.reset_cmd = r.reset_cmd := by
  unfold moveWsigEchoMove
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_reset_cmd, moveWsigStart_reset_cmd, moveWsigCheckLast_reset_cmd, moveWsigTransferStopAligned_reset_cmd, moveWsigMoveWritePreservingNonempty_reset_cmd, moveWsigLeaderSignal_reset_cmd, moveWsigSignalMove_reset_cmd])

-- WriteSeqPersistenceRepair.lean:388
theorem moveWsigFinishPreservingCommand_reset_cmd (l r : AgentState ψ) :
    (moveWsigFinishPreservingCommand l r).1.reset_cmd = l.reset_cmd ∧ (moveWsigFinishPreservingCommand l r).2.reset_cmd = r.reset_cmd := by
  unfold moveWsigFinishPreservingCommand
  try dsimp only
  repeat' split
  all_goals simp_all [moveWsigCheckGenWs_reset_cmd, moveWsigStart_reset_cmd, moveWsigCheckLast_reset_cmd, moveWsigTransferStopAligned_reset_cmd, moveWsigMoveWritePreservingNonempty_reset_cmd, moveWsigLeaderSignal_reset_cmd, moveWsigSignalMove_reset_cmd, moveWsigEchoMove_reset_cmd]

-- WriteSeqPersistenceRepair.lean:397
theorem moveWsigStopAligned_reset_cmd (_hψ : ψ > 0) (l r : AgentState ψ) :
    (moveWsigStopAligned _hψ l r).1.reset_cmd = l.reset_cmd ∧ (moveWsigStopAligned _hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold moveWsigStopAligned
  try dsimp only
  repeat' split
  all_goals simp_all [moveWsigCheckGenWs_reset_cmd, moveWsigStart_reset_cmd, moveWsigCheckLast_reset_cmd, moveWsigTransferStopAligned_reset_cmd, moveWsigMoveWritePreservingNonempty_reset_cmd, moveWsigLeaderSignal_reset_cmd, moveWsigSignalMove_reset_cmd, moveWsigEchoMove_reset_cmd, moveWsigFinishPreservingCommand_reset_cmd]

-- WriteSeqPersistenceRepair.lean:412
theorem writeSeqAfterPrepareComparisonTransport_reset_cmd (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqAfterPrepareComparisonTransport hψ l r).1.reset_cmd = l.reset_cmd ∧ (writeSeqAfterPrepareComparisonTransport hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold writeSeqAfterPrepareComparisonTransport
  try dsimp only
  repeat' split
  all_goals simp_all [moveWsigStopAligned_reset_cmd, compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd, singleUseControlTail_reset_cmd, doneCaptureSigMove_reset_cmd, compareSigDispatch_reset_cmd, compareSigDispatchActionOne_reset_cmd, authorizedCmpUpdate_reset_cmd, clearInputIncrementPair_reset_cmd, writeSeqGenerate_reset_cmd, writeActionPreservingComparison_reset_cmd, swPersistentThroughPrepare_reset_cmd]

-- BirthStationaryWritePersistent.lean:32
theorem stationaryPersistentRaw_reset_cmd (hψ : 0 < ψ) (l r : AgentState ψ) :
    (stationaryPersistentRaw hψ l r).1.reset_cmd = l.reset_cmd ∧ (stationaryPersistentRaw hψ l r).2.reset_cmd = r.reset_cmd := by
  unfold stationaryPersistentRaw
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd, singleUseControlTail_reset_cmd, doneCaptureSigMove_reset_cmd, compareSigDispatch_reset_cmd, compareSigDispatchActionOne_reset_cmd, authorizedCmpUpdate_reset_cmd, clearInputIncrementPair_reset_cmd, writeSeqGenerate_reset_cmd, writeActionPreservingComparison_reset_cmd, swPersistentThroughPrepare_reset_cmd, writeSeqAfterPrepareComparisonTransport_reset_cmd]

-- BirthGenerationControlRepair.lean:50
theorem genCleanAfterWait_reset_cmd (hpsi : psi > 0) (l r : AgentState psi) :
    (genCleanAfterWait hpsi l r).1.reset_cmd = l.reset_cmd ∧ (genCleanAfterWait hpsi l r).2.reset_cmd = r.reset_cmd := by
  unfold genCleanAfterWait
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd, singleUseControlTail_reset_cmd, doneCaptureSigMove_reset_cmd, compareSigDispatch_reset_cmd, compareSigDispatchActionOne_reset_cmd, authorizedCmpUpdate_reset_cmd, clearInputIncrementPair_reset_cmd, writeSeqGenerate_reset_cmd, writeActionPreservingComparison_reset_cmd, swPersistentThroughPrepare_reset_cmd, writeSeqAfterPrepareComparisonTransport_reset_cmd, stationaryPersistentRaw_reset_cmd]

-- WallSweepPreCheckResetRepair.lean:42
theorem preCheckResetWall_reset_cmd (l r : AuthorizedAgentState psi) :
    (preCheckResetWall l r).1.core.reset_cmd = l.core.reset_cmd ∧ (preCheckResetWall l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold preCheckResetWall
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd, singleUseControlTail_reset_cmd, doneCaptureSigMove_reset_cmd, compareSigDispatch_reset_cmd, compareSigDispatchActionOne_reset_cmd, authorizedCmpUpdate_reset_cmd, clearInputIncrementPair_reset_cmd, writeSeqGenerate_reset_cmd, writeActionPreservingComparison_reset_cmd, swPersistentThroughPrepare_reset_cmd, writeSeqAfterPrepareComparisonTransport_reset_cmd, stationaryPersistentRaw_reset_cmd, genCleanAfterWait_reset_cmd]

-- TerminalEqualSupportRepair.lean:69
theorem sanitizeAuthorizedPair_reset_cmd (hψ : ψ > 0) (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    (sanitizeAuthorizedPair hψ q).1.core.reset_cmd = q.1.core.reset_cmd ∧ (sanitizeAuthorizedPair hψ q).2.core.reset_cmd = q.2.core.reset_cmd := by
  unfold sanitizeAuthorizedPair
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd, singleUseControlTail_reset_cmd, doneCaptureSigMove_reset_cmd, compareSigDispatch_reset_cmd, compareSigDispatchActionOne_reset_cmd, authorizedCmpUpdate_reset_cmd, clearInputIncrementPair_reset_cmd, writeSeqGenerate_reset_cmd, writeActionPreservingComparison_reset_cmd, swPersistentThroughPrepare_reset_cmd, writeSeqAfterPrepareComparisonTransport_reset_cmd, stationaryPersistentRaw_reset_cmd, genCleanAfterWait_reset_cmd, preCheckResetWall_reset_cmd]

-- LeaderCreationCleanupRepair.lean:95
theorem markLeaderBirth_reset_cmd (born : Bool) (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    (markLeaderBirth born q).1.core.reset_cmd = q.1.core.reset_cmd ∧ (markLeaderBirth born q).2.core.reset_cmd = q.2.core.reset_cmd := by
  unfold markLeaderBirth
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_reset_cmd, writeSeqSetWriteReadyTransport_reset_cmd, writeSeqSetWriteAct_reset_cmd, writeSeqFinalR_reset_cmd, writeSeqCheckBit_reset_cmd, writeActionApplyOverwrite_reset_cmd, writeActionApplyMoveFlip_reset_cmd, genSigSaturatedFinish_reset_cmd, clearComparisonSignal_reset_cmd, resetKillComparison_reset_cmd, clearIfLeader_reset_cmd, clearIncrementAction_reset_cmd, compareSigInit_reset_cmd, cleanSigGenConnect_reset_cmd, cleanSigStep3_reset_cmd, cleanSigStep4_reset_cmd, cleanSigStep5_reset_cmd, cleanSigStep6_reset_cmd, cleanSigCleanApply_reset_cmd, checkSigSetReady_reset_cmd, checkSigCheckL_reset_cmd, checkSigCheckR_reset_cmd, checkSigSetResult_reset_cmd, checkSigSetLeader_reset_cmd, pPsi_reset_cmd, eliminateSig_reset_cmd, disappear_reset_cmd, compareBitUpdateL_reset_cmd, compareBitUpdateR_reset_cmd, compareBit_reset_cmd, compareBitActionOne_reset_cmd, captureStep1_reset_cmd, holdDoneStep1_reset_cmd, sigMoveStep2_reset_cmd, sigMoveStep3_reset_cmd, sigMoveStep4_reset_cmd, sigMoveStep5_reset_cmd, singleUseApplyControl_reset_cmd, gatePreparedIncrement_reset_cmd, writeActionActivateNonempty_reset_cmd, writeActionExecutePreservingDepart_reset_cmd, writeActionExecutePreservingComparison_reset_cmd, writeSeqReadyTransport_reset_cmd, writeSeqCompare_reset_cmd, writeSeqCommands_reset_cmd, writeSeqPrepareTransport_reset_cmd, gensigWriteseq_reset_cmd, groupInfo_reset_cmd, waitSaturatedPrepare_reset_cmd, terminalInactiveClear_reset_cmd, waitWidthReset_reset_cmd, waitWidthFinish_reset_cmd, genSigSaturatedStart_reset_cmd, genCleanEmit_reset_cmd, genCleanPropagate_reset_cmd, suppressSigFinish_reset_cmd, normalizeDeletion_reset_cmd, markComparisonForDeletion_reset_cmd, sanitizeAuthorizedTerminalEqual_reset_cmd, clearAuthorizedComparison_reset_cmd, cmpUpdateReturnPriority_reset_cmd, cmpUpdateSetPath2_reset_cmd, cleanSig_reset_cmd, checkSig_reset_cmd, pPsiLeaderResetProbeWall_reset_cmd, comparisonLeaderWall_reset_cmd, sigMoveLeaderPreclear_reset_cmd, controlTransfers_reset_cmd, doneTransfers_reset_cmd, singleUseControlTail_reset_cmd, doneCaptureSigMove_reset_cmd, compareSigDispatch_reset_cmd, compareSigDispatchActionOne_reset_cmd, authorizedCmpUpdate_reset_cmd, clearInputIncrementPair_reset_cmd, writeSeqGenerate_reset_cmd, writeActionPreservingComparison_reset_cmd, swPersistentThroughPrepare_reset_cmd, writeSeqAfterPrepareComparisonTransport_reset_cmd, stationaryPersistentRaw_reset_cmd, genCleanAfterWait_reset_cmd, preCheckResetWall_reset_cmd, sanitizeAuthorizedPair_reset_cmd]


theorem authorizedEliminateSig_reset_cmd (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedEliminateSig hψ l r).1.core.reset_cmd = l.core.reset_cmd ∧
      (authorizedEliminateSig hψ l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold authorizedEliminateSig
  rw [(BirthB1InnerCountFrames.authorizedReconcile_core _ l r).1, (BirthB1InnerCountFrames.authorizedReconcile_core _ l r).2]
  exact eliminateSig_reset_cmd hψ l.core r.core

theorem authorizedCleanSig_reset_cmd (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedCleanSig hψ l r).1.core.reset_cmd = l.core.reset_cmd ∧
      (authorizedCleanSig hψ l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold authorizedCleanSig
  rw [(BirthB1InnerCountFrames.authorizedReconcile_core _ l r).1, (BirthB1InnerCountFrames.authorizedReconcile_core _ l r).2]
  exact cleanSig_reset_cmd hψ l.core r.core

theorem authorizedDisappear_reset_cmd (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedDisappear hψ l r).1.core.reset_cmd = l.core.reset_cmd ∧
      (authorizedDisappear hψ l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold authorizedDisappear
  rw [(BirthB1InnerCountFrames.authorizedReconcile_core _ l r).1, (BirthB1InnerCountFrames.authorizedReconcile_core _ l r).2]
  exact disappear_reset_cmd hψ l.core r.core

theorem authorizedCheckSig_reset_cmd (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedCheckSig hψ l r).1.core.reset_cmd = l.core.reset_cmd ∧
      (authorizedCheckSig hψ l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold authorizedCheckSig
  rw [(BirthB1InnerCountFrames.authorizedReconcile_core _ l r).1, (BirthB1InnerCountFrames.authorizedReconcile_core _ l r).2]
  exact checkSig_reset_cmd hψ l.core r.core

theorem stationaryPersistentAuthorizedRow_reset_cmd (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    (stationaryPersistentAuthorizedRow hψ l r).1.core.reset_cmd = l.core.reset_cmd ∧
      (stationaryPersistentAuthorizedRow hψ l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold stationaryPersistentAuthorizedRow
  rw [(BirthB1InnerCountFrames.authorizedReconcile_core _ l r).1, (BirthB1InnerCountFrames.authorizedReconcile_core _ l r).2]
  exact stationaryPersistentRaw_reset_cmd hψ l.core r.core

theorem authorizedPPsiLeaderResetProbeWall_reset_cmd (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedPPsiLeaderResetProbeWall hψ l r).1.core.reset_cmd = l.core.reset_cmd ∧
      (authorizedPPsiLeaderResetProbeWall hψ l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold authorizedPPsiLeaderResetProbeWall
  simp only []
  exact pPsiLeaderResetProbeWall_reset_cmd hψ l.core r.core

theorem authorizedDoneMove_reset_cmd (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedDoneMove hpsi l r).1.core.reset_cmd = l.core.reset_cmd ∧
      (authorizedDoneMove hpsi l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold authorizedDoneMove
  simp only []
  split
  · exact doneCaptureSigMove_reset_cmd hpsi l.core r.core
  · exact doneCaptureSigMove_reset_cmd hpsi l.core r.core

theorem congestGuardCheck_reset_cmd (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (congestGuardCheck hpsi l r).1.core.reset_cmd = l.core.reset_cmd ∧
      (congestGuardCheck hpsi l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold congestGuardCheck
  split
  · exact ⟨rfl, rfl⟩
  · exact authorizedCheckSig_reset_cmd hpsi l r

theorem preserveTossCheck_reset_cmd' (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (preserveTossCheck hpsi l r).1.core.reset_cmd = l.core.reset_cmd ∧
      (preserveTossCheck hpsi l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold preserveTossCheck
  split
  · exact ⟨rfl, rfl⟩
  · exact congestGuardCheck_reset_cmd hpsi l r

theorem preserveDoneCheck_reset_cmd (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (preserveDoneCheck hpsi l r).1.core.reset_cmd = l.core.reset_cmd ∧
      (preserveDoneCheck hpsi l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold preserveDoneCheck
  split
  · exact ⟨rfl, rfl⟩
  · exact preserveTossCheck_reset_cmd' hpsi l r


/-- Authorization reconciliation keeps the raw pair. -/
theorem authorizedReconcile_core (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthorizedAgentState ψ) :
    (authorizedReconcile f l r).1.core = (f l.core r.core).1 ∧
      (authorizedReconcile f l r).2.core = (f l.core r.core).2 := ⟨rfl, rfl⟩

-- Repairs.lean:1085
theorem compareBitUpdateRActionOne_leader {ψ : Nat} (hψ : ψ > 0) (r : AgentState ψ) :
    (compareBitUpdateRActionOne hψ r).leader = r.leader := by
  unfold compareBitUpdateRActionOne
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- WriteSeqPersistenceRepair.lean:74
theorem writeSeqSetWriteReadyTransport_leader (u : AgentState ψ) :
    (writeSeqSetWriteReadyTransport u).leader = u.leader := by
  unfold writeSeqSetWriteReadyTransport
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:982
theorem writeSeqSetWriteAct_leader (u : AgentState ψ) :
    (writeSeqSetWriteAct u).leader = u.leader := by
  unfold writeSeqSetWriteAct
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:992
theorem writeSeqFinalR_leader (r : AgentState ψ) :
    (writeSeqFinalR r).leader = r.leader := by
  unfold writeSeqFinalR
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:977
theorem writeSeqCheckBit_leader (r : AgentState ψ) :
    (writeSeqCheckBit r).leader = r.leader := by
  unfold writeSeqCheckBit
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:785
theorem writeActionApplyOverwrite_leader (r : AgentState ψ) :
    (writeActionApplyOverwrite r).leader = r.leader := by
  unfold writeActionApplyOverwrite
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:792
theorem writeActionApplyMoveFlip_leader (r : AgentState ψ) :
    (writeActionApplyMoveFlip r).leader = r.leader := by
  unfold writeActionApplyMoveFlip
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Repairs.lean:153
theorem genSigSaturatedFinish_leader {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (genSigSaturatedFinish hψ l r).1.leader = l.leader ∧ (genSigSaturatedFinish hψ l r).2.leader = r.leader := by
  unfold genSigSaturatedFinish
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- WallSweepRepair.lean:25
theorem clearComparisonSignal_leader (u : AgentState ψ) :
    (clearComparisonSignal u).leader = u.leader := by
  unfold clearComparisonSignal
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, ])

-- WallSweepRepair.lean:60
theorem resetKillComparison_leader (u : AgentState ψ) :
    (resetKillComparison u).leader = u.leader := by
  unfold resetKillComparison
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader])

-- WallSweepRepair.lean:429
theorem clearIfLeader_leader (u : AgentState ψ) :
    (clearIfLeader u).leader = u.leader := by
  unfold clearIfLeader
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader])

-- WriteIncrementGate.lean:28
theorem clearIncrementAction_leader (u : AgentState ψ) :
    (clearIncrementAction u).leader = u.leader := by
  unfold clearIncrementAction
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader])

-- Algorithm.lean:436
theorem compareSigInit_leader (l : AgentState ψ) :
    (compareSigInit l).leader = l.leader := by
  unfold compareSigInit
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader])

-- Algorithm.lean:121
theorem cleanSigGenConnect_leader (u : AgentState ψ) :
    (cleanSigGenConnect u).leader = u.leader := by
  unfold cleanSigGenConnect
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader])

-- Algorithm.lean:147
theorem cleanSigStep3_leader (l r : AgentState ψ) :
    (cleanSigStep3 l r).1.leader = l.leader ∧ (cleanSigStep3 l r).2.leader = r.leader := by
  unfold cleanSigStep3
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader])

-- Algorithm.lean:157
theorem cleanSigStep4_leader (l r : AgentState ψ) :
    (cleanSigStep4 l r).1.leader = l.leader ∧ (cleanSigStep4 l r).2.leader = r.leader := by
  unfold cleanSigStep4
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader])

-- Algorithm.lean:167
theorem cleanSigStep5_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).1.leader = l.leader ∧ (cleanSigStep5 hψ l r).2.leader = r.leader := by
  unfold cleanSigStep5
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader])

-- Algorithm.lean:177
theorem cleanSigStep6_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).1.leader = l.leader ∧ (cleanSigStep6 hψ l r).2.leader = r.leader := by
  unfold cleanSigStep6
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader])

-- Algorithm.lean:129
theorem cleanSigCleanApply_leader (u : AgentState ψ) :
    (cleanSigCleanApply u).leader = u.leader := by
  unfold cleanSigCleanApply
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader])

-- Algorithm.lean:226
theorem checkSigSetReady_leader (u : AgentState ψ) :
    (checkSigSetReady u).leader = u.leader := by
  unfold checkSigSetReady
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader])

-- Algorithm.lean:235
theorem checkSigCheckL_leader (hψ : ψ > 0) (u : AgentState ψ) :
    (checkSigCheckL hψ u).leader = u.leader := by
  unfold checkSigCheckL
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader])

-- Algorithm.lean:243
theorem checkSigCheckR_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).leader = r.leader := by
  unfold checkSigCheckR
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader])

-- Algorithm.lean:253
theorem checkSigSetResult_leader (u : AgentState ψ) :
    (checkSigSetResult u).leader = u.leader := by
  unfold checkSigSetResult
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader])

-- checkSigSetLeader_leader removed: this stage writes the field

-- pPsi_leader removed: this stage writes the field

-- Algorithm.lean:201
theorem eliminateSig_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.leader = l.leader ∧ (eliminateSig hψ l r).2.leader = r.leader := by
  unfold eliminateSig
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader])

-- Algorithm.lean:338
theorem disappear_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (disappear hψ l r).1.leader = l.leader ∧ (disappear hψ l r).2.leader = r.leader := by
  unfold disappear
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader])

-- Algorithm.lean:403
theorem compareBitUpdateL_leader (hψ : ψ > 0) (l : AgentState ψ) :
    (compareBitUpdateL hψ l).leader = l.leader := by
  unfold compareBitUpdateL
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader])

-- Algorithm.lean:411
theorem compareBitUpdateR_leader (hψ : ψ > 0) (r : AgentState ψ) :
    (compareBitUpdateR hψ r).leader = r.leader := by
  unfold compareBitUpdateR
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader])

-- Algorithm.lean:428
theorem compareBit_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareBit hψ l r).1.leader = l.leader ∧ (compareBit hψ l r).2.leader = r.leader := by
  unfold compareBit
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader])

-- MultiLeaderCleanup.lean:53
theorem compareBitActionOne_leader (hpsi : psi > 0) (l r : AgentState psi) :
    (compareBitActionOne hpsi l r).1.leader = l.leader ∧ (compareBitActionOne hpsi l r).2.leader = r.leader := by
  unfold compareBitActionOne
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader])

-- BirthArrivalCaptureRepair.lean:28
theorem captureStep1_leader (l r : AgentState psi) :
    (captureStep1 l r).1.leader = l.leader ∧ (captureStep1 l r).2.leader = r.leader := by
  unfold captureStep1
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader])

-- BirthGenerationDone.lean:66
theorem holdDoneStep1_leader (l r : AgentState psi) :
    (holdDoneStep1 l r).1.leader = l.leader ∧ (holdDoneStep1 l r).2.leader = r.leader := by
  unfold holdDoneStep1
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader])

-- Algorithm.lean:482
theorem sigMoveStep2_leader (l r : AgentState ψ) :
    (sigMoveStep2 l r).1.leader = l.leader ∧ (sigMoveStep2 l r).2.leader = r.leader := by
  unfold sigMoveStep2
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader])

-- Algorithm.lean:491
theorem sigMoveStep3_leader (l r : AgentState ψ) :
    (sigMoveStep3 l r).1.leader = l.leader ∧ (sigMoveStep3 l r).2.leader = r.leader := by
  unfold sigMoveStep3
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader])

-- Algorithm.lean:500
theorem sigMoveStep4_leader (l r : AgentState ψ) :
    (sigMoveStep4 l r).1.leader = l.leader ∧ (sigMoveStep4 l r).2.leader = r.leader := by
  unfold sigMoveStep4
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader])

-- Algorithm.lean:508
theorem sigMoveStep5_leader (l r : AgentState ψ) :
    (sigMoveStep5 l r).1.leader = l.leader ∧ (sigMoveStep5 l r).2.leader = r.leader := by
  unfold sigMoveStep5
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader])

-- BirthSingleUseReleaseRepair.lean:103
theorem singleUseApplyControl_leader (hpsi : psi > 0) (u : AgentState psi) :
    (singleUseApplyControl hpsi u).leader = u.leader := by
  unfold singleUseApplyControl
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader])

-- WriteIncrementGate.lean:33
theorem gatePreparedIncrement_leader (u : AgentState ψ) :
    (gatePreparedIncrement u).leader = u.leader := by
  unfold gatePreparedIncrement
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader])

-- WriteSeqPersistenceRepair.lean:215
theorem writeActionActivateNonempty_leader (hψ : ψ > 0) (u : AgentState ψ) :
    (writeActionActivateNonempty hψ u).leader = u.leader := by
  unfold writeActionActivateNonempty
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader])

-- WriteSeqPersistenceRepair.lean:177
theorem writeActionApplyIncrementAndFlip_leader (r : AgentState ψ) :
    (writeActionApplyIncrementAndFlip r).leader = r.leader := by
  unfold writeActionApplyIncrementAndFlip
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, writeActionApplyIncrementAndFlip_leader, writeActionPropagateState_leader])

-- WriteSeqPersistenceRepair.lean:225
theorem writeActionPropagateState_leader (l : AgentState ψ) (state : WriteState) :
    (writeActionPropagateState l state).leader = l.leader := by
  unfold writeActionPropagateState
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, writeActionApplyIncrementAndFlip_leader, writeActionPropagateState_leader])

-- WriteSeqPersistenceRepair.lean:245
theorem writeActionExecutePreservingDepart_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeActionExecutePreservingDepart hψ l r).1.leader = l.leader ∧ (writeActionExecutePreservingDepart hψ l r).2.leader = r.leader := by
  unfold writeActionExecutePreservingDepart
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [writeActionApplyIncrementAndFlip_leader, writeActionPropagateState_leader, compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader])

-- WriteSeqPersistenceRepair.lean:263
theorem writeActionPreservingDepart_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeActionPreservingDepart hψ l r).1.leader = l.leader ∧ (writeActionPreservingDepart hψ l r).2.leader = r.leader := by
  unfold writeActionPreservingDepart
  try simp only []
  have h := writeActionExecutePreservingDepart_leader hψ (writeActionActivateNonempty hψ l) (writeActionActivateNonempty hψ r)
  rw [h.1, h.2, writeActionActivateNonempty_leader, writeActionActivateNonempty_leader]
  exact ⟨rfl, rfl⟩

-- WriteSeqPersistenceRepair.lean:283
theorem writeActionExecutePreservingComparison_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeActionExecutePreservingComparison hψ l r).1.leader = l.leader ∧ (writeActionExecutePreservingComparison hψ l r).2.leader = r.leader := by
  unfold writeActionExecutePreservingComparison
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader])

-- WriteSeqPersistenceRepair.lean:139
theorem writeSeqReadyTransport_leader (l r : AgentState ψ) :
    (writeSeqReadyTransport l r).1.leader = l.leader ∧ (writeSeqReadyTransport l r).2.leader = r.leader := by
  unfold writeSeqReadyTransport
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader])

-- Algorithm.lean:1018
theorem writeSeqCompare_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqCompare hψ l r).1.leader = l.leader ∧ (writeSeqCompare hψ l r).2.leader = r.leader := by
  unfold writeSeqCompare
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader])

-- Algorithm.lean:1030
theorem writeSeqCommands_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqCommands hψ l r).1.leader = l.leader ∧ (writeSeqCommands hψ l r).2.leader = r.leader := by
  unfold writeSeqCommands
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader])

-- WriteSeqPersistenceRepair.lean:144
theorem writeSeqPrepareTransport_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqPrepareTransport hψ l r).1.leader = l.leader ∧ (writeSeqPrepareTransport hψ l r).2.leader = r.leader := by
  unfold writeSeqPrepareTransport
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader])

-- Algorithm.lean:749
theorem gensigWriteseq_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (gensigWriteseq hψ l r).1.leader = l.leader ∧ (gensigWriteseq hψ l r).2.leader = r.leader := by
  unfold gensigWriteseq
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader])

-- Algorithm.lean:668
theorem groupInfo_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (groupInfo hψ l r).1.leader = l.leader ∧ (groupInfo hψ l r).2.leader = r.leader := by
  unfold groupInfo
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader])

-- Repairs.lean:61
theorem waitSaturatedPrepare_leader {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (waitSaturatedPrepare hψ l r).1.leader = l.leader ∧ (waitSaturatedPrepare hψ l r).2.leader = r.leader := by
  unfold waitSaturatedPrepare
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader])

-- BirthShortWaitTerminalEntryRepair.lean:31
theorem terminalInactiveClear_leader {psi width : Nat} (hwidth : 0 < width) (hle : width ≤ psi) (l r : AgentState psi) :
    (terminalInactiveClear hwidth hle l r).1.leader = l.leader ∧ (terminalInactiveClear hwidth hle l r).2.leader = r.leader := by
  unfold terminalInactiveClear
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader])

-- BirthShortWait.lean:46
theorem waitWidthReset_leader {psi width : Nat} (hwidth : 0 < width) (hle : width <= psi) (l r : AgentState psi) :
    (waitWidthReset hwidth hle l r).1.leader = l.leader ∧ (waitWidthReset hwidth hle l r).2.leader = r.leader := by
  unfold waitWidthReset
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader])

-- BirthShortWait.lean:59
theorem waitWidthFinish_leader {psi width : Nat} (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi) (kappa : Nat) (l r : AgentState psi) :
    (waitWidthFinish hpsi hwidth hle kappa l r).1.leader = l.leader ∧ (waitWidthFinish hpsi hwidth hle kappa l r).2.leader = r.leader := by
  unfold waitWidthFinish
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader])

-- Repairs.lean:119
theorem genSigSaturatedStart_leader {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (genSigSaturatedStart hψ l r).1.leader = l.leader ∧ (genSigSaturatedStart hψ l r).2.leader = r.leader := by
  unfold genSigSaturatedStart
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader])

-- BirthGenerationControlRepair.lean:27
theorem genCleanEmit_leader (hpsi : psi > 0) (l r : AgentState psi) :
    (genCleanEmit hpsi l r).1.leader = l.leader ∧ (genCleanEmit hpsi l r).2.leader = r.leader := by
  unfold genCleanEmit
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader])

-- BirthGenerationControlRepair.lean:39
theorem genCleanPropagate_leader (hpsi : psi > 0) (l r : AgentState psi) :
    (genCleanPropagate hpsi l r).1.leader = l.leader ∧ (genCleanPropagate hpsi l r).2.leader = r.leader := by
  unfold genCleanPropagate
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader])

-- Algorithm.lean:535
theorem suppressSigStart_leader (l r : AgentState ψ) :
    (suppressSigStart l r).1.leader = l.leader ∧ (suppressSigStart l r).2.leader = r.leader := by
  unfold suppressSigStart
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader])

-- Algorithm.lean:539
theorem suppressSigMoveReset_leader (l r : AgentState ψ) :
    (suppressSigMoveReset l r).1.leader = l.leader ∧ (suppressSigMoveReset l r).2.leader = r.leader := by
  unfold suppressSigMoveReset
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader])

-- Algorithm.lean:552
theorem suppressSigEcho_leader (l r : AgentState ψ) :
    (suppressSigEcho l r).1.leader = l.leader ∧ (suppressSigEcho l r).2.leader = r.leader := by
  unfold suppressSigEcho
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader])

-- Algorithm.lean:561
theorem suppressSigFinish_leader (l r : AgentState ψ) :
    (suppressSigFinish l r).1.leader = l.leader ∧ (suppressSigFinish l r).2.leader = r.leader := by
  unfold suppressSigFinish
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader])

-- LeaderCreationCleanupRepair.lean:42
theorem normalizeDeletion_leader (u : AuthorizedAgentState ψ) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader])

-- LeaderCreationCleanupRepair.lean:49
theorem markComparisonForDeletion_leader (u : AuthorizedAgentState ψ) :
    (markComparisonForDeletion u).core.leader = u.core.leader := by
  unfold markComparisonForDeletion
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader])

-- TerminalEqualSupportRepair.lean:62
theorem sanitizeAuthorizedTerminalEqual_leader (hψ : ψ > 0) (u : AuthorizedAgentState ψ) :
    (sanitizeAuthorizedTerminalEqual hψ u).core.leader = u.core.leader := by
  unfold sanitizeAuthorizedTerminalEqual
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader])

-- WallSweepPreCheckResetRepair.lean:35
theorem clearAuthorizedComparison_leader (u : AuthorizedAgentState psi) :
    (clearAuthorizedComparison u).core.leader = u.core.leader := by
  unfold clearAuthorizedComparison
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader])

-- AuthorizedComparisonRepair.lean:151
theorem cmpUpdateReturnPriority_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (cmpUpdateReturnPriority hψ l r).1.leader = l.leader ∧ (cmpUpdateReturnPriority hψ l r).2.leader = r.leader := by
  unfold cmpUpdateReturnPriority
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader])

-- Algorithm.lean:386
theorem cmpUpdateSetPath2_leader (hψ : ψ > 0) (l : AgentState ψ) :
    (cmpUpdateSetPath2 hψ l).leader = l.leader := by
  unfold cmpUpdateSetPath2
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader])

-- Algorithm.lean:187
theorem cleanSig_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSig hψ l r).1.leader = l.leader ∧ (cleanSig hψ l r).2.leader = r.leader := by
  unfold cleanSig
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader]

-- checkSig_leader removed: this stage writes the field

-- pPsiLeaderResetProbeWall_leader removed (depends on a leader writer; not needed after the SUPPRESS stage)

-- WallSweepRepair.lean:74
theorem comparisonLeaderWall_leader (l r : AgentState ψ) :
    (comparisonLeaderWall l r).1.leader = l.leader ∧ (comparisonLeaderWall l r).2.leader = r.leader := by
  unfold comparisonLeaderWall
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader]

-- WallSweepRepair.lean:456
theorem sigMoveLeaderPreclear_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (sigMoveLeaderPreclear hψ l r).1.leader = l.leader ∧ (sigMoveLeaderPreclear hψ l r).2.leader = r.leader := by
  unfold sigMoveLeaderPreclear
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader]

-- BirthGenerationDone.lean:81
theorem controlTransfers_leader (l r : AgentState psi) :
    (controlTransfers l r).1.leader = l.leader ∧ (controlTransfers l r).2.leader = r.leader := by
  unfold controlTransfers
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader]

-- BirthGenerationDone.lean:88
theorem doneTransfers_leader (l r : AgentState psi) :
    (doneTransfers l r).1.leader = l.leader ∧ (doneTransfers l r).2.leader = r.leader := by
  unfold doneTransfers
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader]

-- BirthSingleUseReleaseRepair.lean:137
theorem singleUseControlTail_leader (hpsi : psi > 0) (l r : AgentState psi) :
    (singleUseControlTail hpsi l r).1.leader = l.leader ∧ (singleUseControlTail hpsi l r).2.leader = r.leader := by
  unfold singleUseControlTail
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader]

-- BirthGenerationDone.lean:178
theorem doneCaptureSigMove_leader (hpsi : psi > 0) (l r : AgentState psi) :
    (doneCaptureSigMove hpsi l r).1.leader = l.leader ∧ (doneCaptureSigMove hpsi l r).2.leader = r.leader := by
  unfold doneCaptureSigMove
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader, singleUseControlTail_leader]

-- Algorithm.lean:441
theorem compareSigDispatch_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareSigDispatch hψ l r).1.leader = l.leader ∧ (compareSigDispatch hψ l r).2.leader = r.leader := by
  unfold compareSigDispatch
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader, singleUseControlTail_leader, doneCaptureSigMove_leader]

-- MultiLeaderCleanup.lean:62
theorem compareSigDispatchActionOne_leader (hpsi : psi > 0) (l r : AgentState psi) :
    (compareSigDispatchActionOne hpsi l r).1.leader = l.leader ∧ (compareSigDispatchActionOne hpsi l r).2.leader = r.leader := by
  unfold compareSigDispatchActionOne
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader, singleUseControlTail_leader, doneCaptureSigMove_leader, compareSigDispatch_leader]

-- AuthorizedComparisonRepair.lean:168
theorem authorizedCmpUpdate_leader (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedCmpUpdate hψ l r).1.core.leader = l.core.leader ∧ (authorizedCmpUpdate hψ l r).2.core.leader = r.core.leader := by
  unfold authorizedCmpUpdate
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader, singleUseControlTail_leader, doneCaptureSigMove_leader, compareSigDispatch_leader, compareSigDispatchActionOne_leader]

-- WriteSeqPersistenceRepair.lean:152
theorem clearInputIncrementPair_leader (l r : AgentState ψ) :
    (clearInputIncrementPair l r).1.leader = l.leader ∧ (clearInputIncrementPair l r).2.leader = r.leader := by
  unfold clearInputIncrementPair
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader, singleUseControlTail_leader, doneCaptureSigMove_leader, compareSigDispatch_leader, compareSigDispatchActionOne_leader, authorizedCmpUpdate_leader]

-- Algorithm.lean:1007
theorem writeSeqGenerate_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqGenerate hψ l r).1.leader = l.leader ∧ (writeSeqGenerate hψ l r).2.leader = r.leader := by
  unfold writeSeqGenerate
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader, singleUseControlTail_leader, doneCaptureSigMove_leader, compareSigDispatch_leader, compareSigDispatchActionOne_leader, authorizedCmpUpdate_leader, clearInputIncrementPair_leader]

-- WriteSeqPersistenceRepair.lean:290
theorem writeActionPreservingComparison_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeActionPreservingComparison hψ l r).1.leader = l.leader ∧ (writeActionPreservingComparison hψ l r).2.leader = r.leader := by
  unfold writeActionPreservingComparison
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader, singleUseControlTail_leader, doneCaptureSigMove_leader, compareSigDispatch_leader, compareSigDispatchActionOne_leader, authorizedCmpUpdate_leader, clearInputIncrementPair_leader, writeSeqGenerate_leader]

-- BirthStationaryWritePersistent.lean:24
theorem swPersistentThroughPrepare_leader (hψ : 0 < ψ) (l r : AgentState ψ) :
    (swPersistentThroughPrepare hψ l r).1.leader = l.leader ∧ (swPersistentThroughPrepare hψ l r).2.leader = r.leader := by
  unfold swPersistentThroughPrepare
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader, singleUseControlTail_leader, doneCaptureSigMove_leader, compareSigDispatch_leader, compareSigDispatchActionOne_leader, authorizedCmpUpdate_leader, clearInputIncrementPair_leader, writeSeqGenerate_leader, writeActionPreservingComparison_leader]

-- Algorithm.lean:875
theorem moveWsigCheckGenWs_leader (l r : AgentState ψ) :
    (moveWsigCheckGenWs l r).leader = r.leader := by
  unfold moveWsigCheckGenWs
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [])

-- Algorithm.lean:891
theorem moveWsigStart_leader (l r : AgentState ψ) :
    (moveWsigStart l r).1.leader = l.leader ∧ (moveWsigStart l r).2.leader = r.leader := by
  unfold moveWsigStart
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_leader])

-- Algorithm.lean:882
theorem moveWsigCheckLast_leader (l : AgentState ψ) :
    (moveWsigCheckLast l).leader = l.leader := by
  unfold moveWsigCheckLast
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_leader, moveWsigStart_leader])

-- WriteSeqPersistenceRepair.lean:332
theorem moveWsigTransferStopAligned_leader (l r : AgentState ψ) :
    (moveWsigTransferStopAligned l r).1.leader = l.leader ∧ (moveWsigTransferStopAligned l r).2.leader = r.leader := by
  unfold moveWsigTransferStopAligned
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_leader, moveWsigStart_leader, moveWsigCheckLast_leader])

-- WriteSeqPersistenceRepair.lean:364
theorem moveWsigMoveWritePreservingNonempty_leader (l r : AgentState ψ) :
    (moveWsigMoveWritePreservingNonempty l r).1.leader = l.leader ∧ (moveWsigMoveWritePreservingNonempty l r).2.leader = r.leader := by
  unfold moveWsigMoveWritePreservingNonempty
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_leader, moveWsigStart_leader, moveWsigCheckLast_leader, moveWsigTransferStopAligned_leader])

-- Algorithm.lean:904
theorem moveWsigLeaderSignal_leader (l r : AgentState ψ) :
    (moveWsigLeaderSignal l r).1.leader = l.leader ∧ (moveWsigLeaderSignal l r).2.leader = r.leader := by
  unfold moveWsigLeaderSignal
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_leader, moveWsigStart_leader, moveWsigCheckLast_leader, moveWsigTransferStopAligned_leader, moveWsigMoveWritePreservingNonempty_leader])

-- Algorithm.lean:908
theorem moveWsigSignalMove_leader (l r : AgentState ψ) :
    (moveWsigSignalMove l r).1.leader = l.leader ∧ (moveWsigSignalMove l r).2.leader = r.leader := by
  unfold moveWsigSignalMove
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_leader, moveWsigStart_leader, moveWsigCheckLast_leader, moveWsigTransferStopAligned_leader, moveWsigMoveWritePreservingNonempty_leader, moveWsigLeaderSignal_leader])

-- Algorithm.lean:916
theorem moveWsigEchoMove_leader (l r : AgentState ψ) :
    (moveWsigEchoMove l r).1.leader = l.leader ∧ (moveWsigEchoMove l r).2.leader = r.leader := by
  unfold moveWsigEchoMove
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_leader, moveWsigStart_leader, moveWsigCheckLast_leader, moveWsigTransferStopAligned_leader, moveWsigMoveWritePreservingNonempty_leader, moveWsigLeaderSignal_leader, moveWsigSignalMove_leader])

-- WriteSeqPersistenceRepair.lean:388
theorem moveWsigFinishPreservingCommand_leader (l r : AgentState ψ) :
    (moveWsigFinishPreservingCommand l r).1.leader = l.leader ∧ (moveWsigFinishPreservingCommand l r).2.leader = r.leader := by
  unfold moveWsigFinishPreservingCommand
  try dsimp only
  repeat' split
  all_goals simp_all [moveWsigCheckGenWs_leader, moveWsigStart_leader, moveWsigCheckLast_leader, moveWsigTransferStopAligned_leader, moveWsigMoveWritePreservingNonempty_leader, moveWsigLeaderSignal_leader, moveWsigSignalMove_leader, moveWsigEchoMove_leader]

-- WriteSeqPersistenceRepair.lean:397
theorem moveWsigStopAligned_leader (_hψ : ψ > 0) (l r : AgentState ψ) :
    (moveWsigStopAligned _hψ l r).1.leader = l.leader ∧ (moveWsigStopAligned _hψ l r).2.leader = r.leader := by
  unfold moveWsigStopAligned
  try dsimp only
  repeat' split
  all_goals simp_all [moveWsigCheckGenWs_leader, moveWsigStart_leader, moveWsigCheckLast_leader, moveWsigTransferStopAligned_leader, moveWsigMoveWritePreservingNonempty_leader, moveWsigLeaderSignal_leader, moveWsigSignalMove_leader, moveWsigEchoMove_leader, moveWsigFinishPreservingCommand_leader]

-- WriteSeqPersistenceRepair.lean:412
theorem writeSeqAfterPrepareComparisonTransport_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqAfterPrepareComparisonTransport hψ l r).1.leader = l.leader ∧ (writeSeqAfterPrepareComparisonTransport hψ l r).2.leader = r.leader := by
  unfold writeSeqAfterPrepareComparisonTransport
  try dsimp only
  repeat' split
  all_goals simp_all [moveWsigStopAligned_leader, compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader, singleUseControlTail_leader, doneCaptureSigMove_leader, compareSigDispatch_leader, compareSigDispatchActionOne_leader, authorizedCmpUpdate_leader, clearInputIncrementPair_leader, writeSeqGenerate_leader, writeActionPreservingComparison_leader, swPersistentThroughPrepare_leader]

-- BirthStationaryWritePersistent.lean:32
theorem stationaryPersistentRaw_leader (hψ : 0 < ψ) (l r : AgentState ψ) :
    (stationaryPersistentRaw hψ l r).1.leader = l.leader ∧ (stationaryPersistentRaw hψ l r).2.leader = r.leader := by
  unfold stationaryPersistentRaw
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader, singleUseControlTail_leader, doneCaptureSigMove_leader, compareSigDispatch_leader, compareSigDispatchActionOne_leader, authorizedCmpUpdate_leader, clearInputIncrementPair_leader, writeSeqGenerate_leader, writeActionPreservingComparison_leader, swPersistentThroughPrepare_leader, writeSeqAfterPrepareComparisonTransport_leader]

-- BirthGenerationControlRepair.lean:50
theorem genCleanAfterWait_leader (hpsi : psi > 0) (l r : AgentState psi) :
    (genCleanAfterWait hpsi l r).1.leader = l.leader ∧ (genCleanAfterWait hpsi l r).2.leader = r.leader := by
  unfold genCleanAfterWait
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader, singleUseControlTail_leader, doneCaptureSigMove_leader, compareSigDispatch_leader, compareSigDispatchActionOne_leader, authorizedCmpUpdate_leader, clearInputIncrementPair_leader, writeSeqGenerate_leader, writeActionPreservingComparison_leader, swPersistentThroughPrepare_leader, writeSeqAfterPrepareComparisonTransport_leader, stationaryPersistentRaw_leader]

-- WallSweepPreCheckResetRepair.lean:42
theorem preCheckResetWall_leader (l r : AuthorizedAgentState psi) :
    (preCheckResetWall l r).1.core.leader = l.core.leader ∧ (preCheckResetWall l r).2.core.leader = r.core.leader := by
  unfold preCheckResetWall
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader, singleUseControlTail_leader, doneCaptureSigMove_leader, compareSigDispatch_leader, compareSigDispatchActionOne_leader, authorizedCmpUpdate_leader, clearInputIncrementPair_leader, writeSeqGenerate_leader, writeActionPreservingComparison_leader, swPersistentThroughPrepare_leader, writeSeqAfterPrepareComparisonTransport_leader, stationaryPersistentRaw_leader, genCleanAfterWait_leader]

-- TerminalEqualSupportRepair.lean:69
theorem sanitizeAuthorizedPair_leader (hψ : ψ > 0) (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    (sanitizeAuthorizedPair hψ q).1.core.leader = q.1.core.leader ∧ (sanitizeAuthorizedPair hψ q).2.core.leader = q.2.core.leader := by
  unfold sanitizeAuthorizedPair
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader, singleUseControlTail_leader, doneCaptureSigMove_leader, compareSigDispatch_leader, compareSigDispatchActionOne_leader, authorizedCmpUpdate_leader, clearInputIncrementPair_leader, writeSeqGenerate_leader, writeActionPreservingComparison_leader, swPersistentThroughPrepare_leader, writeSeqAfterPrepareComparisonTransport_leader, stationaryPersistentRaw_leader, genCleanAfterWait_leader, preCheckResetWall_leader]

-- LeaderCreationCleanupRepair.lean:95
theorem markLeaderBirth_leader (born : Bool) (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    (markLeaderBirth born q).1.core.leader = q.1.core.leader ∧ (markLeaderBirth born q).2.core.leader = q.2.core.leader := by
  unfold markLeaderBirth
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_leader, writeSeqSetWriteReadyTransport_leader, writeSeqSetWriteAct_leader, writeSeqFinalR_leader, writeSeqCheckBit_leader, writeActionApplyOverwrite_leader, writeActionApplyMoveFlip_leader, genSigSaturatedFinish_leader, clearComparisonSignal_leader, resetKillComparison_leader, clearIfLeader_leader, clearIncrementAction_leader, compareSigInit_leader, cleanSigGenConnect_leader, cleanSigStep3_leader, cleanSigStep4_leader, cleanSigStep5_leader, cleanSigStep6_leader, cleanSigCleanApply_leader, checkSigSetReady_leader, checkSigCheckL_leader, checkSigCheckR_leader, checkSigSetResult_leader, eliminateSig_leader, disappear_leader, compareBitUpdateL_leader, compareBitUpdateR_leader, compareBit_leader, compareBitActionOne_leader, captureStep1_leader, holdDoneStep1_leader, sigMoveStep2_leader, sigMoveStep3_leader, sigMoveStep4_leader, sigMoveStep5_leader, singleUseApplyControl_leader, gatePreparedIncrement_leader, writeActionActivateNonempty_leader, writeActionExecutePreservingDepart_leader, writeActionExecutePreservingComparison_leader, writeSeqReadyTransport_leader, writeSeqCompare_leader, writeSeqCommands_leader, writeSeqPrepareTransport_leader, gensigWriteseq_leader, groupInfo_leader, waitSaturatedPrepare_leader, terminalInactiveClear_leader, waitWidthReset_leader, waitWidthFinish_leader, genSigSaturatedStart_leader, genCleanEmit_leader, genCleanPropagate_leader, suppressSigStart_leader, suppressSigMoveReset_leader, suppressSigEcho_leader, suppressSigFinish_leader, normalizeDeletion_leader, markComparisonForDeletion_leader, sanitizeAuthorizedTerminalEqual_leader, clearAuthorizedComparison_leader, cmpUpdateReturnPriority_leader, cmpUpdateSetPath2_leader, cleanSig_leader, comparisonLeaderWall_leader, sigMoveLeaderPreclear_leader, controlTransfers_leader, doneTransfers_leader, singleUseControlTail_leader, doneCaptureSigMove_leader, compareSigDispatch_leader, compareSigDispatchActionOne_leader, authorizedCmpUpdate_leader, clearInputIncrementPair_leader, writeSeqGenerate_leader, writeActionPreservingComparison_leader, swPersistentThroughPrepare_leader, writeSeqAfterPrepareComparisonTransport_leader, stationaryPersistentRaw_leader, genCleanAfterWait_leader, preCheckResetWall_leader, sanitizeAuthorizedPair_leader]


theorem authorizedEliminateSig_leader (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedEliminateSig hψ l r).1.core.leader = l.core.leader ∧
      (authorizedEliminateSig hψ l r).2.core.leader = r.core.leader := by
  unfold authorizedEliminateSig
  rw [(BirthB1InnerCountFrames.authorizedReconcile_core _ l r).1, (BirthB1InnerCountFrames.authorizedReconcile_core _ l r).2]
  exact eliminateSig_leader hψ l.core r.core

theorem authorizedCleanSig_leader (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedCleanSig hψ l r).1.core.leader = l.core.leader ∧
      (authorizedCleanSig hψ l r).2.core.leader = r.core.leader := by
  unfold authorizedCleanSig
  rw [(BirthB1InnerCountFrames.authorizedReconcile_core _ l r).1, (BirthB1InnerCountFrames.authorizedReconcile_core _ l r).2]
  exact cleanSig_leader hψ l.core r.core

theorem authorizedDisappear_leader (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedDisappear hψ l r).1.core.leader = l.core.leader ∧
      (authorizedDisappear hψ l r).2.core.leader = r.core.leader := by
  unfold authorizedDisappear
  rw [(BirthB1InnerCountFrames.authorizedReconcile_core _ l r).1, (BirthB1InnerCountFrames.authorizedReconcile_core _ l r).2]
  exact disappear_leader hψ l.core r.core

-- authorizedCheckSig_leader removed (depends on a leader writer; not needed after the SUPPRESS stage)

theorem stationaryPersistentAuthorizedRow_leader (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    (stationaryPersistentAuthorizedRow hψ l r).1.core.leader = l.core.leader ∧
      (stationaryPersistentAuthorizedRow hψ l r).2.core.leader = r.core.leader := by
  unfold stationaryPersistentAuthorizedRow
  rw [(BirthB1InnerCountFrames.authorizedReconcile_core _ l r).1, (BirthB1InnerCountFrames.authorizedReconcile_core _ l r).2]
  exact stationaryPersistentRaw_leader hψ l.core r.core

-- authorizedPPsiLeaderResetProbeWall_leader removed (depends on a leader writer; not needed after the SUPPRESS stage)

theorem authorizedDoneMove_leader (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedDoneMove hpsi l r).1.core.leader = l.core.leader ∧
      (authorizedDoneMove hpsi l r).2.core.leader = r.core.leader := by
  unfold authorizedDoneMove
  simp only []
  split
  · exact doneCaptureSigMove_leader hpsi l.core r.core
  · exact doneCaptureSigMove_leader hpsi l.core r.core

-- congestGuardCheck_leader removed (depends on a leader writer; not needed after the SUPPRESS stage)

-- preserveTossCheck_leader' removed (depends on a leader writer; not needed after the SUPPRESS stage)

-- preserveDoneCheck_leader removed (depends on a leader writer; not needed after the SUPPRESS stage)


/-! Leader frames for the SUPPRESS chain (it writes reset_cmd/echo/count, never leader). -/
theorem shortCountReset_leader {width : Nat} (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) :
    (shortCountReset hwidth hle l r).1.leader = l.leader ∧ (shortCountReset hwidth hle l r).2.leader = r.leader := by
  unfold shortCountReset
  split <;> exact ⟨rfl, rfl⟩

theorem suppressSigTerminal_leader (hψ : ψ > 0) (l r : AgentState ψ) :
    (suppressSigTerminal hψ l r).1.leader = l.leader ∧ (suppressSigTerminal hψ l r).2.leader = r.leader := by
  unfold suppressSigTerminal
  split <;> exact ⟨rfl, rfl⟩

theorem suppressPrefix_leader (l r : AgentState ψ) :
    (suppressPrefix l r).1.leader = l.leader ∧ (suppressPrefix l r).2.leader = r.leader := by
  unfold suppressPrefix
  simp only []
  have h0 := suppressSigStart_leader l r
  have hk1 := resetKillComparison_leader (suppressSigStart l r).1
  have hk2 := resetKillComparison_leader (suppressSigStart l r).2
  have h1 := suppressSigMoveReset_leader (resetKillComparison (suppressSigStart l r).1) (resetKillComparison (suppressSigStart l r).2)
  have hk3 := resetKillComparison_leader (suppressSigMoveReset (resetKillComparison (suppressSigStart l r).1) (resetKillComparison (suppressSigStart l r).2)).1
  have hk4 := resetKillComparison_leader (suppressSigMoveReset (resetKillComparison (suppressSigStart l r).1) (resetKillComparison (suppressSigStart l r).2)).2
  rw [hk3, hk4, h1.1, h1.2, hk1, hk2, h0.1, h0.2]
  exact ⟨rfl, rfl⟩

theorem suppressSigResetKillWidth_leader {width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (l r : AgentState ψ) :
    (suppressSigResetKillWidth hψ hwidth hle l r).1.leader = l.leader ∧
      (suppressSigResetKillWidth hψ hwidth hle l r).2.leader = r.leader := by
  unfold suppressSigResetKillWidth
  simp only []
  have h1 := suppressPrefix_leader l r
  have h2 := shortCountReset_leader hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2
  have h3 := suppressSigTerminal_leader hψ (shortCountReset hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2).1 (shortCountReset hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2).2
  have h4 := suppressSigEcho_leader (suppressSigTerminal hψ (shortCountReset hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2).1 (shortCountReset hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2).2).1 (suppressSigTerminal hψ (shortCountReset hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2).1 (shortCountReset hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2).2).2
  have h5 := suppressSigFinish_leader (suppressSigEcho (suppressSigTerminal hψ (shortCountReset hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2).1 (shortCountReset hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2).2).1 (suppressSigTerminal hψ (shortCountReset hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2).1 (shortCountReset hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2).2).2).1 (suppressSigEcho (suppressSigTerminal hψ (shortCountReset hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2).1 (shortCountReset hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2).2).1 (suppressSigTerminal hψ (shortCountReset hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2).1 (shortCountReset hwidth hle (suppressPrefix l r).1 (suppressPrefix l r).2).2).2).2
  rw [h5.1, h5.2, h4.1, h4.2, h3.1, h3.2, h2.1, h2.2, h1.1, h1.2]
  exact ⟨rfl, rfl⟩

theorem authorizedSuppressWidth_leader {width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (l r : AuthorizedAgentState ψ) :
    (authorizedSuppressWidth hψ hwidth hle l r).1.core.leader = l.core.leader ∧
      (authorizedSuppressWidth hψ hwidth hle l r).2.core.leader = r.core.leader := by
  unfold authorizedSuppressWidth
  rw [(BirthB1InnerCountFrames.authorizedReconcile_core _ l r).1, (BirthB1InnerCountFrames.authorizedReconcile_core _ l r).2]
  exact suppressSigResetKillWidth_leader hψ hwidth hle l.core r.core

end BirthB1InnerFieldFrames
