import Leader.Wu.Birth.ShortDoneTerminalHost

set_option autoImplicit false

namespace BirthB1InnerCountFrames

open PPLLWallSweepFinite PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair BirthCheckCongestGuardRepair PPLLCompleteMultiLeaderCleanup BirthShortDoneCuts BirthArrivalCaptureRepair BirthGenerationControlRepair BirthGenerationDone BirthShortWait BirthShortWaitTerminalEntryRepair BirthSingleUseReleaseRepair BirthStationaryWrite BirthTossCheckPreservationRepair PPLL PPLLLeaderCreationCleanupRepair PPLLRepair PPLLTerminalEqualSupportRepair PPLLWallSweepPreCheckResetRepair PPLLWallSweepRepair PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair

variable {ψ psi κ kappa τ tau width n : Nat}

/-- Authorization reconciliation keeps the raw pair. -/
theorem authorizedReconcile_core (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthorizedAgentState ψ) :
    (authorizedReconcile f l r).1.core = (f l.core r.core).1 ∧
      (authorizedReconcile f l r).2.core = (f l.core r.core).2 := ⟨rfl, rfl⟩

-- Repairs.lean:1085
theorem compareBitUpdateRActionOne_count {ψ : Nat} (hψ : ψ > 0) (r : AgentState ψ) :
    (compareBitUpdateRActionOne hψ r).count = r.count := by
  unfold compareBitUpdateRActionOne
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- WriteSeqPersistenceRepair.lean:74
theorem writeSeqSetWriteReadyTransport_count (u : AgentState ψ) :
    (writeSeqSetWriteReadyTransport u).count = u.count := by
  unfold writeSeqSetWriteReadyTransport
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:982
theorem writeSeqSetWriteAct_count (u : AgentState ψ) :
    (writeSeqSetWriteAct u).count = u.count := by
  unfold writeSeqSetWriteAct
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:992
theorem writeSeqFinalR_count (r : AgentState ψ) :
    (writeSeqFinalR r).count = r.count := by
  unfold writeSeqFinalR
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:977
theorem writeSeqCheckBit_count (r : AgentState ψ) :
    (writeSeqCheckBit r).count = r.count := by
  unfold writeSeqCheckBit
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:785
theorem writeActionApplyOverwrite_count (r : AgentState ψ) :
    (writeActionApplyOverwrite r).count = r.count := by
  unfold writeActionApplyOverwrite
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Algorithm.lean:792
theorem writeActionApplyMoveFlip_count (r : AgentState ψ) :
    (writeActionApplyMoveFlip r).count = r.count := by
  unfold writeActionApplyMoveFlip
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- Repairs.lean:153
theorem genSigSaturatedFinish_count {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (genSigSaturatedFinish hψ l r).1.count = l.count ∧ (genSigSaturatedFinish hψ l r).2.count = r.count := by
  unfold genSigSaturatedFinish
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp)

-- WallSweepRepair.lean:25
theorem clearComparisonSignal_count (u : AgentState ψ) :
    (clearComparisonSignal u).count = u.count := by
  unfold clearComparisonSignal
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, ])

-- WallSweepRepair.lean:60
theorem resetKillComparison_count (u : AgentState ψ) :
    (resetKillComparison u).count = u.count := by
  unfold resetKillComparison
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count])

-- WallSweepRepair.lean:429
theorem clearIfLeader_count (u : AgentState ψ) :
    (clearIfLeader u).count = u.count := by
  unfold clearIfLeader
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count])

-- WriteIncrementGate.lean:28
theorem clearIncrementAction_count (u : AgentState ψ) :
    (clearIncrementAction u).count = u.count := by
  unfold clearIncrementAction
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count])

-- Algorithm.lean:436
theorem compareSigInit_count (l : AgentState ψ) :
    (compareSigInit l).count = l.count := by
  unfold compareSigInit
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count])

-- Algorithm.lean:121
theorem cleanSigGenConnect_count (u : AgentState ψ) :
    (cleanSigGenConnect u).count = u.count := by
  unfold cleanSigGenConnect
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count])

-- Algorithm.lean:147
theorem cleanSigStep3_count (l r : AgentState ψ) :
    (cleanSigStep3 l r).1.count = l.count ∧ (cleanSigStep3 l r).2.count = r.count := by
  unfold cleanSigStep3
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count])

-- Algorithm.lean:157
theorem cleanSigStep4_count (l r : AgentState ψ) :
    (cleanSigStep4 l r).1.count = l.count ∧ (cleanSigStep4 l r).2.count = r.count := by
  unfold cleanSigStep4
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count])

-- Algorithm.lean:167
theorem cleanSigStep5_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).1.count = l.count ∧ (cleanSigStep5 hψ l r).2.count = r.count := by
  unfold cleanSigStep5
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count])

-- Algorithm.lean:177
theorem cleanSigStep6_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).1.count = l.count ∧ (cleanSigStep6 hψ l r).2.count = r.count := by
  unfold cleanSigStep6
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count])

-- Algorithm.lean:129
theorem cleanSigCleanApply_count (u : AgentState ψ) :
    (cleanSigCleanApply u).count = u.count := by
  unfold cleanSigCleanApply
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count])

-- Algorithm.lean:226
theorem checkSigSetReady_count (u : AgentState ψ) :
    (checkSigSetReady u).count = u.count := by
  unfold checkSigSetReady
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count])

-- Algorithm.lean:235
theorem checkSigCheckL_count (hψ : ψ > 0) (u : AgentState ψ) :
    (checkSigCheckL hψ u).count = u.count := by
  unfold checkSigCheckL
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count])

-- Algorithm.lean:243
theorem checkSigCheckR_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).count = r.count := by
  unfold checkSigCheckR
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count])

-- Algorithm.lean:253
theorem checkSigSetResult_count (u : AgentState ψ) :
    (checkSigSetResult u).count = u.count := by
  unfold checkSigSetResult
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count])

-- Algorithm.lean:262
theorem checkSigSetLeader_count (hψ : ψ > 0) (r : AgentState ψ) :
    (checkSigSetLeader hψ r).count = r.count := by
  unfold checkSigSetLeader
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count])

-- Algorithm.lean:30
theorem pPsi_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (pPsi hψ l r).1.count = l.count ∧ (pPsi hψ l r).2.count = r.count := by
  unfold pPsi
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count])

-- Algorithm.lean:201
theorem eliminateSig_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.count = l.count ∧ (eliminateSig hψ l r).2.count = r.count := by
  unfold eliminateSig
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count])

-- Algorithm.lean:338
theorem disappear_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (disappear hψ l r).1.count = l.count ∧ (disappear hψ l r).2.count = r.count := by
  unfold disappear
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count])

-- Algorithm.lean:403
theorem compareBitUpdateL_count (hψ : ψ > 0) (l : AgentState ψ) :
    (compareBitUpdateL hψ l).count = l.count := by
  unfold compareBitUpdateL
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count])

-- Algorithm.lean:411
theorem compareBitUpdateR_count (hψ : ψ > 0) (r : AgentState ψ) :
    (compareBitUpdateR hψ r).count = r.count := by
  unfold compareBitUpdateR
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count])

-- Algorithm.lean:428
theorem compareBit_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareBit hψ l r).1.count = l.count ∧ (compareBit hψ l r).2.count = r.count := by
  unfold compareBit
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count])

-- MultiLeaderCleanup.lean:53
theorem compareBitActionOne_count (hpsi : psi > 0) (l r : AgentState psi) :
    (compareBitActionOne hpsi l r).1.count = l.count ∧ (compareBitActionOne hpsi l r).2.count = r.count := by
  unfold compareBitActionOne
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count])

-- BirthArrivalCaptureRepair.lean:28
theorem captureStep1_count (l r : AgentState psi) :
    (captureStep1 l r).1.count = l.count ∧ (captureStep1 l r).2.count = r.count := by
  unfold captureStep1
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count])

-- BirthGenerationDone.lean:66
theorem holdDoneStep1_count (l r : AgentState psi) :
    (holdDoneStep1 l r).1.count = l.count ∧ (holdDoneStep1 l r).2.count = r.count := by
  unfold holdDoneStep1
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count])

-- Algorithm.lean:482
theorem sigMoveStep2_count (l r : AgentState ψ) :
    (sigMoveStep2 l r).1.count = l.count ∧ (sigMoveStep2 l r).2.count = r.count := by
  unfold sigMoveStep2
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count])

-- Algorithm.lean:491
theorem sigMoveStep3_count (l r : AgentState ψ) :
    (sigMoveStep3 l r).1.count = l.count ∧ (sigMoveStep3 l r).2.count = r.count := by
  unfold sigMoveStep3
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count])

-- Algorithm.lean:500
theorem sigMoveStep4_count (l r : AgentState ψ) :
    (sigMoveStep4 l r).1.count = l.count ∧ (sigMoveStep4 l r).2.count = r.count := by
  unfold sigMoveStep4
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count])

-- Algorithm.lean:508
theorem sigMoveStep5_count (l r : AgentState ψ) :
    (sigMoveStep5 l r).1.count = l.count ∧ (sigMoveStep5 l r).2.count = r.count := by
  unfold sigMoveStep5
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count])

-- BirthSingleUseReleaseRepair.lean:103
theorem singleUseApplyControl_count (hpsi : psi > 0) (u : AgentState psi) :
    (singleUseApplyControl hpsi u).count = u.count := by
  unfold singleUseApplyControl
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count])

-- WriteIncrementGate.lean:33
theorem gatePreparedIncrement_count (u : AgentState ψ) :
    (gatePreparedIncrement u).count = u.count := by
  unfold gatePreparedIncrement
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count])

-- WriteSeqPersistenceRepair.lean:215
theorem writeActionActivateNonempty_count (hψ : ψ > 0) (u : AgentState ψ) :
    (writeActionActivateNonempty hψ u).count = u.count := by
  unfold writeActionActivateNonempty
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count])

-- WriteSeqPersistenceRepair.lean:177
theorem writeActionApplyIncrementAndFlip_count (r : AgentState ψ) :
    (writeActionApplyIncrementAndFlip r).count = r.count := by
  unfold writeActionApplyIncrementAndFlip
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, writeActionApplyIncrementAndFlip_count, writeActionPropagateState_count])

-- WriteSeqPersistenceRepair.lean:225
theorem writeActionPropagateState_count (l : AgentState ψ) (state : WriteState) :
    (writeActionPropagateState l state).count = l.count := by
  unfold writeActionPropagateState
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, writeActionApplyIncrementAndFlip_count, writeActionPropagateState_count])

-- WriteSeqPersistenceRepair.lean:245
theorem writeActionExecutePreservingDepart_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeActionExecutePreservingDepart hψ l r).1.count = l.count ∧ (writeActionExecutePreservingDepart hψ l r).2.count = r.count := by
  unfold writeActionExecutePreservingDepart
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [writeActionApplyIncrementAndFlip_count, writeActionPropagateState_count, compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count])

-- WriteSeqPersistenceRepair.lean:263
theorem writeActionPreservingDepart_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeActionPreservingDepart hψ l r).1.count = l.count ∧ (writeActionPreservingDepart hψ l r).2.count = r.count := by
  unfold writeActionPreservingDepart
  try simp only []
  have h := writeActionExecutePreservingDepart_count hψ (writeActionActivateNonempty hψ l) (writeActionActivateNonempty hψ r)
  rw [h.1, h.2, writeActionActivateNonempty_count, writeActionActivateNonempty_count]
  exact ⟨rfl, rfl⟩

-- WriteSeqPersistenceRepair.lean:283
theorem writeActionExecutePreservingComparison_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeActionExecutePreservingComparison hψ l r).1.count = l.count ∧ (writeActionExecutePreservingComparison hψ l r).2.count = r.count := by
  unfold writeActionExecutePreservingComparison
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count])

-- WriteSeqPersistenceRepair.lean:139
theorem writeSeqReadyTransport_count (l r : AgentState ψ) :
    (writeSeqReadyTransport l r).1.count = l.count ∧ (writeSeqReadyTransport l r).2.count = r.count := by
  unfold writeSeqReadyTransport
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count])

-- Algorithm.lean:1018
theorem writeSeqCompare_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqCompare hψ l r).1.count = l.count ∧ (writeSeqCompare hψ l r).2.count = r.count := by
  unfold writeSeqCompare
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count])

-- Algorithm.lean:1030
theorem writeSeqCommands_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqCommands hψ l r).1.count = l.count ∧ (writeSeqCommands hψ l r).2.count = r.count := by
  unfold writeSeqCommands
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count])

-- WriteSeqPersistenceRepair.lean:144
theorem writeSeqPrepareTransport_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqPrepareTransport hψ l r).1.count = l.count ∧ (writeSeqPrepareTransport hψ l r).2.count = r.count := by
  unfold writeSeqPrepareTransport
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count])

-- Algorithm.lean:749
theorem gensigWriteseq_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (gensigWriteseq hψ l r).1.count = l.count ∧ (gensigWriteseq hψ l r).2.count = r.count := by
  unfold gensigWriteseq
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count])

-- Algorithm.lean:668
theorem groupInfo_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (groupInfo hψ l r).1.count = l.count ∧ (groupInfo hψ l r).2.count = r.count := by
  unfold groupInfo
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count])

-- Repairs.lean:61
theorem waitSaturatedPrepare_count {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (waitSaturatedPrepare hψ l r).1.count = l.count ∧ (waitSaturatedPrepare hψ l r).2.count = r.count := by
  unfold waitSaturatedPrepare
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count])

-- BirthShortWaitTerminalEntryRepair.lean:31
theorem terminalInactiveClear_count {psi width : Nat} (hwidth : 0 < width) (hle : width ≤ psi) (l r : AgentState psi) :
    (terminalInactiveClear hwidth hle l r).1.count = l.count ∧ (terminalInactiveClear hwidth hle l r).2.count = r.count := by
  unfold terminalInactiveClear
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count])

-- BirthShortWait.lean:46
theorem waitWidthReset_count {psi width : Nat} (hwidth : 0 < width) (hle : width <= psi) (l r : AgentState psi) :
    (waitWidthReset hwidth hle l r).1.count = l.count ∧ (waitWidthReset hwidth hle l r).2.count = r.count := by
  unfold waitWidthReset
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count])

-- BirthShortWait.lean:59
theorem waitWidthFinish_count {psi width : Nat} (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi) (kappa : Nat) (l r : AgentState psi) :
    (waitWidthFinish hpsi hwidth hle kappa l r).1.count = l.count ∧ (waitWidthFinish hpsi hwidth hle kappa l r).2.count = r.count := by
  unfold waitWidthFinish
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count])

-- Repairs.lean:119
theorem genSigSaturatedStart_count {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (genSigSaturatedStart hψ l r).1.count = l.count ∧ (genSigSaturatedStart hψ l r).2.count = r.count := by
  unfold genSigSaturatedStart
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count])

-- BirthGenerationControlRepair.lean:27
theorem genCleanEmit_count (hpsi : psi > 0) (l r : AgentState psi) :
    (genCleanEmit hpsi l r).1.count = l.count ∧ (genCleanEmit hpsi l r).2.count = r.count := by
  unfold genCleanEmit
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count])

-- BirthGenerationControlRepair.lean:39
theorem genCleanPropagate_count (hpsi : psi > 0) (l r : AgentState psi) :
    (genCleanPropagate hpsi l r).1.count = l.count ∧ (genCleanPropagate hpsi l r).2.count = r.count := by
  unfold genCleanPropagate
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count])

-- Algorithm.lean:535
theorem suppressSigStart_count (l r : AgentState ψ) :
    (suppressSigStart l r).1.count = l.count ∧ (suppressSigStart l r).2.count = r.count := by
  unfold suppressSigStart
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count])

-- Algorithm.lean:539
theorem suppressSigMoveReset_count (l r : AgentState ψ) :
    (suppressSigMoveReset l r).1.count = l.count ∧ (suppressSigMoveReset l r).2.count = r.count := by
  unfold suppressSigMoveReset
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count])

-- Algorithm.lean:552
theorem suppressSigEcho_count (l r : AgentState ψ) :
    (suppressSigEcho l r).1.count = l.count ∧ (suppressSigEcho l r).2.count = r.count := by
  unfold suppressSigEcho
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count])

-- Algorithm.lean:561
theorem suppressSigFinish_count (l r : AgentState ψ) :
    (suppressSigFinish l r).1.count = l.count ∧ (suppressSigFinish l r).2.count = r.count := by
  unfold suppressSigFinish
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count])

-- LeaderCreationCleanupRepair.lean:42
theorem normalizeDeletion_count (u : AuthorizedAgentState ψ) :
    (normalizeDeletion u).core.count = u.core.count := by
  unfold normalizeDeletion
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count])

-- LeaderCreationCleanupRepair.lean:49
theorem markComparisonForDeletion_count (u : AuthorizedAgentState ψ) :
    (markComparisonForDeletion u).core.count = u.core.count := by
  unfold markComparisonForDeletion
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count])

-- TerminalEqualSupportRepair.lean:62
theorem sanitizeAuthorizedTerminalEqual_count (hψ : ψ > 0) (u : AuthorizedAgentState ψ) :
    (sanitizeAuthorizedTerminalEqual hψ u).core.count = u.core.count := by
  unfold sanitizeAuthorizedTerminalEqual
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count])

-- WallSweepPreCheckResetRepair.lean:35
theorem clearAuthorizedComparison_count (u : AuthorizedAgentState psi) :
    (clearAuthorizedComparison u).core.count = u.core.count := by
  unfold clearAuthorizedComparison
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count])

-- AuthorizedComparisonRepair.lean:151
theorem cmpUpdateReturnPriority_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (cmpUpdateReturnPriority hψ l r).1.count = l.count ∧ (cmpUpdateReturnPriority hψ l r).2.count = r.count := by
  unfold cmpUpdateReturnPriority
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count])

-- Algorithm.lean:386
theorem cmpUpdateSetPath2_count (hψ : ψ > 0) (l : AgentState ψ) :
    (cmpUpdateSetPath2 hψ l).count = l.count := by
  unfold cmpUpdateSetPath2
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count])

-- Algorithm.lean:187
theorem cleanSig_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSig hψ l r).1.count = l.count ∧ (cleanSig hψ l r).2.count = r.count := by
  unfold cleanSig
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count]

-- Algorithm.lean:277
theorem checkSig_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (checkSig hψ l r).1.count = l.count ∧ (checkSig hψ l r).2.count = r.count := by
  unfold checkSig
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count]

-- WallSweepRepair.lean:116
theorem pPsiLeaderResetProbeWall_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (pPsiLeaderResetProbeWall hψ l r).1.count = l.count ∧ (pPsiLeaderResetProbeWall hψ l r).2.count = r.count := by
  unfold pPsiLeaderResetProbeWall
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count]

-- WallSweepRepair.lean:74
theorem comparisonLeaderWall_count (l r : AgentState ψ) :
    (comparisonLeaderWall l r).1.count = l.count ∧ (comparisonLeaderWall l r).2.count = r.count := by
  unfold comparisonLeaderWall
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count]

-- WallSweepRepair.lean:456
theorem sigMoveLeaderPreclear_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (sigMoveLeaderPreclear hψ l r).1.count = l.count ∧ (sigMoveLeaderPreclear hψ l r).2.count = r.count := by
  unfold sigMoveLeaderPreclear
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count]

-- BirthGenerationDone.lean:81
theorem controlTransfers_count (l r : AgentState psi) :
    (controlTransfers l r).1.count = l.count ∧ (controlTransfers l r).2.count = r.count := by
  unfold controlTransfers
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count]

-- BirthGenerationDone.lean:88
theorem doneTransfers_count (l r : AgentState psi) :
    (doneTransfers l r).1.count = l.count ∧ (doneTransfers l r).2.count = r.count := by
  unfold doneTransfers
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count]

-- BirthSingleUseReleaseRepair.lean:137
theorem singleUseControlTail_count (hpsi : psi > 0) (l r : AgentState psi) :
    (singleUseControlTail hpsi l r).1.count = l.count ∧ (singleUseControlTail hpsi l r).2.count = r.count := by
  unfold singleUseControlTail
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count]

-- BirthGenerationDone.lean:178
theorem doneCaptureSigMove_count (hpsi : psi > 0) (l r : AgentState psi) :
    (doneCaptureSigMove hpsi l r).1.count = l.count ∧ (doneCaptureSigMove hpsi l r).2.count = r.count := by
  unfold doneCaptureSigMove
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count, singleUseControlTail_count]

-- Algorithm.lean:441
theorem compareSigDispatch_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (compareSigDispatch hψ l r).1.count = l.count ∧ (compareSigDispatch hψ l r).2.count = r.count := by
  unfold compareSigDispatch
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count, singleUseControlTail_count, doneCaptureSigMove_count]

-- MultiLeaderCleanup.lean:62
theorem compareSigDispatchActionOne_count (hpsi : psi > 0) (l r : AgentState psi) :
    (compareSigDispatchActionOne hpsi l r).1.count = l.count ∧ (compareSigDispatchActionOne hpsi l r).2.count = r.count := by
  unfold compareSigDispatchActionOne
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count, singleUseControlTail_count, doneCaptureSigMove_count, compareSigDispatch_count]

-- AuthorizedComparisonRepair.lean:168
theorem authorizedCmpUpdate_count (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedCmpUpdate hψ l r).1.core.count = l.core.count ∧ (authorizedCmpUpdate hψ l r).2.core.count = r.core.count := by
  unfold authorizedCmpUpdate
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count, singleUseControlTail_count, doneCaptureSigMove_count, compareSigDispatch_count, compareSigDispatchActionOne_count]

-- WriteSeqPersistenceRepair.lean:152
theorem clearInputIncrementPair_count (l r : AgentState ψ) :
    (clearInputIncrementPair l r).1.count = l.count ∧ (clearInputIncrementPair l r).2.count = r.count := by
  unfold clearInputIncrementPair
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count, singleUseControlTail_count, doneCaptureSigMove_count, compareSigDispatch_count, compareSigDispatchActionOne_count, authorizedCmpUpdate_count]

-- Algorithm.lean:1007
theorem writeSeqGenerate_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqGenerate hψ l r).1.count = l.count ∧ (writeSeqGenerate hψ l r).2.count = r.count := by
  unfold writeSeqGenerate
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count, singleUseControlTail_count, doneCaptureSigMove_count, compareSigDispatch_count, compareSigDispatchActionOne_count, authorizedCmpUpdate_count, clearInputIncrementPair_count]

-- WriteSeqPersistenceRepair.lean:290
theorem writeActionPreservingComparison_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeActionPreservingComparison hψ l r).1.count = l.count ∧ (writeActionPreservingComparison hψ l r).2.count = r.count := by
  unfold writeActionPreservingComparison
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count, singleUseControlTail_count, doneCaptureSigMove_count, compareSigDispatch_count, compareSigDispatchActionOne_count, authorizedCmpUpdate_count, clearInputIncrementPair_count, writeSeqGenerate_count]

-- BirthStationaryWritePersistent.lean:24
theorem swPersistentThroughPrepare_count (hψ : 0 < ψ) (l r : AgentState ψ) :
    (swPersistentThroughPrepare hψ l r).1.count = l.count ∧ (swPersistentThroughPrepare hψ l r).2.count = r.count := by
  unfold swPersistentThroughPrepare
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count, singleUseControlTail_count, doneCaptureSigMove_count, compareSigDispatch_count, compareSigDispatchActionOne_count, authorizedCmpUpdate_count, clearInputIncrementPair_count, writeSeqGenerate_count, writeActionPreservingComparison_count]

-- Algorithm.lean:875
theorem moveWsigCheckGenWs_count (l r : AgentState ψ) :
    (moveWsigCheckGenWs l r).count = r.count := by
  unfold moveWsigCheckGenWs
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [])

-- Algorithm.lean:891
theorem moveWsigStart_count (l r : AgentState ψ) :
    (moveWsigStart l r).1.count = l.count ∧ (moveWsigStart l r).2.count = r.count := by
  unfold moveWsigStart
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_count])

-- Algorithm.lean:882
theorem moveWsigCheckLast_count (l : AgentState ψ) :
    (moveWsigCheckLast l).count = l.count := by
  unfold moveWsigCheckLast
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_count, moveWsigStart_count])

-- WriteSeqPersistenceRepair.lean:332
theorem moveWsigTransferStopAligned_count (l r : AgentState ψ) :
    (moveWsigTransferStopAligned l r).1.count = l.count ∧ (moveWsigTransferStopAligned l r).2.count = r.count := by
  unfold moveWsigTransferStopAligned
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_count, moveWsigStart_count, moveWsigCheckLast_count])

-- WriteSeqPersistenceRepair.lean:364
theorem moveWsigMoveWritePreservingNonempty_count (l r : AgentState ψ) :
    (moveWsigMoveWritePreservingNonempty l r).1.count = l.count ∧ (moveWsigMoveWritePreservingNonempty l r).2.count = r.count := by
  unfold moveWsigMoveWritePreservingNonempty
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_count, moveWsigStart_count, moveWsigCheckLast_count, moveWsigTransferStopAligned_count])

-- Algorithm.lean:904
theorem moveWsigLeaderSignal_count (l r : AgentState ψ) :
    (moveWsigLeaderSignal l r).1.count = l.count ∧ (moveWsigLeaderSignal l r).2.count = r.count := by
  unfold moveWsigLeaderSignal
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_count, moveWsigStart_count, moveWsigCheckLast_count, moveWsigTransferStopAligned_count, moveWsigMoveWritePreservingNonempty_count])

-- Algorithm.lean:908
theorem moveWsigSignalMove_count (l r : AgentState ψ) :
    (moveWsigSignalMove l r).1.count = l.count ∧ (moveWsigSignalMove l r).2.count = r.count := by
  unfold moveWsigSignalMove
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_count, moveWsigStart_count, moveWsigCheckLast_count, moveWsigTransferStopAligned_count, moveWsigMoveWritePreservingNonempty_count, moveWsigLeaderSignal_count])

-- Algorithm.lean:916
theorem moveWsigEchoMove_count (l r : AgentState ψ) :
    (moveWsigEchoMove l r).1.count = l.count ∧ (moveWsigEchoMove l r).2.count = r.count := by
  unfold moveWsigEchoMove
  try dsimp only
  repeat' split
  all_goals (first | rfl | simp [moveWsigCheckGenWs_count, moveWsigStart_count, moveWsigCheckLast_count, moveWsigTransferStopAligned_count, moveWsigMoveWritePreservingNonempty_count, moveWsigLeaderSignal_count, moveWsigSignalMove_count])

-- WriteSeqPersistenceRepair.lean:388
theorem moveWsigFinishPreservingCommand_count (l r : AgentState ψ) :
    (moveWsigFinishPreservingCommand l r).1.count = l.count ∧ (moveWsigFinishPreservingCommand l r).2.count = r.count := by
  unfold moveWsigFinishPreservingCommand
  try dsimp only
  repeat' split
  all_goals simp_all [moveWsigCheckGenWs_count, moveWsigStart_count, moveWsigCheckLast_count, moveWsigTransferStopAligned_count, moveWsigMoveWritePreservingNonempty_count, moveWsigLeaderSignal_count, moveWsigSignalMove_count, moveWsigEchoMove_count]

-- WriteSeqPersistenceRepair.lean:397
theorem moveWsigStopAligned_count (_hψ : ψ > 0) (l r : AgentState ψ) :
    (moveWsigStopAligned _hψ l r).1.count = l.count ∧ (moveWsigStopAligned _hψ l r).2.count = r.count := by
  unfold moveWsigStopAligned
  try dsimp only
  repeat' split
  all_goals simp_all [moveWsigCheckGenWs_count, moveWsigStart_count, moveWsigCheckLast_count, moveWsigTransferStopAligned_count, moveWsigMoveWritePreservingNonempty_count, moveWsigLeaderSignal_count, moveWsigSignalMove_count, moveWsigEchoMove_count, moveWsigFinishPreservingCommand_count]

-- WriteSeqPersistenceRepair.lean:412
theorem writeSeqAfterPrepareComparisonTransport_count (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeqAfterPrepareComparisonTransport hψ l r).1.count = l.count ∧ (writeSeqAfterPrepareComparisonTransport hψ l r).2.count = r.count := by
  unfold writeSeqAfterPrepareComparisonTransport
  try dsimp only
  repeat' split
  all_goals simp_all [moveWsigStopAligned_count, compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count, singleUseControlTail_count, doneCaptureSigMove_count, compareSigDispatch_count, compareSigDispatchActionOne_count, authorizedCmpUpdate_count, clearInputIncrementPair_count, writeSeqGenerate_count, writeActionPreservingComparison_count, swPersistentThroughPrepare_count]

-- BirthStationaryWritePersistent.lean:32
theorem stationaryPersistentRaw_count (hψ : 0 < ψ) (l r : AgentState ψ) :
    (stationaryPersistentRaw hψ l r).1.count = l.count ∧ (stationaryPersistentRaw hψ l r).2.count = r.count := by
  unfold stationaryPersistentRaw
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count, singleUseControlTail_count, doneCaptureSigMove_count, compareSigDispatch_count, compareSigDispatchActionOne_count, authorizedCmpUpdate_count, clearInputIncrementPair_count, writeSeqGenerate_count, writeActionPreservingComparison_count, swPersistentThroughPrepare_count, writeSeqAfterPrepareComparisonTransport_count]

-- BirthGenerationControlRepair.lean:50
theorem genCleanAfterWait_count (hpsi : psi > 0) (l r : AgentState psi) :
    (genCleanAfterWait hpsi l r).1.count = l.count ∧ (genCleanAfterWait hpsi l r).2.count = r.count := by
  unfold genCleanAfterWait
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count, singleUseControlTail_count, doneCaptureSigMove_count, compareSigDispatch_count, compareSigDispatchActionOne_count, authorizedCmpUpdate_count, clearInputIncrementPair_count, writeSeqGenerate_count, writeActionPreservingComparison_count, swPersistentThroughPrepare_count, writeSeqAfterPrepareComparisonTransport_count, stationaryPersistentRaw_count]

-- WallSweepPreCheckResetRepair.lean:42
theorem preCheckResetWall_count (l r : AuthorizedAgentState psi) :
    (preCheckResetWall l r).1.core.count = l.core.count ∧ (preCheckResetWall l r).2.core.count = r.core.count := by
  unfold preCheckResetWall
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count, singleUseControlTail_count, doneCaptureSigMove_count, compareSigDispatch_count, compareSigDispatchActionOne_count, authorizedCmpUpdate_count, clearInputIncrementPair_count, writeSeqGenerate_count, writeActionPreservingComparison_count, swPersistentThroughPrepare_count, writeSeqAfterPrepareComparisonTransport_count, stationaryPersistentRaw_count, genCleanAfterWait_count]

-- TerminalEqualSupportRepair.lean:69
theorem sanitizeAuthorizedPair_count (hψ : ψ > 0) (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    (sanitizeAuthorizedPair hψ q).1.core.count = q.1.core.count ∧ (sanitizeAuthorizedPair hψ q).2.core.count = q.2.core.count := by
  unfold sanitizeAuthorizedPair
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count, singleUseControlTail_count, doneCaptureSigMove_count, compareSigDispatch_count, compareSigDispatchActionOne_count, authorizedCmpUpdate_count, clearInputIncrementPair_count, writeSeqGenerate_count, writeActionPreservingComparison_count, swPersistentThroughPrepare_count, writeSeqAfterPrepareComparisonTransport_count, stationaryPersistentRaw_count, genCleanAfterWait_count, preCheckResetWall_count]

-- LeaderCreationCleanupRepair.lean:95
theorem markLeaderBirth_count (born : Bool) (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    (markLeaderBirth born q).1.core.count = q.1.core.count ∧ (markLeaderBirth born q).2.core.count = q.2.core.count := by
  unfold markLeaderBirth
  try dsimp only
  repeat' split
  all_goals simp_all [compareBitUpdateRActionOne_count, writeSeqSetWriteReadyTransport_count, writeSeqSetWriteAct_count, writeSeqFinalR_count, writeSeqCheckBit_count, writeActionApplyOverwrite_count, writeActionApplyMoveFlip_count, genSigSaturatedFinish_count, clearComparisonSignal_count, resetKillComparison_count, clearIfLeader_count, clearIncrementAction_count, compareSigInit_count, cleanSigGenConnect_count, cleanSigStep3_count, cleanSigStep4_count, cleanSigStep5_count, cleanSigStep6_count, cleanSigCleanApply_count, checkSigSetReady_count, checkSigCheckL_count, checkSigCheckR_count, checkSigSetResult_count, checkSigSetLeader_count, pPsi_count, eliminateSig_count, disappear_count, compareBitUpdateL_count, compareBitUpdateR_count, compareBit_count, compareBitActionOne_count, captureStep1_count, holdDoneStep1_count, sigMoveStep2_count, sigMoveStep3_count, sigMoveStep4_count, sigMoveStep5_count, singleUseApplyControl_count, gatePreparedIncrement_count, writeActionActivateNonempty_count, writeActionExecutePreservingDepart_count, writeActionExecutePreservingComparison_count, writeSeqReadyTransport_count, writeSeqCompare_count, writeSeqCommands_count, writeSeqPrepareTransport_count, gensigWriteseq_count, groupInfo_count, waitSaturatedPrepare_count, terminalInactiveClear_count, waitWidthReset_count, waitWidthFinish_count, genSigSaturatedStart_count, genCleanEmit_count, genCleanPropagate_count, suppressSigStart_count, suppressSigMoveReset_count, suppressSigEcho_count, suppressSigFinish_count, normalizeDeletion_count, markComparisonForDeletion_count, sanitizeAuthorizedTerminalEqual_count, clearAuthorizedComparison_count, cmpUpdateReturnPriority_count, cmpUpdateSetPath2_count, cleanSig_count, checkSig_count, pPsiLeaderResetProbeWall_count, comparisonLeaderWall_count, sigMoveLeaderPreclear_count, controlTransfers_count, doneTransfers_count, singleUseControlTail_count, doneCaptureSigMove_count, compareSigDispatch_count, compareSigDispatchActionOne_count, authorizedCmpUpdate_count, clearInputIncrementPair_count, writeSeqGenerate_count, writeActionPreservingComparison_count, swPersistentThroughPrepare_count, writeSeqAfterPrepareComparisonTransport_count, stationaryPersistentRaw_count, genCleanAfterWait_count, preCheckResetWall_count, sanitizeAuthorizedPair_count]


theorem authorizedEliminateSig_count (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedEliminateSig hψ l r).1.core.count = l.core.count ∧
      (authorizedEliminateSig hψ l r).2.core.count = r.core.count := by
  unfold authorizedEliminateSig
  rw [(authorizedReconcile_core _ l r).1, (authorizedReconcile_core _ l r).2]
  exact eliminateSig_count hψ l.core r.core

theorem authorizedCleanSig_count (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedCleanSig hψ l r).1.core.count = l.core.count ∧
      (authorizedCleanSig hψ l r).2.core.count = r.core.count := by
  unfold authorizedCleanSig
  rw [(authorizedReconcile_core _ l r).1, (authorizedReconcile_core _ l r).2]
  exact cleanSig_count hψ l.core r.core

theorem authorizedDisappear_count (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedDisappear hψ l r).1.core.count = l.core.count ∧
      (authorizedDisappear hψ l r).2.core.count = r.core.count := by
  unfold authorizedDisappear
  rw [(authorizedReconcile_core _ l r).1, (authorizedReconcile_core _ l r).2]
  exact disappear_count hψ l.core r.core

theorem authorizedCheckSig_count (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedCheckSig hψ l r).1.core.count = l.core.count ∧
      (authorizedCheckSig hψ l r).2.core.count = r.core.count := by
  unfold authorizedCheckSig
  rw [(authorizedReconcile_core _ l r).1, (authorizedReconcile_core _ l r).2]
  exact checkSig_count hψ l.core r.core

theorem stationaryPersistentAuthorizedRow_count (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    (stationaryPersistentAuthorizedRow hψ l r).1.core.count = l.core.count ∧
      (stationaryPersistentAuthorizedRow hψ l r).2.core.count = r.core.count := by
  unfold stationaryPersistentAuthorizedRow
  rw [(authorizedReconcile_core _ l r).1, (authorizedReconcile_core _ l r).2]
  exact stationaryPersistentRaw_count hψ l.core r.core

theorem authorizedPPsiLeaderResetProbeWall_count (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedPPsiLeaderResetProbeWall hψ l r).1.core.count = l.core.count ∧
      (authorizedPPsiLeaderResetProbeWall hψ l r).2.core.count = r.core.count := by
  unfold authorizedPPsiLeaderResetProbeWall
  simp only []
  exact pPsiLeaderResetProbeWall_count hψ l.core r.core

theorem authorizedDoneMove_count (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedDoneMove hpsi l r).1.core.count = l.core.count ∧
      (authorizedDoneMove hpsi l r).2.core.count = r.core.count := by
  unfold authorizedDoneMove
  simp only []
  split
  · exact doneCaptureSigMove_count hpsi l.core r.core
  · exact doneCaptureSigMove_count hpsi l.core r.core

theorem congestGuardCheck_count (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (congestGuardCheck hpsi l r).1.core.count = l.core.count ∧
      (congestGuardCheck hpsi l r).2.core.count = r.core.count := by
  unfold congestGuardCheck
  split
  · exact ⟨rfl, rfl⟩
  · exact authorizedCheckSig_count hpsi l r

theorem preserveTossCheck_count' (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (preserveTossCheck hpsi l r).1.core.count = l.core.count ∧
      (preserveTossCheck hpsi l r).2.core.count = r.core.count := by
  unfold preserveTossCheck
  split
  · exact ⟨rfl, rfl⟩
  · exact congestGuardCheck_count hpsi l r

theorem preserveDoneCheck_count (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (preserveDoneCheck hpsi l r).1.core.count = l.core.count ∧
      (preserveDoneCheck hpsi l r).2.core.count = r.core.count := by
  unfold preserveDoneCheck
  split
  · exact ⟨rfl, rfl⟩
  · exact preserveTossCheck_count' hpsi l r

end BirthB1InnerCountFrames
