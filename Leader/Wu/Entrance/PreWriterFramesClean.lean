import Leader.Wu.Entrance.PreWriterFramesWait


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B6PreWriterFramesB


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLWallSweepRepair PPLLWallSweepFinite
open BirthGenerationDone BirthArrivalCaptureRepair BirthSingleUseReleaseRepair
open B6PreWriterFramesA


variable {ψ : Nat}


private theorem cleanConnect_frame (l r : AgentState ψ) :
    rawPreWriterFrame (cleanSigGenConnect l, cleanSigGenConnect r) =
      rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame cleanSigGenConnect
  dsimp only
  repeat (first | rfl | split)


private theorem clean3_frame (l r : AgentState ψ) :
    rawPreWriterFrame (cleanSigStep3 l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame cleanSigStep3; repeat (first | rfl | split)
private theorem clean4_frame (l r : AgentState ψ) :
    rawPreWriterFrame (cleanSigStep4 l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame cleanSigStep4; repeat (first | rfl | split)
private theorem clean5_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (cleanSigStep5 hψ l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame cleanSigStep5; repeat (first | rfl | split)
private theorem clean6_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (cleanSigStep6 hψ l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame cleanSigStep6; repeat (first | rfl | split)


private theorem cleanApply_left_frame (l r : AgentState ψ) :
    rawPreWriterFrame (cleanSigCleanApply l, r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame cleanSigCleanApply
  dsimp only
  repeat (first | rfl | split)
private theorem cleanApply_right_frame (l r : AgentState ψ) :
    rawPreWriterFrame (l, cleanSigCleanApply r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame cleanSigCleanApply
  dsimp only
  repeat (first | rfl | split)
private theorem cleanApply_frame (l r : AgentState ψ) :
    rawPreWriterFrame (cleanSigCleanApply l, cleanSigCleanApply r) =
      rawPreWriterFrame (l, r) :=
  (cleanApply_left_frame l (cleanSigCleanApply r)).trans
    (cleanApply_right_frame l r)


private theorem cleanRaw_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (cleanSig hψ l r) = rawPreWriterFrame (l, r) := by
  unfold cleanSig
  dsimp only
  rw [cleanApply_frame, clean6_frame, clean5_frame,
    clean4_frame, clean3_frame, cleanConnect_frame]


theorem clean_frame (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    PreWriterFrame (authorizedCleanSig hψ l r) = PreWriterFrame (l, r) := by
  unfold authorizedCleanSig
  exact authorizedReconcile_frame _ (cleanRaw_frame hψ) l r


private theorem eliminateRaw_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (eliminateSig hψ l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame eliminateSig
  dsimp only
  repeat (first | rfl | split)


theorem eliminate_frame (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    PreWriterFrame (authorizedEliminateSig hψ l r) = PreWriterFrame (l, r) := by
  unfold authorizedEliminateSig
  exact authorizedReconcile_frame _ (eliminateRaw_frame hψ) l r


private theorem clearLeft_frame (l r : AgentState ψ) :
    rawPreWriterFrame (clearComparisonSignal l, r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame clearComparisonSignal; rfl
private theorem clearRight_frame (l r : AgentState ψ) :
    rawPreWriterFrame (l, clearComparisonSignal r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame clearComparisonSignal; rfl
private theorem clearIfLeader_right_frame (l r : AgentState ψ) :
    rawPreWriterFrame (l, clearIfLeader r) = rawPreWriterFrame (l, r) := by
  unfold clearIfLeader
  split
  · exact clearRight_frame l r
  · rfl


private theorem preclear_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (sigMoveLeaderPreclear hψ l r) = rawPreWriterFrame (l, r) := by
  unfold sigMoveLeaderPreclear
  dsimp only
  split
  · exact (clearLeft_frame l (clearIfLeader r)).trans
      (clearIfLeader_right_frame l r)
  · exact clearIfLeader_right_frame l r


private theorem capture_frame (l r : AgentState ψ) :
    rawPreWriterFrame (captureStep1 l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame captureStep1; dsimp only
  repeat (first | rfl | split)
private theorem step2_frame (l r : AgentState ψ) :
    rawPreWriterFrame (sigMoveStep2 l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame sigMoveStep2; repeat (first | rfl | split)
private theorem step3_frame (l r : AgentState ψ) :
    rawPreWriterFrame (sigMoveStep3 l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame sigMoveStep3; repeat (first | rfl | split)
private theorem step4_frame (l r : AgentState ψ) :
    rawPreWriterFrame (sigMoveStep4 l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame sigMoveStep4; repeat (first | rfl | split)
private theorem step5_frame (l r : AgentState ψ) :
    rawPreWriterFrame (sigMoveStep5 l r) = rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame sigMoveStep5; repeat (first | rfl | split)


private theorem holdDone_frame (l r : AgentState ψ) :
    rawPreWriterFrame (holdDoneStep1 l r) = rawPreWriterFrame (l, r) := by
  unfold holdDoneStep1
  split
  · rfl
  · exact capture_frame l r


private theorem controlTransfers_frame (l r : AgentState ψ) :
    rawPreWriterFrame (controlTransfers l r) = rawPreWriterFrame (l, r) := by
  unfold controlTransfers
  dsimp only
  rw [step5_frame, step4_frame, step3_frame, step2_frame]


private theorem doneTransfers_frame (l r : AgentState ψ) :
    rawPreWriterFrame (doneTransfers l r) = rawPreWriterFrame (l, r) := by
  unfold doneTransfers
  dsimp only
  rw [controlTransfers_frame, holdDone_frame]


private theorem leaderWall_frame (l r : AgentState ψ) :
    rawPreWriterFrame (comparisonLeaderWall l r) = rawPreWriterFrame (l, r) := by
  unfold comparisonLeaderWall
  dsimp only
  split
  · split
    · exact (clearLeft_frame l (clearComparisonSignal r)).trans
        (clearRight_frame l r)
    · exact clearLeft_frame l r
  · split
    · exact clearRight_frame l r
    · rfl


private theorem applyControl_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame
        (singleUseApplyControl hψ l, singleUseApplyControl hψ r) =
      rawPreWriterFrame (l, r) := by
  unfold rawPreWriterFrame singleUseApplyControl
  dsimp only
  repeat (first | rfl | split)


private theorem controlTail_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (singleUseControlTail hψ l r) = rawPreWriterFrame (l, r) := by
  unfold singleUseControlTail
  dsimp only
  split
  · split
    · simpa [rawPreWriterFrame] using applyControl_frame hψ l r
    · exact applyControl_frame hψ l r
  · exact applyControl_frame hψ l r


private theorem doneRaw_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (doneCaptureSigMove hψ l r) = rawPreWriterFrame (l, r) := by
  unfold doneCaptureSigMove
  dsimp only
  rw [controlTail_frame, leaderWall_frame, doneTransfers_frame, preclear_frame]


theorem doneMove_frame (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    PreWriterFrame (authorizedDoneMove hψ l r) = PreWriterFrame (l, r) := by
  change rawPreWriterFrame
      ((authorizedDoneMove hψ l r).1.core,
       (authorizedDoneMove hψ l r).2.core) = _
  exact (congrArg rawPreWriterFrame (authorizedDoneMove_core hψ l r)).trans
    (doneRaw_frame hψ l.core r.core)


end B6PreWriterFramesB


#print axioms B6PreWriterFramesB.clean_frame
#print axioms B6PreWriterFramesB.eliminate_frame
#print axioms B6PreWriterFramesB.doneMove_frame
