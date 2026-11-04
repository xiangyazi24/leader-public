import Leader.Wu.Splice.OrdinaryBirthLabelGeneration
import Leader.Wu.WallSweep.Repair
import Leader.Wu.WallSweep.FiniteIntegration


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceV8BirthCaseAdapterLabelDone


open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
open PPLLWallSweepPreCheckResetContracts PPLLCompleteMultiLeaderCleanup
open BirthGenerationControlRepair BirthGenerationDone BirthShortWait
  BirthShortDoneTerminalEntryCut BirthSigMoveDisposalRepair
  BirthArrivalCaptureRepair BirthSingleUseReleaseRepair
  BirthTossCheckPreservationRepair BirthCheckCongestGuardRepair
open B9SpliceV8LeftLeaderOpaqueBridge B9SpliceV8BirthCaseAdapterLabelGen


variable {psi width kappa : Nat}


private theorem holdDoneStep1_labels (l r : AgentState psi) :
    rawLabels (holdDoneStep1 l r) = (l.label, r.label) := by
  unfold holdDoneStep1
  split
  · rfl
  · have h := captureStep1_path_and_sender_control l r
    exact Prod.ext h.2.2.2.1 h.2.2.2.2.1


private theorem step2_labels (l r : AgentState psi) :
    rawLabels (sigMoveStep2 l r) = (l.label, r.label) := by
  unfold rawLabels sigMoveStep2; repeat (first | rfl | split <;> try dsimp only)
private theorem step3_labels (l r : AgentState psi) :
    rawLabels (sigMoveStep3 l r) = (l.label, r.label) := by
  unfold rawLabels sigMoveStep3; repeat (first | rfl | split <;> try dsimp only)
private theorem step4_labels (l r : AgentState psi) :
    rawLabels (sigMoveStep4 l r) = (l.label, r.label) := by
  unfold rawLabels sigMoveStep4; repeat (first | rfl | split <;> try dsimp only)
private theorem step5_labels (l r : AgentState psi) :
    rawLabels (sigMoveStep5 l r) = (l.label, r.label) := by
  unfold rawLabels sigMoveStep5; repeat (first | rfl | split <;> try dsimp only)


private theorem doneTransfers_labels (l r : AgentState psi) :
    rawLabels (doneTransfers l r) = (l.label, r.label) := by
  let q0 := holdDoneStep1 l r; let q1 := sigMoveStep2 q0.1 q0.2
  let q2 := sigMoveStep3 q1.1 q1.2; let q3 := sigMoveStep4 q2.1 q2.2
  have h0 := holdDoneStep1_labels l r; have h1 := step2_labels q0.1 q0.2
  have h2 := step3_labels q1.1 q1.2; have h3 := step4_labels q2.1 q2.2
  have h4 := step5_labels q3.1 q3.2
  change rawLabels (sigMoveStep5 q3.1 q3.2) = (l.label, r.label)
  exact h4.trans (h3.trans (h2.trans (h1.trans h0)))


private theorem preclear_labels (hpsi : 0 < psi) (l r : AgentState psi) :
    rawLabels (PPLLWallSweepRepair.sigMoveLeaderPreclear hpsi l r) =
      (l.label, r.label) := by
  unfold rawLabels PPLLWallSweepRepair.sigMoveLeaderPreclear
    PPLLWallSweepRepair.incompleteLeftLeaderBoundary PPLLWallSweepRepair.clearIfLeader
  repeat (first | rfl | split <;> try dsimp only)


private theorem leaderWall_labels (l r : AgentState psi) :
    rawLabels (PPLLWallSweepRepair.comparisonLeaderWall l r) =
      (l.label, r.label) := by
  unfold rawLabels PPLLWallSweepRepair.comparisonLeaderWall PPLLWallSweepRepair.clearComparisonSignal
  repeat (first | rfl | split <;> try dsimp only)


private theorem singleUseTail_labels (hpsi : 0 < psi) (l r : AgentState psi) :
    rawLabels (singleUseControlTail hpsi l r) = (l.label, r.label) := by
  let old := PPLLWallSweepRepair.sigMoveControlTail hpsi l r
  have hold : rawLabels old = (l.label, r.label) := by
    let l0 := sigMoveApplyControl hpsi l; let r0 := sigMoveApplyControl hpsi r
    let l1 := if r0.state = .depart then
      if l0.label.val < psi - 1 ∧ l0.state = .CHECK_ready then
        { l0 with state := .depart } else l0 else l0
    have hl1 : l1.label = l0.label := by unfold l1; repeat (first | rfl | split)
    change (l1.label, r0.label) = (l.label, r.label)
    exact Prod.ext (hl1.trans (PPLLVerify.sigMoveApplyControl_label_eq hpsi l))
      (PPLLVerify.sigMoveApplyControl_label_eq hpsi r)
  have ht := singleUseControlTail_preserves_departure hpsi l r
  change (singleUseControlTail hpsi l r).1.state = old.1.state ∧
    (singleUseControlTail hpsi l r).2.state = old.2.state ∧
    (singleUseControlTail hpsi l r).1.path = old.1.path ∧
    (singleUseControlTail hpsi l r).2.path = old.2.path ∧
    (singleUseControlTail hpsi l r).1.label = old.1.label ∧
    (singleUseControlTail hpsi l r).2.label = old.2.label at ht
  exact (Prod.ext ht.2.2.2.2.1 ht.2.2.2.2.2).trans hold


private theorem doneCapture_labels (hpsi : 0 < psi) (l r : AgentState psi) :
    rawLabels (doneCaptureSigMove hpsi l r) = (l.label, r.label) := by
  let p := PPLLWallSweepRepair.sigMoveLeaderPreclear hpsi l r
  let m := doneTransfers p.1 p.2
  let w := PPLLWallSweepRepair.comparisonLeaderWall m.1 m.2
  have hp := preclear_labels hpsi l r
  have hm := doneTransfers_labels p.1 p.2
  have hw := leaderWall_labels m.1 m.2
  have ht := singleUseTail_labels hpsi w.1 w.2
  change rawLabels (singleUseControlTail hpsi w.1 w.2) = (l.label, r.label)
  exact ht.trans (hw.trans (hm.trans hp))


private theorem doneMove_labels (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) :
    authLabels (authorizedDoneMove hpsi l r) = authLabels (l, r) := by
  have hp := congrArg rawLabels (authorizedDoneMove_core hpsi l r)
  change authLabels (authorizedDoneMove hpsi l r) =
    rawLabels (doneCaptureSigMove hpsi l.core r.core) at hp
  exact hp.trans (doneCapture_labels hpsi l.core r.core)


private theorem sanitize_labels (hpsi : 0 < psi)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authLabels (sanitizeAuthorizedPair hpsi (preCheckResetWall q.1 q.2)) = authLabels q := by
  have h := sanitizePreCheckResetWall_peaceViewPair hpsi q
  exact Prod.ext (congrArg (fun z => z.1.label) h) (congrArg (fun z => z.2.label) h)


theorem doneBefore_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat) (l r : AuthorizedAgentState psi) :
    authLabels (doneBeforeCheckEntryWidth hpsi hwidth hle cap l r) =
      authLabels (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hpsi l r) := by
  let g := generationBeforeMoveEntryWidth hpsi hwidth hle cap l r
  let m := authorizedDoneMove hpsi g.1 g.2
  have hg := generation_labels hpsi hwidth hle cap l r
  have hm := doneMove_labels hpsi g.1 g.2
  have hz := sanitize_labels hpsi m
  have hs : doneBeforeCheckEntryWidth hpsi hwidth hle cap l r =
      sanitizeAuthorizedPair hpsi (preCheckResetWall m.1 m.2) :=
    doneBefore_eq_stages hpsi hwidth hle cap l r
  exact (congrArg authLabels hs).trans (hz.trans (hm.trans hg))


end B9SpliceV8BirthCaseAdapterLabelDone


#print axioms B9SpliceV8BirthCaseAdapterLabelDone.doneBefore_labels
