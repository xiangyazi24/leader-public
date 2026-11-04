import Leader.Wu.Entrance.PreWriterFramesClean


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B6PreWriterFramesC


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
  PPLLCompleteMultiLeaderCleanup PPLLNoCheckBirthConditionTwoPhysical
open BirthGenerationControlRepair BirthGenerationDone
  BirthArrivalCaptureRepair BirthSingleUseReleaseRepair
  BirthTossCheckPreservationRepair BirthCheckCongestGuardRepair
  BirthSigMoveDisposalRepair BirthShortWait
  BirthShortWaitTerminalEntryRepair BirthShortDoneTerminalEntryCut
  BirthShortDoneCuts BirthStationaryWrite BirthShortDoneTerminalHost
open B6WriterPremiseStage1 B6WriterPremiseStage2 B6MicroAlg18Disabled
open B6PreWriterFramesA B6PreWriterFramesB


variable {ψ κ width : Nat}


/-- The responder part of `PreWriterFrame`, packaged so the COMPARE proof is
written once rather than four times. -/
private def rightFrame (u : AgentState ψ) : PreWriterFrameView :=
  ⟨false, u.bit, u.path3, u.write, u.write_state⟩


private theorem rawFrame_of_left_right
    (l0 r0 l1 r1 : AgentState ψ)
    (hl : l1.leader = l0.leader)
    (hr : rightFrame r1 = rightFrame r0) :
    rawPreWriterFrame (l1, r1) = rawPreWriterFrame (l0, r0) := by
  unfold rawPreWriterFrame
  change PreWriterFrameView.mk l1.leader
      (rightFrame r1).rightBit (rightFrame r1).rightPath3
      (rightFrame r1).rightWrite (rightFrame r1).rightWriteState =
    PreWriterFrameView.mk l0.leader
      (rightFrame r0).rightBit (rightFrame r0).rightPath3
      (rightFrame r0).rightWrite (rightFrame r0).rightWriteState
  rw [hl, hr]


private theorem resetSanitize_right
    (hψ : 0 < ψ) (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    rightFrame
        (sanitizeAuthorizedPair hψ (preCheckResetWall q.1 q.2)).2.core =
      rightFrame q.2.core := by
  unfold rightFrame sanitizeAuthorizedPair sanitizeAuthorizedTerminalEqual
    preCheckResetWall clearAuthorizedComparison clearComparisonSignal
  dsimp only
  repeat (first | rfl | split)


/-- The pre-CHECK reset/sanitize wall frames the B6 writer projection. -/
theorem resetSanitize_frame
    (hψ : 0 < ψ) (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    PreWriterFrame (sanitizeAuthorizedPair hψ (preCheckResetWall q.1 q.2)) =
      PreWriterFrame q := by
  have hp := sanitizePreCheckResetWall_peaceViewPair hψ q
  have hl := congrArg
    (fun p : PeaceView ψ × PeaceView ψ => p.1.leader) hp
  change (sanitizeAuthorizedPair hψ
      (preCheckResetWall q.1 q.2)).1.core.leader = q.1.core.leader at hl
  change rawPreWriterFrame
      ((sanitizeAuthorizedPair hψ (preCheckResetWall q.1 q.2)).1.core,
       (sanitizeAuthorizedPair hψ (preCheckResetWall q.1 q.2)).2.core) =
    rawPreWriterFrame (q.1.core, q.2.core)
  exact rawFrame_of_left_right q.1.core q.2.core _ _ hl
    (resetSanitize_right hψ q)


private theorem checkReadyLeftRaw_frame (l r : AgentState ψ) :
    rawPreWriterFrame (checkSigSetReady l, r) = rawPreWriterFrame (l, r) := by
  unfold checkSigSetReady rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem checkReadyRightRaw_frame (l r : AgentState ψ) :
    rawPreWriterFrame (l, checkSigSetReady r) = rawPreWriterFrame (l, r) := by
  unfold checkSigSetReady rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem checkReadyPairRaw_frame (l r : AgentState ψ) :
    rawPreWriterFrame (checkSigSetReady l, checkSigSetReady r) =
      rawPreWriterFrame (l, r) :=
  (checkReadyLeftRaw_frame l (checkSigSetReady r)).trans
    (checkReadyRightRaw_frame l r)


private theorem checkLRaw_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (checkSigCheckL hψ l, r) =
      rawPreWriterFrame (l, r) := by
  unfold checkSigCheckL rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem checkRRaw_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (l, checkSigCheckR hψ l r) =
      rawPreWriterFrame (l, r) := by
  unfold checkSigCheckR rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem checkResultLeftRaw_frame (l r : AgentState ψ) :
    rawPreWriterFrame (checkSigSetResult l, r) =
      rawPreWriterFrame (l, r) := by
  unfold checkSigSetResult rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem checkResultRightRaw_frame (l r : AgentState ψ) :
    rawPreWriterFrame (l, checkSigSetResult r) =
      rawPreWriterFrame (l, r) := by
  unfold checkSigSetResult rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem checkResultPairRaw_frame (l r : AgentState ψ) :
    rawPreWriterFrame (checkSigSetResult l, checkSigSetResult r) =
      rawPreWriterFrame (l, r) :=
  (checkResultLeftRaw_frame l (checkSigSetResult r)).trans
    (checkResultRightRaw_frame l r)


private theorem checkLeaderRaw_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (l, checkSigSetLeader hψ r) =
      rawPreWriterFrame (l, r) := by
  unfold checkSigSetLeader rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem checkRaw_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (checkSig hψ l r) = rawPreWriterFrame (l, r) := by
  rw [checkSig_eq_staged]
  unfold checkSigStaged
  dsimp only
  rw [checkLeaderRaw_frame, checkResultPairRaw_frame,
    checkRRaw_frame, checkLRaw_frame, checkReadyPairRaw_frame]


/-- Literal CHECK may create the responder leader, outside this projection. -/
theorem check_frame (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    PreWriterFrame (authorizedCheckSig hψ l r) = PreWriterFrame (l, r) := by
  unfold authorizedCheckSig
  exact authorizedReconcile_frame _ (checkRaw_frame hψ) l r


/-- The actual guarded CHECK host is either a stutter or the framed CHECK. -/
theorem preserveDoneCheck_frame
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    PreWriterFrame (preserveDoneCheck hψ l r) = PreWriterFrame (l, r) := by
  unfold preserveDoneCheck
  split
  · rfl
  · unfold preserveTossCheck
    split
    · rfl
    · unfold congestGuardCheck
      split
      · rfl
      · exact check_frame hψ l r


private theorem throughCheck_frame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    PreWriterFrame (doneThroughCheckEntryWidth hψ hwidth hle κ l r) =
      PreWriterFrame (l, r) := by
  unfold doneThroughCheckEntryWidth doneBeforeCheckEntryWidth
  dsimp only
  rw [preserveDoneCheck_frame hψ, resetSanitize_frame hψ,
    B6PreWriterFramesB.doneMove_frame hψ]
  unfold generationBeforeMoveEntryWidth
  dsimp only
  rw [B6PreWriterFramesB.eliminate_frame hψ,
    B6PreWriterFramesB.clean_frame hψ,
    B6PreWriterFramesA.genEntry_frame hψ hwidth hle κ,
    B6PreWriterFramesA.pprime_frame hψ]


private theorem disappearRaw_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (disappear hψ l r) = rawPreWriterFrame (l, r) := by
  unfold disappear rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


/-- DISAPPEAR frames the pre-writer projection. -/
theorem disappear_frame (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    PreWriterFrame (authorizedDisappear hψ l r) = PreWriterFrame (l, r) := by
  unfold authorizedDisappear
  exact authorizedReconcile_frame _ (disappearRaw_frame hψ) l r


private theorem cmpReturn_right (hψ : 0 < ψ) (l r : AgentState ψ) :
    rightFrame (cmpUpdateReturnPriority hψ l r).2 = rightFrame r := by
  unfold cmpUpdateReturnPriority rightFrame
  repeat (first | rfl | split)


private theorem cmpUpdate_right
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    rightFrame (authorizedCmpUpdate hψ l r).2.core = rightFrame r.core := by
  let allowed := freshComparisonStart hψ l
  let lCore := if allowed && !comparisonActive l.core.state then
    { l.core with state := MainState.congest } else l.core
  let q := cmpUpdateReturnPriority hψ lCore r.core
  change rightFrame q.2 = rightFrame r.core
  exact cmpReturn_right hψ lCore r.core


private theorem compareR_right (hψ : 0 < ψ) (r : AgentState ψ) :
    rightFrame (compareBitUpdateRActionOne hψ r) = rightFrame r := by
  unfold compareBitUpdateRActionOne rightFrame
  dsimp only
  repeat (first | rfl | split)


private theorem compareDispatch_right (hψ : 0 < ψ) (l r : AgentState ψ) :
    rightFrame (compareSigDispatchActionOne hψ l r).2 = rightFrame r := by
  unfold compareSigDispatchActionOne compareBitActionOne
  repeat (first | exact compareR_right hψ r | rfl | split)


private theorem compare_right
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    rightFrame (authorizedCompareSigActionOne hψ l r).2.core =
      rightFrame r.core := by
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState ψ :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  unfold authorizedCompareSigActionOne
  dsimp only
  split
  · rfl
  · split
    · rfl
    · let q := authorizedCmpUpdate hψ l0 r
      exact (compareDispatch_right hψ q.1.core q.2.core).trans
        (cmpUpdate_right hψ l0 r)


/-- Action-one COMPARE preserves the left leader via the existing PeaceView
frame and preserves the complete responder writer projection. -/
theorem compare_frame
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    PreWriterFrame (authorizedCompareSigActionOne hψ l r) =
      PreWriterFrame (l, r) := by
  have hp :=
    PPLLCompleteMultiLeaderCleanup.PhysicalBridge.CheckInert.compareActionOne_peaceViewPair
      hψ l r
  have hl := congrArg
    (fun p : PeaceView ψ × PeaceView ψ => p.1.leader) hp
  change (authorizedCompareSigActionOne hψ l r).1.core.leader =
    l.core.leader at hl
  change rawPreWriterFrame
      ((authorizedCompareSigActionOne hψ l r).1.core,
       (authorizedCompareSigActionOne hψ l r).2.core) =
    rawPreWriterFrame (l.core, r.core)
  exact rawFrame_of_left_right l.core r.core _ _ hl (compare_right hψ l r)


private theorem suppressStartRaw_frame (l r : AgentState ψ) :
    rawPreWriterFrame (suppressSigStart l r) = rawPreWriterFrame (l, r) := by
  unfold suppressSigStart rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem resetKillLeftRaw_frame (l r : AgentState ψ) :
    rawPreWriterFrame (resetKillComparison l, r) =
      rawPreWriterFrame (l, r) := by
  unfold resetKillComparison clearComparisonSignal rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem resetKillRightRaw_frame (l r : AgentState ψ) :
    rawPreWriterFrame (l, resetKillComparison r) =
      rawPreWriterFrame (l, r) := by
  unfold resetKillComparison clearComparisonSignal rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem resetKillPairRaw_frame (l r : AgentState ψ) :
    rawPreWriterFrame (resetKillComparison l, resetKillComparison r) =
      rawPreWriterFrame (l, r) :=
  (resetKillLeftRaw_frame l (resetKillComparison r)).trans
    (resetKillRightRaw_frame l r)


private theorem suppressMoveRaw_frame (l r : AgentState ψ) :
    rawPreWriterFrame (suppressSigMoveReset l r) =
      rawPreWriterFrame (l, r) := by
  unfold suppressSigMoveReset rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem shortCountResetRaw_frame
    (hwidth : 0 < width) (hle : width ≤ ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (shortCountReset hwidth hle l r) =
      rawPreWriterFrame (l, r) := by
  unfold shortCountReset rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem suppressTerminalRaw_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    rawPreWriterFrame (suppressSigTerminal hψ l r) =
      rawPreWriterFrame (l, r) := by
  unfold suppressSigTerminal rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem suppressEchoRaw_frame (l r : AgentState ψ) :
    rawPreWriterFrame (suppressSigEcho l r) =
      rawPreWriterFrame (l, r) := by
  unfold suppressSigEcho rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem suppressFinishRaw_frame (l r : AgentState ψ) :
    rawPreWriterFrame (suppressSigFinish l r) =
      rawPreWriterFrame (l, r) := by
  unfold suppressSigFinish rawPreWriterFrame
  dsimp only
  repeat (first | rfl | split)


private theorem suppressPrefixRaw_frame (l r : AgentState ψ) :
    rawPreWriterFrame (suppressPrefix l r) = rawPreWriterFrame (l, r) := by
  unfold suppressPrefix
  dsimp only
  rw [resetKillPairRaw_frame, suppressMoveRaw_frame,
    resetKillPairRaw_frame, suppressStartRaw_frame]


private theorem suppressRaw_frame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    rawPreWriterFrame (suppressSigResetKillWidth hψ hwidth hle l r) =
      rawPreWriterFrame (l, r) := by
  unfold suppressSigResetKillWidth
  dsimp only
  rw [suppressFinishRaw_frame, suppressEchoRaw_frame,
    suppressTerminalRaw_frame, shortCountResetRaw_frame,
    suppressPrefixRaw_frame]


/-- Width-SUPPRESS frames the pre-writer projection. -/
theorem suppress_frame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) :
    PreWriterFrame (authorizedSuppressWidth hψ hwidth hle l r) =
      PreWriterFrame (l, r) := by
  unfold authorizedSuppressWidth
  exact authorizedReconcile_frame _ (suppressRaw_frame hψ hwidth hle) l r


private theorem normalizePair_frame (l r : AuthorizedAgentState ψ) :
    PreWriterFrame (normalizeDeletion l, normalizeDeletion r) =
      PreWriterFrame (l, r) := by
  unfold PreWriterFrame rawPreWriterFrame normalizeDeletion
  dsimp only
  repeat (first | rfl | split)


/-- Exact ordinary-branch input to the stationary writer inside
`BirthShortDoneTerminalHost.row`, starting from the prepared authorized pair. -/
def rowPreWriterInput
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let c := doneThroughCheckEntryWidth hψ hwidth hle κ l0 r0
  beforeWriteWidth hψ hwidth hle c.1 c.2


/-- All pre-writer stages frame the five coordinates; the proof is only stage
rewrites, with no unfolding of the whole row. -/
theorem rowPreWriterInput_frame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    PreWriterFrame (rowPreWriterInput hψ hwidth hle κ l r) =
      PreWriterFrame (l, r) := by
  unfold rowPreWriterInput
  dsimp only
  unfold beforeWriteWidth
  dsimp only
  rw [suppress_frame hψ hwidth hle, compare_frame hψ, disappear_frame hψ,
    throughCheck_frame hψ hwidth hle κ, normalizePair_frame]


private theorem normalizeDeletion_open
    (u : AuthorizedAgentState ψ) (h : deletionActive u = false) :
    deletionActive (normalizeDeletion u) = false := by
  unfold normalizeDeletion
  split
  · simp [deletionActive]
  · exact h


/-- Stage 3 selects the ordinary metadata branch after deletion normalization. -/
theorem stage3_priority_open
    (l r : AuthorizedAgentState ψ) (h : Stage3PreparedHypotheses l r) :
    deletionActive (normalizeDeletion l) = false ∧
      deletionActive (normalizeDeletion r) = false := by
  change RequestedPreparedHypotheses l r ∧ MissingLeftFollowerConjunct l at h
  exact ⟨normalizeDeletion_open l h.1.2.2.2.2.1,
    normalizeDeletion_open r h.1.2.2.2.2.2.1⟩


/-- At the actual ordinary-branch writer cut, the initiator is a follower and
the responder has the complete idle writer triple required for the next round. -/
theorem stage3_writer_input_idle
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) (h : Stage3PreparedHypotheses l r) :
    let w := rowPreWriterInput hψ hwidth hle κ l r
    w.1.core.leader = false ∧
      w.2.core.path3 = none ∧
      w.2.core.write = .none ∧
      w.2.core.write_state = .none := by
  change RequestedPreparedHypotheses l r ∧ MissingLeftFollowerConjunct l at h
  have hleft : l.core.leader = false := h.2
  have hwriter : PreparedResponderWriterPremise r :=
    h.1.2.2.2.2.2.2.2.2


  dsimp only
  generalize hrow : rowPreWriterInput hψ hwidth hle κ l r = w


  unfold rowPreWriterInput at hrow
  dsimp only at hrow
  generalize hl0 : normalizeDeletion l = l0 at hrow
  generalize hr0 : normalizeDeletion r = r0 at hrow
  generalize ht : doneThroughCheckEntryWidth hψ hwidth hle κ l0 r0 = t at hrow


  unfold beforeWriteWidth at hrow
  dsimp only at hrow
  generalize hd : authorizedDisappear hψ t.1 t.2 = d at hrow
  generalize hx : authorizedCompareSigActionOne hψ d.1 d.2 = x at hrow
  generalize hs : authorizedSuppressWidth hψ hwidth hle x.1 x.2 = s at hrow


  unfold doneThroughCheckEntryWidth at ht
  dsimp only at ht
  generalize hb : doneBeforeCheckEntryWidth hψ hwidth hle κ l0 r0 = b at ht
  generalize hc : preserveDoneCheck hψ b.1 b.2 = c at ht


  unfold doneBeforeCheckEntryWidth at hb
  dsimp only at hb
  generalize hg : generationBeforeMoveEntryWidth hψ hwidth hle κ l0 r0 = g at hb
  generalize hm : authorizedDoneMove hψ g.1 g.2 = m at hb
  generalize hz :
      sanitizeAuthorizedPair hψ (preCheckResetWall m.1 m.2) = z at hb


  unfold generationBeforeMoveEntryWidth at hg
  dsimp only at hg
  generalize hp : authorizedPPsiLeaderResetProbeWall hψ l0 r0 = p at hg
  generalize hge :
      authorizedGenCleanEntryWidth hψ hwidth hle κ p.1 p.2 = ge at hg
  generalize hcl : authorizedCleanSig hψ ge.1 ge.2 = cl at hg
  generalize hel : authorizedEliminateSig hψ cl.1 cl.2 = el at hg


  have hn := normalizePair_frame l r
  rw [hl0, hr0] at hn


  have hpF := B6PreWriterFramesA.pprime_frame hψ l0 r0
  rw [hp] at hpF


  have hgeF := B6PreWriterFramesA.genEntry_frame
    hψ hwidth hle κ p.1 p.2
  rw [hge] at hgeF


  have hclF := B6PreWriterFramesB.clean_frame hψ ge.1 ge.2
  rw [hcl] at hclF


  have helF := B6PreWriterFramesB.eliminate_frame hψ cl.1 cl.2
  rw [hel, hg] at helF


  have hmF := B6PreWriterFramesB.doneMove_frame hψ g.1 g.2
  rw [hm] at hmF


  have hzF := resetSanitize_frame hψ m
  rw [hz, hb] at hzF


  have hcF := preserveDoneCheck_frame hψ b.1 b.2
  rw [hc, ht] at hcF


  have hdF := disappear_frame hψ t.1 t.2
  rw [hd] at hdF


  have hxF := compare_frame hψ d.1 d.2
  rw [hx] at hxF


  have hsF := suppress_frame hψ hwidth hle x.1 x.2
  rw [hs, hrow] at hsF


  have hf : PreWriterFrame w = PreWriterFrame (l, r) := by
    calc
      PreWriterFrame w = PreWriterFrame x := hsF
      _ = PreWriterFrame d := hxF
      _ = PreWriterFrame t := hdF
      _ = PreWriterFrame b := hcF
      _ = PreWriterFrame m := hzF
      _ = PreWriterFrame g := hmF
      _ = PreWriterFrame cl := helF
      _ = PreWriterFrame ge := hclF
      _ = PreWriterFrame p := hgeF
      _ = PreWriterFrame (l0, r0) := hpF
      _ = PreWriterFrame (l, r) := hn


  have hl := congrArg PreWriterFrameView.leftLeader hf
  have hp3 := congrArg PreWriterFrameView.rightPath3 hf
  have hw := congrArg PreWriterFrameView.rightWrite hf
  have hws := congrArg PreWriterFrameView.rightWriteState hf
  change w.1.core.leader = l.core.leader at hl
  change w.2.core.path3 = r.core.path3 at hp3
  change w.2.core.write = r.core.write at hw
  change w.2.core.write_state = r.core.write_state at hws
  exact ⟨hl.trans hleft, hp3.trans hwriter.1,
    hw.trans hwriter.2.1, hws.trans hwriter.2.2⟩


end B6PreWriterFramesC


#print axioms B6PreWriterFramesC.resetSanitize_frame
#print axioms B6PreWriterFramesC.check_frame
#print axioms B6PreWriterFramesC.preserveDoneCheck_frame
#print axioms B6PreWriterFramesC.disappear_frame
#print axioms B6PreWriterFramesC.compare_frame
#print axioms B6PreWriterFramesC.suppress_frame
#print axioms B6PreWriterFramesC.rowPreWriterInput_frame
#print axioms B6PreWriterFramesC.stage3_priority_open
#print axioms B6PreWriterFramesC.stage3_writer_input_idle
