import Leader.Wu.Entrance.PreWriterFramesCheck

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6CheckWriteStateFrame

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
open B6PreWriterFramesA B6PreWriterFramesB B6PreWriterFramesC

variable {ψ κ width : Nat}

private def ws (u : AgentState ψ) : WriteState := u.write_state
private def wsp (q : AgentState ψ × AgentState ψ) : WriteState × WriteState :=
  (ws q.1, ws q.2)
private def awsp
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    WriteState × WriteState := wsp (q.1.core, q.2.core)

/-- A slightly wider projection makes the raw stage rewrites stable; only its
write-state coordinates are exported. -/
private structure WV where
  bit : Bool
  path3 : Option Path3Info
  write : WriteAction
  state : WriteState

private abbrev MV (ψ : Nat) := Fin ψ × WV
private abbrev MP (ψ : Nat) := MV ψ × MV ψ

private def wv (u : AgentState ψ) : WV :=
  ⟨u.bit, u.path3, u.write, u.write_state⟩
private def mv (u : AgentState ψ) : MV ψ := (u.label, wv u)
private def mp (q : AgentState ψ × AgentState ψ) : MP ψ :=
  (mv q.1, mv q.2)
private def am (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) : MP ψ :=
  mp (q.1.core, q.2.core)

private def statesOfMP (q : MP ψ) : WriteState × WriteState :=
  (q.1.2.state, q.2.2.state)

private theorem wsp_of_mp {a b : AgentState ψ × AgentState ψ}
    (h : mp a = mp b) : wsp a = wsp b := by
  exact congrArg statesOfMP h

private theorem awsp_of_am
    {a b : AuthorizedAgentState ψ × AuthorizedAgentState ψ}
    (h : am a = am b) : awsp a = awsp b := by
  exact congrArg statesOfMP h

private theorem lift_m
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ l r, mp (f l r) = mp (l, r))
    (l r : AuthorizedAgentState ψ) :
    am (authorizedReconcile f l r) = am (l, r) :=
  hf l.core r.core

/-! ### generationBeforeMoveEntryWidth -/

private theorem pprime_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    wsp (pPsiLeaderResetProbeWall hψ l r) = wsp (l, r) := by
  unfold pPsiLeaderResetProbeWall pPsi wsp ws
  try dsimp only
  repeat (first | rfl | split)

private theorem wait_prepare_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (waitSaturatedPrepare hψ l r) = mp (l, r) := by
  unfold waitSaturatedPrepare mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem wait_clear_m (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    mp (terminalInactiveClear hw hle l r) = mp (l, r) := by
  unfold terminalInactiveClear mp mv wv
  repeat (first | rfl | split)

private theorem wait_carry_m (hw : 0 < width) (hle : width ≤ ψ)
    (cap : Nat) (l r : AgentState ψ) :
    mp (waitWidthCarry hw hle cap l r) = mp (l, r) := by
  unfold waitWidthCarry mp mv wv
  repeat (first | rfl | split)

private theorem wait_reset_m (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AgentState ψ) :
    mp (waitWidthReset hw hle l r) = mp (l, r) := by
  unfold waitWidthReset mp mv wv
  repeat (first | rfl | split)

private theorem wait_finish_m
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (cap : Nat) (l r : AgentState ψ) :
    mp (waitWidthFinish hψ hw hle cap l r) = mp (l, r) := by
  unfold waitWidthFinish mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem wait_entry_m
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (cap : Nat) (l r : AgentState ψ) :
    mp (waitWidthEntry hψ hw hle cap l r) = mp (l, r) := by
  unfold waitWidthEntry
  try dsimp only
  rw [wait_finish_m, wait_reset_m, wait_carry_m,
    wait_clear_m, wait_prepare_m]

private theorem gen_start_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (genSigSaturatedStart hψ l r) = mp (l, r) := by
  unfold genSigSaturatedStart mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem gen_emit_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (genCleanEmit hψ l r) = mp (l, r) := by
  unfold genCleanEmit mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem gen_propagate_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (genCleanPropagate hψ l r) = mp (l, r) := by
  unfold genCleanPropagate mp mv wv
  repeat (first | rfl | split)

private theorem gen_finish_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (genSigSaturatedFinish hψ l r) = mp (l, r) := by
  unfold genSigSaturatedFinish mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem gen_after_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (genCleanAfterWait hψ l r) = mp (l, r) := by
  unfold genCleanAfterWait
  try dsimp only
  rw [gen_finish_m, gen_propagate_m, gen_emit_m, gen_start_m]

private theorem gen_entry_m
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (cap : Nat) (l r : AgentState ψ) :
    mp (genCleanEntryWidth hψ hw hle cap l r) = mp (l, r) := by
  unfold genCleanEntryWidth
  try dsimp only
  rw [gen_after_m, wait_entry_m]

private theorem gen_entry_am
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (cap : Nat) (l r : AuthorizedAgentState ψ) :
    am (authorizedGenCleanEntryWidth hψ hw hle cap l r) = am (l, r) :=
  lift_m _ (gen_entry_m hψ hw hle cap) l r

private theorem clean_connect_m (l r : AgentState ψ) :
    mp (cleanSigGenConnect l, cleanSigGenConnect r) = mp (l, r) := by
  unfold cleanSigGenConnect mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem clean3_m (l r : AgentState ψ) :
    mp (cleanSigStep3 l r) = mp (l, r) := by
  unfold cleanSigStep3 mp mv wv
  repeat (first | rfl | split)

private theorem clean4_m (l r : AgentState ψ) :
    mp (cleanSigStep4 l r) = mp (l, r) := by
  unfold cleanSigStep4 mp mv wv
  repeat (first | rfl | split)

private theorem clean5_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (cleanSigStep5 hψ l r) = mp (l, r) := by
  unfold cleanSigStep5 mp mv wv
  repeat (first | rfl | split)

private theorem clean6_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (cleanSigStep6 hψ l r) = mp (l, r) := by
  unfold cleanSigStep6 mp mv wv
  repeat (first | rfl | split)

private theorem clean_apply_m (u : AgentState ψ) :
    mv (cleanSigCleanApply u) = mv u := by
  unfold cleanSigCleanApply mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem clean_apply_pair_m (l r : AgentState ψ) :
    mp (cleanSigCleanApply l, cleanSigCleanApply r) = mp (l, r) :=
  Prod.ext (clean_apply_m l) (clean_apply_m r)

private theorem clean_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (cleanSig hψ l r) = mp (l, r) := by
  unfold cleanSig
  try dsimp only
  rw [clean_apply_pair_m, clean6_m, clean5_m, clean4_m,
    clean3_m, clean_connect_m]

private theorem clean_am (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) :
    am (authorizedCleanSig hψ l r) = am (l, r) :=
  lift_m _ (clean_m hψ) l r

private theorem eliminate_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (eliminateSig hψ l r) = mp (l, r) := by
  unfold eliminateSig mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem eliminate_am (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) :
    am (authorizedEliminateSig hψ l r) = am (l, r) :=
  lift_m _ (eliminate_m hψ) l r

private theorem generationBeforeMoveEntryWidth_ws
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) (cap : Nat)
    (l r : AuthorizedAgentState ψ) :
    awsp (generationBeforeMoveEntryWidth hψ hw hle cap l r) = awsp (l, r) := by
  let p := authorizedPPsiLeaderResetProbeWall hψ l r
  let g := authorizedGenCleanEntryWidth hψ hw hle cap p.1 p.2
  let c := authorizedCleanSig hψ g.1 g.2
  unfold generationBeforeMoveEntryWidth
  exact (awsp_of_am (eliminate_am hψ c.1 c.2)).trans
    ((awsp_of_am (clean_am hψ g.1 g.2)).trans
      ((awsp_of_am (gen_entry_am hψ hw hle cap p.1 p.2)).trans
        ((congrArg wsp
          (authorizedPPsiLeaderResetProbeWall_core hψ l r)).trans
          (pprime_m hψ l.core r.core))))

/-! ### authorizedDoneMove -/

private theorem preclear_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (sigMoveLeaderPreclear hψ l r) = mp (l, r) := by
  unfold sigMoveLeaderPreclear clearIfLeader clearComparisonSignal mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem capture_m (l r : AgentState ψ) :
    mp (captureStep1 l r) = mp (l, r) := by
  unfold captureStep1 mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem hold_done_m (l r : AgentState ψ) :
    mp (holdDoneStep1 l r) = mp (l, r) := by
  unfold holdDoneStep1
  split
  · rfl
  · exact capture_m l r

private theorem sig2_m (l r : AgentState ψ) :
    mp (sigMoveStep2 l r) = mp (l, r) := by
  unfold sigMoveStep2 mp mv wv
  repeat (first | rfl | split)

private theorem sig3_m (l r : AgentState ψ) :
    mp (sigMoveStep3 l r) = mp (l, r) := by
  unfold sigMoveStep3 mp mv wv
  repeat (first | rfl | split)

private theorem sig4_m (l r : AgentState ψ) :
    mp (sigMoveStep4 l r) = mp (l, r) := by
  unfold sigMoveStep4 mp mv wv
  repeat (first | rfl | split)

private theorem sig5_m (l r : AgentState ψ) :
    mp (sigMoveStep5 l r) = mp (l, r) := by
  unfold sigMoveStep5 mp mv wv
  repeat (first | rfl | split)

private theorem controls_m (l r : AgentState ψ) :
    mp (controlTransfers l r) = mp (l, r) := by
  unfold controlTransfers
  try dsimp only
  rw [sig5_m, sig4_m, sig3_m, sig2_m]

private theorem done_transfers_m (l r : AgentState ψ) :
    mp (doneTransfers l r) = mp (l, r) := by
  unfold doneTransfers
  try dsimp only
  rw [controls_m, hold_done_m]

private theorem leader_wall_m (l r : AgentState ψ) :
    mp (comparisonLeaderWall l r) = mp (l, r) := by
  unfold comparisonLeaderWall clearComparisonSignal mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem control_apply_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (singleUseApplyControl hψ l, singleUseApplyControl hψ r) = mp (l, r) := by
  unfold singleUseApplyControl mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem control_tail_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (singleUseControlTail hψ l r) = mp (l, r) := by
  unfold singleUseControlTail
  try dsimp only
  split
  · split
    · simpa only [mp, mv, wv] using control_apply_m hψ l r
    · exact control_apply_m hψ l r
  · exact control_apply_m hψ l r

private theorem done_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (doneCaptureSigMove hψ l r) = mp (l, r) := by
  unfold doneCaptureSigMove
  try dsimp only
  rw [control_tail_m, leader_wall_m, done_transfers_m, preclear_m]

private theorem authorizedDoneMove_ws
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    awsp (authorizedDoneMove hψ l r) = awsp (l, r) := by
  have hm : am (authorizedDoneMove hψ l r) = am (l, r) :=
    (congrArg mp (authorizedDoneMove_core hψ l r)).trans
      (done_m hψ l.core r.core)
  exact awsp_of_am hm

/-! ### preCheckResetWall / sanitizeAuthorizedPair -/

private theorem reset_sanitize_m (hψ : 0 < ψ)
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    am (sanitizeAuthorizedPair hψ (preCheckResetWall q.1 q.2)) = am q := by
  unfold sanitizeAuthorizedPair sanitizeAuthorizedTerminalEqual
    preCheckResetWall clearAuthorizedComparison clearComparisonSignal am mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem resetSanitize_ws (hψ : 0 < ψ)
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    awsp (sanitizeAuthorizedPair hψ (preCheckResetWall q.1 q.2)) = awsp q :=
  awsp_of_am (reset_sanitize_m hψ q)

/-! ### authorizedCheckSig / congestGuardCheck / preserveDoneCheck -/

private theorem check_ready_m (l r : AgentState ψ) :
    mp (checkSigSetReady l, checkSigSetReady r) = mp (l, r) := by
  unfold checkSigSetReady mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem check_left_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (checkSigCheckL hψ l, r) = mp (l, r) := by
  unfold checkSigCheckL mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem check_right_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (l, checkSigCheckR hψ l r) = mp (l, r) := by
  unfold checkSigCheckR mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem check_result_m (l r : AgentState ψ) :
    mp (checkSigSetResult l, checkSigSetResult r) = mp (l, r) := by
  unfold checkSigSetResult mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem check_leader_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (l, checkSigSetLeader hψ r) = mp (l, r) := by
  unfold checkSigSetLeader mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem check_m (hψ : 0 < ψ) (l r : AgentState ψ) :
    mp (checkSig hψ l r) = mp (l, r) := by
  rw [checkSig_eq_staged]
  unfold checkSigStaged
  try dsimp only
  rw [check_leader_m, check_result_m, check_right_m,
    check_left_m, check_ready_m]

private theorem authorizedCheckSig_ws
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    awsp (authorizedCheckSig hψ l r) = awsp (l, r) := by
  unfold authorizedCheckSig
  exact awsp_of_am (lift_m _ (check_m hψ) l r)

private theorem congestGuardCheck_ws
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    awsp (congestGuardCheck hψ l r) = awsp (l, r) := by
  unfold congestGuardCheck
  split
  · rfl
  · exact authorizedCheckSig_ws hψ l r

private theorem preserveDoneCheck_ws
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    awsp (preserveDoneCheck hψ l r) = awsp (l, r) := by
  unfold preserveDoneCheck
  split
  · rfl
  · unfold preserveTossCheck
    split
    · rfl
    · exact congestGuardCheck_ws hψ l r

/-- Public two-sided writer-state frame through the actual through-CHECK cut. -/
theorem doneThroughCheckEntryWidth_writeState_frame
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) (cap : Nat)
    (l r : AuthorizedAgentState ψ) :
    (doneThroughCheckEntryWidth hψ hw hle cap l r).1.core.write_state =
        l.core.write_state ∧
      (doneThroughCheckEntryWidth hψ hw hle cap l r).2.core.write_state =
        r.core.write_state := by
  let g := generationBeforeMoveEntryWidth hψ hw hle cap l r
  let m := authorizedDoneMove hψ g.1 g.2
  let s := sanitizeAuthorizedPair hψ (preCheckResetWall m.1 m.2)
  let z := preserveDoneCheck hψ s.1 s.2
  have hg : awsp g = awsp (l, r) :=
    generationBeforeMoveEntryWidth_ws hψ hw hle cap l r
  have hm : awsp m = awsp g := authorizedDoneMove_ws hψ g.1 g.2
  have hs : awsp s = awsp m := resetSanitize_ws hψ m
  have hz : awsp z = awsp s := preserveDoneCheck_ws hψ s.1 s.2
  have hstage : doneThroughCheckEntryWidth hψ hw hle cap l r = z := by
    rfl
  have hpair :
      awsp (doneThroughCheckEntryWidth hψ hw hle cap l r) = awsp (l, r) := by
    rw [hstage]
    exact hz.trans (hs.trans (hm.trans hg))
  constructor
  · have h := congrArg (fun p : WriteState × WriteState => p.1) hpair
    simpa [awsp, wsp, ws] using h
  · have h := congrArg (fun p : WriteState × WriteState => p.2) hpair
    simpa [awsp, wsp, ws] using h

end B6CheckWriteStateFrame
