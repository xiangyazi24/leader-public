import Leader.Wu.ZeroDivisible.HeadAnchor

/-!
Unconditional responder facts for the frozen round-two Head pipeline. A claim
here concerns the complete pair transition, with arbitrary raw ancillary state;
it does not establish convergence or closure of a global normalized sector.
-/
namespace PPLLAstraResponder
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard PPLLFableDesignR1 PPLLAstraDesign2

private def Frame {ψ : Nat} (a b : AgentState ψ) : Prop :=
  a.probe = b.probe ∧ a.echo = b.echo ∧ a.bullet = b.bullet

private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem probe_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).probe = if p then a.probe else b.probe := by split <;> rfl
private theorem echo_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).echo = if p then a.echo else b.echo := by split <;> rfl
private theorem bullet_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).bullet = if p then a.bullet else b.bullet := by split <;> rfl

private theorem writeActionApplyOverwrite_frame {ψ : Nat} (u : AgentState ψ) :
    Frame (writeActionApplyOverwrite u) u := by
  unfold Frame writeActionApplyOverwrite
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeActionApplyMoveFlip_frame {ψ : Nat} (u : AgentState ψ) :
    Frame (writeActionApplyMoveFlip u) u := by
  unfold Frame writeActionApplyMoveFlip
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem moveWsigCheckLast_frame {ψ : Nat} (u : AgentState ψ) :
    Frame (moveWsigCheckLast u) u := by
  unfold Frame moveWsigCheckLast
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeSeqSetWriteReady_frame {ψ : Nat} (u : AgentState ψ) :
    Frame (writeSeqSetWriteReady u) u := by
  unfold Frame writeSeqSetWriteReady
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeSeqCheckBit_frame {ψ : Nat} (u : AgentState ψ) :
    Frame (writeSeqCheckBit u) u := by
  unfold Frame writeSeqCheckBit
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeSeqSetWriteAct_frame {ψ : Nat} (u : AgentState ψ) :
    Frame (writeSeqSetWriteAct u) u := by
  cases hp : u.path3 <;> simp only [Frame, writeSeqSetWriteAct, hp] <;>
    simp [probe_ite, echo_ite, bullet_ite, hp]

private theorem writeSeqFinalR_frame {ψ : Nat} (u : AgentState ψ) :
    Frame (writeSeqFinalR u) u := by
  unfold Frame writeSeqFinalR
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem moveWsigCheckGenWs_frame {ψ : Nat} (l r : AgentState ψ) :
    Frame (moveWsigCheckGenWs l r) r := by
  unfold Frame moveWsigCheckGenWs
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem moveWsigTransfer_frame {ψ : Nat} (l r : AgentState ψ) :
    Frame (moveWsigTransfer l r).1 l ∧ Frame (moveWsigTransfer l r).2 r := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp only [Frame, moveWsigTransfer, hl, hr] <;>
    simp only [fst_ite, snd_ite, probe_ite, echo_ite, bullet_ite, ite_self, and_self]

private theorem groupInfo_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (groupInfo hψ l r).1 l ∧ Frame (groupInfo hψ l r).2 r := by
  simp only [Frame, groupInfo]
  simp only [fst_ite, snd_ite, probe_ite, echo_ite, bullet_ite, ite_self, and_self]

private theorem gensigWriteseq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (gensigWriteseq hψ l r).1 l ∧ Frame (gensigWriteseq hψ l r).2 r := by
  simp only [Frame, gensigWriteseq]
  simp only [fst_ite, snd_ite, probe_ite, echo_ite, bullet_ite, ite_self, and_self]

private theorem writeAction_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (writeAction hψ l r).1 l ∧ Frame (writeAction hψ l r).2 r := by
  simp only [Frame, writeAction]
  simp only [fst_ite, snd_ite, probe_ite, echo_ite, bullet_ite, ite_self, and_self , (writeActionApplyOverwrite_frame _).1, (writeActionApplyOverwrite_frame _).2.1, (writeActionApplyOverwrite_frame _).2.2, (writeActionApplyMoveFlip_frame _).1, (writeActionApplyMoveFlip_frame _).2.1, (writeActionApplyMoveFlip_frame _).2.2]

private theorem moveWsig_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (moveWsig hψ l r).1 l ∧ Frame (moveWsig hψ l r).2 r := by
  simp only [Frame, moveWsig]
  simp only [fst_ite, snd_ite, probe_ite, echo_ite, bullet_ite, ite_self, and_self , (moveWsigCheckGenWs_frame _ _).1, (moveWsigCheckGenWs_frame _ _).2.1, (moveWsigCheckGenWs_frame _ _).2.2, (moveWsigCheckLast_frame _).1, (moveWsigCheckLast_frame _).2.1, (moveWsigCheckLast_frame _).2.2, (moveWsigTransfer_frame _ _).1.1, (moveWsigTransfer_frame _ _).1.2.1, (moveWsigTransfer_frame _ _).1.2.2, (moveWsigTransfer_frame _ _).2.1, (moveWsigTransfer_frame _ _).2.2.1, (moveWsigTransfer_frame _ _).2.2.2]

private theorem writeSeq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (writeSeq hψ l r).1 l ∧ Frame (writeSeq hψ l r).2 r := by
  simp only [Frame, writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands]
  simp only [fst_ite, snd_ite, probe_ite, echo_ite, bullet_ite, ite_self, and_self, (groupInfo_frame _ _ _).1.1, (groupInfo_frame _ _ _).1.2.1, (groupInfo_frame _ _ _).1.2.2, (groupInfo_frame _ _ _).2.1, (groupInfo_frame _ _ _).2.2.1, (groupInfo_frame _ _ _).2.2.2, (gensigWriteseq_frame _ _ _).1.1, (gensigWriteseq_frame _ _ _).1.2.1, (gensigWriteseq_frame _ _ _).1.2.2, (gensigWriteseq_frame _ _ _).2.1, (gensigWriteseq_frame _ _ _).2.2.1, (gensigWriteseq_frame _ _ _).2.2.2, (writeAction_frame _ _ _).1.1, (writeAction_frame _ _ _).1.2.1, (writeAction_frame _ _ _).1.2.2, (writeAction_frame _ _ _).2.1, (writeAction_frame _ _ _).2.2.1, (writeAction_frame _ _ _).2.2.2, (moveWsig_frame _ _ _).1.1, (moveWsig_frame _ _ _).1.2.1, (moveWsig_frame _ _ _).1.2.2, (moveWsig_frame _ _ _).2.1, (moveWsig_frame _ _ _).2.2.1, (moveWsig_frame _ _ _).2.2.2, (writeSeqSetWriteReady_frame _).1, (writeSeqSetWriteReady_frame _).2.1, (writeSeqSetWriteReady_frame _).2.2, (writeSeqCheckBit_frame _).1, (writeSeqCheckBit_frame _).2.1, (writeSeqCheckBit_frame _).2.2, (writeSeqSetWriteAct_frame _).1, (writeSeqSetWriteAct_frame _).2.1, (writeSeqSetWriteAct_frame _).2.2, (writeSeqFinalR_frame _).1, (writeSeqFinalR_frame _).2.1, (writeSeqFinalR_frame _).2.2]

private theorem write_responder_label {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : (writeWithBundle hψ l r).2.label = r.label := by
  unfold writeWithBundle
  by_cases h : r.leader = true ∧ r.label.val ≠ 0 ∧ l.leader = false
  · simp only [if_pos h]
    exact PPLLVerify.writeSeq_r_label hψ l r
  · simp only [if_neg h]
    exact PPLLVerify.writeSeq_r_label hψ l r

private theorem write_responder_leader {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (writeWithBundle hψ l r).2.leader = (writeSeq hψ l r).2.leader := by
  unfold writeWithBundle
  by_cases h : r.leader = true ∧ r.label.val ≠ 0 ∧ l.leader = false
  · simp only [if_pos h]
  · simp only [if_neg h]

/-- WRITE migrates any nonzero-label responder leader, independently of its
origin in the earlier birth stages. The bundle transfer does not change this
leader/label property. -/
theorem writeWithBundle_responder_leader_label_zero {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (h : (writeWithBundle hψ l r).2.leader = true) :
    (writeWithBundle hψ l r).2.label = ⟨0, hψ⟩ := by
  rw [write_responder_label]
  rw [write_responder_leader] at h
  have hr := PPLLVerify.writeSeq_responder_leader_was_leader hψ l r h
  by_cases hz : r.label = ⟨0, hψ⟩
  · exact hz
  · have hf := PPLLVerify.writeSeq_responder_false_of_nonzero_leader hψ l r ⟨hr, hz⟩
    rw [hf] at h
    cases h

private theorem conserve_responder_label_zero {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (q : AgentState ψ × AgentState ψ)
    (hq : q.2.leader = true → q.2.label = ⟨0, hψ⟩) :
    (conserve .head l r q).2.leader = true →
      (conserve .head l r q).2.label = ⟨0, hψ⟩ := by
  unfold conserve
  split
  · simp
  · exact hq

/-- After every complete Head interaction, any responder leader has label0.
The assertion is unconditional in the two input agents: WRITE handles all
ordinary births and surviving leaders, and emergency Head replacement sets0. -/
theorem pipeline_responder_leader_label_zero {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ)
    (h : (PPLLAstraDesign2.pipeline hψ κ .head l r).2.leader = true) :
    (PPLLAstraDesign2.pipeline hψ κ .head l r).2.label = ⟨0, hψ⟩ := by
  apply conserve_responder_label_zero hψ l r _ _ h
  exact writeWithBundle_responder_leader_label_zero hψ _ _


private theorem echo_stage_false {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigEcho l r).2.echo = false := by
  cases h : r.echo <;> simp [suppressSigEcho, h]

private theorem suppression_echo_false {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (suppressSigResetKill hψ l r).2.echo = false := by
  simp only [suppressSigResetKill, suppressSigFinish, echo_stage_false]

private theorem kernel_probe_echo {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (k4Kernel hψ l r).2.probe = r.probe ∧
    (k4Kernel hψ l r).2.echo = r.echo := by
  simp only [k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire,
    absorbAnyMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp only [fst_ite, snd_ite, probe_ite, echo_ite, ite_self, and_self]

private theorem write_probe_echo {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeWithBundle hψ l r).2.probe = r.probe ∧
    (writeWithBundle hψ l r).2.echo = r.echo := by
  simp only [writeWithBundle, fst_ite, snd_ite, probe_ite, echo_ite,
    (writeSeq_frame _ _ _).2.1, (writeSeq_frame _ _ _).2.2.1, ite_self, and_self]

private theorem conserve_probe_echo {ψ : Nat} (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) :
    (conserve .head l r q).2.probe = q.2.probe ∧
    (conserve .head l r q).2.echo = q.2.echo := by
  simp only [conserve, replacement, clearCmp]
  simp [fst_ite, snd_ite, probe_ite, echo_ite]

/-- Every complete Head step consumes responder echo. The final suppression
stage moves or cancels it, and K4, WRITE and emergency replacement frame echo. -/
theorem pipeline_responder_echo_false {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (PPLLAstraDesign2.pipeline hψ κ .head l r).2.echo = false := by
  simp only [PPLLAstraDesign2.pipeline, (conserve_probe_echo _ _ _).2,
    (write_probe_echo _ _ _).2, (kernel_probe_echo _ _ _).2,
    beforeElimination, suppression_echo_false]


private theorem kernel_no_live_responder {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : (k4Kernel hψ l r).2.bullet ≠ (2 : Fin 3) := by
  have hb : r.bullet = (0 : Fin 3) ∨ r.bullet = 1 ∨ r.bullet = 2 := by omega
  cases hl : l.leader <;> cases hs : l.shield <;> cases hr : r.leader <;>
    by_cases hsl : l.signal_B = (1 : Fin 2) <;>
    by_cases hsr : r.signal_B = (1 : Fin 2) <;>
    rcases hb with hb | hb | hb <;>
    simp only [k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire,
      absorbAnyMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink] <;>
    simp [hl, hs, hr, hsl, hsr, hb]

private theorem write_no_live_responder {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (h : r.bullet ≠ (2 : Fin 3)) :
    (writeWithBundle hψ l r).2.bullet ≠ (2 : Fin 3) := by
  simp only [writeWithBundle, fst_ite, snd_ite, bullet_ite,
    (writeSeq_frame _ _ _).2.2.2]
  split
  · decide
  · exact h

private theorem conserve_no_live_responder {ψ : Nat} (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) (h : q.2.bullet ≠ (2 : Fin 3)) :
    (conserve .head l r q).2.bullet ≠ (2 : Fin 3) := by
  simp only [conserve, replacement, clearCmp]
  simp only [fst_ite, snd_ite, bullet_ite]
  split
  · simp
  · exact h

/-- Every complete Head interaction leaves no live bullet at its responder.
K4 either consumes a live bullet or changes it to dummy before FIRE; WRITE can
only preserve this fact or clear the migrated bundle, and Head replaces with0. -/
theorem pipeline_responder_bullet_not_live {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (PPLLAstraDesign2.pipeline hψ κ .head l r).2.bullet ≠ (2 : Fin 3) := by
  apply conserve_no_live_responder
  apply write_no_live_responder
  exact kernel_no_live_responder hψ _ _

private theorem gen_probes {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (genSigSaturated hψ κ l r).1.probe = l.probe ∧
    (genSigSaturated hψ κ l r).2.probe = r.probe := by
  simp only [genSigSaturated, genSigSaturatedAfterWait, genSigSaturatedStart,
    genSigSaturatedEmit, genSigSaturatedPropagate, genSigSaturatedFinish,
    waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish] <;> simp only [fst_ite, snd_ite, probe_ite, ite_self, and_self]

private theorem cleanSigGenConnect_probe {ψ : Nat} (u : AgentState ψ) :
    (cleanSigGenConnect u).probe = u.probe := by
  cases h : u.path <;>
    simp only [cleanSigGenConnect, h] <;>
    simp [fst_ite, snd_ite, probe_ite]

private theorem cleanSigCleanApply_probe {ψ : Nat} (u : AgentState ψ) :
    (cleanSigCleanApply u).probe = u.probe := by
  cases h : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp only [cleanSigCleanApply, h, h4, h5] <;>
    (repeat split) <;> simp_all [probe_ite]

private theorem clean3_probes {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep3 l r).1.probe = l.probe ∧
    (cleanSigStep3 l r).2.probe = r.probe := by
  cases h : r.path4 <;> cases hp : l.path <;> simp only [cleanSigStep3, h, hp] <;>
    simp [fst_ite, snd_ite, probe_ite]

private theorem clean4_probes {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep4 l r).1.probe = l.probe ∧
    (cleanSigStep4 l r).2.probe = r.probe := by
  cases h : l.path5 <;> cases hp : r.path <;> simp only [cleanSigStep4, h, hp] <;>
    simp [fst_ite, snd_ite, probe_ite]

private theorem clean5_probes {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).1.probe = l.probe ∧
    (cleanSigStep5 hψ l r).2.probe = r.probe := by
  cases h : r.path4 <;> simp only [cleanSigStep5, h] <;>
    simp [fst_ite, snd_ite, probe_ite]

private theorem clean6_probes {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).1.probe = l.probe ∧
    (cleanSigStep6 hψ l r).2.probe = r.probe := by
  cases h : l.path5 <;> simp only [cleanSigStep6, h] <;>
    simp [fst_ite, snd_ite, probe_ite]

private theorem clean_probes {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (cleanSig hψ l r).1.probe = l.probe ∧
    (cleanSig hψ l r).2.probe = r.probe := by
  simp only [cleanSig]
  simp only [cleanSigGenConnect_probe, cleanSigCleanApply_probe,
    (clean3_probes _ _).1, (clean3_probes _ _).2,
    (clean4_probes _ _).1, (clean4_probes _ _).2,
    (clean5_probes _ _ _).1, (clean5_probes _ _ _).2,
    (clean6_probes _ _ _).1, (clean6_probes _ _ _).2, and_self]

private theorem eliminate_probes {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.probe = l.probe ∧
    (eliminateSig hψ l r).2.probe = r.probe := by
  simp only [eliminateSig] <;> simp [fst_ite, snd_ite, probe_ite]

private theorem step1_probes {ψ : Nat} (l r : AgentState ψ) :
    (sigMoveStep1With .dropMisaligned l r).1.probe = l.probe ∧
    (sigMoveStep1With .dropMisaligned l r).2.probe = r.probe := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [sigMoveStep1With, hl, hr] <;> simp [fst_ite, snd_ite, probe_ite]

private theorem moveTokens_probes {ψ : Nat} (l r : AgentState ψ) :
    (moveTokens l r).1.probe = l.probe ∧
    (moveTokens l r).2.probe = r.probe := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [moveTokens, hl, hr] <;> simp [fst_ite, snd_ite, probe_ite]

private theorem control_probe {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (sigMoveApplyControlConsume hψ u).probe = u.probe := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;> simp [fst_ite, snd_ite, probe_ite]

private theorem sig_probes {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (sigMoveF hψ true .dropMisaligned l r).1.probe = l.probe ∧
    (sigMoveF hψ true .dropMisaligned l r).2.probe = r.probe := by
  simp only [sigMoveF]
  simp only [fst_ite, snd_ite, probe_ite, control_probe]
  simp only [leaderWall, clearCmp, fst_ite, snd_ite, probe_ite,
    ite_self, (moveTokens_probes _ _).1, (moveTokens_probes _ _).2,
    (step1_probes _ _).1, (step1_probes _ _).2, and_self]


private theorem drop_probe {ψ : Nat} (u : AgentState ψ) :
    (dropStale u).probe = u.probe := by
  simp only [dropStale]
  simp [probe_ite]

private theorem reset_probes {ψ : Nat} (l r : AgentState ψ) :
    (preCheckReset l r).1.probe = l.probe ∧
    (preCheckReset l r).2.probe = r.probe := by
  simp only [preCheckReset, clearCmp]
  simp [probe_ite]

private theorem ready_probe {ψ : Nat} (u : AgentState ψ) :
    (readyF u).probe = u.probe := by
  cases hp : u.path <;>
    simp only [readyF, checkSigSetReadyGuarded, checkSigSetReady, hp] <;>
    simp [probe_ite]

private theorem checkL_probe {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (checkSigCheckL hψ u).probe = u.probe := by
  unfold checkSigCheckL
  split <;> simp [probe_ite]

private theorem result_probe {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetResult u).probe = u.probe := by
  simp only [checkSigSetResult]
  simp [probe_ite]

private theorem check_left {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (checkSigF hψ κ false l r).1.probe = l.probe := by
  simp only [checkSigF, fst_ite, probe_ite, result_probe,
    checkL_probe, ready_probe, clearCmp]
  simp [probe_ite]

private theorem disappear_probes {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (disappear hψ l r).1.probe = l.probe ∧
    (disappear hψ l r).2.probe = r.probe := by
  simp only [disappear]
  simp [fst_ite, snd_ite, probe_ite]


private theorem kill_probe {ψ : Nat} (u : AgentState ψ) :
    (if u.reset_cmd then clearCmp u else u).probe = u.probe := by
  by_cases h : u.reset_cmd = true <;> simp [h, clearCmp]

private theorem suppressSigStart_probes {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigStart l r).1.probe = l.probe ∧
    (suppressSigStart l r).2.probe = r.probe := by
  simp only [suppressSigStart]
  simp [fst_ite, snd_ite, probe_ite]

private theorem suppressSigMoveReset_probes {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigMoveReset l r).1.probe = l.probe ∧
    (suppressSigMoveReset l r).2.probe = r.probe := by
  simp only [suppressSigMoveReset]
  simp [fst_ite, snd_ite, probe_ite]

private theorem suppressSigTerminal_probes {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (suppressSigTerminal hψ l r).1.probe = l.probe ∧
    (suppressSigTerminal hψ l r).2.probe = r.probe := by
  simp only [suppressSigTerminal]
  simp [fst_ite, snd_ite, probe_ite]

private theorem suppressSigEcho_probes {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigEcho l r).1.probe = l.probe ∧
    (suppressSigEcho l r).2.probe = r.probe := by
  simp only [suppressSigEcho]
  simp [fst_ite, snd_ite, probe_ite]

private theorem suppressSigFinish_probes {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigFinish l r).1.probe = l.probe ∧
    (suppressSigFinish l r).2.probe = r.probe := by
  simp only [suppressSigFinish]
  simp [fst_ite, snd_ite, probe_ite]

private theorem suppress_probes {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (suppressSigResetKill hψ l r).1.probe = l.probe ∧
    (suppressSigResetKill hψ l r).2.probe = r.probe := by
  simp only [suppressSigResetKill,
    (suppressSigFinish_probes _ _).1, (suppressSigFinish_probes _ _).2,
    (suppressSigEcho_probes _ _).1, (suppressSigEcho_probes _ _).2,
    (suppressSigTerminal_probes _ _ _).1, (suppressSigTerminal_probes _ _ _).2,
    (suppressSigMoveReset_probes _ _).1, (suppressSigMoveReset_probes _ _).2,
    (suppressSigStart_probes _ _).1, (suppressSigStart_probes _ _).2,
    kill_probe, and_self]


private theorem checkR_probe {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).probe = r.probe := by
  unfold checkSigCheckR
  repeat (first | rfl | split)

private theorem check_right_probe {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : (checkSigF hψ κ false l r).2.probe = r.probe := by
  simp only [checkSigF, snd_ite, probe_ite, result_probe,
    checkR_probe, ready_probe, clearCmp]
  simp [probe_ite]

private theorem maintain_right_probe {ψ : Nat} (l r : AgentState ψ) :
    (maintain l r).2.probe = r.probe := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [maintain, hl, hr] <;> simp [probe_ite]

private theorem wave_right_probe {ψ : Nat} (l r : AgentState ψ) :
    (wave l r).2.probe = r.probe := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [wave, hl, hr] <;> simp [probe_ite]

private theorem stray_right_probe {ψ : Nat} (l r : AgentState ψ) :
    (dropStray l r).2.probe = r.probe := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [dropStray, hl, hr] <;> simp [probe_ite]

private theorem forward_probe {ψ : Nat} (κ : Nat) (u : AgentState ψ) :
    (landForward κ false true u).probe = u.probe := by
  cases ht : u.path2 <;> cases hp : u.path <;>
    simp only [landForward, ht, hp] <;> simp [probe_ite]

private theorem compare_right_probe {ψ : Nat} (κ : Nat) (l r : AgentState ψ) :
    (compareSigF κ false true l r).2.probe = r.probe := by
  simp only [compareSigF, forward_probe, stray_right_probe,
    wave_right_probe, maintain_right_probe]

private theorem pPsi_right_probe_false {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (pPsi hψ l r).2.probe = false := by
  by_cases hb : r.label ≠ (⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ : Fin ψ) <;>
    by_cases hp : r.probe = true <;> simp [pPsi, hb, hp]

private theorem prefix_probe_false {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : (beforeElimination hψ κ l r).2.probe = false := by
  simp only [beforeElimination, (suppress_probes _ _ _).2,
    compare_right_probe, (disappear_probes _ _ _).2, check_right_probe,
    (reset_probes _ _).2, drop_probe, (sig_probes _ _ _).2,
    (eliminate_probes _ _ _).2, (clean_probes _ _ _).2,
    (gen_probes _ _ _ _).2, pPsiProbeWall, pPsi_right_probe_false]

/-- Every complete Head step clears the selected responder's probe. Ordinary
P'_ψ consumes or moves every responder probe; every later stage frames that
field, including emergency Head replacement. No initial cleanliness is assumed. -/
theorem pipeline_responder_probe_false {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (PPLLAstraDesign2.pipeline hψ κ .head l r).2.probe = false := by
  simp only [PPLLAstraDesign2.pipeline, (conserve_probe_echo _ _ _).1,
    (write_probe_echo _ _ _).1, (kernel_probe_echo _ _ _).1, prefix_probe_false]

/-- Complete local responder sanitation for the frozen Head transition.
This is a one-interaction statement; it does not assert that later interactions
with this agent as initiator preserve any of the four properties. -/
theorem pipeline_responder_sanitized {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    let u := (PPLLAstraDesign2.pipeline hψ κ .head l r).2
    u.probe = false ∧ u.echo = false ∧ u.bullet ≠ (2 : Fin 3) ∧
      (u.leader = true → u.label = ⟨0, hψ⟩) := by
  exact ⟨pipeline_responder_probe_false hψ κ l r,
    pipeline_responder_echo_false hψ κ l r,
    pipeline_responder_bullet_not_live hψ κ l r,
    pipeline_responder_leader_label_zero hψ κ l r⟩

#print axioms pipeline_responder_leader_label_zero
#print axioms pipeline_responder_echo_false
#print axioms pipeline_responder_bullet_not_live
#check @pipeline_responder_leader_label_zero
#check @pipeline_responder_echo_false
#check @pipeline_responder_bullet_not_live
#print axioms pipeline_responder_probe_false
#print axioms pipeline_responder_sanitized
#check @pipeline_responder_sanitized
end PPLLAstraResponder
