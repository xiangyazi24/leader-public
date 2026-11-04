import Leader.Wu.ZeroDivisible.K4BoundaryEquality
import Leader.Wu.Safety.ConcreteProtocolProperties

/-!
Local anchor lemmas for the frozen round-two Head pipeline. These results concern
arbitrary ancillary fields at an edge with an existing leader. They do not claim
that a global execution reaches or retains singleton count.
-/
namespace PPLLAstraHeadAnchor
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2
  PPLLPostElectionGuard PPLLFableDesignR1 PPLLAstraDesign2


private theorem leader_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).leader = if p then a.leader else b.leader := by
  split <;> rfl

private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by
  split <;> rfl

private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by
  split <;> rfl

private theorem pPsi_wall_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) (h : l.leader = true ∨ r.leader = true) :
    (pPsiProbeWall hψ l r).1.leader = l.leader ∧
    (pPsiProbeWall hψ l r).2.leader = r.leader := by
  rcases h with h | h <;>
    simp only [pPsiProbeWall, pPsi, h] <;> simp [fst_ite, snd_ite, leader_ite]

private theorem gen_leaders {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (genSigSaturated hψ κ l r).1.leader = l.leader ∧
    (genSigSaturated hψ κ l r).2.leader = r.leader := by
  simp only [genSigSaturated, genSigSaturatedAfterWait, genSigSaturatedStart,
    genSigSaturatedEmit, genSigSaturatedPropagate, genSigSaturatedFinish,
    waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish] <;> simp only [fst_ite, snd_ite, leader_ite, ite_self, and_self]

private theorem cleanSigGenConnect_leader {ψ : Nat} (u : AgentState ψ) :
    (cleanSigGenConnect u).leader = u.leader := by
  cases h : u.path <;>
    simp only [cleanSigGenConnect, h] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem cleanSigCleanApply_leader {ψ : Nat} (u : AgentState ψ) :
    (cleanSigCleanApply u).leader = u.leader := by
  cases h : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp only [cleanSigCleanApply, h, h4, h5] <;>
    (repeat split) <;> simp_all [leader_ite]

private theorem clean3_leaders {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep3 l r).1.leader = l.leader ∧
    (cleanSigStep3 l r).2.leader = r.leader := by
  cases h : r.path4 <;> cases hp : l.path <;> simp only [cleanSigStep3, h, hp] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem clean4_leaders {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep4 l r).1.leader = l.leader ∧
    (cleanSigStep4 l r).2.leader = r.leader := by
  cases h : l.path5 <;> cases hp : r.path <;> simp only [cleanSigStep4, h, hp] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem clean5_leaders {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).1.leader = l.leader ∧
    (cleanSigStep5 hψ l r).2.leader = r.leader := by
  cases h : r.path4 <;> simp only [cleanSigStep5, h] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem clean6_leaders {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).1.leader = l.leader ∧
    (cleanSigStep6 hψ l r).2.leader = r.leader := by
  cases h : l.path5 <;> simp only [cleanSigStep6, h] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem clean_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (cleanSig hψ l r).1.leader = l.leader ∧
    (cleanSig hψ l r).2.leader = r.leader := by
  simp only [cleanSig]
  simp only [cleanSigGenConnect_leader, cleanSigCleanApply_leader,
    (clean3_leaders _ _).1, (clean3_leaders _ _).2,
    (clean4_leaders _ _).1, (clean4_leaders _ _).2,
    (clean5_leaders _ _ _).1, (clean5_leaders _ _ _).2,
    (clean6_leaders _ _ _).1, (clean6_leaders _ _ _).2, and_self]

private theorem eliminate_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.leader = l.leader ∧
    (eliminateSig hψ l r).2.leader = r.leader := by
  simp only [eliminateSig] <;> simp [fst_ite, snd_ite, leader_ite]

private theorem step1_leaders {ψ : Nat} (l r : AgentState ψ) :
    (sigMoveStep1With .dropMisaligned l r).1.leader = l.leader ∧
    (sigMoveStep1With .dropMisaligned l r).2.leader = r.leader := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [sigMoveStep1With, hl, hr] <;> simp [fst_ite, snd_ite, leader_ite]

private theorem moveTokens_leaders {ψ : Nat} (l r : AgentState ψ) :
    (moveTokens l r).1.leader = l.leader ∧
    (moveTokens l r).2.leader = r.leader := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [moveTokens, hl, hr] <;> simp [fst_ite, snd_ite, leader_ite]

private theorem control_leader {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (sigMoveApplyControlConsume hψ u).leader = u.leader := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;> simp [fst_ite, snd_ite, leader_ite]

private theorem sig_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (sigMoveF hψ true .dropMisaligned l r).1.leader = l.leader ∧
    (sigMoveF hψ true .dropMisaligned l r).2.leader = r.leader := by
  simp only [sigMoveF]
  simp only [fst_ite, snd_ite, leader_ite, control_leader]
  simp only [leaderWall, clearCmp, fst_ite, snd_ite, leader_ite,
    ite_self, (moveTokens_leaders _ _).1, (moveTokens_leaders _ _).2,
    (step1_leaders _ _).1, (step1_leaders _ _).2, and_self]

private theorem pPsi_wall_left {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (pPsiProbeWall hψ l r).1.leader = l.leader := by
  simp only [pPsiProbeWall, pPsi]
  simp [fst_ite, snd_ite, leader_ite]

private theorem drop_leader {ψ : Nat} (u : AgentState ψ) :
    (dropStale u).leader = u.leader := by
  simp only [dropStale]
  simp [leader_ite]

private theorem reset_leaders {ψ : Nat} (l r : AgentState ψ) :
    (preCheckReset l r).1.leader = l.leader ∧
    (preCheckReset l r).2.leader = r.leader := by
  simp only [preCheckReset, clearCmp]
  simp [leader_ite]

private theorem ready_leader {ψ : Nat} (u : AgentState ψ) :
    (readyF u).leader = u.leader := by
  cases hp : u.path <;>
    simp only [readyF, checkSigSetReadyGuarded, checkSigSetReady, hp] <;>
    simp [leader_ite]

private theorem checkL_leader {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (checkSigCheckL hψ u).leader = u.leader := by
  unfold checkSigCheckL
  split <;> simp [leader_ite]

private theorem result_leader {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetResult u).leader = u.leader := by
  simp only [checkSigSetResult]
  simp [leader_ite]

private theorem check_left {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (checkSigF hψ κ false l r).1.leader = l.leader := by
  simp only [checkSigF, fst_ite, leader_ite, result_leader,
    checkL_leader, ready_leader, clearCmp]
  simp [leader_ite]

private theorem disappear_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (disappear hψ l r).1.leader = l.leader ∧
    (disappear hψ l r).2.leader = r.leader := by
  simp only [disappear]
  simp [fst_ite, snd_ite, leader_ite]

private theorem init_leader {ψ : Nat} (u : AgentState ψ) :
    (compareSigInit u).leader = u.leader := by
  cases h : u.path <;> simp [compareSigInit, h]

private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by
  split <;> rfl

private theorem maintain_left {ψ : Nat} (l r : AgentState ψ) :
    (maintain l r).1.leader = l.leader := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [maintain, hl, hr] <;>
    simp [leader_ite, path_ite, hl, hr]

private theorem wave_left {ψ : Nat} (l r : AgentState ψ) :
    (wave l r).1.leader = l.leader := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [wave, hl, hr] <;> simp [leader_ite]

private theorem stray_left {ψ : Nat} (l r : AgentState ψ) :
    (dropStray l r).1.leader = l.leader := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [dropStray, hl, hr] <;> simp [leader_ite]

private theorem backward_leader {ψ : Nat} (u : AgentState ψ) :
    (landBackward u).leader = u.leader := by
  cases ht : u.path2 <;> cases hp : u.path <;>
    simp only [landBackward, ht, hp] <;> simp [leader_ite]

private theorem compare_left {ψ : Nat} (κ : Nat) (l r : AgentState ψ) :
    (compareSigF κ false true l r).1.leader = l.leader := by
  simp only [compareSigF, backward_leader, stray_left, wave_left,
    maintain_left, init_leader]

private theorem kill_leader {ψ : Nat} (u : AgentState ψ) :
    (if u.reset_cmd then clearCmp u else u).leader = u.leader := by
  by_cases h : u.reset_cmd = true <;> simp [h, clearCmp]

private theorem suppressSigStart_leaders {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigStart l r).1.leader = l.leader ∧
    (suppressSigStart l r).2.leader = r.leader := by
  simp only [suppressSigStart]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppressSigMoveReset_leaders {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigMoveReset l r).1.leader = l.leader ∧
    (suppressSigMoveReset l r).2.leader = r.leader := by
  simp only [suppressSigMoveReset]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppressSigTerminal_leaders {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (suppressSigTerminal hψ l r).1.leader = l.leader ∧
    (suppressSigTerminal hψ l r).2.leader = r.leader := by
  simp only [suppressSigTerminal]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppressSigEcho_leaders {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigEcho l r).1.leader = l.leader ∧
    (suppressSigEcho l r).2.leader = r.leader := by
  simp only [suppressSigEcho]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppressSigFinish_leaders {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigFinish l r).1.leader = l.leader ∧
    (suppressSigFinish l r).2.leader = r.leader := by
  simp only [suppressSigFinish]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppress_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (suppressSigResetKill hψ l r).1.leader = l.leader ∧
    (suppressSigResetKill hψ l r).2.leader = r.leader := by
  simp only [suppressSigResetKill,
    (suppressSigFinish_leaders _ _).1, (suppressSigFinish_leaders _ _).2,
    (suppressSigEcho_leaders _ _).1, (suppressSigEcho_leaders _ _).2,
    (suppressSigTerminal_leaders _ _ _).1, (suppressSigTerminal_leaders _ _ _).2,
    (suppressSigMoveReset_leaders _ _).1, (suppressSigMoveReset_leaders _ _).2,
    (suppressSigStart_leaders _ _).1, (suppressSigStart_leaders _ _).2,
    kill_leader, and_self]

private def stagePrefix {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :=
  let q := pPsiProbeWall hψ l r
  let q := genSigSaturated hψ κ q.1 q.2
  let q := cleanSig hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  let q := sigMoveF hψ true .dropMisaligned q.1 q.2
  (dropStale q.1, dropStale q.2)

private def suffix {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :=
  let q := checkSigF hψ κ false l r
  let q := disappear hψ q.1 q.2
  let q := compareSigF κ false true q.1 q.2
  suppressSigResetKill hψ q.1 q.2

private theorem stagePrefix_left {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : (stagePrefix hψ κ l r).1.leader = l.leader := by
  simp only [stagePrefix, drop_leader, (sig_leaders _ _ _).1,
    (eliminate_leaders _ _ _).1, (clean_leaders _ _ _).1,
    (gen_leaders _ _ _ _).1, pPsi_wall_left]

private theorem stagePrefix_leaders {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) (h : l.leader = true ∨ r.leader = true) :
    (stagePrefix hψ κ l r).1.leader = l.leader ∧
    (stagePrefix hψ κ l r).2.leader = r.leader := by
  simp only [stagePrefix, drop_leader, (sig_leaders _ _ _).1, (sig_leaders _ _ _).2,
    (eliminate_leaders _ _ _).1, (eliminate_leaders _ _ _).2,
    (clean_leaders _ _ _).1, (clean_leaders _ _ _).2,
    (gen_leaders _ _ _ _).1, (gen_leaders _ _ _ _).2]
  exact pPsi_wall_leaders hψ l r h

private theorem suffix_left {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : (suffix hψ κ l r).1.leader = l.leader := by
  simp only [suffix, (suppress_leaders _ _ _).1, compare_left,
    (disappear_leaders _ _ _).1, check_left]

private theorem suffix_clear {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (suffix hψ κ (clearCmp l) (clearCmp r)).1.leader = l.leader ∧
    (suffix hψ κ (clearCmp l) (clearCmp r)).2.leader = r.leader := by
  simp only [suffix, (suppress_leaders _ _ _).1, (suppress_leaders _ _ _).2]
  simp [checkSigF, readyF, checkSigSetReadyGuarded, controlPending,
    checkSigSetReady, checkSigCheckL, checkSigCheckR, checkSigSetResult,
    disappear, compareSigF, compareSigInit, maintain, wave, dropStray,
    landBackward, landForward, clearCmp, waveState, lockedState]

/-- Before elimination, an input leader excludes the creation of a second
leader at that edge. The initiating leader supplies pre-CHECK reset; a follower
initiator is framed by every birth stage. No ancillary-field hypothesis is used. -/
theorem beforeElimination_not_both {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) (h : ¬ (l.leader = true ∧ r.leader = true)) :
    ¬ ((beforeElimination hψ κ l r).1.leader = true ∧
       (beforeElimination hψ κ l r).2.leader = true) := by
  have heq : beforeElimination hψ κ l r =
      suffix hψ κ (preCheckReset (stagePrefix hψ κ l r).1
        (stagePrefix hψ κ l r).2).1
        (preCheckReset (stagePrefix hψ κ l r).1 (stagePrefix hψ κ l r).2).2 := rfl
  rw [heq]
  by_cases hl : l.leader = true
  · have hp := stagePrefix_leaders hψ κ l r (Or.inl hl)
    have hs : (stagePrefix hψ κ l r).1.leader = true := hp.1.trans hl
    simp only [preCheckReset, hs, Bool.true_or, ite_true]
    rw [(suffix_clear hψ κ _ _).1, (suffix_clear hψ κ _ _).2, hp.1, hp.2]
    exact h
  · intro hc
    apply hl
    exact (stagePrefix_left hψ κ l r).symm.trans
      ((reset_leaders _ _).1.symm.trans ((suffix_left hψ κ _ _).symm.trans hc.1))

private theorem fire_leaders {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.leader = l.leader ∧
    (eliminateLeadersNoCollisionFire hψ l r).2.leader = r.leader := by
  simp only [eliminateLeadersNoCollisionFire]
  simp [leader_ite]

private theorem absorb_right {ψ : Nat} (hψ : ψ > 0) (nl : Fin ψ)
    (l r : AgentState ψ) : (absorbAnyMove hψ nl l r).2.leader = r.leader := by
  simp only [absorbAnyMove, eliminateLeadersNoCollisionZeroLeaderEgressMove]
  simp [fst_ite, snd_ite, leader_ite]

private theorem absorb_left_false {ψ : Nat} (hψ : ψ > 0) (nl : Fin ψ)
    (l r : AgentState ψ) (hl : l.leader = false) :
    (absorbAnyMove hψ nl l r).1.leader = false := by
  simp only [absorbAnyMove, eliminateLeadersNoCollisionZeroLeaderEgressMove, hl]
  simp [fst_ite, snd_ite, leader_ite, hl]

private theorem signal_leaders {ψ : Nat} (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).1.leader = l.leader ∧
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.leader = r.leader := by
  simp only [eliminateLeadersNoCollisionSignalLeaderSink]
  simp [leader_ite]

private theorem dummy_leaders {ψ : Nat} (q : AgentState ψ × AgentState ψ) :
    (dummyBulletSink q).1.leader = q.1.leader ∧
    (dummyBulletSink q).2.leader = q.2.leader := by
  simp only [dummyBulletSink]
  simp [fst_ite, snd_ite, leader_ite]

private theorem k3_right {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (k3Kernel hψ l r).2.leader = r.leader := by
  simp only [k3Kernel, (dummy_leaders _).2, (signal_leaders _ _ _).2,
    absorb_right, (fire_leaders _ _ _).2]

private theorem k3_left_false {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false) : (k3Kernel hψ l r).1.leader = false := by
  simp only [k3Kernel, (dummy_leaders _).1, (signal_leaders _ _ _).1]
  exact absorb_left_false hψ _ _ _ ((fire_leaders hψ l r).1.trans hl)

private theorem k4_right {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (k4Kernel hψ l r).2.leader = r.leader := by
  by_cases h : r.bullet = (2 : Fin 3) ∧ l.leader = true ∧ l.shield = false
  · simp only [k4Kernel, if_pos h, k3_right]
  · simp only [k4Kernel, if_neg h, k3_right]

private theorem k4_left_false {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = false) : (k4Kernel hψ l r).1.leader = false := by
  simpa [k4Kernel, hl] using k3_left_false hψ l r hl

private theorem k4_not_both {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (h : ¬ (l.leader = true ∧ r.leader = true)) :
    ¬ ((k4Kernel hψ l r).1.leader = true ∧
       (k4Kernel hψ l r).2.leader = true) := by
  intro hc
  by_cases hl : l.leader = true
  · exact h ⟨hl, (k4_right hψ l r).symm.trans hc.2⟩
  · have hf : l.leader = false := Bool.eq_false_iff.mpr hl
    have he := k4_left_false hψ l r hf
    rw [he] at hc
    cases hc.1

private theorem write_not_both {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (h : ¬ (l.leader = true ∧ r.leader = true)) :
    ¬ ((writeWithBundle hψ l r).1.leader = true ∧
       (writeWithBundle hψ l r).2.leader = true) := by
  have frame : (writeWithBundle hψ l r).1.leader = (writeSeq hψ l r).1.leader ∧
      (writeWithBundle hψ l r).2.leader = (writeSeq hψ l r).2.leader := by
    simp only [writeWithBundle, fst_ite, snd_ite, leader_ite, ite_self, and_self]
  rw [frame.1, frame.2]
  intro hc
  have hr := PPLLVerify.writeSeq_responder_leader_was_leader hψ l r hc.2
  have hl : l.leader = false := Bool.eq_false_iff.mpr (fun hl => h ⟨hl, hr⟩)
  have hm := PPLLVerify.writeSeq_new_initiator_requires_responder_leader hψ l r hc.1 hl
  have hz := PPLLVerify.writeSeq_responder_false_of_nonzero_leader hψ l r hm
  rw [hz] at hc
  cases hc.2

private theorem conserve_not_both {ψ : Nat} (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ)
    (h : ¬ (q.1.leader = true ∧ q.2.leader = true)) :
    ¬ ((conserve .head l r q).1.leader = true ∧
       (conserve .head l r q).2.leader = true) := by
  cases hl : l.leader <;> cases hr : r.leader <;>
    cases hq1 : q.1.leader <;> cases hq2 : q.2.leader <;>
    simp_all [conserve, replacement, clearCmp]

/-- Head cannot output two leaders from an input edge with at most one. This
uses its actual BEQ, K4, WRITE-bundle and final conservation stages. -/
theorem pipeline_not_both {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) (h : ¬ (l.leader = true ∧ r.leader = true)) :
    ¬ ((PPLLAstraDesign2.pipeline hψ κ .head l r).1.leader = true ∧
       (PPLLAstraDesign2.pipeline hψ κ .head l r).2.leader = true) := by
  apply conserve_not_both
  apply write_not_both
  apply k4_not_both
  exact beforeElimination_not_both hψ κ l r h

/-- An incident edge with exactly one input leader has exactly one output
leader, for arbitrary ancillary fields. This local count-preservation result
supplies the no-birth part of a guarded anchor schedule; it does not establish
global convergence or the existence of a shielded anchor. -/
theorem pipeline_exactly_one {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ)
    (hpos : l.leader = true ∨ r.leader = true)
    (hone : ¬ (l.leader = true ∧ r.leader = true)) :
    ((PPLLAstraDesign2.pipeline hψ κ .head l r).1.leader = true ∨
     (PPLLAstraDesign2.pipeline hψ κ .head l r).2.leader = true) ∧
    ¬ ((PPLLAstraDesign2.pipeline hψ κ .head l r).1.leader = true ∧
       (PPLLAstraDesign2.pipeline hψ κ .head l r).2.leader = true) :=
  ⟨pipeline_nonempty hψ κ .head l r hpos, pipeline_not_both hψ κ l r hone⟩

#print axioms pipeline_exactly_one
#check @pipeline_exactly_one
end PPLLAstraHeadAnchor
