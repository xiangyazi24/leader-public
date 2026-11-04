import Leader.Wu.ZeroDivisible.HeadAnchor
/-! Projection interfaces for a shielded initiator of the Astra2 Head
pipeline. These local claims impose no provenance assumptions on other fields. -/
namespace PPLLAstraShieldAnchor
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2
  PPLLPostElectionGuard PPLLFableDesignR1 PPLLAstraDesign2
set_option linter.unusedSimpArgs false

namespace Frame_leader
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

private theorem suffix_left {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : (suffix hψ κ l r).1.leader = l.leader := by
  simp only [suffix, (suppress_leaders _ _ _).1, compare_left,
    (disappear_leaders _ _ _).1, check_left]

theorem before_left {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    (beforeElimination hψ κ l r).1.leader = l.leader := by
  simp only [beforeElimination, (suppress_leaders _ _ _).1, compare_left,
    (disappear_leaders _ _ _).1, check_left, (reset_leaders _ _).1,
    drop_leader, (sig_leaders _ _ _).1, (eliminate_leaders _ _ _).1,
    (clean_leaders _ _ _).1, (gen_leaders _ _ _ _).1, pPsi_wall_left]
end Frame_leader

namespace Frame_shield
private theorem leader_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).shield = if p then a.shield else b.shield := by
  split <;> rfl

private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by
  split <;> rfl

private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by
  split <;> rfl

private theorem gen_leaders {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (genSigSaturated hψ κ l r).1.shield = l.shield ∧
    (genSigSaturated hψ κ l r).2.shield = r.shield := by
  simp only [genSigSaturated, genSigSaturatedAfterWait, genSigSaturatedStart,
    genSigSaturatedEmit, genSigSaturatedPropagate, genSigSaturatedFinish,
    waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish] <;> simp only [fst_ite, snd_ite, leader_ite, ite_self, and_self]

private theorem cleanSigGenConnect_leader {ψ : Nat} (u : AgentState ψ) :
    (cleanSigGenConnect u).shield = u.shield := by
  cases h : u.path <;>
    simp only [cleanSigGenConnect, h] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem cleanSigCleanApply_leader {ψ : Nat} (u : AgentState ψ) :
    (cleanSigCleanApply u).shield = u.shield := by
  cases h : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp only [cleanSigCleanApply, h, h4, h5] <;>
    (repeat split) <;> simp_all [leader_ite]

private theorem clean3_leaders {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep3 l r).1.shield = l.shield ∧
    (cleanSigStep3 l r).2.shield = r.shield := by
  cases h : r.path4 <;> cases hp : l.path <;> simp only [cleanSigStep3, h, hp] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem clean4_leaders {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep4 l r).1.shield = l.shield ∧
    (cleanSigStep4 l r).2.shield = r.shield := by
  cases h : l.path5 <;> cases hp : r.path <;> simp only [cleanSigStep4, h, hp] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem clean5_leaders {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).1.shield = l.shield ∧
    (cleanSigStep5 hψ l r).2.shield = r.shield := by
  cases h : r.path4 <;> simp only [cleanSigStep5, h] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem clean6_leaders {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).1.shield = l.shield ∧
    (cleanSigStep6 hψ l r).2.shield = r.shield := by
  cases h : l.path5 <;> simp only [cleanSigStep6, h] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem clean_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (cleanSig hψ l r).1.shield = l.shield ∧
    (cleanSig hψ l r).2.shield = r.shield := by
  simp only [cleanSig]
  simp only [cleanSigGenConnect_leader, cleanSigCleanApply_leader,
    (clean3_leaders _ _).1, (clean3_leaders _ _).2,
    (clean4_leaders _ _).1, (clean4_leaders _ _).2,
    (clean5_leaders _ _ _).1, (clean5_leaders _ _ _).2,
    (clean6_leaders _ _ _).1, (clean6_leaders _ _ _).2, and_self]

private theorem eliminate_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.shield = l.shield ∧
    (eliminateSig hψ l r).2.shield = r.shield := by
  simp only [eliminateSig] <;> simp [fst_ite, snd_ite, leader_ite]

private theorem step1_leaders {ψ : Nat} (l r : AgentState ψ) :
    (sigMoveStep1With .dropMisaligned l r).1.shield = l.shield ∧
    (sigMoveStep1With .dropMisaligned l r).2.shield = r.shield := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [sigMoveStep1With, hl, hr] <;> simp [fst_ite, snd_ite, leader_ite]

private theorem moveTokens_leaders {ψ : Nat} (l r : AgentState ψ) :
    (moveTokens l r).1.shield = l.shield ∧
    (moveTokens l r).2.shield = r.shield := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [moveTokens, hl, hr] <;> simp [fst_ite, snd_ite, leader_ite]

private theorem control_leader {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (sigMoveApplyControlConsume hψ u).shield = u.shield := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;> simp [fst_ite, snd_ite, leader_ite]

private theorem sig_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (sigMoveF hψ true .dropMisaligned l r).1.shield = l.shield ∧
    (sigMoveF hψ true .dropMisaligned l r).2.shield = r.shield := by
  simp only [sigMoveF]
  simp only [fst_ite, snd_ite, leader_ite, control_leader]
  simp only [leaderWall, clearCmp, fst_ite, snd_ite, leader_ite,
    ite_self, (moveTokens_leaders _ _).1, (moveTokens_leaders _ _).2,
    (step1_leaders _ _).1, (step1_leaders _ _).2, and_self]

private theorem pPsi_wall_left {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (pPsiProbeWall hψ l r).1.shield = l.shield := by
  simp only [pPsiProbeWall, pPsi]
  simp [fst_ite, snd_ite, leader_ite]

private theorem drop_leader {ψ : Nat} (u : AgentState ψ) :
    (dropStale u).shield = u.shield := by
  simp only [dropStale]
  simp [leader_ite]

private theorem reset_leaders {ψ : Nat} (l r : AgentState ψ) :
    (preCheckReset l r).1.shield = l.shield ∧
    (preCheckReset l r).2.shield = r.shield := by
  simp only [preCheckReset, clearCmp]
  simp [leader_ite]

private theorem ready_leader {ψ : Nat} (u : AgentState ψ) :
    (readyF u).shield = u.shield := by
  cases hp : u.path <;>
    simp only [readyF, checkSigSetReadyGuarded, checkSigSetReady, hp] <;>
    simp [leader_ite]

private theorem checkL_leader {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (checkSigCheckL hψ u).shield = u.shield := by
  unfold checkSigCheckL
  split <;> simp [leader_ite]

private theorem result_leader {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetResult u).shield = u.shield := by
  simp only [checkSigSetResult]
  simp [leader_ite]

private theorem check_left {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (checkSigF hψ κ false l r).1.shield = l.shield := by
  simp only [checkSigF, fst_ite, leader_ite, result_leader,
    checkL_leader, ready_leader, clearCmp]
  simp [leader_ite]

private theorem disappear_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (disappear hψ l r).1.shield = l.shield ∧
    (disappear hψ l r).2.shield = r.shield := by
  simp only [disappear]
  simp [fst_ite, snd_ite, leader_ite]

private theorem init_leader {ψ : Nat} (u : AgentState ψ) :
    (compareSigInit u).shield = u.shield := by
  cases h : u.path <;> simp [compareSigInit, h]

private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by
  split <;> rfl

private theorem maintain_left {ψ : Nat} (l r : AgentState ψ) :
    (maintain l r).1.shield = l.shield := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [maintain, hl, hr] <;>
    simp [leader_ite, path_ite, hl, hr]

private theorem wave_left {ψ : Nat} (l r : AgentState ψ) :
    (wave l r).1.shield = l.shield := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [wave, hl, hr] <;> simp [leader_ite]

private theorem stray_left {ψ : Nat} (l r : AgentState ψ) :
    (dropStray l r).1.shield = l.shield := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [dropStray, hl, hr] <;> simp [leader_ite]

private theorem backward_leader {ψ : Nat} (u : AgentState ψ) :
    (landBackward u).shield = u.shield := by
  cases ht : u.path2 <;> cases hp : u.path <;>
    simp only [landBackward, ht, hp] <;> simp [leader_ite]

private theorem compare_left {ψ : Nat} (κ : Nat) (l r : AgentState ψ) :
    (compareSigF κ false true l r).1.shield = l.shield := by
  simp only [compareSigF, backward_leader, stray_left, wave_left,
    maintain_left, init_leader]

private theorem kill_leader {ψ : Nat} (u : AgentState ψ) :
    (if u.reset_cmd then clearCmp u else u).shield = u.shield := by
  by_cases h : u.reset_cmd = true <;> simp [h, clearCmp]

private theorem suppressSigStart_leaders {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigStart l r).1.shield = l.shield ∧
    (suppressSigStart l r).2.shield = r.shield := by
  simp only [suppressSigStart]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppressSigMoveReset_leaders {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigMoveReset l r).1.shield = l.shield ∧
    (suppressSigMoveReset l r).2.shield = r.shield := by
  simp only [suppressSigMoveReset]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppressSigTerminal_leaders {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (suppressSigTerminal hψ l r).1.shield = l.shield ∧
    (suppressSigTerminal hψ l r).2.shield = r.shield := by
  simp only [suppressSigTerminal]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppressSigEcho_leaders {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigEcho l r).1.shield = l.shield ∧
    (suppressSigEcho l r).2.shield = r.shield := by
  simp only [suppressSigEcho]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppressSigFinish_leaders {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigFinish l r).1.shield = l.shield ∧
    (suppressSigFinish l r).2.shield = r.shield := by
  simp only [suppressSigFinish]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppress_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (suppressSigResetKill hψ l r).1.shield = l.shield ∧
    (suppressSigResetKill hψ l r).2.shield = r.shield := by
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
    (l r : AgentState ψ) : (stagePrefix hψ κ l r).1.shield = l.shield := by
  simp only [stagePrefix, drop_leader, (sig_leaders _ _ _).1,
    (eliminate_leaders _ _ _).1, (clean_leaders _ _ _).1,
    (gen_leaders _ _ _ _).1, pPsi_wall_left]

private theorem suffix_left {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : (suffix hψ κ l r).1.shield = l.shield := by
  simp only [suffix, (suppress_leaders _ _ _).1, compare_left,
    (disappear_leaders _ _ _).1, check_left]

theorem before_left {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    (beforeElimination hψ κ l r).1.shield = l.shield := by
  simp only [beforeElimination, (suppress_leaders _ _ _).1, compare_left,
    (disappear_leaders _ _ _).1, check_left, (reset_leaders _ _).1,
    drop_leader, (sig_leaders _ _ _).1, (eliminate_leaders _ _ _).1,
    (clean_leaders _ _ _).1, (gen_leaders _ _ _ _).1, pPsi_wall_left]
end Frame_shield



namespace Frame_label
private theorem leader_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).label = if p then a.label else b.label := by
  split <;> rfl

private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by
  split <;> rfl

private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by
  split <;> rfl

private theorem gen_leaders {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (genSigSaturated hψ κ l r).1.label = l.label ∧
    (genSigSaturated hψ κ l r).2.label = r.label := by
  simp only [genSigSaturated, genSigSaturatedAfterWait, genSigSaturatedStart,
    genSigSaturatedEmit, genSigSaturatedPropagate, genSigSaturatedFinish,
    waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish] <;> simp only [fst_ite, snd_ite, leader_ite, ite_self, and_self]

private theorem cleanSigGenConnect_leader {ψ : Nat} (u : AgentState ψ) :
    (cleanSigGenConnect u).label = u.label := by
  cases h : u.path <;>
    simp only [cleanSigGenConnect, h] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem cleanSigCleanApply_leader {ψ : Nat} (u : AgentState ψ) :
    (cleanSigCleanApply u).label = u.label := by
  cases h : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp only [cleanSigCleanApply, h, h4, h5] <;>
    (repeat split) <;> simp_all [leader_ite]

private theorem clean3_leaders {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep3 l r).1.label = l.label ∧
    (cleanSigStep3 l r).2.label = r.label := by
  cases h : r.path4 <;> cases hp : l.path <;> simp only [cleanSigStep3, h, hp] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem clean4_leaders {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep4 l r).1.label = l.label ∧
    (cleanSigStep4 l r).2.label = r.label := by
  cases h : l.path5 <;> cases hp : r.path <;> simp only [cleanSigStep4, h, hp] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem clean5_leaders {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).1.label = l.label ∧
    (cleanSigStep5 hψ l r).2.label = r.label := by
  cases h : r.path4 <;> simp only [cleanSigStep5, h] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem clean6_leaders {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).1.label = l.label ∧
    (cleanSigStep6 hψ l r).2.label = r.label := by
  cases h : l.path5 <;> simp only [cleanSigStep6, h] <;>
    simp [fst_ite, snd_ite, leader_ite]

private theorem clean_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (cleanSig hψ l r).1.label = l.label ∧
    (cleanSig hψ l r).2.label = r.label := by
  simp only [cleanSig]
  simp only [cleanSigGenConnect_leader, cleanSigCleanApply_leader,
    (clean3_leaders _ _).1, (clean3_leaders _ _).2,
    (clean4_leaders _ _).1, (clean4_leaders _ _).2,
    (clean5_leaders _ _ _).1, (clean5_leaders _ _ _).2,
    (clean6_leaders _ _ _).1, (clean6_leaders _ _ _).2, and_self]

private theorem eliminate_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.label = l.label ∧
    (eliminateSig hψ l r).2.label = r.label := by
  simp only [eliminateSig] <;> simp [fst_ite, snd_ite, leader_ite]

private theorem step1_leaders {ψ : Nat} (l r : AgentState ψ) :
    (sigMoveStep1With .dropMisaligned l r).1.label = l.label ∧
    (sigMoveStep1With .dropMisaligned l r).2.label = r.label := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [sigMoveStep1With, hl, hr] <;> simp [fst_ite, snd_ite, leader_ite]

private theorem moveTokens_leaders {ψ : Nat} (l r : AgentState ψ) :
    (moveTokens l r).1.label = l.label ∧
    (moveTokens l r).2.label = r.label := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [moveTokens, hl, hr] <;> simp [fst_ite, snd_ite, leader_ite]

private theorem control_leader {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (sigMoveApplyControlConsume hψ u).label = u.label := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;> simp [fst_ite, snd_ite, leader_ite]

private theorem sig_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (sigMoveF hψ true .dropMisaligned l r).1.label = l.label ∧
    (sigMoveF hψ true .dropMisaligned l r).2.label = r.label := by
  simp only [sigMoveF]
  simp only [fst_ite, snd_ite, leader_ite, control_leader]
  simp only [leaderWall, clearCmp, fst_ite, snd_ite, leader_ite,
    ite_self, (moveTokens_leaders _ _).1, (moveTokens_leaders _ _).2,
    (step1_leaders _ _).1, (step1_leaders _ _).2, and_self]

private theorem pPsi_wall_left {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (pPsiProbeWall hψ l r).1.label = l.label := by
  simp only [pPsiProbeWall, pPsi]
  simp [fst_ite, snd_ite, leader_ite]

private theorem drop_leader {ψ : Nat} (u : AgentState ψ) :
    (dropStale u).label = u.label := by
  simp only [dropStale]
  simp [leader_ite]

private theorem reset_leaders {ψ : Nat} (l r : AgentState ψ) :
    (preCheckReset l r).1.label = l.label ∧
    (preCheckReset l r).2.label = r.label := by
  simp only [preCheckReset, clearCmp]
  simp [leader_ite]

private theorem ready_leader {ψ : Nat} (u : AgentState ψ) :
    (readyF u).label = u.label := by
  cases hp : u.path <;>
    simp only [readyF, checkSigSetReadyGuarded, checkSigSetReady, hp] <;>
    simp [leader_ite]

private theorem checkL_leader {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (checkSigCheckL hψ u).label = u.label := by
  unfold checkSigCheckL
  split <;> simp [leader_ite]

private theorem result_leader {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetResult u).label = u.label := by
  simp only [checkSigSetResult]
  simp [leader_ite]

private theorem check_left {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (checkSigF hψ κ false l r).1.label = l.label := by
  simp only [checkSigF, fst_ite, leader_ite, result_leader,
    checkL_leader, ready_leader, clearCmp]
  simp [leader_ite]

private theorem disappear_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (disappear hψ l r).1.label = l.label ∧
    (disappear hψ l r).2.label = r.label := by
  simp only [disappear]
  simp [fst_ite, snd_ite, leader_ite]

private theorem init_leader {ψ : Nat} (u : AgentState ψ) :
    (compareSigInit u).label = u.label := by
  cases h : u.path <;> simp [compareSigInit, h]

private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by
  split <;> rfl

private theorem maintain_left {ψ : Nat} (l r : AgentState ψ) :
    (maintain l r).1.label = l.label := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [maintain, hl, hr] <;>
    simp [leader_ite, path_ite, hl, hr]

private theorem wave_left {ψ : Nat} (l r : AgentState ψ) :
    (wave l r).1.label = l.label := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [wave, hl, hr] <;> simp [leader_ite]

private theorem stray_left {ψ : Nat} (l r : AgentState ψ) :
    (dropStray l r).1.label = l.label := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [dropStray, hl, hr] <;> simp [leader_ite]

private theorem backward_leader {ψ : Nat} (u : AgentState ψ) :
    (landBackward u).label = u.label := by
  cases ht : u.path2 <;> cases hp : u.path <;>
    simp only [landBackward, ht, hp] <;> simp [leader_ite]

private theorem compare_left {ψ : Nat} (κ : Nat) (l r : AgentState ψ) :
    (compareSigF κ false true l r).1.label = l.label := by
  simp only [compareSigF, backward_leader, stray_left, wave_left,
    maintain_left, init_leader]

private theorem kill_leader {ψ : Nat} (u : AgentState ψ) :
    (if u.reset_cmd then clearCmp u else u).label = u.label := by
  by_cases h : u.reset_cmd = true <;> simp [h, clearCmp]

private theorem suppressSigStart_leaders {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigStart l r).1.label = l.label ∧
    (suppressSigStart l r).2.label = r.label := by
  simp only [suppressSigStart]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppressSigMoveReset_leaders {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigMoveReset l r).1.label = l.label ∧
    (suppressSigMoveReset l r).2.label = r.label := by
  simp only [suppressSigMoveReset]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppressSigTerminal_leaders {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (suppressSigTerminal hψ l r).1.label = l.label ∧
    (suppressSigTerminal hψ l r).2.label = r.label := by
  simp only [suppressSigTerminal]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppressSigEcho_leaders {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigEcho l r).1.label = l.label ∧
    (suppressSigEcho l r).2.label = r.label := by
  simp only [suppressSigEcho]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppressSigFinish_leaders {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigFinish l r).1.label = l.label ∧
    (suppressSigFinish l r).2.label = r.label := by
  simp only [suppressSigFinish]
  simp [fst_ite, snd_ite, leader_ite]

private theorem suppress_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (suppressSigResetKill hψ l r).1.label = l.label ∧
    (suppressSigResetKill hψ l r).2.label = r.label := by
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
    (l r : AgentState ψ) : (stagePrefix hψ κ l r).1.label = l.label := by
  simp only [stagePrefix, drop_leader, (sig_leaders _ _ _).1,
    (eliminate_leaders _ _ _).1, (clean_leaders _ _ _).1,
    (gen_leaders _ _ _ _).1, pPsi_wall_left]

private theorem suffix_left {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : (suffix hψ κ l r).1.label = l.label := by
  simp only [suffix, (suppress_leaders _ _ _).1, compare_left,
    (disappear_leaders _ _ _).1, check_left]

theorem before_left {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    (beforeElimination hψ κ l r).1.label = l.label := by
  simp only [beforeElimination, (suppress_leaders _ _ _).1, compare_left,
    (disappear_leaders _ _ _).1, check_left, (reset_leaders _ _).1,
    drop_leader, (sig_leaders _ _ _).1, (eliminate_leaders _ _ _).1,
    (clean_leaders _ _ _).1, (gen_leaders _ _ _ _).1, pPsi_wall_left]
end Frame_label

namespace Write_shield
private theorem proj_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).shield = if p then a.shield else b.shield := by split <;> rfl
private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem writeSeqSetWriteReady_frame {ψ : Nat} (u : AgentState ψ) : (writeSeqSetWriteReady u).shield = u.shield := by
  unfold writeSeqSetWriteReady; repeat (first | rfl | split)
private theorem writeSeqSetWriteAct_frame {ψ : Nat} (u : AgentState ψ) : (writeSeqSetWriteAct u).shield = u.shield := by
  cases h : u.path3 <;> simp [writeSeqSetWriteAct, h, proj_ite]
private theorem moveWsigCheckLast_frame {ψ : Nat} (u : AgentState ψ) : (moveWsigCheckLast u).shield = u.shield := by
  unfold moveWsigCheckLast; repeat (first | rfl | split)
private theorem moveWsigTransfer_frame {ψ : Nat} (l r : AgentState ψ) :
    (moveWsigTransfer l r).1.shield = l.shield := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp [moveWsigTransfer, hl, hr, fst_ite, snd_ite, proj_ite]
private theorem groupInfo_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (groupInfo hψ l r).1.shield = l.shield := by
  simp only [groupInfo, fst_ite, snd_ite, proj_ite, ite_self]
private theorem gensigWriteseq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (gensigWriteseq hψ l r).1.shield = l.shield := by
  simp only [gensigWriteseq, fst_ite, snd_ite, proj_ite, ite_self]
private theorem writeAction_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeAction hψ l r).1.shield = l.shield := by
  simp only [writeAction, fst_ite, snd_ite, proj_ite, ite_self]
private theorem move_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (moveWsig hψ l r).1.shield = l.shield := by
  simp only [moveWsig, moveWsigTransfer_frame, moveWsigCheckLast_frame,
    fst_ite, snd_ite, proj_ite, ite_self]
theorem frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeq hψ l r).1.shield = l.shield := by
  simp only [writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands, groupInfo_frame, gensigWriteseq_frame,
    writeSeqSetWriteReady_frame, writeSeqSetWriteAct_frame,
    writeAction_frame, move_frame, fst_ite, snd_ite, proj_ite, ite_self]
end Write_shield

namespace Write_signal_B
private theorem proj_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).signal_B = if p then a.signal_B else b.signal_B := by split <;> rfl
private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem writeSeqSetWriteReady_frame {ψ : Nat} (u : AgentState ψ) : (writeSeqSetWriteReady u).signal_B = u.signal_B := by
  unfold writeSeqSetWriteReady; repeat (first | rfl | split)
private theorem writeSeqSetWriteAct_frame {ψ : Nat} (u : AgentState ψ) : (writeSeqSetWriteAct u).signal_B = u.signal_B := by
  cases h : u.path3 <;> simp [writeSeqSetWriteAct, h, proj_ite]
private theorem moveWsigCheckLast_frame {ψ : Nat} (u : AgentState ψ) : (moveWsigCheckLast u).signal_B = u.signal_B := by
  unfold moveWsigCheckLast; repeat (first | rfl | split)
private theorem moveWsigTransfer_frame {ψ : Nat} (l r : AgentState ψ) :
    (moveWsigTransfer l r).1.signal_B = l.signal_B := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp [moveWsigTransfer, hl, hr, fst_ite, snd_ite, proj_ite]
private theorem groupInfo_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (groupInfo hψ l r).1.signal_B = l.signal_B := by
  simp only [groupInfo, fst_ite, snd_ite, proj_ite, ite_self]
private theorem gensigWriteseq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (gensigWriteseq hψ l r).1.signal_B = l.signal_B := by
  simp only [gensigWriteseq, fst_ite, snd_ite, proj_ite, ite_self]
private theorem writeAction_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeAction hψ l r).1.signal_B = l.signal_B := by
  simp only [writeAction, fst_ite, snd_ite, proj_ite, ite_self]
private theorem move_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (moveWsig hψ l r).1.signal_B = l.signal_B := by
  simp only [moveWsig, moveWsigTransfer_frame, moveWsigCheckLast_frame,
    fst_ite, snd_ite, proj_ite, ite_self]
theorem frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeSeq hψ l r).1.signal_B = l.signal_B := by
  simp only [writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands, groupInfo_frame, gensigWriteseq_frame,
    writeSeqSetWriteReady_frame, writeSeqSetWriteAct_frame,
    writeAction_frame, move_frame, fst_ite, snd_ite, proj_ite, ite_self]
end Write_signal_B

/-- K4 cannot kill a shielded initiating leader. FIRE consumes its binary
absence signal; neither absorption nor the responder signal update changes
this initiator projection. -/
theorem kernel_outgoing {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hs : l.shield = true) :
    (k4Kernel hψ l r).1.leader = true ∧
    (k4Kernel hψ l r).1.shield = true ∧
    (k4Kernel hψ l r).1.signal_B = 0 ∧
    (k4Kernel hψ l r).1.label = l.label := by
  have hb : l.signal_B = 0 ∨ l.signal_B = 1 := by
    have := l.signal_B.isLt
    omega
  have hsig : r.signal_B = 0 ∨ r.signal_B = 1 := by
    have := r.signal_B.isLt
    omega
  have hbul : r.bullet = 0 ∨ r.bullet = 1 ∨ r.bullet = 2 := by
    have := r.bullet.isLt
    omega
  rcases hb with hb | hb <;> rcases hsig with hsig | hsig <;>
    rcases hbul with hbul | hbul | hbul <;> cases hr : r.leader <;>
    simp [hr, hsig, hbul, k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire, hl, hs, hb,
      absorbAnyMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]

attribute [local irreducible] beforeElimination k4Kernel writeSeq

/-- The full frozen Head transition preserves a shielded initiating leader,
retains its physical label, and clears its absence signal. All responder and
ancillary fields are arbitrary. This is a local interface, not convergence. -/
theorem pipeline_outgoing {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) (hl : l.leader = true) (hs : l.shield = true) :
    (PPLLAstraDesign2.pipeline hψ κ .head l r).1.leader = true ∧
    (PPLLAstraDesign2.pipeline hψ κ .head l r).1.shield = true ∧
    (PPLLAstraDesign2.pipeline hψ κ .head l r).1.signal_B = 0 ∧
    (PPLLAstraDesign2.pipeline hψ κ .head l r).1.label = l.label := by
  simp only [PPLLAstraDesign2.pipeline]
  generalize hq : beforeElimination hψ κ l r = q
  have ql : q.1.leader = true := by
    rw [← hq, Frame_leader.before_left, hl]
  have qs : q.1.shield = true := by
    rw [← hq, Frame_shield.before_left, hs]
  have qlabel : q.1.label = l.label := by
    rw [← hq, Frame_label.before_left]
  have hk := kernel_outgoing hψ q.1 q.2 ql qs
  generalize hkdef : k4Kernel hψ q.1 q.2 = k at *
  have kl : k.1.leader = true := hk.1
  have wl : (writeSeq hψ k.1 k.2).1.leader = true :=
    PPLLVerify.writeSeq_initiator_leader_of_true hψ _ _ kl
  simp only [writeWithBundle, kl, Bool.true_eq_false, and_false, ite_false]
  simp only [conserve, wl, Bool.true_or, Bool.not_true, Bool.and_false, ite_false]
  exact ⟨wl, (Write_shield.frame hψ _ _).trans hk.2.1,
    (Write_signal_B.frame hψ _ _).trans hk.2.2.1,
    (PPLLVerify.writeSeq_l_label hψ _ _).trans (hk.2.2.2.trans qlabel)⟩
#print axioms pipeline_outgoing
#check @pipeline_outgoing
end PPLLAstraShieldAnchor
