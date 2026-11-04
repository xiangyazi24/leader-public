import Leader.Wu.ZeroDivisible.HeadResponder
/-! Local active-source reset interfaces for the frozen round-two Head step.
No global sweep normalization or convergence is asserted. -/
namespace PPLLAstraReset
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard PPLLFableDesignR1 PPLLAstraDesign2
set_option linter.unusedSimpArgs false
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

private theorem reset_cmd_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).reset_cmd = if p then a.reset_cmd else b.reset_cmd := by split <;> rfl
private theorem echo_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).echo = if p then a.echo else b.echo := by split <;> rfl
/-! The pre-CHECK prefix preserves the initiator leader/reset and responder echo. -/

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

private theorem gen_reset_cmds {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (genSigSaturated hψ κ l r).1.reset_cmd = l.reset_cmd ∧
    (genSigSaturated hψ κ l r).2.reset_cmd = r.reset_cmd := by
  simp only [genSigSaturated, genSigSaturatedAfterWait, genSigSaturatedStart,
    genSigSaturatedEmit, genSigSaturatedPropagate, genSigSaturatedFinish,
    waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish] <;> simp only [fst_ite, snd_ite, reset_cmd_ite, ite_self, and_self]

private theorem cleanSigGenConnect_reset_cmd {ψ : Nat} (u : AgentState ψ) :
    (cleanSigGenConnect u).reset_cmd = u.reset_cmd := by
  cases h : u.path <;>
    simp only [cleanSigGenConnect, h] <;>
    simp [fst_ite, snd_ite, reset_cmd_ite]

private theorem cleanSigCleanApply_reset_cmd {ψ : Nat} (u : AgentState ψ) :
    (cleanSigCleanApply u).reset_cmd = u.reset_cmd := by
  cases h : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp only [cleanSigCleanApply, h, h4, h5] <;>
    (repeat split) <;> simp_all [reset_cmd_ite]

private theorem clean3_reset_cmds {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep3 l r).1.reset_cmd = l.reset_cmd ∧
    (cleanSigStep3 l r).2.reset_cmd = r.reset_cmd := by
  cases h : r.path4 <;> cases hp : l.path <;> simp only [cleanSigStep3, h, hp] <;>
    simp [fst_ite, snd_ite, reset_cmd_ite]

private theorem clean4_reset_cmds {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep4 l r).1.reset_cmd = l.reset_cmd ∧
    (cleanSigStep4 l r).2.reset_cmd = r.reset_cmd := by
  cases h : l.path5 <;> cases hp : r.path <;> simp only [cleanSigStep4, h, hp] <;>
    simp [fst_ite, snd_ite, reset_cmd_ite]

private theorem clean5_reset_cmds {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).1.reset_cmd = l.reset_cmd ∧
    (cleanSigStep5 hψ l r).2.reset_cmd = r.reset_cmd := by
  cases h : r.path4 <;> simp only [cleanSigStep5, h] <;>
    simp [fst_ite, snd_ite, reset_cmd_ite]

private theorem clean6_reset_cmds {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).1.reset_cmd = l.reset_cmd ∧
    (cleanSigStep6 hψ l r).2.reset_cmd = r.reset_cmd := by
  cases h : l.path5 <;> simp only [cleanSigStep6, h] <;>
    simp [fst_ite, snd_ite, reset_cmd_ite]

private theorem clean_reset_cmds {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (cleanSig hψ l r).1.reset_cmd = l.reset_cmd ∧
    (cleanSig hψ l r).2.reset_cmd = r.reset_cmd := by
  simp only [cleanSig]
  simp only [cleanSigGenConnect_reset_cmd, cleanSigCleanApply_reset_cmd,
    (clean3_reset_cmds _ _).1, (clean3_reset_cmds _ _).2,
    (clean4_reset_cmds _ _).1, (clean4_reset_cmds _ _).2,
    (clean5_reset_cmds _ _ _).1, (clean5_reset_cmds _ _ _).2,
    (clean6_reset_cmds _ _ _).1, (clean6_reset_cmds _ _ _).2, and_self]

private theorem eliminate_reset_cmds {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.reset_cmd = l.reset_cmd ∧
    (eliminateSig hψ l r).2.reset_cmd = r.reset_cmd := by
  simp only [eliminateSig] <;> simp [fst_ite, snd_ite, reset_cmd_ite]

private theorem step1_reset_cmds {ψ : Nat} (l r : AgentState ψ) :
    (sigMoveStep1With .dropMisaligned l r).1.reset_cmd = l.reset_cmd ∧
    (sigMoveStep1With .dropMisaligned l r).2.reset_cmd = r.reset_cmd := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [sigMoveStep1With, hl, hr] <;> simp [fst_ite, snd_ite, reset_cmd_ite]

private theorem moveTokens_reset_cmds {ψ : Nat} (l r : AgentState ψ) :
    (moveTokens l r).1.reset_cmd = l.reset_cmd ∧
    (moveTokens l r).2.reset_cmd = r.reset_cmd := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [moveTokens, hl, hr] <;> simp [fst_ite, snd_ite, reset_cmd_ite]

private theorem control_reset_cmd {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (sigMoveApplyControlConsume hψ u).reset_cmd = u.reset_cmd := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;> simp [fst_ite, snd_ite, reset_cmd_ite]

private theorem sig_reset_cmds {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (sigMoveF hψ true .dropMisaligned l r).1.reset_cmd = l.reset_cmd ∧
    (sigMoveF hψ true .dropMisaligned l r).2.reset_cmd = r.reset_cmd := by
  simp only [sigMoveF]
  simp only [fst_ite, snd_ite, reset_cmd_ite, control_reset_cmd]
  simp only [leaderWall, clearCmp, fst_ite, snd_ite, reset_cmd_ite,
    ite_self, (moveTokens_reset_cmds _ _).1, (moveTokens_reset_cmds _ _).2,
    (step1_reset_cmds _ _).1, (step1_reset_cmds _ _).2, and_self]


private theorem drop_reset_cmd {ψ : Nat} (u : AgentState ψ) :
    (dropStale u).reset_cmd = u.reset_cmd := by
  simp only [dropStale]
  simp [reset_cmd_ite]

private theorem gen_echos {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (genSigSaturated hψ κ l r).1.echo = l.echo ∧
    (genSigSaturated hψ κ l r).2.echo = r.echo := by
  simp only [genSigSaturated, genSigSaturatedAfterWait, genSigSaturatedStart,
    genSigSaturatedEmit, genSigSaturatedPropagate, genSigSaturatedFinish,
    waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish] <;> simp only [fst_ite, snd_ite, echo_ite, ite_self, and_self]

private theorem cleanSigGenConnect_echo {ψ : Nat} (u : AgentState ψ) :
    (cleanSigGenConnect u).echo = u.echo := by
  cases h : u.path <;>
    simp only [cleanSigGenConnect, h] <;>
    simp [fst_ite, snd_ite, echo_ite]

private theorem cleanSigCleanApply_echo {ψ : Nat} (u : AgentState ψ) :
    (cleanSigCleanApply u).echo = u.echo := by
  cases h : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp only [cleanSigCleanApply, h, h4, h5] <;>
    (repeat split) <;> simp_all [echo_ite]

private theorem clean3_echos {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep3 l r).1.echo = l.echo ∧
    (cleanSigStep3 l r).2.echo = r.echo := by
  cases h : r.path4 <;> cases hp : l.path <;> simp only [cleanSigStep3, h, hp] <;>
    simp [fst_ite, snd_ite, echo_ite]

private theorem clean4_echos {ψ : Nat} (l r : AgentState ψ) :
    (cleanSigStep4 l r).1.echo = l.echo ∧
    (cleanSigStep4 l r).2.echo = r.echo := by
  cases h : l.path5 <;> cases hp : r.path <;> simp only [cleanSigStep4, h, hp] <;>
    simp [fst_ite, snd_ite, echo_ite]

private theorem clean5_echos {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep5 hψ l r).1.echo = l.echo ∧
    (cleanSigStep5 hψ l r).2.echo = r.echo := by
  cases h : r.path4 <;> simp only [cleanSigStep5, h] <;>
    simp [fst_ite, snd_ite, echo_ite]

private theorem clean6_echos {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (cleanSigStep6 hψ l r).1.echo = l.echo ∧
    (cleanSigStep6 hψ l r).2.echo = r.echo := by
  cases h : l.path5 <;> simp only [cleanSigStep6, h] <;>
    simp [fst_ite, snd_ite, echo_ite]

private theorem clean_echos {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (cleanSig hψ l r).1.echo = l.echo ∧
    (cleanSig hψ l r).2.echo = r.echo := by
  simp only [cleanSig]
  simp only [cleanSigGenConnect_echo, cleanSigCleanApply_echo,
    (clean3_echos _ _).1, (clean3_echos _ _).2,
    (clean4_echos _ _).1, (clean4_echos _ _).2,
    (clean5_echos _ _ _).1, (clean5_echos _ _ _).2,
    (clean6_echos _ _ _).1, (clean6_echos _ _ _).2, and_self]

private theorem eliminate_echos {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.echo = l.echo ∧
    (eliminateSig hψ l r).2.echo = r.echo := by
  simp only [eliminateSig] <;> simp [fst_ite, snd_ite, echo_ite]

private theorem step1_echos {ψ : Nat} (l r : AgentState ψ) :
    (sigMoveStep1With .dropMisaligned l r).1.echo = l.echo ∧
    (sigMoveStep1With .dropMisaligned l r).2.echo = r.echo := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [sigMoveStep1With, hl, hr] <;> simp [fst_ite, snd_ite, echo_ite]

private theorem moveTokens_echos {ψ : Nat} (l r : AgentState ψ) :
    (moveTokens l r).1.echo = l.echo ∧
    (moveTokens l r).2.echo = r.echo := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [moveTokens, hl, hr] <;> simp [fst_ite, snd_ite, echo_ite]

private theorem control_echo {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (sigMoveApplyControlConsume hψ u).echo = u.echo := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;> simp [fst_ite, snd_ite, echo_ite]

private theorem sig_echos {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (sigMoveF hψ true .dropMisaligned l r).1.echo = l.echo ∧
    (sigMoveF hψ true .dropMisaligned l r).2.echo = r.echo := by
  simp only [sigMoveF]
  simp only [fst_ite, snd_ite, echo_ite, control_echo]
  simp only [leaderWall, clearCmp, fst_ite, snd_ite, echo_ite,
    ite_self, (moveTokens_echos _ _).1, (moveTokens_echos _ _).2,
    (step1_echos _ _).1, (step1_echos _ _).2, and_self]


private theorem drop_echo {ψ : Nat} (u : AgentState ψ) :
    (dropStale u).echo = u.echo := by
  simp only [dropStale]
  simp [echo_ite]

private def stagePrefix {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :=
  let q := pPsiProbeWall hψ l r
  let q := genSigSaturated hψ κ q.1 q.2
  let q := cleanSig hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  let q := sigMoveF hψ true .dropMisaligned q.1 q.2
  (dropStale q.1, dropStale q.2)
private theorem prefix_left_leader {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    (stagePrefix hψ κ l r).1.leader = l.leader := by
  simp only [stagePrefix, drop_leader, (sig_leaders _ _ _).1,
    (eliminate_leaders _ _ _).1, (clean_leaders _ _ _).1, (gen_leaders _ _ _ _).1, pPsi_wall_left]
private theorem prefix_reset_cmd {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    (stagePrefix hψ κ l r).1.reset_cmd = l.reset_cmd := by
  simp only [stagePrefix, drop_reset_cmd, (sig_reset_cmds _ _ _).1,
    (eliminate_reset_cmds _ _ _).1, (clean_reset_cmds _ _ _).1, (gen_reset_cmds _ _ _ _).1]
  simp [pPsiProbeWall, pPsi, fst_ite, snd_ite, reset_cmd_ite]
private theorem prefix_echo {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    (stagePrefix hψ κ l r).2.echo = r.echo := by
  simp only [stagePrefix, drop_echo, (sig_echos _ _ _).2,
    (eliminate_echos _ _ _).2, (clean_echos _ _ _).2, (gen_echos _ _ _ _).2]
  simp [pPsiProbeWall, pPsi, fst_ite, snd_ite, echo_ite]

/-- The five comparison registers erased by an active reset edge. WRITE's own
registers and the suppression command are deliberately excluded. -/
def CmpEmpty {ψ : Nat} (u : AgentState ψ) : Prop :=
  u.state = .none ∧ u.path = .bot ∧ u.path2 = none ∧ u.path4 = none ∧ u.path5 = none
/-! Once pre-CHECK reset clears both endpoints, the comparison stages are identity. -/

private def comparison {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :=
  let q := checkSigF hψ κ false l r
  let q := disappear hψ q.1 q.2
  compareSigF κ false true q.1 q.2
private theorem comparison_clear {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    comparison hψ κ (clearCmp l) (clearCmp r) = (clearCmp l, clearCmp r) := by
  simp [comparison, checkSigF, readyF, checkSigSetReadyGuarded, controlPending,
    checkSigSetReady, checkSigCheckL, checkSigCheckR, checkSigSetResult,
    disappear, compareSigF, compareSigInit, maintain, wave, dropStray,
    landBackward, landForward, clearCmp, waveState, lockedState]

private theorem state_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).state = if p then a.state else b.state := by split <;> rfl
private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by split <;> rfl
private theorem path2_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path2 = if p then a.path2 else b.path2 := by split <;> rfl
private theorem path4_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path4 = if p then a.path4 else b.path4 := by split <;> rfl
private theorem path5_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path5 = if p then a.path5 else b.path5 := by split <;> rfl
/-! K4 and WRITE preserve comparison and reset registers, including arbitrary WRITE debris.
The two frame groups keep the proof terms small without altering pipeline order. -/

private def FrameA {ψ : Nat} (a b : AgentState ψ) : Prop :=
  a.state = b.state ∧ a.path = b.path ∧ a.reset_cmd = b.reset_cmd
private theorem writeActionApplyOverwrite_frameA {ψ : Nat} (u : AgentState ψ) :
    FrameA (writeActionApplyOverwrite u) u := by
  unfold FrameA writeActionApplyOverwrite
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeActionApplyMoveFlip_frameA {ψ : Nat} (u : AgentState ψ) :
    FrameA (writeActionApplyMoveFlip u) u := by
  unfold FrameA writeActionApplyMoveFlip
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem moveWsigCheckLast_frameA {ψ : Nat} (u : AgentState ψ) :
    FrameA (moveWsigCheckLast u) u := by
  unfold FrameA moveWsigCheckLast
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeSeqSetWriteReady_frameA {ψ : Nat} (u : AgentState ψ) :
    FrameA (writeSeqSetWriteReady u) u := by
  unfold FrameA writeSeqSetWriteReady
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeSeqCheckBit_frameA {ψ : Nat} (u : AgentState ψ) :
    FrameA (writeSeqCheckBit u) u := by
  unfold FrameA writeSeqCheckBit
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeSeqSetWriteAct_frameA {ψ : Nat} (u : AgentState ψ) :
    FrameA (writeSeqSetWriteAct u) u := by
  cases hp : u.path3 <;> simp only [FrameA, writeSeqSetWriteAct, hp] <;>
    simp [state_ite, path_ite, reset_cmd_ite, hp]

private theorem writeSeqFinalR_frameA {ψ : Nat} (u : AgentState ψ) :
    FrameA (writeSeqFinalR u) u := by
  unfold FrameA writeSeqFinalR
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem moveWsigCheckGenWs_frameA {ψ : Nat} (l r : AgentState ψ) :
    FrameA (moveWsigCheckGenWs l r) r := by
  unfold FrameA moveWsigCheckGenWs
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem moveWsigTransfer_frameA {ψ : Nat} (l r : AgentState ψ) :
    FrameA (moveWsigTransfer l r).1 l ∧ FrameA (moveWsigTransfer l r).2 r := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp only [FrameA, moveWsigTransfer, hl, hr] <;>
    simp only [fst_ite, snd_ite, state_ite, path_ite, reset_cmd_ite, ite_self, and_self]

private theorem groupInfo_frameA {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    FrameA (groupInfo hψ l r).1 l ∧ FrameA (groupInfo hψ l r).2 r := by
  simp only [FrameA, groupInfo]
  simp only [fst_ite, snd_ite, state_ite, path_ite, reset_cmd_ite, ite_self, and_self]

private theorem gensigWriteseq_frameA {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    FrameA (gensigWriteseq hψ l r).1 l ∧ FrameA (gensigWriteseq hψ l r).2 r := by
  simp only [FrameA, gensigWriteseq]
  simp only [fst_ite, snd_ite, state_ite, path_ite, reset_cmd_ite, ite_self, and_self]

private theorem writeAction_frameA {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    FrameA (writeAction hψ l r).1 l ∧ FrameA (writeAction hψ l r).2 r := by
  simp only [FrameA, writeAction]
  simp only [fst_ite, snd_ite, state_ite, path_ite, reset_cmd_ite, ite_self, and_self , (writeActionApplyOverwrite_frameA _).1, (writeActionApplyOverwrite_frameA _).2.1, (writeActionApplyOverwrite_frameA _).2.2, (writeActionApplyMoveFlip_frameA _).1, (writeActionApplyMoveFlip_frameA _).2.1, (writeActionApplyMoveFlip_frameA _).2.2]

private theorem moveWsig_frameA {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    FrameA (moveWsig hψ l r).1 l ∧ FrameA (moveWsig hψ l r).2 r := by
  simp only [FrameA, moveWsig]
  simp only [fst_ite, snd_ite, state_ite, path_ite, reset_cmd_ite, ite_self, and_self , (moveWsigCheckGenWs_frameA _ _).1, (moveWsigCheckGenWs_frameA _ _).2.1, (moveWsigCheckGenWs_frameA _ _).2.2, (moveWsigCheckLast_frameA _).1, (moveWsigCheckLast_frameA _).2.1, (moveWsigCheckLast_frameA _).2.2, (moveWsigTransfer_frameA _ _).1.1, (moveWsigTransfer_frameA _ _).1.2.1, (moveWsigTransfer_frameA _ _).1.2.2, (moveWsigTransfer_frameA _ _).2.1, (moveWsigTransfer_frameA _ _).2.2.1, (moveWsigTransfer_frameA _ _).2.2.2]

private theorem writeSeq_frameA {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    FrameA (writeSeq hψ l r).1 l ∧ FrameA (writeSeq hψ l r).2 r := by
  simp only [FrameA, writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands]
  simp only [fst_ite, snd_ite, state_ite, path_ite, reset_cmd_ite, ite_self, and_self, (groupInfo_frameA _ _ _).1.1, (groupInfo_frameA _ _ _).1.2.1, (groupInfo_frameA _ _ _).1.2.2, (groupInfo_frameA _ _ _).2.1, (groupInfo_frameA _ _ _).2.2.1, (groupInfo_frameA _ _ _).2.2.2, (gensigWriteseq_frameA _ _ _).1.1, (gensigWriteseq_frameA _ _ _).1.2.1, (gensigWriteseq_frameA _ _ _).1.2.2, (gensigWriteseq_frameA _ _ _).2.1, (gensigWriteseq_frameA _ _ _).2.2.1, (gensigWriteseq_frameA _ _ _).2.2.2, (writeAction_frameA _ _ _).1.1, (writeAction_frameA _ _ _).1.2.1, (writeAction_frameA _ _ _).1.2.2, (writeAction_frameA _ _ _).2.1, (writeAction_frameA _ _ _).2.2.1, (writeAction_frameA _ _ _).2.2.2, (moveWsig_frameA _ _ _).1.1, (moveWsig_frameA _ _ _).1.2.1, (moveWsig_frameA _ _ _).1.2.2, (moveWsig_frameA _ _ _).2.1, (moveWsig_frameA _ _ _).2.2.1, (moveWsig_frameA _ _ _).2.2.2, (writeSeqSetWriteReady_frameA _).1, (writeSeqSetWriteReady_frameA _).2.1, (writeSeqSetWriteReady_frameA _).2.2, (writeSeqCheckBit_frameA _).1, (writeSeqCheckBit_frameA _).2.1, (writeSeqCheckBit_frameA _).2.2, (writeSeqSetWriteAct_frameA _).1, (writeSeqSetWriteAct_frameA _).2.1, (writeSeqSetWriteAct_frameA _).2.2, (writeSeqFinalR_frameA _).1, (writeSeqFinalR_frameA _).2.1, (writeSeqFinalR_frameA _).2.2]

private theorem kernel_frameA {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    FrameA (k4Kernel hψ l r).1 l ∧ FrameA (k4Kernel hψ l r).2 r := by
  simp only [FrameA, k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire,
    absorbAnyMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp only [fst_ite, snd_ite, state_ite, path_ite, reset_cmd_ite, ite_self, and_self]
private theorem write_frameA {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    FrameA (writeWithBundle hψ l r).1 l ∧ FrameA (writeWithBundle hψ l r).2 r := by
  simp only [FrameA, writeWithBundle, fst_ite, snd_ite, state_ite, path_ite, reset_cmd_ite,
    (writeSeq_frameA _ _ _).1.1, (writeSeq_frameA _ _ _).1.2.1, (writeSeq_frameA _ _ _).1.2.2, (writeSeq_frameA _ _ _).2.1, (writeSeq_frameA _ _ _).2.2.1, (writeSeq_frameA _ _ _).2.2.2, ite_self, and_self]
private def FrameB {ψ : Nat} (a b : AgentState ψ) : Prop :=
  a.path2 = b.path2 ∧ a.path4 = b.path4 ∧ a.path5 = b.path5
private theorem writeActionApplyOverwrite_frameB {ψ : Nat} (u : AgentState ψ) :
    FrameB (writeActionApplyOverwrite u) u := by
  unfold FrameB writeActionApplyOverwrite
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeActionApplyMoveFlip_frameB {ψ : Nat} (u : AgentState ψ) :
    FrameB (writeActionApplyMoveFlip u) u := by
  unfold FrameB writeActionApplyMoveFlip
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem moveWsigCheckLast_frameB {ψ : Nat} (u : AgentState ψ) :
    FrameB (moveWsigCheckLast u) u := by
  unfold FrameB moveWsigCheckLast
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeSeqSetWriteReady_frameB {ψ : Nat} (u : AgentState ψ) :
    FrameB (writeSeqSetWriteReady u) u := by
  unfold FrameB writeSeqSetWriteReady
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeSeqCheckBit_frameB {ψ : Nat} (u : AgentState ψ) :
    FrameB (writeSeqCheckBit u) u := by
  unfold FrameB writeSeqCheckBit
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeSeqSetWriteAct_frameB {ψ : Nat} (u : AgentState ψ) :
    FrameB (writeSeqSetWriteAct u) u := by
  cases hp : u.path3 <;> simp only [FrameB, writeSeqSetWriteAct, hp] <;>
    simp [path2_ite, path4_ite, path5_ite, hp]

private theorem writeSeqFinalR_frameB {ψ : Nat} (u : AgentState ψ) :
    FrameB (writeSeqFinalR u) u := by
  unfold FrameB writeSeqFinalR
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem moveWsigCheckGenWs_frameB {ψ : Nat} (l r : AgentState ψ) :
    FrameB (moveWsigCheckGenWs l r) r := by
  unfold FrameB moveWsigCheckGenWs
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem moveWsigTransfer_frameB {ψ : Nat} (l r : AgentState ψ) :
    FrameB (moveWsigTransfer l r).1 l ∧ FrameB (moveWsigTransfer l r).2 r := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp only [FrameB, moveWsigTransfer, hl, hr] <;>
    simp only [fst_ite, snd_ite, path2_ite, path4_ite, path5_ite, ite_self, and_self]

private theorem groupInfo_frameB {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    FrameB (groupInfo hψ l r).1 l ∧ FrameB (groupInfo hψ l r).2 r := by
  simp only [FrameB, groupInfo]
  simp only [fst_ite, snd_ite, path2_ite, path4_ite, path5_ite, ite_self, and_self]

private theorem gensigWriteseq_frameB {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    FrameB (gensigWriteseq hψ l r).1 l ∧ FrameB (gensigWriteseq hψ l r).2 r := by
  simp only [FrameB, gensigWriteseq]
  simp only [fst_ite, snd_ite, path2_ite, path4_ite, path5_ite, ite_self, and_self]

private theorem writeAction_frameB {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    FrameB (writeAction hψ l r).1 l ∧ FrameB (writeAction hψ l r).2 r := by
  simp only [FrameB, writeAction]
  simp only [fst_ite, snd_ite, path2_ite, path4_ite, path5_ite, ite_self, and_self , (writeActionApplyOverwrite_frameB _).1, (writeActionApplyOverwrite_frameB _).2.1, (writeActionApplyOverwrite_frameB _).2.2, (writeActionApplyMoveFlip_frameB _).1, (writeActionApplyMoveFlip_frameB _).2.1, (writeActionApplyMoveFlip_frameB _).2.2]

private theorem moveWsig_frameB {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    FrameB (moveWsig hψ l r).1 l ∧ FrameB (moveWsig hψ l r).2 r := by
  simp only [FrameB, moveWsig]
  simp only [fst_ite, snd_ite, path2_ite, path4_ite, path5_ite, ite_self, and_self , (moveWsigCheckGenWs_frameB _ _).1, (moveWsigCheckGenWs_frameB _ _).2.1, (moveWsigCheckGenWs_frameB _ _).2.2, (moveWsigCheckLast_frameB _).1, (moveWsigCheckLast_frameB _).2.1, (moveWsigCheckLast_frameB _).2.2, (moveWsigTransfer_frameB _ _).1.1, (moveWsigTransfer_frameB _ _).1.2.1, (moveWsigTransfer_frameB _ _).1.2.2, (moveWsigTransfer_frameB _ _).2.1, (moveWsigTransfer_frameB _ _).2.2.1, (moveWsigTransfer_frameB _ _).2.2.2]

private theorem writeSeq_frameB {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    FrameB (writeSeq hψ l r).1 l ∧ FrameB (writeSeq hψ l r).2 r := by
  simp only [FrameB, writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands]
  simp only [fst_ite, snd_ite, path2_ite, path4_ite, path5_ite, ite_self, and_self, (groupInfo_frameB _ _ _).1.1, (groupInfo_frameB _ _ _).1.2.1, (groupInfo_frameB _ _ _).1.2.2, (groupInfo_frameB _ _ _).2.1, (groupInfo_frameB _ _ _).2.2.1, (groupInfo_frameB _ _ _).2.2.2, (gensigWriteseq_frameB _ _ _).1.1, (gensigWriteseq_frameB _ _ _).1.2.1, (gensigWriteseq_frameB _ _ _).1.2.2, (gensigWriteseq_frameB _ _ _).2.1, (gensigWriteseq_frameB _ _ _).2.2.1, (gensigWriteseq_frameB _ _ _).2.2.2, (writeAction_frameB _ _ _).1.1, (writeAction_frameB _ _ _).1.2.1, (writeAction_frameB _ _ _).1.2.2, (writeAction_frameB _ _ _).2.1, (writeAction_frameB _ _ _).2.2.1, (writeAction_frameB _ _ _).2.2.2, (moveWsig_frameB _ _ _).1.1, (moveWsig_frameB _ _ _).1.2.1, (moveWsig_frameB _ _ _).1.2.2, (moveWsig_frameB _ _ _).2.1, (moveWsig_frameB _ _ _).2.2.1, (moveWsig_frameB _ _ _).2.2.2, (writeSeqSetWriteReady_frameB _).1, (writeSeqSetWriteReady_frameB _).2.1, (writeSeqSetWriteReady_frameB _).2.2, (writeSeqCheckBit_frameB _).1, (writeSeqCheckBit_frameB _).2.1, (writeSeqCheckBit_frameB _).2.2, (writeSeqSetWriteAct_frameB _).1, (writeSeqSetWriteAct_frameB _).2.1, (writeSeqSetWriteAct_frameB _).2.2, (writeSeqFinalR_frameB _).1, (writeSeqFinalR_frameB _).2.1, (writeSeqFinalR_frameB _).2.2]

private theorem kernel_frameB {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    FrameB (k4Kernel hψ l r).1 l ∧ FrameB (k4Kernel hψ l r).2 r := by
  simp only [FrameB, k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire,
    absorbAnyMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp only [fst_ite, snd_ite, path2_ite, path4_ite, path5_ite, ite_self, and_self]
private theorem write_frameB {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    FrameB (writeWithBundle hψ l r).1 l ∧ FrameB (writeWithBundle hψ l r).2 r := by
  simp only [FrameB, writeWithBundle, fst_ite, snd_ite, path2_ite, path4_ite, path5_ite,
    (writeSeq_frameB _ _ _).1.1, (writeSeq_frameB _ _ _).1.2.1, (writeSeq_frameB _ _ _).1.2.2, (writeSeq_frameB _ _ _).2.1, (writeSeq_frameB _ _ _).2.2.1, (writeSeq_frameB _ _ _).2.2.2, ite_self, and_self]

/-! Suppression preserves comparison emptiness and delivers an uncanceled reset. -/

private theorem suppress_empty {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : CmpEmpty l) (hr : CmpEmpty r) :
    CmpEmpty (suppressSigResetKill hψ l r).1 ∧ CmpEmpty (suppressSigResetKill hψ l r).2 := by
  rcases hl with ⟨hl1,hl2,hl3,hl4,hl5⟩
  rcases hr with ⟨hr1,hr2,hr3,hr4,hr5⟩
  cases h1 : l.leader <;> cases h2 : l.reset_cmd <;>
    cases h3 : r.reset_cmd <;> cases h4 : r.echo <;>
    simp [CmpEmpty, suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
      suppressSigTerminal, suppressSigEcho, suppressSigFinish, clearCmp,
      h1,h2,h3,h4, fst_ite, snd_ite, state_ite, path_ite, path2_ite, path4_ite, path5_ite,
      hl1,hl2,hl3,hl4,hl5,hr1,hr2,hr3,hr4,hr5]
private theorem suppress_reset {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (h : l.leader = true ∨ l.reset_cmd = true) (he : r.echo = false) :
    (suppressSigResetKill hψ l r).2.reset_cmd = true := by
  rcases h with h | h <;>
    simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
      suppressSigTerminal, suppressSigEcho, suppressSigFinish, clearCmp,
      h, he, fst_ite, snd_ite, reset_cmd_ite, echo_ite]


private theorem prefix_active {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ)
    (h : l.leader = true ∨ l.reset_cmd = true) :
    (stagePrefix hψ κ l r).1.leader = true ∨ (stagePrefix hψ κ l r).1.reset_cmd = true := by
  rwa [prefix_left_leader, prefix_reset_cmd]

private theorem precheck_active {ψ : Nat} (l r : AgentState ψ)
    (h : l.leader = true ∨ l.reset_cmd = true) :
    preCheckReset l r = (clearCmp l, clearCmp r) := by
  rcases h with h | h <;> simp [preCheckReset, h]

private theorem active_cut {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ)
    (h : l.leader = true ∨ l.reset_cmd = true) :
    beforeElimination hψ κ l r =
      suppressSigResetKill hψ (clearCmp (stagePrefix hψ κ l r).1) (clearCmp (stagePrefix hψ κ l r).2) := by
  have heq : beforeElimination hψ κ l r =
      suppressSigResetKill hψ
        (comparison hψ κ (preCheckReset (stagePrefix hψ κ l r).1 (stagePrefix hψ κ l r).2).1
          (preCheckReset (stagePrefix hψ κ l r).1 (stagePrefix hψ κ l r).2).2).1
        (comparison hψ κ (preCheckReset (stagePrefix hψ κ l r).1 (stagePrefix hψ κ l r).2).1
          (preCheckReset (stagePrefix hψ κ l r).1 (stagePrefix hψ κ l r).2).2).2 := rfl
  rw [heq]
  simp only [precheck_active (stagePrefix hψ κ l r).1 (stagePrefix hψ κ l r).2
    (prefix_active hψ κ l r h), comparison_clear]

private theorem before_empty {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ)
    (h : l.leader = true ∨ l.reset_cmd = true) :
    CmpEmpty (beforeElimination hψ κ l r).1 ∧ CmpEmpty (beforeElimination hψ κ l r).2 := by
  rw [active_cut hψ κ l r h]
  exact suppress_empty hψ (clearCmp (stagePrefix hψ κ l r).1) (clearCmp (stagePrefix hψ κ l r).2)
    (by simp [CmpEmpty, clearCmp]) (by simp [CmpEmpty, clearCmp])

private theorem clear_leader {ψ : Nat} (u : AgentState ψ) :
    (clearCmp u).leader = u.leader := rfl
private theorem clear_reset {ψ : Nat} (u : AgentState ψ) :
    (clearCmp u).reset_cmd = u.reset_cmd := rfl
private theorem clear_echo {ψ : Nat} (u : AgentState ψ) :
    (clearCmp u).echo = u.echo := rfl
private theorem before_reset {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ)
    (h : l.leader = true ∨ l.reset_cmd = true) (he : r.echo = false) :
    (beforeElimination hψ κ l r).2.reset_cmd = true := by
  rw [active_cut hψ κ l r h]
  exact suppress_reset hψ (clearCmp (stagePrefix hψ κ l r).1)
    (clearCmp (stagePrefix hψ κ l r).2)
    (by simpa only [clear_leader, clear_reset] using prefix_active hψ κ l r h)
    (by simpa only [clear_echo, prefix_echo] using he)

private theorem kernel_empty {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : CmpEmpty l) (hr : CmpEmpty r) :
    CmpEmpty (k4Kernel hψ l r).1 ∧ CmpEmpty (k4Kernel hψ l r).2 := by
  simpa only [CmpEmpty, (kernel_frameA _ _ _).1.1, (kernel_frameA _ _ _).1.2.1,
    (kernel_frameA _ _ _).2.1, (kernel_frameA _ _ _).2.2.1,
    (kernel_frameB _ _ _).1.1, (kernel_frameB _ _ _).1.2.1, (kernel_frameB _ _ _).1.2.2,
    (kernel_frameB _ _ _).2.1, (kernel_frameB _ _ _).2.2.1, (kernel_frameB _ _ _).2.2.2] using And.intro hl hr
private theorem write_empty {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : CmpEmpty l) (hr : CmpEmpty r) :
    CmpEmpty (writeWithBundle hψ l r).1 ∧ CmpEmpty (writeWithBundle hψ l r).2 := by
  simpa only [CmpEmpty, (write_frameA _ _ _).1.1, (write_frameA _ _ _).1.2.1,
    (write_frameA _ _ _).2.1, (write_frameA _ _ _).2.2.1,
    (write_frameB _ _ _).1.1, (write_frameB _ _ _).1.2.1, (write_frameB _ _ _).1.2.2,
    (write_frameB _ _ _).2.1, (write_frameB _ _ _).2.2.1, (write_frameB _ _ _).2.2.2] using And.intro hl hr
private theorem conserve_empty {ψ : Nat} (l r : AgentState ψ) (q : AgentState ψ × AgentState ψ)
    (h : CmpEmpty q.1 ∧ CmpEmpty q.2) :
    CmpEmpty (conserve .head l r q).1 ∧ CmpEmpty (conserve .head l r q).2 := by
  unfold conserve
  split
  · simpa [CmpEmpty, replacement, clearCmp] using h.1
  · exact h
private theorem conserve_reset {ψ : Nat} (l r : AgentState ψ) (q : AgentState ψ × AgentState ψ) :
    (conserve .head l r q).2.reset_cmd = q.2.reset_cmd := by
  simp [conserve, replacement, clearCmp, snd_ite, reset_cmd_ite]

/-- An initiating leader or reset command clears all five comparison registers
at both endpoints of the complete Head interaction. Earlier arbitrary comparison
material is erased at pre-CHECK reset; K4 and WRITE frame the resulting fields. -/
theorem pipeline_active_source_cmp_empty {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) (h : l.leader = true ∨ l.reset_cmd = true) :
    CmpEmpty (PPLLAstraDesign2.pipeline hψ κ .head l r).1 ∧
    CmpEmpty (PPLLAstraDesign2.pipeline hψ κ .head l r).2 := by
  have hb := before_empty hψ κ l r h
  let q := beforeElimination hψ κ l r
  let k := k4Kernel hψ q.1 q.2
  have hk := kernel_empty hψ q.1 q.2 hb.1 hb.2
  have hw := write_empty hψ k.1 k.2 hk.1 hk.2
  exact conserve_empty l r (writeWithBundle hψ k.1 k.2) hw

/-- An active initiator delivers a responder reset command provided the input
responder has no echo to cancel it. All other input fields are arbitrary. The
complete step also consumes responder echo, by the independent responder lemma. -/
theorem pipeline_active_source_reset {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) (h : l.leader = true ∨ l.reset_cmd = true)
    (he : r.echo = false) :
    (PPLLAstraDesign2.pipeline hψ κ .head l r).2.reset_cmd = true ∧
    (PPLLAstraDesign2.pipeline hψ κ .head l r).2.echo = false := by
  constructor
  · simpa only [PPLLAstraDesign2.pipeline, conserve_reset,
      (write_frameA _ _ _).2.2.2, (kernel_frameA _ _ _).2.2.2]
      using before_reset hψ κ l r h he
  · exact PPLLAstraResponder.pipeline_responder_echo_false hψ κ l r

/-- Exact active-source cut for consumers that need fields beyond comparison
emptiness. The explicit prefix is the actual pre-CHECK pipeline; the comparison
suffix becomes identity on the two cleared agents. This additive interface
exposes no private helper or extra premise. -/
theorem beforeElimination_active_cut {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) (h : l.leader = true ∨ l.reset_cmd = true) :
    beforeElimination hψ κ l r =
      (let q := pPsiProbeWall hψ l r
       let q := genSigSaturated hψ κ q.1 q.2
       let q := cleanSig hψ q.1 q.2
       let q := eliminateSig hψ q.1 q.2
       let q := sigMoveF hψ true .dropMisaligned q.1 q.2
       let q := (dropStale q.1, dropStale q.2)
       suppressSigResetKill hψ (clearCmp q.1) (clearCmp q.2)) := by
  exact active_cut hψ κ l r h

#print axioms beforeElimination_active_cut
#check @beforeElimination_active_cut
#print axioms pipeline_active_source_cmp_empty
#print axioms pipeline_active_source_reset
#check @pipeline_active_source_cmp_empty
#check @pipeline_active_source_reset
end PPLLAstraReset
