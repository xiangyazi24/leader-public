import Leader.Wu.ZeroDivisible.HeadShieldAnchor

/-! Incoming WRITE normalization for the frozen Head pipeline, with arbitrary
ancillary fields. This local result does not assert global convergence. -/
namespace PPLLAstraIncoming
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
  PPLLFableDesignR1 PPLLAstraDesign2
namespace LeaderFrame
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

private theorem clean_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (cleanSig hψ l r).1.leader = l.leader ∧
    (cleanSig hψ l r).2.leader = r.leader := by
  exact PPLLVerify.cleanSig_leaders_eq hψ l r

private theorem eliminate_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.leader = l.leader ∧
    (eliminateSig hψ l r).2.leader = r.leader := by
  exact PPLLVerify.eliminateSig_leaders_eq hψ l r

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

private theorem result_leader {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetResult u).leader = u.leader := by
  simp only [checkSigSetResult]
  simp [leader_ite]

private theorem disappear_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (disappear hψ l r).1.leader = l.leader ∧
    (disappear hψ l r).2.leader = r.leader := by
  exact PPLLVerify.disappear_leaders_eq hψ l r

private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by
  split <;> rfl

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

private theorem maintain_right {ψ : Nat} (l r : AgentState ψ) :
    (maintain l r).2.leader = r.leader := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [maintain, hl, hr] <;>
    simp [leader_ite, path_ite, hl, hr]

private theorem wave_right {ψ : Nat} (l r : AgentState ψ) :
    (wave l r).2.leader = r.leader := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [wave, hl, hr] <;> simp [leader_ite]

private theorem stray_right {ψ : Nat} (l r : AgentState ψ) :
    (dropStray l r).2.leader = r.leader := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [dropStray, hl, hr] <;> simp [leader_ite]

private theorem checkR_leader {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).leader = r.leader := by
  unfold checkSigCheckR
  split <;> simp [leader_ite]
private theorem check_right {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) (hr : r.leader = true) :
    (checkSigF hψ κ false l r).2.leader = true := by
  simp only [checkSigF, snd_ite, leader_ite, result_leader,
    checkR_leader, ready_leader]
  simp [hr, leader_ite]
private theorem forward_true {ψ : Nat} (κ : Nat) (u : AgentState ψ)
    (hu : u.leader = true) : (landForward κ false true u).leader = true := by
  cases ht : u.path2 <;> cases hp : u.path <;>
    simp only [landForward, ht, hp] <;> simp [leader_ite, hu]
private theorem compare_right {ψ : Nat} (κ : Nat) (l r : AgentState ψ)
    (hr : r.leader = true) : (compareSigF κ false true l r).2.leader = true := by
  simp only [compareSigF]
  apply forward_true
  simp only [stray_right, wave_right, maintain_right, hr]
theorem before_right {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) (hr : r.leader = true) :
    (beforeElimination hψ κ l r).2.leader = true := by
  simp only [beforeElimination, (suppress_leaders _ _ _).2]
  apply compare_right
  simp only [(disappear_leaders _ _ _).2]
  apply check_right
  simp only [(reset_leaders _ _).2, drop_leader, (sig_leaders _ _ _).2,
    (eliminate_leaders _ _ _).2, (clean_leaders _ _ _).2, (gen_leaders _ _ _ _).2]
  exact (pPsi_wall_leaders hψ l r (Or.inr hr)).2.trans hr
end LeaderFrame

namespace LabelFrame

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

private theorem clean_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (cleanSig hψ l r).1.label = l.label ∧
    (cleanSig hψ l r).2.label = r.label := by
  exact PPLLVerify.cleanSig_labels_eq hψ l r

private theorem eliminate_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.label = l.label ∧
    (eliminateSig hψ l r).2.label = r.label := by
  exact PPLLVerify.eliminateSig_labels_eq hψ l r

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

private theorem result_leader {ψ : Nat} (u : AgentState ψ) :
    (checkSigSetResult u).label = u.label := by
  simp only [checkSigSetResult]
  simp [leader_ite]

private theorem disappear_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (disappear hψ l r).1.label = l.label ∧
    (disappear hψ l r).2.label = r.label := by
  exact PPLLVerify.disappear_labels_eq hψ l r

private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by
  split <;> rfl

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

private theorem maintain_right {ψ : Nat} (l r : AgentState ψ) :
    (maintain l r).2.label = r.label := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [maintain, hl, hr] <;>
    simp [leader_ite, path_ite, hl, hr]

private theorem wave_right {ψ : Nat} (l r : AgentState ψ) :
    (wave l r).2.label = r.label := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [wave, hl, hr] <;> simp [leader_ite]

private theorem stray_right {ψ : Nat} (l r : AgentState ψ) :
    (dropStray l r).2.label = r.label := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [dropStray, hl, hr] <;> simp [leader_ite]

private theorem pPsi_right {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hr : r.leader = true) : (pPsiProbeWall hψ l r).2.label = r.label := by
  simp only [pPsiProbeWall, pPsi, hr]
  simp [fst_ite, snd_ite, leader_ite]
private theorem checkR_label {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).label = r.label := by
  unfold checkSigCheckR
  split <;> simp [leader_ite]
private theorem check_right {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    (checkSigF hψ κ false l r).2.label = r.label := by
  simp only [checkSigF, snd_ite, leader_ite, result_leader, checkR_label, ready_leader, ite_self]
  simp [clearCmp, leader_ite]
private theorem forward_label {ψ : Nat} (κ : Nat) (u : AgentState ψ) :
    (landForward κ false true u).label = u.label := by
  cases ht : u.path2 <;> cases hp : u.path <;>
    simp only [landForward, ht, hp] <;> simp [leader_ite]
private theorem compare_right {ψ : Nat} (κ : Nat) (l r : AgentState ψ) :
    (compareSigF κ false true l r).2.label = r.label := by
  simp only [compareSigF, forward_label, stray_right, wave_right, maintain_right]
theorem before_right {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ)
    (hr : r.leader = true) : (beforeElimination hψ κ l r).2.label = r.label := by
  simp only [beforeElimination, (suppress_leaders _ _ _).2, compare_right,
    (disappear_leaders _ _ _).2, check_right, (reset_leaders _ _).2,
    drop_leader, (sig_leaders _ _ _).2, (eliminate_leaders _ _ _).2,
    (clean_leaders _ _ _).2, (gen_leaders _ _ _ _).2, pPsi_right _ _ _ hr]
end LabelFrame

private theorem kernel_right {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (k4Kernel hψ l r).2.leader = r.leader ∧
    (k4Kernel hψ l r).2.label = r.label ∧
    (k4Kernel hψ l r).1.label = l.label := by
  simp only [k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire,
    absorbAnyMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp [LeaderFrame.fst_ite, LeaderFrame.snd_ite, LeaderFrame.leader_ite,
    LabelFrame.leader_ite]

attribute [local irreducible] beforeElimination k4Kernel writeSeq
/-- Every nonzero-label responder leader transfers or merges into the
initiator during the complete Head step. K4 may kill the old initiator, but
cannot kill the responder before WRITE performs this transfer. -/
theorem pipeline_incoming {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) (hr : r.leader = true) (hn : r.label.val ≠ 0) :
    (PPLLAstraDesign2.pipeline hψ κ .head l r).1.leader = true ∧
    (PPLLAstraDesign2.pipeline hψ κ .head l r).2.leader = false ∧
    (PPLLAstraDesign2.pipeline hψ κ .head l r).1.label = l.label := by
  simp only [PPLLAstraDesign2.pipeline]
  generalize hq : beforeElimination hψ κ l r = q
  have qr : q.2.leader = true := by rw [← hq]; exact LeaderFrame.before_right hψ κ l r hr
  have qlabel : q.2.label = r.label := by rw [← hq]; exact LabelFrame.before_right hψ κ l r hr
  have qleft : q.1.label = l.label := by rw [← hq]; exact PPLLAstraShieldAnchor.Frame_label.before_left hψ κ l r
  have hk := kernel_right hψ q.1 q.2
  generalize hkdef : k4Kernel hψ q.1 q.2 = k at *
  have kr : k.2.leader = true := hk.1.trans qr
  have kn : k.2.label ≠ ⟨0, hψ⟩ := by
    intro hz
    apply hn
    have heq := (hk.2.1.trans qlabel).symm.trans hz
    exact congrArg Fin.val heq
  have wl := PPLLVerify.writeSeq_initiator_true_of_nonzero_responder_leader hψ k.1 k.2 ⟨kr, kn⟩
  have wr := PPLLVerify.writeSeq_responder_false_of_nonzero_leader hψ k.1 k.2 ⟨kr, kn⟩
  have wlabel := (PPLLVerify.writeSeq_l_label hψ k.1 k.2).trans (hk.2.2.trans qleft)
  unfold writeWithBundle
  split <;> simp [conserve, wl, wr, wlabel]
#print axioms pipeline_incoming
#check @pipeline_incoming
end PPLLAstraIncoming
