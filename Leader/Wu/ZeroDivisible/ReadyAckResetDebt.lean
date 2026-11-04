import Leader.Wu.ZeroDivisible.ReadyAckThreeAgent
/-! Restatement of the ReadyAck reset-debt frames.

The frame sections `Fields`, `Left` and `Writer` are copied here verbatim from
the earlier reset-debt development. The `prefix_identity` `rfl` identity is
replaced by `simp only` normalisation of the constant design guards, and the frames are exported as public equations. The Algorithm 14
lemmas are re-proved stage by stage in `PPLLAstraReadyResetDrain`. -/
namespace PPLLAstraReadyResetDebtR
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3
set_option linter.unusedSimpArgs false
/-- Exact ReadyAck beforeSuppress ending just before signal suppression. -/
def beforeSuppress {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := pPsiProbeWall hp l r
  let q := genSigSaturated hp κ q.1 q.2
  let q := cleanSource hp q.1 q.2
  let q := releaseSource hp q.1 q.2
  let q := eliminateSig hp q.1 q.2
  let q := moveSource hp q.1 q.2
  let q := (dropStale q.1, dropStale q.2)
  let q := preCheckReset q.1 q.2
  let q := (normalizeReady q.1, normalizeReady q.2)
  let q := checkSource hp q.1 q.2
  let q := disappear hp q.1 q.2
  let q := repair .readyAck q.1 q.2
  compareLifecycle κ q.1 q.2
namespace Fields
private def view {ψ : Nat} (u : AgentState ψ) := (u.reset_cmd,u.echo)
private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem reset_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).reset_cmd = if p then a.reset_cmd else b.reset_cmd := by split <;> rfl
private theorem label_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).label = if p then a.label else b.label := by split <;> rfl
private theorem echo_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).echo = if p then a.echo else b.echo := by split <;> rfl
private theorem view_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (view (if p then a else b)) = if p then (view a) else (view b) := by split <;> rfl
private theorem gen_views {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (view (genSigSaturated hψ κ l r).1) = (view l) ∧
    (view (genSigSaturated hψ κ l r).2) = (view r) := by
  simp only [genSigSaturated, genSigSaturatedAfterWait, genSigSaturatedStart,
    genSigSaturatedEmit, genSigSaturatedPropagate, genSigSaturatedFinish,
    waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish] <;> simp only [fst_ite, snd_ite, view_ite, view,  reset_ite, label_ite, echo_ite, ite_self, and_self]

private theorem cleanSigGenConnect_view {ψ : Nat} (u : AgentState ψ) :
    (view (cleanSigGenConnect u)) = (view u) := by
  cases h : u.path <;>
    simp only [cleanSigGenConnect, h] <;>
    simp [fst_ite, snd_ite, view_ite, view,  reset_ite, label_ite, echo_ite]

private theorem cleanSigCleanApply_view {ψ : Nat} (u : AgentState ψ) :
    (view (cleanSigCleanApply u)) = (view u) := by
  cases h : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp only [cleanSigCleanApply, h, h4, h5] <;>
    (repeat split) <;> simp_all [view_ite, view,  reset_ite, label_ite, echo_ite]

private theorem clean3_views {ψ : Nat} (l r : AgentState ψ) :
    (view (cleanSigStep3 l r).1) = (view l) ∧
    (view (cleanSigStep3 l r).2) = (view r) := by
  cases h : r.path4 <;> cases hp : l.path <;> simp only [cleanSigStep3, h, hp] <;>
    simp [fst_ite, snd_ite, view_ite, view,  reset_ite, label_ite, echo_ite]

private theorem clean4_views {ψ : Nat} (l r : AgentState ψ) :
    (view (cleanSigStep4 l r).1) = (view l) ∧
    (view (cleanSigStep4 l r).2) = (view r) := by
  cases h : l.path5 <;> cases hp : r.path <;> simp only [cleanSigStep4, h, hp] <;>
    simp [fst_ite, snd_ite, view_ite, view,  reset_ite, label_ite, echo_ite]

private theorem clean5_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (cleanSigStep5 hψ l r).1) = (view l) ∧
    (view (cleanSigStep5 hψ l r).2) = (view r) := by
  cases h : r.path4 <;> simp only [cleanSigStep5, h] <;>
    simp [fst_ite, snd_ite, view_ite, view,  reset_ite, label_ite, echo_ite]

private theorem clean6_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (cleanSigStep6 hψ l r).1) = (view l) ∧
    (view (cleanSigStep6 hψ l r).2) = (view r) := by
  cases h : l.path5 <;> simp only [cleanSigStep6, h] <;>
    simp [fst_ite, snd_ite, view_ite, view,  reset_ite, label_ite, echo_ite]

private theorem clean_views {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (view (cleanSig hψ l r).1) = (view l) ∧
    (view (cleanSig hψ l r).2) = (view r) := by
  simp only [cleanSig]
  simp only [cleanSigGenConnect_view,  cleanSigCleanApply_view, 
    (clean3_views _ _).1, (clean3_views _ _).2,
    (clean4_views _ _).1, (clean4_views _ _).2,
    (clean5_views _ _ _).1, (clean5_views _ _ _).2,
    (clean6_views _ _ _).1, (clean6_views _ _ _).2, and_self]

private theorem eliminate_views {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (view (eliminateSig hψ l r).1) = (view l) ∧
    (view (eliminateSig hψ l r).2) = (view r) := by
  simp only [eliminateSig] <;> simp [fst_ite, snd_ite, view_ite, view,  reset_ite, label_ite, echo_ite]

private theorem step1_views {ψ : Nat} (l r : AgentState ψ) :
    (view (sigMoveStep1With .dropMisaligned l r).1) = (view l) ∧
    (view (sigMoveStep1With .dropMisaligned l r).2) = (view r) := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [sigMoveStep1With, hl, hr] <;> simp [fst_ite, snd_ite, view_ite, view,  reset_ite, label_ite, echo_ite]

private theorem moveTokens_views {ψ : Nat} (l r : AgentState ψ) :
    (view (moveTokens l r).1) = (view l) ∧
    (view (moveTokens l r).2) = (view r) := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [moveTokens, hl, hr] <;> simp [fst_ite, snd_ite, view_ite, view,  reset_ite, label_ite, echo_ite]

private theorem control_view {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (view (sigMoveApplyControlConsume hψ u)) = (view u) := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;> simp [fst_ite, snd_ite, view_ite, view,  reset_ite, label_ite, echo_ite]

private theorem clear_view {ψ : Nat} (u : AgentState ψ) : view (clearCmp u) = view u := rfl
private theorem state_view {ψ : Nat} (u : AgentState ψ) (s : MainState) :
    view { u with state := s } = view u := rfl
private theorem sig_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    view (sigMoveF hψ true .dropMisaligned l r).1 = view l ∧
    view (sigMoveF hψ true .dropMisaligned l r).2 = view r := by
  simp only [sigMoveF, fst_ite, snd_ite, view_ite, state_view,  control_view, 
    leaderWall, clear_view,  (moveTokens_views _ _).1, (moveTokens_views _ _).2,
    (step1_views _ _).1, (step1_views _ _).2, ite_self, and_self]

private theorem drop_view {ψ : Nat} (u : AgentState ψ) :
    (view (dropStale u)) = (view u) := by
  simp only [dropStale]
  simp [view_ite, view,  reset_ite, label_ite, echo_ite]


private theorem path4_view {ψ : Nat} (u : AgentState ψ) : view {u with path4 := none} = view u := rfl
private theorem path5_view {ψ : Nat} (u : AgentState ψ) : view {u with path5 := none} = view u := rfl
private theorem leader_view {ψ : Nat} (u : AgentState ψ) (b : Bool) : view {u with leader := b} = view u := rfl
private theorem cleanSource_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (cleanSource hp l r).1 = view l ∧ view (cleanSource hp l r).2 = view r := by
  simp only [cleanSource]
  simp only [fst_ite,snd_ite,view_ite,path4_view,path5_view,cleanSigGenConnect_view,cleanSigCleanApply_view,
    (clean3_views _ _).1,(clean3_views _ _).2,(clean4_views _ _).1,(clean4_views _ _).2,
    (clean5_views _ _ _).1,(clean5_views _ _ _).2,(clean6_views _ _ _).1,(clean6_views _ _ _).2,ite_self,and_self]
private theorem releaseSource_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (releaseSource hp l r).1 = view l ∧ view (releaseSource hp l r).2 = view r := by
  simp [releaseSource,fst_ite,snd_ite,view_ite,view,reset_ite,label_ite,echo_ite]
private theorem moveSource_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (moveSource hp l r).1 = view l ∧ view (moveSource hp l r).2 = view r := by
  simp only [moveSource]
  simp only [fst_ite,snd_ite,view_ite,control_view,state_view,
    leaderWall,clear_view,(moveTokens_views _ _).1,(moveTokens_views _ _).2,
    (step1_views _ _).1,(step1_views _ _).2,ite_self,and_self]
private theorem reset_views {ψ : Nat} (l r : AgentState ψ) :
    view (preCheckReset l r).1 = view l ∧ view (preCheckReset l r).2 = view r := by
  simp [preCheckReset,clearCmp,view,reset_ite,label_ite,echo_ite]
private theorem orphan_view {ψ : Nat} (u : AgentState ψ) : view (normalizeOrphan u) = view u := by
  cases h : u.path <;> simp [normalizeOrphan,h,view_ite,view,reset_ite,label_ite,echo_ite]
private theorem carrier_view {ψ : Nat} (u : AgentState ψ) : view (normalizeCarrier u) = view u := by
  cases h : u.path <;> simp [normalizeCarrier,releaseCongest,h,view_ite,view,reset_ite,label_ite,echo_ite]
private theorem ready_view {ψ : Nat} (u : AgentState ψ) : view (normalizeReady u) = view u := by
  generalize ho : normalizeOrphan u = o
  have vo : view o = view u := by rw [←ho];exact orphan_view u
  simp only [normalizeReady,ho]
  generalize hc : (if o.state = .none ∧ aligned o then o else normalizeCarrier o) = c
  have vc : view c = view o := by rw [←hc];simp [view_ite,carrier_view]
  have ht := vc.trans vo
  cases hp : c.path <;> simpa [hp,view_ite,view,reset_ite,label_ite,echo_ite] using ht
private theorem checkReady_view {ψ : Nat} (u : AgentState ψ) : view (checkSigSetReadyGuarded u) = view u := by
  cases h : u.path <;> simp [checkSigSetReadyGuarded,checkSigSetReady,h,view_ite,view,reset_ite,label_ite,echo_ite]
private theorem checkL_view {ψ : Nat} (hp : ψ > 0) (u : AgentState ψ) : view (checkSigCheckL hp u) = view u := by
  unfold checkSigCheckL
  split <;> simp [view_ite,view,reset_ite,label_ite,echo_ite]
private theorem checkR_view {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) : view (checkSigCheckR hp l r) = view r := by
  unfold checkSigCheckR
  split <;> simp [view_ite,view,reset_ite,label_ite,echo_ite]
private theorem result_view {ψ : Nat} (u : AgentState ψ) : view (checkSigSetResult u) = view u := by
  simp [checkSigSetResult,view_ite,view,reset_ite,label_ite,echo_ite]
private theorem checkSource_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (checkSource hp l r).1 = view l ∧ view (checkSource hp l r).2 = view r := by
  simp only [checkSource]
  simp only [fst_ite,snd_ite,view_ite,leader_view,state_view,result_view,checkL_view,checkR_view,checkReady_view,ite_self,and_self]

private theorem disappear_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (disappear hp l r).1 = view l ∧ view (disappear hp l r).2 = view r := by
  simp [disappear,fst_ite,snd_ite,view_ite,view,reset_ite,label_ite,echo_ite]
private theorem release_views {ψ : Nat} (l r : AgentState ψ) :
    view (releaseReadySuffix l r).1 = view l ∧ view (releaseReadySuffix l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [releaseReadySuffix,hl,hr,fst_ite,snd_ite,view_ite,view,reset_ite,label_ite,echo_ite]
private theorem ack_views {ψ : Nat} (l r : AgentState ψ) :
    view (ackTail l r).1 = view l ∧ view (ackTail l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [ackTail,hl,hr,fst_ite,snd_ite,view_ite,view,reset_ite,label_ite,echo_ite]
private theorem repair_views {ψ : Nat} (l r : AgentState ψ) :
    view (repair .readyAck l r).1 = view l ∧ view (repair .readyAck l r).2 = view r := by
  simp only [repair,(ack_views _ _).1,(ack_views _ _).2,(release_views _ _).1,(release_views _ _).2,carrier_view,orphan_view,and_self]
private theorem maintain_views {ψ : Nat} (l r : AgentState ψ) :
    view (maintain l r).1 = view l ∧ view (maintain l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [maintain,hl,hr,fst_ite,snd_ite,view_ite,view,reset_ite,label_ite,echo_ite]
private theorem completeWave_views {ψ : Nat} (l r : AgentState ψ) :
    view (completeWave l r).1 = view l ∧ view (completeWave l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [completeWave,hl,hr,fst_ite,snd_ite,view_ite,view,reset_ite,label_ite,echo_ite]
private theorem wave_views {ψ : Nat} (l r : AgentState ψ) :
    view (wave l r).1 = view l ∧ view (wave l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [wave,hl,hr,fst_ite,snd_ite,view_ite,view,reset_ite,label_ite,echo_ite]
private theorem dropStray_views {ψ : Nat} (l r : AgentState ψ) :
    view (dropStray l r).1 = view l ∧ view (dropStray l r).2 = view r := by
  cases hl : l.path2 <;> cases hr : r.path2 <;> simp [dropStray,hl,hr,fst_ite,snd_ite,view_ite,view,reset_ite,label_ite,echo_ite]
private theorem landBackward_view {ψ : Nat} (u : AgentState ψ) : view (landBackward u) = view u := by
  cases hp : u.path <;> cases ht : u.path2 <;> simp [landBackward,hp,ht,view_ite,view,reset_ite,label_ite,echo_ite]
private theorem landForward_view {ψ : Nat} (κ : Nat) (u : AgentState ψ) : view (landForward κ false true u) = view u := by
  cases hp : u.path <;> cases ht : u.path2 <;> simp [landForward,hp,ht,view_ite,view,reset_ite,label_ite,echo_ite]
private theorem compare_views {ψ : Nat} (κ : Nat) (l r : AgentState ψ) :
    view (compareLifecycle κ l r).1 = view l ∧ view (compareLifecycle κ l r).2 = view r := by
  simp only [compareLifecycle,landBackward_view,landForward_view,
    (dropStray_views _ _).1,(dropStray_views _ _).2,(wave_views _ _).1,(wave_views _ _).2,
    (completeWave_views _ _).1,(completeWave_views _ _).2,(maintain_views _ _).1,(maintain_views _ _).2]
  cases hp : l.path <;> simp [hp,view_ite,view,reset_ite,label_ite,echo_ite]

private theorem pPsi_views {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    view (pPsiProbeWall hp l r).1 = view l ∧ view (pPsiProbeWall hp l r).2 = view r := by
  simp only [pPsiProbeWall,pPsi]
  simp [fst_ite,snd_ite,view_ite,view,reset_ite,echo_ite]
theorem prefix_fields {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ) :
    view (beforeSuppress hp κ l r).1 = view l ∧ view (beforeSuppress hp κ l r).2 = view r := by
  simp only [beforeSuppress]
  simp only [(compare_views _ _ _).1,(compare_views _ _ _).2,
    (repair_views _ _).1,(repair_views _ _).2,(disappear_views _ _ _).1,(disappear_views _ _ _).2,
    (checkSource_views _ _ _).1,(checkSource_views _ _ _).2,ready_view,(reset_views _ _).1,(reset_views _ _).2,
    drop_view,(moveSource_views _ _ _).1,(moveSource_views _ _ _).2,(eliminate_views _ _ _).1,(eliminate_views _ _ _).2,
    (releaseSource_views _ _ _).1,(releaseSource_views _ _ _).2,(cleanSource_views _ _ _).1,(cleanSource_views _ _ _).2,
    (gen_views _ _ _ _).1,(gen_views _ _ _ _).2,(pPsi_views _ _ _).1,(pPsi_views _ _ _).2,and_self]
end Fields
namespace Left

private def view {ψ : Nat} (u : AgentState ψ) := u.leader
private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem leader_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).leader = if p then a.leader else b.leader := by split <;> rfl
private theorem label_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).label = if p then a.label else b.label := by split <;> rfl
private theorem probe_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).probe = if p then a.probe else b.probe := by split <;> rfl
private theorem view_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (view (if p then a else b)) = if p then (view a) else (view b) := by split <;> rfl
private theorem gen_views {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (view (genSigSaturated hψ κ l r).1) = (view l) ∧
    (view (genSigSaturated hψ κ l r).2) = (view r) := by
  simp only [genSigSaturated, genSigSaturatedAfterWait, genSigSaturatedStart,
    genSigSaturatedEmit, genSigSaturatedPropagate, genSigSaturatedFinish,
    waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish] <;> simp only [fst_ite, snd_ite, view_ite, view, control, leader_ite, label_ite, probe_ite, ite_self, and_self]

private theorem cleanSigGenConnect_view {ψ : Nat} (u : AgentState ψ) :
    (view (cleanSigGenConnect u)) = (view u) := by
  cases h : u.path <;>
    simp only [cleanSigGenConnect, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, control, leader_ite, label_ite, probe_ite]

private theorem cleanSigCleanApply_view {ψ : Nat} (u : AgentState ψ) :
    (view (cleanSigCleanApply u)) = (view u) := by
  cases h : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp only [cleanSigCleanApply, h, h4, h5] <;>
    (repeat split) <;> simp_all [view_ite, view, control, leader_ite, label_ite, probe_ite]

private theorem clean3_views {ψ : Nat} (l r : AgentState ψ) :
    (view (cleanSigStep3 l r).1) = (view l) ∧
    (view (cleanSigStep3 l r).2) = (view r) := by
  cases h : r.path4 <;> cases hp : l.path <;> simp only [cleanSigStep3, h, hp] <;>
    simp [fst_ite, snd_ite, view_ite, view, control, leader_ite, label_ite, probe_ite]

private theorem clean4_views {ψ : Nat} (l r : AgentState ψ) :
    (view (cleanSigStep4 l r).1) = (view l) ∧
    (view (cleanSigStep4 l r).2) = (view r) := by
  cases h : l.path5 <;> cases hp : r.path <;> simp only [cleanSigStep4, h, hp] <;>
    simp [fst_ite, snd_ite, view_ite, view, control, leader_ite, label_ite, probe_ite]

private theorem clean5_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (cleanSigStep5 hψ l r).1) = (view l) ∧
    (view (cleanSigStep5 hψ l r).2) = (view r) := by
  cases h : r.path4 <;> simp only [cleanSigStep5, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, control, leader_ite, label_ite, probe_ite]

private theorem clean6_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (cleanSigStep6 hψ l r).1) = (view l) ∧
    (view (cleanSigStep6 hψ l r).2) = (view r) := by
  cases h : l.path5 <;> simp only [cleanSigStep6, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, control, leader_ite, label_ite, probe_ite]

private theorem clean_views {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (view (cleanSig hψ l r).1) = (view l) ∧
    (view (cleanSig hψ l r).2) = (view r) := by
  simp only [cleanSig]
  simp only [cleanSigGenConnect_view, control, cleanSigCleanApply_view, control,
    (clean3_views _ _).1, (clean3_views _ _).2,
    (clean4_views _ _).1, (clean4_views _ _).2,
    (clean5_views _ _ _).1, (clean5_views _ _ _).2,
    (clean6_views _ _ _).1, (clean6_views _ _ _).2, and_self]

private theorem eliminate_views {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (view (eliminateSig hψ l r).1) = (view l) ∧
    (view (eliminateSig hψ l r).2) = (view r) := by
  simp only [eliminateSig] <;> simp [fst_ite, snd_ite, view_ite, view, control, leader_ite, label_ite, probe_ite]

private theorem step1_views {ψ : Nat} (l r : AgentState ψ) :
    (view (sigMoveStep1With .dropMisaligned l r).1) = (view l) ∧
    (view (sigMoveStep1With .dropMisaligned l r).2) = (view r) := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [sigMoveStep1With, hl, hr] <;> simp [fst_ite, snd_ite, view_ite, view, control, leader_ite, label_ite, probe_ite]

private theorem moveTokens_views {ψ : Nat} (l r : AgentState ψ) :
    (view (moveTokens l r).1) = (view l) ∧
    (view (moveTokens l r).2) = (view r) := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [moveTokens, hl, hr] <;> simp [fst_ite, snd_ite, view_ite, view, control, leader_ite, label_ite, probe_ite]

private theorem control_view {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (view (sigMoveApplyControlConsume hψ u)) = (view u) := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;> simp [fst_ite, snd_ite, view_ite, view, control, leader_ite, label_ite, probe_ite]

private theorem clear_view {ψ : Nat} (u : AgentState ψ) : view (clearCmp u) = view u := rfl
private theorem state_view {ψ : Nat} (u : AgentState ψ) (s : MainState) :
    view { u with state := s } = view u := rfl
private theorem sig_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    view (sigMoveF hψ true .dropMisaligned l r).1 = view l ∧
    view (sigMoveF hψ true .dropMisaligned l r).2 = view r := by
  simp only [sigMoveF, fst_ite, snd_ite, view_ite, state_view, control, control_view, control,
    leaderWall, clear_view, control, (moveTokens_views _ _).1, (moveTokens_views _ _).2,
    (step1_views _ _).1, (step1_views _ _).2, ite_self, and_self]

private theorem drop_view {ψ : Nat} (u : AgentState ψ) :
    (view (dropStale u)) = (view u) := by
  simp only [dropStale]
  simp [view_ite, view, control, leader_ite, label_ite, probe_ite]


private theorem path4_view {ψ : Nat} (u : AgentState ψ) : view {u with path4 := none} = view u := rfl
private theorem path5_view {ψ : Nat} (u : AgentState ψ) : view {u with path5 := none} = view u := rfl
private theorem cleanSource_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (cleanSource hp l r).1 = view l ∧ view (cleanSource hp l r).2 = view r := by
  simp only [cleanSource]
  simp only [fst_ite,snd_ite,view_ite,path4_view,path5_view,cleanSigGenConnect_view,cleanSigCleanApply_view,
    (clean3_views _ _).1,(clean3_views _ _).2,(clean4_views _ _).1,(clean4_views _ _).2,
    (clean5_views _ _ _).1,(clean5_views _ _ _).2,(clean6_views _ _ _).1,(clean6_views _ _ _).2,ite_self,and_self]
private theorem releaseSource_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (releaseSource hp l r).1 = view l ∧ view (releaseSource hp l r).2 = view r := by
  simp [releaseSource,fst_ite,snd_ite,view_ite,view,control,leader_ite,label_ite,probe_ite]
private theorem moveSource_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (moveSource hp l r).1 = view l ∧ view (moveSource hp l r).2 = view r := by
  simp only [moveSource]
  simp only [fst_ite,snd_ite,view_ite,control_view,state_view,
    leaderWall,clear_view,(moveTokens_views _ _).1,(moveTokens_views _ _).2,
    (step1_views _ _).1,(step1_views _ _).2,ite_self,and_self]
private theorem reset_views {ψ : Nat} (l r : AgentState ψ) :
    view (preCheckReset l r).1 = view l ∧ view (preCheckReset l r).2 = view r := by
  simp [preCheckReset,clearCmp,view,control,leader_ite,label_ite,probe_ite]
private theorem orphan_view {ψ : Nat} (u : AgentState ψ) : view (normalizeOrphan u) = view u := by
  cases h : u.path <;> simp [normalizeOrphan,h,view_ite,view,control,leader_ite,label_ite,probe_ite]
private theorem carrier_view {ψ : Nat} (u : AgentState ψ) : view (normalizeCarrier u) = view u := by
  cases h : u.path <;> simp [normalizeCarrier,releaseCongest,h,view_ite,view,control,leader_ite,label_ite,probe_ite]
private theorem ready_view {ψ : Nat} (u : AgentState ψ) : view (normalizeReady u) = view u := by
  generalize ho : normalizeOrphan u = o
  have vo : view o = view u := by rw [←ho];exact orphan_view u
  simp only [normalizeReady,ho]
  generalize hc : (if o.state = .none ∧ aligned o then o else normalizeCarrier o) = c
  have vc : view c = view o := by rw [←hc];simp [view_ite,carrier_view]
  have ht := vc.trans vo
  cases hp : c.path <;> simpa [hp,view_ite,view,control,leader_ite,label_ite,probe_ite] using ht
private theorem checkReady_view {ψ : Nat} (u : AgentState ψ) : view (checkSigSetReadyGuarded u) = view u := by
  cases h : u.path <;> simp [checkSigSetReadyGuarded,checkSigSetReady,h,view_ite,view,control,leader_ite,label_ite,probe_ite]
private theorem checkL_view {ψ : Nat} (hp : ψ > 0) (u : AgentState ψ) : view (checkSigCheckL hp u) = view u := by
  unfold checkSigCheckL
  split <;> simp [view_ite,view,control,leader_ite,label_ite,probe_ite]
private theorem checkR_view {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) : view (checkSigCheckR hp l r) = view r := by
  unfold checkSigCheckR
  split <;> simp [view_ite,view,control,leader_ite,label_ite,probe_ite]
private theorem result_view {ψ : Nat} (u : AgentState ψ) : view (checkSigSetResult u) = view u := by
  simp [checkSigSetResult,view_ite,view,control,leader_ite,label_ite,probe_ite]
private theorem disappear_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (disappear hp l r).1 = view l ∧ view (disappear hp l r).2 = view r := by
  simp [disappear,fst_ite,snd_ite,view_ite,view,control,leader_ite,label_ite,probe_ite]
private theorem release_views {ψ : Nat} (l r : AgentState ψ) :
    view (releaseReadySuffix l r).1 = view l ∧ view (releaseReadySuffix l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [releaseReadySuffix,hl,hr,fst_ite,snd_ite,view_ite,view,control,leader_ite,label_ite,probe_ite]
private theorem ack_views {ψ : Nat} (l r : AgentState ψ) :
    view (ackTail l r).1 = view l ∧ view (ackTail l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [ackTail,hl,hr,fst_ite,snd_ite,view_ite,view,control,leader_ite,label_ite,probe_ite]
private theorem repair_views {ψ : Nat} (l r : AgentState ψ) :
    view (repair .readyAck l r).1 = view l ∧ view (repair .readyAck l r).2 = view r := by
  simp only [repair,(ack_views _ _).1,(ack_views _ _).2,(release_views _ _).1,(release_views _ _).2,carrier_view,orphan_view,and_self]
private theorem maintain_views {ψ : Nat} (l r : AgentState ψ) :
    view (maintain l r).1 = view l ∧ view (maintain l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [maintain,hl,hr,fst_ite,snd_ite,view_ite,view,control,leader_ite,label_ite,probe_ite]
private theorem completeWave_views {ψ : Nat} (l r : AgentState ψ) :
    view (completeWave l r).1 = view l ∧ view (completeWave l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [completeWave,hl,hr,fst_ite,snd_ite,view_ite,view,control,leader_ite,label_ite,probe_ite]
private theorem wave_views {ψ : Nat} (l r : AgentState ψ) :
    view (wave l r).1 = view l ∧ view (wave l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [wave,hl,hr,fst_ite,snd_ite,view_ite,view,control,leader_ite,label_ite,probe_ite]
private theorem dropStray_views {ψ : Nat} (l r : AgentState ψ) :
    view (dropStray l r).1 = view l ∧ view (dropStray l r).2 = view r := by
  cases hl : l.path2 <;> cases hr : r.path2 <;> simp [dropStray,hl,hr,fst_ite,snd_ite,view_ite,view,control,leader_ite,label_ite,probe_ite]
private theorem landBackward_view {ψ : Nat} (u : AgentState ψ) : view (landBackward u) = view u := by
  cases hp : u.path <;> cases ht : u.path2 <;> simp [landBackward,hp,ht,view_ite,view,control,leader_ite,label_ite,probe_ite]

private theorem checkSource_left {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    view (checkSource hp l r).1 = view l := by
  simp only [checkSource,fst_ite,view_ite,result_view,checkL_view,state_view,checkReady_view,ite_self]
private theorem compare_left {ψ : Nat} (κ : Nat) (l r : AgentState ψ) :
    view (compareLifecycle κ l r).1 = view l := by
  simp only [compareLifecycle,landBackward_view,(dropStray_views _ _).1,(wave_views _ _).1,
    (completeWave_views _ _).1,(maintain_views _ _).1]
  cases h : l.path <;> simp [h,view_ite,view,leader_ite]
private theorem pPsi_left {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    view (pPsiProbeWall hp l r).1 = view l := by
  simp [pPsiProbeWall,pPsi,fst_ite,view_ite,view,leader_ite]
theorem prefix_left {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ) :
    (beforeSuppress hp κ l r).1.leader = l.leader := by
  change view _ = view _
  simp only [beforeSuppress,compare_left,(repair_views _ _).1,(disappear_views _ _ _).1,
    checkSource_left,ready_view,(reset_views _ _).1,drop_view,(moveSource_views _ _ _).1,
    (eliminate_views _ _ _).1,(releaseSource_views _ _ _).1,(cleanSource_views _ _ _).1,
    (gen_views _ _ _ _).1,pPsi_left]
end Left

namespace Writer
private def Frame {ψ : Nat} (a b : AgentState ψ) : Prop :=
  a.reset_cmd = b.reset_cmd ∧ a.echo = b.echo ∧ a.probe = b.probe

private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem reset_cmd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).reset_cmd = if p then a.reset_cmd else b.reset_cmd := by split <;> rfl
private theorem echo_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).echo = if p then a.echo else b.echo := by split <;> rfl
private theorem probe_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).probe = if p then a.probe else b.probe := by split <;> rfl

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
    simp [reset_cmd_ite, echo_ite, probe_ite, hp]

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
    simp only [fst_ite, snd_ite, reset_cmd_ite, echo_ite, probe_ite, ite_self, and_self]

private theorem groupInfo_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (groupInfo hψ l r).1 l ∧ Frame (groupInfo hψ l r).2 r := by
  simp only [Frame, groupInfo]
  simp only [fst_ite, snd_ite, reset_cmd_ite, echo_ite, probe_ite, ite_self, and_self]

private theorem gensigWriteseq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (gensigWriteseq hψ l r).1 l ∧ Frame (gensigWriteseq hψ l r).2 r := by
  simp only [Frame, gensigWriteseq]
  simp only [fst_ite, snd_ite, reset_cmd_ite, echo_ite, probe_ite, ite_self, and_self]

private theorem writeAction_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (writeAction hψ l r).1 l ∧ Frame (writeAction hψ l r).2 r := by
  simp only [Frame, writeAction]
  simp only [fst_ite, snd_ite, reset_cmd_ite, echo_ite, probe_ite, ite_self, and_self , (writeActionApplyOverwrite_frame _).1, (writeActionApplyOverwrite_frame _).2.1, (writeActionApplyOverwrite_frame _).2.2, (writeActionApplyMoveFlip_frame _).1, (writeActionApplyMoveFlip_frame _).2.1, (writeActionApplyMoveFlip_frame _).2.2]

private theorem moveWsig_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (moveWsig hψ l r).1 l ∧ Frame (moveWsig hψ l r).2 r := by
  simp only [Frame, moveWsig]
  simp only [fst_ite, snd_ite, reset_cmd_ite, echo_ite, probe_ite, ite_self, and_self , (moveWsigCheckGenWs_frame _ _).1, (moveWsigCheckGenWs_frame _ _).2.1, (moveWsigCheckGenWs_frame _ _).2.2, (moveWsigCheckLast_frame _).1, (moveWsigCheckLast_frame _).2.1, (moveWsigCheckLast_frame _).2.2, (moveWsigTransfer_frame _ _).1.1, (moveWsigTransfer_frame _ _).1.2.1, (moveWsigTransfer_frame _ _).1.2.2, (moveWsigTransfer_frame _ _).2.1, (moveWsigTransfer_frame _ _).2.2.1, (moveWsigTransfer_frame _ _).2.2.2]

private theorem writeSeq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (writeSeq hψ l r).1 l ∧ Frame (writeSeq hψ l r).2 r := by
  simp only [Frame, writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands]
  simp only [fst_ite, snd_ite, reset_cmd_ite, echo_ite, probe_ite, ite_self, and_self, (groupInfo_frame _ _ _).1.1, (groupInfo_frame _ _ _).1.2.1, (groupInfo_frame _ _ _).1.2.2, (groupInfo_frame _ _ _).2.1, (groupInfo_frame _ _ _).2.2.1, (groupInfo_frame _ _ _).2.2.2, (gensigWriteseq_frame _ _ _).1.1, (gensigWriteseq_frame _ _ _).1.2.1, (gensigWriteseq_frame _ _ _).1.2.2, (gensigWriteseq_frame _ _ _).2.1, (gensigWriteseq_frame _ _ _).2.2.1, (gensigWriteseq_frame _ _ _).2.2.2, (writeAction_frame _ _ _).1.1, (writeAction_frame _ _ _).1.2.1, (writeAction_frame _ _ _).1.2.2, (writeAction_frame _ _ _).2.1, (writeAction_frame _ _ _).2.2.1, (writeAction_frame _ _ _).2.2.2, (moveWsig_frame _ _ _).1.1, (moveWsig_frame _ _ _).1.2.1, (moveWsig_frame _ _ _).1.2.2, (moveWsig_frame _ _ _).2.1, (moveWsig_frame _ _ _).2.2.1, (moveWsig_frame _ _ _).2.2.2, (writeSeqSetWriteReady_frame _).1, (writeSeqSetWriteReady_frame _).2.1, (writeSeqSetWriteReady_frame _).2.2, (writeSeqCheckBit_frame _).1, (writeSeqCheckBit_frame _).2.1, (writeSeqCheckBit_frame _).2.2, (writeSeqSetWriteAct_frame _).1, (writeSeqSetWriteAct_frame _).2.1, (writeSeqSetWriteAct_frame _).2.2, (writeSeqFinalR_frame _).1, (writeSeqFinalR_frame _).2.1, (writeSeqFinalR_frame _).2.2]


private theorem write_fields {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    (writeWithBundle hp l r).1.reset_cmd=l.reset_cmd ∧
    (writeWithBundle hp l r).1.echo=l.echo ∧
    (writeWithBundle hp l r).2.reset_cmd=r.reset_cmd ∧
    (writeWithBundle hp l r).2.echo=r.echo := by
  simp only [writeWithBundle,fst_ite,snd_ite,reset_cmd_ite,echo_ite,
    (writeSeq_frame hp l r).1.1,(writeSeq_frame hp l r).1.2.1,
    (writeSeq_frame hp l r).2.1,(writeSeq_frame hp l r).2.2.1,ite_self,and_self]
private theorem kernel_fields {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    (k4Kernel hp l r).1.reset_cmd=l.reset_cmd ∧ (k4Kernel hp l r).1.echo=l.echo ∧
    (k4Kernel hp l r).2.reset_cmd=r.reset_cmd ∧ (k4Kernel hp l r).2.echo=r.echo := by
  simp only [k4Kernel,k3Kernel,eliminateLeadersNoCollisionFire,absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink,dummyBulletSink]
  simp [fst_ite,snd_ite,reset_cmd_ite,echo_ite]
theorem suffix_fields {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) :
    let z := conserve .head l r (writeWithBundle hp (k4Kernel hp q.1 q.2).1 (k4Kernel hp q.1 q.2).2)
    z.1.reset_cmd=q.1.reset_cmd ∧ z.1.echo=q.1.echo ∧
    z.2.reset_cmd=q.2.reset_cmd ∧ z.2.echo=q.2.echo := by
  simp only [conserve,replacement,clearCmp]
  simp only [fst_ite,snd_ite,reset_cmd_ite,echo_ite,
    (write_fields _ _ _).1,(write_fields _ _ _).2.1,(write_fields _ _ _).2.2.1,(write_fields _ _ _).2.2.2,
    (kernel_fields _ _ _).1,(kernel_fields _ _ _).2.1,(kernel_fields _ _ _).2.2.1,(kernel_fields _ _ _).2.2.2,ite_self,and_self]
end Writer

/-- `beforeElimination` for ReadyAck is the ReadyAck prefix followed by signal
suppression. Proved by normalising the constant design guards. -/
theorem prefix_identity {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ) :
    PPLLAstraDesign3.beforeElimination hp κ .readyAck l r =
      suppressSigResetKill hp (beforeSuppress hp κ l r).1 (beforeSuppress hp κ l r).2 := by
  simp only [PPLLAstraDesign3.beforeElimination,beforeSuppress,reduceCtorEq,or_true,or_false,
    decide_true,ite_true,ite_false,if_true,if_false]

/-- The ReadyAck prefix preserves reset and echo bits on both endpoints. -/
theorem prefix_bits {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ) :
    (beforeSuppress hp κ l r).1.reset_cmd=l.reset_cmd ∧ (beforeSuppress hp κ l r).1.echo=l.echo ∧
    (beforeSuppress hp κ l r).2.reset_cmd=r.reset_cmd ∧ (beforeSuppress hp κ l r).2.echo=r.echo := by
  have h := Fields.prefix_fields hp κ l r
  simp only [Fields.view,Prod.mk.injEq] at h
  exact ⟨h.1.1,h.1.2,h.2.1,h.2.2⟩

/-- The initiator's leader bit is preserved by the ReadyAck prefix. -/
theorem prefix_leader {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ) :
    (beforeSuppress hp κ l r).1.leader=l.leader := Left.prefix_left hp κ l r

/-- K4, WRITE and the Head conservation guard preserve reset and echo bits. -/
theorem pipeline_bits {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ) :
    (PPLLAstraDesign3.pipeline hp κ .readyAck l r).1.reset_cmd=
      (PPLLAstraDesign3.beforeElimination hp κ .readyAck l r).1.reset_cmd ∧
    (PPLLAstraDesign3.pipeline hp κ .readyAck l r).1.echo=
      (PPLLAstraDesign3.beforeElimination hp κ .readyAck l r).1.echo ∧
    (PPLLAstraDesign3.pipeline hp κ .readyAck l r).2.reset_cmd=
      (PPLLAstraDesign3.beforeElimination hp κ .readyAck l r).2.reset_cmd ∧
    (PPLLAstraDesign3.pipeline hp κ .readyAck l r).2.echo=
      (PPLLAstraDesign3.beforeElimination hp κ .readyAck l r).2.echo :=
  Writer.suffix_fields hp l r (PPLLAstraDesign3.beforeElimination hp κ .readyAck l r)

#print axioms prefix_identity
#print axioms prefix_bits
#print axioms pipeline_bits
end PPLLAstraReadyResetDebtR
