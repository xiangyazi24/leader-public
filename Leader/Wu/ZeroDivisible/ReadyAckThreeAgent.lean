import Leader.Wu.ZeroDivisible.LockCycleRepairs
import Leader.Wu.Safety.ConcreteProtocolProperties
/-! ReadyAck-specific local projections for the three-agent bootstrap.
Every local statement quantifies over raw ancillary fields and arbitrary κ;
these statements do not substitute the Head active-cut for ReadyAck. -/
namespace PPLLAstraReadyThree
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3
set_option linter.unusedSimpArgs false
/-- Physical control visible to P′, ignoring comparison and writer debris. -/
def control {ψ : Nat} (u : AgentState ψ) := (u.label,u.phase,u.probe)
private def view := @control
private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem phase_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).phase = if p then a.phase else b.phase := by split <;> rfl
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
    waitSaturatedReset, waitSaturatedFinish] <;> simp only [fst_ite, snd_ite, view_ite, view, control, phase_ite, label_ite, probe_ite, ite_self, and_self]

private theorem cleanSigGenConnect_view {ψ : Nat} (u : AgentState ψ) :
    (view (cleanSigGenConnect u)) = (view u) := by
  cases h : u.path <;>
    simp only [cleanSigGenConnect, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, control, phase_ite, label_ite, probe_ite]

private theorem cleanSigCleanApply_view {ψ : Nat} (u : AgentState ψ) :
    (view (cleanSigCleanApply u)) = (view u) := by
  cases h : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp only [cleanSigCleanApply, h, h4, h5] <;>
    (repeat split) <;> simp_all [view_ite, view, control, phase_ite, label_ite, probe_ite]

private theorem clean3_views {ψ : Nat} (l r : AgentState ψ) :
    (view (cleanSigStep3 l r).1) = (view l) ∧
    (view (cleanSigStep3 l r).2) = (view r) := by
  cases h : r.path4 <;> cases hp : l.path <;> simp only [cleanSigStep3, h, hp] <;>
    simp [fst_ite, snd_ite, view_ite, view, control, phase_ite, label_ite, probe_ite]

private theorem clean4_views {ψ : Nat} (l r : AgentState ψ) :
    (view (cleanSigStep4 l r).1) = (view l) ∧
    (view (cleanSigStep4 l r).2) = (view r) := by
  cases h : l.path5 <;> cases hp : r.path <;> simp only [cleanSigStep4, h, hp] <;>
    simp [fst_ite, snd_ite, view_ite, view, control, phase_ite, label_ite, probe_ite]

private theorem clean5_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (cleanSigStep5 hψ l r).1) = (view l) ∧
    (view (cleanSigStep5 hψ l r).2) = (view r) := by
  cases h : r.path4 <;> simp only [cleanSigStep5, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, control, phase_ite, label_ite, probe_ite]

private theorem clean6_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (cleanSigStep6 hψ l r).1) = (view l) ∧
    (view (cleanSigStep6 hψ l r).2) = (view r) := by
  cases h : l.path5 <;> simp only [cleanSigStep6, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, control, phase_ite, label_ite, probe_ite]

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
  simp only [eliminateSig] <;> simp [fst_ite, snd_ite, view_ite, view, control, phase_ite, label_ite, probe_ite]

private theorem step1_views {ψ : Nat} (l r : AgentState ψ) :
    (view (sigMoveStep1With .dropMisaligned l r).1) = (view l) ∧
    (view (sigMoveStep1With .dropMisaligned l r).2) = (view r) := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [sigMoveStep1With, hl, hr] <;> simp [fst_ite, snd_ite, view_ite, view, control, phase_ite, label_ite, probe_ite]

private theorem moveTokens_views {ψ : Nat} (l r : AgentState ψ) :
    (view (moveTokens l r).1) = (view l) ∧
    (view (moveTokens l r).2) = (view r) := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [moveTokens, hl, hr] <;> simp [fst_ite, snd_ite, view_ite, view, control, phase_ite, label_ite, probe_ite]

private theorem control_view {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (view (sigMoveApplyControlConsume hψ u)) = (view u) := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;> simp [fst_ite, snd_ite, view_ite, view, control, phase_ite, label_ite, probe_ite]

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
  simp [view_ite, view, control, phase_ite, label_ite, probe_ite]


private theorem suppress_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (suppressSigResetKill hψ l r).1) = (view l) ∧
    (view (suppressSigResetKill hψ l r).2) = (view r) := by
  cases h1 : l.phase <;> cases h2 : l.reset_cmd <;>
    cases h3 : r.reset_cmd <;> cases h4 : r.echo <;>
    simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
      suppressSigTerminal, suppressSigEcho, suppressSigFinish, clearCmp,
      view, control,h1,h2,h3,h4,fst_ite,snd_ite,phase_ite,label_ite,probe_ite]

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
  simp [releaseSource,fst_ite,snd_ite,view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem moveSource_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (moveSource hp l r).1 = view l ∧ view (moveSource hp l r).2 = view r := by
  simp only [moveSource]
  simp only [fst_ite,snd_ite,view_ite,control_view,state_view,
    leaderWall,clear_view,(moveTokens_views _ _).1,(moveTokens_views _ _).2,
    (step1_views _ _).1,(step1_views _ _).2,ite_self,and_self]
private theorem reset_views {ψ : Nat} (l r : AgentState ψ) :
    view (preCheckReset l r).1 = view l ∧ view (preCheckReset l r).2 = view r := by
  simp [preCheckReset,clearCmp,view,control,phase_ite,label_ite,probe_ite]
private theorem orphan_view {ψ : Nat} (u : AgentState ψ) : view (normalizeOrphan u) = view u := by
  cases h : u.path <;> simp [normalizeOrphan,h,view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem carrier_view {ψ : Nat} (u : AgentState ψ) : view (normalizeCarrier u) = view u := by
  cases h : u.path <;> simp [normalizeCarrier,releaseCongest,h,view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem ready_view {ψ : Nat} (u : AgentState ψ) : view (normalizeReady u) = view u := by
  generalize ho : normalizeOrphan u = o
  have vo : view o = view u := by rw [←ho];exact orphan_view u
  simp only [normalizeReady,ho]
  generalize hc : (if o.state = .none ∧ aligned o then o else normalizeCarrier o) = c
  have vc : view c = view o := by rw [←hc];simp [view_ite,carrier_view]
  have ht := vc.trans vo
  cases hp : c.path <;> simpa [hp,view_ite,view,control,phase_ite,label_ite,probe_ite] using ht
private theorem checkReady_view {ψ : Nat} (u : AgentState ψ) : view (checkSigSetReadyGuarded u) = view u := by
  cases h : u.path <;> simp [checkSigSetReadyGuarded,checkSigSetReady,h,view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem checkL_view {ψ : Nat} (hp : ψ > 0) (u : AgentState ψ) : view (checkSigCheckL hp u) = view u := by
  unfold checkSigCheckL
  split <;> simp [view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem checkR_view {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) : view (checkSigCheckR hp l r) = view r := by
  unfold checkSigCheckR
  split <;> simp [view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem result_view {ψ : Nat} (u : AgentState ψ) : view (checkSigSetResult u) = view u := by
  simp [checkSigSetResult,view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem checkSource_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (checkSource hp l r).1 = view l ∧ view (checkSource hp l r).2 = view r := by
  simp only [checkSource]
  simp only [fst_ite,snd_ite,view_ite,leader_view,state_view,result_view,checkL_view,checkR_view,checkReady_view,ite_self,and_self]

private theorem disappear_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (disappear hp l r).1 = view l ∧ view (disappear hp l r).2 = view r := by
  simp [disappear,fst_ite,snd_ite,view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem release_views {ψ : Nat} (l r : AgentState ψ) :
    view (releaseReadySuffix l r).1 = view l ∧ view (releaseReadySuffix l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [releaseReadySuffix,hl,hr,fst_ite,snd_ite,view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem ack_views {ψ : Nat} (l r : AgentState ψ) :
    view (ackTail l r).1 = view l ∧ view (ackTail l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [ackTail,hl,hr,fst_ite,snd_ite,view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem repair_views {ψ : Nat} (l r : AgentState ψ) :
    view (repair .readyAck l r).1 = view l ∧ view (repair .readyAck l r).2 = view r := by
  simp only [repair,(ack_views _ _).1,(ack_views _ _).2,(release_views _ _).1,(release_views _ _).2,carrier_view,orphan_view,and_self]
private theorem maintain_views {ψ : Nat} (l r : AgentState ψ) :
    view (maintain l r).1 = view l ∧ view (maintain l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [maintain,hl,hr,fst_ite,snd_ite,view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem completeWave_views {ψ : Nat} (l r : AgentState ψ) :
    view (completeWave l r).1 = view l ∧ view (completeWave l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [completeWave,hl,hr,fst_ite,snd_ite,view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem wave_views {ψ : Nat} (l r : AgentState ψ) :
    view (wave l r).1 = view l ∧ view (wave l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [wave,hl,hr,fst_ite,snd_ite,view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem dropStray_views {ψ : Nat} (l r : AgentState ψ) :
    view (dropStray l r).1 = view l ∧ view (dropStray l r).2 = view r := by
  cases hl : l.path2 <;> cases hr : r.path2 <;> simp [dropStray,hl,hr,fst_ite,snd_ite,view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem landBackward_view {ψ : Nat} (u : AgentState ψ) : view (landBackward u) = view u := by
  cases hp : u.path <;> cases ht : u.path2 <;> simp [landBackward,hp,ht,view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem landForward_view {ψ : Nat} (κ : Nat) (u : AgentState ψ) : view (landForward κ false true u) = view u := by
  cases hp : u.path <;> cases ht : u.path2 <;> simp [landForward,hp,ht,view_ite,view,control,phase_ite,label_ite,probe_ite]
private theorem compare_views {ψ : Nat} (κ : Nat) (l r : AgentState ψ) :
    view (compareLifecycle κ l r).1 = view l ∧ view (compareLifecycle κ l r).2 = view r := by
  simp only [compareLifecycle,landBackward_view,landForward_view,
    (dropStray_views _ _).1,(dropStray_views _ _).2,(wave_views _ _).1,(wave_views _ _).2,
    (completeWave_views _ _).1,(completeWave_views _ _).2,(maintain_views _ _).1,(maintain_views _ _).2]
  cases hp : l.path <;> simp [hp,view_ite,view,control,phase_ite,label_ite,probe_ite]
/-- Every ReadyAck comparison-prefix stage after P′ frames its physical
label/phase/probe control, without an active-reset assumption. -/
theorem before_control {ψ : Nat} (hp : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    control (PPLLAstraDesign3.beforeElimination hp κ .readyAck l r).1 = control (pPsiProbeWall hp l r).1 ∧
    control (PPLLAstraDesign3.beforeElimination hp κ .readyAck l r).2 = control (pPsiProbeWall hp l r).2 := by
  change view _ = view _ ∧ view _ = view _
  simp only [PPLLAstraDesign3.beforeElimination,reduceCtorEq,or_true,or_false,decide_true,ite_true,ite_false]
  simp only [(suppress_views _ _ _).1,(suppress_views _ _ _).2,(compare_views _ _ _).1,(compare_views _ _ _).2,
    (repair_views _ _).1,(repair_views _ _).2,(disappear_views _ _ _).1,(disappear_views _ _ _).2,
    (checkSource_views _ _ _).1,(checkSource_views _ _ _).2,ready_view,(reset_views _ _).1,(reset_views _ _).2,
    drop_view,(moveSource_views _ _ _).1,(moveSource_views _ _ _).2,(eliminate_views _ _ _).1,(eliminate_views _ _ _).2,
    (releaseSource_views _ _ _).1,(releaseSource_views _ _ _).2,(cleanSource_views _ _ _).1,(cleanSource_views _ _ _).2,
    (gen_views _ _ _ _).1,(gen_views _ _ _ _).2,and_self]


namespace Writer
private def Frame {ψ : Nat} (a b : AgentState ψ) : Prop :=
  a.phase = b.phase ∧ a.echo = b.echo ∧ a.probe = b.probe

private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem phase_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).phase = if p then a.phase else b.phase := by split <;> rfl
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
    simp [phase_ite, echo_ite, probe_ite, hp]

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
    simp only [fst_ite, snd_ite, phase_ite, echo_ite, probe_ite, ite_self, and_self]

private theorem groupInfo_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (groupInfo hψ l r).1 l ∧ Frame (groupInfo hψ l r).2 r := by
  simp only [Frame, groupInfo]
  simp only [fst_ite, snd_ite, phase_ite, echo_ite, probe_ite, ite_self, and_self]

private theorem gensigWriteseq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (gensigWriteseq hψ l r).1 l ∧ Frame (gensigWriteseq hψ l r).2 r := by
  simp only [Frame, gensigWriteseq]
  simp only [fst_ite, snd_ite, phase_ite, echo_ite, probe_ite, ite_self, and_self]

private theorem writeAction_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (writeAction hψ l r).1 l ∧ Frame (writeAction hψ l r).2 r := by
  simp only [Frame, writeAction]
  simp only [fst_ite, snd_ite, phase_ite, echo_ite, probe_ite, ite_self, and_self , (writeActionApplyOverwrite_frame _).1, (writeActionApplyOverwrite_frame _).2.1, (writeActionApplyOverwrite_frame _).2.2, (writeActionApplyMoveFlip_frame _).1, (writeActionApplyMoveFlip_frame _).2.1, (writeActionApplyMoveFlip_frame _).2.2]

private theorem moveWsig_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (moveWsig hψ l r).1 l ∧ Frame (moveWsig hψ l r).2 r := by
  simp only [Frame, moveWsig]
  simp only [fst_ite, snd_ite, phase_ite, echo_ite, probe_ite, ite_self, and_self , (moveWsigCheckGenWs_frame _ _).1, (moveWsigCheckGenWs_frame _ _).2.1, (moveWsigCheckGenWs_frame _ _).2.2, (moveWsigCheckLast_frame _).1, (moveWsigCheckLast_frame _).2.1, (moveWsigCheckLast_frame _).2.2, (moveWsigTransfer_frame _ _).1.1, (moveWsigTransfer_frame _ _).1.2.1, (moveWsigTransfer_frame _ _).1.2.2, (moveWsigTransfer_frame _ _).2.1, (moveWsigTransfer_frame _ _).2.2.1, (moveWsigTransfer_frame _ _).2.2.2]

private theorem writeSeq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (writeSeq hψ l r).1 l ∧ Frame (writeSeq hψ l r).2 r := by
  simp only [Frame, writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands]
  simp only [fst_ite, snd_ite, phase_ite, echo_ite, probe_ite, ite_self, and_self, (groupInfo_frame _ _ _).1.1, (groupInfo_frame _ _ _).1.2.1, (groupInfo_frame _ _ _).1.2.2, (groupInfo_frame _ _ _).2.1, (groupInfo_frame _ _ _).2.2.1, (groupInfo_frame _ _ _).2.2.2, (gensigWriteseq_frame _ _ _).1.1, (gensigWriteseq_frame _ _ _).1.2.1, (gensigWriteseq_frame _ _ _).1.2.2, (gensigWriteseq_frame _ _ _).2.1, (gensigWriteseq_frame _ _ _).2.2.1, (gensigWriteseq_frame _ _ _).2.2.2, (writeAction_frame _ _ _).1.1, (writeAction_frame _ _ _).1.2.1, (writeAction_frame _ _ _).1.2.2, (writeAction_frame _ _ _).2.1, (writeAction_frame _ _ _).2.2.1, (writeAction_frame _ _ _).2.2.2, (moveWsig_frame _ _ _).1.1, (moveWsig_frame _ _ _).1.2.1, (moveWsig_frame _ _ _).1.2.2, (moveWsig_frame _ _ _).2.1, (moveWsig_frame _ _ _).2.2.1, (moveWsig_frame _ _ _).2.2.2, (writeSeqSetWriteReady_frame _).1, (writeSeqSetWriteReady_frame _).2.1, (writeSeqSetWriteReady_frame _).2.2, (writeSeqCheckBit_frame _).1, (writeSeqCheckBit_frame _).2.1, (writeSeqCheckBit_frame _).2.2, (writeSeqSetWriteAct_frame _).1, (writeSeqSetWriteAct_frame _).2.1, (writeSeqSetWriteAct_frame _).2.2, (writeSeqFinalR_frame _).1, (writeSeqFinalR_frame _).2.1, (writeSeqFinalR_frame _).2.2]

theorem write_control {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    control (writeWithBundle hp l r).1 = control l ∧ control (writeWithBundle hp l r).2 = control r := by
  simp only [control,writeWithBundle,fst_ite,snd_ite,phase_ite,probe_ite,
    PPLLAstraReadyThree.label_ite,PPLLVerify.writeSeq_l_label,PPLLVerify.writeSeq_r_label,
    (writeSeq_frame hp l r).1.1,(writeSeq_frame hp l r).1.2.2,
    (writeSeq_frame hp l r).2.1,(writeSeq_frame hp l r).2.2.2,ite_self,and_self]
end Writer
private theorem kernel_control {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    control (k4Kernel hp l r).1 = control l ∧ control (k4Kernel hp l r).2 = control r := by
  simp only [k4Kernel,k3Kernel,eliminateLeadersNoCollisionFire,absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink,dummyBulletSink]
  simp [control,fst_ite,snd_ite,label_ite,phase_ite,probe_ite]
attribute [local irreducible] k4Kernel writeWithBundle
/-- On a follower/follower input, the complete ReadyAck transition has exactly
P′'s label/phase/probe outputs, even if later comparison stages elect a leader. -/
theorem pipeline_followers_control {ψ : Nat} (hp : ψ > 0) (κ : Nat) (l r : AgentState ψ)
    (hl : l.leader = false) (hr : r.leader = false) :
    control (PPLLAstraDesign3.pipeline hp κ .readyAck l r).1 = control (pPsiProbeWall hp l r).1 ∧
    control (PPLLAstraDesign3.pipeline hp κ .readyAck l r).2 = control (pPsiProbeWall hp l r).2 := by
  have hb := before_control hp κ l r
  simp only [PPLLAstraDesign3.pipeline]
  generalize he : PPLLAstraDesign3.beforeElimination hp κ .readyAck l r = q at *
  have hk := kernel_control hp q.1 q.2
  generalize hke : k4Kernel hp q.1 q.2 = k at *
  have hw := Writer.write_control hp k.1 k.2
  generalize hwe : writeWithBundle hp k.1 k.2 = w at *
  simp only [conserve,hl,hr,Bool.false_or,Bool.false_and,ite_false]
  exact ⟨hw.1.trans (hk.1.trans hb.1),hw.2.trans (hk.2.trans hb.2)⟩


/-! Responder leadership is monotone through the comparison prefix. Unlike
control framing, CHECK/BEQ may set this field, so their lemmas are one-way. -/
namespace Leaders
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


private theorem suppress_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (suppressSigResetKill hψ l r).1) = (view l) ∧
    (view (suppressSigResetKill hψ l r).2) = (view r) := by
  cases h1 : l.leader <;> cases h2 : l.reset_cmd <;>
    cases h3 : r.reset_cmd <;> cases h4 : r.echo <;>
    simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
      suppressSigTerminal, suppressSigEcho, suppressSigFinish, clearCmp,
      view, control,h1,h2,h3,h4,fst_ite,snd_ite,leader_ite,label_ite,probe_ite]

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
private theorem forward_true {ψ : Nat} (κ : Nat) (u : AgentState ψ)
    (hu : u.leader = true) : (landForward κ false true u).leader = true := by
  cases hp : u.path <;> cases ht : u.path2 <;>
    simp [landForward,hp,ht,leader_ite,hu]
private theorem checkSource_true {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ)
    (hr : r.leader = true) : (checkSource hp l r).2.leader = true := by
  change view (checkSource hp l r).2 = true
  simp only [checkSource,snd_ite,view_ite,result_view,checkR_view,checkReady_view]
  simp [view,leader_ite,hr]
private theorem compare_true {ψ : Nat} (κ : Nat) (l r : AgentState ψ)
    (hr : r.leader = true) : (compareLifecycle κ l r).2.leader = true := by
  simp only [compareLifecycle]
  apply forward_true
  change view _ = true
  simp only [(dropStray_views _ _).2,(wave_views _ _).2,(completeWave_views _ _).2,(maintain_views _ _).2]
  exact hr
/-- A responder leader produced by P′ survives all ReadyAck comparison stages. -/
theorem before_true {ψ : Nat} (hp : ψ > 0) (κ : Nat) (l r : AgentState ψ)
    (hr : (pPsiProbeWall hp l r).2.leader = true) :
    (PPLLAstraDesign3.beforeElimination hp κ .readyAck l r).2.leader = true := by
  simp only [PPLLAstraDesign3.beforeElimination,reduceCtorEq,or_true,or_false,decide_true,ite_true,ite_false]
  change view _ = true
  rw [(suppress_views _ _ _).2]
  apply compare_true
  change view _ = true
  rw [(repair_views _ _).2,(disappear_views _ _ _).2]
  apply checkSource_true
  change view _ = true
  simp only [ready_view,(reset_views _ _).2,drop_view,(moveSource_views _ _ _).2,
    (eliminate_views _ _ _).2,(releaseSource_views _ _ _).2,(cleanSource_views _ _ _).2,(gen_views _ _ _ _).2]
  exact hr
end Leaders


private theorem leader_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).leader = if p then a.leader else b.leader := by split <;> rfl
private theorem kernel_right {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    (k4Kernel hp l r).2.leader = r.leader ∧ (k4Kernel hp l r).2.label = r.label := by
  simp only [k4Kernel,k3Kernel,eliminateLeadersNoCollisionFire,absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink,dummyBulletSink]
  simp only [fst_ite,snd_ite,leader_ite,label_ite,ite_self,and_self]
attribute [local irreducible] PPLLAstraDesign3.beforeElimination
/-- A zero-label responder leader at the actual P′ cut survives complete
ReadyAck, for arbitrary κ and all ancillary fields. This directly includes
P′ probe births; no comparison cleanliness or active-source premise is used. -/
theorem pipeline_pPsi_responder_survives {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) (hr : (pPsiProbeWall hp l r).2.leader = true)
    (hz : (pPsiProbeWall hp l r).2.label.val = 0) :
    (PPLLAstraDesign3.pipeline hp κ .readyAck l r).2.leader = true := by
  have qr := Leaders.before_true hp κ l r hr
  have qz := congrArg Prod.fst (before_control hp κ l r).2
  change (PPLLAstraDesign3.beforeElimination hp κ .readyAck l r).2.label = (pPsiProbeWall hp l r).2.label at qz
  simp only [PPLLAstraDesign3.pipeline]
  generalize he : PPLLAstraDesign3.beforeElimination hp κ .readyAck l r = q at *
  have hk := kernel_right hp q.1 q.2
  generalize hkdef : k4Kernel hp q.1 q.2 = k at *
  have kr : k.2.leader = true := hk.1.trans qr
  have kz : k.2.label = ⟨0,hp⟩ := by
    apply Fin.ext
    rw [hk.2,qz]
    exact hz
  have wr := PPLLVerify.writeSeq_responder_leader_of_label_zero hp k.1 k.2 kr kz
  have wb : (writeWithBundle hp k.1 k.2).2.leader = true := by
    simp only [writeWithBundle,snd_ite,leader_ite,wr,ite_self]
  simp [conserve,wb]
/-- If a follower pair finishes ReadyAck with a follower responder, then the
input had no probe barrier: either no responder probe or successor alignment.
Together with the exact control projection this is the universal zero-row
interface needed for the three-site mismatch schedule. -/
theorem pipeline_zero_no_probe_barrier {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) (hl : l.leader = false) (hr : r.leader = false)
    (hout : (PPLLAstraDesign3.pipeline hp κ .readyAck l r).2.leader = false) :
    r.probe = false ∨ r.label = ⟨(l.label.val + 1) % ψ,Nat.mod_lt _ hp⟩ := by
  cases hpr : r.probe
  · exact Or.inl rfl
  · right
    by_cases hne : r.label = ⟨(l.label.val + 1) % ψ,Nat.mod_lt _ hp⟩
    · exact hne
    apply False.elim
    have hbirth : (pPsiProbeWall hp l r).2.leader = true := by
      simp [pPsiProbeWall,pPsi,hl,hr,hpr,hne]
    have hzero : (pPsiProbeWall hp l r).2.label.val = 0 := by
      simp [pPsiProbeWall,pPsi,hl,hr,hpr,hne]
    have hs := pipeline_pPsi_responder_survives hp κ l r hbirth hzero
    simp [hout] at hs
#print axioms pipeline_followers_control
#print axioms pipeline_pPsi_responder_survives
#print axioms pipeline_zero_no_probe_barrier
end PPLLAstraReadyThree
