import Leader.Wu.ZeroDivisible.CheckRepair

/-! Corrected one-row terminal drainage for the actual R5 pipeline.
The predecessor cannot be produce. All other raw fields, including both
leader bits, are unrestricted. No bounded reification is used. -/
namespace PPLLAstraR5TerminalDrain
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3
set_option autoImplicit false
set_option linter.unusedSimpArgs false

private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by split <;> rfl
private theorem state_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).state = if p then a.state else b.state := by split <;> rfl
private theorem label_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).label = if p then a.label else b.label := by split <;> rfl

namespace Prefix
private def view {ψ : Nat} (u : AgentState ψ) := (u.label,u.state)
private theorem view_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    view (if p then a else b) = if p then view a else view b := by split <;> rfl
private theorem path4_view {ψ : Nat} (u : AgentState ψ) : view {u with path4 := none} = view u := rfl
private theorem path5_view {ψ : Nat} (u : AgentState ψ) : view {u with path5 := none} = view u := rfl

private theorem pPsi_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ)
    (hn : r.label = ⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩) :
    view (pPsiProbeWall hp l r).1 = view l ∧ view (pPsiProbeWall hp l r).2 = view r := by
  simp [pPsiProbeWall,pPsi,fst_ite,snd_ite,view_ite,view,label_ite,state_ite,hn]

private theorem wait_views {ψ : Nat} (hp : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    view (waitSaturated hp κ l r).1 = view l ∧
    view (waitSaturated hp κ l r).2 = view r := by
  simp only [waitSaturated,waitSaturatedPrepare,waitSaturatedCarry,waitSaturatedReset,waitSaturatedFinish]
  simp only [fst_ite,snd_ite,view_ite,view,label_ite,state_ite,ite_self,and_self]

private theorem gen_views {ψ : Nat} (hp : ψ > 0) (κ : Nat) (l r : AgentState ψ)
    (hl : l.label ≠ ⟨0,hp⟩) (hs : l.state ≠ .produce) (hr : r.state = .eliminate_signal) :
    view (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).1 = view l ∧
    view (PPLLFableZDiv.genSigOverwrite hp κ true 0 l r).2 = view r := by
  have hw := wait_views hp κ l r
  simp only [view,Prod.mk.injEq] at hw
  simp only [PPLLFableZDiv.genSigOverwrite]
  generalize he : waitSaturated hp κ l r = q at *
  have hl' : q.1.label ≠ ⟨0,hp⟩ := by rw [hw.1.1]; exact hl
  have hs' : q.1.state ≠ .produce := by rw [hw.1.2]; exact hs
  have hr' : q.2.state = .eliminate_signal := hw.2.2.trans hr
  simp [hl,hs,hr,hl',hs',hr',genSigSaturatedEmit,genSigSaturatedPropagate,genSigSaturatedFinish,
    view,hw.1.1,hw.1.2,hw.2.1,hw.2.2]
private theorem cleanSigGenConnect_view {ψ : Nat} (u : AgentState ψ) :
    (view (cleanSigGenConnect u)) = (view u) := by
  cases h : u.path <;>
    simp only [cleanSigGenConnect, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem cleanSigCleanApply_view {ψ : Nat} (u : AgentState ψ) :
    (view (cleanSigCleanApply u)) = (view u) := by
  cases h : u.path <;> cases h4 : u.path4 <;> cases h5 : u.path5 <;>
    simp only [cleanSigCleanApply, h, h4, h5] <;>
    (repeat split) <;> simp_all [view_ite, view, label_ite, state_ite]

private theorem clean3_views {ψ : Nat} (l r : AgentState ψ) :
    (view (cleanSigStep3 l r).1) = (view l) ∧
    (view (cleanSigStep3 l r).2) = (view r) := by
  cases h : r.path4 <;> cases hp : l.path <;> simp only [cleanSigStep3, h, hp] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem clean4_views {ψ : Nat} (l r : AgentState ψ) :
    (view (cleanSigStep4 l r).1) = (view l) ∧
    (view (cleanSigStep4 l r).2) = (view r) := by
  cases h : l.path5 <;> cases hp : r.path <;> simp only [cleanSigStep4, h, hp] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem clean5_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (cleanSigStep5 hψ l r).1) = (view l) ∧
    (view (cleanSigStep5 hψ l r).2) = (view r) := by
  cases h : r.path4 <;> simp only [cleanSigStep5, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem clean6_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (cleanSigStep6 hψ l r).1) = (view l) ∧
    (view (cleanSigStep6 hψ l r).2) = (view r) := by
  cases h : l.path5 <;> simp only [cleanSigStep6, h] <;>
    simp [fst_ite, snd_ite, view_ite, view, label_ite, state_ite]

private theorem clean_views {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (view (cleanSig hψ l r).1) = (view l) ∧
    (view (cleanSig hψ l r).2) = (view r) := by
  simp only [cleanSig]
  simp only [cleanSigGenConnect_view, cleanSigCleanApply_view,
    (clean3_views _ _).1, (clean3_views _ _).2,
    (clean4_views _ _).1, (clean4_views _ _).2,
    (clean5_views _ _ _).1, (clean5_views _ _ _).2,
    (clean6_views _ _ _).1, (clean6_views _ _ _).2, and_self]

private theorem cleanSource_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (cleanSource hp l r).1 = view l ∧ view (cleanSource hp l r).2 = view r := by
  simp only [cleanSource]
  simp only [fst_ite,snd_ite,view_ite,path4_view,path5_view,cleanSigGenConnect_view,cleanSigCleanApply_view,
    (clean3_views _ _).1,(clean3_views _ _).2,(clean4_views _ _).1,(clean4_views _ _).2,
    (clean5_views _ _ _).1,(clean5_views _ _ _).2,(clean6_views _ _ _).1,(clean6_views _ _ _).2,ite_self,and_self]

/-- P-prime, WAIT/GEN and CLEAN leave the pending terminal signal available. -/
theorem before_eliminate {ψ : Nat} (hp : ψ > 0) (κ : Nat) (l r : AgentState ψ)
    (hψ : 4 ≤ ψ) (hl : l.label.val = ψ-2) (hr : r.label.val = ψ-1)
    (hs : l.state ≠ .produce) (he : r.state = .eliminate_signal) :
    let q := pPsiProbeWall hp l r
    let q := PPLLFableZDiv.genSigOverwrite hp κ true 0 q.1 q.2
    let q := cleanSource hp q.1 q.2
    let q := releaseSource hp q.1 q.2
    q.1.label.val = ψ-2 ∧ q.2.state = .eliminate_signal := by
  dsimp only
  have hn : r.label = ⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩ := by
    apply Fin.ext
    simp only [hl,hr]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hpv := pPsi_views hp l r hn
  generalize hpp : pPsiProbeWall hp l r = p at *
  simp only [view,Prod.mk.injEq] at hpv
  have hp0 : p.1.label ≠ ⟨0,hp⟩ := by
    intro h; have := congrArg Fin.val h
    rw [hpv.1.1,hl] at this
    simp only [Fin.val_zero] at this
    omega
  have hgs := gen_views hp κ p.1 p.2 hp0 (by rw [hpv.1.2]; exact hs) (hpv.2.2.trans he)
  generalize hgen : PPLLFableZDiv.genSigOverwrite hp κ true 0 p.1 p.2 = g at *
  have hcl := cleanSource_views hp g.1 g.2
  generalize hclean : cleanSource hp g.1 g.2 = z at *
  simp only [view,Prod.mk.injEq] at hgs hcl
  have hz : z.2.state = .eliminate_signal := hcl.2.2.trans (hgs.2.2.trans (hpv.2.2.trans he))
  have hzlab : z.1.label = l.label := hcl.1.1.trans (hgs.1.1.trans hpv.1.1)
  simp [releaseSource,hz,hzlab,hl]
end Prefix

namespace Paths
private def view {ψ : Nat} (u : AgentState ψ) := u.path
private theorem view_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    view (if p then a else b) = if p then view a else view b := by split <;> rfl
private theorem state_view {ψ : Nat} (u : AgentState ψ) (s : MainState) :
    view {u with state := s} = view u := rfl
private theorem leader_view {ψ : Nat} (u : AgentState ψ) (b : Bool) :
    view {u with leader := b} = view u := rfl
theorem moveTokens_views {ψ : Nat} (l r : AgentState ψ) :
    (view (moveTokens l r).1) = (view l) ∧
    (view (moveTokens l r).2) = (view r) := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [moveTokens, hl, hr] <;> simp [fst_ite, snd_ite, view_ite, view, path_ite]

theorem control_view {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (view (sigMoveApplyControlConsume hψ u)) = (view u) := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;> simp [fst_ite, snd_ite, view_ite, view, path_ite]

private theorem orphan_view {ψ : Nat} (u : AgentState ψ) : view (normalizeOrphan u) = view u := by
  cases h : u.path <;> simp [normalizeOrphan,h,view_ite,view,path_ite]
private theorem carrier_view {ψ : Nat} (u : AgentState ψ) : view (normalizeCarrier u) = view u := by
  cases h : u.path <;> simp [normalizeCarrier,releaseCongest,h,view_ite,view,path_ite]
private theorem ready_view {ψ : Nat} (u : AgentState ψ) : view (normalizeReady u) = view u := by
  generalize ho : normalizeOrphan u = o
  have vo : view o = view u := by rw [←ho];exact orphan_view u
  simp only [normalizeReady,ho]
  generalize hc : (if o.state = .none ∧ aligned o then o else normalizeCarrier o) = c
  have vc : view c = view o := by rw [←hc];simp [view_ite,carrier_view]
  have ht := vc.trans vo
  cases hp : c.path <;> simpa [hp,view_ite,view,path_ite] using ht
private theorem checkReady_view {ψ : Nat} (u : AgentState ψ) : view (checkSigSetReadyGuarded u) = view u := by
  cases h : u.path <;> simp [checkSigSetReadyGuarded,checkSigSetReady,h,view_ite,view,path_ite]
private theorem checkL_view {ψ : Nat} (hp : ψ > 0) (u : AgentState ψ) : view (checkSigCheckL hp u) = view u := by
  unfold checkSigCheckL
  split <;> simp [view_ite,view,path_ite]
private theorem checkR_view {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) : view (checkSigCheckR hp l r) = view r := by
  unfold checkSigCheckR
  split <;> simp [view_ite,view,path_ite]
private theorem result_view {ψ : Nat} (u : AgentState ψ) : view (checkSigSetResult u) = view u := by
  simp [checkSigSetResult,view_ite,view,path_ite]
private theorem guarded_result_view {ψ : Nat} (c : PPLLAstraR5Repair.Cfg) (u : AgentState ψ) :
    view (PPLLAstraR5Repair.setResult c u) = view u := by
  simp only [PPLLAstraR5Repair.setResult,view_ite,result_view,ite_self]
private theorem releaseEqual_view {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (PPLLAstraR5Repair.releaseEqual hp l r) = view l := by
  cases hl : l.path <;> cases hr : r.path <;> simp [PPLLAstraR5Repair.releaseEqual,hl,hr,view_ite,view,path_ite]

private theorem checkSource_views {ψ : Nat} (hp : ψ > 0) (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ) :
    view (PPLLAstraR5Repair.checkSource hp c l r).1 = view l ∧ view (PPLLAstraR5Repair.checkSource hp c l r).2 = view r := by
  simp only [PPLLAstraR5Repair.checkSource]
  simp only [fst_ite,snd_ite,view_ite,leader_view,state_view,guarded_result_view,releaseEqual_view,checkL_view,checkR_view,checkReady_view,ite_self,and_self]

private theorem disappear_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    view (disappear hp l r).1 = view l ∧ view (disappear hp l r).2 = view r := by
  simp [disappear,fst_ite,snd_ite,view_ite,view,path_ite]
private theorem release_views {ψ : Nat} (l r : AgentState ψ) :
    view (releaseReadySuffix l r).1 = view l ∧ view (releaseReadySuffix l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [releaseReadySuffix,hl,hr,fst_ite,snd_ite,view_ite,view,path_ite]
private theorem ack_views {ψ : Nat} (l r : AgentState ψ) :
    view (ackTail l r).1 = view l ∧ view (ackTail l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [ackTail,hl,hr,fst_ite,snd_ite,view_ite,view,path_ite]
private theorem repair_views {ψ : Nat} (l r : AgentState ψ) :
    view (repair .readyAck l r).1 = view l ∧ view (repair .readyAck l r).2 = view r := by
  simp only [repair,(ack_views _ _).1,(ack_views _ _).2,(release_views _ _).1,(release_views _ _).2,carrier_view,orphan_view,and_self]
private theorem maintain_views {ψ : Nat} (l r : AgentState ψ) :
    view (maintain l r).1 = view l ∧ view (maintain l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [maintain,hl,hr,fst_ite,snd_ite,view_ite,view,path_ite]
private theorem completeWave_views {ψ : Nat} (l r : AgentState ψ) :
    view (completeWave l r).1 = view l ∧ view (completeWave l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [completeWave,hl,hr,fst_ite,snd_ite,view_ite,view,path_ite]
private theorem wave_views {ψ : Nat} (l r : AgentState ψ) :
    view (wave l r).1 = view l ∧ view (wave l r).2 = view r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [wave,hl,hr,fst_ite,snd_ite,view_ite,view,path_ite]
private theorem dropStray_views {ψ : Nat} (l r : AgentState ψ) :
    view (dropStray l r).1 = view l ∧ view (dropStray l r).2 = view r := by
  cases hl : l.path2 <;> cases hr : r.path2 <;> simp [dropStray,hl,hr,fst_ite,snd_ite,view_ite,view,path_ite]
private theorem landBackward_view {ψ : Nat} (u : AgentState ψ) : view (landBackward u) = view u := by
  cases hp : u.path <;> cases ht : u.path2 <;> simp [landBackward,hp,ht,view_ite,view,path_ite]
private theorem landForward_view {ψ : Nat} (κ : Nat) (u : AgentState ψ) : view (landForward κ false true u) = view u := by
  cases hp : u.path <;> cases ht : u.path2 <;> simp [landForward,hp,ht,view_ite,view,path_ite]
private theorem compare_views {ψ : Nat} (κ : Nat) (l r : AgentState ψ) :
    view (compareLifecycle κ l r).1 = view l ∧ view (compareLifecycle κ l r).2 = view r := by
  simp only [compareLifecycle,landBackward_view,landForward_view,
    (dropStray_views _ _).1,(dropStray_views _ _).2,(wave_views _ _).1,(wave_views _ _).2,
    (completeWave_views _ _).1,(completeWave_views _ _).2,(maintain_views _ _).1,(maintain_views _ _).2]
  cases hp : l.path <;> simp [hp,view_ite,view,path_ite]

private theorem clear_path {ψ : Nat} (u : AgentState ψ) : (clearCmp u).path=.bot := rfl
private theorem tokens_r_path {ψ : Nat} (l r : AgentState ψ) :
    (moveTokens l r).2.path = r.path := (moveTokens_views l r).2
private theorem control_path {ψ : Nat} (hp : ψ > 0) (u : AgentState ψ) :
    (sigMoveApplyControlConsume hp u).path = u.path := control_view hp u

/-- A propagated elimination marker blocks refill; leader preclears only help. -/
theorem move_r_bot {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ)
    (hl : l.state = .eliminate_signal) (hr : r.path = .bot) :
    (PPLLFableZDiv.moveSourceF hp PPLLAstraR5Repair.sourceCfg l r).2.path = .bot := by
  let a := if l.leader = true ∨ (r.leader = true ∧ r.label ≠
      ⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩) then clearCmp l else l
  let b := if r.leader = true then clearCmp r else r
  have ha : a.path=.bot ∨ a.state=.eliminate_signal := by
    dsimp only [a]; split
    · exact Or.inl rfl
    · exact Or.inr hl
  have hb : b.path=.bot := by simp only [b,path_ite,clear_path,hr,ite_self]
  let q := if a.state=.done then (a,b)
    else PPLLFableZDiv.sigMoveStep1F PPLLAstraR5Repair.sourceCfg a b
  have hq : q.2.path=.bot := by
    dsimp only [q]; split
    · exact hb
    · rcases ha with ha | ha
      · simp [PPLLFableZDiv.sigMoveStep1F,ha,hb]
      · cases hap : a.path <;>
          simp [PPLLFableZDiv.sigMoveStep1F,hap,hb,ha,
            PPLLAstraR5Repair.sourceCfg,PPLLFableZDiv.outcomePending,blockingState]
  change (sigMoveApplyControlConsume hp
    (leaderWall (moveTokens q.1 q.2).1 (moveTokens q.1 q.2).2).2).path=.bot
  rw [control_path]
  simp only [leaderWall,path_ite,clear_path,tokens_r_path,hq,ite_self]

private theorem drop_bot {ψ : Nat} (u : AgentState ψ) (h : u.path=.bot) :
    (dropStale u).path=.bot := by simp [dropStale,h]
private theorem reset_r_bot {ψ : Nat} (l r : AgentState ψ) (h : r.path=.bot) :
    (preCheckReset l r).2.path=.bot := by simp [preCheckReset,path_ite,clearCmp,h]
private theorem suppressStart_r_path {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigStart l r).2.path=r.path := by simp [suppressSigStart,snd_ite,path_ite]
private theorem suppressMove_r_path {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigMoveReset l r).2.path=r.path := by simp [suppressSigMoveReset,snd_ite,path_ite]
private theorem suppressTerminal_r_path {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    (suppressSigTerminal hp l r).2.path=r.path := by simp [suppressSigTerminal,snd_ite,path_ite]
private theorem suppressEcho_r_path {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigEcho l r).2.path=r.path := by simp [suppressSigEcho,snd_ite,path_ite]
private theorem suppressFinish_r_path {ψ : Nat} (l r : AgentState ψ) :
    (suppressSigFinish l r).2.path=r.path := rfl
private theorem suppress_r_bot {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) (h : r.path=.bot) :
    (suppressSigResetKill hp l r).2.path=.bot := by
  simp only [suppressSigResetKill,suppressFinish_r_path,suppressEcho_r_path,
    suppressTerminal_r_path,suppressMove_r_path,suppressStart_r_path,
    path_ite,clear_path,h,ite_self]

/-- Every stage after movement through suppression preserves a responder hole. -/
theorem post_move_r_bot {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ) (h : r.path=.bot) :
    let q := (dropStale l,dropStale r)
    let q := preCheckReset q.1 q.2
    let q := (normalizeReady q.1,normalizeReady q.2)
    let q := PPLLAstraR5Repair.checkSource hp c q.1 q.2
    let q := disappear hp q.1 q.2
    let q := repair .readyAck q.1 q.2
    let q := compareLifecycle κ q.1 q.2
    (suppressSigResetKill hp q.1 q.2).2.path = .bot := by
  apply suppress_r_bot
  change view _ = .bot
  simp only [(compare_views _ _ _).2,(repair_views _ _).2,(disappear_views _ _ _).2,
    (checkSource_views _ _ _ _).2,ready_view]
  exact reset_r_bot _ _ (drop_bot r h)
end Paths
namespace Writer
private def Frame {ψ : Nat} (a b : AgentState ψ) : Prop :=
  a.path = b.path ∧ a.path2 = b.path2 ∧ a.state = b.state

private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by split <;> rfl
private theorem path2_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).path2 = if p then a.path2 else b.path2 := by split <;> rfl
private theorem state_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).state = if p then a.state else b.state := by split <;> rfl

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
    simp [path_ite, path2_ite, state_ite, hp]

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
    simp only [fst_ite, snd_ite, path_ite, path2_ite, state_ite, ite_self, and_self]

private theorem groupInfo_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (groupInfo hψ l r).1 l ∧ Frame (groupInfo hψ l r).2 r := by
  simp only [Frame, groupInfo]
  simp only [fst_ite, snd_ite, path_ite, path2_ite, state_ite, ite_self, and_self]

private theorem gensigWriteseq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (gensigWriteseq hψ l r).1 l ∧ Frame (gensigWriteseq hψ l r).2 r := by
  simp only [Frame, gensigWriteseq]
  simp only [fst_ite, snd_ite, path_ite, path2_ite, state_ite, ite_self, and_self]

private theorem writeAction_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (writeAction hψ l r).1 l ∧ Frame (writeAction hψ l r).2 r := by
  simp only [Frame, writeAction]
  simp only [fst_ite, snd_ite, path_ite, path2_ite, state_ite, ite_self, and_self , (writeActionApplyOverwrite_frame _).1, (writeActionApplyOverwrite_frame _).2.1, (writeActionApplyOverwrite_frame _).2.2, (writeActionApplyMoveFlip_frame _).1, (writeActionApplyMoveFlip_frame _).2.1, (writeActionApplyMoveFlip_frame _).2.2]

private theorem moveWsig_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (moveWsig hψ l r).1 l ∧ Frame (moveWsig hψ l r).2 r := by
  simp only [Frame, moveWsig]
  simp only [fst_ite, snd_ite, path_ite, path2_ite, state_ite, ite_self, and_self , (moveWsigCheckGenWs_frame _ _).1, (moveWsigCheckGenWs_frame _ _).2.1, (moveWsigCheckGenWs_frame _ _).2.2, (moveWsigCheckLast_frame _).1, (moveWsigCheckLast_frame _).2.1, (moveWsigCheckLast_frame _).2.2, (moveWsigTransfer_frame _ _).1.1, (moveWsigTransfer_frame _ _).1.2.1, (moveWsigTransfer_frame _ _).1.2.2, (moveWsigTransfer_frame _ _).2.1, (moveWsigTransfer_frame _ _).2.2.1, (moveWsigTransfer_frame _ _).2.2.2]

private theorem writeSeq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    Frame (writeSeq hψ l r).1 l ∧ Frame (writeSeq hψ l r).2 r := by
  simp only [Frame, writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands]
  simp only [fst_ite, snd_ite, path_ite, path2_ite, state_ite, ite_self, and_self, (groupInfo_frame _ _ _).1.1, (groupInfo_frame _ _ _).1.2.1, (groupInfo_frame _ _ _).1.2.2, (groupInfo_frame _ _ _).2.1, (groupInfo_frame _ _ _).2.2.1, (groupInfo_frame _ _ _).2.2.2, (gensigWriteseq_frame _ _ _).1.1, (gensigWriteseq_frame _ _ _).1.2.1, (gensigWriteseq_frame _ _ _).1.2.2, (gensigWriteseq_frame _ _ _).2.1, (gensigWriteseq_frame _ _ _).2.2.1, (gensigWriteseq_frame _ _ _).2.2.2, (writeAction_frame _ _ _).1.1, (writeAction_frame _ _ _).1.2.1, (writeAction_frame _ _ _).1.2.2, (writeAction_frame _ _ _).2.1, (writeAction_frame _ _ _).2.2.1, (writeAction_frame _ _ _).2.2.2, (moveWsig_frame _ _ _).1.1, (moveWsig_frame _ _ _).1.2.1, (moveWsig_frame _ _ _).1.2.2, (moveWsig_frame _ _ _).2.1, (moveWsig_frame _ _ _).2.2.1, (moveWsig_frame _ _ _).2.2.2, (writeSeqSetWriteReady_frame _).1, (writeSeqSetWriteReady_frame _).2.1, (writeSeqSetWriteReady_frame _).2.2, (writeSeqCheckBit_frame _).1, (writeSeqCheckBit_frame _).2.1, (writeSeqCheckBit_frame _).2.2, (writeSeqSetWriteAct_frame _).1, (writeSeqSetWriteAct_frame _).2.1, (writeSeqSetWriteAct_frame _).2.2, (writeSeqFinalR_frame _).1, (writeSeqFinalR_frame _).2.1, (writeSeqFinalR_frame _).2.2]


private theorem write_paths {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    (writeWithBundle hp l r).2.path = r.path := by
  simp only [writeWithBundle,snd_ite,path_ite,(writeSeq_frame hp l r).2.1,ite_self]
end Writer

private theorem kernel_r_path {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    (k4Kernel hp l r).2.path = r.path := by
  simp only [k4Kernel,k3Kernel,eliminateLeadersNoCollisionFire,absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink,dummyBulletSink]
  simp [fst_ite,snd_ite,path_ite]

/-- K4/WRITE and emergency conservation cannot restore a responder path. -/
theorem suffix_r_bot {ψ : Nat} (hp : ψ > 0) (oldl oldr l r : AgentState ψ)
    (h : r.path=.bot) :
    let q := k4Kernel hp l r
    let q := writeWithBundle hp q.1 q.2
    (conserve .head oldl oldr q).2.path = .bot := by
  simp only [conserve,replacement,clearCmp,snd_ite,path_ite,
    Writer.write_paths,kernel_r_path,h,ite_self]

-- Keep stage bodies opaque during composition; the frame lemmas above carry
-- the needed projections without expanding the entire transition expression.
attribute [local irreducible] pPsiProbeWall PPLLFableZDiv.genSigOverwrite
  cleanSource releaseSource PPLLFableZDiv.moveSourceF dropStale preCheckReset
  normalizeReady PPLLAstraR5Repair.checkSource disappear repair compareLifecycle
  suppressSigResetKill k4Kernel writeWithBundle conserve

private theorem eliminate_views {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ)
    (hψ : 4 ≤ ψ) (hl : l.label.val = ψ-2) (hr : r.state=.eliminate_signal) :
    (eliminateSig hp l r).1.state=.eliminate_signal ∧
    (eliminateSig hp l r).2.path=.bot := by
  have hne : l.label ≠ ⟨ψ-1,by omega⟩ := by
    intro hh
    have hh' := congrArg Fin.val hh
    rw [hl] at hh'
    simp only at hh'
    omega
  simp [eliminateSig,hr,hne]

attribute [local irreducible] eliminateSig

/-- Corrected terminal drain D1 for both guards, with arbitrary raw ancillary
fields and arbitrary input leaders. Main-path payloads need not be aligned. -/
theorem terminal_drain {ψ : Nat} (hp : ψ > 0) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ)
    (hψ : 4 ≤ ψ) (hl : l.label.val = ψ-2) (hr : r.label.val = ψ-1)
    (he : r.state = .eliminate_signal) (hs : l.state ≠ .produce) :
    (PPLLAstraR5Repair.pipeline hp κ c l r).2.path = .bot := by
  have hpre := Prefix.before_eliminate hp κ l r hψ hl hr hs he
  dsimp only at hpre
  simp only [PPLLAstraR5Repair.pipeline]
  apply suffix_r_bot
  simp only [PPLLAstraR5Repair.beforeElimination]
  apply Paths.post_move_r_bot
  apply Paths.move_r_bot
  · exact (eliminate_views hp _ _ hψ hpre.1 hpre.2).1
  · exact (eliminate_views hp _ _ hψ hpre.1 hpre.2).2

#print axioms terminal_drain
#print axioms Prefix.before_eliminate
#print axioms Paths.move_r_bot
#print axioms Paths.post_move_r_bot
#print axioms suffix_r_bot
end PPLLAstraR5TerminalDrain
