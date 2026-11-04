import Leader.Wu.ZeroDivisible.HeadFreshStable
import Leader.Wu.Elimination.OutputSafety
import Leader.Wu.ZeroDivisible.LockCycleRepairs
import Leader.Wu.ZeroDivisible.HeadResetWord
/-! Physical elimination safety for the frozen Head fresh-comparison sector.
The observation is the repository's existing K2 RowSafe, not a protocol change. -/
namespace PPLLAstraFreshStableRow
open PPLL PPLLRepair PPLLPostElectionGuard PPLLAstraDesign2
  PPLLNoCheckBirthConditionTwoPhysical K2OutputSafety LDSinkKernelC
  PPLLBirthPatch PPLLBirthPatchM2 PPLLFableDesignR1
  PPLLNoCheckBirthConditionTwoFrames PPLLNoCheckBirthBoundaryFrames
private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1=if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2=if p then a.2 else b.2 := by split <;> rfl
private theorem leader_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).leader=if p then a.leader else b.leader := by split <;> rfl
/-- On a pair with at most one leader, and no unshielded live-bullet target,
the actual K4 stage is exactly the existing K2 kernel, including all state fields. -/
theorem k4_eq_sink {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (hone : ¬(l.leader=true ∧ r.leader=true))
    (hshield : l.leader=true → r.bullet=2 → l.shield=true) :
    k4Kernel hp l r=sinkKernelC hp l r := by
  have hkill : ¬(r.bullet=2 ∧ l.leader=true ∧ l.shield=false) := by
    rintro ⟨hb,hl,hs⟩
    have ht := hshield hl hb
    simp [hs] at ht
  let f := eliminateLeadersNoCollisionFire hp l r
  have hf : f.1.leader=l.leader ∧ f.2.leader=r.leader := by
    simp only [f,eliminateLeadersNoCollisionFire,leader_ite,ite_self,and_self]
  have hmove : absorbAnyMove hp ⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩ f.1 f.2 =
      absorbProtectedMove hp ⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩ f.1 f.2 := by
    by_cases hl : f.1.leader=true
    · have hr : f.2.leader=false := by
        cases h : f.2.leader
        · rfl
        · exact False.elim (hone ⟨hf.1.symm.trans hl,hf.2.symm.trans h⟩)
      simp [absorbAnyMove,absorbProtectedMove,hr]
    · simp [absorbAnyMove,absorbProtectedMove,hl]
  simpa only [k4Kernel,if_neg hkill,k3Kernel,sinkKernelC] using
    congrArg (fun q => dummyBulletSink
      (eliminateLeadersNoCollisionSignalLeaderSink
        ⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩ q.1 q.2)) hmove
/-- A live bullet anywhere forces the unique RowSafe leader to be shielded.
The distance-zero bullet case is included by the existing peacefulness definition. -/
theorem rowSafe_live_shield {ψ n : Nat} (hp : ψ>0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : RowSafe hp ring C) (i j : Fin n)
    (hi : (C i).leader=true) (hj : (C j).bullet=2) : (C i).shield=true := by
  obtain ⟨root,hroot,hu⟩ := hC.1.unique_leader
  have hpeace := hC.1.no_nonpeaceful_bullet j hj
  obtain ⟨_,d,hd,ht,hs,hz,hl⟩ := hpeace
  have heq := hu _ ht
  have hieq := hu i hi
  change (C ⟨(j.val+d)%n,Nat.mod_lt _ ring.hn⟩).shield=true at hs
  rw [heq,← hieq] at hs
  exact hs

/-! The prefix frames labels and the three non-geometric bullet fields.
Existing public frame APIs handle the unchanged printed stages. -/
namespace Passive
private def view {ψ : Nat} (u : AgentState ψ) := (u.label,BulletFields.ofState u)
private theorem pair_of_fields {ψ : Nat} (q : AgentState ψ × AgentState ψ) (l r : AgentState ψ)
    (hl : q.1.label=l.label ∧ q.2.label=r.label)
    (hb : bulletFieldPair q=bulletFieldPair (l,r)) :
    view q.1=view l ∧ view q.2=view r := by
  change (BulletFields.ofState q.1, BulletFields.ofState q.2) =
    (BulletFields.ofState l, BulletFields.ofState r) at hb
  have hbl : BulletFields.ofState q.1=BulletFields.ofState l := congrArg Prod.fst hb
  have hbr : BulletFields.ofState q.2=BulletFields.ofState r := congrArg Prod.snd hb
  simp only [view,hl.1,hl.2,hbl,hbr,and_self]
private theorem gen_views {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ) :
    view (genSigSaturated hp κ l r).1=view l ∧ view (genSigSaturated hp κ l r).2=view r := by
  have h := genSigSaturated_labels hp κ l r
  exact pair_of_fields _ l r ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩
    (genSigSaturated_bulletFieldPair hp κ l r)
private theorem clean_views {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    view (cleanSig hp l r).1=view l ∧ view (cleanSig hp l r).2=view r :=
  pair_of_fields _ l r (PPLLVerify.cleanSig_labels_eq hp l r) (cleanSig_bulletFieldPair hp l r)
private theorem eliminate_views {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    view (eliminateSig hp l r).1=view l ∧ view (eliminateSig hp l r).2=view r :=
  pair_of_fields _ l r (PPLLVerify.eliminateSig_labels_eq hp l r) (eliminateSig_bulletFieldPair hp l r)
private theorem disappear_views {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    view (disappear hp l r).1=view l ∧ view (disappear hp l r).2=view r :=
  pair_of_fields _ l r (PPLLVerify.disappear_labels_eq hp l r) (disappear_bulletFieldPair hp l r)
private theorem label_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).label=if p then a.label else b.label := by split <;> rfl
private theorem shield_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).shield=if p then a.shield else b.shield := by split <;> rfl
private theorem bullet_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).bullet=if p then a.bullet else b.bullet := by split <;> rfl
private theorem signal_B_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).signal_B=if p then a.signal_B else b.signal_B := by split <;> rfl
private theorem view_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    view (if p then a else b)=if p then view a else view b := by split <;> rfl
private theorem step1_views {ψ : Nat} (l r : AgentState ψ) :
    (view (sigMoveStep1With .dropMisaligned l r).1) = (view l) ∧
    (view (sigMoveStep1With .dropMisaligned l r).2) = (view r) := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp only [sigMoveStep1With, hl, hr] <;> simp [fst_ite, snd_ite, view_ite, view,BulletFields.ofState, label_ite, shield_ite, bullet_ite, signal_B_ite]

private theorem moveTokens_views {ψ : Nat} (l r : AgentState ψ) :
    (view (moveTokens l r).1) = (view l) ∧
    (view (moveTokens l r).2) = (view r) := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp only [moveTokens, hl, hr] <;> simp [fst_ite, snd_ite, view_ite, view,BulletFields.ofState, label_ite, shield_ite, bullet_ite, signal_B_ite]

private theorem control_view {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) :
    (view (sigMoveApplyControlConsume hψ u)) = (view u) := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;> simp [fst_ite, snd_ite, view_ite, view,BulletFields.ofState, label_ite, shield_ite, bullet_ite, signal_B_ite]

private theorem clear_view {ψ : Nat} (u : AgentState ψ) : view (clearCmp u) = view u := rfl
private theorem state_view {ψ : Nat} (u : AgentState ψ) (s : MainState) :
    view { u with state := s } = view u := rfl
private theorem sig_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    view (sigMoveF hψ true .dropMisaligned l r).1 = view l ∧
    view (sigMoveF hψ true .dropMisaligned l r).2 = view r := by
  simp only [sigMoveF, fst_ite, snd_ite, view_ite, state_view,BulletFields.ofState, control_view,BulletFields.ofState,
    leaderWall, clear_view,BulletFields.ofState, (moveTokens_views _ _).1, (moveTokens_views _ _).2,
    (step1_views _ _).1, (step1_views _ _).2, ite_self, and_self]

private theorem drop_view {ψ : Nat} (u : AgentState ψ) :
    (view (dropStale u)) = (view u) := by
  simp only [dropStale]
  simp [view_ite, view,BulletFields.ofState, label_ite, shield_ite, bullet_ite, signal_B_ite]


private theorem suppress_views {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (view (suppressSigResetKill hψ l r).1) = (view l) ∧
    (view (suppressSigResetKill hψ l r).2) = (view r) := by
  cases h1 : l.leader <;> cases h2 : l.reset_cmd <;>
    cases h3 : r.reset_cmd <;> cases h4 : r.echo <;>
    simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
      suppressSigTerminal, suppressSigEcho, suppressSigFinish, clearCmp,
      view,BulletFields.ofState,h1,h2,h3,h4,fst_ite,snd_ite,label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem precheck_views {ψ : Nat} (l r : AgentState ψ) :
    view (preCheckReset l r).1=view l ∧ view (preCheckReset l r).2=view r := by
  simp only [preCheckReset,view_ite,clear_view,ite_self,and_self]
private theorem readyF_view {ψ : Nat} (u : AgentState ψ) : view (readyF u)=view u := by
  cases h : u.path <;> simp [readyF,checkSigSetReadyGuarded,checkSigSetReady,h,view,BulletFields.ofState,view_ite,
    label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem checkSigSetResult_view {ψ : Nat} (u : AgentState ψ) : view (checkSigSetResult u)=view u := by
  cases h : u.path <;> simp [checkSigSetResult,h,view,BulletFields.ofState,view_ite,
    label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem checkL_view {ψ : Nat} (hp : ψ>0) (u : AgentState ψ) :
    view (checkSigCheckL hp u)=view u := by
  cases h : u.path with
  | bot => simp [checkSigCheckL,h]
  | some k b =>
    cases k <;> simp [checkSigCheckL,h,view,BulletFields.ofState,
      label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem checkR_view {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    view (checkSigCheckR hp l r)=view r := by
  cases h : r.path <;> simp [checkSigCheckR,h,view,BulletFields.ofState,
    label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem check_views {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ) :
    view (checkSigF hp κ false l r).1=view l ∧ view (checkSigF hp κ false l r).2=view r := by
  have leader_view (u : AgentState ψ) (b : Bool) : view {u with leader := b}=view u := rfl
  simp only [checkSigF,Bool.not_false,Bool.true_or,ite_true,fst_ite,snd_ite,view_ite,leader_view,state_view,checkL_view,checkR_view,
    checkSigSetResult_view,readyF_view]
  simp only [view,BulletFields.ofState,label_ite,shield_ite,bullet_ite,signal_B_ite,ite_self,and_self]

private theorem init_view {ψ : Nat} (u : AgentState ψ) : view (compareSigInit u)=view u := by
  cases h : u.path <;> simp [compareSigInit,h,view,BulletFields.ofState]
private theorem maintain_views {ψ : Nat} (l r : AgentState ψ) :
    view (maintain l r).1=view l ∧ view (maintain l r).2=view r := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [maintain,hl,hr,fst_ite,snd_ite,view,BulletFields.ofState,
      label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem wave_views {ψ : Nat} (l r : AgentState ψ) :
    view (wave l r).1=view l ∧ view (wave l r).2=view r := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [wave,hl,hr,view,BulletFields.ofState,label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem stray_views {ψ : Nat} (l r : AgentState ψ) :
    view (dropStray l r).1=view l ∧ view (dropStray l r).2=view r := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [dropStray,hl,hr,view,BulletFields.ofState,label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem backward_view {ψ : Nat} (u : AgentState ψ) : view (landBackward u)=view u := by
  cases ht : u.path2 <;> cases hp : u.path <;>
    simp [landBackward,ht,hp,view,BulletFields.ofState,label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem forward_view {ψ : Nat} (κ : Nat) (u : AgentState ψ) :
    view (landForward κ false true u)=view u := by
  cases ht : u.path2 <;> cases hp : u.path <;>
    simp [landForward,ht,hp,view,BulletFields.ofState,label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem compare_views {ψ : Nat} (κ : Nat) (l r : AgentState ψ) :
    view (compareSigF κ false true l r).1=view l ∧ view (compareSigF κ false true l r).2=view r := by
  simp only [compareSigF,backward_view,forward_view,(stray_views _ _).1,(stray_views _ _).2,
    (wave_views _ _).1,(wave_views _ _).2,(maintain_views _ _).1,(maintain_views _ _).2,
    init_view,and_self]
private theorem pprime_views {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (ha : r.label=⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩ ∨ r.leader=true) :
    view (pPsiProbeWall hp l r).1=view l ∧ view (pPsiProbeWall hp l r).2=view r := by
  rcases ha with ha | ha
  · cases hl : l.leader <;> cases hr : r.leader <;> cases hb : r.probe <;>
      simp [pPsiProbeWall,pPsi,ha,hl,hr,hb,view,BulletFields.ofState]
  · cases hl : l.leader <;> simp [pPsiProbeWall,pPsi,ha,hl,view,BulletFields.ofState,
      fst_ite,snd_ite,label_ite,shield_ite,bullet_ite,signal_B_ite]
attribute [local irreducible] view
private theorem before_views {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ)
    (ha : r.label=⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩ ∨ r.leader=true) :
    view (beforeElimination hp κ l r).1=view l ∧ view (beforeElimination hp κ l r).2=view r := by
  simp only [beforeElimination,(suppress_views _ _ _).1,(suppress_views _ _ _).2,
    (compare_views _ _ _).1,(compare_views _ _ _).2,(disappear_views _ _ _).1,(disappear_views _ _ _).2,
    (check_views _ _ _ _).1,(check_views _ _ _ _).2,(precheck_views _ _).1,(precheck_views _ _).2,
    drop_view,(sig_views _ _ _).1,(sig_views _ _ _).2,(eliminate_views _ _ _).1,
    (eliminate_views _ _ _).2,(clean_views _ _ _).1,(clean_views _ _ _).2,
    (gen_views _ _ _ _).1,(gen_views _ _ _ _).2,(pprime_views hp l r ha).1,
    (pprime_views hp l r ha).2,and_self]
end Passive
/-- On a compatible fresh-safe edge, the entire Head prefix frames all five
physical fields consumed by RowSafe and K2. -/
theorem before_peace_of_leaders {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ)
    (ha : r.label=⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩ ∨ r.leader=true)
    (hlead : (beforeElimination hp κ l r).1.leader=l.leader ∧
      (beforeElimination hp κ l r).2.leader=r.leader) :
    peaceViewPair (beforeElimination hp κ l r)=peaceViewPair (l,r) := by
  generalize hq : beforeElimination hp κ l r = q
  have hv := Passive.before_views hp κ l r ha
  rw [hq] at hv
  rw [hq] at hlead
  apply Prod.ext
  · exact PeaceView.ext _ _ hlead.1 (congrArg Prod.fst hv.1)
      (congrArg BulletFields.shield (congrArg Prod.snd hv.1))
      (congrArg BulletFields.bullet (congrArg Prod.snd hv.1))
      (congrArg BulletFields.signal_B (congrArg Prod.snd hv.1))
  · exact PeaceView.ext _ _ hlead.2 (congrArg Prod.fst hv.2)
      (congrArg BulletFields.shield (congrArg Prod.snd hv.2))
      (congrArg BulletFields.bullet (congrArg Prod.snd hv.2))
      (congrArg BulletFields.signal_B (congrArg Prod.snd hv.2))

/-- Fresh-safe compatible edges have no comparison birth, hence frame PeaceView. -/
theorem before_peace {ψ : Nat} (hp : ψ>0) (h3 : 3≤ψ) (κ : Nat) (l r : AgentState ψ)
    (ha : r.label=⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩ ∨ r.leader=true)
    (hl : PPLLAstraFreshSafe.Safe l) (hr : PPLLAstraFreshSafe.Safe r) :
    peaceViewPair (beforeElimination hp κ l r)=peaceViewPair (l,r) :=
  before_peace_of_leaders hp κ l r ha
    (PPLLAstraFreshStable.before_compatible_leaders hp h3 κ l r ha hl hr)

namespace Writer
private theorem label_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).label=if p then a.label else b.label := by split <;> rfl
private theorem shield_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).shield=if p then a.shield else b.shield := by split <;> rfl
private theorem bullet_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).bullet=if p then a.bullet else b.bullet := by split <;> rfl
private theorem signal_B_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).signal_B=if p then a.signal_B else b.signal_B := by split <;> rfl
private def Frame {ψ : Nat} (a b : AgentState ψ) : Prop :=
  a.label=b.label ∧ a.shield=b.shield ∧ a.bullet=b.bullet ∧ a.signal_B=b.signal_B
private theorem writeActionApplyOverwrite_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeActionApplyOverwrite u) u := by
  unfold Frame writeActionApplyOverwrite
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem writeActionApplyMoveFlip_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeActionApplyMoveFlip u) u := by
  unfold Frame writeActionApplyMoveFlip
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem moveWsigCheckLast_frame {ψ : Nat} (u : AgentState ψ) : Frame (moveWsigCheckLast u) u := by
  unfold Frame moveWsigCheckLast
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem writeSeqSetWriteReady_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeSeqSetWriteReady u) u := by
  unfold Frame writeSeqSetWriteReady
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem writeSeqCheckBit_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeSeqCheckBit u) u := by
  unfold Frame writeSeqCheckBit
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem writeSeqSetWriteAct_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeSeqSetWriteAct u) u := by
  cases hp : u.path3 <;> simp only [Frame,writeSeqSetWriteAct,hp] <;>
    simp [label_ite,shield_ite,bullet_ite,signal_B_ite,hp]
private theorem writeSeqFinalR_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeSeqFinalR u) u := by
  unfold Frame writeSeqFinalR
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem moveWsigCheckGenWs_frame {ψ : Nat} (l r : AgentState ψ) :
    Frame (moveWsigCheckGenWs l r) r := by
  unfold Frame moveWsigCheckGenWs
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,shield_ite,bullet_ite,signal_B_ite]
private theorem moveWsigTransfer_frame {ψ : Nat} (l r : AgentState ψ) :
    Frame (moveWsigTransfer l r).1 l ∧ Frame (moveWsigTransfer l r).2 r := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp only [Frame,moveWsigTransfer,hl,hr] <;>
    simp only [fst_ite,snd_ite,label_ite,shield_ite,bullet_ite,signal_B_ite,ite_self,and_self]
private theorem groupInfo_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (groupInfo hp l r).1 l ∧ Frame (groupInfo hp l r).2 r := by
  simp only [Frame,groupInfo,fst_ite,snd_ite,label_ite,shield_ite,bullet_ite,signal_B_ite,ite_self,and_self]
private theorem gensigWriteseq_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (gensigWriteseq hp l r).1 l ∧ Frame (gensigWriteseq hp l r).2 r := by
  simp only [Frame,gensigWriteseq,fst_ite,snd_ite,label_ite,shield_ite,bullet_ite,signal_B_ite,ite_self,and_self]
private theorem writeAction_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (writeAction hp l r).1 l ∧ Frame (writeAction hp l r).2 r := by
  simp only [Frame,writeAction]
  simp only [fst_ite,snd_ite,label_ite,shield_ite,bullet_ite,signal_B_ite,ite_self,and_self,(writeActionApplyOverwrite_frame _).1,(writeActionApplyOverwrite_frame _).2.1,(writeActionApplyOverwrite_frame _).2.2.1,(writeActionApplyOverwrite_frame _).2.2.2,(writeActionApplyMoveFlip_frame _).1,(writeActionApplyMoveFlip_frame _).2.1,(writeActionApplyMoveFlip_frame _).2.2.1,(writeActionApplyMoveFlip_frame _).2.2.2]
private theorem moveWsig_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (moveWsig hp l r).1 l ∧ Frame (moveWsig hp l r).2 r := by
  simp only [Frame,moveWsig]
  simp only [fst_ite,snd_ite,label_ite,shield_ite,bullet_ite,signal_B_ite,ite_self,and_self,(moveWsigCheckGenWs_frame _ _).1,(moveWsigCheckGenWs_frame _ _).2.1,(moveWsigCheckGenWs_frame _ _).2.2.1,(moveWsigCheckGenWs_frame _ _).2.2.2,(moveWsigCheckLast_frame _).1,(moveWsigCheckLast_frame _).2.1,(moveWsigCheckLast_frame _).2.2.1,(moveWsigCheckLast_frame _).2.2.2,(moveWsigTransfer_frame _ _).1.1,(moveWsigTransfer_frame _ _).1.2.1,(moveWsigTransfer_frame _ _).1.2.2.1,(moveWsigTransfer_frame _ _).1.2.2.2,(moveWsigTransfer_frame _ _).2.1,(moveWsigTransfer_frame _ _).2.2.1,(moveWsigTransfer_frame _ _).2.2.2.1,(moveWsigTransfer_frame _ _).2.2.2.2]
private theorem writeSeq_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (writeSeq hp l r).1 l ∧ Frame (writeSeq hp l r).2 r := by
  simp only [Frame,writeSeq,writeSeqThroughPrepare,writeSeqAfterPrepare,writeSeqLeaderMove,writeSeqGenerate,writeSeqPrepare,writeSeqReady,writeSeqCompare,writeSeqCommands]
  simp only [fst_ite,snd_ite,label_ite,shield_ite,bullet_ite,signal_B_ite,ite_self,and_self,(groupInfo_frame _ _ _).1.1,(groupInfo_frame _ _ _).1.2.1,(groupInfo_frame _ _ _).1.2.2.1,(groupInfo_frame _ _ _).1.2.2.2,(groupInfo_frame _ _ _).2.1,(groupInfo_frame _ _ _).2.2.1,(groupInfo_frame _ _ _).2.2.2.1,(groupInfo_frame _ _ _).2.2.2.2,(gensigWriteseq_frame _ _ _).1.1,(gensigWriteseq_frame _ _ _).1.2.1,(gensigWriteseq_frame _ _ _).1.2.2.1,(gensigWriteseq_frame _ _ _).1.2.2.2,(gensigWriteseq_frame _ _ _).2.1,(gensigWriteseq_frame _ _ _).2.2.1,(gensigWriteseq_frame _ _ _).2.2.2.1,(gensigWriteseq_frame _ _ _).2.2.2.2,(writeAction_frame _ _ _).1.1,(writeAction_frame _ _ _).1.2.1,(writeAction_frame _ _ _).1.2.2.1,(writeAction_frame _ _ _).1.2.2.2,(writeAction_frame _ _ _).2.1,(writeAction_frame _ _ _).2.2.1,(writeAction_frame _ _ _).2.2.2.1,(writeAction_frame _ _ _).2.2.2.2,(moveWsig_frame _ _ _).1.1,(moveWsig_frame _ _ _).1.2.1,(moveWsig_frame _ _ _).1.2.2.1,(moveWsig_frame _ _ _).1.2.2.2,(moveWsig_frame _ _ _).2.1,(moveWsig_frame _ _ _).2.2.1,(moveWsig_frame _ _ _).2.2.2.1,(moveWsig_frame _ _ _).2.2.2.2,(writeSeqSetWriteReady_frame _).1,(writeSeqSetWriteReady_frame _).2.1,(writeSeqSetWriteReady_frame _).2.2.1,(writeSeqSetWriteReady_frame _).2.2.2,(writeSeqCheckBit_frame _).1,(writeSeqCheckBit_frame _).2.1,(writeSeqCheckBit_frame _).2.2.1,(writeSeqCheckBit_frame _).2.2.2,(writeSeqSetWriteAct_frame _).1,(writeSeqSetWriteAct_frame _).2.1,(writeSeqSetWriteAct_frame _).2.2.1,(writeSeqSetWriteAct_frame _).2.2.2,(writeSeqFinalR_frame _).1,(writeSeqFinalR_frame _).2.1,(writeSeqFinalR_frame _).2.2.1,(writeSeqFinalR_frame _).2.2.2]

/-- The original WRITE preserves every elimination register and its labels;
its only leader motion is disabled when responder leaders have label zero. -/
theorem peace {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (hz : r.leader=true → r.label=⟨0,hp⟩) :
    peaceViewPair (writeWithBundle hp l r)=peaceViewPair (l,r) := by
  have hg : ¬(r.leader=true ∧ r.label.val≠0 ∧ l.leader=false) := by
    rintro ⟨hr,hn,_⟩
    exact hn (congrArg Fin.val (hz hr))
  simp only [writeWithBundle,if_neg hg]
  generalize hq : writeSeq hp l r=q
  have hf := writeSeq_frame hp l r
  rw [hq] at hf
  have hll : q.1.leader=l.leader := by
    cases hl : l.leader
    · cases ho : q.1.leader
      · rfl
      · have h := PPLLVerify.writeSeq_new_initiator_requires_responder_leader hp l r
          (hq.symm ▸ ho) hl
        exact False.elim (h.2 (hz h.1))
    · have h := PPLLVerify.writeSeq_initiator_leader_of_true hp l r hl
      rwa [hq] at h
  have hrr : q.2.leader=r.leader := by
    cases hr : r.leader
    · cases ho : q.2.leader
      · rfl
      · have h := PPLLVerify.writeSeq_responder_leader_was_leader hp l r (hq.symm ▸ ho)
        simp [hr] at h
    · have h := PPLLVerify.writeSeq_responder_leader_of_label_zero hp l r hr (hz hr)
      rwa [hq] at h
  exact Prod.ext (PeaceView.ext _ _ hll hf.1.1 hf.1.2.1 hf.1.2.2.1 hf.1.2.2.2)
    (PeaceView.ext _ _ hrr hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2)
end Writer


/-- RowSafe depends only on the five fields in PeaceView. Ancillary writer
and comparison data are not silently constrained by this transport lemma. -/
theorem rowSafe_congr {ψ n : Nat} (hp : ψ>0) (ring : DirectedRing n)
    (C D : Fin n → AgentState ψ)
    (h : ∀ i, PeaceView.ofState (D i)=PeaceView.ofState (C i))
    (hc : RowSafe hp ring C) : RowSafe hp ring D := by
  have hl (i) : (D i).leader=(C i).leader := congrArg PeaceView.leader (h i)
  have hn (i) : (D i).label=(C i).label := congrArg PeaceView.label (h i)
  have hs (i) : (D i).shield=(C i).shield := congrArg PeaceView.shield (h i)
  have hb (i) : (D i).bullet=(C i).bullet := congrArg PeaceView.bullet (h i)
  have hz (i) : (D i).signal_B=(C i).signal_B := congrArg PeaceView.signal_B (h i)
  have hv : signalConfig D=signalConfig C := by
    funext i
    simp only [signalConfig,signalView,hl i,hs i,hb i,hz i]
  refine ⟨hv.symm ▸ hc.1, ?_, ?_⟩
  · intro i hi
    rw [hn]
    exact hc.2.1 i (by simpa only [AgentState.isLeader,hl] using hi)
  · simpa only [noFreeBarrier,isBarrier,AgentState.isLeader,hl,hn] using hc.2.2

private theorem edge_ne {n : Nat} (ring : DirectedRing n) (hn : 1<n) (e : Fin n) :
    e≠ring.rightNeighbor e := by
  intro h
  have he := congrArg Fin.val h.symm
  change (e.val+1)%n=e.val at he
  by_cases ht : e.val+1<n
  · rw [Nat.mod_eq_of_lt ht] at he
    omega
  · have ht : e.val+1=n := by omega
    rw [ht,Nat.mod_self] at he
    omega

attribute [local irreducible] beforeElimination k4Kernel PPLLAstraDesign2.pipeline

/-- Every actual Head edge preserves RowSafe, comparison safety, and the
entire leader vector. This is a closed singleton sector, with no requirement
that identifiers differ or that the ring size be divisible by ψ. -/
theorem step_closed_of_edge {ψ n : Nat} (hp : ψ>0) (κ : Nat)
    (ring : DirectedRing n) (hn : 1<n) (C : Fin n → AgentState ψ)
    (hc : RowSafe hp ring C) (hf : ∀i, PPLLAstraFreshSafe.Safe (C i)) (e : Fin n)
    (hprefix : peaceViewPair (beforeElimination hp κ (C e) (C (ring.rightNeighbor e)))=
      peaceViewPair (C e,C (ring.rightNeighbor e)))
    (hsafe : PPLLAstraFreshSafe.Safe (pipeline hp κ .head (C e) (C (ring.rightNeighbor e))).1 ∧
      PPLLAstraFreshSafe.Safe (pipeline hp κ .head (C e) (C (ring.rightNeighbor e))).2) :
    let D := (PPLLAstraResetWord.protocol hp κ).step ring C e
    RowSafe hp ring D ∧ (∀i, PPLLAstraFreshSafe.Safe (D i)) ∧
      (∀i, (D i).leader=(C i).leader) := by
  let j := ring.rightNeighbor e
  have hne : e≠j := edge_ne ring hn e
  have hne' : j≠e := Ne.symm hne
  let a := beforeElimination hp κ (C e) (C j)
  have hav : peaceViewPair a=peaceViewPair (C e,C j) := hprefix
  let A := updatePair C e j a
  have hAv (i) : PeaceView.ofState (A i)=PeaceView.ofState (C i) := by
    dsimp only [A,updatePair]
    split
    · rename_i hi
      subst i
      exact congrArg Prod.fst hav
    · split
      · rename_i _ hi
        subst i
        exact congrArg Prod.snd hav
      · rfl
  have hA : RowSafe hp ring A := rowSafe_congr hp ring C A hAv hc
  have hAe : A e=a.1 := by simp [A,updatePair]
  have hAj : A j=a.2 := by simp [A,updatePair,hne']
  have hnone : ¬(a.1.leader=true ∧ a.2.leader=true) := by
    rintro ⟨hl,hr⟩
    obtain ⟨root,hroot,hu⟩ := hA.1.unique_leader
    have hel : e=root := hu e (by change (A e).leader=true; simpa only [hAe] using hl)
    have her : j=root := hu j (by change (A j).leader=true; simpa only [hAj] using hr)
    exact hne (hel.trans her.symm)
  have hshield : a.1.leader=true → a.2.bullet=2 → a.1.shield=true := by
    intro hl hb
    have h := rowSafe_live_shield hp ring A hA e j
      (by simpa only [hAe] using hl) (by simpa only [hAj] using hb)
    simpa only [hAe] using h
  let b := k4Kernel hp a.1 a.2
  let B := rawStep hp ring A e
  have hbe : B e=b.1 := by
    change (updatePair A e j (sinkKernelC hp (A e) (A j)) e)=b.1
    simp only [updatePair,ite_true,hAe,hAj]
    rw [← k4_eq_sink hp a.1 a.2 hnone hshield]
  have hbj : B j=b.2 := by
    change (updatePair A e j (sinkKernelC hp (A e) (A j)) j)=b.2
    simp only [updatePair,hne',ite_false,ite_true,hAe,hAj]
    rw [← k4_eq_sink hp a.1 a.2 hnone hshield]
  have hB : RowSafe hp ring B := rowSafe_step hp hn ring A hA e
  have hBl (i) : (B i).leader=(C i).leader :=
    (rawStep_leader hp ring A hA e i).trans (congrArg PeaceView.leader (hAv i))
  have hbz : b.2.leader=true → b.2.label=⟨0,hp⟩ := by
    intro hb
    have h := hB.2.1 j (by change (B j).leader=true; simpa only [hbj] using hb)
    simpa only [hbj] using h
  let w := writeWithBundle hp b.1 b.2
  have hw : peaceViewPair w=peaceViewPair b := Writer.peace hp b.1 b.2 hbz
  have hwl : w.1.leader=(C e).leader :=
    (congrArg (fun q => q.1.leader) hw).trans ((congrArg AgentState.leader hbe).symm.trans (hBl e))
  have hwr : w.2.leader=(C j).leader :=
    (congrArg (fun q => q.2.leader) hw).trans ((congrArg AgentState.leader hbj).symm.trans (hBl j))
  have hcons : conserve .head (C e) (C j) w=w := by
    simp only [conserve,hwl,hwr]
    cases (C e).leader <;> cases (C j).leader <;> rfl
  have hout : pipeline hp κ .head (C e) (C j)=w := by
    simpa only [PPLLAstraDesign2.pipeline] using hcons
  let D := (PPLLAstraResetWord.protocol hp κ).step ring C e
  have hDv (i) : PeaceView.ofState (D i)=PeaceView.ofState (B i) := by
    change PeaceView.ofState (updatePair C e j (pipeline hp κ .head (C e) (C j)) i)=_
    rw [hout]
    unfold updatePair
    split
    · rename_i hi
      subst i
      rw [hbe]
      exact congrArg Prod.fst hw
    · split
      · rename_i _ hi
        subst i
        rw [hbj]
        exact congrArg Prod.snd hw
      · rename_i hi hj
        change PeaceView.ofState (C i)=PeaceView.ofState
          (updatePair A e j (sinkKernelC hp (A e) (A j)) i)
        simp only [updatePair,hi,hj,ite_false,A]
  refine ⟨rowSafe_congr hp ring B D hDv hB, ?_, ?_⟩
  · intro i
    change PPLLAstraFreshSafe.Safe (updatePair C e j (pipeline hp κ .head (C e) (C j)) i)
    unfold updatePair
    split
    · exact hsafe.1
    · split
      · exact hsafe.2
      · exact hf i
  · intro i
    exact (congrArg PeaceView.leader (hDv i)).trans (hBl i)

/-- The ψ≥3 comparison theorem discharges the two exact local interfaces. -/
theorem step_closed {ψ n : Nat} (hp : ψ>0) (h3 : 3≤ψ) (κ : Nat)
    (ring : DirectedRing n) (hn : 1<n) (C : Fin n → AgentState ψ)
    (hc : RowSafe hp ring C) (hf : ∀i, PPLLAstraFreshSafe.Safe (C i)) (e : Fin n) :
    let D := (PPLLAstraResetWord.protocol hp κ).step ring C e
    RowSafe hp ring D ∧ (∀i, PPLLAstraFreshSafe.Safe (D i)) ∧
      (∀i, (D i).leader=(C i).leader) := by
  have ha : (C (ring.rightNeighbor e)).label=⟨((C e).label.val+1)%ψ,Nat.mod_lt _ hp⟩ ∨
      (C (ring.rightNeighbor e)).leader=true := by
    by_cases hj : (C (ring.rightNeighbor e)).leader=true
    · exact Or.inr hj
    · exact Or.inl (successor_label_of_noFreeBarrier_of_right_not_leader hp ring C hc.2.2 e hj)
  exact step_closed_of_edge hp κ ring hn C hc hf e
    (before_peace hp h3 κ _ _ ha (hf e) (hf _))
    (PPLLAstraFreshStable.pipeline_compatible_safe hp h3 κ _ _ ha (hf e) (hf _))

/-- Arbitrary finite schedules remain in the sector and preserve the same
leader at the same physical site. No fairness or chosen word is assumed. -/
theorem reachable_closed {ψ n : Nat} (hp : ψ>0) (h3 : 3≤ψ) (κ : Nat)
    (ring : DirectedRing n) (hn : 1<n) {C D : Fin n → AgentState ψ}
    (hc : RowSafe hp ring C) (hf : ∀i, PPLLAstraFreshSafe.Safe (C i))
    (hr : (PPLLAstraResetWord.protocol hp κ).Reachable ring C D) :
    RowSafe hp ring D ∧ (∀i, PPLLAstraFreshSafe.Safe (D i)) ∧
      (∀i, (D i).leader=(C i).leader) := by
  apply PopulationProtocol.ClosedPred.reachable
    (P := PPLLAstraResetWord.protocol hp κ)
    (S := fun E => RowSafe hp ring E ∧ (∀i, PPLLAstraFreshSafe.Safe (E i)) ∧
      (∀i, (E i).leader=(C i).leader)) (hC := ⟨hc,hf,fun _ => rfl⟩) (hr := hr)
  intro A ih B hs
  obtain ⟨e,rfl⟩ := hs
  have ht := step_closed hp h3 κ ring hn A ih.1 ih.2.1 e
  exact ⟨ht.1,ht.2.1,fun i => (ht.2.2 i).trans (ih.2.2 i)⟩

end PPLLAstraFreshStableRow
