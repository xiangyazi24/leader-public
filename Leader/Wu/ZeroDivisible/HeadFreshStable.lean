import Leader.Wu.ZeroDivisible.HeadFreshSafe
/-! Incoming leader walls and the fresh comparison sector for frozen Head.
This module extends the aligned-edge result without altering its frozen source. -/
namespace PPLLAstraFreshStable
open PPLLElimVariants PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
  PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraReset PPLLAstraFreshSafe
/-- Comparison cleanup including the two carry fields used by DISAPPEAR. -/
def Clean {ψ : Nat} (u : AgentState ψ) : Prop :=
  CmpEmpty u ∧ u.p=false ∧ u.p_carry=false
private theorem clear_clean {ψ : Nat} (u : AgentState ψ) : Clean (clearCmp u) := by
  simp [Clean,CmpEmpty,clearCmp]
private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
private theorem leader_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).leader = if p then a.leader else b.leader := by split <;> rfl
private theorem label_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).label = if p then a.label else b.label := by split <;> rfl
private theorem state_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).state = if p then a.state else b.state := by split <;> rfl
private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by split <;> rfl
private theorem path2_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path2 = if p then a.path2 else b.path2 := by split <;> rfl
private theorem gen_leaders {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ) :
    (genSigSaturated hp κ l r).1.leader=l.leader ∧
    (genSigSaturated hp κ l r).2.leader=r.leader := by
  simp only [genSigSaturated,genSigSaturatedAfterWait,genSigSaturatedStart,
    genSigSaturatedEmit,genSigSaturatedPropagate,genSigSaturatedFinish,
    waitSaturated,waitSaturatedPrepare,waitSaturatedCarry,waitSaturatedReset,
    waitSaturatedFinish,fst_ite,snd_ite,leader_ite,ite_self,and_self]
private theorem eliminate_leaders {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    (eliminateSig hp l r).1.leader=l.leader ∧ (eliminateSig hp l r).2.leader=r.leader := by
  simp only [eliminateSig,fst_ite,snd_ite,leader_ite,ite_self,and_self]
private theorem move1_leaders {ψ : Nat} (l r : AgentState ψ) :
    (sigMoveStep1With .dropMisaligned l r).1.leader=l.leader ∧
    (sigMoveStep1With .dropMisaligned l r).2.leader=r.leader := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [sigMoveStep1With,hl,hr,fst_ite,snd_ite,leader_ite]
private theorem moveToken_leaders {ψ : Nat} (l r : AgentState ψ) :
    (moveTokens l r).1.leader=l.leader ∧ (moveTokens l r).2.leader=r.leader := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [moveTokens,hl,hr,fst_ite,snd_ite,leader_ite]
private theorem control_leader {ψ : Nat} (hp : ψ>0) (u : AgentState ψ) :
    (sigMoveApplyControlConsume hp u).leader=u.leader := by
  cases h : u.path2 <;> simp [sigMoveApplyControlConsume,h,leader_ite]
private theorem clean_leaders {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (cleanSig hψ l r).1.leader = l.leader ∧
    (cleanSig hψ l r).2.leader = r.leader := by
  exact PPLLVerify.cleanSig_leaders_eq hψ l r


/-- A responding leader causes the post-transfer leader wall to clear both
comparison endpoints, regardless of carriers or incoming edge alignment. -/
theorem sigmove_responder_clean {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (hr : r.leader=true) :
    Clean (sigMoveF hp true .dropMisaligned l r).1 ∧
    Clean (sigMoveF hp true .dropMisaligned l r).2 := by
  unfold sigMoveF
  simp only [hr, show (true : Bool)=true from rfl, true_and,ite_true]
  generalize hA : (if l.leader=true ∨ r.label≠⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩
    then clearCmp l else l) = a
  generalize hB : sigMoveStep1With .dropMisaligned a (clearCmp r) = b
  have hb := move1_leaders a (clearCmp r)
  rw [hB] at hb
  have hbr : b.2.leader=true := hb.2.trans hr
  generalize hC : moveTokens b.1 b.2 = c
  have hc := moveToken_leaders b.1 b.2
  rw [hC] at hc
  have hcr : c.2.leader=true := hc.2.trans hbr
  simp [leaderWall,hcr,sigMoveApplyControlConsume,clearCmp,Clean,CmpEmpty]

private theorem drop_clean {ψ : Nat} (u : AgentState ψ) (h : Clean u) : Clean (dropStale u) := by
  simpa [dropStale,h.1.2.1] using h
private theorem precheck_clean {ψ : Nat} (l r : AgentState ψ) (hl : Clean l) (hr : Clean r) :
    Clean (preCheckReset l r).1 ∧ Clean (preCheckReset l r).2 := by
  unfold preCheckReset
  dsimp only
  split <;> split <;> simp_all [Clean,CmpEmpty,clearCmp]
private theorem check_clean {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ)
    (hl : Clean l) (hr : Clean r) : checkSigF hp κ false l r=(l,r) := by
  simp [checkSigF,readyF,waveState,checkSigSetReadyGuarded,controlPending,
    checkSigSetReady,checkSigCheckL,checkSigCheckR,checkSigSetResult,
    hl.1.1,hl.1.2.1,hr.1.1,hr.1.2.1]
private theorem disappear_clean {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (hl : Clean l) (hr : Clean r) : disappear hp l r=(l,r) := by
  simp [disappear,hl.1.1,hr.1.1,hl.2.2]
private theorem compare_clean {ψ : Nat} (κ : Nat) (l r : AgentState ψ)
    (hl : Clean l) (hr : Clean r) : compareSigF κ false true l r=(l,r) := by
  rw [PPLLAstraFreshSafe.compare_core_eq κ false true l r
    (PPLLAstraFreshSafe.cmpEmpty_safe l hl.1).1
    (PPLLAstraFreshSafe.cmpEmpty_safe r hr.1).1]
  simp [compareSigInit,hl.1.2.1,← hl.1.1]
  rw [← hl.1.2.1]
private theorem path4_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path4=if p then a.path4 else b.path4 := by split <;> rfl
private theorem path5_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path5=if p then a.path5 else b.path5 := by split <;> rfl
private theorem p_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).p=if p then a.p else b.p := by split <;> rfl
private theorem p_carry_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).p_carry=if p then a.p_carry else b.p_carry := by split <;> rfl
private theorem suppress_clean {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (hl : Clean l) (hr : Clean r) :
    Clean (suppressSigResetKill hp l r).1 ∧ Clean (suppressSigResetKill hp l r).2 := by
  cases h1 : l.leader <;> cases h2 : l.reset_cmd <;>
    cases h3 : r.reset_cmd <;> cases h4 : r.echo <;>
    simp_all [suppressSigResetKill,suppressSigStart,suppressSigMoveReset,
      suppressSigTerminal,suppressSigEcho,suppressSigFinish,clearCmp,
      Clean,CmpEmpty,fst_ite,snd_ite,state_ite,path_ite,path2_ite,path4_ite,path5_ite,p_ite,p_carry_ite]
private theorem pprime_responder_leaders {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (hr : r.leader=true) :
    (pPsiProbeWall hp l r).1.leader=l.leader ∧ (pPsiProbeWall hp l r).2.leader=true := by
  simp [pPsiProbeWall,pPsi,hr,fst_ite,snd_ite,leader_ite]
/-- A leader responder forces complete comparison cleanup through the full
Head prefix. Its label, ψ, κ, incoming alignment and comparison fields are free. -/
theorem before_responder_clean {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ)
    (hr : r.leader=true) :
    Clean (beforeElimination hp κ l r).1 ∧ Clean (beforeElimination hp κ l r).2 := by
  unfold beforeElimination
  try dsimp only
  generalize hA : pPsiProbeWall hp l r = a
  try dsimp only
  have har := pprime_responder_leaders hp l r hr
  rw [hA] at har
  generalize hB : genSigSaturated hp κ a.1 a.2 = b
  try dsimp only
  have hbr := gen_leaders hp κ a.1 a.2
  rw [hB] at hbr
  generalize hC : cleanSig hp b.1 b.2 = c
  try dsimp only
  have hcr := clean_leaders hp b.1 b.2
  rw [hC] at hcr
  generalize hD : eliminateSig hp c.1 c.2 = d
  try dsimp only
  have hdr := eliminate_leaders hp c.1 c.2
  rw [hD] at hdr
  have hd : d.2.leader=true := hdr.2.trans (hcr.2.trans (hbr.2.trans har.2))
  generalize hE : sigMoveF hp true .dropMisaligned d.1 d.2 = e
  try dsimp only
  have he := sigmove_responder_clean hp d.1 d.2 hd
  rw [hE] at he
  have hf : Clean (dropStale e.1) ∧ Clean (dropStale e.2) :=
    ⟨drop_clean e.1 he.1,drop_clean e.2 he.2⟩
  generalize hG : preCheckReset (dropStale e.1) (dropStale e.2) = g
  try dsimp only
  have hg := precheck_clean (dropStale e.1) (dropStale e.2) hf.1 hf.2
  rw [hG] at hg
  rw [check_clean hp κ g.1 g.2 hg.1 hg.2,disappear_clean hp g.1 g.2 hg.1 hg.2,
    compare_clean κ g.1 g.2 hg.1 hg.2]
  exact suppress_clean hp g.1 g.2 hg.1 hg.2

/-! Comparison fields are framed by elimination and WRITE. The frozen
FreshSafe module does not export these field frames, so these small direct
source proofs are local to this suffix extension. -/
private def CmpView {ψ : Nat} (u : AgentState ψ) := (u.label,u.state,u.path,u.path2)
private theorem cmpview_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    CmpView (if p then a else b)=if p then CmpView a else CmpView b := by split <;> rfl
private theorem safe_of_cmpview {ψ : Nat} (a b : AgentState ψ) (hv : CmpView a=CmpView b)
    (hb : Safe b) : Safe a := by
  simp only [CmpView,Prod.mk.injEq] at hv
  simpa only [Safe,Core,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2] using hb
private theorem kernel_cmpview {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    CmpView (k4Kernel hp l r).1=CmpView l ∧ CmpView (k4Kernel hp l r).2=CmpView r := by
  simp only [k4Kernel,k3Kernel,eliminateLeadersNoCollisionFire,absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink,dummyBulletSink]
  simp only [CmpView,fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self]

/-! WRITE frames are proved directly from the frozen writer definitions;
writer fields and bit mutations impose no comparison-safety premise. -/
namespace Writer
private def Frame {ψ : Nat} (a b : AgentState ψ) : Prop :=
  a.label=b.label ∧ a.state=b.state ∧ a.path=b.path ∧ a.path2=b.path2
private theorem writeActionApplyOverwrite_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeActionApplyOverwrite u) u := by
  unfold Frame writeActionApplyOverwrite
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,state_ite,path_ite,path2_ite]
private theorem writeActionApplyMoveFlip_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeActionApplyMoveFlip u) u := by
  unfold Frame writeActionApplyMoveFlip
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,state_ite,path_ite,path2_ite]
private theorem moveWsigCheckLast_frame {ψ : Nat} (u : AgentState ψ) : Frame (moveWsigCheckLast u) u := by
  unfold Frame moveWsigCheckLast
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,state_ite,path_ite,path2_ite]
private theorem writeSeqSetWriteReady_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeSeqSetWriteReady u) u := by
  unfold Frame writeSeqSetWriteReady
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,state_ite,path_ite,path2_ite]
private theorem writeSeqCheckBit_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeSeqCheckBit u) u := by
  unfold Frame writeSeqCheckBit
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,state_ite,path_ite,path2_ite]
private theorem writeSeqSetWriteAct_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeSeqSetWriteAct u) u := by
  cases hp : u.path3 <;> simp only [Frame,writeSeqSetWriteAct,hp] <;>
    simp [label_ite,state_ite,path_ite,path2_ite,hp]
private theorem writeSeqFinalR_frame {ψ : Nat} (u : AgentState ψ) : Frame (writeSeqFinalR u) u := by
  unfold Frame writeSeqFinalR
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,state_ite,path_ite,path2_ite]
private theorem moveWsigCheckGenWs_frame {ψ : Nat} (l r : AgentState ψ) :
    Frame (moveWsigCheckGenWs l r) r := by
  unfold Frame moveWsigCheckGenWs
  repeat (first | constructor | rfl | split)
  all_goals simp [label_ite,state_ite,path_ite,path2_ite]
private theorem moveWsigTransfer_frame {ψ : Nat} (l r : AgentState ψ) :
    Frame (moveWsigTransfer l r).1 l ∧ Frame (moveWsigTransfer l r).2 r := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp only [Frame,moveWsigTransfer,hl,hr] <;>
    simp only [fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self]
private theorem groupInfo_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (groupInfo hp l r).1 l ∧ Frame (groupInfo hp l r).2 r := by
  simp only [Frame,groupInfo,fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self]
private theorem gensigWriteseq_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (gensigWriteseq hp l r).1 l ∧ Frame (gensigWriteseq hp l r).2 r := by
  simp only [Frame,gensigWriteseq,fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self]
private theorem writeAction_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (writeAction hp l r).1 l ∧ Frame (writeAction hp l r).2 r := by
  simp only [Frame,writeAction]
  simp only [fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self,(writeActionApplyOverwrite_frame _).1,(writeActionApplyOverwrite_frame _).2.1,(writeActionApplyOverwrite_frame _).2.2.1,(writeActionApplyOverwrite_frame _).2.2.2,(writeActionApplyMoveFlip_frame _).1,(writeActionApplyMoveFlip_frame _).2.1,(writeActionApplyMoveFlip_frame _).2.2.1,(writeActionApplyMoveFlip_frame _).2.2.2]
private theorem moveWsig_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (moveWsig hp l r).1 l ∧ Frame (moveWsig hp l r).2 r := by
  simp only [Frame,moveWsig]
  simp only [fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self,(moveWsigCheckGenWs_frame _ _).1,(moveWsigCheckGenWs_frame _ _).2.1,(moveWsigCheckGenWs_frame _ _).2.2.1,(moveWsigCheckGenWs_frame _ _).2.2.2,(moveWsigCheckLast_frame _).1,(moveWsigCheckLast_frame _).2.1,(moveWsigCheckLast_frame _).2.2.1,(moveWsigCheckLast_frame _).2.2.2,(moveWsigTransfer_frame _ _).1.1,(moveWsigTransfer_frame _ _).1.2.1,(moveWsigTransfer_frame _ _).1.2.2.1,(moveWsigTransfer_frame _ _).1.2.2.2,(moveWsigTransfer_frame _ _).2.1,(moveWsigTransfer_frame _ _).2.2.1,(moveWsigTransfer_frame _ _).2.2.2.1,(moveWsigTransfer_frame _ _).2.2.2.2]
private theorem writeSeq_frame {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    Frame (writeSeq hp l r).1 l ∧ Frame (writeSeq hp l r).2 r := by
  simp only [Frame,writeSeq,writeSeqThroughPrepare,writeSeqAfterPrepare,writeSeqLeaderMove,writeSeqGenerate,writeSeqPrepare,writeSeqReady,writeSeqCompare,writeSeqCommands]
  simp only [fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,ite_self,and_self,(groupInfo_frame _ _ _).1.1,(groupInfo_frame _ _ _).1.2.1,(groupInfo_frame _ _ _).1.2.2.1,(groupInfo_frame _ _ _).1.2.2.2,(groupInfo_frame _ _ _).2.1,(groupInfo_frame _ _ _).2.2.1,(groupInfo_frame _ _ _).2.2.2.1,(groupInfo_frame _ _ _).2.2.2.2,(gensigWriteseq_frame _ _ _).1.1,(gensigWriteseq_frame _ _ _).1.2.1,(gensigWriteseq_frame _ _ _).1.2.2.1,(gensigWriteseq_frame _ _ _).1.2.2.2,(gensigWriteseq_frame _ _ _).2.1,(gensigWriteseq_frame _ _ _).2.2.1,(gensigWriteseq_frame _ _ _).2.2.2.1,(gensigWriteseq_frame _ _ _).2.2.2.2,(writeAction_frame _ _ _).1.1,(writeAction_frame _ _ _).1.2.1,(writeAction_frame _ _ _).1.2.2.1,(writeAction_frame _ _ _).1.2.2.2,(writeAction_frame _ _ _).2.1,(writeAction_frame _ _ _).2.2.1,(writeAction_frame _ _ _).2.2.2.1,(writeAction_frame _ _ _).2.2.2.2,(moveWsig_frame _ _ _).1.1,(moveWsig_frame _ _ _).1.2.1,(moveWsig_frame _ _ _).1.2.2.1,(moveWsig_frame _ _ _).1.2.2.2,(moveWsig_frame _ _ _).2.1,(moveWsig_frame _ _ _).2.2.1,(moveWsig_frame _ _ _).2.2.2.1,(moveWsig_frame _ _ _).2.2.2.2,(writeSeqSetWriteReady_frame _).1,(writeSeqSetWriteReady_frame _).2.1,(writeSeqSetWriteReady_frame _).2.2.1,(writeSeqSetWriteReady_frame _).2.2.2,(writeSeqCheckBit_frame _).1,(writeSeqCheckBit_frame _).2.1,(writeSeqCheckBit_frame _).2.2.1,(writeSeqCheckBit_frame _).2.2.2,(writeSeqSetWriteAct_frame _).1,(writeSeqSetWriteAct_frame _).2.1,(writeSeqSetWriteAct_frame _).2.2.1,(writeSeqSetWriteAct_frame _).2.2.2,(writeSeqFinalR_frame _).1,(writeSeqFinalR_frame _).2.1,(writeSeqFinalR_frame _).2.2.1,(writeSeqFinalR_frame _).2.2.2]
private theorem write_cmpview {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    CmpView (writeWithBundle hp l r).1=CmpView l ∧
    CmpView (writeWithBundle hp l r).2=CmpView r := by
  have h := writeSeq_frame hp l r
  simp only [CmpView,writeWithBundle,fst_ite,snd_ite,label_ite,state_ite,path_ite,path2_ite,
    h.1.1,h.1.2.1,h.1.2.2.1,h.1.2.2.2,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,ite_self,and_self]
end Writer


private theorem finish_safe {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) (hq : Safe q.1 ∧ Safe q.2) :
    let b := k4Kernel hp q.1 q.2
    let c := writeWithBundle hp b.1 b.2
    Safe (conserve .head l r c).1 ∧ Safe (conserve .head l r c).2 := by
  generalize hB : k4Kernel hp q.1 q.2 = b
  try dsimp only
  have hbV := kernel_cmpview hp q.1 q.2
  rw [hB] at hbV
  have hb : Safe b.1 ∧ Safe b.2 :=
    ⟨safe_of_cmpview _ _ hbV.1 hq.1,safe_of_cmpview _ _ hbV.2 hq.2⟩
  generalize hC : writeWithBundle hp b.1 b.2 = c
  try dsimp only
  have hcV := Writer.write_cmpview hp b.1 b.2
  rw [hC] at hcV
  have hc : Safe c.1 ∧ Safe c.2 :=
    ⟨safe_of_cmpview _ _ hcV.1 hb.1,safe_of_cmpview _ _ hcV.2 hb.2⟩
  unfold conserve
  split
  · simpa [replacement,clearCmp,Safe,Core,StateOK,NoZero] using hc.1
  · exact hc
/-- Full actual Head comparison safety for a responding leader, including
unaligned incoming edges and arbitrary initial comparison garbage. -/
theorem pipeline_responder_safe {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ)
    (hr : r.leader=true) :
    Safe (PPLLAstraDesign2.pipeline hp κ .head l r).1 ∧
    Safe (PPLLAstraDesign2.pipeline hp κ .head l r).2 := by
  have hc := before_responder_clean hp κ l r hr
  exact finish_safe hp l r (beforeElimination hp κ l r)
    ⟨cmpEmpty_safe _ hc.1.1,cmpEmpty_safe _ hc.2.1⟩
/-- Fresh comparison safety on every no-free-barrier-compatible Head edge.
The responder-leader case does not require successor alignment. -/
theorem pipeline_compatible_safe {ψ : Nat} (hp : ψ>0) (h3 : 3≤ψ) (κ : Nat)
    (l r : AgentState ψ)
    (ha : r.label=⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩ ∨ r.leader=true)
    (hl : Safe l) (hr : Safe r) :
    Safe (PPLLAstraDesign2.pipeline hp κ .head l r).1 ∧
    Safe (PPLLAstraDesign2.pipeline hp κ .head l r).2 := by
  rcases ha with ha | ha
  · exact PPLLAstraFreshSafe.pipeline_safe hp h3 κ l r ha hl hr
  · exact pipeline_responder_safe hp κ l r ha
private theorem sigmove_leaders {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    (sigMoveF hp true .dropMisaligned l r).1.leader=l.leader ∧
    (sigMoveF hp true .dropMisaligned l r).2.leader=r.leader := by
  simp only [sigMoveF,leaderWall,fst_ite,snd_ite,leader_ite,control_leader,
    (move1_leaders _ _).1,(move1_leaders _ _).2,
    (moveToken_leaders _ _).1,(moveToken_leaders _ _).2,clearCmp,ite_self,and_self]
private theorem drop_leader {ψ : Nat} (u : AgentState ψ) : (dropStale u).leader=u.leader := by
  simp [dropStale,leader_ite]
private theorem precheck_leaders {ψ : Nat} (l r : AgentState ψ) :
    (preCheckReset l r).1.leader=l.leader ∧ (preCheckReset l r).2.leader=r.leader := by
  simp [preCheckReset,clearCmp,leader_ite]
private theorem suppress_leaders {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigResetKill hp l r).1.leader=l.leader ∧
    (suppressSigResetKill hp l r).2.leader=r.leader := by
  cases h1 : l.leader <;> cases h2 : l.reset_cmd <;>
    cases h3 : r.reset_cmd <;> cases h4 : r.echo <;>
    simp [suppressSigResetKill,suppressSigStart,suppressSigMoveReset,
      suppressSigTerminal,suppressSigEcho,suppressSigFinish,clearCmp,
      h1,h2,h3,h4,fst_ite,snd_ite,leader_ite]

/-- Incoming leader walls exclude every comparison-prefix birth, with arbitrary debris. -/
theorem before_responder_leaders {ψ : Nat} (hp : ψ>0) (κ : Nat) (l r : AgentState ψ)
    (hr : r.leader=true) :
    (beforeElimination hp κ l r).1.leader=l.leader ∧
    (beforeElimination hp κ l r).2.leader=r.leader := by
  unfold beforeElimination
  try dsimp only
  generalize hA : pPsiProbeWall hp l r = a
  try dsimp only
  have har := pprime_responder_leaders hp l r hr
  rw [hA] at har
  generalize hB : genSigSaturated hp κ a.1 a.2 = b
  try dsimp only
  have hbr := gen_leaders hp κ a.1 a.2
  rw [hB] at hbr
  generalize hC : cleanSig hp b.1 b.2 = c
  try dsimp only
  have hcr := clean_leaders hp b.1 b.2
  rw [hC] at hcr
  generalize hD : eliminateSig hp c.1 c.2 = d
  try dsimp only
  have hdr := eliminate_leaders hp c.1 c.2
  rw [hD] at hdr
  have hd : d.2.leader=true := hdr.2.trans (hcr.2.trans (hbr.2.trans har.2))
  generalize hE : sigMoveF hp true .dropMisaligned d.1 d.2 = e
  try dsimp only
  have he := sigmove_responder_clean hp d.1 d.2 hd
  rw [hE] at he
  have hf : Clean (dropStale e.1) ∧ Clean (dropStale e.2) :=
    ⟨drop_clean e.1 he.1,drop_clean e.2 he.2⟩
  generalize hG : preCheckReset (dropStale e.1) (dropStale e.2) = g
  try dsimp only
  have hg := precheck_clean (dropStale e.1) (dropStale e.2) hf.1 hf.2
  rw [hG] at hg
  rw [check_clean hp κ g.1 g.2 hg.1 hg.2,disappear_clean hp g.1 g.2 hg.1 hg.2,
    compare_clean κ g.1 g.2 hg.1 hg.2]
  have hes := sigmove_leaders hp d.1 d.2
  rw [hE] at hes
  have hgp := precheck_leaders (dropStale e.1) (dropStale e.2)
  rw [hG] at hgp
  have hsup := suppress_leaders hp g.1 g.2
  constructor
  · exact hsup.1.trans (hgp.1.trans ((drop_leader e.1).trans
      (hes.1.trans (hdr.1.trans (hcr.1.trans (hbr.1.trans har.1))))))
  · exact hsup.2.trans (hgp.2.trans ((drop_leader e.2).trans
      (hes.2.trans (hdr.2.trans (hcr.2.trans (hbr.2.trans (har.2.trans hr.symm)))))))


/-- Exact prefix leader lineage on every compatible edge of the fresh sector. -/
theorem before_compatible_leaders {ψ : Nat} (hp : ψ>0) (h3 : 3≤ψ) (κ : Nat)
    (l r : AgentState ψ)
    (ha : r.label=⟨(l.label.val+1)%ψ,Nat.mod_lt _ hp⟩ ∨ r.leader=true)
    (hl : Safe l) (hr : Safe r) :
    (beforeElimination hp κ l r).1.leader=l.leader ∧
    (beforeElimination hp κ l r).2.leader=r.leader := by
  rcases ha with ha | ha
  · exact PPLLAstraFreshSafe.before_leaders hp h3 κ l r ha hl hr
  · exact before_responder_leaders hp κ l r ha
end PPLLAstraFreshStable
