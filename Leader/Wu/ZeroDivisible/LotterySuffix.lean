import Leader.Wu.ZeroDivisible.SuffixSurvival

/-!
# Lottery fields after the actual R5 CHECK cut

DISAPPEAR performs the lottery update. ReadyAck repair, COMPARE, K4 and
WRITE retain its lottery fields; suppression and conservation may instead
clear the same endpoint's main path. The private projection includes that
path so a deletion remains visible through composition.

The public contracts use the actual named suffix and full pipeline with
original conservation inputs. They impose no state, path, token, leader,
label or auxiliary-field conditions. Prefix preservation, head-toss state
invariants and sweep termination are separate obligations.
-/
namespace PPLLAstraR5LotterySuffix
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLElimVariants
open PPLLAstraR5Repair
set_option autoImplicit false

private def core {ψ : Nat} (u : AgentState ψ) := (u.p,u.p_carry,u.path)
private theorem view_p {ψ : Nat} {a b : AgentState ψ} (h : core a=core b) : a.p=b.p :=
  congrArg Prod.fst h
private theorem view_carry {ψ : Nat} {a b : AgentState ψ} (h : core a=core b) : a.p_carry=b.p_carry :=
  congrArg (fun x => x.2.1) h
private theorem view_path {ψ : Nat} {a b : AgentState ψ} (h : core a=core b) : a.path=b.path :=
  congrArg (fun x => x.2.2) h
private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1=if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2=if p then a.2 else b.2 := by split <;> rfl
private theorem p_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).p=if p then a.p else b.p := by split <;> rfl
private theorem carry_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).p_carry=if p then a.p_carry else b.p_carry := by split <;> rfl
private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path=if p then a.path else b.path := by split <;> rfl
private theorem core_ite {ψ : Nat} (p : Prop) [Decidable p] (a b : AgentState ψ) :
    core (if p then a else b)=if p then core a else core b := by split <;> rfl
attribute [local simp] fst_ite snd_ite p_ite carry_ite path_ite core_ite

private def Mono {ψ : Nat} (a b : AgentState ψ) := b.path=.bot ∨ core b=core a
private def PairMono {ψ : Nat} (a b : AgentState ψ × AgentState ψ) := Mono a.1 b.1 ∧ Mono a.2 b.2
private theorem mono_trans {ψ : Nat} {a b c : AgentState ψ} (h : Mono a b) (k : Mono b c) : Mono a c := by
  rcases k with kc | kc
  · exact Or.inl kc
  · rcases h with hb | hb
    · exact Or.inl ((view_path kc).trans hb)
    · exact Or.inr (kc.trans hb)
private theorem pair_trans {ψ : Nat} {a b c : AgentState ψ × AgentState ψ}
    (h : PairMono a b) (k : PairMono b c) : PairMono a c :=
  ⟨mono_trans h.1 k.1,mono_trans h.2 k.2⟩

private theorem suppress_mono {ψ : Nat} (hp : ψ>0) (l r : AgentState ψ) :
    PairMono (l,r) (suppressSigResetKill hp l r) := by
  cases h1 : l.leader <;> cases h2 : l.reset_cmd <;>
    cases h3 : r.reset_cmd <;> cases h4 : r.echo <;>
    simp [PairMono,Mono,core,suppressSigResetKill,suppressSigStart,
      suppressSigMoveReset,suppressSigTerminal,suppressSigEcho,suppressSigFinish,
      clearCmp,h1,h2,h3,h4] <;>
    repeat (first | split) <;> simp_all [PairMono,Mono,core,clearCmp]

private theorem kernel_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    core (k4Kernel hp l r).1 = core l ∧
    core (k4Kernel hp l r).2 = core r := by
  simp only [k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire,
    absorbAnyMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp only [core, fst_ite, snd_ite, carry_ite, path_ite,p_ite,
    ite_self, and_self]


namespace Writer


private theorem writeActionApplyOverwrite_view {ψ : Nat}
    (u : AgentState ψ) :
    core (writeActionApplyOverwrite u) = core u := by
  unfold writeActionApplyOverwrite
  cases u.path3 <;> rfl


private theorem writeActionApplyMoveFlip_view {ψ : Nat}
    (u : AgentState ψ) :
    core (writeActionApplyMoveFlip u) = core u := by
  unfold writeActionApplyMoveFlip
  cases u.path3 <;> rfl


private theorem moveWsigCheckLast_view {ψ : Nat}
    (u : AgentState ψ) :
    core (moveWsigCheckLast u) = core u := by
  cases hp : u.path3 <;>
    simp [moveWsigCheckLast, hp, core]


private theorem writeSeqSetWriteReady_view {ψ : Nat}
    (u : AgentState ψ) :
    core (writeSeqSetWriteReady u) = core u := by
  cases hp : u.path3 <;>
    simp [writeSeqSetWriteReady, hp, core]


private theorem writeSeqCheckBit_view {ψ : Nat}
    (u : AgentState ψ) :
    core (writeSeqCheckBit u) = core u := by
  cases hp : u.path3 <;>
    simp [writeSeqCheckBit, hp, core]


private theorem writeSeqSetWriteAct_view {ψ : Nat}
    (u : AgentState ψ) :
    core (writeSeqSetWriteAct u) = core u := by
  cases hp : u.path3 <;>
    simp [writeSeqSetWriteAct, hp, core]


private theorem writeSeqFinalR_view {ψ : Nat}
    (u : AgentState ψ) :
    core (writeSeqFinalR u) = core u := by
  cases hp : u.path3 <;>
    simp [writeSeqFinalR, hp, core]


private theorem moveWsigCheckGenWs_view {ψ : Nat}
    (l r : AgentState ψ) :
    core (moveWsigCheckGenWs l r) = core r := by
  cases hp : l.path3 <;>
    simp [moveWsigCheckGenWs, hp, core]


private theorem moveWsigTransfer_view {ψ : Nat}
    (l r : AgentState ψ) :
    core (moveWsigTransfer l r).1 = core l ∧
    core (moveWsigTransfer l r).2 = core r := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp [moveWsigTransfer, hl, hr, core, fst_ite, snd_ite, core_ite]


private theorem groupInfo_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    core (groupInfo hp l r).1 = core l ∧
    core (groupInfo hp l r).2 = core r := by
  simp only [groupInfo, fst_ite, snd_ite, core_ite, core,
    carry_ite, path_ite,p_ite, ite_self, and_self]


private theorem gensigWriteseq_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    core (gensigWriteseq hp l r).1 = core l ∧
    core (gensigWriteseq hp l r).2 = core r := by
  simp only [gensigWriteseq, fst_ite, snd_ite, core_ite, core,
    carry_ite, path_ite,p_ite, ite_self, and_self]


private theorem writeAction_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    core (writeAction hp l r).1 = core l ∧
    core (writeAction hp l r).2 = core r := by
  simp only [writeAction, fst_ite, snd_ite, core_ite, core,
    carry_ite, path_ite,p_ite, ite_self, and_self,
    (view_p (writeActionApplyOverwrite_view _)), (view_carry (writeActionApplyOverwrite_view _)), (view_path (writeActionApplyOverwrite_view _)), (view_p (writeActionApplyMoveFlip_view _)), (view_carry (writeActionApplyMoveFlip_view _)), (view_path (writeActionApplyMoveFlip_view _))]


private theorem moveWsig_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    core (moveWsig hp l r).1 = core l ∧
    core (moveWsig hp l r).2 = core r := by
  simp only [moveWsig, fst_ite, snd_ite, core_ite, core,
    carry_ite, path_ite,p_ite, ite_self, and_self,
    (view_p (moveWsigCheckGenWs_view _ _)), (view_carry (moveWsigCheckGenWs_view _ _)), (view_path (moveWsigCheckGenWs_view _ _)), (view_p (moveWsigCheckLast_view _)), (view_carry (moveWsigCheckLast_view _)), (view_path (moveWsigCheckLast_view _)),
    (view_p (moveWsigTransfer_view _ _).1), (view_carry (moveWsigTransfer_view _ _).1), (view_path (moveWsigTransfer_view _ _).1), (view_p (moveWsigTransfer_view _ _).2), (view_carry (moveWsigTransfer_view _ _).2), (view_path (moveWsigTransfer_view _ _).2)]


private theorem writeSeq_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    core (writeSeq hp l r).1 = core l ∧
    core (writeSeq hp l r).2 = core r := by
  simp only [writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare,
    writeSeqReady, writeSeqCompare, writeSeqCommands,
    fst_ite, snd_ite, core_ite, core, carry_ite, path_ite,p_ite,
    ite_self, and_self,
    (view_p (groupInfo_view _ _ _).1), (view_carry (groupInfo_view _ _ _).1), (view_path (groupInfo_view _ _ _).1), (view_p (groupInfo_view _ _ _).2), (view_carry (groupInfo_view _ _ _).2), (view_path (groupInfo_view _ _ _).2),
    (view_p (gensigWriteseq_view _ _ _).1), (view_carry (gensigWriteseq_view _ _ _).1), (view_path (gensigWriteseq_view _ _ _).1), (view_p (gensigWriteseq_view _ _ _).2), (view_carry (gensigWriteseq_view _ _ _).2), (view_path (gensigWriteseq_view _ _ _).2),
    (view_p (writeAction_view _ _ _).1), (view_carry (writeAction_view _ _ _).1), (view_path (writeAction_view _ _ _).1), (view_p (writeAction_view _ _ _).2), (view_carry (writeAction_view _ _ _).2), (view_path (writeAction_view _ _ _).2),
    (view_p (moveWsig_view _ _ _).1), (view_carry (moveWsig_view _ _ _).1), (view_path (moveWsig_view _ _ _).1), (view_p (moveWsig_view _ _ _).2), (view_carry (moveWsig_view _ _ _).2), (view_path (moveWsig_view _ _ _).2),
    (view_p (writeSeqSetWriteReady_view _)), (view_carry (writeSeqSetWriteReady_view _)), (view_path (writeSeqSetWriteReady_view _)), (view_p (writeSeqCheckBit_view _)), (view_carry (writeSeqCheckBit_view _)), (view_path (writeSeqCheckBit_view _)),
    (view_p (writeSeqSetWriteAct_view _)), (view_carry (writeSeqSetWriteAct_view _)), (view_path (writeSeqSetWriteAct_view _)), (view_p (writeSeqFinalR_view _)), (view_carry (writeSeqFinalR_view _)), (view_path (writeSeqFinalR_view _))]


theorem writeWithBundle_view {ψ : Nat} (hp : ψ > 0)
    (l r : AgentState ψ) :
    core (writeWithBundle hp l r).1 = core l ∧
    core (writeWithBundle hp l r).2 = core r := by
  have h := writeSeq_view hp l r
  simp only [writeWithBundle, fst_ite, snd_ite, core_ite, core,
    carry_ite, path_ite,p_ite, view_p h.1, view_carry h.1, view_path h.1, view_p h.2, view_carry h.2, view_path h.2, ite_self, and_self]


end Writer

private theorem conserve_mono {ψ : Nat} (l r : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) : PairMono q (conserve .head l r q) := by
  unfold conserve
  split <;> simp [PairMono,Mono,core,replacement,clearCmp]

private theorem finish_mono {ψ : Nat} (hp : ψ>0) (origL origR l r : AgentState ψ) :
    PairMono (l,r) (SuffixInterfaces.finishAfterCompare hp origL origR l r) := by
  let a := suppressSigResetKill hp l r
  let b := k4Kernel hp a.1 a.2
  let w := writeWithBundle hp b.1 b.2
  have ha : PairMono (l,r) a := suppress_mono hp l r
  have hb : PairMono a b := ⟨Or.inr (kernel_view hp a.1 a.2).1,Or.inr (kernel_view hp a.1 a.2).2⟩
  have hw : PairMono b w := ⟨Or.inr (Writer.writeWithBundle_view hp b.1 b.2).1,
    Or.inr (Writer.writeWithBundle_view hp b.1 b.2).2⟩
  exact pair_trans (pair_trans (pair_trans ha hb) hw) (conserve_mono origL origR w)

private theorem releaseCongest_view {ψ : Nat} (u : AgentState ψ) : core (releaseCongest u)=core u := by
  simp [releaseCongest,core]
private theorem orphan_view {ψ : Nat} (u : AgentState ψ) : core (normalizeOrphan u)=core u := by
  cases h : u.path <;> simp [normalizeOrphan,h,core]
private theorem carrier_view {ψ : Nat} (u : AgentState ψ) : core (normalizeCarrier u)=core u := by
  cases h : u.path <;> simp [normalizeCarrier,h,releaseCongest,core]

private theorem release_view {ψ : Nat} (l r : AgentState ψ) :
    core (releaseReadySuffix l r).1=core l ∧ core (releaseReadySuffix l r).2=core r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [releaseReadySuffix,hl,hr,core]
private theorem ack_view {ψ : Nat} (l r : AgentState ψ) :
    core (ackTail l r).1=core l ∧ core (ackTail l r).2=core r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [ackTail,hl,hr,core]
private theorem repair_view {ψ : Nat} (l r : AgentState ψ) :
    core (repair .readyAck l r).1=core l ∧ core (repair .readyAck l r).2=core r := by
  simp only [repair,(ack_view _ _).1,(ack_view _ _).2,
    (release_view _ _).1,(release_view _ _).2,carrier_view,orphan_view,and_self]

private theorem maintain_view {ψ : Nat} (l r : AgentState ψ) :
    core (maintain l r).1=core l ∧ core (maintain l r).2=core r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [maintain,hl,hr,core]
private theorem complete_view {ψ : Nat} (l r : AgentState ψ) :
    core (completeWave l r).1=core l ∧ core (completeWave l r).2=core r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [completeWave,hl,hr,core]
private theorem wave_view {ψ : Nat} (l r : AgentState ψ) :
    core (wave l r).1=core l ∧ core (wave l r).2=core r := by
  cases hl : l.path <;> cases hr : r.path <;> simp [wave,hl,hr,core]
private theorem drop_view {ψ : Nat} (l r : AgentState ψ) :
    core (dropStray l r).1=core l ∧ core (dropStray l r).2=core r := by
  cases hl : l.path2 <;> cases hr : r.path2 <;> simp [dropStray,hl,hr,core]
private theorem backward_view {ψ : Nat} (u : AgentState ψ) : core (landBackward u)=core u := by
  cases hp : u.path <;> cases ht : u.path2 <;> simp [landBackward,hp,ht,core]
private theorem forward_view {ψ : Nat} (κ : Nat) (u : AgentState ψ) : core (landForward κ false true u)=core u := by
  cases hp : u.path <;> cases ht : u.path2 <;> simp [landForward,hp,ht,core]
private theorem compare_view {ψ : Nat} (κ : Nat) (l r : AgentState ψ) :
    core (compareLifecycle κ l r).1=core l ∧ core (compareLifecycle κ l r).2=core r := by
  simp only [compareLifecycle,backward_view,forward_view,
    (drop_view _ _).1,(drop_view _ _).2,(wave_view _ _).1,(wave_view _ _).2,
    (complete_view _ _).1,(complete_view _ _).2,(maintain_view _ _).1,(maintain_view _ _).2]
  cases h : l.path <;> simp [h,core]

/-- From an arbitrary actual CHECK-cut pair, each completed suffix endpoint
either has an empty main path or keeps both lottery fields exactly as set
by DISAPPEAR. Original inputs remain present for the conservation guard. -/
theorem finishAfterCheck_lottery_or_hole {ψ : Nat} (hp : ψ>0) (κ : Nat)
    (origL origR l r : AgentState ψ) :
    let ds := disappear hp l r
    let z := SuffixInterfaces.finishAfterCheck hp κ origL origR l r
    (z.1.path=.bot ∨ (z.1.p,z.1.p_carry)=(ds.1.p,ds.1.p_carry)) ∧
    (z.2.path=.bot ∨ (z.2.p,z.2.p_carry)=(ds.2.p,ds.2.p_carry)) := by
  let ds := disappear hp l r
  let rr := repair .readyAck ds.1 ds.2
  let cp := compareLifecycle κ rr.1 rr.2
  have hrr := repair_view ds.1 ds.2
  have hcp := compare_view κ rr.1 rr.2
  have hs := finish_mono hp origL origR cp.1 cp.2
  change ( _ ∨ _) ∧ (_ ∨ _)
  constructor
  · rcases hs.1 with h | h
    · exact Or.inl h
    · exact Or.inr (congrArg (fun x => (x.1,x.2.1)) (h.trans (hcp.1.trans hrr.1)))
  · rcases hs.2 with h | h
    · exact Or.inl h
    · exact Or.inr (congrArg (fun x => (x.1,x.2.1)) (h.trans (hcp.2.trans hrr.2)))

/-- Universal full-R5 lottery suffix frame at the actual named CHECK cut.
No assumption concerns leaders, main states, labels, occupancy, token actions
or auxiliaries. This does not claim that the prefix preserved lottery data. -/
theorem pipeline_lottery_or_hole {ψ : Nat} (hp : ψ>0) (κ : Nat)
    (c : PPLLAstraR5Repair.Cfg) (l r : AgentState ψ) :
    let ch := SuffixInterfaces.throughCheck hp κ c l r
    let ds := disappear hp ch.1 ch.2
    let z := PPLLAstraR5Repair.pipeline hp κ c l r
    (z.1.path=.bot ∨ (z.1.p,z.1.p_carry)=(ds.1.p,ds.1.p_carry)) ∧
    (z.2.path=.bot ∨ (z.2.p,z.2.p_carry)=(ds.2.p,ds.2.p_carry)) := by
  rw [SuffixInterfaces.pipeline_eq_from_check]
  exact finishAfterCheck_lottery_or_hole hp κ l r _ _

/-- A pair hole already present at the actual CHECK cut survives its suffix.
This bridge permits a prefix consumer to stop on deletion without requiring
lottery-field equality on that deleted endpoint. Original inputs are raw. -/
theorem finishAfterCheck_pairHole {ψ : Nat} (hp : ψ>0) (κ : Nat)
    (origL origR l r : AgentState ψ) (h : l.path=.bot ∨ r.path=.bot) :
    let z := SuffixInterfaces.finishAfterCheck hp κ origL origR l r
    z.1.path=.bot ∨ z.2.path=.bot := by
  let ds := disappear hp l r
  let rr := repair .readyAck ds.1 ds.2
  let cp := compareLifecycle κ rr.1 rr.2
  have hd : ds.1.path=l.path ∧ ds.2.path=r.path := by
    simp only [ds,disappear,fst_ite,snd_ite,path_ite,ite_self,and_self]
  have hrr := repair_view ds.1 ds.2
  have hcp := compare_view κ rr.1 rr.2
  have hs := finish_mono hp origL origR cp.1 cp.2
  rcases h with h | h
  · left
    rcases hs.1 with hz | hf
    · exact hz
    · exact ((view_path (hf.trans (hcp.1.trans hrr.1))).trans hd.1).trans h
  · right
    rcases hs.2 with hz | hf
    · exact hz
    · exact ((view_path (hf.trans (hcp.2.trans hrr.2))).trans hd.2).trans h

#print axioms finishAfterCheck_lottery_or_hole
#print axioms pipeline_lottery_or_hole
#print axioms finishAfterCheck_pairHole
end PPLLAstraR5LotterySuffix
