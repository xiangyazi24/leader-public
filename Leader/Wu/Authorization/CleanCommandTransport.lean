import Leader.Wu.Authorization.CleanNoCommand
import Leader.Wu.Authorization.GenerationDrain

/-!
# CLEAN-command transport through the original AuthF row

The transport invariant allows an empty main path, whose old command slots
need not be empty. Occupied outputs must have neither distinguished command.
All fields and configurations are raw: no domain, follower, or mark premises
are added. This file uses fresh field frames for the CLEAN slots; the existing
generation views do not contain them.
-/

namespace PPLLAuthCheckNoCmdFrame

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
open PPLLAuthGenDrain (gfst_ite gsnd_ite gstate_ite gpath_ite)
open PPLLAuthCheckCleanNoCmd (NoCmd)

set_option autoImplicit false

variable {ψ : Nat}

def PathNoCmd (u : AuthState ψ) : Prop := u.core.path = .bot ∨ NoCmd u

private def CoreGood (u : AgentState ψ) : Prop :=
  u.path = .bot ∨ (isCmd u.path4 = false ∧ isCmd u.path5 = false)

private def Keeps (a b : AgentState ψ) : Prop := CoreGood a → CoreGood b

private theorem Keeps.refl (a : AgentState ψ) : Keeps a a := id
private theorem Keeps.trans {a b c : AgentState ψ} (h : Keeps a b) (k : Keeps b c) :
    Keeps a c := fun ha => k (h ha)
private theorem Keeps.fields {a b : AgentState ψ}
    (hp : b.path = a.path) (h4 : b.path4 = a.path4) (h5 : b.path5 = a.path5) :
    Keeps a b := by
  unfold Keeps CoreGood
  rw [hp,h4,h5]
  exact id
private theorem Keeps.hole {a b : AgentState ψ} (h : b.path = .bot) : Keeps a b :=
  fun _ => Or.inl h
private theorem Keeps.scrub {a b : AgentState ψ}
    (h4 : b.path4 = none) (h5 : b.path5 = none) : Keeps a b := by
  intro _
  exact Or.inr (by simp [h4,h5,isCmd])

private theorem slot4_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path4 = if p then a.path4 else b.path4 := by split <;> rfl
private theorem slot5_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path5 = if p then a.path5 else b.path5 := by split <;> rfl

/-! Fresh WRITE/K4 frames: state, main path, and both CLEAN slots. -/

namespace SlotFrame

def WF {ψ : Nat} (a b : AgentState ψ) : Prop :=
  a.state = b.state ∧ a.path = b.path ∧ a.path4 = b.path4 ∧ a.path5 = b.path5

private theorem writeActionApplyOverwrite_frame {ψ : Nat} (u : AgentState ψ) :
    WF (writeActionApplyOverwrite u) u := by
  unfold WF writeActionApplyOverwrite
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeActionApplyMoveFlip_frame {ψ : Nat} (u : AgentState ψ) :
    WF (writeActionApplyMoveFlip u) u := by
  unfold WF writeActionApplyMoveFlip
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem moveWsigCheckLast_frame {ψ : Nat} (u : AgentState ψ) :
    WF (moveWsigCheckLast u) u := by
  unfold WF moveWsigCheckLast
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeSeqSetWriteReady_frame {ψ : Nat} (u : AgentState ψ) :
    WF (writeSeqSetWriteReady u) u := by
  unfold WF writeSeqSetWriteReady
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeSeqCheckBit_frame {ψ : Nat} (u : AgentState ψ) :
    WF (writeSeqCheckBit u) u := by
  unfold WF writeSeqCheckBit
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem writeSeqSetWriteAct_frame {ψ : Nat} (u : AgentState ψ) :
    WF (writeSeqSetWriteAct u) u := by
  cases hp : u.path3 <;> simp only [WF, writeSeqSetWriteAct, hp] <;>
    simp [gstate_ite, gpath_ite, slot4_ite, slot5_ite, hp]

private theorem writeSeqFinalR_frame {ψ : Nat} (u : AgentState ψ) :
    WF (writeSeqFinalR u) u := by
  unfold WF writeSeqFinalR
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem moveWsigCheckGenWs_frame {ψ : Nat} (l r : AgentState ψ) :
    WF (moveWsigCheckGenWs l r) r := by
  unfold WF moveWsigCheckGenWs
  repeat (first | constructor | rfl | split)
  all_goals simp

private theorem moveWsigTransfer_frame {ψ : Nat} (l r : AgentState ψ) :
    WF (moveWsigTransfer l r).1 l ∧ WF (moveWsigTransfer l r).2 r := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp only [WF, moveWsigTransfer, hl, hr] <;>
    simp only [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, slot4_ite, slot5_ite, ite_self, and_self]

private theorem groupInfo_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WF (groupInfo hψ l r).1 l ∧ WF (groupInfo hψ l r).2 r := by
  simp only [WF, groupInfo]
  simp only [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, slot4_ite, slot5_ite, ite_self, and_self]

private theorem gensigWriteseq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WF (gensigWriteseq hψ l r).1 l ∧ WF (gensigWriteseq hψ l r).2 r := by
  simp only [WF, gensigWriteseq]
  simp only [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, slot4_ite, slot5_ite, ite_self, and_self]

private theorem writeAction_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WF (writeAction hψ l r).1 l ∧ WF (writeAction hψ l r).2 r := by
  simp only [WF, writeAction]
  simp only [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, slot4_ite, slot5_ite, ite_self, and_self,
    (writeActionApplyOverwrite_frame _).1, (writeActionApplyOverwrite_frame _).2.1,
    (writeActionApplyOverwrite_frame _).2.2.1, (writeActionApplyOverwrite_frame _).2.2.2,
    (writeActionApplyMoveFlip_frame _).1, (writeActionApplyMoveFlip_frame _).2.1,
    (writeActionApplyMoveFlip_frame _).2.2.1, (writeActionApplyMoveFlip_frame _).2.2.2]

private theorem moveWsig_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WF (moveWsig hψ l r).1 l ∧ WF (moveWsig hψ l r).2 r := by
  simp only [WF, moveWsig]
  simp only [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, slot4_ite, slot5_ite, ite_self, and_self,
    (moveWsigCheckGenWs_frame _ _).1, (moveWsigCheckGenWs_frame _ _).2.1,
    (moveWsigCheckGenWs_frame _ _).2.2.1, (moveWsigCheckGenWs_frame _ _).2.2.2,
    (moveWsigCheckLast_frame _).1, (moveWsigCheckLast_frame _).2.1,
    (moveWsigCheckLast_frame _).2.2.1, (moveWsigCheckLast_frame _).2.2.2,
    (moveWsigTransfer_frame _ _).1.1, (moveWsigTransfer_frame _ _).1.2.1,
    (moveWsigTransfer_frame _ _).1.2.2.1, (moveWsigTransfer_frame _ _).1.2.2.2,
    (moveWsigTransfer_frame _ _).2.1, (moveWsigTransfer_frame _ _).2.2.1,
    (moveWsigTransfer_frame _ _).2.2.2.1, (moveWsigTransfer_frame _ _).2.2.2.2]

theorem writeSeq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WF (writeSeq hψ l r).1 l ∧ WF (writeSeq hψ l r).2 r := by
  simp only [WF, writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands]
  simp only [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, slot4_ite, slot5_ite, ite_self, and_self,
    (groupInfo_frame _ _ _).1.1, (groupInfo_frame _ _ _).1.2.1,
    (groupInfo_frame _ _ _).1.2.2.1, (groupInfo_frame _ _ _).1.2.2.2,
    (groupInfo_frame _ _ _).2.1, (groupInfo_frame _ _ _).2.2.1,
    (groupInfo_frame _ _ _).2.2.2.1, (groupInfo_frame _ _ _).2.2.2.2,
    (gensigWriteseq_frame _ _ _).1.1, (gensigWriteseq_frame _ _ _).1.2.1,
    (gensigWriteseq_frame _ _ _).1.2.2.1, (gensigWriteseq_frame _ _ _).1.2.2.2,
    (gensigWriteseq_frame _ _ _).2.1, (gensigWriteseq_frame _ _ _).2.2.1,
    (gensigWriteseq_frame _ _ _).2.2.2.1, (gensigWriteseq_frame _ _ _).2.2.2.2,
    (writeAction_frame _ _ _).1.1, (writeAction_frame _ _ _).1.2.1,
    (writeAction_frame _ _ _).1.2.2.1, (writeAction_frame _ _ _).1.2.2.2,
    (writeAction_frame _ _ _).2.1, (writeAction_frame _ _ _).2.2.1,
    (writeAction_frame _ _ _).2.2.2.1, (writeAction_frame _ _ _).2.2.2.2,
    (moveWsig_frame _ _ _).1.1, (moveWsig_frame _ _ _).1.2.1,
    (moveWsig_frame _ _ _).1.2.2.1, (moveWsig_frame _ _ _).1.2.2.2,
    (moveWsig_frame _ _ _).2.1, (moveWsig_frame _ _ _).2.2.1,
    (moveWsig_frame _ _ _).2.2.2.1, (moveWsig_frame _ _ _).2.2.2.2,
    (writeSeqSetWriteReady_frame _).1, (writeSeqSetWriteReady_frame _).2.1,
    (writeSeqSetWriteReady_frame _).2.2.1, (writeSeqSetWriteReady_frame _).2.2.2,
    (writeSeqCheckBit_frame _).1, (writeSeqCheckBit_frame _).2.1,
    (writeSeqCheckBit_frame _).2.2.1, (writeSeqCheckBit_frame _).2.2.2,
    (writeSeqSetWriteAct_frame _).1, (writeSeqSetWriteAct_frame _).2.1,
    (writeSeqSetWriteAct_frame _).2.2.1, (writeSeqSetWriteAct_frame _).2.2.2,
    (writeSeqFinalR_frame _).1, (writeSeqFinalR_frame _).2.1,
    (writeSeqFinalR_frame _).2.2.1, (writeSeqFinalR_frame _).2.2.2]

theorem write_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WF (writeWithBundle hψ l r).1 l ∧ WF (writeWithBundle hψ l r).2 r := by
  have h := writeSeq_frame hψ l r
  simp only [WF] at h ⊢
  simp only [writeWithBundle, gfst_ite, gsnd_ite, gstate_ite, gpath_ite, slot4_ite, slot5_ite,
    h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, ite_self,
    and_self]

theorem kernel_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WF (k4Kernel hψ l r).1 l ∧ WF (k4Kernel hψ l r).2 r := by
  simp only [WF, k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire, absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, slot4_ite, slot5_ite]

end SlotFrame


/-! Elementary updates either retain all three fields, delete the path, or
clear both slots. These alternatives cover arrivals as well as resets. -/
local macro "ncclose" : tactic => `(tactic| first
  | exact Keeps.refl _
  | (apply Keeps.fields <;> rfl)
  | (apply Keeps.hole; rfl)
  | (apply Keeps.scrub <;> rfl)
  | (simp only [AuthState.withCore, AuthState.dropP2, AuthState.setState,
      AuthState.lineage, clearCmpAuth, clearCmp, AuthState.st]
     first
     | exact Keeps.refl _
     | (apply Keeps.fields <;> rfl)
     | (apply Keeps.hole; rfl)
     | (apply Keeps.scrub <;> rfl)))
local macro "ncsplit" : tactic => `(tactic|
  ((repeat' (first | (dsimp only) | split)) <;>
    (first | (constructor <;> ncclose) | ncclose)))

theorem releaseSource_mono (hψ : ψ > 0) (l r : AgentState ψ) :
    Keeps l (releaseSource hψ l r).1 ∧ Keeps r (releaseSource hψ l r).2 := by
  unfold releaseSource; ncsplit

theorem eliminate_mono (hψ : ψ > 0) (l r : AgentState ψ) :
    Keeps l (eliminateSig hψ l r).1 ∧ Keeps r (eliminateSig hψ l r).2 := by
  unfold eliminateSig; ncsplit

theorem control_mono (hψ : ψ > 0) (u : AgentState ψ) :
    Keeps u (sigMoveApplyControlConsume hψ u) := by
  unfold sigMoveApplyControlConsume; ncsplit

theorem dropStale_mono (u : AgentState ψ) : Keeps u (dropStale u) := by
  unfold dropStale; ncsplit

theorem orphan_mono (u : AgentState ψ) : Keeps u (normalizeOrphan u) := by
  unfold normalizeOrphan; ncsplit

theorem releaseCongest_mono (u : AgentState ψ) : Keeps u (releaseCongest u) := by
  unfold releaseCongest; ncsplit

theorem carrier_mono (u : AgentState ψ) : Keeps u (normalizeCarrier u) := by
  unfold normalizeCarrier
  split
  · exact Keeps.refl _
  · split
    · exact releaseCongest_mono u
    · split <;> ncclose

theorem checkReady_mono (u : AgentState ψ) : Keeps u (checkSigSetReadyGuarded u) := by
  unfold checkSigSetReadyGuarded checkSigSetReady; ncsplit

theorem checkL_mono (hψ : ψ > 0) (u : AgentState ψ) : Keeps u (checkSigCheckL hψ u) := by
  unfold checkSigCheckL; ncsplit

theorem checkR_mono (hψ : ψ > 0) (l r : AgentState ψ) : Keeps r (checkSigCheckR hψ l r) := by
  unfold checkSigCheckR; ncsplit

theorem result_mono (u : AgentState ψ) : Keeps u (checkSigSetResult u) := by
  unfold checkSigSetResult; ncsplit

theorem disStart_mono (hψ : ψ > 0) (l r : AgentState ψ) :
    Keeps l (disappearStartL hψ l r).1 ∧ Keeps r (disappearStartL hψ l r).2 := by
  unfold disappearStartL; ncsplit

theorem disCarry_mono (hψ : ψ > 0) (l r : AgentState ψ) :
    Keeps l (disappearCarry hψ l r).1 ∧ Keeps r (disappearCarry hψ l r).2 := by
  unfold disappearCarry; ncsplit

theorem releaseSuffix_mono (l r : AgentState ψ) :
    Keeps l (releaseReadySuffix l r).1 ∧ Keeps r (releaseReadySuffix l r).2 := by
  unfold releaseReadySuffix; ncsplit

theorem ackTail_mono (l r : AgentState ψ) :
    Keeps l (ackTail l r).1 ∧ Keeps r (ackTail l r).2 := by
  unfold ackTail; ncsplit

theorem dropStray_mono (l r : AgentState ψ) :
    Keeps l (PPLLFableDesignR1.dropStray l r).1 ∧ Keeps r (PPLLFableDesignR1.dropStray l r).2 := by
  unfold PPLLFableDesignR1.dropStray; ncsplit

theorem landBackward_mono (u : AgentState ψ) : Keeps u (PPLLFableDesignR1.landBackward u) := by
  unfold PPLLFableDesignR1.landBackward; ncsplit

theorem landForward_mono (κ : Nat) (d e : Bool) (u : AgentState ψ) :
    Keeps u (PPLLFableDesignR1.landForward κ d e u) := by
  unfold PPLLFableDesignR1.landForward; ncsplit



/-! Endpoint-local transport across AuthF lifts and comparison stages. -/
private def KeepsA (a b : AuthState ψ) : Prop := Keeps a.core b.core
private theorem KeepsA.refl (a : AuthState ψ) : KeepsA a a := Keeps.refl _
private theorem KeepsA.trans {a b c : AuthState ψ} (h : KeepsA a b) (k : KeepsA b c) :
    KeepsA a c := Keeps.trans h k
private def KeepsPair (q : AuthState ψ × AuthState ψ) (l r : AuthState ψ) : Prop :=
  KeepsA l q.1 ∧ KeepsA r q.2
private theorem KeepsPair.refl (l r : AuthState ψ) : KeepsPair (l,r) l r :=
  ⟨KeepsA.refl _,KeepsA.refl _⟩
private theorem KeepsPair.trans {l r : AuthState ψ} {q q' : AuthState ψ × AuthState ψ}
    (h : KeepsPair q l r) (k : KeepsPair q' q.1 q.2) : KeepsPair q' l r :=
  ⟨h.1.trans k.1,h.2.trans k.2⟩

open PPLLAuthGenDrain (csA csB csC csD csE csF csG csH checkSource_eq cmp0 cmpTail compare_eq)

theorem liftLife_mono (f : AgentState ψ → AgentState ψ) (hf : ∀ a, Keeps a (f a))
    (u : AuthState ψ) : KeepsA u (liftLife f u) := by
  unfold liftLife; dsimp only
  split
  · exact hf u.core
  · exact hf u.core

theorem lift2_pm (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, Keeps a (f a b).1 ∧ Keeps b (f a b).2) (l r : AuthState ψ) :
    KeepsPair (lift2 f l r) l r := hf l.core r.core

theorem lift2Life_pm (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, Keeps a (f a b).1 ∧ Keeps b (f a b).2) (l r : AuthState ψ) :
    KeepsPair (lift2Life f l r) l r := by
  have h := hf l.core r.core
  unfold lift2Life KeepsPair
  constructor
  · dsimp only
    split
    · exact h.1
    · exact h.1
  · dsimp only
    split
    · exact h.2
    · exact h.2

theorem clearAuth_mono (u : AuthState ψ) : KeepsA u (clearCmpAuth u) := by
  apply Keeps.hole
  rfl

theorem dropP2_mono (u : AuthState ψ) : KeepsA u u.dropP2 := Keeps.fields rfl rfl rfl

theorem validate_pm (l r : AuthState ψ) : KeepsPair (validateCheck l r) l r := by
  unfold validateCheck KeepsPair demote; ncsplit

theorem sanitize_mono (u : AuthState ψ) : KeepsA u (sanitizeP2 u) := by
  unfold sanitizeP2; ncsplit

theorem step1_pm (l r : AuthState ψ) : KeepsPair (step1Auth l r) l r := by
  unfold step1Auth KeepsPair; ncsplit

theorem receive_mono (e : Entry) (src dst : AuthState ψ) (t : Path2Info) :
    KeepsA dst (receive e src dst t) := by
  unfold receive claimA2; ncsplit

theorem receive_drop_mono (e : Entry) (src dst : AuthState ψ) (t : Path2Info) (b : Prop)
    [Decidable b] : KeepsA dst (receive e src (if b then dst.dropP2 else dst) t) := by
  split
  · exact KeepsA.trans (dropP2_mono dst) (receive_mono e src _ t)
  · exact receive_mono e src dst t

private def tokenQueue (eL eR : Entry) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  match l.core.path2, r.core.path2 with
  | some tl, some tr =>
    if canMoveR l.core tl ∧ canMoveL r.core tr then
      (receive eL r l (dec tr), receive eR l r (dec tl))
    else if canMoveR l.core tl ∧ rightward tr ∧ canMoveR r.core tr then
      (l.dropP2, r)
    else if canMoveL r.core tr ∧ leftward tl ∧ canMoveL l.core tl then
      (l, r.dropP2)
    else (l, r)
  | some tl, none =>
    if canMoveR l.core tl then (l.dropP2, receive eR l r (dec tl)) else (l, r)
  | none, some tr =>
    if canMoveL r.core tr then (receive eL r l (dec tr), r.dropP2) else (l, r)
  | none, none => (l, r)


private theorem tokenQueue_keeps (eL eR : Entry) (l r : AuthState ψ) :
    KeepsPair (tokenQueue eL eR l r) l r := by
  cases h1 : l.core.path2 <;> cases h2 : r.core.path2 <;>
    simp only [tokenQueue,h1,h2] <;>
    (repeat' (first | (dsimp only) | split)) <;>
    (constructor <;> first
      | exact KeepsA.refl _
      | exact dropP2_mono _
      | exact receive_mono _ _ _ _)

private theorem tokenQueue_drop_keeps (eL eR : Entry) (l r : AuthState ψ) :
    KeepsPair (tokenQueue eL eR
      (if eR = .reject then l.dropP2 else l)
      (if eL = .reject then r.dropP2 else r)) l r := by
  have hl : KeepsA l (if eR = .reject then l.dropP2 else l) := by
    split
    · exact dropP2_mono _
    · exact KeepsA.refl _
  have hr : KeepsA r (if eL = .reject then r.dropP2 else r) := by
    split
    · exact dropP2_mono _
    · exact KeepsA.refl _
  have hq := tokenQueue_keeps eL eR
    (if eR = .reject then l.dropP2 else l)
    (if eL = .reject then r.dropP2 else r)
  exact ⟨hl.trans hq.1,hr.trans hq.2⟩

private def retirement4 (c : PPLLAuthF.Cfg) (l r : AuthState ψ) : Bool :=
  match l.core.path2 with
    | some tl => c.retire && tl.action == 4 && l.path2_scope == .line && p2Valid l &&
        canMoveR l.core tl && r.hasPath && l.path2_mark != r.path_mark
    | none => false

private def retirement2 (c : PPLLAuthF.Cfg) (l r : AuthState ψ) : Bool :=
  match r.core.path2 with
    | some tr => c.retire && tr.action == 2 && r.path2_scope == .session && p2Valid r &&
        canMoveL r.core tr && l.hasPath &&
        (waveState l.st || l.st == .CHECK_ready || l.st == .equal || l.st == .larger || l.st == .less) &&
        l.ctrl_mark != r.path2_mark && !claimable c.claimCheck l
    | none => false

private def moveTokensFactored (c : PPLLAuthF.Cfg) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let cc := c.claimCheck
  let failA4 := retirement4 c l r
  let failA2 := retirement2 c l r
  if failA4 || failA2 then
    ((if failA4 then clearCmpAuth l else l), (if failA2 then clearCmpAuth r else r))
  else
  let eR : Entry := match l.core.path2 with
    | some tl => if canMoveR l.core tl then entry cc l r tl else .ok
    | none => .ok
  let eL : Entry := match r.core.path2 with
    | some tr => if canMoveL r.core tr then entry cc r l tr else .ok
    | none => .ok
  let l := if eR = .reject then l.dropP2 else l
  let r := if eL = .reject then r.dropP2 else r
  tokenQueue eL eR l r

private theorem moveTokens_eq (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    moveTokensAuth c l r = moveTokensFactored c l r := rfl

theorem moveTokens_pm (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    KeepsPair (moveTokensAuth c l r) l r := by
  rw [moveTokens_eq]
  unfold moveTokensFactored
  dsimp only
  generalize retirement4 c l r = b4
  generalize retirement2 c l r = b2
  by_cases hret : (b4 || b2) = true
  · rw [if_pos hret]
    unfold KeepsPair
    constructor
    · change KeepsA l (if b4 then clearCmpAuth l else l)
      split
      · exact clearAuth_mono l
      · exact KeepsA.refl l
    · change KeepsA r (if b2 then clearCmpAuth r else r)
      split
      · exact clearAuth_mono r
      · exact KeepsA.refl r
  · rw [if_neg hret]
    exact tokenQueue_drop_keeps _ _ l r

theorem leaderWall_pm (l r : AuthState ψ) : KeepsPair (leaderWallAuth l r) l r := by
  unfold leaderWallAuth KeepsPair
  dsimp only
  refine ⟨?_, ?_⟩ <;> split
  all_goals first | exact clearAuth_mono _ | exact KeepsA.refl _

theorem applyControl_mono (hψ : ψ > 0) (u : AuthState ψ) : KeepsA u (applyControlAuth hψ u) := by
  unfold applyControlAuth
  (repeat' (first | (dsimp only) | split))
  all_goals first
    | exact KeepsA.refl _
    | exact dropP2_mono _
    | exact control_mono hψ u.core

theorem moveSource_pm (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    KeepsPair (moveSourceAuth hψ c l r) l r := by
  unfold moveSourceAuth
  dsimp only
  have ha : KeepsA l (if l.core.leader = true ∨ (r.core.leader = true ∧
      r.core.label ≠ ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) then clearCmpAuth l else l) := by
    split
    · exact clearAuth_mono l
    · exact KeepsA.refl l
  have hb : KeepsA r (if r.core.leader = true then clearCmpAuth r else r) := by
    split
    · exact clearAuth_mono r
    · exact KeepsA.refl r
  generalize (if l.core.leader = true ∨ (r.core.leader = true ∧
      r.core.label ≠ ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) then clearCmpAuth l else l) = l0 at ha ⊢
  generalize (if r.core.leader = true then clearCmpAuth r else r) = r0 at hb ⊢
  have h1 := validate_pm l0 r0
  generalize validateCheck l0 r0 = q1 at h1 ⊢
  obtain ⟨l1, r1⟩ := q1
  have s1 := sanitize_mono l1
  have s2 := sanitize_mono r1
  generalize sanitizeP2 l1 = l2 at s1 ⊢
  generalize sanitizeP2 r1 = r2 at s2 ⊢
  have h3 : KeepsPair (if l2.st = MainState.done then (l2, r2) else step1Auth l2 r2) l2 r2 := by
    split
    · exact KeepsPair.refl l2 r2
    · exact step1_pm l2 r2
  generalize (if l2.st = MainState.done then (l2, r2) else step1Auth l2 r2) = q3 at h3 ⊢
  obtain ⟨l3, r3⟩ := q3
  have h4 := moveTokens_pm c l3 r3
  generalize moveTokensAuth c l3 r3 = q4 at h4 ⊢
  obtain ⟨l4, r4⟩ := q4
  have h5 := leaderWall_pm l4 r4
  generalize leaderWallAuth l4 r4 = q5 at h5 ⊢
  obtain ⟨l5, r5⟩ := q5
  have a1 := applyControl_mono hψ l5
  have a2 := applyControl_mono hψ r5
  generalize applyControlAuth hψ l5 = l6 at a1 ⊢
  generalize applyControlAuth hψ r5 = r6 at a2 ⊢
  have h7 : KeepsA l6 (if r6.st = MainState.depart ∧ l6.core.label.val < ψ - 1 ∧
      l6.st = MainState.CHECK_ready then l6.lineage MainState.depart else l6) := by
    split
    · ncclose
    · exact KeepsA.refl l6
  exact ⟨ha.trans (h1.1.trans (s1.trans (h3.1.trans (h4.1.trans (h5.1.trans (a1.trans h7)))))),
    hb.trans (h1.2.trans (s2.trans (h3.2.trans (h4.2.trans (h5.2.trans a2)))))⟩

theorem preCheck_pm (l r : AuthState ψ) : KeepsPair (preCheckResetAuth l r) l r := by
  unfold preCheckResetAuth KeepsPair
  dsimp only
  refine ⟨?_, ?_⟩ <;> split
  all_goals first | exact clearAuth_mono _ | exact KeepsA.refl _

theorem normalizeReady_mono (u : AgentState ψ) : Keeps u (normalizeReady u) := by
  unfold normalizeReady
  dsimp only
  have h1 := orphan_mono u
  generalize normalizeOrphan u = u1 at h1 ⊢
  have h2 : Keeps u1 (if u1.state = MainState.none ∧ aligned u1 = true then u1
      else normalizeCarrier u1) := by
    split
    · exact Keeps.refl _
    · exact carrier_mono u1
  generalize (if u1.state = MainState.none ∧ aligned u1 = true then u1
      else normalizeCarrier u1) = u2 at h2 ⊢
  refine h1.trans (h2.trans ?_)
  ncsplit

theorem readyAuth_mono (u : AuthState ψ) : KeepsA u (readyAuth u) := by
  unfold readyAuth
  dsimp only
  split
  · exact KeepsA.refl u
  · have h := checkReady_mono u.core
    split
    · exact h
    · exact h

theorem issue_mono (u : AuthState ψ) : KeepsA u (issue u) := by
  unfold issue
  split
  · exact result_mono u.core
  · exact KeepsA.refl u

theorem checkSource_pm (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    KeepsPair (checkSourceAuth hψ c l r) l r := by
  rw [checkSource_eq]
  have h1 := validate_pm l r
  generalize validateCheck l r = q1 at h1 ⊢
  obtain ⟨l1, r1⟩ := q1
  have h2 : KeepsPair (csA c l1 r1) l1 r1 := by
    unfold csA
    constructor
    · dsimp only; split
      · exact readyAuth_mono l1
      · exact KeepsA.refl l1
    · dsimp only; split
      · exact readyAuth_mono r1
      · exact KeepsA.refl r1
  dsimp only
  generalize csA c l1 r1 = q2 at h2 ⊢
  obtain ⟨l2, r2⟩ := q2
  dsimp only
  have h3 : KeepsA l2 (csB l2 r2) := by
    unfold csB; split
    · ncclose
    · exact KeepsA.refl l2
  have h4 : KeepsA (csB l2 r2) (csC hψ (csB l2 r2)) := checkL_mono hψ _
  generalize csC hψ (csB l2 r2) = l4 at h4 ⊢
  generalize certPred l4 r2 = cert
  have h5 : KeepsA r2 (csD c cert r2) := by
    unfold csD; split
    · dsimp only; split
      · exact checkReady_mono r2.core
      · exact KeepsA.refl r2
    · exact KeepsA.refl r2
  have h6 : KeepsA (csD c cert r2) (csE hψ cert l4 (csD c cert r2)) := by
    unfold csE; split
    · exact checkR_mono hψ _ _
    · exact KeepsA.refl _
  have h7 : KeepsA l4 (csF l4) := by
    unfold csF; split
    · exact issue_mono l4
    · exact KeepsA.refl l4
  have h8 : ∀ u : AuthState ψ, KeepsA u (csG cert u) := by
    intro u; unfold csG; split
    · exact issue_mono u
    · exact KeepsA.refl u
  have h9 : ∀ a b : AuthState ψ, KeepsPair (csH hψ cert a b) a b := by
    intro a b; unfold csH; dsimp only; split
    · exact ⟨KeepsA.refl _, Keeps.fields rfl rfl rfl⟩
    · exact KeepsPair.refl a b
  exact KeepsPair.trans (q := (csF l4, csG cert (csE hψ cert l4 (csD c cert r2))))
    ⟨h1.1.trans (h2.1.trans (h3.trans (h4.trans h7))),
     h1.2.trans (h2.2.trans (h5.trans (h6.trans (h8 _))))⟩ (h9 _ _)

theorem disappear_pm (hψ : ψ > 0) (l r : AuthState ψ) : KeepsPair (disappearAuth hψ l r) l r := by
  unfold disappearAuth
  dsimp only
  have h0 : KeepsA r (if r.st = MainState.toss ∧ r.core.label = ⟨0, hψ⟩ then
      { r with core := { r.core with state := MainState.toss_done, path2 := some ⟨0, 0, 0, 5⟩,
                                      p := false },
               path2_scope := P2Scope.line, path2_mark := r.ctrl_mark }
      else r) := by
    split
    · ncclose
    · exact KeepsA.refl r
  generalize (if r.st = MainState.toss ∧ r.core.label = ⟨0, hψ⟩ then
      { r with core := { r.core with state := MainState.toss_done, path2 := some ⟨0, 0, 0, 5⟩,
                                      p := false },
               path2_scope := P2Scope.line, path2_mark := r.ctrl_mark }
      else r) = r0 at h0 ⊢
  have h1 := lift2_pm (disappearStartL hψ) (disStart_mono hψ) l r0
  generalize lift2 (disappearStartL hψ) l r0 = q1 at h1 ⊢
  obtain ⟨l1, r1⟩ := q1
  have h2 := lift2_pm (disappearCarry hψ) (disCarry_mono hψ) l1 r1
  exact ⟨h1.1.trans h2.1, h0.trans (h1.2.trans h2.2)⟩

theorem repair_pm (l r : AuthState ψ) : KeepsPair (repairAuth l r) l r := by
  unfold repairAuth
  dsimp only
  have hc : ∀ a : AgentState ψ, Keeps a (normalizeCarrier (normalizeOrphan a)) :=
    fun a => (orphan_mono a).trans (carrier_mono _)
  have h1 := liftLife_mono _ hc l
  have h2 := liftLife_mono _ hc r
  generalize liftLife (fun u => normalizeCarrier (normalizeOrphan u)) l = l1 at h1 ⊢
  generalize liftLife (fun u => normalizeCarrier (normalizeOrphan u)) r = r1 at h2 ⊢
  have h3 := lift2Life_pm releaseReadySuffix releaseSuffix_mono l1 r1
  generalize lift2Life releaseReadySuffix l1 r1 = q3 at h3 ⊢
  obtain ⟨l3, r3⟩ := q3
  have h4 : KeepsPair (ackTailAuth l3 r3) l3 r3 := by
    unfold ackTailAuth
    split
    · exact lift2_pm ackTail ackTail_mono l3 r3
    · exact KeepsPair.refl l3 r3
  exact ⟨h1.trans (h3.1.trans h4.1), h2.trans (h3.2.trans h4.2)⟩

theorem maintain_pm (l r : AuthState ψ) : KeepsPair (maintainAuth l r) l r := by
  unfold maintainAuth KeepsPair; ncsplit

theorem completeWave_pm (l r : AuthState ψ) : KeepsPair (completeWaveAuth l r) l r := by
  unfold completeWaveAuth KeepsPair; ncsplit

theorem wave_pm (l r : AuthState ψ) : KeepsPair (waveAuth l r) l r := by
  unfold waveAuth KeepsPair; ncsplit

theorem landBackwardAuth_mono (u : AuthState ψ) : KeepsA u (landBackwardAuth u) := by
  unfold landBackwardAuth
  (repeat' (first | (dsimp only) | split))
  all_goals first
    | exact KeepsA.refl _
    | exact dropP2_mono _
    | exact landBackward_mono u.core

theorem landForwardAuth_mono (κ : Nat) (u : AuthState ψ) : KeepsA u (landForwardAuth κ u) := by
  unfold landForwardAuth
  (repeat' (first | (dsimp only) | split))
  all_goals first
    | exact KeepsA.refl _
    | exact dropP2_mono _
    | exact landForward_mono κ false true u.core

theorem cmpTail_pm (κ : Nat) (l r : AuthState ψ) : KeepsPair (cmpTail κ l r) l r := by
  unfold cmpTail
  have h1 := maintain_pm l r
  generalize maintainAuth l r = q1 at h1 ⊢
  obtain ⟨l1, r1⟩ := q1
  dsimp only
  have h2 := completeWave_pm l1 r1
  generalize completeWaveAuth l1 r1 = q2 at h2 ⊢
  obtain ⟨l2, r2⟩ := q2
  dsimp only
  have h3 := wave_pm l2 r2
  generalize waveAuth l2 r2 = q3 at h3 ⊢
  obtain ⟨l3, r3⟩ := q3
  dsimp only
  have h4 := lift2_pm PPLLFableDesignR1.dropStray dropStray_mono l3 r3
  generalize lift2 PPLLFableDesignR1.dropStray l3 r3 = q4 at h4 ⊢
  obtain ⟨l4, r4⟩ := q4
  exact ⟨h1.1.trans (h2.1.trans (h3.1.trans (h4.1.trans (landBackwardAuth_mono _)))),
    h1.2.trans (h2.2.trans (h3.2.trans (h4.2.trans (landForwardAuth_mono κ _))))⟩

theorem cmp0_mono (l : AuthState ψ) : KeepsA l (cmp0 l) := by
  unfold cmp0
  split
  · split
    · exact KeepsA.refl l
    · ncclose
  · exact KeepsA.refl l

theorem compare_pm (κ : Nat) (l r : AuthState ψ) : KeepsPair (compareLifecycleAuth κ l r) l r := by
  rw [compare_eq]
  have h := cmpTail_pm κ (cmp0 l) r
  exact ⟨(cmp0_mono l).trans h.1, h.2⟩


/-! Exact T2--T11 composition, after the established CLEAN cut. -/
open PPLLAuthGenDrain (Pair T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 restLo restHi restPair)

private def GoodPair (q : Pair ψ) : Prop := CoreGood q.1.core ∧ CoreGood q.2.core

private theorem KeepsPair.apply {q : Pair ψ} {l r : AuthState ψ}
    (h : KeepsPair q l r) (hl : CoreGood l.core) (hr : CoreGood r.core) : GoodPair q :=
  ⟨h.1 hl,h.2 hr⟩

private theorem clean_good (hp : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) : GoodPair (T1 hp c q) := by
  have h := PPLLAuthCheckCleanNoCmd.cleanSource_retained_noCmd hp c q.1 q.2
  constructor
  · by_cases hh : (T1 hp c q).1.core.path = .bot
    · exact Or.inl hh
    · exact Or.inr (h.1 hh)
  · by_cases hh : (T1 hp c q).2.core.path = .bot
    · exact Or.inl hh
    · exact Or.inr (h.2 hh)

private theorem restLo_keeps (hp : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) :
    KeepsPair (restLo hp c q) q.1 q.2 := by
  unfold restLo
  have h3 : KeepsPair (T3 hp q) q.1 q.2 :=
    lift2_pm (eliminateSig hp) (eliminate_mono hp) q.1 q.2
  generalize T3 hp q = a at h3 ⊢
  rcases a with ⟨a,b⟩
  have h4 : KeepsPair (T4 hp c (a,b)) a b := moveSource_pm hp c a b
  generalize T4 hp c (a,b) = d at h4 ⊢
  rcases d with ⟨d,e⟩
  have h5 : KeepsPair (T5 (d,e)) d e :=
    ⟨liftLife_mono dropStale dropStale_mono _,liftLife_mono dropStale dropStale_mono _⟩
  generalize T5 (d,e) = f at h5 ⊢
  rcases f with ⟨f,g⟩
  exact ((h3.trans h4).trans h5).trans (preCheck_pm f g)

private theorem restHi_keeps (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ) :
    KeepsPair (restHi hp κ c q) q.1 q.2 := by
  unfold restHi
  have h8 : KeepsPair (T8 hp c q) q.1 q.2 := checkSource_pm hp c q.1 q.2
  generalize T8 hp c q = a at h8 ⊢
  rcases a with ⟨a,b⟩
  have h9 : KeepsPair (T9 hp (a,b)) a b := disappear_pm hp a b
  generalize T9 hp (a,b) = d at h9 ⊢
  rcases d with ⟨d,e⟩
  have h10 : KeepsPair (T10 (d,e)) d e := repair_pm d e
  generalize T10 (d,e) = f at h10 ⊢
  rcases f with ⟨f,g⟩
  exact ((h8.trans h9).trans h10).trans (compare_pm κ f g)

private theorem rest_good (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ) :
    GoodPair (restPair hp κ c q) := by
  unfold restPair
  have h1 := clean_good hp c q
  generalize T1 hp c q = a at h1 ⊢
  rcases a with ⟨a,b⟩
  have h2 : GoodPair (T2 hp (a,b)) :=
    (lift2Life_pm (releaseSource hp) (releaseSource_mono hp) a b).apply h1.1 h1.2
  generalize T2 hp (a,b) = d at h2 ⊢
  rcases d with ⟨d,e⟩
  have h3 := (restLo_keeps hp c (d,e)).apply h2.1 h2.2
  generalize restLo hp c (d,e) = f at h3 ⊢
  rcases f with ⟨f,g⟩
  have h7 : GoodPair (T7 (f,g)) :=
    ⟨liftLife_mono normalizeReady normalizeReady_mono f h3.1,
      liftLife_mono normalizeReady normalizeReady_mono g h3.2⟩
  generalize T7 (f,g) = i at h7 ⊢
  rcases i with ⟨i,j⟩
  exact (restHi_keeps hp κ c (i,j)).apply h7.1 h7.2

private theorem start_keeps (l r : AgentState ψ) :
    Keeps l (suppressSigStart l r).1 ∧ Keeps r (suppressSigStart l r).2 := by
  unfold suppressSigStart; ncsplit
private theorem reset_keeps (l r : AgentState ψ) :
    Keeps l (suppressSigMoveReset l r).1 ∧ Keeps r (suppressSigMoveReset l r).2 := by
  unfold suppressSigMoveReset; ncsplit
private theorem terminal_keeps (hp : ψ > 0) (l r : AgentState ψ) :
    Keeps l (suppressSigTerminal hp l r).1 ∧ Keeps r (suppressSigTerminal hp l r).2 := by
  unfold suppressSigTerminal; ncsplit
private theorem echo_keeps (l r : AgentState ψ) :
    Keeps l (suppressSigEcho l r).1 ∧ Keeps r (suppressSigEcho l r).2 := by
  unfold suppressSigEcho; ncsplit
private theorem finish_keeps (l r : AgentState ψ) :
    Keeps l (suppressSigFinish l r).1 ∧ Keeps r (suppressSigFinish l r).2 := by
  unfold suppressSigFinish; ncsplit

private def kill (u : AuthState ψ) : AuthState ψ :=
  if u.core.reset_cmd then clearCmpAuth u else u
private theorem kill_keeps (u : AuthState ψ) : KeepsA u (kill u) := by
  unfold kill
  split
  · exact clearAuth_mono _
  · exact KeepsA.refl _

private theorem suppress_keeps (hp : ψ > 0) (l r : AuthState ψ) :
    KeepsPair (suppressSigResetKillAuth hp l r) l r := by
  change KeepsPair
    (let q0 := lift2 suppressSigStart l r
     let q0 := (kill q0.1,kill q0.2)
     let q1 := lift2 suppressSigMoveReset q0.1 q0.2
     let q1 := (kill q1.1,kill q1.2)
     let q2 := lift2 (suppressSigTerminal hp) q1.1 q1.2
     let q3 := lift2 suppressSigEcho q2.1 q2.2
     lift2 suppressSigFinish q3.1 q3.2) l r
  have h0 := lift2_pm suppressSigStart start_keeps l r
  generalize lift2 suppressSigStart l r = q0 at h0 ⊢
  rcases q0 with ⟨a,b⟩
  dsimp only
  have hk : KeepsPair (kill a,kill b) a b := ⟨kill_keeps _,kill_keeps _⟩
  have h1 := lift2_pm suppressSigMoveReset reset_keeps (kill a) (kill b)
  generalize lift2 suppressSigMoveReset (kill a) (kill b) = q1 at h1 ⊢
  rcases q1 with ⟨d,e⟩
  dsimp only
  have hk' : KeepsPair (kill d,kill e) d e := ⟨kill_keeps _,kill_keeps _⟩
  have h2 := lift2_pm (suppressSigTerminal hp) (terminal_keeps hp) (kill d) (kill e)
  generalize lift2 (suppressSigTerminal hp) (kill d) (kill e) = q2 at h2 ⊢
  rcases q2 with ⟨f,g⟩
  dsimp only
  have h3 := lift2_pm suppressSigEcho echo_keeps f g
  generalize lift2 suppressSigEcho f g = q3 at h3 ⊢
  rcases q3 with ⟨i,j⟩
  dsimp only
  exact ((((h0.trans hk).trans h1).trans hk').trans h2).trans
    (h3.trans (lift2_pm suppressSigFinish finish_keeps i j))

private theorem conserve_keeps (l r : AuthState ψ) (q : Pair ψ) :
    KeepsPair (conserveAuth l r q) q.1 q.2 := by
  unfold conserveAuth conserve KeepsPair
  ncsplit

private theorem write_keeps (hp : ψ > 0) (l r : AuthState ψ) :
    KeepsPair (lift2 (writeWithBundle hp) l r) l r := by
  have h := SlotFrame.write_frame hp l.core r.core
  exact ⟨Keeps.fields h.1.2.1 h.1.2.2.1 h.1.2.2.2,
    Keeps.fields h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩
private theorem kernel_keeps (hp : ψ > 0) (l r : AuthState ψ) :
    KeepsPair (lift2 (k4Kernel hp) l r) l r := by
  have h := SlotFrame.kernel_frame hp l.core r.core
  exact ⟨Keeps.fields h.1.2.1 h.1.2.2.1 h.1.2.2.2,
    Keeps.fields h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩

private theorem pipeline_eq (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) :
    PPLLAuthF.pipeline hp κ c l r =
      (let g := genSigAuth hp κ (PPLLAuthGenDrain.P0 hp l r).1
        (PPLLAuthGenDrain.P0 hp l r).2
       let q := restPair hp κ c g
       let q := suppressSigResetKillAuth hp q.1 q.2
       let q := lift2 (k4Kernel hp) q.1 q.2
       let q := lift2 (writeWithBundle hp) q.1 q.2
       conserveAuth l r q) := rfl

private theorem pipeline_good (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    GoodPair (PPLLAuthF.pipeline hp κ c l r) := by
  rw [pipeline_eq]
  generalize genSigAuth hp κ (PPLLAuthGenDrain.P0 hp l r).1
    (PPLLAuthGenDrain.P0 hp l r).2 = g
  dsimp only
  have hg := rest_good hp κ c g
  generalize restPair hp κ c g = a at hg ⊢
  rcases a with ⟨a,b⟩
  dsimp only
  have hs := (suppress_keeps hp a b).apply hg.1 hg.2
  generalize suppressSigResetKillAuth hp a b = s at hs ⊢
  rcases s with ⟨d,e⟩
  dsimp only
  have hk := (kernel_keeps hp d e).apply hs.1 hs.2
  generalize lift2 (k4Kernel hp) d e = k at hk ⊢
  rcases k with ⟨f,g⟩
  dsimp only
  have hw := (write_keeps hp f g).apply hk.1 hk.2
  generalize lift2 (writeWithBundle hp) f g = w at hw ⊢
  rcases w with ⟨i,j⟩
  exact (conserve_keeps l r (i,j)).apply hw.1 hw.2

/-- Every original AuthF row has the path-or-no-command property independently
at each output, for arbitrary raw inputs and every configuration. -/
theorem pipeline_pathNoCmd (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    PathNoCmd (PPLLAuthF.pipeline hp κ c l r).1 ∧
      PathNoCmd (PPLLAuthF.pipeline hp κ c l r).2 :=
  pipeline_good hp κ c l r

/-- Retaining an occupied main path excludes commands in both CLEAN slots.
No occupancy, token, provenance, leader, reset, or domain premise is required
on either input. This is a complete row statement, not an internal stopping cut. -/
theorem pipeline_retained_noCmd (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    let q := PPLLAuthF.pipeline hp κ c l r
    (q.1.core.path ≠ .bot → NoCmd q.1) ∧
      (q.2.core.path ≠ .bot → NoCmd q.2) := by
  have h := pipeline_pathNoCmd hp κ c l r
  exact ⟨fun hn => h.1.resolve_left hn,fun hn => h.2.resolve_left hn⟩

/- Source-level nonvacuity: the quantifiers permit psi=2 and any raw pair,
including occupied own paths with empty CLEAN slots. There is no entrance
predicate whose consistency must be assumed, and no bounded-record conclusion. -/

#print axioms pipeline_pathNoCmd
#print axioms pipeline_retained_noCmd

end PPLLAuthCheckNoCmdFrame
