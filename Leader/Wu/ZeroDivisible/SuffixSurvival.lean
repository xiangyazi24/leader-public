import Leader.Wu.ZeroDivisible.CheckRepair
import Leader.Wu.Safety.ConcreteProtocolProperties

/-!
# Actual R5 suffix survival interfaces

Literal cut factorizations connect post-CHECK and post-compare states to the
unchanged full R5 pipeline. A responder leader survives each remaining suffix
as a leader somewhere in the completed pair: K4 preserves that responder,
and WRITE either retains it or moves leadership to the initiator.

After comparison, suppression and conservation may clear comparison data;
each endpoint's token is otherwise unchanged. Such a clear also deletes that
same endpoint's main path. The token-or-hole interface therefore covers every
raw path2 value and arbitrary leaders/reset/writer fields, with no action or
cleanliness assumptions. These are local suffix facts, not token provenance
or a global liveness theorem.
-/

namespace PPLLAstraR5Repair


namespace SuffixInterfaces


open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3


set_option autoImplicit false
set_option linter.unusedSimpArgs false


/-- Exact R5 prefix ending immediately after guarded CHECK. -/
def throughCheck {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := pPsiProbeWall hψ l r
  let q := PPLLFableZDiv.genSigOverwrite hψ κ true 0 q.1 q.2
  let q := cleanSource hψ q.1 q.2
  let q := releaseSource hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  let q := PPLLFableZDiv.moveSourceF hψ sourceCfg q.1 q.2
  let q := (dropStale q.1, dropStale q.2)
  let q := preCheckReset q.1 q.2
  let q := (normalizeReady q.1, normalizeReady q.2)
  checkSource hψ c q.1 q.2


/-- DISAPPEAR, readyAck repair, and comparison in their actual order. -/
def afterCheckToCompare {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := disappear hψ l r
  let q := repair .readyAck q.1 q.2
  compareLifecycle κ q.1 q.2


/-- Exact R5 prefix ending immediately after compareLifecycle. -/
def throughCompare {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := throughCheck hψ κ c l r
  afterCheckToCompare hψ κ q.1 q.2


/-- Remaining suppression, K4, and WRITE stages before conservation. -/
def beforeConserveAfterCompare {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := suppressSigResetKill hψ l r
  let q := k4Kernel hψ q.1 q.2
  writeWithBundle hψ q.1 q.2


/-- Full suffix from the comparison cut, with the original inputs retained for conservation. -/
def finishAfterCompare {ψ : Nat} (hψ : ψ > 0)
    (origL origR l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  conserve .head origL origR (beforeConserveAfterCompare hψ l r)


/-- Full suffix from the CHECK cut, retaining original conservation inputs. -/
def finishAfterCheck {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (origL origR l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := afterCheckToCompare hψ κ l r
  finishAfterCompare hψ origL origR q.1 q.2


/-- Definitional factorization of the actual full row at the CHECK cut. -/
theorem pipeline_eq_from_check {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (c : Cfg) (l r : AgentState ψ) :
    pipeline hψ κ c l r =
      finishAfterCheck hψ κ l r
        (throughCheck hψ κ c l r).1
        (throughCheck hψ κ c l r).2 := by
  rfl


/-- Definitional factorization of the actual full row at the comparison cut. -/
theorem pipeline_eq_from_compare {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (c : Cfg) (l r : AgentState ψ) :
    pipeline hψ κ c l r =
      finishAfterCompare hψ l r
        (throughCompare hψ κ c l r).1
        (throughCompare hψ κ c l r).2 := by
  rfl


/-- The pre-K4 prefix ends with suppression immediately after comparison. -/
theorem beforeElimination_eq_from_compare {ψ : Nat}
    (hψ : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ) :
    beforeElimination hψ κ c l r =
      suppressSigResetKill hψ
        (throughCompare hψ κ c l r).1
        (throughCompare hψ κ c l r).2 := by
  rfl


private theorem fst_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).1 = if p then a.1 else b.1 := by
  split <;> rfl


private theorem snd_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ × AgentState ψ) :
    (if p then a else b).2 = if p then a.2 else b.2 := by
  split <;> rfl


private theorem leader_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).leader =
      if p then a.leader else b.leader := by
  split <;> rfl


private theorem label_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).label =
      if p then a.label else b.label := by
  split <;> rfl


private theorem path_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).path =
      if p then a.path else b.path := by
  split <;> rfl


private theorem path2_ite {ψ : Nat} (p : Prop) [Decidable p]
    (a b : AgentState ψ) :
    (if p then a else b).path2 =
      if p then a.path2 else b.path2 := by
  split <;> rfl


private theorem normalizeOrphan_leader {ψ : Nat} (u : AgentState ψ) :
    (normalizeOrphan u).leader = u.leader := by
  cases hl : u.leader <;> cases hp : u.path <;>
    simp [normalizeOrphan, hl, hp, leader_ite]


private theorem normalizeCarrier_leader {ψ : Nat} (u : AgentState ψ) :
    (normalizeCarrier u).leader = u.leader := by
  cases hl : u.leader <;> cases hp : u.path <;>
    simp [normalizeCarrier, releaseCongest, hl, hp, leader_ite]


private theorem releaseReadySuffix_leaders {ψ : Nat}
    (l r : AgentState ψ) :
    (releaseReadySuffix l r).1.leader = l.leader ∧
    (releaseReadySuffix l r).2.leader = r.leader := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [releaseReadySuffix, hl, hr, fst_ite, snd_ite, leader_ite]


private theorem ackTail_leaders {ψ : Nat} (l r : AgentState ψ) :
    (ackTail l r).1.leader = l.leader ∧
    (ackTail l r).2.leader = r.leader := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [ackTail, hl, hr, fst_ite, snd_ite, leader_ite]


private theorem repairReady_leaders {ψ : Nat}
    (l r : AgentState ψ) :
    (repair .readyAck l r).1.leader = l.leader ∧
    (repair .readyAck l r).2.leader = r.leader := by
  simp only [repair,
    normalizeOrphan_leader, normalizeCarrier_leader,
    (releaseReadySuffix_leaders _ _).1,
    (releaseReadySuffix_leaders _ _).2,
    (ackTail_leaders _ _).1,
    (ackTail_leaders _ _).2,
    and_self]


private theorem maintain_right_leader {ψ : Nat}
    (l r : AgentState ψ) :
    (maintain l r).2.leader = r.leader := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [maintain, hl, hr, leader_ite]


private theorem completeWave_right_leader {ψ : Nat}
    (l r : AgentState ψ) :
    (completeWave l r).2.leader = r.leader := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [completeWave, hl, hr, leader_ite]


private theorem wave_right_leader {ψ : Nat}
    (l r : AgentState ψ) :
    (wave l r).2.leader = r.leader := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [wave, hl, hr, leader_ite]


private theorem dropStray_right_leader {ψ : Nat}
    (l r : AgentState ψ) :
    (dropStray l r).2.leader = r.leader := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [dropStray, hl, hr, leader_ite]


private theorem landForward_true {ψ : Nat} (κ : Nat)
    (u : AgentState ψ) (hu : u.leader = true) :
    (landForward κ false true u).leader = true := by
  cases hp : u.path <;> cases ht : u.path2 <;>
    simp [landForward, hp, ht, leader_ite, hu]


private theorem compareLifecycle_right_true {ψ : Nat} (κ : Nat)
    (l r : AgentState ψ) (hr : r.leader = true) :
    (compareLifecycle κ l r).2.leader = true := by
  simp only [compareLifecycle]
  apply landForward_true
  simp only [
    dropStray_right_leader,
    wave_right_leader,
    completeWave_right_leader,
    maintain_right_leader]
  exact hr


private theorem suppress_right_leader_eq {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    (suppressSigResetKill hψ l r).2.leader = r.leader := by
  cases h1 : l.leader <;> cases h2 : l.reset_cmd <;>
    cases h3 : r.reset_cmd <;> cases h4 : r.echo <;>
    simp_all [suppressSigResetKill, suppressSigStart,
      suppressSigMoveReset, suppressSigTerminal,
      suppressSigEcho, suppressSigFinish, clearCmp,
      fst_ite, snd_ite, leader_ite]


private theorem k4_right_leader_label_frame {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    (k4Kernel hψ l r).2.leader = r.leader ∧
    (k4Kernel hψ l r).2.label = r.label := by
  simp only [k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire,
    absorbAnyMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp only [fst_ite, snd_ite, leader_ite, label_ite,
    ite_self, and_self]


private theorem writeWithBundle_nonempty_of_right_leader
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ)
    (hr : r.leader = true) :
    (writeWithBundle hψ l r).1.leader = true ∨
    (writeWithBundle hψ l r).2.leader = true := by
  by_cases hl : l.leader = true
  · left
    have hw :=
      PPLLVerify.writeSeq_initiator_leader_of_true hψ l r hl
    simp only [writeWithBundle, fst_ite, leader_ite, hw, ite_self]
  · by_cases hz : r.label = ⟨0, hψ⟩
    · right
      have hw :=
        PPLLVerify.writeSeq_responder_leader_of_label_zero
          hψ l r hr hz
      simp only [writeWithBundle, snd_ite, leader_ite, hw, ite_self]
    · left
      have hw :=
        PPLLVerify.writeSeq_initiator_true_of_nonzero_responder_leader
          hψ l r ⟨hr, hz⟩
      simp only [writeWithBundle, fst_ite, leader_ite, hw, ite_self]


private theorem conserve_nonempty_of_computed_nonempty
    {ψ : Nat} (origL origR : AgentState ψ)
    (q : AgentState ψ × AgentState ψ)
    (h : q.1.leader = true ∨ q.2.leader = true) :
    (conserve .head origL origR q).1.leader = true ∨
    (conserve .head origL origR q).2.leader = true := by
  rcases h with h | h
  · simp [conserve, h]
  · simp [conserve, h]


private theorem finishAfterCompare_nonempty_of_right_leader
    {ψ : Nat} (hψ : ψ > 0)
    (origL origR l r : AgentState ψ)
    (hr : r.leader = true) :
    (finishAfterCompare hψ origL origR l r).1.leader = true ∨
    (finishAfterCompare hψ origL origR l r).2.leader = true := by
  let s := suppressSigResetKill hψ l r
  have hs : s.2.leader = true := by
    exact (suppress_right_leader_eq hψ l r).trans hr
  let k := k4Kernel hψ s.1 s.2
  have hkf := k4_right_leader_label_frame hψ s.1 s.2
  have hk : k.2.leader = true := by
    exact hkf.1.trans hs
  let w := writeWithBundle hψ k.1 k.2
  have hw :
      w.1.leader = true ∨ w.2.leader = true := by
    exact writeWithBundle_nonempty_of_right_leader hψ k.1 k.2 hk
  have hc :=
    conserve_nonempty_of_computed_nonempty origL origR w hw
  simpa [finishAfterCompare, beforeConserveAfterCompare, s, k, w]
    using hc


private theorem finishAfterCheck_nonempty_of_right_leader
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (origL origR l r : AgentState ψ)
    (hr : r.leader = true) :
    (finishAfterCheck hψ κ origL origR l r).1.leader = true ∨
    (finishAfterCheck hψ κ origL origR l r).2.leader = true := by
  let d := disappear hψ l r
  have hd : d.2.leader = true := by
    exact (PPLLVerify.disappear_leaders_eq hψ l r).2.trans hr
  let a := repair .readyAck d.1 d.2
  have ha : a.2.leader = true := by
    exact (repairReady_leaders d.1 d.2).2.trans hd
  let q := compareLifecycle κ a.1 a.2
  have hq : q.2.leader = true := by
    exact compareLifecycle_right_true κ a.1 a.2 ha
  have hf :=
    finishAfterCompare_nonempty_of_right_leader
      hψ origL origR q.1 q.2 hq
  simpa [finishAfterCheck, afterCheckToCompare, d, a, q] using hf


/-- A responder leader at CHECK survives the actual full row, regardless of original leaders. -/
theorem pipeline_nonempty_of_check_cut_right_leader
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ)
    (hbirth : (throughCheck hψ κ c l r).2.leader = true) :
    (pipeline hψ κ c l r).1.leader = true ∨
    (pipeline hψ κ c l r).2.leader = true := by
  rw [pipeline_eq_from_check]
  exact finishAfterCheck_nonempty_of_right_leader
    hψ κ l r
    (throughCheck hψ κ c l r).1
    (throughCheck hψ κ c l r).2
    hbirth


/-- A responder leader at comparison survives the actual full row, at any physical label. -/
theorem pipeline_nonempty_of_compare_cut_right_leader
    {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ)
    (hbirth : (throughCompare hψ κ c l r).2.leader = true) :
    (pipeline hψ κ c l r).1.leader = true ∨
    (pipeline hψ κ c l r).2.leader = true := by
  rw [pipeline_eq_from_compare]
  exact finishAfterCompare_nonempty_of_right_leader
    hψ l r
    (throughCompare hψ κ c l r).1
    (throughCompare hψ κ c l r).2
    hbirth


/-- K4 and WRITE preserve both main path and comparison token holderwise. -/
private def TailFrame {ψ : Nat}
    (after before : AgentState ψ) : Prop :=
  after.path = before.path ∧ after.path2 = before.path2


/-- A suffix can erase a token only while leaving the same endpoint pathless. -/
private def TailMono {ψ : Nat}
    (before after : AgentState ψ) : Prop :=
  (after.path = before.path ∨ after.path = .bot) ∧
  (after.path2 = before.path2 ∨ after.path = .bot)


private def PairTailMono {ψ : Nat}
    (l r l' r' : AgentState ψ) : Prop :=
  TailMono l l' ∧ TailMono r r'


private theorem tailMono_refl {ψ : Nat} (u : AgentState ψ) :
    TailMono u u := by
  simp [TailMono]


private theorem tailMono_of_frame {ψ : Nat}
    {a b : AgentState ψ} (h : TailFrame b a) :
    TailMono a b := by
  exact ⟨Or.inl h.1, Or.inl h.2⟩


private theorem tailMono_trans {ψ : Nat}
    {a b c : AgentState ψ}
    (hab : TailMono a b) (hbc : TailMono b c) :
    TailMono a c := by
  constructor
  · rcases hbc.1 with hcb | hc
    · rcases hab.1 with hba | hb
      · exact Or.inl (hcb.trans hba)
      · exact Or.inr (hcb.trans hb)
    · exact Or.inr hc
  · rcases hbc.2 with hcb | hc
    · rcases hab.2 with hba | hb
      · exact Or.inl (hcb.trans hba)
      · rcases hbc.1 with hp | hp
        · exact Or.inr (hp.trans hb)
        · exact Or.inr hp
    · exact Or.inr hc


private theorem pairTailMono_refl {ψ : Nat}
    (l r : AgentState ψ) :
    PairTailMono l r l r :=
  ⟨tailMono_refl l, tailMono_refl r⟩


private theorem pairTailMono_trans {ψ : Nat}
    {l r a b c d : AgentState ψ}
    (h1 : PairTailMono l r a b)
    (h2 : PairTailMono a b c d) :
    PairTailMono l r c d :=
  ⟨tailMono_trans h1.1 h2.1, tailMono_trans h1.2 h2.2⟩


private theorem suppress_tail_mono {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    PairTailMono l r
      (suppressSigResetKill hψ l r).1
      (suppressSigResetKill hψ l r).2 := by
  cases h1 : l.leader <;> cases h2 : l.reset_cmd <;>
    cases h3 : r.reset_cmd <;> cases h4 : r.echo <;>
    simp_all [PairTailMono, TailMono,
      suppressSigResetKill, suppressSigStart,
      suppressSigMoveReset, suppressSigTerminal,
      suppressSigEcho, suppressSigFinish,
      clearCmp, fst_ite, snd_ite, path_ite, path2_ite]


private theorem k4_tail_frame {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    TailFrame (k4Kernel hψ l r).1 l ∧
    TailFrame (k4Kernel hψ l r).2 r := by
  simp only [TailFrame, k4Kernel, k3Kernel,
    eliminateLeadersNoCollisionFire, absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp only [fst_ite, snd_ite, path_ite, path2_ite,
    ite_self, and_self]


namespace Writer


private theorem writeActionApplyOverwrite_frame {ψ : Nat}
    (u : AgentState ψ) :
    TailFrame (writeActionApplyOverwrite u) u := by
  unfold TailFrame writeActionApplyOverwrite
  repeat (first | constructor | rfl | split)
  all_goals simp [path_ite, path2_ite]


private theorem writeActionApplyMoveFlip_frame {ψ : Nat}
    (u : AgentState ψ) :
    TailFrame (writeActionApplyMoveFlip u) u := by
  unfold TailFrame writeActionApplyMoveFlip
  repeat (first | constructor | rfl | split)
  all_goals simp [path_ite, path2_ite]


private theorem moveWsigCheckLast_frame {ψ : Nat}
    (u : AgentState ψ) :
    TailFrame (moveWsigCheckLast u) u := by
  unfold TailFrame moveWsigCheckLast
  repeat (first | constructor | rfl | split)
  all_goals simp [path_ite, path2_ite]


private theorem writeSeqSetWriteReady_frame {ψ : Nat}
    (u : AgentState ψ) :
    TailFrame (writeSeqSetWriteReady u) u := by
  unfold TailFrame writeSeqSetWriteReady
  repeat (first | constructor | rfl | split)
  all_goals simp [path_ite, path2_ite]


private theorem writeSeqCheckBit_frame {ψ : Nat}
    (u : AgentState ψ) :
    TailFrame (writeSeqCheckBit u) u := by
  unfold TailFrame writeSeqCheckBit
  repeat (first | constructor | rfl | split)
  all_goals simp [path_ite, path2_ite]


private theorem writeSeqSetWriteAct_frame {ψ : Nat}
    (u : AgentState ψ) :
    TailFrame (writeSeqSetWriteAct u) u := by
  cases hp : u.path3 <;>
    simp only [TailFrame, writeSeqSetWriteAct, hp] <;>
    simp [path_ite, path2_ite, hp]


private theorem writeSeqFinalR_frame {ψ : Nat}
    (u : AgentState ψ) :
    TailFrame (writeSeqFinalR u) u := by
  unfold TailFrame writeSeqFinalR
  repeat (first | constructor | rfl | split)
  all_goals simp [path_ite, path2_ite]


private theorem moveWsigCheckGenWs_frame {ψ : Nat}
    (l r : AgentState ψ) :
    TailFrame (moveWsigCheckGenWs l r) r := by
  unfold TailFrame moveWsigCheckGenWs
  repeat (first | constructor | rfl | split)
  all_goals simp [path_ite, path2_ite]


private theorem moveWsigTransfer_frame {ψ : Nat}
    (l r : AgentState ψ) :
    TailFrame (moveWsigTransfer l r).1 l ∧
    TailFrame (moveWsigTransfer l r).2 r := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp only [TailFrame, moveWsigTransfer, hl, hr] <;>
    simp only [fst_ite, snd_ite, path_ite, path2_ite,
      ite_self, and_self]


private theorem groupInfo_frame {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    TailFrame (groupInfo hψ l r).1 l ∧
    TailFrame (groupInfo hψ l r).2 r := by
  simp only [TailFrame, groupInfo, fst_ite, snd_ite,
    path_ite, path2_ite, ite_self, and_self]


private theorem gensigWriteseq_frame {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    TailFrame (gensigWriteseq hψ l r).1 l ∧
    TailFrame (gensigWriteseq hψ l r).2 r := by
  simp only [TailFrame, gensigWriteseq, fst_ite, snd_ite,
    path_ite, path2_ite, ite_self, and_self]


private theorem writeAction_frame {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    TailFrame (writeAction hψ l r).1 l ∧
    TailFrame (writeAction hψ l r).2 r := by
  simp only [TailFrame, writeAction, fst_ite, snd_ite,
    path_ite, path2_ite, ite_self, and_self,
    (writeActionApplyOverwrite_frame _).1,
    (writeActionApplyOverwrite_frame _).2,
    (writeActionApplyMoveFlip_frame _).1,
    (writeActionApplyMoveFlip_frame _).2]


private theorem moveWsig_frame {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    TailFrame (moveWsig hψ l r).1 l ∧
    TailFrame (moveWsig hψ l r).2 r := by
  simp only [TailFrame, moveWsig, fst_ite, snd_ite,
    path_ite, path2_ite, ite_self, and_self,
    (moveWsigCheckGenWs_frame _ _).1,
    (moveWsigCheckGenWs_frame _ _).2,
    (moveWsigCheckLast_frame _).1,
    (moveWsigCheckLast_frame _).2,
    (moveWsigTransfer_frame _ _).1.1,
    (moveWsigTransfer_frame _ _).1.2,
    (moveWsigTransfer_frame _ _).2.1,
    (moveWsigTransfer_frame _ _).2.2]


private theorem writeSeq_frame {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    TailFrame (writeSeq hψ l r).1 l ∧
    TailFrame (writeSeq hψ l r).2 r := by
  simp only [TailFrame, writeSeq, writeSeqThroughPrepare,
    writeSeqAfterPrepare, writeSeqLeaderMove, writeSeqGenerate,
    writeSeqPrepare, writeSeqReady, writeSeqCompare,
    writeSeqCommands,
    fst_ite, snd_ite, path_ite, path2_ite, ite_self, and_self,
    (groupInfo_frame _ _ _).1.1,
    (groupInfo_frame _ _ _).1.2,
    (groupInfo_frame _ _ _).2.1,
    (groupInfo_frame _ _ _).2.2,
    (gensigWriteseq_frame _ _ _).1.1,
    (gensigWriteseq_frame _ _ _).1.2,
    (gensigWriteseq_frame _ _ _).2.1,
    (gensigWriteseq_frame _ _ _).2.2,
    (writeAction_frame _ _ _).1.1,
    (writeAction_frame _ _ _).1.2,
    (writeAction_frame _ _ _).2.1,
    (writeAction_frame _ _ _).2.2,
    (moveWsig_frame _ _ _).1.1,
    (moveWsig_frame _ _ _).1.2,
    (moveWsig_frame _ _ _).2.1,
    (moveWsig_frame _ _ _).2.2,
    (writeSeqSetWriteReady_frame _).1,
    (writeSeqSetWriteReady_frame _).2,
    (writeSeqCheckBit_frame _).1,
    (writeSeqCheckBit_frame _).2,
    (writeSeqSetWriteAct_frame _).1,
    (writeSeqSetWriteAct_frame _).2,
    (writeSeqFinalR_frame _).1,
    (writeSeqFinalR_frame _).2]


private theorem writeWithBundle_frame {ψ : Nat}
    (hψ : ψ > 0) (l r : AgentState ψ) :
    TailFrame (writeWithBundle hψ l r).1 l ∧
    TailFrame (writeWithBundle hψ l r).2 r := by
  have h := writeSeq_frame hψ l r
  simp only [TailFrame, writeWithBundle, fst_ite, snd_ite,
    path_ite, path2_ite,
    h.1.1, h.1.2, h.2.1, h.2.2,
    ite_self, and_self]


end Writer


private theorem conserve_tail_mono {ψ : Nat}
    (origL origR : AgentState ψ)
    (q : AgentState ψ × AgentState ψ) :
    PairTailMono q.1 q.2
      (conserve .head origL origR q).1
      (conserve .head origL origR q).2 := by
  unfold conserve
  split
  · simp [PairTailMono, TailMono, replacement, clearCmp]
  · exact pairTailMono_refl q.1 q.2


private theorem finishAfterCompare_tail_mono {ψ : Nat}
    (hψ : ψ > 0)
    (origL origR l r : AgentState ψ) :
    PairTailMono l r
      (finishAfterCompare hψ origL origR l r).1
      (finishAfterCompare hψ origL origR l r).2 := by
  let s := suppressSigResetKill hψ l r
  have hs :
      PairTailMono l r s.1 s.2 :=
    suppress_tail_mono hψ l r


  let k := k4Kernel hψ s.1 s.2
  have hkf := k4_tail_frame hψ s.1 s.2
  have hk :
      PairTailMono s.1 s.2 k.1 k.2 :=
    ⟨tailMono_of_frame hkf.1, tailMono_of_frame hkf.2⟩


  let w := writeWithBundle hψ k.1 k.2
  have hwf := Writer.writeWithBundle_frame hψ k.1 k.2
  have hw :
      PairTailMono k.1 k.2 w.1 w.2 :=
    ⟨tailMono_of_frame hwf.1, tailMono_of_frame hwf.2⟩


  have hc :
      PairTailMono w.1 w.2
        (conserve .head origL origR w).1
        (conserve .head origL origR w).2 :=
    conserve_tail_mono origL origR w


  have h :=
    pairTailMono_trans hs
      (pairTailMono_trans hk
        (pairTailMono_trans hw hc))


  simpa [finishAfterCompare, beforeConserveAfterCompare, s, k, w]
    using h


private theorem finishAfterCompare_path2_or_hole {ψ : Nat}
    (hψ : ψ > 0)
    (origL origR l r : AgentState ψ) :
    ((finishAfterCompare hψ origL origR l r).1.path2 = l.path2 ∨
      (finishAfterCompare hψ origL origR l r).1.path = .bot) ∧
    ((finishAfterCompare hψ origL origR l r).2.path2 = r.path2 ∨
      (finishAfterCompare hψ origL origR l r).2.path = .bot) := by
  have h := finishAfterCompare_tail_mono hψ origL origR l r
  exact ⟨h.1.2, h.2.2⟩


private theorem finishAfterCompare_path2_eq_of_no_hole {ψ : Nat}
    (hψ : ψ > 0)
    (origL origR l r : AgentState ψ)
    (hl : (finishAfterCompare hψ origL origR l r).1.path ≠ .bot)
    (hr : (finishAfterCompare hψ origL origR l r).2.path ≠ .bot) :
    (finishAfterCompare hψ origL origR l r).1.path2 = l.path2 ∧
    (finishAfterCompare hψ origL origR l r).2.path2 = r.path2 := by
  have h := finishAfterCompare_path2_or_hole hψ origL origR l r
  constructor
  · rcases h.1 with h | h
    · exact h
    · exact False.elim (hl h)
  · rcases h.2 with h | h
    · exact h
    · exact False.elim (hr h)


/-- Every post-comparison token survives exactly unless its own endpoint finishes pathless. -/
theorem pipeline_compare_cut_path2_or_hole {ψ : Nat}
    (hψ : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ) :
    ((pipeline hψ κ c l r).1.path2 =
        (throughCompare hψ κ c l r).1.path2 ∨
      (pipeline hψ κ c l r).1.path = .bot) ∧
    ((pipeline hψ κ c l r).2.path2 =
        (throughCompare hψ κ c l r).2.path2 ∨
      (pipeline hψ κ c l r).2.path = .bot) := by
  rw [pipeline_eq_from_compare]
  exact finishAfterCompare_path2_or_hole
    hψ l r
    (throughCompare hψ κ c l r).1
    (throughCompare hψ κ c l r).2


/-- With no output hole, both completed tokens equal their post-comparison values exactly. -/
theorem pipeline_compare_cut_path2_eq_of_no_hole {ψ : Nat}
    (hψ : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ)
    (hl : (pipeline hψ κ c l r).1.path ≠ .bot)
    (hr : (pipeline hψ κ c l r).2.path ≠ .bot) :
    (pipeline hψ κ c l r).1.path2 =
        (throughCompare hψ κ c l r).1.path2 ∧
    (pipeline hψ κ c l r).2.path2 =
        (throughCompare hψ κ c l r).2.path2 := by
  have h := pipeline_compare_cut_path2_or_hole hψ κ c l r
  constructor
  · rcases h.1 with h | h
    · exact h
    · exact False.elim (hl h)
  · rcases h.2 with h | h
    · exact h
    · exact False.elim (hr h)


#print axioms pipeline_nonempty_of_check_cut_right_leader
#print axioms pipeline_nonempty_of_compare_cut_right_leader
#print axioms pipeline_compare_cut_path2_or_hole
#print axioms pipeline_compare_cut_path2_eq_of_no_hole

end SuffixInterfaces
end PPLLAstraR5Repair
