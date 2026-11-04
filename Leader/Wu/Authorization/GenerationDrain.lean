import Leader.Wu.Authorization.ResetDrain
import Leader.Wu.Authorization.WriterFrame

/-!
# GEN-DRAIN for AuthF

From a leaderless, reset-free AuthF configuration with perfect labels
(`label(i) = i mod ψ`, `ψ ≥ 2`; `echo` arbitrary) in which block `g` has a cell
in `produce` or `done`, some word of at most `ψ² - 2` interactions on the edges
of block `g` reaches a leader, GenEntrance for block `g`, or a
configuration with strictly smaller `Ngen` (the number of cells in `produce` or
`done`). The statements hold for every `PPLLAuthF.Cfg`, in particular
`authFplusmcc`.

* `genDrain_block`: the block form (hypothesis `Ngen_g > 0`);
* `genDrain_global`: with `ψ ∣ n` and `Ngen > 0`, a block with `Ngen_g > 0`
  and the same conclusion.

The word is `W_B = F ++ R^(ψ-2)` (`F` = edges `0..ψ-2`, `R` = edges
`ψ-3..0`), which removes every `done` cell and every occupied producer, then
the cleanup from the leftmost producer (at most `2ψ-3` edges). Total
`(ψ-1) + (ψ-2)² + (2ψ-3) = ψ² - ψ`.

Differences from the original sketch: `W_B` needs `ψ-2` sweeps of `R` (not `(F ++ R)`
repeated, whose length count does not match); after `W_B` no block cell
is `done`, so the `D_g(j)` case of the cleanup does not arise; the leftmost
producer at `ψ-2` is handled by the terminal edge followed by the release C4.

Architecture: Parts A–C frame the AuthF stages around GENSIG (the suffix after
GENSIG changes no generation field, `MonoC`); Part D decomposes the stages after
GENSIG (`restPair`); Part E proves the GENSIG row cases; Part F the stage
lemmas after GENSIG; Part G the row lemmas F1–F3 and C1–C4; Part H the
standing invariants; Parts I–L the configuration level and the headlines.
-/

set_option autoImplicit false

namespace PPLLAuthGenDrain

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF

/-! ## Part A. Field lemmas and the frame of the suffix stages -/

section Basics
variable {ψ : Nat}

theorem gfst_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
theorem gsnd_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
theorem gstate_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).state = if p then a.state else b.state := by split <;> rfl
theorem gpath_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by split <;> rfl
theorem gpath2_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path2 = if p then a.path2 else b.path2 := by split <;> rfl
theorem gwait_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).wait = if p then a.wait else b.wait := by split <;> rfl

end Basics

/-! ### The writer and K4 keep state, path, path2 and wait

`WF a b` says that `a` and `b` agree on the four core fields the generation
argument reads after the comparison prefix. The proofs follow the
`PPLLAstraReadyResetDebtR.Writer` frame template field by field. -/

namespace WFrame

def WF {ψ : Nat} (a b : AgentState ψ) : Prop :=
  a.state = b.state ∧ a.path = b.path ∧ a.path2 = b.path2 ∧ a.wait = b.wait

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
    simp [gstate_ite, gpath_ite, gpath2_ite, gwait_ite, hp]

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
    simp only [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, gpath2_ite, gwait_ite, ite_self, and_self]

private theorem groupInfo_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WF (groupInfo hψ l r).1 l ∧ WF (groupInfo hψ l r).2 r := by
  simp only [WF, groupInfo]
  simp only [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, gpath2_ite, gwait_ite, ite_self, and_self]

private theorem gensigWriteseq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WF (gensigWriteseq hψ l r).1 l ∧ WF (gensigWriteseq hψ l r).2 r := by
  simp only [WF, gensigWriteseq]
  simp only [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, gpath2_ite, gwait_ite, ite_self, and_self]

private theorem writeAction_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WF (writeAction hψ l r).1 l ∧ WF (writeAction hψ l r).2 r := by
  simp only [WF, writeAction]
  simp only [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, gpath2_ite, gwait_ite, ite_self, and_self,
    (writeActionApplyOverwrite_frame _).1, (writeActionApplyOverwrite_frame _).2.1,
    (writeActionApplyOverwrite_frame _).2.2.1, (writeActionApplyOverwrite_frame _).2.2.2,
    (writeActionApplyMoveFlip_frame _).1, (writeActionApplyMoveFlip_frame _).2.1,
    (writeActionApplyMoveFlip_frame _).2.2.1, (writeActionApplyMoveFlip_frame _).2.2.2]

private theorem moveWsig_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WF (moveWsig hψ l r).1 l ∧ WF (moveWsig hψ l r).2 r := by
  simp only [WF, moveWsig]
  simp only [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, gpath2_ite, gwait_ite, ite_self, and_self,
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
  simp only [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, gpath2_ite, gwait_ite, ite_self, and_self,
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
  simp only [writeWithBundle, gfst_ite, gsnd_ite, gstate_ite, gpath_ite, gpath2_ite, gwait_ite,
    h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, ite_self,
    and_self]

theorem kernel_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WF (k4Kernel hψ l r).1 l ∧ WF (k4Kernel hψ l r).2 r := by
  simp only [WF, k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire, absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, gpath2_ite, gwait_ite]

end WFrame

/-! ## Part B. No stage after GENSIG creates a generation state

`MonoC a b` says that the cell `b` could have come from the cell `a` without a
generation birth: if `b` is in `produce` (resp. `done`) then so was `a`, and an
occupied `produce` in `b` was already occupied in `a`. It is a preorder. Every
AuthF stage after `genSigAuth` satisfies it on both endpoints, because the only
writers of `MainState.produce`/`MainState.done` are in GENSIG and the only
writer of a path onto an empty cell (`step1Auth`) also writes `state := none`. -/

section Mono
variable {ψ : Nat}

def MonoC (a b : AgentState ψ) : Prop :=
  (b.state = .produce → a.state = .produce) ∧ (b.state = .done → a.state = .done) ∧
  (b.state = .produce → b.path ≠ .bot → a.path ≠ .bot)

def MonoA (a b : AuthState ψ) : Prop := MonoC a.core b.core

theorem MonoC.refl (a : AgentState ψ) : MonoC a a := ⟨id, id, fun _ h => h⟩

theorem MonoC.trans {a b c : AgentState ψ} (h1 : MonoC a b) (h2 : MonoC b c) : MonoC a c :=
  ⟨fun h => h1.1 (h2.1 h), fun h => h1.2.1 (h2.2.1 h),
   fun h hp => h1.2.2 (h2.1 h) (h2.2.2 h hp)⟩

theorem MonoA.refl (a : AuthState ψ) : MonoA a a := MonoC.refl _

theorem MonoA.trans {a b c : AuthState ψ} (h1 : MonoA a b) (h2 : MonoA b c) : MonoA a c :=
  MonoC.trans h1 h2

/-- Same state and path. -/
theorem MonoC.of_eq {a b : AgentState ψ} (h1 : b.state = a.state) (h2 : b.path = a.path) :
    MonoC a b := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; rw [← h1]; exact h
  · intro h; rw [← h1]; exact h
  · intro _ hp; rw [← h2]; exact hp

/-- A non-generation state. -/
theorem MonoC.of_ne {a b : AgentState ψ} (h1 : b.state ≠ .produce) (h2 : b.state ≠ .done) :
    MonoC a b :=
  ⟨fun h => absurd h h1, fun h => absurd h h2, fun h => absurd h h1⟩

/-- Same state, path deleted or kept. -/
theorem MonoC.of_state {a b : AgentState ψ} (h1 : b.state = a.state)
    (h2 : b.path = a.path ∨ b.path = .bot) : MonoC a b := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; rw [← h1]; exact h
  · intro h; rw [← h1]; exact h
  · intro _ hp
    rcases h2 with h2 | h2
    · rw [← h2]; exact hp
    · exact absurd h2 hp

theorem checkBit_ne_produce (b : Bool) (s : Nat) : checkBit b s ≠ .produce := by
  unfold checkBit
  (repeat' (first | (dsimp only) | split)) <;> simp

theorem checkBit_ne_done (b : Bool) (s : Nat) : checkBit b s ≠ .done := by
  unfold checkBit
  (repeat' (first | (dsimp only) | split)) <;> simp

/-- Close a `MonoC` leaf that is a record update of the input cell. -/
syntax "mclose" : tactic
macro_rules
  | `(tactic| mclose) => `(tactic| first
      | exact MonoC.refl _
      | exact MonoA.refl _
      | (apply MonoC.of_eq <;> rfl)
      | (apply MonoC.of_ne <;> (simp [checkBit_ne_produce, checkBit_ne_done]; done))
      | (apply MonoC.of_state <;> first | rfl | exact Or.inl rfl | exact Or.inr rfl)
      | (simp only [MonoA, AuthState.withCore, AuthState.dropP2, AuthState.setState,
          AuthState.lineage, clearCmpAuth, clearCmp, AuthState.st]
         first
         | exact MonoC.refl _
         | (apply MonoC.of_eq <;> rfl)
         | (apply MonoC.of_ne <;> (simp [checkBit_ne_produce, checkBit_ne_done]; done))
         | (apply MonoC.of_state <;> first | rfl | exact Or.inl rfl | exact Or.inr rfl)))

/-- Split all `if`/`match` and close every leaf (a pair of `MonoA`/`MonoC` goals). -/
syntax "msplit" : tactic
macro_rules
  | `(tactic| msplit) => `(tactic| ((repeat' (first | (dsimp only) | split)) <;>
      (first | (constructor <;> mclose) | mclose)))

/-! ### Core functions -/

theorem genConnect_mono (u : AgentState ψ) : MonoC u (cleanSigGenConnect u) := by
  unfold cleanSigGenConnect; msplit

theorem releaseSource_mono (hψ : ψ > 0) (l r : AgentState ψ) :
    MonoC l (releaseSource hψ l r).1 ∧ MonoC r (releaseSource hψ l r).2 := by
  unfold releaseSource; msplit

theorem eliminate_mono (hψ : ψ > 0) (l r : AgentState ψ) :
    MonoC l (eliminateSig hψ l r).1 ∧ MonoC r (eliminateSig hψ l r).2 := by
  unfold eliminateSig; msplit

theorem control_mono (hψ : ψ > 0) (u : AgentState ψ) :
    MonoC u (sigMoveApplyControlConsume hψ u) := by
  unfold sigMoveApplyControlConsume; msplit

theorem dropStale_mono (u : AgentState ψ) : MonoC u (dropStale u) := by
  unfold dropStale; msplit

theorem orphan_mono (u : AgentState ψ) : MonoC u (normalizeOrphan u) := by
  unfold normalizeOrphan; msplit

theorem releaseCongest_mono (u : AgentState ψ) : MonoC u (releaseCongest u) := by
  unfold releaseCongest; msplit

theorem carrier_mono (u : AgentState ψ) : MonoC u (normalizeCarrier u) := by
  unfold normalizeCarrier
  split
  · exact MonoC.refl _
  · split
    · exact releaseCongest_mono u
    · split <;> mclose

theorem checkReady_mono (u : AgentState ψ) : MonoC u (checkSigSetReadyGuarded u) := by
  unfold checkSigSetReadyGuarded checkSigSetReady; msplit

theorem checkL_mono (hψ : ψ > 0) (u : AgentState ψ) : MonoC u (checkSigCheckL hψ u) := by
  unfold checkSigCheckL; msplit

theorem checkR_mono (hψ : ψ > 0) (l r : AgentState ψ) : MonoC r (checkSigCheckR hψ l r) := by
  unfold checkSigCheckR; msplit

theorem result_mono (u : AgentState ψ) : MonoC u (checkSigSetResult u) := by
  unfold checkSigSetResult; msplit

theorem disStart_mono (hψ : ψ > 0) (l r : AgentState ψ) :
    MonoC l (disappearStartL hψ l r).1 ∧ MonoC r (disappearStartL hψ l r).2 := by
  unfold disappearStartL; msplit

theorem disCarry_mono (hψ : ψ > 0) (l r : AgentState ψ) :
    MonoC l (disappearCarry hψ l r).1 ∧ MonoC r (disappearCarry hψ l r).2 := by
  unfold disappearCarry; msplit

theorem releaseSuffix_mono (l r : AgentState ψ) :
    MonoC l (releaseReadySuffix l r).1 ∧ MonoC r (releaseReadySuffix l r).2 := by
  unfold releaseReadySuffix; msplit

theorem ackTail_mono (l r : AgentState ψ) :
    MonoC l (ackTail l r).1 ∧ MonoC r (ackTail l r).2 := by
  unfold ackTail; msplit

theorem dropStray_mono (l r : AgentState ψ) :
    MonoC l (PPLLFableDesignR1.dropStray l r).1 ∧ MonoC r (PPLLFableDesignR1.dropStray l r).2 := by
  unfold PPLLFableDesignR1.dropStray; msplit

theorem landBackward_mono (u : AgentState ψ) : MonoC u (PPLLFableDesignR1.landBackward u) := by
  unfold PPLLFableDesignR1.landBackward; msplit

theorem landForward_mono (κ : Nat) (d e : Bool) (u : AgentState ψ) :
    MonoC u (PPLLFableDesignR1.landForward κ d e u) := by
  unfold PPLLFableDesignR1.landForward; msplit

end Mono

/-! ### AuthF stages -/

section MonoStages
variable {ψ : Nat}

/-- Both endpoints of a pair stage output are `MonoA`-descendants of the inputs. -/
def PM (q : AuthState ψ × AuthState ψ) (l r : AuthState ψ) : Prop := MonoA l q.1 ∧ MonoA r q.2

theorem PM.trans {l r : AuthState ψ} {q q' : AuthState ψ × AuthState ψ}
    (h1 : PM q l r) (h2 : PM q' q.1 q.2) : PM q' l r :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem PM.refl (l r : AuthState ψ) : PM (l, r) l r := ⟨MonoA.refl _, MonoA.refl _⟩

theorem liftLife_mono (f : AgentState ψ → AgentState ψ) (hf : ∀ a, MonoC a (f a))
    (u : AuthState ψ) : MonoA u (liftLife f u) := by
  unfold liftLife; dsimp only
  split
  · exact hf u.core
  · exact hf u.core

theorem lift2_pm (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, MonoC a (f a b).1 ∧ MonoC b (f a b).2) (l r : AuthState ψ) :
    PM (lift2 f l r) l r := hf l.core r.core

theorem lift2Life_pm (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, MonoC a (f a b).1 ∧ MonoC b (f a b).2) (l r : AuthState ψ) :
    PM (lift2Life f l r) l r := by
  have h := hf l.core r.core
  unfold lift2Life PM
  constructor
  · dsimp only
    split
    · exact h.1
    · exact h.1
  · dsimp only
    split
    · exact h.2
    · exact h.2

theorem clearAuth_mono (u : AuthState ψ) : MonoA u (clearCmpAuth u) := by
  apply MonoC.of_ne <;> simp [clearCmpAuth, clearCmp]

theorem dropP2_mono (u : AuthState ψ) : MonoA u u.dropP2 := MonoC.of_eq rfl rfl

theorem genConnectAuth_mono (u : AuthState ψ) : MonoA u (genConnectAuth u) := by
  unfold genConnectAuth
  split
  · exact genConnect_mono u.core
  · exact MonoA.refl u

theorem step3_pm (nbr mc : Bool) (l r : AuthState ψ) : PM (step3Auth nbr mc l r) l r := by
  unfold step3Auth PM; msplit

theorem step4_pm (nbr mc : Bool) (l r : AuthState ψ) : PM (step4Auth nbr mc l r) l r := by
  unfold step4Auth PM; msplit

theorem step5_pm (hψ : ψ > 0) (l r : AuthState ψ) : PM (step5Auth hψ l r) l r := by
  unfold step5Auth PM; msplit

theorem step6_pm (hψ : ψ > 0) (l r : AuthState ψ) : PM (step6Auth hψ l r) l r := by
  unfold step6Auth PM; msplit

theorem cleanApplyAuth_mono (u : AuthState ψ) : MonoA u (cleanApplyAuth u) := by
  unfold cleanApplyAuth; msplit

theorem cleanSource_pm (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    PM (cleanSourceAuth hψ c l r) l r := by
  unfold cleanSourceAuth
  dsimp only
  have g1 := genConnectAuth_mono l
  have g2 := genConnectAuth_mono r
  generalize genConnectAuth l = l1 at g1 ⊢
  generalize genConnectAuth r = r1 at g2 ⊢
  have h3 := step3_pm c.cleanNbr c.markClean l1 r1
  generalize step3Auth c.cleanNbr c.markClean l1 r1 = q3 at h3 ⊢
  obtain ⟨l3, r3⟩ := q3
  have h4 := step4_pm c.cleanNbr c.markClean l3 r3
  generalize step4Auth c.cleanNbr c.markClean l3 r3 = q4 at h4 ⊢
  obtain ⟨l4, r4⟩ := q4
  have h5 : PM (if isCmd l4.core.path4 = true then
      (l4, { r4 with core := { r4.core with path4 := none } }) else step5Auth hψ l4 r4) l4 r4 := by
    split
    · exact ⟨MonoA.refl _, MonoC.of_eq rfl rfl⟩
    · exact step5_pm hψ l4 r4
  generalize (if isCmd l4.core.path4 = true then
      (l4, { r4 with core := { r4.core with path4 := none } }) else step5Auth hψ l4 r4) = q5 at h5 ⊢
  obtain ⟨l5, r5⟩ := q5
  have h6 : PM (if isCmd r5.core.path5 = true then
      ({ l5 with core := { l5.core with path5 := none } }, r5) else step6Auth hψ l5 r5) l5 r5 := by
    split
    · exact ⟨MonoC.of_eq rfl rfl, MonoA.refl _⟩
    · exact step6_pm hψ l5 r5
  generalize (if isCmd r5.core.path5 = true then
      ({ l5 with core := { l5.core with path5 := none } }, r5) else step6Auth hψ l5 r5) = q6 at h6 ⊢
  obtain ⟨l6, r6⟩ := q6
  exact ⟨g1.trans (h3.1.trans (h4.1.trans (h5.1.trans (h6.1.trans (cleanApplyAuth_mono _))))),
    g2.trans (h3.2.trans (h4.2.trans (h5.2.trans (h6.2.trans (cleanApplyAuth_mono _)))))⟩

theorem validate_pm (l r : AuthState ψ) : PM (validateCheck l r) l r := by
  unfold validateCheck PM demote; msplit

theorem sanitize_mono (u : AuthState ψ) : MonoA u (sanitizeP2 u) := by
  unfold sanitizeP2; msplit

theorem step1_pm (l r : AuthState ψ) : PM (step1Auth l r) l r := by
  unfold step1Auth PM; msplit

theorem receive_mono (e : Entry) (src dst : AuthState ψ) (t : Path2Info) :
    MonoA dst (receive e src dst t) := by
  unfold receive claimA2; msplit

theorem receive_drop_mono (e : Entry) (src dst : AuthState ψ) (t : Path2Info) (b : Prop)
    [Decidable b] : MonoA dst (receive e src (if b then dst.dropP2 else dst) t) := by
  split
  · exact MonoA.trans (dropP2_mono dst) (receive_mono e src _ t)
  · exact receive_mono e src dst t

set_option maxHeartbeats 4000000 in
theorem moveTokens_pm (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    PM (moveTokensAuth c l r) l r := by
  unfold PM
  cases h1 : l.core.path2 <;> cases h2 : r.core.path2 <;> simp only [moveTokensAuth, h1, h2] <;>
    (repeat' (first | (dsimp only) | split)) <;>
    (constructor <;> first
      | exact MonoA.refl _
      | exact dropP2_mono _
      | exact (dropP2_mono _).trans (dropP2_mono _)
      | exact receive_mono _ _ _ _
      | exact (dropP2_mono _).trans (receive_mono _ _ _ _)
      | exact clearAuth_mono _)

theorem leaderWall_pm (l r : AuthState ψ) : PM (leaderWallAuth l r) l r := by
  unfold leaderWallAuth PM
  dsimp only
  refine ⟨?_, ?_⟩ <;> split
  all_goals first | exact clearAuth_mono _ | exact MonoA.refl _

theorem applyControl_mono (hψ : ψ > 0) (u : AuthState ψ) : MonoA u (applyControlAuth hψ u) := by
  unfold applyControlAuth
  (repeat' (first | (dsimp only) | split))
  all_goals first
    | exact MonoA.refl _
    | exact dropP2_mono _
    | exact control_mono hψ u.core

theorem moveSource_pm (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    PM (moveSourceAuth hψ c l r) l r := by
  unfold moveSourceAuth
  dsimp only
  have ha : MonoA l (if l.core.leader = true ∨ (r.core.leader = true ∧
      r.core.label ≠ ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) then clearCmpAuth l else l) := by
    split
    · exact clearAuth_mono l
    · exact MonoA.refl l
  have hb : MonoA r (if r.core.leader = true then clearCmpAuth r else r) := by
    split
    · exact clearAuth_mono r
    · exact MonoA.refl r
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
  have h3 : PM (if l2.st = MainState.done then (l2, r2) else step1Auth l2 r2) l2 r2 := by
    split
    · exact PM.refl l2 r2
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
  have h7 : MonoA l6 (if r6.st = MainState.depart ∧ l6.core.label.val < ψ - 1 ∧
      l6.st = MainState.CHECK_ready then l6.lineage MainState.depart else l6) := by
    split
    · exact MonoC.of_ne (by simp [AuthState.lineage]) (by simp [AuthState.lineage])
    · exact MonoA.refl l6
  exact ⟨ha.trans (h1.1.trans (s1.trans (h3.1.trans (h4.1.trans (h5.1.trans (a1.trans h7)))))),
    hb.trans (h1.2.trans (s2.trans (h3.2.trans (h4.2.trans (h5.2.trans a2)))))⟩

theorem preCheck_pm (l r : AuthState ψ) : PM (preCheckResetAuth l r) l r := by
  unfold preCheckResetAuth PM
  dsimp only
  refine ⟨?_, ?_⟩ <;> split
  all_goals first | exact clearAuth_mono _ | exact MonoA.refl _

theorem normalizeReady_mono (u : AgentState ψ) : MonoC u (normalizeReady u) := by
  unfold normalizeReady
  dsimp only
  have h1 := orphan_mono u
  generalize normalizeOrphan u = u1 at h1 ⊢
  have h2 : MonoC u1 (if u1.state = MainState.none ∧ aligned u1 = true then u1
      else normalizeCarrier u1) := by
    split
    · exact MonoC.refl _
    · exact carrier_mono u1
  generalize (if u1.state = MainState.none ∧ aligned u1 = true then u1
      else normalizeCarrier u1) = u2 at h2 ⊢
  refine h1.trans (h2.trans ?_)
  msplit

/-- `normalizeReady` leaves no occupied `produce` on a follower. -/
theorem normalizeReady_noPo (u : AgentState ψ) (h : (normalizeReady u).leader = false) :
    ¬ ((normalizeReady u).state = .produce ∧ (normalizeReady u).path ≠ .bot) := by
  revert h
  unfold normalizeReady
  dsimp only
  generalize normalizeOrphan u = u1
  generalize (if u1.state = MainState.none ∧ aligned u1 = true then u1
      else normalizeCarrier u1) = u2
  (repeat' (first | (dsimp only) | split)) <;> simp_all

theorem readyAuth_mono (u : AuthState ψ) : MonoA u (readyAuth u) := by
  unfold readyAuth
  dsimp only
  split
  · exact MonoA.refl u
  · have h := checkReady_mono u.core
    split
    · exact h
    · exact h

theorem issue_mono (u : AuthState ψ) : MonoA u (issue u) := by
  unfold issue
  split
  · exact result_mono u.core
  · exact MonoA.refl u

/-! CHECK decomposed into named cell steps (definitionally equal to `checkSourceAuth`). -/

def csA (c : PPLLAuthF.Cfg) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  (if (!c.strictReady || isHead l) = true then readyAuth l else l,
   if (!c.strictReady || isHead r) = true then readyAuth r else r)

def csB (l r : AuthState ψ) : AuthState ψ :=
  if r.st = .depart ∧ aligned r.core ∧ l.st = .equal ∧ aligned l.core ∧
      l.core.label.val < ψ - 1 then l.lineage .depart else l

def csC (hψ : ψ > 0) (l : AuthState ψ) : AuthState ψ := l.withCore (checkSigCheckL hψ l.core)

def csD (c : PPLLAuthF.Cfg) (cert : Bool) (r : AuthState ψ) : AuthState ψ :=
  if c.strictReady && cert && !isHead r then
    let v := checkSigSetReadyGuarded r.core
    if v.state = .CHECK_ready ∧ r.st ≠ .CHECK_ready ∧ ¬ waveState r.st ∧ r.st ≠ .congest ∧
        r.st ≠ .done then
      { r with core := v, ctrl_mark := r.path_mark } else r
  else r

def csE (hψ : ψ > 0) (cert : Bool) (l r : AuthState ψ) : AuthState ψ :=
  if cert then r.withCore (checkSigCheckR hψ l.core r.core) else r

def csF (l : AuthState ψ) : AuthState ψ :=
  if isHead l && l.ctrl_mark == l.path_mark then issue l else l

def csG (cert : Bool) (r : AuthState ψ) : AuthState ψ :=
  if (isHead r && r.ctrl_mark == r.path_mark) || (cert && r.ctrl_mark == r.path_mark) then
    issue r else r

def csH (hψ : ψ > 0) (cert : Bool) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let birthOK : Bool := cert || (ψ == 1 && isHead r && r.ctrl_mark == r.path_mark)
  if r.core.label = ⟨ψ - 1, by omega⟩ ∧ r.st = .equal ∧ birthOK then
    (l, { r with core := { r.core with leader := true } }) else (l, r)

theorem checkSource_eq (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    checkSourceAuth hψ c l r =
      (let q := validateCheck l r
       let q := csA c q.1 q.2
       let l2 := csC hψ (csB q.1 q.2)
       let cert := certPred l2 q.2
       csH hψ cert (csF l2) (csG cert (csE hψ cert l2 (csD c cert q.2)))) := rfl

theorem checkSource_pm (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    PM (checkSourceAuth hψ c l r) l r := by
  rw [checkSource_eq]
  have h1 := validate_pm l r
  generalize validateCheck l r = q1 at h1 ⊢
  obtain ⟨l1, r1⟩ := q1
  have h2 : PM (csA c l1 r1) l1 r1 := by
    unfold csA
    constructor
    · dsimp only; split
      · exact readyAuth_mono l1
      · exact MonoA.refl l1
    · dsimp only; split
      · exact readyAuth_mono r1
      · exact MonoA.refl r1
  dsimp only
  generalize csA c l1 r1 = q2 at h2 ⊢
  obtain ⟨l2, r2⟩ := q2
  dsimp only
  have h3 : MonoA l2 (csB l2 r2) := by
    unfold csB; split
    · exact MonoC.of_ne (by simp [AuthState.lineage]) (by simp [AuthState.lineage])
    · exact MonoA.refl l2
  have h4 : MonoA (csB l2 r2) (csC hψ (csB l2 r2)) := checkL_mono hψ _
  generalize csC hψ (csB l2 r2) = l4 at h4 ⊢
  generalize certPred l4 r2 = cert
  have h5 : MonoA r2 (csD c cert r2) := by
    unfold csD; split
    · dsimp only; split
      · exact checkReady_mono r2.core
      · exact MonoA.refl r2
    · exact MonoA.refl r2
  have h6 : MonoA (csD c cert r2) (csE hψ cert l4 (csD c cert r2)) := by
    unfold csE; split
    · exact checkR_mono hψ _ _
    · exact MonoA.refl _
  have h7 : MonoA l4 (csF l4) := by
    unfold csF; split
    · exact issue_mono l4
    · exact MonoA.refl l4
  have h8 : ∀ u : AuthState ψ, MonoA u (csG cert u) := by
    intro u; unfold csG; split
    · exact issue_mono u
    · exact MonoA.refl u
  have h9 : ∀ a b : AuthState ψ, PM (csH hψ cert a b) a b := by
    intro a b; unfold csH; dsimp only; split
    · exact ⟨MonoA.refl _, MonoC.of_eq rfl rfl⟩
    · exact PM.refl a b
  exact PM.trans (q := (csF l4, csG cert (csE hψ cert l4 (csD c cert r2))))
    ⟨h1.1.trans (h2.1.trans (h3.trans (h4.trans h7))),
     h1.2.trans (h2.2.trans (h5.trans (h6.trans (h8 _))))⟩ (h9 _ _)

theorem disappear_pm (hψ : ψ > 0) (l r : AuthState ψ) : PM (disappearAuth hψ l r) l r := by
  unfold disappearAuth
  dsimp only
  have h0 : MonoA r (if r.st = MainState.toss ∧ r.core.label = ⟨0, hψ⟩ then
      { r with core := { r.core with state := MainState.toss_done, path2 := some ⟨0, 0, 0, 5⟩,
                                      p := false },
               path2_scope := P2Scope.line, path2_mark := r.ctrl_mark }
      else r) := by
    split
    · exact MonoC.of_ne (by simp) (by simp)
    · exact MonoA.refl r
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

theorem repair_pm (l r : AuthState ψ) : PM (repairAuth l r) l r := by
  unfold repairAuth
  dsimp only
  have hc : ∀ a : AgentState ψ, MonoC a (normalizeCarrier (normalizeOrphan a)) :=
    fun a => (orphan_mono a).trans (carrier_mono _)
  have h1 := liftLife_mono _ hc l
  have h2 := liftLife_mono _ hc r
  generalize liftLife (fun u => normalizeCarrier (normalizeOrphan u)) l = l1 at h1 ⊢
  generalize liftLife (fun u => normalizeCarrier (normalizeOrphan u)) r = r1 at h2 ⊢
  have h3 := lift2Life_pm releaseReadySuffix releaseSuffix_mono l1 r1
  generalize lift2Life releaseReadySuffix l1 r1 = q3 at h3 ⊢
  obtain ⟨l3, r3⟩ := q3
  have h4 : PM (ackTailAuth l3 r3) l3 r3 := by
    unfold ackTailAuth
    split
    · exact lift2_pm ackTail ackTail_mono l3 r3
    · exact PM.refl l3 r3
  exact ⟨h1.trans (h3.1.trans h4.1), h2.trans (h3.2.trans h4.2)⟩

theorem maintain_pm (l r : AuthState ψ) : PM (maintainAuth l r) l r := by
  unfold maintainAuth PM; msplit

theorem completeWave_pm (l r : AuthState ψ) : PM (completeWaveAuth l r) l r := by
  unfold completeWaveAuth PM; msplit

theorem wave_pm (l r : AuthState ψ) : PM (waveAuth l r) l r := by
  unfold waveAuth PM; msplit

theorem landBackwardAuth_mono (u : AuthState ψ) : MonoA u (landBackwardAuth u) := by
  unfold landBackwardAuth
  (repeat' (first | (dsimp only) | split))
  all_goals first
    | exact MonoA.refl _
    | exact dropP2_mono _
    | exact landBackward_mono u.core

theorem landForwardAuth_mono (κ : Nat) (u : AuthState ψ) : MonoA u (landForwardAuth κ u) := by
  unfold landForwardAuth
  (repeat' (first | (dsimp only) | split))
  all_goals first
    | exact MonoA.refl _
    | exact dropP2_mono _
    | exact landForward_mono κ false true u.core

def cmp0 (l : AuthState ψ) : AuthState ψ :=
  match l.core.path with
  | .bot => if l.st = .produce then l else l.setState .none
  | .some _ _ => l

def cmpTail (κ : Nat) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let (l, r) := maintainAuth l r
  let (l, r) := completeWaveAuth l r
  let (l, r) := waveAuth l r
  let (l, r) := lift2 PPLLFableDesignR1.dropStray l r
  (landBackwardAuth l, landForwardAuth κ r)

theorem compare_eq (κ : Nat) (l r : AuthState ψ) :
    compareLifecycleAuth κ l r = cmpTail κ (cmp0 l) r := by
  unfold compareLifecycleAuth cmpTail cmp0; rfl

theorem cmpTail_pm (κ : Nat) (l r : AuthState ψ) : PM (cmpTail κ l r) l r := by
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

theorem cmp0_mono (l : AuthState ψ) : MonoA l (cmp0 l) := by
  unfold cmp0
  split
  · split
    · exact MonoA.refl l
    · exact MonoC.of_ne (by simp [AuthState.setState]) (by simp [AuthState.setState])
  · exact MonoA.refl l

theorem compare_pm (κ : Nat) (l r : AuthState ψ) : PM (compareLifecycleAuth κ l r) l r := by
  rw [compare_eq]
  have h := cmpTail_pm κ (cmp0 l) r
  exact ⟨(cmp0_mono l).trans h.1, h.2⟩

end MonoStages

/-! ## Part D. One row as a chain of named pair stages

`restPair` is the AuthF prefix after GENSIG (CLEAN through the comparison
lifecycle), written as eleven pair stages `T1 … T11`.  `mid` of
`PPLLAuthResetDrain` is `restPair` after `genSigAuth`, definitionally. -/

section Row
variable {ψ : Nat}

open PPLLAuthResetDrain (av dv mid beforeSuppressAuth)

abbrev Pair (ψ : Nat) : Type := AuthState ψ × AuthState ψ

def T1 (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) : Pair ψ := cleanSourceAuth hψ c q.1 q.2
def T2 (hψ : ψ > 0) (q : Pair ψ) : Pair ψ := lift2Life (releaseSource hψ) q.1 q.2
def T3 (hψ : ψ > 0) (q : Pair ψ) : Pair ψ := lift2 (eliminateSig hψ) q.1 q.2
def T4 (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) : Pair ψ := moveSourceAuth hψ c q.1 q.2
def T5 (q : Pair ψ) : Pair ψ := (liftLife dropStale q.1, liftLife dropStale q.2)
def T6 (q : Pair ψ) : Pair ψ := preCheckResetAuth q.1 q.2
def T7 (q : Pair ψ) : Pair ψ := (liftLife normalizeReady q.1, liftLife normalizeReady q.2)
def T8 (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) : Pair ψ := checkSourceAuth hψ c q.1 q.2
def T9 (hψ : ψ > 0) (q : Pair ψ) : Pair ψ := disappearAuth hψ q.1 q.2
def T10 (q : Pair ψ) : Pair ψ := repairAuth q.1 q.2
def T11 (κ : Nat) (q : Pair ψ) : Pair ψ := compareLifecycleAuth κ q.1 q.2

/-- The stages between the release `T2` and the normalisation `T7`. -/
def restLo (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) : Pair ψ :=
  T6 (T5 (T4 hψ c (T3 hψ q)))

/-- The stages after the normalisation `T7`. -/
def restHi (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ) : Pair ψ :=
  T11 κ (T10 (T9 hψ (T8 hψ c q)))

/-- The AuthF row after GENSIG and before Algorithm 14. -/
def restPair (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ) : Pair ψ :=
  restHi hψ κ c (T7 (restLo hψ c (T2 hψ (T1 hψ c q))))

theorem mid_eq (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    mid hψ κ c l r = restPair hψ κ c (genSigAuth hψ κ l r) := rfl

/-- The P′ stage as a pair map. -/
def P0 (hψ : ψ > 0) (l r : AuthState ψ) : Pair ψ := lift2 (pPsiProbeWall hψ) l r

theorem beforeSuppress_eq (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    beforeSuppressAuth hψ κ c l r =
      restPair hψ κ c (genSigAuth hψ κ (P0 hψ l r).1 (P0 hψ l r).2) := rfl

/-! ### No stage of `restPair` creates a generation state -/

theorem T1_pm (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) : PM (T1 hψ c q) q.1 q.2 :=
  cleanSource_pm hψ c q.1 q.2
theorem T2_pm (hψ : ψ > 0) (q : Pair ψ) : PM (T2 hψ q) q.1 q.2 :=
  lift2Life_pm _ (releaseSource_mono hψ) q.1 q.2
theorem T3_pm (hψ : ψ > 0) (q : Pair ψ) : PM (T3 hψ q) q.1 q.2 :=
  lift2_pm _ (eliminate_mono hψ) q.1 q.2
theorem T4_pm (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) : PM (T4 hψ c q) q.1 q.2 :=
  moveSource_pm hψ c q.1 q.2
theorem T5_pm (q : Pair ψ) : PM (T5 q) q.1 q.2 :=
  ⟨liftLife_mono _ dropStale_mono q.1, liftLife_mono _ dropStale_mono q.2⟩
theorem T6_pm (q : Pair ψ) : PM (T6 q) q.1 q.2 := preCheck_pm q.1 q.2
theorem T7_pm (q : Pair ψ) : PM (T7 q) q.1 q.2 :=
  ⟨liftLife_mono _ normalizeReady_mono q.1, liftLife_mono _ normalizeReady_mono q.2⟩
theorem T8_pm (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) : PM (T8 hψ c q) q.1 q.2 :=
  checkSource_pm hψ c q.1 q.2
theorem T9_pm (hψ : ψ > 0) (q : Pair ψ) : PM (T9 hψ q) q.1 q.2 := disappear_pm hψ q.1 q.2
theorem T10_pm (q : Pair ψ) : PM (T10 q) q.1 q.2 := repair_pm q.1 q.2
theorem T11_pm (κ : Nat) (q : Pair ψ) : PM (T11 κ q) q.1 q.2 := compare_pm κ q.1 q.2

theorem restLo_pm (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) :
    PM (restLo hψ c q) q.1 q.2 :=
  (((T3_pm hψ q).trans (T4_pm hψ c _)).trans (T5_pm _)).trans (T6_pm _)

theorem restHi_pm (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ) :
    PM (restHi hψ κ c q) q.1 q.2 :=
  (((T8_pm hψ c q).trans (T9_pm hψ _)).trans (T10_pm _)).trans (T11_pm κ _)

/-- No stage after GENSIG creates `produce`/`done` or an occupied `produce`. -/
theorem restPair_pm (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ) :
    PM (restPair hψ κ c q) q.1 q.2 :=
  ((((T1_pm hψ c q).trans (T2_pm hψ _)).trans (restLo_pm hψ c _)).trans (T7_pm _)).trans
    (restHi_pm hψ κ c _)

/-! ### Drain views through the stages before CHECK -/

/-- Both endpoints keep their drain view (reset, echo, label, leader). -/
def PA (q q' : Pair ψ) : Prop := av q'.1 = av q.1 ∧ av q'.2 = av q.2

theorem PA.trans {q q' q'' : Pair ψ} (h1 : PA q q') (h2 : PA q' q'') : PA q q'' :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem T1_pa (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) : PA q (T1 hψ c q) :=
  PPLLAuthResetDrain.cleanSource_av hψ c q.1 q.2
theorem T2_pa (hψ : ψ > 0) (q : Pair ψ) : PA q (T2 hψ q) :=
  PPLLAuthResetDrain.lift2Life_av _ (PPLLAuthResetDrain.releaseSource_dv hψ) q.1 q.2
theorem T3_pa (hψ : ψ > 0) (q : Pair ψ) : PA q (T3 hψ q) :=
  PPLLAuthResetDrain.lift2_av _ (PPLLAuthResetDrain.eliminate_dv hψ) q.1 q.2
theorem T4_pa (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) : PA q (T4 hψ c q) :=
  PPLLAuthResetDrain.moveSource_av hψ c q.1 q.2
theorem T5_pa (q : Pair ψ) : PA q (T5 q) :=
  ⟨PPLLAuthResetDrain.liftLife_av _ PPLLAuthResetDrain.dropStale_dv q.1,
   PPLLAuthResetDrain.liftLife_av _ PPLLAuthResetDrain.dropStale_dv q.2⟩
theorem T6_pa (q : Pair ψ) : PA q (T6 q) := PPLLAuthResetDrain.preCheck_av q.1 q.2
theorem T7_pa (q : Pair ψ) : PA q (T7 q) :=
  ⟨PPLLAuthResetDrain.liftLife_av _ PPLLAuthResetDrain.ready_dv q.1,
   PPLLAuthResetDrain.liftLife_av _ PPLLAuthResetDrain.ready_dv q.2⟩

theorem restLo_pa (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) : PA q (restLo hψ c q) :=
  (((T3_pa hψ q).trans (T4_pa hψ c _)).trans (T5_pa _)).trans (T6_pa _)

theorem genSig_pa (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) : PA (l, r) (genSigAuth hψ κ l r) :=
  PPLLAuthResetDrain.genSig_av hψ κ l r

theorem av_leader (u : AuthState ψ) : u.core.leader = (av u).2.2.2 := rfl
theorem av_label (u : AuthState ψ) : u.core.label = (av u).2.2.1 := rfl
theorem av_reset (u : AuthState ψ) : u.core.reset_cmd = (av u).1 := rfl

/-! ### Occupied `produce` does not survive a follower row -/

/-- An occupied `produce` cell. -/
def Po (u : AuthState ψ) : Prop := u.core.state = .produce ∧ u.core.path ≠ .bot

theorem MonoA.noPo {a b : AuthState ψ} (h : MonoA a b) (ha : ¬ Po a) : ¬ Po b :=
  fun hb => ha ⟨h.1 hb.1, h.2.2 hb.1 hb.2⟩

theorem liftLife_core (f : AgentState ψ → AgentState ψ) (u : AuthState ψ) :
    (liftLife f u).core = f u.core := by
  unfold liftLife; dsimp only; split <;> rfl

theorem T7_noPo (q : Pair ψ) (h1 : q.1.core.leader = false) (h2 : q.2.core.leader = false) :
    ¬ Po (T7 q).1 ∧ ¬ Po (T7 q).2 := by
  have e1 : (normalizeReady q.1.core).leader = false := by
    rw [show (normalizeReady q.1.core).leader = (dv (normalizeReady q.1.core)).2.2.2 from rfl,
      PPLLAuthResetDrain.ready_dv]; exact h1
  have e2 : (normalizeReady q.2.core).leader = false := by
    rw [show (normalizeReady q.2.core).leader = (dv (normalizeReady q.2.core)).2.2.2 from rfl,
      PPLLAuthResetDrain.ready_dv]; exact h2
  refine ⟨?_, ?_⟩
  · intro h
    have h' : (T7 q).1.core = normalizeReady q.1.core := liftLife_core _ _
    unfold Po at h; rw [h'] at h
    exact normalizeReady_noPo _ e1 h
  · intro h
    have h' : (T7 q).2.core = normalizeReady q.2.core := liftLife_core _ _
    unfold Po at h; rw [h'] at h
    exact normalizeReady_noPo _ e2 h

/-- F1 on `restPair`: a leaderless GENSIG output leaves no occupied `produce`. -/
theorem restPair_noPo (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ)
    (h1 : q.1.core.leader = false) (h2 : q.2.core.leader = false) :
    ¬ Po (restPair hψ κ c q).1 ∧ ¬ Po (restPair hψ κ c q).2 := by
  have hA : PA q (restLo hψ c (T2 hψ (T1 hψ c q))) :=
    ((T1_pa hψ c q).trans (T2_pa hψ _)).trans (restLo_pa hψ c _)
  have k1 : (restLo hψ c (T2 hψ (T1 hψ c q))).1.core.leader = false := by
    rw [av_leader, hA.1, ← av_leader]; exact h1
  have k2 : (restLo hψ c (T2 hψ (T1 hψ c q))).2.core.leader = false := by
    rw [av_leader, hA.2, ← av_leader]; exact h2
  have hn := T7_noPo _ k1 k2
  have hm := restHi_pm hψ κ c (T7 (restLo hψ c (T2 hψ (T1 hψ c q))))
  exact ⟨hm.1.noPo hn.1, hm.2.noPo hn.2⟩

/-! ### The suffix (Algorithm 14, K4, WRITE, conservation) on a follower pair -/

/-- The fields the generation argument reads after the prefix. -/
def FV (u : AuthState ψ) : MainState × PathInfo × Option Path2Info × Bool × ProvColor × ProvColor :=
  (u.core.state, u.core.path, u.core.path2, u.core.wait, u.ctrl_mark, u.path_mark)

theorem suppress_FV (hψ : ψ > 0) (a b : AuthState ψ) (ha : a.core.leader = false)
    (ha' : a.core.reset_cmd = false) (hb' : b.core.reset_cmd = false) :
    FV (suppressSigResetKillAuth hψ a b).1 = FV a ∧ FV (suppressSigResetKillAuth hψ a b).2 = FV b := by
  simp only [suppressSigResetKillAuth, lift2, suppressSigStart, suppressSigMoveReset,
    suppressSigTerminal, suppressSigFinish, suppressSigEcho]
  simp only [ha, ha', hb', Bool.false_eq_true, ite_false, and_false]
  (repeat' split) <;> simp_all [FV]

theorem suffix_WF (hψ : ψ > 0) (a b : AgentState ψ) :
    WFrame.WF (writeWithBundle hψ (k4Kernel hψ a b).1 (k4Kernel hψ a b).2).1 a ∧
    WFrame.WF (writeWithBundle hψ (k4Kernel hψ a b).1 (k4Kernel hψ a b).2).2 b := by
  have hk := WFrame.kernel_frame hψ a b
  have hw := WFrame.write_frame hψ (k4Kernel hψ a b).1 (k4Kernel hψ a b).2
  unfold WFrame.WF at hk hw ⊢
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hw.1.1, hk.1.1]
  · rw [hw.1.2.1, hk.1.2.1]
  · rw [hw.1.2.2.1, hk.1.2.2.1]
  · rw [hw.1.2.2.2, hk.1.2.2.2]
  · rw [hw.2.1, hk.2.1]
  · rw [hw.2.2.1, hk.2.2.1]
  · rw [hw.2.2.2.1, hk.2.2.2.1]
  · rw [hw.2.2.2.2, hk.2.2.2.2]

/-- SF: on a leaderless, reset-free input pair the whole AuthF row agrees with
its prefix `beforeSuppressAuth` on state, paths, `wait` and the two marks. -/
theorem pipeline_FV (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hl' : l.core.reset_cmd = false) (hr' : r.core.reset_cmd = false) :
    FV (PPLLAuthF.pipeline hψ κ c l r).1 = FV (beforeSuppressAuth hψ κ c l r).1 ∧
    FV (PPLLAuthF.pipeline hψ κ c l r).2 = FV (beforeSuppressAuth hψ κ c l r).2 := by
  have hpf := PPLLAuthResetDrain.prefix_facts hψ κ c l r
  dsimp only at hpf
  obtain ⟨b1, -, b3, -, b5, -, -⟩ := hpf
  have hs := suppress_FV hψ (beforeSuppressAuth hψ κ c l r).1 (beforeSuppressAuth hψ κ c l r).2
    (b5.trans hl) (b1.trans hl') (b3.trans hr')
  rw [← PPLLAuthResetDrain.beforeElimination_eq] at hs
  rw [← hs.1, ← hs.2]
  unfold PPLLAuthF.pipeline
  dsimp only
  generalize PPLLAuthF.beforeElimination hψ κ c l r = E
  have hw := suffix_WF hψ E.1.core E.2.core
  unfold WFrame.WF at hw
  simp only [conserveAuth, conserve, hl, hr, Bool.false_or, Bool.false_and, Bool.false_eq_true,
    ite_false, lift2, FV]
  rw [hw.1.1, hw.1.2.1, hw.1.2.2.1, hw.1.2.2.2, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2]
  exact ⟨rfl, rfl⟩

/-! ### P′ on a correctly labelled follower pair only moves the probe -/

theorem pPsi_frame (hψ : ψ > 0) (l r : AgentState ψ) (hl : l.leader = false)
    (hr : r.leader = false) (hlab : r.label.val = (l.label.val + 1) % ψ) :
    ∃ x y : Bool, pPsiProbeWall hψ l r = ({ l with probe := x }, { r with probe := y }) := by
  have hn : r.label = ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ := Fin.ext hlab
  have e1 : (if l.leader = true then { l with probe := false } else l) = l := if_neg (by simp [hl])
  have e2 : (if r.leader = true ∨ l.leader = true then { r with probe := false } else r) = r :=
    if_neg (by simp [hl, hr])
  have e3 : ¬ (r.label ≠ ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) := by simp [hn]
  unfold pPsiProbeWall
  dsimp only
  rw [e1, e2]
  unfold pPsi
  dsimp only
  rw [if_neg e3]
  split
  · exact ⟨true, false, rfl⟩
  · exact ⟨l.probe, r.probe, rfl⟩

theorem P0_frame (hψ : ψ > 0) (l r : AuthState ψ) (hl : l.core.leader = false)
    (hr : r.core.leader = false) (hlab : r.core.label.val = (l.core.label.val + 1) % ψ) :
    ∃ x y : Bool, P0 hψ l r =
      ({ l with core := { l.core with probe := x } }, { r with core := { r.core with probe := y } }) := by
  obtain ⟨x, y, h⟩ := pPsi_frame hψ l.core r.core hl hr hlab
  refine ⟨x, y, ?_⟩
  unfold P0 lift2
  dsimp only
  rw [h]

end Row

/-! ## Part E. GENSIG on the pairs of the block word

Every lemma below unfolds `genSigAuth`, replaces the WAIT output by its
(state, path, path2, label, leader, marks) frame and splits the five
generation guards (head start, recruitment, emission, propagation, head finish). -/

section GenSig
variable {ψ : Nat}

theorem glabel_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).label = if p then a.label else b.label := by split <;> rfl
theorem gleader_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).leader = if p then a.leader else b.leader := by split <;> rfl

/-- WAIT never touches the fields GENSIG's guards read (besides `wait`). -/
theorem waitSat_fields (hψ : ψ > 0) (κ : Nat) (a b : AgentState ψ) :
    (waitSaturated hψ κ a b).1.state = a.state ∧ (waitSaturated hψ κ a b).1.path = a.path ∧
    (waitSaturated hψ κ a b).1.path2 = a.path2 ∧ (waitSaturated hψ κ a b).1.label = a.label ∧
    (waitSaturated hψ κ a b).1.leader = a.leader ∧
    (waitSaturated hψ κ a b).2.state = b.state ∧ (waitSaturated hψ κ a b).2.path = b.path ∧
    (waitSaturated hψ κ a b).2.path2 = b.path2 ∧ (waitSaturated hψ κ a b).2.label = b.label ∧
    (waitSaturated hψ κ a b).2.leader = b.leader := by
  simp only [waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish]
  simp only [gfst_ite, gsnd_ite, gstate_ite, gpath_ite, gpath2_ite, glabel_ite, gleader_ite,
    ite_self, and_self]

/-- The WAIT stage of GENSIG on `AuthState`s, with its frame. -/
theorem W_fields (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) :
    (lift2 (waitSaturated hψ κ) l r).1.core.state = l.core.state ∧
    (lift2 (waitSaturated hψ κ) l r).1.core.path = l.core.path ∧
    (lift2 (waitSaturated hψ κ) l r).1.core.path2 = l.core.path2 ∧
    (lift2 (waitSaturated hψ κ) l r).1.core.label = l.core.label ∧
    (lift2 (waitSaturated hψ κ) l r).1.core.leader = l.core.leader ∧
    (lift2 (waitSaturated hψ κ) l r).1.ctrl_mark = l.ctrl_mark ∧
    (lift2 (waitSaturated hψ κ) l r).1.path_mark = l.path_mark ∧
    (lift2 (waitSaturated hψ κ) l r).2.core.state = r.core.state ∧
    (lift2 (waitSaturated hψ κ) l r).2.core.path = r.core.path ∧
    (lift2 (waitSaturated hψ κ) l r).2.core.path2 = r.core.path2 ∧
    (lift2 (waitSaturated hψ κ) l r).2.core.label = r.core.label ∧
    (lift2 (waitSaturated hψ κ) l r).2.core.leader = r.core.leader ∧
    (lift2 (waitSaturated hψ κ) l r).2.ctrl_mark = r.ctrl_mark ∧
    (lift2 (waitSaturated hψ κ) l r).2.path_mark = r.path_mark := by
  have h := waitSat_fields hψ κ l.core r.core
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, rfl, rfl,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2, rfl, rfl⟩

/-! ### The five guards of GENSIG as separate maps -/

/-- Line 2: head start on an empty follower head with `wait = false`. -/
def gsH (hψ : ψ > 0) (l r : AuthState ψ) : AuthState ψ :=
  if l.core.leader = false ∧ l.core.label = ⟨0, hψ⟩ ∧ l.core.wait = false ∧
      l.core.path = .bot then
    wipeProduceAuth (if l.st = .produce then l.ctrl_mark else fresh3 l.path_mark r.path_mark) l
  else l

/-- Line 4: recruitment of the successor by a producer. -/
def gsR (hψ : ψ > 0) (l r : AuthState ψ) : AuthState ψ :=
  if r.core.label ≠ ⟨0, hψ⟩ ∧ l.st = .produce ∧
      (r.core.path = .bot ∨ (r.st ≠ .produce ∧ r.st ≠ .done) ∨ r.ctrl_mark ≠ l.ctrl_mark) then
    wipeProduceAuth l.ctrl_mark r
  else r

/-- Emission of the terminal path. -/
def gsE (hψ : ψ > 0) (r : AuthState ψ) : AuthState ψ :=
  if r.core.label = ⟨ψ - 1, by omega⟩ ∧ r.st = .produce then
    { r with core := { r.core with state := .done,
                                   path := .some r.core.label.val (if r.core.bit then 1 else 0) },
             path_mark := r.ctrl_mark }
  else r

/-- Backward propagation of `done`. -/
def gsPair (hψ : ψ > 0) (l r : AuthState ψ) : Pair ψ :=
  if l.core.label ≠ ⟨ψ - 1, by omega⟩ ∧ l.st = .produce ∧ r.st = .done then
    ({ l with core := { l.core with state := .done,
                                    path := .some l.core.label.val (if l.core.bit then 1 else 0) },
              path_mark := r.path_mark, ctrl_mark := r.path_mark },
     r.setState .depart)
  else (l, r)

/-- The head leaves `done` for `depart` and starts waiting. -/
def gsF (hψ : ψ > 0) (l : AuthState ψ) : AuthState ψ :=
  if l.core.label = ⟨0, hψ⟩ ∧ l.st = .done then
    { l with core := { l.core with state := .depart, wait := true } }
  else l

/-- GENSIG after its WAIT stage. -/
def gsBody (hψ : ψ > 0) (l r : AuthState ψ) : Pair ψ :=
  match gsPair hψ (gsH hψ l r) (gsE hψ (gsR hψ (gsH hψ l r) r)) with
  | (l, r) => (gsF hψ l, r)

/-- Reduce a property of GENSIG to its body on an abstract WAIT output that
agrees with the input on state, path, path2, label, leader and both marks. -/
theorem gs_reduce (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) (P : Pair ψ → Prop)
    (h : ∀ l1 r1 : AuthState ψ,
      l1.core.state = l.core.state → l1.core.path = l.core.path →
      l1.core.path2 = l.core.path2 → l1.core.label = l.core.label →
      l1.core.leader = l.core.leader → l1.ctrl_mark = l.ctrl_mark → l1.path_mark = l.path_mark →
      r1.core.state = r.core.state → r1.core.path = r.core.path →
      r1.core.path2 = r.core.path2 → r1.core.label = r.core.label →
      r1.core.leader = r.core.leader → r1.ctrl_mark = r.ctrl_mark → r1.path_mark = r.path_mark →
      P (gsBody hψ l1 r1)) :
    P (genSigAuth hψ κ l r) := by
  have hW := W_fields hψ κ l r
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, f1, f2, f3, f4, f5, f6, f7⟩ := hW
  have key := h _ _ e1 e2 e3 e4 e5 e6 e7 f1 f2 f3 f4 f5 f6 f7
  unfold genSigAuth
  generalize lift2 (waitSaturated hψ κ) l r = w at key ⊢
  obtain ⟨l1, r1⟩ := w
  exact key

/-! ### Specifications of the five maps (labels as naturals) -/

/-- The label and leader bit of a cell. -/
def LL (u : AuthState ψ) : Fin ψ × Bool := (u.core.label, u.core.leader)

theorem gsH_spec (hψ : ψ > 0) (l r : AuthState ψ) :
    LL (gsH hψ l r) = LL l ∧
    ((¬ (l.core.leader = false ∧ l.core.label.val = 0 ∧ l.core.wait = false ∧
          l.core.path = .bot) ∧ gsH hψ l r = l) ∨
     (l.core.leader = false ∧ l.core.label.val = 0 ∧ l.core.wait = false ∧ l.core.path = .bot ∧
      (gsH hψ l r).core.state = .produce ∧ (gsH hψ l r).core.path = .bot ∧
      (gsH hψ l r).core.path2 = none ∧ (gsH hψ l r).core.wait = false ∧
      (l.core.state = .produce → (gsH hψ l r).ctrl_mark = l.ctrl_mark) ∧
      (l.core.state ≠ .produce → (gsH hψ l r).ctrl_mark = fresh3 l.path_mark r.path_mark))) := by
  unfold gsH
  split
  · rename_i h
    refine ⟨rfl, Or.inr ⟨h.1, congrArg Fin.val h.2.1, h.2.2.1, h.2.2.2, rfl, rfl, rfl, h.2.2.1, ?_, ?_⟩⟩
    · intro hp; simp [wipeProduceAuth, AuthState.st, hp]
    · intro hp; simp [wipeProduceAuth, AuthState.st, hp]
  · rename_i h
    refine ⟨rfl, Or.inl ⟨?_, rfl⟩⟩
    intro h'
    exact h ⟨h'.1, Fin.ext h'.2.1, h'.2.2.1, h'.2.2.2⟩

theorem gsR_spec (hψ : ψ > 0) (l r : AuthState ψ) :
    LL (gsR hψ l r) = LL r ∧
    ((¬ (r.core.label.val ≠ 0 ∧ l.core.state = .produce ∧
          (r.core.path = .bot ∨ (r.core.state ≠ .produce ∧ r.core.state ≠ .done) ∨
            r.ctrl_mark ≠ l.ctrl_mark)) ∧ gsR hψ l r = r) ∨
     (r.core.label.val ≠ 0 ∧ l.core.state = .produce ∧
      (r.core.path = .bot ∨ (r.core.state ≠ .produce ∧ r.core.state ≠ .done) ∨
        r.ctrl_mark ≠ l.ctrl_mark) ∧
      (gsR hψ l r).core.state = .produce ∧ (gsR hψ l r).core.path = .bot ∧
      (gsR hψ l r).core.path2 = none ∧ (gsR hψ l r).ctrl_mark = l.ctrl_mark)) := by
  unfold gsR
  split
  · rename_i h
    refine ⟨rfl, Or.inr ⟨fun h0 => h.1 (Fin.ext h0), h.2.1, h.2.2, rfl, rfl, rfl, rfl⟩⟩
  · rename_i h
    refine ⟨rfl, Or.inl ⟨?_, rfl⟩⟩
    intro h'
    exact h ⟨fun h0 => h'.1 (congrArg Fin.val h0), h'.2.1, h'.2.2⟩

theorem gsE_spec (hψ : ψ > 0) (r : AuthState ψ) :
    LL (gsE hψ r) = LL r ∧
    ((¬ (r.core.label.val = ψ - 1 ∧ r.core.state = .produce) ∧ gsE hψ r = r) ∨
     (r.core.label.val = ψ - 1 ∧ r.core.state = .produce ∧
      (gsE hψ r).core.state = .done ∧ (∃ b, (gsE hψ r).core.path = .some r.core.label.val b) ∧
      (gsE hψ r).core.path2 = r.core.path2 ∧ (gsE hψ r).path_mark = r.ctrl_mark ∧
      (gsE hψ r).ctrl_mark = r.ctrl_mark)) := by
  unfold gsE
  split
  · rename_i h
    exact ⟨rfl, Or.inr ⟨congrArg Fin.val h.1, h.2, rfl, ⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  · rename_i h
    refine ⟨rfl, Or.inl ⟨?_, rfl⟩⟩
    intro h'
    exact h ⟨Fin.ext h'.1, h'.2⟩

theorem gsPair_spec (hψ : ψ > 0) (l r : AuthState ψ) :
    LL (gsPair hψ l r).1 = LL l ∧ LL (gsPair hψ l r).2 = LL r ∧
    (gsPair hψ l r).1.core.wait = l.core.wait ∧
    ((¬ (l.core.label.val ≠ ψ - 1 ∧ l.core.state = .produce ∧ r.core.state = .done) ∧
        gsPair hψ l r = (l, r)) ∨
     (l.core.label.val ≠ ψ - 1 ∧ l.core.state = .produce ∧ r.core.state = .done ∧
      (gsPair hψ l r).1.core.state = .done ∧
      (∃ b, (gsPair hψ l r).1.core.path = .some l.core.label.val b) ∧
      (gsPair hψ l r).1.core.path2 = l.core.path2 ∧
      (gsPair hψ l r).1.path_mark = r.path_mark ∧ (gsPair hψ l r).1.ctrl_mark = r.path_mark ∧
      (gsPair hψ l r).2.core.state = .depart ∧ (gsPair hψ l r).2.core.path = r.core.path ∧
      (gsPair hψ l r).2.core.path2 = r.core.path2 ∧ (gsPair hψ l r).2.path_mark = r.path_mark ∧
      (gsPair hψ l r).2.ctrl_mark = r.ctrl_mark)) := by
  unfold gsPair
  split
  · rename_i h
    exact ⟨rfl, rfl, rfl, Or.inr ⟨fun h0 => h.1 (Fin.ext h0), h.2.1, h.2.2, rfl, ⟨_, rfl⟩, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · rename_i h
    refine ⟨rfl, rfl, rfl, Or.inl ⟨?_, rfl⟩⟩
    intro h'
    exact h ⟨fun h0 => h'.1 (congrArg Fin.val h0), h'.2.1, h'.2.2⟩

theorem gsF_spec (hψ : ψ > 0) (l : AuthState ψ) :
    LL (gsF hψ l) = LL l ∧
    ((¬ (l.core.label.val = 0 ∧ l.core.state = .done) ∧ gsF hψ l = l) ∨
     (l.core.label.val = 0 ∧ l.core.state = .done ∧ (gsF hψ l).core.state = .depart)) := by
  unfold gsF
  split
  · rename_i h
    exact ⟨rfl, Or.inr ⟨congrArg Fin.val h.1, h.2, rfl⟩⟩
  · rename_i h
    refine ⟨rfl, Or.inl ⟨?_, rfl⟩⟩
    intro h'
    exact h ⟨Fin.ext h'.1, h'.2⟩

theorem LL_label {u v : AuthState ψ} (h : LL u = LL v) : u.core.label = v.core.label :=
  congrArg Prod.fst h
theorem LL_leader {u v : AuthState ψ} (h : LL u = LL v) : u.core.leader = v.core.leader :=
  congrArg Prod.snd h

/-- Open GENSIG's body into its five maps with all specifications in context. -/
theorem gsBody_open (hψ : ψ > 0) (l r : AuthState ψ) (P : Pair ψ → Prop)
    (h : ∀ (H R E : AuthState ψ) (Q : Pair ψ),
      H = gsH hψ l r → R = gsR hψ H r → E = gsE hψ R → Q = gsPair hψ H E →
      P (gsF hψ Q.1, Q.2)) :
    P (gsBody hψ l r) := by
  unfold gsBody
  have key := h _ _ _ _ rfl rfl rfl rfl
  generalize gsPair hψ (gsH hψ l r) (gsE hψ (gsR hψ (gsH hψ l r) r)) = Q at key ⊢
  obtain ⟨a, b⟩ := Q
  exact key

/-- F2 at GENSIG: the head never leaves GENSIG in `done`. -/
theorem gs_head_not_done (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) (hl0 : l.core.label.val = 0) :
    (genSigAuth hψ κ l r).1.core.state ≠ .done := by
  apply gs_reduce hψ κ l r (fun G => G.1.core.state ≠ .done)
  intro l1 r1 _ _ _ e4 _ _ _ _ _ _ _ _ _ _
  apply gsBody_open hψ l1 r1 (fun G => G.1.core.state ≠ .done)
  intro H R E Q hH hR hE hQ
  dsimp only
  obtain ⟨sH, -⟩ := gsH_spec hψ l1 r1
  obtain ⟨sQ, -, -, -⟩ := gsPair_spec hψ H E
  obtain ⟨-, sF⟩ := gsF_spec hψ Q.1
  rw [← hH] at sH; rw [← hQ] at sQ
  have lab : Q.1.core.label.val = 0 := by
    rw [LL_label sQ, LL_label sH, e4]; exact hl0
  rcases sF with ⟨hn, he⟩ | ⟨-, -, hd⟩
  · rw [he]; intro hd; exact hn ⟨lab, hd⟩
  · rw [hd]; simp

/-- GENSIG opened into WAIT and its five maps. -/
theorem gs_open (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) :
    ∃ (l1 r1 H R E : AuthState ψ) (Q : Pair ψ),
      genSigAuth hψ κ l r = (gsF hψ Q.1, Q.2) ∧
      l1.core.state = l.core.state ∧ l1.core.path = l.core.path ∧
      l1.core.path2 = l.core.path2 ∧ l1.core.label = l.core.label ∧
      l1.core.leader = l.core.leader ∧ l1.ctrl_mark = l.ctrl_mark ∧ l1.path_mark = l.path_mark ∧
      r1.core.state = r.core.state ∧ r1.core.path = r.core.path ∧
      r1.core.path2 = r.core.path2 ∧ r1.core.label = r.core.label ∧
      r1.core.leader = r.core.leader ∧ r1.ctrl_mark = r.ctrl_mark ∧ r1.path_mark = r.path_mark ∧
      H = gsH hψ l1 r1 ∧ R = gsR hψ H r1 ∧ E = gsE hψ R ∧ Q = gsPair hψ H E := by
  apply gs_reduce hψ κ l r (fun G => ∃ (l1 r1 H R E : AuthState ψ) (Q : Pair ψ),
      G = (gsF hψ Q.1, Q.2) ∧
      l1.core.state = l.core.state ∧ l1.core.path = l.core.path ∧
      l1.core.path2 = l.core.path2 ∧ l1.core.label = l.core.label ∧
      l1.core.leader = l.core.leader ∧ l1.ctrl_mark = l.ctrl_mark ∧ l1.path_mark = l.path_mark ∧
      r1.core.state = r.core.state ∧ r1.core.path = r.core.path ∧
      r1.core.path2 = r.core.path2 ∧ r1.core.label = r.core.label ∧
      r1.core.leader = r.core.leader ∧ r1.ctrl_mark = r.ctrl_mark ∧ r1.path_mark = r.path_mark ∧
      H = gsH hψ l1 r1 ∧ R = gsR hψ H r1 ∧ E = gsE hψ R ∧ Q = gsPair hψ H E)
  intro l1 r1 e1 e2 e3 e4 e5 e6 e7 f1 f2 f3 f4 f5 f6 f7
  apply gsBody_open hψ l1 r1 (fun G => ∃ (l1' r1' H R E : AuthState ψ) (Q : Pair ψ),
      G = (gsF hψ Q.1, Q.2) ∧
      l1'.core.state = l.core.state ∧ l1'.core.path = l.core.path ∧
      l1'.core.path2 = l.core.path2 ∧ l1'.core.label = l.core.label ∧
      l1'.core.leader = l.core.leader ∧ l1'.ctrl_mark = l.ctrl_mark ∧ l1'.path_mark = l.path_mark ∧
      r1'.core.state = r.core.state ∧ r1'.core.path = r.core.path ∧
      r1'.core.path2 = r.core.path2 ∧ r1'.core.label = r.core.label ∧
      r1'.core.leader = r.core.leader ∧ r1'.ctrl_mark = r.ctrl_mark ∧ r1'.path_mark = r.path_mark ∧
      H = gsH hψ l1' r1' ∧ R = gsR hψ H r1' ∧ E = gsE hψ R ∧ Q = gsPair hψ H E)
  intro H R E Q hH hR hE hQ
  exact ⟨l1, r1, H, R, E, Q, rfl, e1, e2, e3, e4, e5, e6, e7, f1, f2, f3, f4, f5, f6, f7,
    hH, hR, hE, hQ⟩

-- `gsspecs`: open GENSIG on `l r` and put the five specifications in context.
set_option hygiene false in
macro "gsspecs" : tactic => `(tactic| (
  obtain ⟨l1, r1, H, R, E, Q, hG, e1, e2, e3, e4, e5, e6, e7, f1, f2, f3, f4, f5, f6, f7,
    hH, hR, hE, hQ⟩ := gs_open hψ κ l r
  rw [hG]
  dsimp only
  obtain ⟨LH, sH⟩ := gsH_spec hψ l1 r1
  rw [← hH] at LH sH
  obtain ⟨LR, sR⟩ := gsR_spec hψ H r1
  rw [← hR] at LR sR
  obtain ⟨LE, sE⟩ := gsE_spec hψ R
  rw [← hE] at LE sE
  obtain ⟨LQ1, LQ2, wQ, sQ⟩ := gsPair_spec hψ H E
  rw [← hQ] at LQ1 LQ2 wQ sQ
  obtain ⟨LF, sF⟩ := gsF_spec hψ Q.1
  simp only [LL, Prod.mk.injEq] at LH LR LE LQ1 LQ2 LF
  clear hG hH hR hE hQ))

-- `gscases`: split the five guards.
set_option hygiene false in
macro "gscases" : tactic => `(tactic| (
  rcases sH with ⟨hn1, he1⟩ | ⟨c1, c2, c3, c4, h1, h2, h3, h4, h5, h6⟩ <;>
  rcases sR with ⟨hn2, he2⟩ | ⟨d1, d2, d3, g1, g2, g3, g4⟩ <;>
  rcases sE with ⟨hn3, he3⟩ | ⟨k1, k2, k3, ⟨bE, k4⟩, k5, k6, k7⟩ <;>
  rcases sQ with ⟨hn4, he4⟩ | ⟨m1, m2, m3, m4, ⟨bQ, m5⟩, m6, m7, m8, m9, m10, m11, m12, m13⟩ <;>
  rcases sF with ⟨hn5, he5⟩ | ⟨n1, n2, n3⟩))

/-- F3 at GENSIG: if the responder leaves GENSIG in `done` while the initiator
is in `produce`/`done`, then the initiator entered in `done` and is not the head. -/
theorem gs_F3 (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) (hk : l.core.label.val + 1 < ψ) :
    (genSigAuth hψ κ l r).2.core.state = .done →
    ((genSigAuth hψ κ l r).1.core.state = .produce ∨ (genSigAuth hψ κ l r).1.core.state = .done) →
    l.core.state = .done ∧ l.core.label.val ≠ 0 := by
  gsspecs
  intro hrd hlpd
  have hkT : l.core.label.val ≠ ψ - 1 := by omega
  gscases <;> simp_all <;> omega

/-- C1 at GENSIG: a pathless producer recruits a non-terminal successor that is
neither `done` nor an occupied `produce`; both leave GENSIG as pathless
producers of the initiator's generation colour. -/
theorem gs_recruit (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (hlP : l.core.state = .produce) (hlb : l.core.path = .bot)
    (hrD : r.core.state ≠ .done) (hrP : r.core.state = .produce → r.core.path = .bot)
    (hr0 : r.core.label.val ≠ 0) (hrT : r.core.label.val ≠ ψ - 1) (hlT : l.core.label.val ≠ ψ - 1) :
    (genSigAuth hψ κ l r).1.core.state = .produce ∧ (genSigAuth hψ κ l r).1.core.path = .bot ∧
    (genSigAuth hψ κ l r).1.ctrl_mark = l.ctrl_mark ∧
    (genSigAuth hψ κ l r).2.core.state = .produce ∧ (genSigAuth hψ κ l r).2.core.path = .bot ∧
    (genSigAuth hψ κ l r).2.ctrl_mark = l.ctrl_mark := by
  gsspecs
  gscases <;> subst_vars <;> simp_all <;> omega

/-- C2/C3 at GENSIG: a pathless producer next to its emitting terminal or to a
`done` cell of its own colour turns `done` (the head: `depart`) and releases
the successor to `depart`; paths and colours line up. -/
theorem gs_prop (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (hlP : l.core.state = .produce) (hlb : l.core.path = .bot)
    (hlT : l.core.label.val ≠ ψ - 1) (hr0 : r.core.label.val ≠ 0)
    (hr : (r.core.label.val = ψ - 1 ∧ r.core.state ≠ .done ∧
        (r.core.state = .produce → r.core.path = .bot)) ∨
      (r.core.label.val ≠ ψ - 1 ∧ r.core.state = .done ∧ r.ctrl_mark = l.ctrl_mark ∧
        r.path_mark = l.ctrl_mark ∧ ∃ b, r.core.path = .some r.core.label.val b)) :
    (genSigAuth hψ κ l r).2.core.state = .depart ∧
    (∃ b, (genSigAuth hψ κ l r).2.core.path = .some r.core.label.val b) ∧
    (genSigAuth hψ κ l r).2.path_mark = l.ctrl_mark ∧
    ((r.core.path2 = none ∨ r.core.label.val = ψ - 1) → (genSigAuth hψ κ l r).2.core.path2 = none) ∧
    (l.core.label.val = 0 → (genSigAuth hψ κ l r).1.core.state = .depart) ∧
    (l.core.label.val ≠ 0 → (genSigAuth hψ κ l r).1.core.state = .done ∧
      (∃ b, (genSigAuth hψ κ l r).1.core.path = .some l.core.label.val b) ∧
      (genSigAuth hψ κ l r).1.ctrl_mark = l.ctrl_mark ∧
      (genSigAuth hψ κ l r).1.path_mark = l.ctrl_mark ∧
      (l.core.path2 = none → (genSigAuth hψ κ l r).1.core.path2 = none)) := by
  gsspecs
  gscases <;> subst_vars <;> simp_all

/-- C4/C5 at GENSIG: a non-generation initiator next to a successor that is not
a producer (or is the pathless terminal producer).  Either no generation state
is left besides a `done` successor, or the head started a generation and
recruited a non-terminal successor. -/
theorem gs_release (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (hlN1 : l.core.state ≠ .produce) (hlN2 : l.core.state ≠ .done)
    (hlT : l.core.label.val ≠ ψ - 1) (hr0 : r.core.label.val ≠ 0)
    (hr : r.core.state = .produce → r.core.path = .bot ∧ r.core.label.val = ψ - 1) :
    ((genSigAuth hψ κ l r).1.core.state ≠ .produce ∧ (genSigAuth hψ κ l r).1.core.state ≠ .done ∧
      (genSigAuth hψ κ l r).2.core.state ≠ .produce) ∨
    (l.core.label.val = 0 ∧ (genSigAuth hψ κ l r).1.core.state = .produce ∧
      (genSigAuth hψ κ l r).1.core.path = .bot ∧ (genSigAuth hψ κ l r).1.core.wait = false ∧
      (genSigAuth hψ κ l r).2.core.state = .produce ∧ (genSigAuth hψ κ l r).2.core.path = .bot ∧
      r.core.label.val ≠ ψ - 1) := by
  gsspecs
  gscases <;> subst_vars <;> (try simp_all) <;> (intro hp; have hh := hr hp; simp_all)

end GenSig

/-! ## Part F. Lower bounds through `restPair`

`KS u v` says that `v` agrees with `u` on state, path, `wait`, `ctrl_mark` and
`path2`.  CLEAN keeps everything but the path and only deletes paths, so a
pathless pair crosses it unchanged (`T1`).  The later stages leave a pair of
pathless `produce` cells alone except for SIGMOVE's holder validation, which
drops a stray `path2` (`T4`). -/

section Lower
variable {ψ : Nat}

open PPLLAuthResetDrain (av dv)

/-- `v` agrees with `u` on state, path, `wait`, generation colour and `path2`. -/
def KS (u v : AuthState ψ) : Prop :=
  v.core.state = u.core.state ∧ v.core.path = u.core.path ∧ v.core.wait = u.core.wait ∧
  v.ctrl_mark = u.ctrl_mark ∧ v.core.path2 = u.core.path2

theorem KS.refl (u : AuthState ψ) : KS u u := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem KS.trans {u v w : AuthState ψ} (h1 : KS u v) (h2 : KS v w) : KS u w :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
   h2.2.2.2.2.trans h1.2.2.2.2⟩

/-- CLEAN's view: everything `KS` reads except the path, plus the path colour. -/
def cv (u : AuthState ψ) : MainState × Bool × ProvColor × Option Path2Info × ProvColor :=
  (u.core.state, u.core.wait, u.ctrl_mark, u.core.path2, u.path_mark)

syntax "csplit" : tactic
macro_rules
  | `(tactic| csplit) => `(tactic| ((repeat' (first | (dsimp only) | split)) <;>
      simp_all [cv, KS, AuthState.withCore, AuthState.dropP2, AuthState.setState,
        AuthState.lineage]))

theorem genConnectAuth_cv (u : AuthState ψ) :
    cv (genConnectAuth u) = cv u ∧ (genConnectAuth u).core.path = u.core.path := by
  unfold genConnectAuth
  split
  · unfold cleanSigGenConnect; csplit
  · exact ⟨rfl, rfl⟩

theorem step3_cv (nbr mc : Bool) (l r : AuthState ψ) :
    cv (step3Auth nbr mc l r).1 = cv l ∧ cv (step3Auth nbr mc l r).2 = cv r ∧
    (step3Auth nbr mc l r).1.core.path = l.core.path ∧
    (step3Auth nbr mc l r).2.core.path = r.core.path := by
  unfold step3Auth; csplit

theorem step4_cv (nbr mc : Bool) (l r : AuthState ψ) :
    cv (step4Auth nbr mc l r).1 = cv l ∧ cv (step4Auth nbr mc l r).2 = cv r ∧
    (step4Auth nbr mc l r).1.core.path = l.core.path ∧
    (step4Auth nbr mc l r).2.core.path = r.core.path := by
  unfold step4Auth; csplit

theorem step5_cv (hψ : ψ > 0) (l r : AuthState ψ) :
    cv (step5Auth hψ l r).1 = cv l ∧ cv (step5Auth hψ l r).2 = cv r ∧
    (step5Auth hψ l r).1.core.path = l.core.path ∧
    (step5Auth hψ l r).2.core.path = r.core.path := by
  unfold step5Auth; csplit

theorem step6_cv (hψ : ψ > 0) (l r : AuthState ψ) :
    cv (step6Auth hψ l r).1 = cv l ∧ cv (step6Auth hψ l r).2 = cv r ∧
    (step6Auth hψ l r).1.core.path = l.core.path ∧
    (step6Auth hψ l r).2.core.path = r.core.path := by
  unfold step6Auth; csplit

theorem cleanApply_cv (u : AuthState ψ) :
    cv (cleanApplyAuth u) = cv u ∧
    ((cleanApplyAuth u).core.path = u.core.path ∨ (cleanApplyAuth u).core.path = .bot) := by
  unfold cleanApplyAuth; csplit

/-- CLEAN keeps state, `wait`, colour and `path2`, and at most deletes a path. -/
theorem T1_cv (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) :
    cv (T1 hψ c q).1 = cv q.1 ∧ cv (T1 hψ c q).2 = cv q.2 ∧
    ((T1 hψ c q).1.core.path = q.1.core.path ∨ (T1 hψ c q).1.core.path = .bot) ∧
    ((T1 hψ c q).2.core.path = q.2.core.path ∨ (T1 hψ c q).2.core.path = .bot) := by
  obtain ⟨a, b⟩ := q
  unfold T1 cleanSourceAuth
  dsimp only
  have g1 := genConnectAuth_cv a
  have g2 := genConnectAuth_cv b
  generalize genConnectAuth a = a1 at g1 ⊢
  generalize genConnectAuth b = b1 at g2 ⊢
  have s3 := step3_cv c.cleanNbr c.markClean a1 b1
  generalize step3Auth c.cleanNbr c.markClean a1 b1 = q3 at s3 ⊢
  obtain ⟨a3, b3⟩ := q3
  dsimp only at s3 ⊢
  have s4 := step4_cv c.cleanNbr c.markClean a3 b3
  generalize step4Auth c.cleanNbr c.markClean a3 b3 = q4 at s4 ⊢
  obtain ⟨a4, b4⟩ := q4
  dsimp only at s4 ⊢
  have s5 : cv (if isCmd a4.core.path4 = true then (a4, { b4 with core := { b4.core with path4 := none } })
        else step5Auth hψ a4 b4).1 = cv a4 ∧
      cv (if isCmd a4.core.path4 = true then (a4, { b4 with core := { b4.core with path4 := none } })
        else step5Auth hψ a4 b4).2 = cv b4 ∧
      (if isCmd a4.core.path4 = true then (a4, { b4 with core := { b4.core with path4 := none } })
        else step5Auth hψ a4 b4).1.core.path = a4.core.path ∧
      (if isCmd a4.core.path4 = true then (a4, { b4 with core := { b4.core with path4 := none } })
        else step5Auth hψ a4 b4).2.core.path = b4.core.path := by
    split
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact step5_cv hψ a4 b4
  generalize (if isCmd a4.core.path4 = true then (a4, { b4 with core := { b4.core with path4 := none } })
        else step5Auth hψ a4 b4) = q5 at s5 ⊢
  obtain ⟨a5, b5⟩ := q5
  dsimp only at s5 ⊢
  have s6 : cv (if isCmd b5.core.path5 = true then ({ a5 with core := { a5.core with path5 := none } }, b5)
        else step6Auth hψ a5 b5).1 = cv a5 ∧
      cv (if isCmd b5.core.path5 = true then ({ a5 with core := { a5.core with path5 := none } }, b5)
        else step6Auth hψ a5 b5).2 = cv b5 ∧
      (if isCmd b5.core.path5 = true then ({ a5 with core := { a5.core with path5 := none } }, b5)
        else step6Auth hψ a5 b5).1.core.path = a5.core.path ∧
      (if isCmd b5.core.path5 = true then ({ a5 with core := { a5.core with path5 := none } }, b5)
        else step6Auth hψ a5 b5).2.core.path = b5.core.path := by
    split
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact step6_cv hψ a5 b5
  generalize (if isCmd b5.core.path5 = true then ({ a5 with core := { a5.core with path5 := none } }, b5)
        else step6Auth hψ a5 b5) = q6 at s6 ⊢
  obtain ⟨a6, b6⟩ := q6
  dsimp only at s6 ⊢
  have c1 := cleanApply_cv a6
  have c2 := cleanApply_cv b6
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [c1.1, s6.1, s5.1, s4.1, s3.1, g1.1]
  · rw [c2.1, s6.2.1, s5.2.1, s4.2.1, s3.2.1, g2.1]
  · rcases c1.2 with h | h
    · left; rw [h, s6.2.2.1, s5.2.2.1, s4.2.2.1, s3.2.2.1, g1.2]
    · right; exact h
  · rcases c2.2 with h | h
    · left; rw [h, s6.2.2.2, s5.2.2.2, s4.2.2.2, s3.2.2.2, g2.2]
    · right; exact h

theorem KS_of_cv {u v : AuthState ψ} (h1 : cv v = cv u) (h2 : v.core.path = u.core.path) : KS u v := by
  simp only [cv, Prod.mk.injEq] at h1
  exact ⟨h1.1, h2, h1.2.1, h1.2.2.1, h1.2.2.2.1⟩

/-! ### A pair of pathless producers crosses the stages after CLEAN -/

theorem T2_id (hψ : ψ > 0) (q : Pair ψ) (h : q.2.core.state ≠ .done) : T2 hψ q = q := by
  obtain ⟨a, b⟩ := q
  simp only at h
  simp [T2, lift2Life, releaseSource, h]

theorem T3_id (hψ : ψ > 0) (q : Pair ψ) (h : q.2.core.state ≠ .eliminate_signal) : T3 hψ q = q := by
  obtain ⟨a, b⟩ := q
  simp only at h
  simp [T3, lift2, eliminateSig, h]

theorem validate_bot (l r : AuthState ψ) (hl : l.core.path = .bot) (hr : r.core.path = .bot) :
    validateCheck l r = (l, r) := by
  simp [validateCheck, headBad, isHead, aligned, hl, hr]

theorem sanitize_fields (u : AuthState ψ) :
    (sanitizeP2 u).core.state = u.core.state ∧ (sanitizeP2 u).core.path = u.core.path ∧
    (sanitizeP2 u).core.wait = u.core.wait ∧ (sanitizeP2 u).ctrl_mark = u.ctrl_mark ∧
    (sanitizeP2 u).core.leader = u.core.leader ∧ (sanitizeP2 u).core.label = u.core.label ∧
    (sanitizeP2 u).core.reset_cmd = u.core.reset_cmd ∧ (sanitizeP2 u).path_mark = u.path_mark := by
  unfold sanitizeP2; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sanitize_path2_bot (u : AuthState ψ) (h : u.core.path = .bot) :
    (sanitizeP2 u).core.path2 = none := by
  unfold sanitizeP2 p2Valid
  cases hp : u.core.path2 with
  | none => simp [hp]
  | some t => simp [hp, AuthState.hasPath, h, AuthState.dropP2]

theorem step1_bot (l r : AuthState ψ) (hl : l.core.path = .bot) : step1Auth l r = (l, r) := by
  simp [step1Auth, hl]

theorem moveTokens_none (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (hl : l.core.path2 = none)
    (hr : r.core.path2 = none) : moveTokensAuth c l r = (l, r) := by
  simp [moveTokensAuth, hl, hr]

theorem leaderWall_id (l r : AuthState ψ) (hl : l.core.leader = false) (hr : r.core.leader = false) :
    leaderWallAuth l r = (l, r) := by
  simp [leaderWallAuth, hl, hr]

theorem applyControl_none (hψ : ψ > 0) (u : AuthState ψ) (h : u.core.path2 = none) :
    applyControlAuth hψ u = u := by
  simp [applyControlAuth, h]

/-- SIGMOVE on a leaderless pair of pathless cells only drops stray `path2`s. -/
theorem T4_bot (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ)
    (h1 : q.1.core.path = .bot) (h2 : q.2.core.path = .bot)
    (k1 : q.1.core.leader = false) (k2 : q.2.core.leader = false)
    (s1 : q.1.core.state ≠ .done) (s2 : q.1.core.state ≠ .CHECK_ready) :
    T4 hψ c q = (sanitizeP2 q.1, sanitizeP2 q.2) := by
  obtain ⟨a, b⟩ := q
  simp only at h1 h2 k1 k2 s1 s2
  have fa := sanitize_fields a
  have fb := sanitize_fields b
  have na := sanitize_path2_bot a h1
  have nb := sanitize_path2_bot b h2
  unfold T4 moveSourceAuth
  simp only [k1, k2, Bool.false_eq_true, false_or, false_and, ite_false]
  rw [validate_bot a b h1 h2]
  dsimp only
  generalize sanitizeP2 a = a' at fa na ⊢
  generalize sanitizeP2 b = b' at fb nb ⊢
  obtain ⟨fa1, fa2, -, -, fa5, -, -, -⟩ := fa
  obtain ⟨fb1, fb2, -, -, fb5, -, -, -⟩ := fb
  have e1 : (if a'.st = MainState.done then (a', b') else step1Auth a' b') = (a', b') := by
    rw [if_neg (by show ¬ a'.core.state = .done; rw [fa1]; exact s1), step1_bot a' b' (fa2.trans h1)]
  simp only [e1, moveTokens_none c a' b' na nb, leaderWall_id a' b' (fa5.trans k1) (fb5.trans k2),
    applyControl_none hψ a' na, applyControl_none hψ b' nb]
  rw [if_neg (by simp only [AuthState.st, fa1]; intro h; exact s2 h.2.2)]

theorem T5_bot (q : Pair ψ) (h1 : q.1.core.path = .bot) (h2 : q.2.core.path = .bot) : T5 q = q := by
  obtain ⟨a, b⟩ := q
  simp only at h1 h2
  simp [T5, liftLife, dropStale, h1, h2]

theorem T6_id (q : Pair ψ) (k1 : q.1.core.leader = false) (r1 : q.1.core.reset_cmd = false)
    (r2 : q.2.core.reset_cmd = false) : T6 q = q := by
  obtain ⟨a, b⟩ := q
  simp only at k1 r1 r2
  simp [T6, preCheckResetAuth, k1, r1, r2]

theorem normalizeReady_produce_bot (u : AgentState ψ) (hs : u.state = .produce) (hp : u.path = .bot) :
    normalizeReady u = u := by
  simp [normalizeReady, normalizeOrphan, normalizeCarrier, releaseCongest, hs, hp]

theorem T7_Ph (q : Pair ψ) (s1 : q.1.core.state = .produce) (s2 : q.2.core.state = .produce)
    (h1 : q.1.core.path = .bot) (h2 : q.2.core.path = .bot) : T7 q = q := by
  obtain ⟨a, b⟩ := q
  simp only at s1 s2 h1 h2
  simp [T7, liftLife, normalizeReady_produce_bot _ s1 h1, normalizeReady_produce_bot _ s2 h2]

theorem readyAuth_produce_bot (u : AuthState ψ) (hs : u.core.state = .produce)
    (hp : u.core.path = .bot) : readyAuth u = u := by
  simp [readyAuth, checkSigSetReadyGuarded, controlPending, checkSigSetReady, AuthState.st,
    waveState, hs, hp]

theorem T8_Ph (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ)
    (s1 : q.1.core.state = .produce) (s2 : q.2.core.state = .produce)
    (h1 : q.1.core.path = .bot) (h2 : q.2.core.path = .bot) : T8 hψ c q = q := by
  obtain ⟨a, b⟩ := q
  simp only at s1 s2 h1 h2
  simp [T8, checkSourceAuth, validate_bot a b h1 h2, readyAuth_produce_bot a s1 h1,
    readyAuth_produce_bot b s2 h2, certPred, isHead, aligned, checkSigCheckL, AuthState.withCore,
    AuthState.st, h1, h2, s1, s2]

theorem T9_Ph (hψ : ψ > 0) (q : Pair ψ) (s1 : q.1.core.state = .produce)
    (s2 : q.2.core.state = .produce) (hT : q.2.core.label.val ≠ ψ - 1) :
    KS q.1 (T9 hψ q).1 ∧ KS q.2 (T9 hψ q).2 := by
  obtain ⟨a, b⟩ := q
  simp only at s1 s2 hT
  unfold T9 disappearAuth
  simp only [AuthState.st, s2, lift2]
  unfold disappearStartL disappearCarry
  have hb : ¬ b.core.label = ⟨ψ - 1, by omega⟩ := fun h => hT (congrArg Fin.val h)
  (repeat' (first | (dsimp only) | split)) <;> simp_all [KS]

theorem normalizeRepair_produce_bot (u : AgentState ψ) (hs : u.state = .produce)
    (hp : u.path = .bot) : normalizeCarrier (normalizeOrphan u) = u := by
  simp [normalizeOrphan, normalizeCarrier, releaseCongest, hs, hp]

theorem T10_Ph (q : Pair ψ) (s1 : q.1.core.state = .produce) (s2 : q.2.core.state = .produce)
    (h1 : q.1.core.path = .bot) (h2 : q.2.core.path = .bot) : T10 q = q := by
  obtain ⟨a, b⟩ := q
  simp only at s1 s2 h1 h2
  unfold T10 repairAuth
  simp only [liftLife, normalizeRepair_produce_bot _ s1 h1, normalizeRepair_produce_bot _ s2 h2,
    ne_eq, not_true_eq_false, false_and, ite_false]
  simp [lift2Life, releaseReadySuffix, ackTailAuth, lift2, ackTail, h1, h2]

theorem T11_Ph (κ : Nat) (q : Pair ψ) (s1 : q.1.core.state = .produce) (s2 : q.2.core.state = .produce)
    (h1 : q.1.core.path = .bot) (h2 : q.2.core.path = .bot)
    (p1 : q.1.core.path2 = none) (p2 : q.2.core.path2 = none) : T11 κ q = q := by
  obtain ⟨a, b⟩ := q
  simp only at s1 s2 h1 h2 p1 p2
  simp [T11, compareLifecycleAuth, AuthState.st, maintainAuth, completeWaveAuth, waveAuth,
    lift2, dropStray, landBackwardAuth, landForwardAuth, lockedState, waveState, s1, s2, h1, h2,
    p1, p2]

/-- G4: a leaderless, reset-free pair of pathless producers whose responder is
not the terminal leaves `restPair` as a pair of pathless producers, with
colours and `wait` kept and no `path2`. -/
theorem rest_Ph (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ)
    (s1 : q.1.core.state = .produce) (s2 : q.2.core.state = .produce)
    (h1 : q.1.core.path = .bot) (h2 : q.2.core.path = .bot)
    (k1 : q.1.core.leader = false) (k2 : q.2.core.leader = false)
    (r1 : q.1.core.reset_cmd = false) (r2 : q.2.core.reset_cmd = false)
    (hT : q.2.core.label.val ≠ ψ - 1) :
    (restPair hψ κ c q).1.core.state = .produce ∧ (restPair hψ κ c q).1.core.path = .bot ∧
    (restPair hψ κ c q).1.core.path2 = none ∧ (restPair hψ κ c q).1.core.wait = q.1.core.wait ∧
    (restPair hψ κ c q).1.ctrl_mark = q.1.ctrl_mark ∧
    (restPair hψ κ c q).2.core.state = .produce ∧ (restPair hψ κ c q).2.core.path = .bot ∧
    (restPair hψ κ c q).2.core.path2 = none ∧ (restPair hψ κ c q).2.core.wait = q.2.core.wait ∧
    (restPair hψ κ c q).2.ctrl_mark = q.2.ctrl_mark := by
  have t1 := T1_cv hψ c q
  have a1 := T1_pa hψ c q
  unfold restPair
  generalize T1 hψ c q = q1 at t1 a1 ⊢
  obtain ⟨c1, c2, p1, p2⟩ := t1
  simp only [cv, Prod.mk.injEq] at c1 c2
  have hb1 : q1.1.core.path = .bot := by rcases p1 with h | h <;> rw [h]; exact h1
  have hb2 : q1.2.core.path = .bot := by rcases p2 with h | h <;> rw [h]; exact h2
  have lab : q1.2.core.label.val ≠ ψ - 1 := by rw [av_label, a1.2, ← av_label]; exact hT
  have lk1 : q1.1.core.leader = false := by rw [av_leader, a1.1, ← av_leader]; exact k1
  have lk2 : q1.2.core.leader = false := by rw [av_leader, a1.2, ← av_leader]; exact k2
  have rs1 : q1.1.core.reset_cmd = false := by rw [av_reset, a1.1, ← av_reset]; exact r1
  have rs2 : q1.2.core.reset_cmd = false := by rw [av_reset, a1.2, ← av_reset]; exact r2
  rw [T2_id hψ q1 (by rw [c2.1, s2]; nofun)]
  unfold restLo
  rw [T3_id hψ q1 (by rw [c2.1, s2]; nofun)]
  rw [T4_bot hψ c q1 hb1 hb2 lk1 lk2 (by rw [c1.1, s1]; nofun) (by rw [c1.1, s1]; nofun)]
  have f1 := sanitize_fields q1.1
  have f2 := sanitize_fields q1.2
  have n1 := sanitize_path2_bot q1.1 hb1
  have n2 := sanitize_path2_bot q1.2 hb2
  generalize sanitizeP2 q1.1 = x1 at f1 n1 ⊢
  generalize sanitizeP2 q1.2 = x2 at f2 n2 ⊢
  obtain ⟨g1, g2, g3, g4, g5, -, g7, -⟩ := f1
  obtain ⟨j1, j2, j3, j4, j5, j6, j7, -⟩ := f2
  have xs1 : x1.core.state = .produce := by rw [g1, c1.1, s1]
  have xs2 : x2.core.state = .produce := by rw [j1, c2.1, s2]
  have xb1 : x1.core.path = .bot := g2.trans hb1
  have xb2 : x2.core.path = .bot := j2.trans hb2
  rw [T5_bot (x1, x2) xb1 xb2, T6_id (x1, x2) (g5.trans lk1) (g7.trans rs1) (j7.trans rs2),
    T7_Ph (x1, x2) xs1 xs2 xb1 xb2]
  unfold restHi
  rw [T8_Ph hψ c (x1, x2) xs1 xs2 xb1 xb2]
  have t9 := T9_Ph hψ (x1, x2) xs1 xs2 (by rw [j6]; exact lab)
  generalize T9 hψ (x1, x2) = q9 at t9 ⊢
  obtain ⟨⟨u1, u2, u3, u4, u5⟩, ⟨v1, v2, v3, v4, v5⟩⟩ := t9
  simp only at u1 u2 u3 u4 u5 v1 v2 v3 v4 v5
  rw [T10_Ph q9 (u1.trans xs1) (v1.trans xs2) (u2.trans xb1) (v2.trans xb2),
    T11_Ph κ q9 (u1.trans xs1) (v1.trans xs2) (u2.trans xb1) (v2.trans xb2) (u5.trans n1)
      (v5.trans n2)]
  exact ⟨u1.trans xs1, u2.trans xb1, u5.trans n1, u3.trans (g3.trans c1.2.1), u4.trans (g4.trans c1.2.2.1),
    v1.trans xs2, v2.trans xb2, v5.trans n2, v3.trans (j3.trans c2.2.1), v4.trans (j4.trans c2.2.2.1)⟩

/-! ### A `done` chain cell crosses the stages after GENSIG (REST2)

The initiator is an aligned `done` cell with path label `k ∉ {0, ψ-1}` and no
`path2`; the responder carries the next path label with the same path colour
and has just been released to `depart`.  CLEAN's connection records then agree
on both sides (CS), and no later stage touches the initiator. -/

theorem genConnect_link (u : AuthState ψ) (p x : Nat) (h : u.core.path = .some p x) :
    (genConnectAuth u).core.path = .some p x ∧ (genConnectAuth u).path_mark = u.path_mark ∧
    (p ≠ 0 → (genConnectAuth u).core.path4 = some (Int.ofNat p, 1) ∧
      (genConnectAuth u).path4_mark = u.path_mark) ∧
    (p ≠ ψ - 1 → (genConnectAuth u).core.path5 = some (Int.ofNat p, 1) ∧
      (genConnectAuth u).path5_mark = u.path_mark) := by
  simp only [genConnectAuth, h, cleanSigGenConnect]
  refine ⟨?_, ?_, ?_, ?_⟩
  · (repeat' (first | (dsimp only) | split)) <;> simp_all
  · (repeat' (first | (dsimp only) | split)) <;> simp_all
  · intro h0
    (repeat' (first | (dsimp only) | split)) <;> simp_all
  · intro h1
    (repeat' (first | (dsimp only) | split)) <;> simp_all

theorem step3_link (nbr mc : Bool) (l r : AuthState ψ) (k x : Nat)
    (hr : r.core.path4 = some (Int.ofNat (k + 1), 1)) (hl : l.core.path = .some k x)
    (hm : r.path4_mark = l.path_mark) :
    step3Auth nbr mc l r = (l, { r with core := { r.core with path4 := none } }) := by
  have hne : (k : Int) + 1 ≠ -1 := by omega
  simp [step3Auth, hr, hl, hm, hne]

theorem step4_link (nbr mc : Bool) (l r : AuthState ψ) (k x : Nat)
    (hl : l.core.path5 = some (Int.ofNat k, 1)) (hr : r.core.path = .some (k + 1) x)
    (hm : l.path5_mark = r.path_mark) :
    step4Auth nbr mc l r = ({ l with core := { l.core with path5 := none } }, r) := by
  have hne : (k : Int) ≠ -1 := by omega
  simp [step4Auth, hr, hl, hm, hne]

theorem step5_none (hψ : ψ > 0) (l r : AuthState ψ) (h : r.core.path4 = none) :
    step5Auth hψ l r = (l, r) := by
  simp [step5Auth, h]

theorem step6_none (hψ : ψ > 0) (l r : AuthState ψ) (h : l.core.path5 = none) :
    step6Auth hψ l r = (l, r) := by
  simp [step6Auth, h]

theorem cleanApply_keep (u : AuthState ψ) (p x k : Nat) (h : u.core.path = .some p x)
    (h4 : u.core.path4 = some (Int.ofNat k, 1)) (h5 : u.core.path5 = none) :
    (cleanApplyAuth u).core.path = .some p x := by
  have hne : (k : Int) ≠ -1 := by omega
  simp [cleanApplyAuth, h, h4, h5, hne]

/-- CS: CLEAN keeps a consistent chain link intact at the initiator. -/
theorem T1_chain (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) (k ba bb : Nat)
    (ha : q.1.core.path = .some k ba) (hb : q.2.core.path = .some (k + 1) bb)
    (hk0 : k ≠ 0) (hkT : k ≠ ψ - 1) (hm : q.2.path_mark = q.1.path_mark) :
    (T1 hψ c q).1.core.path = .some k ba := by
  obtain ⟨a, b⟩ := q
  simp only at ha hb hm
  obtain ⟨ga1, ga2, ga3, ga4⟩ := genConnect_link a k ba ha
  obtain ⟨gb1, gb2, gb3, -⟩ := genConnect_link b (k + 1) bb hb
  obtain ⟨ga5, ga6⟩ := ga3 hk0
  obtain ⟨ga7, ga8⟩ := ga4 hkT
  obtain ⟨gb5, gb6⟩ := gb3 (by omega)
  unfold T1 cleanSourceAuth
  dsimp only
  generalize genConnectAuth a = a1 at ga1 ga2 ga5 ga6 ga7 ga8 ⊢
  generalize genConnectAuth b = b1 at gb1 gb2 gb5 gb6 ⊢
  have s3 := step3_link c.cleanNbr c.markClean a1 b1 k ba gb5 ga1 (by rw [gb6, ga2, hm])
  generalize step3Auth c.cleanNbr c.markClean a1 b1 = q3 at s3 ⊢
  obtain ⟨a3, b3⟩ := q3
  simp only [Prod.mk.injEq] at s3
  obtain ⟨e3, f3⟩ := s3
  subst e3
  have b3p : b3.core.path = .some (k + 1) bb := by rw [f3]; exact gb1
  have b3m : b3.path_mark = b1.path_mark := by rw [f3]
  have b3n : b3.core.path4 = none := by rw [f3]
  clear f3
  dsimp only
  have s4 := step4_link c.cleanNbr c.markClean a3 b3 k bb ga7 b3p (by rw [ga8, b3m, gb2, hm])
  generalize step4Auth c.cleanNbr c.markClean a3 b3 = q4 at s4 ⊢
  obtain ⟨a4, b4⟩ := q4
  simp only [Prod.mk.injEq] at s4
  obtain ⟨e4, f4⟩ := s4
  subst f4
  have a4p : a4.core.path = .some k ba := by rw [e4]; exact ga1
  have a4c : a4.core.path4 = some (Int.ofNat k, 1) := by rw [e4]; exact ga5
  have a4f : a4.core.path5 = none := by rw [e4]
  clear e4
  dsimp only
  have hne0 : (k : Int) ≠ -1 := by omega
  have s5 : (if isCmd a4.core.path4 = true then (a4, { b4 with core := { b4.core with path4 := none } })
      else step5Auth hψ a4 b4) = (a4, b4) := by
    rw [if_neg (by simp [a4c, isCmd, hne0]), step5_none hψ a4 b4 b3n]
  rw [s5]
  dsimp only
  have s6 : (if isCmd b4.core.path5 = true then ({ a4 with core := { a4.core with path5 := none } }, b4)
      else step6Auth hψ a4 b4).1 = a4 := by
    split
    · rename_i h
      cases a4 with
      | mk core pm cm ps p2m p4m p5m =>
        cases core
        simp only at a4f
        simp [a4f]
    · rw [step6_none hψ a4 b4 a4f]
  rw [s6]
  exact cleanApply_keep a4 k ba k a4p a4c a4f

theorem validate_quiet (l r : AuthState ψ) (hl : checkState l = false) (hr : checkState r = false) :
    validateCheck l r = (l, r) := by
  have hv : verdict r = false := by
    unfold checkState at hr; simp only [Bool.or_eq_false_iff] at hr; exact hr.2
  simp [validateCheck, headBad, hl, hr, hv]

theorem sanitize_none (u : AuthState ψ) (h : u.core.path2 = none) : sanitizeP2 u = u := by
  simp [sanitizeP2, p2Valid, h]

/-- SIGMOVE leaves a leaderless token-free pair alone when the initiator is `done`. -/
theorem T4_quiet (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ)
    (k1 : q.1.core.leader = false) (k2 : q.2.core.leader = false)
    (p1 : q.1.core.path2 = none) (p2 : q.2.core.path2 = none)
    (c1 : checkState q.1 = false) (c2 : checkState q.2 = false) (d : q.1.core.state = .done) :
    T4 hψ c q = q := by
  obtain ⟨a, b⟩ := q
  simp only at k1 k2 p1 p2 c1 c2 d
  unfold T4 moveSourceAuth
  simp only [k1, k2, Bool.false_eq_true, false_or, false_and, ite_false]
  rw [validate_quiet a b c1 c2]
  dsimp only
  rw [sanitize_none a p1, sanitize_none b p2]
  have e1 : (if a.st = MainState.done then (a, b) else step1Auth a b) = (a, b) := if_pos d
  simp only [e1, moveTokens_none c a b p1 p2, leaderWall_id a b k1 k2,
    applyControl_none hψ a p1, applyControl_none hψ b p2]
  rw [if_neg (by simp only [AuthState.st, d]; intro h; cases h.2.2)]

theorem T5_fst (q : Pair ψ) (h : aligned q.1.core = true) : (T5 q).1 = q.1 := by
  obtain ⟨a, b⟩ := q
  simp only at h
  simp [T5, liftLife, dropStale, h]

theorem T6_fst (q : Pair ψ) (k1 : q.1.core.leader = false) (r1 : q.1.core.reset_cmd = false) :
    (T6 q).1 = q.1 := by
  obtain ⟨a, b⟩ := q
  simp only at k1 r1
  simp [T6, preCheckResetAuth, k1, r1]

theorem normalize_done_aligned (u : AgentState ψ) (d : u.state = .done) (k x : Nat)
    (hp : u.path = .some k x) (hl : u.label.val = k) :
    normalizeCarrier (normalizeOrphan u) = u ∧ normalizeReady u = u := by
  have hne : ¬ (k ≠ u.label.val) := by omega
  constructor
  · simp [normalizeOrphan, normalizeCarrier, d, hp, hl]
  · simp [normalizeReady, normalizeOrphan, normalizeCarrier, d, hp, hl, aligned]

theorem T7_fst (q : Pair ψ) (d : q.1.core.state = .done) (k x : Nat)
    (hp : q.1.core.path = .some k x) (hl : q.1.core.label.val = k) : (T7 q).1 = q.1 := by
  obtain ⟨a, b⟩ := q
  simp only at d hp hl
  simp [T7, liftLife, (normalize_done_aligned a.core d k x hp hl).2]

theorem T8_fst (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) (d : q.1.core.state = .done)
    (k x : Nat) (hp : q.1.core.path = .some (k + 1) x) (hl : q.1.core.label.val = k + 1) :
    (T8 hψ c q).1 = q.1 := by
  obtain ⟨a, b⟩ := q
  simp only at d hp hl
  have hh : isHead a = false := by simp [isHead, hl]
  have hr : readyAuth a = a := by simp [readyAuth, AuthState.st, d]
  unfold T8
  rw [checkSource_eq]
  dsimp only
  have e1 : (validateCheck a b).1 = a := by simp [validateCheck, headBad, hh]
  generalize validateCheck a b = v at e1 ⊢
  obtain ⟨v1, v2⟩ := v
  simp only at e1
  subst e1
  have e2 : (csA c v1 v2).1 = v1 := by
    unfold csA; dsimp only; split
    · exact hr
    · rfl
  generalize csA c v1 v2 = w at e2 ⊢
  obtain ⟨w1, w2⟩ := w
  simp only at e2
  subst e2
  dsimp only
  have e3 : csB w1 w2 = w1 := by
    unfold csB; rw [if_neg (by simp [AuthState.st, d])]
  rw [e3]
  have e4 : csC hψ w1 = w1 := by
    unfold csC checkSigCheckL; simp [hp, AuthState.withCore]
  rw [e4]
  have e5 : csF w1 = w1 := by unfold csF; simp [hh]
  unfold csH
  dsimp only
  split <;> exact e5

theorem T9_fst (hψ : ψ > 0) (q : Pair ψ) (d : q.1.core.state ≠ .toss) :
    KS q.1 (T9 hψ q).1 ∧ (T9 hψ q).1.path_mark = q.1.path_mark := by
  obtain ⟨a, b⟩ := q
  simp only at d
  unfold T9 disappearAuth
  simp only [lift2]
  unfold disappearStartL disappearCarry
  (repeat' (first | (dsimp only) | split)) <;> simp_all [KS]

theorem T10_fst (q : Pair ψ) (d : q.1.core.state = .done) (k x : Nat)
    (hp : q.1.core.path = .some k x) (hl : q.1.core.label.val = k) : (T10 q).1 = q.1 := by
  obtain ⟨a, b⟩ := q
  simp only at d hp hl
  unfold T10 repairAuth
  simp only [liftLife, (normalize_done_aligned a.core d k x hp hl).1]
  simp only [ne_eq, not_true_eq_false, false_and, ite_false]
  generalize liftLife (fun u => normalizeCarrier (normalizeOrphan u)) b = b1
  unfold lift2Life releaseReadySuffix
  dsimp only
  (repeat' (first | (dsimp only) | split)) <;> simp_all [ackTailAuth, lift2, ackTail]
  all_goals (repeat' (first | (dsimp only) | split)) <;> simp_all

theorem T11_fst (κ : Nat) (q : Pair ψ) (d : q.1.core.state = .done) (k x : Nat)
    (hp : q.1.core.path = .some k x) (hkT : k ≠ ψ - 1) (p1 : q.1.core.path2 = none) :
    (T11 κ q).1 = q.1 := by
  obtain ⟨a, b⟩ := q
  simp only at d hp p1
  unfold T11
  rw [compare_eq]
  have e0 : cmp0 a = a := by unfold cmp0; simp [hp]
  rw [e0]
  unfold cmpTail
  have e1 : (maintainAuth a b).1 = a := by
    unfold maintainAuth; simp only [hp]
    (repeat' (first | (dsimp only) | split)) <;> simp_all [AuthState.st, lockedState]
  generalize maintainAuth a b = m at e1 ⊢
  obtain ⟨m1, m2⟩ := m
  simp only at e1
  subst e1
  dsimp only
  have e2 : (completeWaveAuth m1 m2).1 = m1 := by
    unfold completeWaveAuth; simp only [hp]
    (repeat' (first | (dsimp only) | split)) <;> simp_all [AuthState.st]
  generalize completeWaveAuth m1 m2 = w at e2 ⊢
  obtain ⟨w1, w2⟩ := w
  simp only at e2
  subst e2
  dsimp only
  have e3 : (waveAuth w1 w2).1 = w1 := by
    unfold waveAuth; simp only [hp]
    (repeat' (first | (dsimp only) | split)) <;> simp_all [AuthState.st, AuthState.setState]
  generalize waveAuth w1 w2 = z at e3 ⊢
  obtain ⟨z1, z2⟩ := z
  simp only at e3
  subst e3
  dsimp only
  simp [lift2, dropStray, landBackwardAuth, p1]

/-- Non-generation state. -/
def NG (u : AuthState ψ) : Prop := u.core.state ≠ .produce ∧ u.core.state ≠ .done

theorem MonoA.ng {a b : AuthState ψ} (h : MonoA a b) (ha : NG a) : NG b :=
  ⟨fun hb => ha.1 (h.1 hb), fun hb => ha.2 (h.2.1 hb)⟩

/-- REST2: a `done` chain link crosses the rest of the row.  The initiator keeps
state, path, colours and its empty `path2`; the released responder stays
outside the generation. -/
theorem rest_chain (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ) (k ba bb : Nat)
    (d : q.1.core.state = .done) (ha : q.1.core.path = .some (k + 1) ba)
    (hl : q.1.core.label.val = k + 1) (hkT : k + 1 ≠ ψ - 1) (p1 : q.1.core.path2 = none)
    (k1 : q.1.core.leader = false) (r1 : q.1.core.reset_cmd = false)
    (hb : q.2.core.path = .some (k + 2) bb) (hm : q.2.path_mark = q.1.path_mark)
    (p2 : q.2.core.path2 = none) (dep : q.2.core.state = .depart) (k2 : q.2.core.leader = false) :
    (restPair hψ κ c q).1.core.state = .done ∧ (restPair hψ κ c q).1.core.path = .some (k + 1) ba ∧
    (restPair hψ κ c q).1.core.path2 = none ∧ (restPair hψ κ c q).1.ctrl_mark = q.1.ctrl_mark ∧
    (restPair hψ κ c q).1.path_mark = q.1.path_mark ∧ NG (restPair hψ κ c q).2 := by
  have hng : NG (restPair hψ κ c q).2 :=
    (restPair_pm hψ κ c q).2.ng ⟨by rw [dep]; nofun, by rw [dep]; nofun⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hng⟩ <;> clear hng
  all_goals
    have t1 := T1_cv hψ c q
    have t2 := T1_chain hψ c q (k + 1) ba bb ha hb (by omega) hkT hm
    have a1 := T1_pa hψ c q
    unfold restPair
    generalize T1 hψ c q = q1 at t1 t2 a1 ⊢
    obtain ⟨c1, c2, -, -⟩ := t1
    simp only [cv, Prod.mk.injEq] at c1 c2
    have lk1 : q1.1.core.leader = false := by rw [av_leader, a1.1, ← av_leader]; exact k1
    have lk2 : q1.2.core.leader = false := by rw [av_leader, a1.2, ← av_leader]; exact k2
    have rs1 : q1.1.core.reset_cmd = false := by rw [av_reset, a1.1, ← av_reset]; exact r1
    have lb1 : q1.1.core.label.val = k + 1 := by rw [av_label, a1.1, ← av_label]; exact hl
    have d1 : q1.1.core.state = .done := c1.1.trans d
    have dp : q1.2.core.state = .depart := c2.1.trans dep
    rw [T2_id hψ q1 (by rw [dp]; nofun)]
    unfold restLo
    rw [T3_id hψ q1 (by rw [dp]; nofun)]
    rw [T4_quiet hψ c q1 lk1 lk2 (c1.2.2.2.1.trans p1) (c2.2.2.2.1.trans p2)
      (by simp [checkState, verdict, AuthState.st, d1]) (by simp [checkState, verdict, AuthState.st, dp]) d1]
    have al : aligned q1.1.core = true := by simp [aligned, t2, lb1]
    have x5 : (T5 q1).1 = q1.1 := T5_fst q1 al
    have x6 : (T6 (T5 q1)).1 = q1.1 := by
      rw [T6_fst _ (by rw [x5]; exact lk1) (by rw [x5]; exact rs1), x5]
    have x7 : (T7 (T6 (T5 q1))).1 = q1.1 := by
      rw [T7_fst _ (by rw [x6]; exact d1) (k + 1) ba (by rw [x6]; exact t2) (by rw [x6]; exact lb1), x6]
    generalize T7 (T6 (T5 q1)) = q7 at x7 ⊢
    unfold restHi
    have x8 : (T8 hψ c q7).1 = q1.1 := by
      rw [T8_fst hψ c q7 (by rw [x7]; exact d1) k ba (by rw [x7]; exact t2) (by rw [x7]; exact lb1), x7]
    generalize T8 hψ c q7 = q8 at x8 ⊢
    have x9 := T9_fst hψ q8 (by rw [x8, d1]; nofun)
    have a9 := (PPLLAuthResetDrain.disappear_av hψ q8.1 q8.2).1
    change av (T9 hψ q8).1 = av q8.1 at a9
    generalize T9 hψ q8 = q9 at x9 a9 ⊢
    obtain ⟨⟨u1, u2, -, u4, u5⟩, u6⟩ := x9
    rw [x8] at u1 u2 u4 u5 u6 a9
    have lb9 : q9.1.core.label.val = k + 1 := by rw [av_label, a9, ← av_label]; exact lb1
    have x10 : (T10 q9).1 = q9.1 := T10_fst q9 (u1.trans d1) (k + 1) ba (u2.trans t2) lb9
    generalize T10 q9 = q10 at x10 ⊢
    have x11 : (T11 κ q10).1 = q10.1 := by
      apply T11_fst κ q10 (by rw [x10, u1, d1]) (k + 1) ba (by rw [x10, u2, t2]) hkT
      rw [x10, u5, c1.2.2.2.1, p1]
    rw [x11, x10]
  · rw [u1, d1]
  · rw [u2, t2]
  · rw [u5, c1.2.2.2.1, p1]
  · rw [u4, c1.2.2.1]
  · rw [u6, c1.2.2.2.2]

/-! ### The release of a `done` successor (`releaseSource`) -/

theorem T2_spec (hψ : ψ > 0) (q : Pair ψ) :
    (T2 hψ q).1.core.state = q.1.core.state ∧
    ((T2 hψ q).2.core.state = .done →
      q.2.core.state = .done ∧
      (q.2.core.label.val ≠ 0 → q.1.core.label.val + 1 = q.2.core.label.val →
        q.1.core.state = .produce ∨ q.1.core.state = .done)) ∧
    (q.2.core.state = .done → q.2.core.label.val ≠ 0 → q.1.core.label.val + 1 = q.2.core.label.val →
      q.1.core.state ≠ .produce → q.1.core.state ≠ .done → (T2 hψ q).2.core.state = .depart) := by
  obtain ⟨a, b⟩ := q
  unfold T2 lift2Life releaseSource
  dsimp only
  by_cases hc : b.core.state = .done ∧ b.core.label ≠ ⟨0, hψ⟩ ∧
      a.core.label.val + 1 = b.core.label.val ∧ a.core.state ≠ .produce ∧ a.core.state ≠ .done
  · rw [if_pos hc]
    refine ⟨?_, ?_, ?_⟩
    · split <;> rfl
    · intro h; split at h <;> simp at h
    · intro _ _ _ _ _; split <;> rfl
  · rw [if_neg hc]
    refine ⟨?_, ?_, ?_⟩
    · split <;> rfl
    · intro h
      have h' : b.core.state = .done := by split at h <;> simp_all
      refine ⟨h', fun h0 hl => ?_⟩
      by_cases p : a.core.state = .produce
      · exact Or.inl p
      · by_cases p' : a.core.state = .done
        · exact Or.inr p'
        · exact absurd ⟨h', fun e => h0 (congrArg Fin.val e), hl, p, p'⟩ hc
    · intro h1 h2 h3 h4 h5
      exact absurd ⟨h1, fun e => h2 (congrArg Fin.val e), h3, h4, h5⟩ hc

/-- RL: a non-generation initiator releases its `done` successor; nothing of
the pair is left in the generation. -/
theorem rest_release (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ) (h1 : NG q.1)
    (h2 : q.2.core.state = .done) (hlab : q.1.core.label.val + 1 = q.2.core.label.val)
    (h0 : q.2.core.label.val ≠ 0) :
    NG (restPair hψ κ c q).1 ∧ NG (restPair hψ κ c q).2 := by
  have t1 := T1_cv hψ c q
  have a1 := T1_pa hψ c q
  obtain ⟨c1, c2, -, -⟩ := t1
  simp only [cv, Prod.mk.injEq] at c1 c2
  have lb1 : (T1 hψ c q).1.core.label.val = q.1.core.label.val := by rw [av_label, a1.1, ← av_label]
  have lb2 : (T1 hψ c q).2.core.label.val = q.2.core.label.val := by rw [av_label, a1.2, ← av_label]
  obtain ⟨s1, -, s3⟩ := T2_spec hψ (T1 hψ c q)
  have n1 : NG (T2 hψ (T1 hψ c q)).1 := by
    unfold NG; rw [s1, c1.1]; exact h1
  have n2 : NG (T2 hψ (T1 hψ c q)).2 := by
    have := s3 (c2.1.trans h2) (by rw [lb2]; exact h0) (by rw [lb1, lb2]; exact hlab)
      (by rw [c1.1]; exact h1.1) (by rw [c1.1]; exact h1.2)
    unfold NG; rw [this]; exact ⟨nofun, nofun⟩
  have hm := ((restLo_pm hψ c (T2 hψ (T1 hψ c q))).trans (T7_pm _)).trans (restHi_pm hψ κ c _)
  exact ⟨hm.1.ng n1, hm.2.ng n2⟩

/-- F3 inside the row: a `done` responder output came from a `done` responder
whose initiator was in the generation. -/
theorem rest_F3 (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ)
    (hlab : q.1.core.label.val + 1 = q.2.core.label.val) (h0 : q.2.core.label.val ≠ 0)
    (hd : (restPair hψ κ c q).2.core.state = .done) :
    q.2.core.state = .done ∧ (q.1.core.state = .produce ∨ q.1.core.state = .done) := by
  have t1 := T1_cv hψ c q
  have a1 := T1_pa hψ c q
  obtain ⟨c1, c2, -, -⟩ := t1
  simp only [cv, Prod.mk.injEq] at c1 c2
  have lb1 : (T1 hψ c q).1.core.label.val = q.1.core.label.val := by rw [av_label, a1.1, ← av_label]
  have lb2 : (T1 hψ c q).2.core.label.val = q.2.core.label.val := by rw [av_label, a1.2, ← av_label]
  obtain ⟨-, s2, -⟩ := T2_spec hψ (T1 hψ c q)
  have hm := ((restLo_pm hψ c (T2 hψ (T1 hψ c q))).trans (T7_pm _)).trans (restHi_pm hψ κ c _)
  have e : restPair hψ κ c q = restHi hψ κ c (T7 (restLo hψ c (T2 hψ (T1 hψ c q)))) := rfl
  rw [e] at hd
  have hd2 : (T2 hψ (T1 hψ c q)).2.core.state = .done := hm.2.2.1 hd
  obtain ⟨e1, e2⟩ := s2 hd2
  have := e2 (by rw [lb2]; exact h0) (by rw [lb1, lb2]; exact hlab)
  rw [c1.1] at this
  exact ⟨c2.1.symm.trans e1, this⟩

end Lower

/-! ## Part G. Row lemmas for one block edge

A row is one interaction of the AuthF pipeline on the block edge
`(g,k) → (g,k+1)` with `k+1 ≤ ψ-1`, between leaderless, reset-free cells with
their correct labels `k` and `k+1`.  By SF and the P′ frame the output agrees,
on state, paths, `wait` and colours, with `restPair` after GENSIG on inputs
that agree with `l`, `r` on every field GENSIG and the row lemmas read. -/

section Rows
variable {ψ : Nat}

open PPLLAuthResetDrain (av dv)

/-- The standing hypotheses of one row. -/
structure RowH (ψ : Nat) (l r : AuthState ψ) (k : Nat) : Prop where
  lk : l.core.label.val = k
  rk : r.core.label.val = k + 1
  kψ : k + 1 ≤ ψ - 1
  ll : l.core.leader = false
  rl : r.core.leader = false
  lr : l.core.reset_cmd = false
  rr : r.core.reset_cmd = false

theorem RowH.lab {l r : AuthState ψ} {k : Nat} (h : RowH ψ l r k) :
    r.core.label.val = (l.core.label.val + 1) % ψ := by
  rw [h.rk, h.lk, Nat.mod_eq_of_lt (by have := h.kψ; omega)]

/-- The P′-updated inputs with all fields but `probe` unchanged. -/
def withProbe (u : AuthState ψ) (x : Bool) : AuthState ψ :=
  { u with core := { u.core with probe := x } }

/-- Open a row: the output fields are those of `restPair` after GENSIG on the
P′-updated inputs. -/
theorem row_open (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (k : Nat)
    (h : RowH ψ l r k) :
    ∃ x y : Bool,
      FV (PPLLAuthF.pipeline hψ κ c l r).1 =
        FV (restPair hψ κ c (genSigAuth hψ κ (withProbe l x) (withProbe r y))).1 ∧
      FV (PPLLAuthF.pipeline hψ κ c l r).2 =
        FV (restPair hψ κ c (genSigAuth hψ κ (withProbe l x) (withProbe r y))).2 := by
  obtain ⟨x, y, hP⟩ := P0_frame hψ l r h.ll h.rl h.lab
  refine ⟨x, y, ?_⟩
  have hf := pipeline_FV hψ κ c l r h.ll h.rl h.lr h.rr
  rw [beforeSuppress_eq, hP] at hf
  exact hf

theorem FV_state {u v : AuthState ψ} (h : FV u = FV v) : u.core.state = v.core.state :=
  congrArg Prod.fst h
theorem FV_path {u v : AuthState ψ} (h : FV u = FV v) : u.core.path = v.core.path :=
  congrArg (fun z => z.2.1) h
theorem FV_path2 {u v : AuthState ψ} (h : FV u = FV v) : u.core.path2 = v.core.path2 :=
  congrArg (fun z => z.2.2.1) h
theorem FV_wait {u v : AuthState ψ} (h : FV u = FV v) : u.core.wait = v.core.wait :=
  congrArg (fun z => z.2.2.2.1) h
theorem FV_ctrl {u v : AuthState ψ} (h : FV u = FV v) : u.ctrl_mark = v.ctrl_mark :=
  congrArg (fun z => z.2.2.2.2.1) h
theorem FV_pm {u v : AuthState ψ} (h : FV u = FV v) : u.path_mark = v.path_mark :=
  congrArg (fun z => z.2.2.2.2.2) h

theorem Po_of_FV {u v : AuthState ψ} (h : FV u = FV v) (hv : ¬ Po v) : ¬ Po u := by
  intro hu; apply hv; unfold Po at hu ⊢; rw [← FV_state h, ← FV_path h]; exact hu

theorem NG_of_FV {u v : AuthState ψ} (h : FV u = FV v) (hv : NG v) : NG u := by
  unfold NG at hv ⊢; rw [FV_state h]; exact hv

/-- GENSIG outputs of a row are leaderless and reset-free, with labels `k`, `k+1`. -/
theorem genSig_row (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) (k : Nat) (h : RowH ψ l r k) (x y : Bool) :
    (genSigAuth hψ κ (withProbe l x) (withProbe r y)).1.core.leader = false ∧
    (genSigAuth hψ κ (withProbe l x) (withProbe r y)).2.core.leader = false ∧
    (genSigAuth hψ κ (withProbe l x) (withProbe r y)).1.core.reset_cmd = false ∧
    (genSigAuth hψ κ (withProbe l x) (withProbe r y)).2.core.reset_cmd = false ∧
    (genSigAuth hψ κ (withProbe l x) (withProbe r y)).1.core.label.val = k ∧
    (genSigAuth hψ κ (withProbe l x) (withProbe r y)).2.core.label.val = k + 1 := by
  have hp := genSig_pa hψ κ (withProbe l x) (withProbe r y)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [av_leader, hp.1]; exact h.ll
  · rw [av_leader, hp.2]; exact h.rl
  · rw [av_reset, hp.1]; exact h.lr
  · rw [av_reset, hp.2]; exact h.rr
  · rw [av_label, hp.1]; exact h.lk
  · rw [av_label, hp.2]; exact h.rk

/-- F1: no row leaves an occupied `produce`. -/
theorem row_F1 (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (k : Nat)
    (h : RowH ψ l r k) :
    ¬ Po (PPLLAuthF.pipeline hψ κ c l r).1 ∧ ¬ Po (PPLLAuthF.pipeline hψ κ c l r).2 := by
  obtain ⟨x, y, e1, e2⟩ := row_open hψ κ c l r k h
  obtain ⟨g1, g2, -⟩ := genSig_row hψ κ l r k h x y
  have hn := restPair_noPo hψ κ c _ g1 g2
  exact ⟨Po_of_FV e1 hn.1, Po_of_FV e2 hn.2⟩

/-- F2: the head never leaves a row in `done`. -/
theorem row_F2 (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (h : RowH ψ l r 0) : (PPLLAuthF.pipeline hψ κ c l r).1.core.state ≠ .done := by
  obtain ⟨x, y, e1, -⟩ := row_open hψ κ c l r 0 h
  rw [FV_state e1]
  intro hd
  have hm := (restPair_pm hψ κ c (genSigAuth hψ κ (withProbe l x) (withProbe r y))).1
  exact gs_head_not_done hψ κ (withProbe l x) (withProbe r y) h.lk (hm.2.1 hd)

/-- F3: a responder leaves a row in `done` only if the initiator entered in
`done` and is not the head. -/
theorem row_F3 (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (k : Nat)
    (h : RowH ψ l r k) (hd : (PPLLAuthF.pipeline hψ κ c l r).2.core.state = .done) :
    l.core.state = .done ∧ k ≠ 0 := by
  obtain ⟨x, y, -, e2⟩ := row_open hψ κ c l r k h
  obtain ⟨-, -, -, -, g5, g6⟩ := genSig_row hψ κ l r k h x y
  rw [FV_state e2] at hd
  have h3 := rest_F3 hψ κ c _ (by rw [g5, g6]) (by rw [g6]; omega) hd
  have h4 := gs_F3 hψ κ (withProbe l x) (withProbe r y) (by show l.core.label.val + 1 < ψ; have := h.kψ; rw [h.lk]; omega) h3.1 h3.2
  exact ⟨h4.1, by have := h4.2; rw [show (withProbe l x).core.label.val = k from h.lk] at this; exact this⟩

/-- C1: a pathless producer recruits a non-terminal successor; both leave the
row as pathless producers of the initiator's colour without `path2`. -/
theorem row_recruit (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (k : Nat)
    (h : RowH ψ l r k) (hk2 : k + 1 < ψ - 1)
    (hlP : l.core.state = .produce) (hlb : l.core.path = .bot)
    (hrD : r.core.state ≠ .done) (hrP : r.core.state = .produce → r.core.path = .bot) :
    (PPLLAuthF.pipeline hψ κ c l r).1.core.state = .produce ∧
    (PPLLAuthF.pipeline hψ κ c l r).1.core.path = .bot ∧
    (PPLLAuthF.pipeline hψ κ c l r).1.core.path2 = none ∧
    (PPLLAuthF.pipeline hψ κ c l r).1.ctrl_mark = l.ctrl_mark ∧
    (PPLLAuthF.pipeline hψ κ c l r).2.core.state = .produce ∧
    (PPLLAuthF.pipeline hψ κ c l r).2.core.path = .bot ∧
    (PPLLAuthF.pipeline hψ κ c l r).2.core.path2 = none ∧
    (PPLLAuthF.pipeline hψ κ c l r).2.ctrl_mark = l.ctrl_mark := by
  obtain ⟨x, y, e1, e2⟩ := row_open hψ κ c l r k h
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := genSig_row hψ κ l r k h x y
  have hs := gs_recruit hψ κ (withProbe l x) (withProbe r y) hlP hlb hrD hrP
    (by show r.core.label.val ≠ 0; rw [h.rk]; omega)
    (by show r.core.label.val ≠ ψ - 1; rw [h.rk]; omega)
    (by show l.core.label.val ≠ ψ - 1; rw [h.lk]; omega)
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hs
  have hq := rest_Ph hψ κ c _ s1 s4 s2 s5 g1 g2 g3 g4 (by rw [g6]; omega)
  obtain ⟨q1, q2, q3, -, q5, q6, q7, q8, -, q10⟩ := hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [FV_state e1]; exact q1
  · rw [FV_path e1]; exact q2
  · rw [FV_path2 e1]; exact q3
  · rw [FV_ctrl e1, q5]; exact s3
  · rw [FV_state e2]; exact q6
  · rw [FV_path e2]; exact q7
  · rw [FV_path2 e2]; exact q8
  · rw [FV_ctrl e2, q10]; exact s6

/-- C2/C3: a pathless producer next to its emitting terminal, or next to a
`done` link of its own colour, becomes the next `done` link (the head leaves
the generation); the successor leaves the generation. -/
theorem row_prop (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (k : Nat)
    (h : RowH ψ l r k) (hlP : l.core.state = .produce) (hlb : l.core.path = .bot)
    (hr : (k + 1 = ψ - 1 ∧ r.core.state ≠ .done ∧ (r.core.state = .produce → r.core.path = .bot)) ∨
      (k + 1 < ψ - 1 ∧ r.core.state = .done ∧ r.ctrl_mark = l.ctrl_mark ∧
        r.path_mark = l.ctrl_mark ∧ r.core.path2 = none ∧ ∃ b, r.core.path = .some (k + 1) b)) :
    NG (PPLLAuthF.pipeline hψ κ c l r).2 ∧
    (PPLLAuthF.pipeline hψ κ c l r).1.core.state ≠ .produce ∧
    (k = 0 → NG (PPLLAuthF.pipeline hψ κ c l r).1) ∧
    (k ≠ 0 → l.core.path2 = none →
      (PPLLAuthF.pipeline hψ κ c l r).1.core.state = .done ∧
      (∃ b, (PPLLAuthF.pipeline hψ κ c l r).1.core.path = .some k b) ∧
      (PPLLAuthF.pipeline hψ κ c l r).1.core.path2 = none ∧
      (PPLLAuthF.pipeline hψ κ c l r).1.ctrl_mark = l.ctrl_mark ∧
      (PPLLAuthF.pipeline hψ κ c l r).1.path_mark = l.ctrl_mark) := by
  obtain ⟨x, y, e1, e2⟩ := row_open hψ κ c l r k h
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := genSig_row hψ κ l r k h x y
  have hs := gs_prop hψ κ (withProbe l x) (withProbe r y) hlP hlb
    (by show l.core.label.val ≠ ψ - 1; rw [h.lk]; have := h.kψ; omega)
    (by show r.core.label.val ≠ 0; rw [h.rk]; omega)
    (by
      show (r.core.label.val = ψ - 1 ∧ r.core.state ≠ .done ∧
          (r.core.state = .produce → r.core.path = .bot)) ∨
        (r.core.label.val ≠ ψ - 1 ∧ r.core.state = .done ∧ r.ctrl_mark = l.ctrl_mark ∧
          r.path_mark = l.ctrl_mark ∧ ∃ b, r.core.path = .some r.core.label.val b)
      rw [h.rk]
      rcases hr with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4, -, a6⟩
      · exact Or.inl ⟨a1, a2, a3⟩
      · exact Or.inr ⟨by omega, a2, a3, a4, a6⟩)
  obtain ⟨s1, ⟨b2, s2⟩, s3, s4, s5, s6⟩ := hs
  have pm := restPair_pm hψ κ c (genSigAuth hψ κ (withProbe l x) (withProbe r y))
  have ng2 : NG (genSigAuth hψ κ (withProbe l x) (withProbe r y)).2 := by
    unfold NG; rw [s1]; exact ⟨by nofun, by nofun⟩
  have np1 : (genSigAuth hψ κ (withProbe l x) (withProbe r y)).1.core.state ≠ .produce := by
    by_cases hk : (withProbe l x).core.label.val = 0
    · rw [s5 hk]; nofun
    · rw [(s6 hk).1]; nofun
  refine ⟨NG_of_FV e2 (pm.2.ng ng2), ?_, ?_, ?_⟩
  · rw [FV_state e1]; intro hp; exact np1 (pm.1.1 hp)
  · intro hk
    have := s5 (show l.core.label.val = 0 by rw [h.lk]; exact hk)
    exact NG_of_FV e1 (pm.1.ng ⟨by rw [this]; nofun, by rw [this]; nofun⟩)
  · intro hk hp2
    obtain ⟨t1, ⟨b1, t2⟩, t3, t4, t5⟩ := s6 (show l.core.label.val ≠ 0 by rw [h.lk]; exact hk)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hq := rest_chain hψ κ c (genSigAuth hψ κ (withProbe l x) (withProbe r y)) k' b1 b2 t1
      (by rw [t2]; show PathInfo.some l.core.label.val b1 = _; rw [h.lk])
      g5 (by have := h.kψ; omega) (t5 hp2) g1 g3
      (by rw [s2]; show PathInfo.some r.core.label.val b2 = _; rw [h.rk])
      (by rw [s3, t4]) (s4 (by
        rcases hr with ⟨a1, -, -⟩ | ⟨-, -, -, -, a5, -⟩
        · right; show r.core.label.val = ψ - 1; rw [h.rk]; exact a1
        · left; exact a5)) s1 g2
    obtain ⟨q1, q2, q3, q4, q5, -⟩ := hq
    refine ⟨?_, ⟨b1, ?_⟩, ?_, ?_, ?_⟩
    · rw [FV_state e1]; exact q1
    · rw [FV_path e1]; exact q2
    · rw [FV_path2 e1]; exact q3
    · rw [FV_ctrl e1, q4]; exact t3
    · rw [FV_pm e1, q5]; exact t4

/-- C4/C5: a non-generation initiator next to a successor that is not a
producer (or is the pathless terminal producer).  Either both leave the
generation, or the head starts a fresh generation with a pathless
`wait = false` head and a recruited successor. -/
theorem row_release (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (k : Nat)
    (h : RowH ψ l r k) (hlN : NG l)
    (hr : r.core.state = .produce → r.core.path = .bot ∧ k + 1 = ψ - 1) :
    (NG (PPLLAuthF.pipeline hψ κ c l r).1 ∧ NG (PPLLAuthF.pipeline hψ κ c l r).2) ∨
    (k = 0 ∧ (PPLLAuthF.pipeline hψ κ c l r).1.core.state = .produce ∧
      (PPLLAuthF.pipeline hψ κ c l r).1.core.path = .bot ∧
      (PPLLAuthF.pipeline hψ κ c l r).1.core.wait = false ∧
      (PPLLAuthF.pipeline hψ κ c l r).2.core.state = .produce ∧
      (PPLLAuthF.pipeline hψ κ c l r).2.core.path = .bot) := by
  obtain ⟨x, y, e1, e2⟩ := row_open hψ κ c l r k h
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := genSig_row hψ κ l r k h x y
  have hs := gs_release hψ κ (withProbe l x) (withProbe r y) hlN.1 hlN.2
    (by show l.core.label.val ≠ ψ - 1; rw [h.lk]; have := h.kψ; omega)
    (by show r.core.label.val ≠ 0; rw [h.rk]; omega)
    (by
      show r.core.state = .produce → r.core.path = .bot ∧ r.core.label.val = ψ - 1
      intro hp; obtain ⟨a1, a2⟩ := hr hp; rw [h.rk]; exact ⟨a1, a2⟩)
  have pm := restPair_pm hψ κ c (genSigAuth hψ κ (withProbe l x) (withProbe r y))
  rcases hs with ⟨n1, n2, n3⟩ | ⟨hk, p1, p2, p3, p4, p5, p6⟩
  · left
    by_cases hd : (genSigAuth hψ κ (withProbe l x) (withProbe r y)).2.core.state = .done
    · have := rest_release hψ κ c _ ⟨n1, n2⟩ hd (by rw [g5, g6]) (by rw [g6]; omega)
      exact ⟨NG_of_FV e1 this.1, NG_of_FV e2 this.2⟩
    · exact ⟨NG_of_FV e1 (pm.1.ng ⟨n1, n2⟩), NG_of_FV e2 (pm.2.ng ⟨n3, hd⟩)⟩
  · right
    have hq := rest_Ph hψ κ c _ p1 p4 p2 p5 g1 g2 g3 g4
      (by rw [g6]; intro he; apply p6; show r.core.label.val = ψ - 1; rw [h.rk]; exact he)
    obtain ⟨q1, q2, -, q4, -, q6, q7, -, -, -⟩ := hq
    refine ⟨by rw [← h.lk]; exact hk, ?_, ?_, ?_, ?_, ?_⟩
    · rw [FV_state e1]; exact q1
    · rw [FV_path e1]; exact q2
    · rw [FV_wait e1, q4]; exact p3
    · rw [FV_state e2]; exact q6
    · rw [FV_path e2]; exact q7

end Rows

/-! ## Part H. Standing invariants of a row

A row between leaderless, reset-free cells with consecutive labels whose two
outputs are leaderless keeps both labels and leaves both cells reset-free
(`reset_cmd` is only moved rightward by Algorithm 14, and both inputs carry
none; `echo` is arbitrary throughout). -/

section Std
variable {ψ : Nat}

theorem klabel_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).label = if p then a.label else b.label := by split <;> rfl

/-- K4 keeps the initiator's label. -/
theorem kernel_left_label (hp : ψ > 0) (l r : AgentState ψ) :
    (k4Kernel hp l r).1.label = l.label := by
  simp only [k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire, absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp only [gfst_ite, gsnd_ite, klabel_ite, ite_self]

/-- **Row standing invariant.** Labels and `reset_cmd = false` survive a row
whose outputs are leaderless. -/
theorem row_std (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false)
    (hnext : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (ho2 : (PPLLAuthF.pipeline hψ κ c l r).2.core.leader = false) :
    (PPLLAuthF.pipeline hψ κ c l r).1.core.label = l.core.label ∧
    (PPLLAuthF.pipeline hψ κ c l r).2.core.label = r.core.label ∧
    (PPLLAuthF.pipeline hψ κ c l r).1.core.reset_cmd = false ∧
    (PPLLAuthF.pipeline hψ κ c l r).2.core.reset_cmd = false := by
  have hc := PPLLAuthWriterFrame.pipeline_writer_compose hψ κ c l r hl hr
  have hi := PPLLAuthWriterFrame.prefix_writer_inputs hψ κ c l r hl hr hnext
  have hrs := PPLLAuthResetDrain.pipeline_follower_reset hψ κ c l r hl
  have hlab := PPLLAuthResetDrain.pipeline_follower_labels hψ κ c l r hl hr ho2
  dsimp only at hc
  refine ⟨?_, ?_, hrs.1, ?_⟩
  · rw [hc.1]
    have hw := (PPLLAstraReadyThree.Writer.write_control hψ
      (k4Kernel hψ (PPLLAuthF.beforeElimination hψ κ c l r).1.core
        (PPLLAuthF.beforeElimination hψ κ c l r).2.core).1
      (k4Kernel hψ (PPLLAuthF.beforeElimination hψ κ c l r).1.core
        (PPLLAuthF.beforeElimination hψ κ c l r).2.core).2).1
    have h1 := congrArg Prod.fst hw
    simp only [PPLLAstraReadyThree.control] at h1
    rw [h1, kernel_left_label, hi.1]
  · apply Fin.ext; rw [hlab.2, hnext]
  · rw [hrs.2, hlr, hrr]; rfl

end Std

/-! ## Part I. Block bookkeeping

Block `g` is the physical segment `gψ, …, gψ+ψ-1`; edge `k` of the block
(`k+1 < ψ`) is the interaction `(gψ+k) → (gψ+k+1)`. A block edge never wraps
around the ring, so perfect labels give the row labels `k`, `k+1` without
`ψ ∣ n`. `Rch C L P` says that some word of length at most `L` from `C`
reaches a configuration with a leader or one satisfying `P`. -/

section Block
variable {n ψ : Nat}

open PPLLAuthResetDrain (authProtocol authRun)

/-- One scheduled interaction on the AuthF protocol. -/
abbrev bstep (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e : Fin n) : Fin n → AuthState ψ :=
  (authProtocol hp κ c).step ring C e

/-- Cell `k` of block `g`, i.e. physical position `gψ+k` (mod `n`). -/
def bcell (ring : DirectedRing n) (ψ g k : Nat) : Fin n := ⟨(g * ψ + k) % n, Nat.mod_lt _ ring.hn⟩

theorem rn_bcell (ring : DirectedRing n) (g k : Nat) :
    ring.rightNeighbor (bcell ring ψ g k) = bcell ring ψ g (k + 1) := by
  apply Fin.ext
  show ((g * ψ + k) % n + 1) % n = (g * ψ + (k + 1)) % n
  rw [Nat.add_mod ((g * ψ + k) % n) 1 n, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]

theorem bcell_val (ring : DirectedRing n) {g k : Nat} (hg : g * ψ + ψ ≤ n) (hk : k < ψ) :
    (bcell ring ψ g k).val = g * ψ + k := by
  show (g * ψ + k) % n = g * ψ + k
  exact Nat.mod_eq_of_lt (by omega)

theorem bcell_mod (g k : Nat) (hk : k < ψ) : (g * ψ + k) % ψ = k := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]

theorem bcell_ne (ring : DirectedRing n) {g k k' : Nat} (hg : g * ψ + ψ ≤ n) (hk : k < ψ)
    (hk' : k' < ψ) (h : k ≠ k') : bcell ring ψ g k ≠ bcell ring ψ g k' := by
  intro he
  have hv := congrArg Fin.val he
  rw [bcell_val ring hg hk, bcell_val ring hg hk'] at hv
  omega

theorem bneighbor_ne (ring : DirectedRing n) (hn : 1 < n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have he := congrArg Fin.val h
  change (e.val + 1) % n = e.val at he
  by_cases hk : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hk] at he; omega
  · have hlast : e.val + 1 = n := by omega
    rw [hlast, Nat.mod_self] at he; omega

theorem bstep_left (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e : Fin n) :
    bstep hp κ c ring C e e = (PPLLAuthF.pipeline hp κ c (C e) (C (ring.rightNeighbor e))).1 := by
  simp [bstep, PopulationProtocol.step, authProtocol]

theorem bstep_right (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (hn : 1 < n) (C : Fin n → AuthState ψ) (e : Fin n) :
    bstep hp κ c ring C e (ring.rightNeighbor e) =
      (PPLLAuthF.pipeline hp κ c (C e) (C (ring.rightNeighbor e))).2 := by
  have ne := bneighbor_ne ring hn e
  simp [bstep, PopulationProtocol.step, authProtocol, ne]

theorem bstep_other (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e i : Fin n) (h1 : i ≠ e) (h2 : i ≠ ring.rightNeighbor e) :
    bstep hp κ c ring C e i = C i := by
  simp [bstep, PopulationProtocol.step, authProtocol, h1, h2]

theorem authRun_app (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (w1 w2 : List (Fin n)) : ∀ C : Fin n → AuthState ψ,
    authRun hp κ c ring C (w1 ++ w2) = authRun hp κ c ring (authRun hp κ c ring C w1) w2 := by
  induction w1 with
  | nil => intro C; rfl
  | cons e es ih => intro C; exact ih _

/-- Some cell is a leader. -/
def Ldr (C : Fin n → AuthState ψ) : Prop := ∃ i, (C i).core.leader = true

/-- The standing hypotheses of GEN-DRAIN: leaderless, reset-free, perfect labels. -/
def Std (C : Fin n → AuthState ψ) : Prop :=
  ∀ i, (C i).core.leader = false ∧ (C i).core.reset_cmd = false ∧
    (C i).core.label.val = i.val % ψ

/-- Cells outside block `g` are those of `C0`. -/
def Out (ring : DirectedRing n) (ψ g : Nat) (C0 C : Fin n → AuthState ψ) : Prop :=
  ∀ i, (∀ k, k < ψ → i ≠ bcell ring ψ g k) → C i = C0 i

/-- Some word of length at most `L` reaches a leader or a configuration in `P`. -/
def Rch (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (L : Nat) (P : (Fin n → AuthState ψ) → Prop) : Prop :=
  ∃ w : List (Fin n), w.length ≤ L ∧
    (Ldr (authRun hp κ c ring C w) ∨ P (authRun hp κ c ring C w))

theorem Rch_now (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {C : Fin n → AuthState ψ} {L : Nat} {P : (Fin n → AuthState ψ) → Prop} (h : P C) :
    Rch hp κ c ring C L P :=
  ⟨[], Nat.zero_le _, Or.inr h⟩

theorem Rch_mono (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {C : Fin n → AuthState ψ} {L L' : Nat} {P Q : (Fin n → AuthState ψ) → Prop}
    (hL : L ≤ L') (hPQ : ∀ D, P D → Q D) (h : Rch hp κ c ring C L P) :
    Rch hp κ c ring C L' Q := by
  obtain ⟨w, hw, h⟩ := h
  exact ⟨w, Nat.le_trans hw hL, h.imp id (hPQ _)⟩

theorem Rch_bind (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {C : Fin n → AuthState ψ} {L1 L2 : Nat} {P Q : (Fin n → AuthState ψ) → Prop}
    (h1 : Rch hp κ c ring C L1 P) (h2 : ∀ D, P D → Rch hp κ c ring D L2 Q) :
    Rch hp κ c ring C (L1 + L2) Q := by
  obtain ⟨w1, hw1, h1⟩ := h1
  rcases h1 with hL | hP
  · exact ⟨w1, Nat.le_trans hw1 (Nat.le_add_right _ _), Or.inl hL⟩
  · obtain ⟨w2, hw2, h2⟩ := h2 _ hP
    refine ⟨w1 ++ w2, ?_, ?_⟩
    · rw [List.length_append]; omega
    · rw [authRun_app]; exact h2

/-- The row hypotheses of block edge `k` in a standing configuration. -/
theorem std_row (ring : DirectedRing n) {g k : Nat} (hg : g * ψ + ψ ≤ n) (hk : k + 1 < ψ)
    {C : Fin n → AuthState ψ} (hS : Std C) :
    RowH ψ (C (bcell ring ψ g k)) (C (bcell ring ψ g (k + 1))) k := by
  have a := hS (bcell ring ψ g k)
  have b := hS (bcell ring ψ g (k + 1))
  rw [bcell_val ring hg (by omega), bcell_mod g k (by omega)] at a
  rw [bcell_val ring hg hk, bcell_mod g (k + 1) hk] at b
  exact ⟨a.2.2, b.2.2, by omega, a.1, b.1, a.2.1, b.2.1⟩

/-- The effect of one block edge on a standing configuration. -/
def StepPost (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n) (g : Nat)
    (C0 C : Fin n → AuthState ψ) (k : Nat) (D : Fin n → AuthState ψ) : Prop :=
  Std D ∧ Out ring ψ g C0 D ∧
  D (bcell ring ψ g k) =
    (PPLLAuthF.pipeline hp κ c (C (bcell ring ψ g k)) (C (bcell ring ψ g (k + 1)))).1 ∧
  D (bcell ring ψ g (k + 1)) =
    (PPLLAuthF.pipeline hp κ c (C (bcell ring ψ g k)) (C (bcell ring ψ g (k + 1)))).2 ∧
  ∀ k', k' < ψ → k' ≠ k → k' ≠ k + 1 → D (bcell ring ψ g k') = C (bcell ring ψ g k')

/-- **One block edge.** From a standing configuration, edge `k` either creates a
leader or yields a standing configuration that differs from `C` only on the two
cells of the edge, which carry the AuthF outputs. -/
theorem step_block (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} (hS : Std C)
    (hO : Out ring ψ g C0 C) {k : Nat} (hk : k + 1 < ψ) :
    Rch hp κ c ring C 1 (StepPost hp κ c ring g C0 C k) := by
  have hn : 1 < n := by omega
  refine ⟨[bcell ring ψ g k], Nat.le_refl _, ?_⟩
  show Ldr (bstep hp κ c ring C (bcell ring ψ g k)) ∨ _
  by_cases hL : Ldr (bstep hp κ c ring C (bcell ring ψ g k))
  · exact Or.inl hL
  right
  show StepPost hp κ c ring g C0 C k (bstep hp κ c ring C (bcell ring ψ g k))
  have hLf : ∀ i, (bstep hp κ c ring C (bcell ring ψ g k) i).core.leader = false := by
    intro i
    cases h : (bstep hp κ c ring C (bcell ring ψ g k) i).core.leader
    · rfl
    · exact absurd ⟨i, h⟩ hL
  have hR := std_row ring hg hk hS
  have e1 := bstep_left hp κ c ring C (bcell ring ψ g k)
  have e2 := bstep_right hp κ c ring hn C (bcell ring ψ g k)
  rw [rn_bcell] at e1 e2
  have eo := bstep_other hp κ c ring C (bcell ring ψ g k)
  rw [rn_bcell] at eo
  have o2 : (PPLLAuthF.pipeline hp κ c (C (bcell ring ψ g k)) (C (bcell ring ψ g (k + 1)))).2.core.leader
      = false := by rw [← e2]; exact hLf _
  have hnext : (C (bcell ring ψ g (k + 1))).core.label =
      ⟨((C (bcell ring ψ g k)).core.label.val + 1) % ψ, Nat.mod_lt _ hp⟩ := by
    apply Fin.ext; show _ = _ % ψ; rw [hR.rk, hR.lk, Nat.mod_eq_of_lt hk]
  have hs := row_std hp κ c _ _ hR.ll hR.rl hR.lr hR.rr hnext o2
  have ne : bcell ring ψ g k ≠ bcell ring ψ g (k + 1) := bcell_ne ring hg (by omega) hk (by omega)
  refine ⟨?_, ?_, e1, e2, ?_⟩
  · intro i
    refine ⟨hLf i, ?_⟩
    by_cases h1 : i = bcell ring ψ g k
    · subst h1; rw [e1, hs.1]; exact ⟨hs.2.2.1, (hS _).2.2⟩
    · by_cases h2 : i = bcell ring ψ g (k + 1)
      · subst h2; rw [e2, hs.2.1]; exact ⟨hs.2.2.2, (hS _).2.2⟩
      · rw [eo i h1 h2]; exact (hS i).2
  · intro i hi
    rw [eo i (hi k (by omega)) (hi (k + 1) hk)]; exact hO i hi
  · intro k' hk' h1 h2
    exact eo _ (bcell_ne ring hg hk' (by omega) h1) (bcell_ne ring hg hk' hk h2)

end Block

/-! ## Part J. The drain word `W_B = F ++ R^(ψ-2)`

`F` serves the block edges `0, 1, …, ψ-2` left to right, `R` serves
`ψ-3, …, 0` right to left. By F1 no served cell stays an occupied producer; by
F2 the head never leaves in `done`; by F3 a responder leaves in `done` only
behind a `done` initiator that is not the head. Hence after `F` no cell is an
occupied producer and the `done` cells lie in `[1, ψ-2]`, and every `R` sweep
raises the lower end of that interval by one. After `ψ-2` sweeps no cell of the
block is `done` or an occupied producer (the original sketch uses `(ψ-1)^2` edges here). -/

section Drain
variable {n ψ : Nat}

open PPLLAuthResetDrain (authProtocol authRun)

/-- A `done` cell. -/
def Done (u : AuthState ψ) : Prop := u.core.state = .done

/-- Invariant after the first `t` edges of `F` (`t ≥ 1`). -/
def InvF (ring : DirectedRing n) (ψ g : Nat) (C0 C : Fin n → AuthState ψ) (t : Nat) : Prop :=
  Std C ∧ Out ring ψ g C0 C ∧ (∀ k, k ≤ t → ¬ Po (C (bcell ring ψ g k))) ∧
  ¬ Done (C (bcell ring ψ g 0)) ∧ ¬ Done (C (bcell ring ψ g t))

theorem F_first (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) (h2 : 2 ≤ ψ) {C0 C : Fin n → AuthState ψ} (hS : Std C)
    (hO : Out ring ψ g C0 C) : Rch hp κ c ring C 1 (fun D => InvF ring ψ g C0 D 1) := by
  apply Rch_mono hp κ c ring (Nat.le_refl _) _ (step_block hp κ c ring hg hS hO (k := 0) (by omega))
  intro D ⟨hS', hO', e1, e2, _⟩
  have hR := std_row ring hg (k := 0) (by omega) hS
  have f1 := row_F1 hp κ c _ _ 0 hR
  have f2 := row_F2 hp κ c _ _ hR
  have e2' : D (bcell ring ψ g 1) = _ := e2
  refine ⟨hS', hO', ?_, ?_, ?_⟩
  · intro k hk
    rcases Nat.lt_or_ge k 1 with h | h
    · obtain rfl : k = 0 := by omega
      rw [e1]; exact f1.1
    · obtain rfl : k = 1 := by omega
      rw [e2']; exact f1.2
  · unfold Done; rw [e1]; exact f2
  · unfold Done; rw [e2']; intro hd
    exact (row_F3 hp κ c _ _ 0 hR hd).2 rfl

theorem F_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {t : Nat} (ht : 1 ≤ t)
    (ht2 : t + 1 < ψ) (hI : InvF ring ψ g C0 C t) :
    Rch hp κ c ring C 1 (fun D => InvF ring ψ g C0 D (t + 1)) := by
  obtain ⟨hS, hO, hP, h0, hT⟩ := hI
  apply Rch_mono hp κ c ring (Nat.le_refl _) _ (step_block hp κ c ring hg hS hO ht2)
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg ht2 hS
  have f1 := row_F1 hp κ c _ _ t hR
  refine ⟨hS', hO', ?_, ?_, ?_⟩
  · intro k hk
    by_cases a : k = t
    · subst a; rw [e1]; exact f1.1
    · by_cases b : k = t + 1
      · subst b; rw [e2]; exact f1.2
      · rw [eo k (by omega) a b]; exact hP k (by omega)
  · rw [eo 0 (by omega) (by omega) (by omega)]; exact h0
  · unfold Done; rw [e2]; intro hd
    exact hT (row_F3 hp κ c _ _ t hR hd).1

theorem F_iter (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 : Fin n → AuthState ψ} :
    ∀ (s t : Nat) (C : Fin n → AuthState ψ), 1 ≤ t → t + s + 1 ≤ ψ →
      InvF ring ψ g C0 C t → Rch hp κ c ring C s (fun D => InvF ring ψ g C0 D (t + s)) := by
  intro s
  induction s with
  | zero => intro t C _ _ hI; exact Rch_now hp κ c ring hI
  | succ s ih =>
    intro t C ht hts hI
    have h := Rch_bind hp κ c ring (F_step hp κ c ring hg ht (by omega) hI)
      (fun D hD => ih (t + 1) D (by omega) (by omega) hD)
    apply Rch_mono hp κ c ring (by omega) _ h
    intro D hD
    rwa [show t + 1 + s = t + (s + 1) by omega] at hD

/-- **Phase F.** `ψ-1` edges leave no occupied producer and no `done` at the
two ends of the block. -/
theorem phaseF (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) (h2 : 2 ≤ ψ) {C0 C : Fin n → AuthState ψ} (hS : Std C)
    (hO : Out ring ψ g C0 C) :
    Rch hp κ c ring C (ψ - 1) (fun D => InvF ring ψ g C0 D (ψ - 1)) := by
  have h := Rch_bind hp κ c ring (F_first hp κ c ring hg h2 hS hO)
    (fun D hD => F_iter hp κ c ring hg (ψ - 2) 1 D (Nat.le_refl _) (by omega) hD)
  apply Rch_mono hp κ c ring (by omega) _ h
  intro D hD
  rwa [show 1 + (ψ - 2) = ψ - 1 by omega] at hD

/-- Invariant between `R` sweeps: no occupied producer, `done` only in `[lo, ψ-2]`. -/
def InvR (ring : DirectedRing n) (ψ g : Nat) (C0 C : Fin n → AuthState ψ) (lo : Nat) : Prop :=
  Std C ∧ Out ring ψ g C0 C ∧ 1 ≤ lo ∧
  ∀ k, k < ψ → ¬ Po (C (bcell ring ψ g k)) ∧
    (Done (C (bcell ring ψ g k)) → lo ≤ k ∧ k ≤ ψ - 2)

/-- Invariant inside an `R` sweep once the edges `ψ-3, …, s` are served. -/
def InvJ (ring : DirectedRing n) (ψ g : Nat) (C0 C : Fin n → AuthState ψ) (lo s : Nat) : Prop :=
  Std C ∧ Out ring ψ g C0 C ∧ (∀ k, k < ψ → ¬ Po (C (bcell ring ψ g k))) ∧
  (∀ k, k < s → Done (C (bcell ring ψ g k)) → lo ≤ k) ∧
  (∀ k, s < k → k < ψ → Done (C (bcell ring ψ g k)) → lo + 1 ≤ k ∧ k ≤ ψ - 2) ∧
  (s = 0 → ¬ Done (C (bcell ring ψ g 0)))

theorem R_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {lo s : Nat}
    (hs : s + 1 ≤ ψ - 2) (hI : InvJ ring ψ g C0 C lo (s + 1)) :
    Rch hp κ c ring C 1 (fun D => InvJ ring ψ g C0 D lo s) := by
  obtain ⟨hS, hO, hP, hlo, hhi, _⟩ := hI
  apply Rch_mono hp κ c ring (Nat.le_refl _) _ (step_block hp κ c ring hg hS hO (k := s) (by omega))
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg (k := s) (by omega) hS
  have f1 := row_F1 hp κ c _ _ s hR
  refine ⟨hS', hO', ?_, ?_, ?_, ?_⟩
  · intro k hk
    by_cases a : k = s
    · subst a; rw [e1]; exact f1.1
    · by_cases b : k = s + 1
      · subst b; rw [e2]; exact f1.2
      · rw [eo k hk a b]; exact hP k hk
  · intro k hk hd
    rw [eo k (by omega) (by omega) (by omega)] at hd
    exact hlo k (by omega) hd
  · intro k hk hk' hd
    by_cases b : k = s + 1
    · subst b
      unfold Done at hd; rw [e2] at hd
      have := hlo s (by omega) (row_F3 hp κ c _ _ s hR hd).1
      omega
    · rw [eo k hk' (by omega) b] at hd
      exact hhi k (by omega) hk' hd
  · intro h0; subst h0
    unfold Done; rw [e1]; exact row_F2 hp κ c _ _ hR

theorem R_iter (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 : Fin n → AuthState ψ} {lo : Nat} :
    ∀ (d : Nat) (C : Fin n → AuthState ψ), d ≤ ψ - 2 →
      InvJ ring ψ g C0 C lo d → Rch hp κ c ring C d (fun D => InvJ ring ψ g C0 D lo 0) := by
  intro d
  induction d with
  | zero => intro C _ hI; exact Rch_now hp κ c ring hI
  | succ d ih =>
    intro C hd hI
    have h := Rch_bind hp κ c ring (R_step hp κ c ring hg hd hI)
      (fun D hD => ih D (by omega) hD)
    exact Rch_mono hp κ c ring (by omega) (fun _ h => h) h

/-- **One `R` sweep** raises the lower end of the `done` interval. -/
theorem R_sweep (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {lo : Nat}
    (hI : InvR ring ψ g C0 C lo) :
    Rch hp κ c ring C (ψ - 2) (fun D => InvR ring ψ g C0 D (lo + 1)) := by
  obtain ⟨hS, hO, hlo1, hk⟩ := hI
  have hJ : InvJ ring ψ g C0 C lo (ψ - 2) := by
    refine ⟨hS, hO, fun k hk' => (hk k hk').1, ?_, ?_, ?_⟩
    · intro k hk' hd; exact ((hk k (by omega)).2 hd).1
    · intro k hk' hk'' hd; have := ((hk k hk'').2 hd).2; omega
    · intro _ hd; have := ((hk 0 (by omega)).2 hd).1; omega
  apply Rch_mono hp κ c ring (Nat.le_refl _) _ (R_iter hp κ c ring hg (ψ - 2) C (Nat.le_refl _) hJ)
  intro D ⟨hS', hO', hP, _, hhi, h0⟩
  refine ⟨hS', hO', by omega, fun k hk' => ⟨hP k hk', fun hd => ?_⟩⟩
  by_cases a : k = 0
  · subst a; exact absurd hd (h0 rfl)
  · exact hhi k (by omega) hk' hd

theorem R_sweeps (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 : Fin n → AuthState ψ} :
    ∀ (m lo : Nat) (C : Fin n → AuthState ψ), InvR ring ψ g C0 C lo →
      Rch hp κ c ring C (m * (ψ - 2)) (fun D => InvR ring ψ g C0 D (lo + m)) := by
  intro m
  induction m with
  | zero => intro lo C hI; exact Rch_now hp κ c ring hI
  | succ m ih =>
    intro lo C hI
    have h := Rch_bind hp κ c ring (R_sweep hp κ c ring hg hI) (fun D hD => ih (lo + 1) D hD)
    apply Rch_mono hp κ c ring (by rw [Nat.succ_mul]; omega) _ h
    intro D hD
    rwa [show lo + 1 + m = lo + (m + 1) by omega] at hD

/-- A block with no occupied producer and no `done` cell. -/
def Cl (ring : DirectedRing n) (ψ g : Nat) (C0 C : Fin n → AuthState ψ) : Prop :=
  Std C ∧ Out ring ψ g C0 C ∧
  ∀ k, k < ψ → ¬ Po (C (bcell ring ψ g k)) ∧ ¬ Done (C (bcell ring ψ g k))

/-- **W_B.** `(ψ-1) + (ψ-2)^2` block edges reach a leader or a block with no
occupied producer and no `done` cell. -/
theorem phaseW (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) (h2 : 2 ≤ ψ) {C0 C : Fin n → AuthState ψ} (hS : Std C)
    (hO : Out ring ψ g C0 C) :
    Rch hp κ c ring C ((ψ - 1) + (ψ - 2) * (ψ - 2)) (Cl ring ψ g C0) := by
  apply Rch_bind hp κ c ring (phaseF hp κ c ring hg h2 hS hO)
  intro D ⟨hS', hO', hP, h0, hT⟩
  have hR : InvR ring ψ g C0 D 1 := by
    refine ⟨hS', hO', Nat.le_refl _, fun k hk => ⟨hP k (by omega), fun hd => ?_⟩⟩
    have a : k ≠ 0 := by intro a; subst a; exact h0 hd
    have b : k ≠ ψ - 1 := by intro b; subst b; exact hT hd
    omega
  apply Rch_mono hp κ c ring (Nat.le_refl _) _ (R_sweeps hp κ c ring hg (ψ - 2) 1 D hR)
  intro E ⟨hS'', hO'', _, hk⟩
  refine ⟨hS'', hO'', fun k hk' => ⟨(hk k hk').1, fun hd => ?_⟩⟩
  have := (hk k hk').2 hd
  omega

end Drain

/-! ## Part K. Cleanup from the leftmost producer

After `W_B` every block cell is either non-generation or a pathless producer.
Let `j` be the leftmost producer. For `j ≤ ψ-3` the forward edges `j, …, ψ-3`
recruit (C1), the terminal edge `ψ-2` turns cell `ψ-2` into a `done` link of
the chain of colour `γ = ctrl(j)` (C2), the backward edges `ψ-3, …, j` pass the
link down to `j` (C3, the link at label `0` is deleted), and finally edge `j-1`
releases (C4): both cells leave the generation, or (`j = 1`) the head starts a
fresh generation with a pathless `wait = false` head, which is GenEntrance.
For `j = ψ-2` the terminal edge acts first and releases through `j-1`; for
`j = ψ-1` edge `ψ-2` releases at once. At most `2ψ-3` edges. -/

section Cleanup
variable {n ψ : Nat}

open PPLLAuthResetDrain (authProtocol authRun)

/-- A cell that GENSIG may recruit. -/
def Recruitable (u : AuthState ψ) : Prop :=
  u.core.path = .bot ∨ (u.core.state ≠ .produce ∧ u.core.state ≠ .done)

/-- GenEntrance for block `g`: a pathless head with `wait = false`
and every block cell recruitable. -/
def GenEntrance (ring : DirectedRing n) (ψ g : Nat) (C : Fin n → AuthState ψ) : Prop :=
  (C (bcell ring ψ g 0)).core.path = .bot ∧ (C (bcell ring ψ g 0)).core.wait = false ∧
  ∀ k, k < ψ → Recruitable (C (bcell ring ψ g k))

/-- No block cell is in `produce` or `done`. -/
def AllNG (ring : DirectedRing n) (ψ g : Nat) (C : Fin n → AuthState ψ) : Prop :=
  ∀ k, k < ψ → NG (C (bcell ring ψ g k))

/-- The cleanup target. -/
def Exit (ring : DirectedRing n) (ψ g : Nat) (C0 C : Fin n → AuthState ψ) : Prop :=
  Std C ∧ Out ring ψ g C0 C ∧ (GenEntrance ring ψ g C ∨ AllNG ring ψ g C)

theorem bot_of_noPo {u : AuthState ψ} (h : ¬ Po u) (hp : u.core.state = .produce) :
    u.core.path = .bot :=
  Classical.byContradiction fun hb => h ⟨hp, hb⟩

/-- **Release (C4).** A block whose only generation cell is `j ≥ 1`, which is
not a producer unless it is the pathless terminal producer, exits in one edge. -/
theorem rel_final (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} (hS : Std C)
    (hO : Out ring ψ g C0 C) {j : Nat} (hj1 : 1 ≤ j) (hj : j < ψ)
    (hN : ∀ k, k < ψ → k ≠ j → NG (C (bcell ring ψ g k)))
    (hJ : (C (bcell ring ψ g j)).core.state = .produce →
      (C (bcell ring ψ g j)).core.path = .bot ∧ j = ψ - 1) :
    Rch hp κ c ring C 1 (Exit ring ψ g C0) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  apply Rch_mono hp κ c ring (Nat.le_refl _) _ (step_block hp κ c ring hg hS hO (k := i) hj)
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg (k := i) hj hS
  have hq := row_release hp κ c _ _ i hR (hN i (by omega) (by omega))
    (fun h => ⟨(hJ h).1, (hJ h).2⟩)
  refine ⟨hS', hO', ?_⟩
  rcases hq with ⟨n1, n2⟩ | ⟨hi, p1, p2, p3, p4, p5⟩
  · right
    intro k hk
    by_cases a : k = i
    · subst a; rw [e1]; exact n1
    · by_cases b : k = i + 1
      · subst b; rw [e2]; exact n2
      · rw [eo k hk a b]; exact hN k hk b
  · left
    subst hi
    refine ⟨by rw [e1]; exact p2, by rw [e1]; exact p3, ?_⟩
    intro k hk
    by_cases a : k = 0
    · subst a; left; rw [e1]; exact p2
    · by_cases b : k = 0 + 1
      · subst b; left; rw [e2]; exact p5
      · right; rw [eo k hk a b]; exact hN k hk b

/-- Forward invariant: cells `j..t` are pathless producers of colour `γ`
(without `path2` once an edge has been served), cells left of `j` are
non-generation, cells right of `t` are untouched. -/
def Fw (ring : DirectedRing n) (ψ g : Nat) (C0 C : Fin n → AuthState ψ) (j : Nat)
    (γ : ProvColor) (t : Nat) : Prop :=
  Std C ∧ Out ring ψ g C0 C ∧ (∀ k, k < j → NG (C (bcell ring ψ g k))) ∧
  (∀ k, j ≤ k → k ≤ t → (C (bcell ring ψ g k)).core.state = .produce ∧
    (C (bcell ring ψ g k)).core.path = .bot ∧ (C (bcell ring ψ g k)).ctrl_mark = γ ∧
    (j < t → (C (bcell ring ψ g k)).core.path2 = none)) ∧
  (∀ k, t < k → k < ψ → ¬ Po (C (bcell ring ψ g k)) ∧ ¬ Done (C (bcell ring ψ g k)))

theorem Fw_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {j t : Nat} {γ : ProvColor}
    (hjt : j ≤ t) (ht : t + 3 ≤ ψ) (hI : Fw ring ψ g C0 C j γ t) :
    Rch hp κ c ring C 1 (fun D => Fw ring ψ g C0 D j γ (t + 1)) := by
  obtain ⟨hS, hO, hL, hM, hRt⟩ := hI
  apply Rch_mono hp κ c ring (Nat.le_refl _) _ (step_block hp κ c ring hg hS hO (k := t) (by omega))
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg (k := t) (by omega) hS
  obtain ⟨m1, m2, m3, -⟩ := hM t hjt (Nat.le_refl _)
  obtain ⟨r1, r2⟩ := hRt (t + 1) (by omega) (by omega)
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ :=
    row_recruit hp κ c _ _ t hR (by omega) m1 m2 r2 (bot_of_noPo r1)
  refine ⟨hS', hO', ?_, ?_, ?_⟩
  · intro k hk; rw [eo k (by omega) (by omega) (by omega)]; exact hL k hk
  · intro k hk1 hk2
    by_cases a : k = t
    · subst a; rw [e1]; exact ⟨q1, q2, q4.trans m3, fun _ => q3⟩
    · by_cases b : k = t + 1
      · subst b; rw [e2]; exact ⟨q5, q6, q8.trans m3, fun _ => q7⟩
      · rw [eo k (by omega) a b]
        obtain ⟨s1, s2, s3, s4⟩ := hM k hk1 (by omega)
        exact ⟨s1, s2, s3, fun _ => s4 (by omega)⟩
  · intro k hk1 hk2
    rw [eo k hk2 (by omega) (by omega)]; exact hRt k (by omega) hk2

theorem Fw_iter (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 : Fin n → AuthState ψ} {j : Nat} {γ : ProvColor} :
    ∀ (d t : Nat) (C : Fin n → AuthState ψ), j ≤ t → t + d + 2 ≤ ψ →
      Fw ring ψ g C0 C j γ t → Rch hp κ c ring C d (fun D => Fw ring ψ g C0 D j γ (t + d)) := by
  intro d
  induction d with
  | zero => intro t C _ _ hI; exact Rch_now hp κ c ring hI
  | succ d ih =>
    intro t C hjt hd hI
    have h := Rch_bind hp κ c ring (Fw_step hp κ c ring hg hjt (by omega) hI)
      (fun D hD => ih (t + 1) D (by omega) (by omega) hD)
    apply Rch_mono hp κ c ring (by omega) _ h
    intro D hD
    rwa [show t + 1 + d = t + (d + 1) by omega] at hD

/-- Backward invariant: cell `s` is a `done` link of colour `γ` pointing at
itself, cells `j..s-1` are pathless producers of colour `γ` without `path2`,
all other block cells are non-generation. -/
def Bw (ring : DirectedRing n) (ψ g : Nat) (C0 C : Fin n → AuthState ψ) (j : Nat)
    (γ : ProvColor) (s : Nat) : Prop :=
  1 ≤ s ∧ s + 2 ≤ ψ ∧ Std C ∧ Out ring ψ g C0 C ∧ (∀ k, k < j → NG (C (bcell ring ψ g k))) ∧
  (∀ k, j ≤ k → k < s → (C (bcell ring ψ g k)).core.state = .produce ∧
    (C (bcell ring ψ g k)).core.path = .bot ∧ (C (bcell ring ψ g k)).ctrl_mark = γ ∧
    (C (bcell ring ψ g k)).core.path2 = none) ∧
  ((C (bcell ring ψ g s)).core.state = .done ∧
    (∃ b, (C (bcell ring ψ g s)).core.path = .some s b) ∧
    (C (bcell ring ψ g s)).core.path2 = none ∧ (C (bcell ring ψ g s)).ctrl_mark = γ ∧
    (C (bcell ring ψ g s)).path_mark = γ) ∧
  (∀ k, s < k → k < ψ → NG (C (bcell ring ψ g k)))

/-- **Terminal edge (C2).** -/
theorem terminal_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {j t : Nat} {γ : ProvColor}
    (hjt : j < t) (ht : t + 2 = ψ) (hI : Fw ring ψ g C0 C j γ t) :
    Rch hp κ c ring C 1 (fun D => Bw ring ψ g C0 D j γ t) := by
  obtain ⟨hS, hO, hL, hM, hRt⟩ := hI
  apply Rch_mono hp κ c ring (Nat.le_refl _) _ (step_block hp κ c ring hg hS hO (k := t) (by omega))
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg (k := t) (by omega) hS
  obtain ⟨m1, m2, m3, m4⟩ := hM t (by omega) (Nat.le_refl _)
  obtain ⟨r1, r2⟩ := hRt (t + 1) (by omega) (by omega)
  obtain ⟨p1, -, -, p4⟩ := row_prop hp κ c _ _ t hR m1 m2
    (Or.inl ⟨by omega, r2, bot_of_noPo r1⟩)
  obtain ⟨d1, ⟨b, d2⟩, d3, d4, d5⟩ := p4 (by omega) (m4 hjt)
  refine ⟨by omega, by omega, hS', hO', ?_, ?_, ?_, ?_⟩
  · intro k hk; rw [eo k (by omega) (by omega) (by omega)]; exact hL k hk
  · intro k hk1 hk2
    rw [eo k (by omega) (by omega) (by omega)]
    obtain ⟨s1, s2, s3, s4⟩ := hM k hk1 (by omega)
    exact ⟨s1, s2, s3, s4 hjt⟩
  · rw [e1]; exact ⟨d1, ⟨b, d2⟩, d3, d4.trans m3, d5.trans m3⟩
  · intro k hk1 hk2
    obtain rfl : k = t + 1 := by omega
    rw [e2]; exact p1

/-- **Backward edge (C3).** -/
theorem back_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {j s : Nat} {γ : ProvColor}
    (hjs : j ≤ s) (hI : Bw ring ψ g C0 C j γ (s + 1)) :
    Rch hp κ c ring C 1
      (fun D => (s ≠ 0 → Bw ring ψ g C0 D j γ s) ∧ (s = 0 → Exit ring ψ g C0 D)) := by
  obtain ⟨_, hs2, hS, hO, hL, hM, ⟨c1, ⟨b, c2⟩, c3, c4, c5⟩, hRt⟩ := hI
  apply Rch_mono hp κ c ring (Nat.le_refl _) _ (step_block hp κ c ring hg hS hO (k := s) (by omega))
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg (k := s) (by omega) hS
  obtain ⟨m1, m2, m3, m4⟩ := hM s hjs (by omega)
  obtain ⟨p1, -, p3, p4⟩ := row_prop hp κ c _ _ s hR m1 m2
    (Or.inr ⟨by omega, c1, c4.trans m3.symm, c5.trans m3.symm, c3, b, c2⟩)
  refine ⟨fun hs0 => ?_, fun hs0 => ?_⟩
  · obtain ⟨d1, ⟨b', d2⟩, d3, d4, d5⟩ := p4 hs0 m4
    refine ⟨by omega, by omega, hS', hO', ?_, ?_, ?_, ?_⟩
    · intro k hk; rw [eo k (by omega) (by omega) (by omega)]; exact hL k hk
    · intro k hk1 hk2
      rw [eo k (by omega) (by omega) (by omega)]; exact hM k hk1 (by omega)
    · rw [e1]; exact ⟨d1, ⟨b', d2⟩, d3, d4.trans m3, d5.trans m3⟩
    · intro k hk1 hk2
      by_cases a : k = s + 1
      · subst a; rw [e2]; exact p1
      · rw [eo k hk2 (by omega) a]; exact hRt k (by omega) hk2
  · subst hs0
    refine ⟨hS', hO', Or.inr ?_⟩
    intro k hk
    by_cases a : k = 0
    · subst a; rw [e1]; exact p3 rfl
    · by_cases a' : k = 0 + 1
      · subst a'; rw [e2]; exact p1
      · rw [eo k hk a a']; exact hRt k (by omega) hk

theorem back_iter (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 : Fin n → AuthState ψ} {j : Nat} {γ : ProvColor} :
    ∀ (d : Nat) (C : Fin n → AuthState ψ), Bw ring ψ g C0 C j γ (j + d) →
      Rch hp κ c ring C d
        (fun D => (j ≠ 0 → Bw ring ψ g C0 D j γ j) ∧ (j = 0 → Exit ring ψ g C0 D)) := by
  intro d
  induction d with
  | zero =>
    intro C hI
    refine Rch_now hp κ c ring ⟨fun _ => hI, fun h0 => ?_⟩
    have := hI.1; omega
  | succ d ih =>
    intro C hI
    have h := Rch_bind hp κ c ring (back_step hp κ c ring hg (s := j + d) (Nat.le_add_right _ _) hI)
      (L2 := d)
      (Q := fun D => (j ≠ 0 → Bw ring ψ g C0 D j γ j) ∧ (j = 0 → Exit ring ψ g C0 D))
      (fun D ⟨hA, hB⟩ => by
        by_cases z : j + d = 0
        · have hj : j = 0 := by omega
          exact Rch_now hp κ c ring ⟨fun h => absurd hj h, fun _ => hB z⟩
        · exact ih D (hA z))
    exact Rch_mono hp κ c ring (by omega) (fun _ h => h) h

/-- Leftmost witness of a predicate on naturals. -/
theorem exists_min (P : Nat → Prop) : ∀ N, (∃ k, k < N ∧ P k) → ∃ j, P j ∧ ∀ k, k < j → ¬ P k := by
  intro N
  induction N with
  | zero => intro ⟨k, hk, _⟩; omega
  | succ N ih =>
    intro ⟨k, hk, hP⟩
    by_cases h : ∃ k, k < N ∧ P k
    · exact ih h
    · refine ⟨k, hP, fun k' hk' hP' => h ⟨k', by omega, hP'⟩⟩

/-- **Cleanup.** From a block with no occupied producer and no `done` cell,
at most `2ψ-3` block edges reach a leader, GenEntrance, or a block with no
generation cell. -/
theorem cleanup (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) (h2 : 2 ≤ ψ) {C0 C : Fin n → AuthState ψ}
    (hI : Cl ring ψ g C0 C) : Rch hp κ c ring C (2 * ψ - 3) (Exit ring ψ g C0) := by
  obtain ⟨hS, hO, hC⟩ := hI
  by_cases hP : ∃ k, k < ψ ∧ (C (bcell ring ψ g k)).core.state = .produce
  · obtain ⟨j, ⟨hj, hjP⟩, hmin⟩ := exists_min
      (fun k => k < ψ ∧ (C (bcell ring ψ g k)).core.state = .produce) ψ
      (by obtain ⟨k, hk, h⟩ := hP; exact ⟨k, hk, hk, h⟩)
    have hL : ∀ k, k < j → NG (C (bcell ring ψ g k)) := fun k hk =>
      ⟨fun h => hmin k hk ⟨by omega, h⟩, (hC k (by omega)).2⟩
    have hjb : (C (bcell ring ψ g j)).core.path = .bot := bot_of_noPo (hC j hj).1 hjP
    by_cases e1 : j = ψ - 1
    · -- the only producer is the terminal cell
      apply Rch_mono hp κ c ring (L := 1) (by omega) (fun _ h => h)
      apply rel_final hp κ c ring hg hS hO (j := j) (by omega) hj
      · intro k hk hkj; exact hL k (by omega)
      · intro _; exact ⟨hjb, e1⟩
    · by_cases e2 : j + 2 = ψ
      · -- terminal edge first, then release through `j-1`
        have hR := std_row ring hg (k := j) (by omega) hS
        have h := Rch_bind hp κ c ring (step_block hp κ c ring hg hS hO (k := j) (by omega))
          (L2 := if j = 0 then 0 else 1) (Q := Exit ring ψ g C0) (fun D ⟨hS', hO', f1, f2, fo⟩ => by
            obtain ⟨r1, r2⟩ := hC (j + 1) (by omega)
            obtain ⟨p1, p2, p3, -⟩ := row_prop hp κ c _ _ j hR hjP hjb
              (Or.inl ⟨by omega, r2, bot_of_noPo r1⟩)
            by_cases z : j = 0
            · subst z
              refine Rch_now hp κ c ring ⟨hS', hO', Or.inr fun k hk => ?_⟩
              by_cases a : k = 0
              · subst a; rw [f1]; exact p3 rfl
              · obtain rfl : k = 0 + 1 := by omega
                rw [f2]; exact p1
            · rw [if_neg z]
              apply rel_final hp κ c ring hg hS' hO' (j := j) (by omega) (by omega)
              · intro k hk hkj
                by_cases b : k = j + 1
                · subst b; rw [f2]; exact p1
                · rw [fo k hk hkj b]; exact hL k (by omega)
              · intro h; rw [f1] at h; exact absurd h p2)
        exact Rch_mono hp κ c ring (by split <;> omega) (fun _ h => h) h
      · -- forward, terminal, backward, release
        have hFw : Fw ring ψ g C0 C j (C (bcell ring ψ g j)).ctrl_mark j := by
          refine ⟨hS, hO, hL, ?_, ?_⟩
          · intro k hk1 hk2
            obtain rfl : k = j := by omega
            exact ⟨hjP, hjb, rfl, fun h => absurd h (Nat.lt_irrefl _)⟩
          · intro k _ hk; exact hC k hk
        have h1 := Rch_bind hp κ c ring
          (Fw_iter hp κ c ring hg (ψ - 2 - j) j C (Nat.le_refl _) (by omega) hFw)
          (fun D hD => terminal_step hp κ c ring hg (t := j + (ψ - 2 - j)) (by omega) (by omega) hD)
        have h2' := Rch_bind hp κ c ring h1
          (fun D hD => back_iter hp κ c ring hg (ψ - 2 - j) D hD)
        have h3 := Rch_bind hp κ c ring h2' (L2 := if j = 0 then 0 else 1)
          (Q := Exit ring ψ g C0) (fun D ⟨hA, hB⟩ => by
            by_cases z : j = 0
            · rw [if_pos z]; exact Rch_now hp κ c ring (hB z)
            · rw [if_neg z]
              obtain ⟨_, _, hS', hO', hL', _, ⟨c1, _⟩, hR'⟩ := hA z
              apply rel_final hp κ c ring hg hS' hO' (j := j) (by omega) (by omega)
              · intro k hk hkj
                rcases Nat.lt_or_gt_of_ne hkj with a | a
                · exact hL' k a
                · exact hR' k a hk
              · intro h; rw [c1] at h; cases h)
        exact Rch_mono hp κ c ring (by split <;> omega) (fun _ h => h) h3
  · refine Rch_now hp κ c ring ⟨hS, hO, Or.inr fun k hk => ⟨fun h => hP ⟨k, hk, h⟩, (hC k hk).2⟩⟩

end Cleanup

/-! ## Part L. Ngen and the headline theorems -/

section Headline
variable {n ψ : Nat}

open PPLLAuthResetDrain (authProtocol authRun authFplusmcc)

/-- A generation cell: `produce` or `done`. -/
def isGen (u : AuthState ψ) : Bool :=
  match u.core.state with
  | .produce => true
  | .done => true
  | _ => false

/-- `Ngen`: the number of cells of the ring in `produce` or `done`. -/
def Ngen (C : Fin n → AuthState ψ) : Nat := (List.finRange n).countP (fun i => isGen (C i))

/-- `Ngen_g`: the number of cells of block `g` in `produce` or `done`. -/
def NgenBlock (ring : DirectedRing n) (ψ g : Nat) (C : Fin n → AuthState ψ) : Nat :=
  (List.range ψ).countP (fun k => isGen (C (bcell ring ψ g k)))

theorem isGen_NG {u : AuthState ψ} (h : NG u) : isGen u = false := by
  obtain ⟨h1, h2⟩ := h
  unfold isGen
  split
  · rename_i hs; exact absurd hs h1
  · rename_i hs; exact absurd hs h2
  · rfl

theorem countP_le' {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, q x = true → p x = true) → l.countP q ≤ l.countP p := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    rw [List.countP_cons, List.countP_cons]
    have h1 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have h2 := h a List.mem_cons_self
    cases hq : q a <;> cases hp : p a <;> simp_all <;> omega

theorem countP_lt' {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, q x = true → p x = true) → (∃ x ∈ l, p x = true ∧ q x = false) →
      l.countP q < l.countP p := by
  intro l
  induction l with
  | nil => intro _ ⟨x, hx, _⟩; simp at hx
  | cons a l ih =>
    intro h ⟨x, hx, hpx, hqx⟩
    rw [List.countP_cons, List.countP_cons]
    have hle := countP_le' p q l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have h2 := h a List.mem_cons_self
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [hpx, hqx]; simp; omega
    · have h1 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) ⟨x, hx', hpx, hqx⟩
      cases hq : q a <;> cases hp : p a <;> simp_all <;> omega

theorem countP_pos' {α : Type} (p : α → Bool) :
    ∀ l : List α, 0 < l.countP p ↔ ∃ x ∈ l, p x = true := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons]
    constructor
    · intro h
      cases hp : p a
      · rw [hp] at h
        obtain ⟨x, hx, hpx⟩ := ih.mp (by simpa using h)
        exact ⟨x, List.mem_cons_of_mem _ hx, hpx⟩
      · exact ⟨a, List.mem_cons_self, hp⟩
    · intro ⟨x, hx, hpx⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [hpx]; simp
      · have := ih.mpr ⟨x, hx', hpx⟩; omega

/-- Emptying block `g` while keeping every other cell strictly lowers `Ngen`,
provided block `g` had a generation cell. -/
theorem Ngen_drop (ring : DirectedRing n) {g : Nat} {C0 C : Fin n → AuthState ψ}
    (hO : Out ring ψ g C0 C) (hA : AllNG ring ψ g C) (hN : 0 < NgenBlock ring ψ g C0) :
    Ngen C < Ngen C0 := by
  obtain ⟨k, hk, hgk⟩ := (countP_pos' _ _).mp hN
  have hk' : k < ψ := List.mem_range.mp hk
  apply countP_lt'
  · intro i _ hi
    by_cases hin : ∃ k, k < ψ ∧ i = bcell ring ψ g k
    · obtain ⟨k', hk'', rfl⟩ := hin
      rw [isGen_NG (hA k' hk'')] at hi; cases hi
    · rw [← hO i (fun k' hk'' he => hin ⟨k', hk'', he⟩)]; exact hi
  · exact ⟨bcell ring ψ g k, List.mem_finRange _, hgk, isGen_NG (hA k hk')⟩

theorem len_arith (h2 : 2 ≤ ψ) :
    (ψ - 1) + (ψ - 2) * (ψ - 2) + (2 * ψ - 3) ≤ ψ * ψ - 2 := by
  obtain ⟨p, rfl⟩ : ∃ p, ψ = p + 2 := ⟨ψ - 2, by omega⟩
  rw [show p + 2 - 2 = p by omega]
  have e : (p + 2) * (p + 2) = p * p + 4 * p + 4 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  rw [e]
  generalize p * p = q
  omega

/-- **GEN-DRAIN, block form.** Let `ψ ≥ 2` and let block `g` (cells
`gψ, …, gψ+ψ-1`) lie inside the ring. From a leaderless, reset-free AuthF
configuration with perfect labels whose block `g` has a cell in `produce` or
`done`, some word of at most `ψ²-2` interactions (all on edges of block `g`)
reaches a configuration with a leader, or one satisfying GenEntrance for block
`g`, or one with strictly smaller `Ngen`. The word is
`W_B = F ++ R^(ψ-2)` followed by the cleanup from the leftmost producer, of
length at most `(ψ-1) + (ψ-2)² + (2ψ-3) = ψ² - ψ`. `echo` is arbitrary; the
statement holds for every AuthF configuration `c`, in particular
`authFplusmcc`. -/
theorem genDrain_block (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (g : Nat) (hg : g * ψ + ψ ≤ n) (C : Fin n → AuthState ψ)
    (hL : ∀ i, (C i).core.leader = false) (hR : ∀ i, (C i).core.reset_cmd = false)
    (hPL : ∀ i, (C i).core.label.val = i.val % ψ) (hN : 0 < NgenBlock ring ψ g C) :
    ∃ w : List (Fin n), w.length ≤ ψ * ψ - 2 ∧
      ((∃ i, (authRun hp κ c ring C w i).core.leader = true) ∨
        GenEntrance ring ψ g (authRun hp κ c ring C w) ∨
        Ngen (authRun hp κ c ring C w) < Ngen C) := by
  have hS : Std C := fun i => ⟨hL i, hR i, hPL i⟩
  have hO : Out ring ψ g C C := fun _ _ => rfl
  have h := Rch_bind hp κ c ring (phaseW hp κ c ring hg h2 hS hO)
    (fun D hD => cleanup hp κ c ring hg h2 hD)
  obtain ⟨w, hw, hE⟩ := h
  refine ⟨w, Nat.le_trans hw (len_arith h2), ?_⟩
  rcases hE with hLd | ⟨_, hO', hGE | hA⟩
  · exact Or.inl hLd
  · exact Or.inr (Or.inl hGE)
  · exact Or.inr (Or.inr (Ngen_drop ring hO' hA hN))

/-- `genDrain_block` for the AuthF variant `authFplusmcc`. -/
theorem genDrain_block_mcc (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (g : Nat) (hg : g * ψ + ψ ≤ n) (C : Fin n → AuthState ψ)
    (hL : ∀ i, (C i).core.leader = false) (hR : ∀ i, (C i).core.reset_cmd = false)
    (hPL : ∀ i, (C i).core.label.val = i.val % ψ) (hN : 0 < NgenBlock ring ψ g C) :
    ∃ w : List (Fin n), w.length ≤ ψ * ψ - 2 ∧
      ((∃ i, (authRun hp κ authFplusmcc ring C w i).core.leader = true) ∨
        GenEntrance ring ψ g (authRun hp κ authFplusmcc ring C w) ∨
        Ngen (authRun hp κ authFplusmcc ring C w) < Ngen C) :=
  genDrain_block hp κ authFplusmcc ring h2 g hg C hL hR hPL hN

/-- **GEN-DRAIN, global form.** With `ψ ∣ n`, a leaderless, reset-free,
perfectly labelled AuthF configuration with `Ngen > 0` has a block `g` with
`Ngen_g > 0` and a word of at most `ψ²-2` interactions reaching a leader,
GenEntrance for block `g`, or strictly smaller `Ngen`. -/
theorem genDrain_global (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (C : Fin n → AuthState ψ)
    (hL : ∀ i, (C i).core.leader = false) (hR : ∀ i, (C i).core.reset_cmd = false)
    (hPL : ∀ i, (C i).core.label.val = i.val % ψ) (hN : 0 < Ngen C) :
    ∃ g, g * ψ + ψ ≤ n ∧ 0 < NgenBlock ring ψ g C ∧
      ∃ w : List (Fin n), w.length ≤ ψ * ψ - 2 ∧
        ((∃ i, (authRun hp κ c ring C w i).core.leader = true) ∨
          GenEntrance ring ψ g (authRun hp κ c ring C w) ∨
          Ngen (authRun hp κ c ring C w) < Ngen C) := by
  obtain ⟨i, _, hi⟩ := (countP_pos' _ _).mp hN
  obtain ⟨m, hm⟩ := hd
  have hdm := Nat.div_add_mod i.val ψ
  have hlt : i.val / ψ < m := (Nat.div_lt_iff_lt_mul hp).mpr (by rw [Nat.mul_comm, ← hm]; exact i.isLt)
  have hg : i.val / ψ * ψ + ψ ≤ n := by
    have := Nat.mul_le_mul_right ψ (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this
    have hm' : n = m * ψ := by rw [hm, Nat.mul_comm]
    omega
  have hk : i.val % ψ < ψ := Nat.mod_lt _ hp
  have hcell : bcell ring ψ (i.val / ψ) (i.val % ψ) = i := by
    apply Fin.ext
    show (i.val / ψ * ψ + i.val % ψ) % n = i.val
    rw [Nat.mul_comm, hdm]; exact Nat.mod_eq_of_lt i.isLt
  have hNb : 0 < NgenBlock ring ψ (i.val / ψ) C :=
    (countP_pos' _ _).mpr ⟨i.val % ψ, List.mem_range.mpr hk, by rw [hcell]; exact hi⟩
  exact ⟨i.val / ψ, hg, hNb, genDrain_block hp κ c ring h2 _ hg C hL hR hPL hNb⟩

end Headline

#print axioms genDrain_block
#print axioms genDrain_block_mcc
#print axioms genDrain_global

end PPLLAuthGenDrain
