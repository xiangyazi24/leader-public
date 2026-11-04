import Leader.Wu.Authorization.ProvenanceMarks
import Leader.Wu.ZeroDivisible.ReadyAckResetDebt
/-! Draining reset debt on the AuthF ring (Z-div liveness, stage 1).

Transfer of `PPLLAstraReadyResetDrain.exists_reset_free_or_positive` from the
ReadyAck pipeline to `PPLLAuthF.pipeline` (every configuration `c : Cfg`, in
particular `authFplusmcc`). From an arbitrary configuration of `AuthState`s on a
directed ring with `n ≥ 2` cells, some physical word reaches a configuration that
has a leader or holds no `reset_cmd` at all. No hypothesis on labels, echoes,
provenance marks or any other field is used.

## Why the ReadyAck argument transfers

The ring argument (sweep, walk, kill) reads only four facts about one
interaction with a follower initiator:

* `pipeline_follower_reset`: the initiator leaves reset-free and the responder
  holds `(l.reset ∨ r.reset) ∧ ¬ r.echo`;
* `pipeline_terminal_echo`: against a responder that P′ labels terminal, reset
  debt gives the initiator an echo;
* `pipeline_echo_walk`: with no reset on either side a responder echo moves to
  the initiator;
* `pipeline_follower_labels`: on a follower pair whose responder stays a
  follower, the responder label becomes `label(l)+1 mod ψ`.

All four are consequences of the following frame facts, proved here stage by
stage for AuthF:

1. Every AuthF stage between P′ and Algorithm 14 preserves `reset_cmd`, `echo`
   and `label` on both endpoints and `leader` on the initiator; the responder's
   `leader` can only be switched on (CHECK's terminal birth in
   `checkSourceAuth`, the BEQ birth in `landForward`). No AuthF stage writes
   `reset_cmd` or `echo`: `PPLLAuthF.lean` only reads them (lines 677, 679,
   683), and every core function it calls writes neither (checked below by the
   frame lemmas, each of which unfolds the callee). The AuthF-only writes are
   `clearCmpAuth`, which clears comparison fields and marks but is `clearCmp` on
   the core, and mark/`path*`/`state` updates.
2. `suppressSigResetKillAuth` acts on cores exactly as ReadyAck's
   `suppressSigResetKill` (`suppress_core`): its `kill` uses `clearCmpAuth`,
   whose core is `clearCmp`.
3. K4, WRITE and `conserveAuth` act on cores as ReadyAck's suffix
   (`pipeline_core`), so `PPLLAstraReadyResetDebtR.Writer.suffix_fields` applies
   verbatim.

The echo created by `suppressSigTerminal` without clearing `reset_cmd`
is exactly the echo birth used by the walk phase; the
argument is positional (sweep order, then one walking reset, then an echo walk)
and never uses a monotone count, so that remark does not obstruct it.
-/
namespace PPLLAuthResetDrain
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
  PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
set_option linter.unusedSimpArgs false

/-! ### Views -/

/-- The drain view of a core: reset bit, echo bit, label, leader bit. -/
def dv {ψ : Nat} (u : AgentState ψ) : Bool × Bool × Fin ψ × Bool :=
  (u.reset_cmd, u.echo, u.label, u.leader)

/-- The drain view without the leader bit. -/
def wv {ψ : Nat} (u : AgentState ψ) : Bool × Bool × Fin ψ :=
  (u.reset_cmd, u.echo, u.label)

/-- The drain view of an AuthF cell is that of its core. -/
def av {ψ : Nat} (u : AuthState ψ) : Bool × Bool × Fin ψ × Bool := dv u.core

/-- Frame relation of one stage `(l,r) ↦ (l',r')`: the initiator keeps its drain
view, the responder keeps reset/echo/label and can only gain leadership. -/
def FR {ψ : Nat} (l r l' r' : AuthState ψ) : Prop :=
  av l' = av l ∧ wv r'.core = wv r.core ∧ (r.core.leader = true → r'.core.leader = true)

theorem FR_trans {ψ : Nat} {l r l1 r1 l2 r2 : AuthState ψ}
    (h1 : FR l r l1 r1) (h2 : FR l1 r1 l2 r2) : FR l r l2 r2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun h => h2.2.2 (h1.2.2 h)⟩

/-- A stage that preserves the full drain view on both sides is a frame. -/
theorem FR_of_av {ψ : Nat} {l r l' r' : AuthState ψ}
    (h1 : av l' = av l) (h2 : av r' = av r) : FR l r l' r' := by
  simp only [av, dv, Prod.mk.injEq] at h2
  refine ⟨h1, ?_, ?_⟩
  · simp only [wv, h2.1, h2.2.1, h2.2.2.1]
  · intro h; rw [h2.2.2.2]; exact h

section Ite
variable {ψ : Nat}
theorem fst_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
theorem snd_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
theorem core_ite (p : Prop) [Decidable p] (a b : AuthState ψ) :
    (if p then a else b).core = if p then a.core else b.core := by split <;> rfl
theorem reset_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).reset_cmd = if p then a.reset_cmd else b.reset_cmd := by split <;> rfl
theorem echo_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).echo = if p then a.echo else b.echo := by split <;> rfl
theorem label_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).label = if p then a.label else b.label := by split <;> rfl
theorem leader_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).leader = if p then a.leader else b.leader := by split <;> rfl
theorem dv_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    dv (if p then a else b) = if p then dv a else dv b := by split <;> rfl
theorem av_ite (p : Prop) [Decidable p] (a b : AuthState ψ) :
    av (if p then a else b) = if p then av a else av b := by split <;> rfl
end Ite

/-! ### Core (AgentState) stages called by AuthF

Each lemma unfolds the callee; together they are the exhaustive check that no
core function reachable from the AuthF comparison prefix writes `reset_cmd`,
`echo`, `label` or (except the two responder births) `leader`. -/

section CoreStages
variable {ψ : Nat}

theorem clearCmp_dv (u : AgentState ψ) : dv (clearCmp u) = dv u := rfl

theorem wait_dv (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    dv (waitSaturated hψ κ l r).1 = dv l ∧ dv (waitSaturated hψ κ l r).2 = dv r := by
  simp only [waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish]
  simp only [fst_ite, snd_ite, dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite,
    ite_self, and_self]

theorem genConnect_dv (u : AgentState ψ) : dv (cleanSigGenConnect u) = dv u := by
  cases h : u.path <;> simp only [cleanSigGenConnect, h] <;>
    simp [dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

theorem releaseSource_dv (hψ : ψ > 0) (l r : AgentState ψ) :
    dv (releaseSource hψ l r).1 = dv l ∧ dv (releaseSource hψ l r).2 = dv r := by
  simp [releaseSource, fst_ite, snd_ite, dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

theorem eliminate_dv (hψ : ψ > 0) (l r : AgentState ψ) :
    dv (eliminateSig hψ l r).1 = dv l ∧ dv (eliminateSig hψ l r).2 = dv r := by
  simp [eliminateSig, fst_ite, snd_ite, dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

theorem control_dv (hψ : ψ > 0) (u : AgentState ψ) :
    dv (sigMoveApplyControlConsume hψ u) = dv u := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;>
    simp [dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

theorem dropStale_dv (u : AgentState ψ) : dv (dropStale u) = dv u := by
  simp [dropStale, dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

theorem orphan_dv (u : AgentState ψ) : dv (normalizeOrphan u) = dv u := by
  cases h : u.path <;> simp [normalizeOrphan, h, dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

theorem carrier_dv (u : AgentState ψ) : dv (normalizeCarrier u) = dv u := by
  cases h : u.path <;>
    simp [normalizeCarrier, releaseCongest, h, dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

theorem ready_dv (u : AgentState ψ) : dv (normalizeReady u) = dv u := by
  generalize ho : normalizeOrphan u = o
  have vo : dv o = dv u := by rw [← ho]; exact orphan_dv u
  simp only [normalizeReady, ho]
  generalize hc : (if o.state = .none ∧ aligned o then o else normalizeCarrier o) = c
  have vc : dv c = dv o := by rw [← hc]; simp [dv_ite, carrier_dv]
  have ht := vc.trans vo
  cases hp : c.path <;> simpa [hp, dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite] using ht

theorem checkReady_dv (u : AgentState ψ) : dv (checkSigSetReadyGuarded u) = dv u := by
  cases h : u.path <;>
    simp [checkSigSetReadyGuarded, checkSigSetReady, h, dv_ite, dv, reset_ite, echo_ite,
      label_ite, leader_ite]

theorem checkL_dv (hψ : ψ > 0) (u : AgentState ψ) : dv (checkSigCheckL hψ u) = dv u := by
  unfold checkSigCheckL
  split <;> simp [dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

theorem checkR_dv (hψ : ψ > 0) (l r : AgentState ψ) : dv (checkSigCheckR hψ l r) = dv r := by
  unfold checkSigCheckR
  split <;> simp [dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

theorem result_dv (u : AgentState ψ) : dv (checkSigSetResult u) = dv u := by
  simp [checkSigSetResult, dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

theorem disStart_dv (hψ : ψ > 0) (l r : AgentState ψ) :
    dv (disappearStartL hψ l r).1 = dv l ∧ dv (disappearStartL hψ l r).2 = dv r := by
  simp [disappearStartL, fst_ite, snd_ite, dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

theorem disCarry_dv (hψ : ψ > 0) (l r : AgentState ψ) :
    dv (disappearCarry hψ l r).1 = dv l ∧ dv (disappearCarry hψ l r).2 = dv r := by
  simp [disappearCarry, fst_ite, snd_ite, dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

theorem releaseSuffix_dv (l r : AgentState ψ) :
    dv (releaseReadySuffix l r).1 = dv l ∧ dv (releaseReadySuffix l r).2 = dv r := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [releaseReadySuffix, hl, hr, fst_ite, snd_ite, dv_ite, dv, reset_ite, echo_ite,
      label_ite, leader_ite]

theorem ackTail_dv (l r : AgentState ψ) :
    dv (ackTail l r).1 = dv l ∧ dv (ackTail l r).2 = dv r := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [ackTail, hl, hr, fst_ite, snd_ite, dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

theorem dropStray_dv (l r : AgentState ψ) :
    dv (dropStray l r).1 = dv l ∧ dv (dropStray l r).2 = dv r := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [dropStray, hl, hr, fst_ite, snd_ite, dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

theorem landBackward_dv (u : AgentState ψ) : dv (landBackward u) = dv u := by
  cases hp : u.path <;> cases ht : u.path2 <;>
    simp [landBackward, hp, ht, dv_ite, dv, reset_ite, echo_ite, label_ite, leader_ite]

/-- The BEQ landing may set the responder's leader bit (equality birth) and
touches no other drain field. -/
theorem landForward_wv (κ : Nat) (u : AgentState ψ) :
    wv (landForward κ false true u) = wv u := by
  cases hp : u.path <;> cases ht : u.path2 <;>
    simp [landForward, hp, ht, wv, reset_ite, echo_ite, label_ite]

theorem landForward_leader (κ : Nat) (u : AgentState ψ) (h : u.leader = true) :
    (landForward κ false true u).leader = true := by
  cases hp : u.path <;> cases ht : u.path2 <;> simp [landForward, hp, ht, leader_ite, h]

/-- P′ keeps the reset and echo bits of both endpoints and the initiator's
leader bit. -/
theorem pPsi_bits (hψ : ψ > 0) (l r : AgentState ψ) :
    (pPsiProbeWall hψ l r).1.reset_cmd = l.reset_cmd ∧ (pPsiProbeWall hψ l r).1.echo = l.echo ∧
    (pPsiProbeWall hψ l r).2.reset_cmd = r.reset_cmd ∧ (pPsiProbeWall hψ l r).2.echo = r.echo ∧
    (pPsiProbeWall hψ l r).1.leader = l.leader := by
  simp only [pPsiProbeWall, pPsi]
  simp [fst_ite, snd_ite, reset_ite, echo_ite, leader_ite]

end CoreStages

/-! ### Lifts and small AuthF cell maps

Small maps are handled by splitting every `if`/`match` and closing each leaf,
which is a record update of the input cell (or a core function with a frame
lemma above). -/

/-- Close a leaf goal of a frame lemma. -/
syntax "fclose" : tactic
macro_rules
  | `(tactic| fclose) => `(tactic| first
      | exact ⟨rfl, rfl⟩
      | rfl
      | (simp only [av, AuthState.withCore, AuthState.dropP2, AuthState.setState,
          AuthState.lineage, clearCmpAuth, genConnect_dv, control_dv, checkReady_dv,
          checkL_dv, checkR_dv, result_dv, landBackward_dv, and_self, and_true, true_and];
         first | done | rfl | exact ⟨rfl, rfl⟩))

/-- Split every `if`/`match` (zeta-reducing `let`s first) and close all leaves. -/
syntax "fsplit" : tactic
macro_rules
  | `(tactic| fsplit) => `(tactic| ((repeat' (first | (dsimp only) | split)) <;> fclose))

section AuthCells
variable {ψ : Nat}

theorem clearCmpAuth_core (u : AuthState ψ) : (clearCmpAuth u).core = clearCmp u.core := rfl
theorem dv_core (u : AuthState ψ) : dv u.core = av u := rfl
theorem av_mk (c : AgentState ψ) (a b : ProvColor) (s : P2Scope) (d e f : ProvColor) :
    av (AuthState.mk c a b s d e f) = dv c := rfl
theorem wv_av (u : AuthState ψ) : wv u.core = ((av u).1, (av u).2.1, (av u).2.2.1) := rfl
theorem leader_av (u : AuthState ψ) : u.core.leader = (av u).2.2.2 := rfl
theorem dv_p4 (u : AgentState ψ) : dv { u with path4 := none } = dv u := rfl
theorem dv_p5 (u : AgentState ψ) : dv { u with path5 := none } = dv u := rfl
theorem wv_leader (u : AgentState ψ) (b : Bool) : wv { u with leader := b } = wv u := rfl
theorem wv_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    wv (if p then a else b) = if p then wv a else wv b := by split <;> rfl

theorem lift2_av (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, dv (f a b).1 = dv a ∧ dv (f a b).2 = dv b) (l r : AuthState ψ) :
    av (lift2 f l r).1 = av l ∧ av (lift2 f l r).2 = av r :=
  hf l.core r.core

theorem lift2Life_av (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, dv (f a b).1 = dv a ∧ dv (f a b).2 = dv b) (l r : AuthState ψ) :
    av (lift2Life f l r).1 = av l ∧ av (lift2Life f l r).2 = av r := by
  have h := hf l.core r.core
  unfold lift2Life
  dsimp only
  refine ⟨?_, ?_⟩ <;> split
  all_goals first | exact h.1 | exact h.2

theorem liftLife_av (f : AgentState ψ → AgentState ψ) (hf : ∀ a, dv (f a) = dv a)
    (u : AuthState ψ) : av (liftLife f u) = av u := by
  unfold liftLife
  dsimp only
  split <;> exact hf u.core

theorem clearAuth_av (u : AuthState ψ) : av (clearCmpAuth u) = av u := rfl
theorem dropP2_av (u : AuthState ψ) : av u.dropP2 = av u := rfl
theorem setState_av (u : AuthState ψ) (s : MainState) : av (u.setState s) = av u := rfl
theorem lineage_av (u : AuthState ψ) (s : MainState) : av (u.lineage s) = av u := rfl
theorem withCore_av (u : AuthState ψ) (c : AgentState ψ) : av (u.withCore c) = dv c := rfl
theorem wipe_av (γ : ProvColor) (u : AuthState ψ) : av (wipeProduceAuth γ u) = av u := rfl
theorem demote_av (u : AuthState ψ) : av (demote u) = av u := rfl
theorem claimA2_av (σ : ProvColor) (u : AuthState ψ) : av (claimA2 σ u) = av u := rfl

theorem receive_av (e : Entry) (src dst : AuthState ψ) (t : Path2Info) :
    av (receive e src dst t) = av dst := by
  show dv (if e = .claim then claimA2 src.path2_mark dst else dst).core = dv dst.core
  split <;> rfl

theorem sanitize_av (u : AuthState ψ) : av (sanitizeP2 u) = av u := by
  unfold sanitizeP2; fsplit

theorem issue_av (u : AuthState ψ) : av (issue u) = av u := by
  unfold issue; fsplit

theorem readyAuth_av (u : AuthState ψ) : av (readyAuth u) = av u := by
  unfold readyAuth; fsplit

theorem applyControl_av (hψ : ψ > 0) (u : AuthState ψ) : av (applyControlAuth hψ u) = av u := by
  unfold applyControlAuth; fsplit

theorem genConnectAuth_av (u : AuthState ψ) : av (genConnectAuth u) = av u := by
  unfold genConnectAuth; fsplit

theorem landBackwardAuth_av (u : AuthState ψ) : av (landBackwardAuth u) = av u := by
  unfold landBackwardAuth; fsplit

theorem landForwardAuth_wv (κ : Nat) (u : AuthState ψ) :
    wv (landForwardAuth κ u).core = wv u.core ∧
      (u.core.leader = true → (landForwardAuth κ u).core.leader = true) := by
  unfold landForwardAuth
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact ⟨rfl, id⟩
    | exact ⟨landForward_wv κ u.core, landForward_leader κ u.core⟩

theorem cleanApplyAuth_av (u : AuthState ψ) : av (cleanApplyAuth u) = av u := by
  unfold cleanApplyAuth; fsplit

end AuthCells

/-! ### The AuthF comparison prefix, stage by stage -/

section AuthStages
variable {ψ : Nat}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem genSig_av (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) :
    av (genSigAuth hψ κ l r).1 = av l ∧ av (genSigAuth hψ κ l r).2 = av r := by
  have hw := lift2_av (waitSaturated hψ κ) (wait_dv hψ κ) l r
  unfold genSigAuth
  generalize lift2 (waitSaturated hψ κ) l r = q at hw ⊢
  obtain ⟨q1, q2⟩ := q
  dsimp only at hw ⊢
  rw [← hw.1, ← hw.2]
  fsplit

theorem step3_av (nbr mc : Bool) (l r : AuthState ψ) :
    av (step3Auth nbr mc l r).1 = av l ∧ av (step3Auth nbr mc l r).2 = av r := by
  unfold step3Auth; fsplit

theorem step4_av (nbr mc : Bool) (l r : AuthState ψ) :
    av (step4Auth nbr mc l r).1 = av l ∧ av (step4Auth nbr mc l r).2 = av r := by
  unfold step4Auth; fsplit

theorem step5_av (hψ : ψ > 0) (l r : AuthState ψ) :
    av (step5Auth hψ l r).1 = av l ∧ av (step5Auth hψ l r).2 = av r := by
  unfold step5Auth; fsplit

theorem step6_av (hψ : ψ > 0) (l r : AuthState ψ) :
    av (step6Auth hψ l r).1 = av l ∧ av (step6Auth hψ l r).2 = av r := by
  unfold step6Auth; fsplit

/-- The simp set that rewrites a composite AuthF stage down to its input view. -/
theorem cleanSource_av (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    av (cleanSourceAuth hψ c l r).1 = av l ∧ av (cleanSourceAuth hψ c l r).2 = av r := by
  simp only [cleanSourceAuth, fst_ite, snd_ite, av_ite, av_mk, dv_p4, dv_p5, dv_core, cleanApplyAuth_av,
    step6_av, step5_av, step4_av, step3_av, genConnectAuth_av, ite_self, and_self]

theorem validate_av (l r : AuthState ψ) :
    av (validateCheck l r).1 = av l ∧ av (validateCheck l r).2 = av r := by
  unfold validateCheck; fsplit

theorem step1_av (l r : AuthState ψ) :
    av (step1Auth l r).1 = av l ∧ av (step1Auth l r).2 = av r := by
  unfold step1Auth; fsplit

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem moveTokens_av (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    av (moveTokensAuth c l r).1 = av l ∧ av (moveTokensAuth c l r).2 = av r := by
  cases h1 : l.core.path2 <;> cases h2 : r.core.path2 <;>
    simp only [moveTokensAuth, h1, h2] <;>
    (repeat' (first | (dsimp only) | split)) <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact ⟨receive_av _ _ _ _, receive_av _ _ _ _⟩
      | exact ⟨rfl, receive_av _ _ _ _⟩
      | exact ⟨receive_av _ _ _ _, rfl⟩
      | fclose

theorem leaderWall_av (l r : AuthState ψ) :
    av (leaderWallAuth l r).1 = av l ∧ av (leaderWallAuth l r).2 = av r := by
  unfold leaderWallAuth; fsplit

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem moveSource_av (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    av (moveSourceAuth hψ c l r).1 = av l ∧ av (moveSourceAuth hψ c l r).2 = av r := by
  simp only [moveSourceAuth, fst_ite, snd_ite, av_ite, lineage_av, applyControl_av,
    leaderWall_av, moveTokens_av, step1_av, sanitize_av, validate_av, clearAuth_av,
    ite_self, and_self]

theorem preCheck_av (l r : AuthState ψ) :
    av (preCheckResetAuth l r).1 = av l ∧ av (preCheckResetAuth l r).2 = av r := by
  unfold preCheckResetAuth; fsplit

/-- The simp set for CHECK's stages below the final birth. -/
theorem checkSource_left (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    av (checkSourceAuth hψ c l r).1 = av l := by
  simp only [checkSourceAuth, fst_ite, snd_ite, av_ite, av_mk, dv_core, withCore_av, lineage_av,
    issue_av, readyAuth_av, checkL_dv, checkR_dv, checkReady_dv, validate_av, ite_self]

/-- The terminal birth of CHECK keeps reset/echo/label. -/
theorem birth_wv (C : Prop) [Decidable C] (B : AuthState ψ) :
    wv (if C then { B with core := { B.core with leader := true } } else B).core = wv B.core := by
  split <;> rfl

theorem birth_leader (C : Prop) [Decidable C] (B : AuthState ψ) (h : B.core.leader = true) :
    (if C then { B with core := { B.core with leader := true } } else B).core.leader = true := by
  split
  · rfl
  · exact h

/-- CHECK: the initiator keeps its drain view; the responder keeps
reset/echo/label and can only become a leader (terminal equality birth). -/
theorem checkSource_FR (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    FR l r (checkSourceAuth hψ c l r).1 (checkSourceAuth hψ c l r).2 := by
  refine ⟨checkSource_left hψ c l r, ?_, ?_⟩
  · simp only [checkSourceAuth, snd_ite]
    rw [birth_wv, wv_av, wv_av]
    simp only [av_ite, av_mk, dv_core, withCore_av, lineage_av, issue_av, readyAuth_av, checkL_dv,
      checkR_dv, checkReady_dv, validate_av, ite_self]
  · intro h
    simp only [checkSourceAuth, snd_ite]
    apply birth_leader
    rw [leader_av]
    simp only [av_ite, av_mk, dv_core, withCore_av, lineage_av, issue_av, readyAuth_av, checkL_dv,
      checkR_dv, checkReady_dv, validate_av, ite_self]
    exact h

theorem disappear_av (hψ : ψ > 0) (l r : AuthState ψ) :
    av (disappearAuth hψ l r).1 = av l ∧ av (disappearAuth hψ l r).2 = av r := by
  have h1 := lift2_av (disappearStartL hψ) (disStart_dv hψ)
  have h2 := lift2_av (disappearCarry hψ) (disCarry_dv hψ)
  unfold disappearAuth
  dsimp only
  split <;> simp only [h2, h1, true_and, and_self]
  all_goals fclose

theorem repair_av (l r : AuthState ψ) :
    av (repairAuth l r).1 = av l ∧ av (repairAuth l r).2 = av r := by
  have hc : ∀ a : AgentState ψ, dv (normalizeCarrier (normalizeOrphan a)) = dv a :=
    fun a => (carrier_dv _).trans (orphan_dv a)
  have hl := liftLife_av _ hc
  have hr := lift2Life_av (ψ := ψ) releaseReadySuffix releaseSuffix_dv
  have ha : ∀ a b : AuthState ψ, av (ackTailAuth a b).1 = av a ∧ av (ackTailAuth a b).2 = av b := by
    intro a b
    unfold ackTailAuth; split
    · exact lift2_av ackTail ackTail_dv a b
    · exact ⟨rfl, rfl⟩
  simp only [repairAuth, ha, hr, hl, and_self]

theorem maintain_av (l r : AuthState ψ) :
    av (maintainAuth l r).1 = av l ∧ av (maintainAuth l r).2 = av r := by
  unfold maintainAuth; fsplit

theorem completeWave_av (l r : AuthState ψ) :
    av (completeWaveAuth l r).1 = av l ∧ av (completeWaveAuth l r).2 = av r := by
  unfold completeWaveAuth; fsplit

theorem wave_av (l r : AuthState ψ) :
    av (waveAuth l r).1 = av l ∧ av (waveAuth l r).2 = av r := by
  unfold waveAuth; fsplit

/-- Comparison lifecycle: the initiator keeps its drain view; the responder can
only gain leadership (BEQ equality birth in `landForward`). -/
theorem compare_FR (κ : Nat) (l r : AuthState ψ) :
    FR l r (compareLifecycleAuth κ l r).1 (compareLifecycleAuth κ l r).2 := by
  have hd := lift2_av (ψ := ψ) dropStray dropStray_dv
  unfold compareLifecycleAuth
  dsimp only
  split
  all_goals (try split)
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals first
    | (simp only [landBackwardAuth_av, hd, wave_av, completeWave_av, maintain_av, setState_av]; done)
    | (rw [(landForwardAuth_wv κ _).1]
       simp only [wv_av, hd, wave_av, completeWave_av, maintain_av, setState_av]; done)
    | (intro h; apply (landForwardAuth_wv κ _).2
       rw [leader_av]
       simp only [hd, wave_av, completeWave_av, maintain_av, setState_av]
       rw [← leader_av]; exact h)

end AuthStages

/-! ### The prefix, Algorithm 14, and the suffix on cores -/

/-- The AuthF stages strictly between P′ and Algorithm 14. -/
def mid {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let q := genSigAuth hψ κ l r
  let q := cleanSourceAuth hψ c q.1 q.2
  let q := lift2Life (releaseSource hψ) q.1 q.2
  let q := lift2 (eliminateSig hψ) q.1 q.2
  let q := moveSourceAuth hψ c q.1 q.2
  let q := (liftLife dropStale q.1, liftLife dropStale q.2)
  let q := preCheckResetAuth q.1 q.2
  let q := (liftLife normalizeReady q.1, liftLife normalizeReady q.2)
  let q := checkSourceAuth hψ c q.1 q.2
  let q := disappearAuth hψ q.1 q.2
  let q := repairAuth q.1 q.2
  compareLifecycleAuth κ q.1 q.2

/-- The AuthF prefix ending just before Algorithm 14. -/
def beforeSuppressAuth {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let q := lift2 (pPsiProbeWall hψ) l r
  mid hψ κ c q.1 q.2

theorem beforeElimination_eq {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    PPLLAuthF.beforeElimination hψ κ c l r =
      suppressSigResetKillAuth hψ (beforeSuppressAuth hψ κ c l r).1
        (beforeSuppressAuth hψ κ c l r).2 := rfl

/-- The stages between P′ and Algorithm 14 are a frame (`FR`). -/
theorem mid_FR {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    FR l r (mid hψ κ c l r).1 (mid hψ κ c l r).2 := by
  simp only [mid]
  have h1 := genSig_av hψ κ l r
  generalize genSigAuth hψ κ l r = q1 at h1
  obtain ⟨a1, b1⟩ := q1
  simp only at h1 ⊢
  have h2 := cleanSource_av hψ c a1 b1
  generalize cleanSourceAuth hψ c a1 b1 = q2 at h2
  obtain ⟨a2, b2⟩ := q2
  simp only at h2 ⊢
  have h3 := lift2Life_av (releaseSource hψ) (releaseSource_dv hψ) a2 b2
  generalize lift2Life (releaseSource hψ) a2 b2 = q3 at h3
  obtain ⟨a3, b3⟩ := q3
  simp only at h3 ⊢
  have h4 := lift2_av (eliminateSig hψ) (eliminate_dv hψ) a3 b3
  generalize lift2 (eliminateSig hψ) a3 b3 = q4 at h4
  obtain ⟨a4, b4⟩ := q4
  simp only at h4 ⊢
  have h5 := moveSource_av hψ c a4 b4
  generalize moveSourceAuth hψ c a4 b4 = q5 at h5
  obtain ⟨a5, b5⟩ := q5
  simp only at h5 ⊢
  have h6 := preCheck_av (liftLife dropStale a5) (liftLife dropStale b5)
  rw [liftLife_av _ dropStale_dv, liftLife_av _ dropStale_dv] at h6
  generalize preCheckResetAuth (liftLife dropStale a5) (liftLife dropStale b5) = q6 at h6
  obtain ⟨a6, b6⟩ := q6
  simp only at h6 ⊢
  have e7 := liftLife_av _ ready_dv a6
  have f7 := liftLife_av _ ready_dv b6
  generalize liftLife normalizeReady a6 = a7 at e7
  generalize liftLife normalizeReady b6 = b7 at f7
  have h8 := checkSource_FR hψ c a7 b7
  generalize checkSourceAuth hψ c a7 b7 = q8 at h8
  obtain ⟨a8, b8⟩ := q8
  simp only at h8 ⊢
  have h9 := disappear_av hψ a8 b8
  generalize disappearAuth hψ a8 b8 = q9 at h9
  obtain ⟨a9, b9⟩ := q9
  simp only at h9 ⊢
  have h10 := repair_av a9 b9
  generalize repairAuth a9 b9 = q10 at h10
  obtain ⟨a10, b10⟩ := q10
  simp only at h10 ⊢
  have h11 := compare_FR κ a10 b10
  generalize compareLifecycleAuth κ a10 b10 = q11 at h11
  obtain ⟨a11, b11⟩ := q11
  simp only at h11 ⊢
  have p1 : FR l r a7 b7 := by
    apply FR_of_av
    · rw [e7, h6.1, h5.1, h4.1, h3.1, h2.1, h1.1]
    · rw [f7, h6.2, h5.2, h4.2, h3.2, h2.2, h1.2]
  have p2 : FR a8 b8 a10 b10 := FR_of_av (h10.1.trans h9.1) (h10.2.trans h9.2)
  exact FR_trans (FR_trans (FR_trans p1 h8) p2) h11

/-- Algorithm 14 acts on the cores exactly as ReadyAck's `suppressSigResetKill`:
`kill` is `clearCmpAuth`, whose core is `clearCmp`. -/
theorem suppress_core {ψ : Nat} (hψ : ψ > 0) (l r : AuthState ψ) :
    (suppressSigResetKillAuth hψ l r).1.core = (suppressSigResetKill hψ l.core r.core).1 ∧
    (suppressSigResetKillAuth hψ l r).2.core = (suppressSigResetKill hψ l.core r.core).2 := by
  unfold suppressSigResetKillAuth suppressSigResetKill lift2
  dsimp only
  refine ⟨?_, ?_⟩ <;> (repeat' (first | (dsimp only [clearCmpAuth]) | split)) <;>
    first | rfl | (exfalso; contradiction) | simp_all

/-- K4, WRITE and `conserveAuth` act on the cores exactly as ReadyAck's suffix. -/
theorem pipeline_core {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    (PPLLAuthF.pipeline hψ κ c l r).1.core = (conserve .head l.core r.core
      (writeWithBundle hψ (k4Kernel hψ (PPLLAuthF.beforeElimination hψ κ c l r).1.core
        (PPLLAuthF.beforeElimination hψ κ c l r).2.core).1
        (k4Kernel hψ (PPLLAuthF.beforeElimination hψ κ c l r).1.core
        (PPLLAuthF.beforeElimination hψ κ c l r).2.core).2)).1 ∧
    (PPLLAuthF.pipeline hψ κ c l r).2.core = (conserve .head l.core r.core
      (writeWithBundle hψ (k4Kernel hψ (PPLLAuthF.beforeElimination hψ κ c l r).1.core
        (PPLLAuthF.beforeElimination hψ κ c l r).2.core).1
        (k4Kernel hψ (PPLLAuthF.beforeElimination hψ κ c l r).1.core
        (PPLLAuthF.beforeElimination hψ κ c l r).2.core).2)).2 := by
  unfold PPLLAuthF.pipeline conserveAuth lift2
  generalize PPLLAuthF.beforeElimination hψ κ c l r = E
  dsimp only
  constructor
  · rfl
  · split <;> rfl

/-! ### Algorithm 14 on cores (restated from `PPLLAstraReadyResetDrain`, where
these lemmas are private) -/

section Stages
variable {ψ : Nat}
private theorem cc_reset (u : AgentState ψ) : (clearCmp u).reset_cmd=u.reset_cmd := rfl
private theorem cc_echo (u : AgentState ψ) : (clearCmp u).echo=u.echo := rfl
private theorem cc_leader (u : AgentState ψ) : (clearCmp u).leader=u.leader := rfl
private theorem cc_label (u : AgentState ψ) : (clearCmp u).label=u.label := rfl

private theorem st1 (l r : AgentState ψ) (hl : l.leader=false) : suppressSigStart l r = (l,r) := by
  simp [suppressSigStart,hl]
private theorem mv1_reset (l r : AgentState ψ) : (suppressSigMoveReset l r).1.reset_cmd=false := by
  cases h : l.reset_cmd <;> simp [suppressSigMoveReset,h]
private theorem mv1_echo (l r : AgentState ψ) : (suppressSigMoveReset l r).1.echo=l.echo := by
  cases h : l.reset_cmd <;> simp [suppressSigMoveReset,h]
private theorem mv1_leader (l r : AgentState ψ) : (suppressSigMoveReset l r).1.leader=l.leader := by
  cases h : l.reset_cmd <;> simp [suppressSigMoveReset,h]
private theorem mv2_reset (l r : AgentState ψ) :
    (suppressSigMoveReset l r).2.reset_cmd=(l.reset_cmd || r.reset_cmd) := by
  cases h : l.reset_cmd <;> simp [suppressSigMoveReset,h]
private theorem mv2_echo (l r : AgentState ψ) : (suppressSigMoveReset l r).2.echo=r.echo := by
  cases h : l.reset_cmd <;> simp [suppressSigMoveReset,h]
private theorem mv2_label (l r : AgentState ψ) : (suppressSigMoveReset l r).2.label=r.label := by
  cases h : l.reset_cmd <;> simp [suppressSigMoveReset,h]
private theorem mv2_leader (l r : AgentState ψ) : (suppressSigMoveReset l r).2.leader=r.leader := by
  cases h : l.reset_cmd <;> simp [suppressSigMoveReset,h]
private theorem tm1_reset (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigTerminal hp l r).1.reset_cmd=l.reset_cmd := by
  unfold suppressSigTerminal; split <;> rfl
private theorem tm1_leader (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigTerminal hp l r).1.leader=l.leader := by
  unfold suppressSigTerminal; split <;> rfl
private theorem tm1_echo (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigTerminal hp l r).1.echo=
      if r.label = ⟨ψ-1,by omega⟩ ∧ r.reset_cmd=true then true else l.echo := by
  unfold suppressSigTerminal; split <;> rfl
private theorem tm2_reset (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigTerminal hp l r).2.reset_cmd=r.reset_cmd := by
  unfold suppressSigTerminal; split <;> rfl
private theorem tm2_echo (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigTerminal hp l r).2.echo=r.echo := by
  unfold suppressSigTerminal; split <;> rfl
private theorem tm2_leader (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigTerminal hp l r).2.leader=r.leader := by
  unfold suppressSigTerminal; split <;> rfl
private theorem ec1_reset (l r : AgentState ψ) : (suppressSigEcho l r).1.reset_cmd=l.reset_cmd := by
  cases h1 : r.echo <;> cases h2 : r.reset_cmd <;> simp [suppressSigEcho,h1,h2]
private theorem ec1_leader (l r : AgentState ψ) : (suppressSigEcho l r).1.leader=l.leader := by
  cases h1 : r.echo <;> cases h2 : r.reset_cmd <;> simp [suppressSigEcho,h1,h2]
private theorem ec1_echo (l r : AgentState ψ) :
    (suppressSigEcho l r).1.echo=(l.echo || (r.echo && !r.reset_cmd)) := by
  cases h1 : r.echo <;> cases h2 : r.reset_cmd <;> simp [suppressSigEcho,h1,h2]
private theorem ec2_reset (l r : AgentState ψ) :
    (suppressSigEcho l r).2.reset_cmd=(r.reset_cmd && !r.echo) := by
  cases h1 : r.echo <;> cases h2 : r.reset_cmd <;> simp [suppressSigEcho,h1,h2]
private theorem ec2_leader (l r : AgentState ψ) : (suppressSigEcho l r).2.leader=r.leader := by
  cases h1 : r.echo <;> cases h2 : r.reset_cmd <;> simp [suppressSigEcho,h1,h2]
private theorem fn1_reset (l r : AgentState ψ) : (suppressSigFinish l r).1.reset_cmd=l.reset_cmd := by
  cases h : l.leader <;> simp [suppressSigFinish,h]
private theorem fn1_echo (l r : AgentState ψ) :
    (suppressSigFinish l r).1.echo=(l.echo && !l.leader) := by
  cases h : l.leader <;> simp [suppressSigFinish,h]
private theorem fn2 (l r : AgentState ψ) : (suppressSigFinish l r).2=r := rfl
private theorem tm2_label (hp : ψ>0) (l r : AgentState ψ) :
    (suppressSigTerminal hp l r).2.label=r.label := by
  unfold suppressSigTerminal; split <;> rfl
private theorem ec2_label (l r : AgentState ψ) : (suppressSigEcho l r).2.label=r.label := by
  cases h1 : r.echo <;> cases h2 : r.reset_cmd <;> simp [suppressSigEcho,h1,h2]

theorem suppress_reset (hp : ψ>0) (l r : AgentState ψ) (hl : l.leader=false) :
    (suppressSigResetKill hp l r).1.reset_cmd=false ∧
    (suppressSigResetKill hp l r).2.reset_cmd=((l.reset_cmd || r.reset_cmd) && !r.echo) := by
  constructor
  · simp only [suppressSigResetKill,st1 l r hl,fn1_reset,ec1_reset,tm1_reset,mv1_reset,
      reset_ite,cc_reset,ite_self]
  · simp only [suppressSigResetKill,st1 l r hl,fn2,ec2_reset,tm2_reset,tm2_echo,mv2_reset,mv2_echo,
      reset_ite,echo_ite,cc_reset,cc_echo,ite_self]

theorem suppress_label (hp : ψ>0) (l r : AgentState ψ) (hl : l.leader=false) :
    (suppressSigResetKill hp l r).2.label=r.label := by
  simp only [suppressSigResetKill,st1 l r hl,fn2,ec2_label,tm2_label,mv2_label,label_ite,cc_label,ite_self]

theorem suppress_right_leader (hp : ψ>0) (l r : AgentState ψ) (hl : l.leader=false) :
    (suppressSigResetKill hp l r).2.leader=r.leader := by
  simp only [suppressSigResetKill,st1 l r hl,fn2,ec2_leader,tm2_leader,mv2_leader,leader_ite,
    cc_leader,ite_self]

theorem suppress_echo_terminal (hp : ψ>0) (l r : AgentState ψ) (hl : l.leader=false)
    (ht : r.label=⟨ψ-1,by omega⟩) (hc : (l.reset_cmd || r.reset_cmd)=true) :
    (suppressSigResetKill hp l r).1.echo=true := by
  simp only [suppressSigResetKill,st1 l r hl,fn1_echo,ec1_echo,ec1_leader,tm1_echo,tm1_leader,
    tm2_echo,tm2_reset,mv1_echo,mv1_leader,mv2_echo,mv2_reset,mv2_label,
    reset_ite,echo_ite,leader_ite,label_ite,cc_reset,cc_echo,cc_leader,cc_label,ite_self]
  simp [ht,hc,hl]

theorem suppress_echo_walk (hp : ψ>0) (l r : AgentState ψ) (hl : l.leader=false)
    (ha : l.reset_cmd=false) (hb : r.reset_cmd=false) (he : r.echo=true) :
    (suppressSigResetKill hp l r).1.echo=true := by
  simp only [suppressSigResetKill,st1 l r hl,fn1_echo,ec1_echo,ec1_leader,tm1_echo,tm1_leader,
    tm2_echo,tm2_reset,mv1_echo,mv1_leader,mv2_echo,mv2_reset,mv2_label,
    reset_ite,echo_ite,leader_ite,label_ite,cc_reset,cc_echo,cc_leader,cc_label,ite_self]
  simp [ha,hb,he,hl]
end Stages

/-! ### Prefix facts in the form used by the ring argument -/

section Prefix
variable {ψ : Nat}

/-- The prefix keeps reset/echo on both endpoints, the initiator's leader bit,
and hands Algorithm 14 the responder label produced by P′; responder leadership
from P′ survives. -/
theorem prefix_facts (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    let B := beforeSuppressAuth hp κ c l r
    let P := pPsiProbeWall hp l.core r.core
    B.1.core.reset_cmd = l.core.reset_cmd ∧ B.1.core.echo = l.core.echo ∧
    B.2.core.reset_cmd = r.core.reset_cmd ∧ B.2.core.echo = r.core.echo ∧
    B.1.core.leader = l.core.leader ∧ B.2.core.label = P.2.label ∧
    (P.2.leader = true → B.2.core.leader = true) := by
  intro B P
  have hm := mid_FR hp κ c (lift2 (pPsiProbeWall hp) l r).1 (lift2 (pPsiProbeWall hp) l r).2
  have hb := pPsi_bits hp l.core r.core
  change FR _ _ B.1 B.2 at hm
  obtain ⟨m1, m2, m3⟩ := hm
  simp only [av, dv, wv, Prod.mk.injEq] at m1 m2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m1.1]; exact hb.1
  · rw [m1.2.1]; exact hb.2.1
  · rw [m2.1]; exact hb.2.2.1
  · rw [m2.2.1]; exact hb.2.2.2.1
  · rw [m1.2.2.2]; exact hb.2.2.2.2
  · rw [m2.2.2]; rfl
  · exact m3

end Prefix

/-! ### Full-pipeline reset/echo/label equations for a follower initiator -/

theorem pipeline_follower_reset {ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader=false) :
    (PPLLAuthF.pipeline hp κ c l r).1.core.reset_cmd=false ∧
    (PPLLAuthF.pipeline hp κ c l r).2.core.reset_cmd=
      ((l.core.reset_cmd || r.core.reset_cmd) && !r.core.echo) := by
  have hpf := prefix_facts hp κ c l r
  dsimp only at hpf
  obtain ⟨b1, _, b3, b4, b5, _, _⟩ := hpf
  have hc := pipeline_core hp κ c l r
  have hsx := PPLLAstraReadyResetDebtR.Writer.suffix_fields hp l.core r.core
    ((PPLLAuthF.beforeElimination hp κ c l r).1.core, (PPLLAuthF.beforeElimination hp κ c l r).2.core)
  dsimp only at hsx
  rw [hc.1, hc.2, hsx.1, hsx.2.2.1, beforeElimination_eq, (suppress_core hp _ _).1,
    (suppress_core hp _ _).2]
  have hs := suppress_reset hp (beforeSuppressAuth hp κ c l r).1.core
    (beforeSuppressAuth hp κ c l r).2.core (b5.trans hl)
  rw [b1, b3, b4] at hs
  exact hs

theorem pipeline_terminal_echo {ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader=false) (ht : (pPsiProbeWall hp l.core r.core).2.label.val=ψ-1)
    (hcd : (l.core.reset_cmd || r.core.reset_cmd)=true) :
    (PPLLAuthF.pipeline hp κ c l r).1.core.echo=true := by
  have hpf := prefix_facts hp κ c l r
  dsimp only at hpf
  obtain ⟨b1, _, b3, _, b5, b6, _⟩ := hpf
  have hc := pipeline_core hp κ c l r
  have hsx := PPLLAstraReadyResetDebtR.Writer.suffix_fields hp l.core r.core
    ((PPLLAuthF.beforeElimination hp κ c l r).1.core, (PPLLAuthF.beforeElimination hp κ c l r).2.core)
  dsimp only at hsx
  rw [hc.1, hsx.2.1, beforeElimination_eq, (suppress_core hp _ _).1]
  apply suppress_echo_terminal hp _ _ (b5.trans hl)
  · exact Fin.ext ((congrArg Fin.val b6).trans ht)
  · rw [b1, b3]; exact hcd

theorem pipeline_echo_walk {ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader=false) (ha : l.core.reset_cmd=false) (hb : r.core.reset_cmd=false)
    (he : r.core.echo=true) :
    (PPLLAuthF.pipeline hp κ c l r).1.core.echo=true := by
  have hpf := prefix_facts hp κ c l r
  dsimp only at hpf
  obtain ⟨b1, _, b3, b4, b5, _, _⟩ := hpf
  have hc := pipeline_core hp κ c l r
  have hsx := PPLLAstraReadyResetDebtR.Writer.suffix_fields hp l.core r.core
    ((PPLLAuthF.beforeElimination hp κ c l r).1.core, (PPLLAuthF.beforeElimination hp κ c l r).2.core)
  dsimp only at hsx
  rw [hc.1, hsx.2.1, beforeElimination_eq, (suppress_core hp _ _).1]
  exact suppress_echo_walk hp _ _ (b5.trans hl) (b1.trans ha) (b3.trans hb) (b4.trans he)

private theorem kernel_right {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    (k4Kernel hp l r).2.leader = r.leader ∧ (k4Kernel hp l r).2.label = r.label := by
  simp only [k4Kernel,k3Kernel,eliminateLeadersNoCollisionFire,absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink,dummyBulletSink]
  simp only [fst_ite,snd_ite,leader_ite,label_ite,ite_self,and_self]

/-- The responder that reaches K4 is the Algorithm 14 output of the prefix. -/
private theorem responder_at_kernel {ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader=false) :
    (PPLLAuthF.beforeElimination hp κ c l r).2.core.label = (pPsiProbeWall hp l.core r.core).2.label ∧
    ((pPsiProbeWall hp l.core r.core).2.leader = true →
      (PPLLAuthF.beforeElimination hp κ c l r).2.core.leader = true) := by
  have hpf := prefix_facts hp κ c l r
  dsimp only at hpf
  obtain ⟨_, _, _, _, b5, b6, b7⟩ := hpf
  rw [beforeElimination_eq, (suppress_core hp _ _).2]
  refine ⟨?_, ?_⟩
  · rw [suppress_label hp _ _ (b5.trans hl)]; exact b6
  · intro h; rw [suppress_right_leader hp _ _ (b5.trans hl)]; exact b7 h

/-- A P′ probe birth at the responder survives the whole AuthF interaction. -/
theorem pipeline_pPsi_responder_survives {ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) (hl : l.core.leader=false)
    (hr : (pPsiProbeWall hp l.core r.core).2.leader = true)
    (hz : (pPsiProbeWall hp l.core r.core).2.label.val = 0) :
    (PPLLAuthF.pipeline hp κ c l r).2.core.leader = true := by
  have hk0 := responder_at_kernel hp κ c l r hl
  have hc := pipeline_core hp κ c l r
  rw [hc.2]
  generalize PPLLAuthF.beforeElimination hp κ c l r = E at hk0
  have hk := kernel_right hp E.1.core E.2.core
  generalize k4Kernel hp E.1.core E.2.core = k at hk
  have kr : k.2.leader = true := hk.1.trans (hk0.2 hr)
  have kz : k.2.label = ⟨0,hp⟩ := by
    apply Fin.ext; rw [hk.2, hk0.1]; exact hz
  have wr := PPLLVerify.writeSeq_responder_leader_of_label_zero hp k.1 k.2 kr kz
  have wb : (writeWithBundle hp k.1 k.2).2.leader = true := by
    simp only [writeWithBundle,snd_ite,leader_ite,wr,ite_self]
  simp [conserve,wb]

theorem pipeline_zero_no_probe_barrier {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hout : (PPLLAuthF.pipeline hp κ c l r).2.core.leader = false) :
    r.core.probe = false ∨ r.core.label = ⟨(l.core.label.val + 1) % ψ,Nat.mod_lt _ hp⟩ := by
  cases hpr : r.core.probe
  · exact Or.inl rfl
  · right
    by_cases hne : r.core.label = ⟨(l.core.label.val + 1) % ψ,Nat.mod_lt _ hp⟩
    · exact hne
    apply False.elim
    have hbirth : (pPsiProbeWall hp l.core r.core).2.leader = true := by
      simp [pPsiProbeWall,pPsi,hl,hr,hpr,hne]
    have hzero : (pPsiProbeWall hp l.core r.core).2.label.val = 0 := by
      simp [pPsiProbeWall,pPsi,hl,hr,hpr,hne]
    have hs := pipeline_pPsi_responder_survives hp κ c l r hl hbirth hzero
    rw [hout] at hs; cases hs

/-- On a follower pair whose responder output is a follower, P′ fired without a
probe birth and the responder leaves with label `label(l)+1 mod ψ`. -/
theorem pipeline_follower_labels {ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader=false) (hr : r.core.leader=false)
    (hout : (PPLLAuthF.pipeline hp κ c l r).2.core.leader=false) :
    (pPsiProbeWall hp l.core r.core).2.label.val=(l.core.label.val+1)%ψ ∧
    (PPLLAuthF.pipeline hp κ c l r).2.core.label.val=(l.core.label.val+1)%ψ := by
  have hs := pipeline_zero_no_probe_barrier hp κ c l r hl hr hout
  have hp1 : (pPsiProbeWall hp l.core r.core).2.label.val=(l.core.label.val+1)%ψ := by
    rcases hs with hs | hs
    · by_cases hn : r.core.label=⟨(l.core.label.val+1)%ψ,Nat.mod_lt _ hp⟩
      · simp [pPsiProbeWall,pPsi,hl,hr,hs,hn]
      · cases hx : l.core.phase <;> simp [pPsiProbeWall,pPsi,hl,hr,hs,hn,hx]
    · simp [pPsiProbeWall,pPsi,hl,hr,hs]
  refine ⟨hp1, ?_⟩
  have hk0 := responder_at_kernel hp κ c l r hl
  have hc := pipeline_core hp κ c l r
  rw [hc.2]
  generalize PPLLAuthF.beforeElimination hp κ c l r = E at hk0
  have hk := kernel_right hp E.1.core E.2.core
  generalize k4Kernel hp E.1.core E.2.core = k at hk
  have hw := (PPLLAstraReadyThree.Writer.write_control hp k.1 k.2).2
  simp only [PPLLAstraReadyThree.control, Prod.mk.injEq] at hw
  simp only [conserve, hl, hr, Bool.false_or, Bool.false_and, ite_false, Bool.false_eq_true]
  rw [hw.1, hk.2, hk0.1]
  exact hp1

/-! ### The AuthF protocol and physical words -/

/-- The AuthF protocol with configuration `c`; the output is the core leader bit. -/
abbrev authProtocol {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) : PopulationProtocol where
  Q := AuthState ψ
  Y := Bool
  transition := PPLLAuthF.pipeline hp κ c
  output := fun a => a.core.leader

/-- `authFplusmcc` of `PPLLAuthF.variants`: sender retirement, mark-mismatch
CLEAN and A2 claiming of CHECK cells. -/
def authFplusmcc : PPLLAuthF.Cfg := { retire := true, markClean := true, claimCheck := true }

/-- Execute a physical word. -/
def authRun {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) : List (Fin n) → (Fin n → AuthState ψ)
  | [] => C
  | e::es => authRun hp κ c ring ((authProtocol hp κ c).step ring C e) es

theorem authRun_reachable {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (w : List (Fin n)) :
    (authProtocol hp κ c).Reachable ring C (authRun hp κ c ring C w) := by
  induction w generalizing C with
  | nil => exact PopulationProtocol.Reachable.refl (P := authProtocol hp κ c) C
  | cons e es ih =>
    have h1 : (authProtocol hp κ c).Reachable ring C ((authProtocol hp κ c).step ring C e) :=
      PopulationProtocol.OneStep.to_reachable ⟨e, rfl⟩
    exact PopulationProtocol.Reachable.trans h1 (ih _)

/-! ### Configuration-level bookkeeping (as in `PPLLAstraReadyResetDrain`) -/

private abbrev S {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e : Fin n) : Fin n → AuthState ψ :=
  (authProtocol hp κ c).step ring C e

private theorem neighbor_ne' {n : Nat} (ring : DirectedRing n) (hn : 1<n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have he := congrArg Fin.val h
  change (e.val+1)%n=e.val at he
  by_cases hk : e.val+1<n
  · rw [Nat.mod_eq_of_lt hk] at he; omega
  · have hlast : e.val+1=n := by omega
    rw [hlast,Nat.mod_self] at he; omega

private theorem step_left {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e : Fin n) :
    S hp κ c ring C e e = (PPLLAuthF.pipeline hp κ c (C e) (C (ring.rightNeighbor e))).1 := by
  simp [S,PopulationProtocol.step,authProtocol]

private theorem step_right {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (hn : 1<n) (C : Fin n → AuthState ψ) (e : Fin n) :
    S hp κ c ring C e (ring.rightNeighbor e) =
      (PPLLAuthF.pipeline hp κ c (C e) (C (ring.rightNeighbor e))).2 := by
  have ne := neighbor_ne' ring hn e
  simp [S,PopulationProtocol.step,authProtocol,ne]

private theorem step_other {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e i : Fin n) (h1 : i≠e) (h2 : i≠ring.rightNeighbor e) :
    S hp κ c ring C e i = C i := by
  simp [S,PopulationProtocol.step,authProtocol,h1,h2]

private theorem authRun_append {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (w1 w2 : List (Fin n)) : ∀ C : Fin n → AuthState ψ,
    authRun hp κ c ring C (w1++w2) = authRun hp κ c ring (authRun hp κ c ring C w1) w2 := by
  induction w1 with
  | nil => intro C; rfl
  | cons e es ih => intro C; exact ih _

/-- Leaderless configuration. -/
private def LF {n ψ : Nat} (C : Fin n → AuthState ψ) : Prop := ∀ i, (C i).core.leader=false

/-- The goal: some word reaches a leader or a reset-free configuration. -/
private def G {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) : Prop :=
  ∃ w : List (Fin n), (∃ i, (authRun hp κ c ring C w i).core.leader=true) ∨
    ∀ i, (authRun hp κ c ring C w i).core.reset_cmd=false

private theorem G_clean {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (h : ∀ i, (C i).core.reset_cmd=false) : G hp κ c ring C :=
  ⟨[],Or.inr h⟩

private theorem G_step {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e : Fin n)
    (h : LF (S hp κ c ring C e) → G hp κ c ring (S hp κ c ring C e)) : G hp κ c ring C := by
  classical
  by_cases hl : ∃ i, (S hp κ c ring C e i).core.leader=true
  · exact ⟨[e],Or.inl hl⟩
  · have hz : LF (S hp κ c ring C e) := by
      intro i
      cases hi : (S hp κ c ring C e i).core.leader
      · rfl
      · exact False.elim (hl ⟨i,hi⟩)
    obtain ⟨w,hw⟩ := h hz
    exact ⟨e::w,hw⟩

private theorem mod_ne_self {n y k : Nat} (hy : y<n) (hk0 : 0<k) (hk : k<n) :
    (y+k)%n ≠ y := by
  by_cases h : y+k<n
  · rw [Nat.mod_eq_of_lt h]; omega
  · have h1 : (y+k)%n = (y+k-n)%n := by
      rw [Nat.mod_eq_sub_mod (by omega)]
    rw [h1,Nat.mod_eq_of_lt (by omega)]; omega

/-! ### Kill: an echo walks counterclockwise onto the reset's right neighbour -/

private theorem kill {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n) (hn : 1<n)
    (d : Nat) : ∀ (C : Fin n → AuthState ψ) (y z : Fin n), d+2 ≤ n → LF C →
    (∀ i, (C i).core.reset_cmd=true → i=y) → (C z).core.echo=true →
    z.val=(y.val+1+d)%n → G hp κ c ring C := by
  induction d with
  | zero =>
    intro C y z _ hC hy hz hzv
    have hzr : z=ring.rightNeighbor y := Fin.ext (by rw [hzv]; rfl)
    rw [hzr] at hz
    apply G_step hp κ c ring C y
    intro _
    apply G_clean
    have hr := pipeline_follower_reset hp κ c (C y) (C (ring.rightNeighbor y)) (hC y)
    intro i
    by_cases h1 : i=y
    · rw [h1,step_left]; exact hr.1
    · by_cases h2 : i=ring.rightNeighbor y
      · rw [h2,step_right hp κ c ring hn]
        rw [hr.2,hz]; simp
      · rw [step_other hp κ c ring C y i h1 h2]
        cases hcc : (C i).core.reset_cmd
        · rfl
        · exact False.elim (h1 (hy i hcc))
  | succ d ih =>
    intro C y z hd hC hy hz hzv
    obtain ⟨p,hpv⟩ : ∃ p : Fin n, p.val=(y.val+1+d)%n := ⟨⟨_,Nat.mod_lt _ (by omega)⟩,rfl⟩
    have hpz : ring.rightNeighbor p = z := by
      apply Fin.ext
      change (p.val+1)%n = z.val
      rw [hpv,Nat.mod_add_mod,hzv,Nat.add_assoc (y.val+1) d 1]
    have hpy : p≠y := by
      intro h
      rw [h] at hpv
      exact mod_ne_self (k:=1+d) y.isLt (by omega) (by omega)
        (by rw [← Nat.add_assoc]; exact hpv.symm)
    have hzy : z≠y := by
      intro h
      rw [h] at hzv
      exact mod_ne_self (k:=1+(d+1)) y.isLt (by omega) (by omega)
        (by rw [← Nat.add_assoc]; exact hzv.symm)
    have hpr : (C p).core.reset_cmd=false := by
      cases hcc : (C p).core.reset_cmd
      · rfl
      · exact False.elim (hpy (hy p hcc))
    have hzr : (C z).core.reset_cmd=false := by
      cases hcc : (C z).core.reset_cmd
      · rfl
      · exact False.elim (hzy (hy z hcc))
    apply G_step hp κ c ring C p
    intro hD
    have hr := pipeline_follower_reset hp κ c (C p) (C (ring.rightNeighbor p)) (hC p)
    apply ih (S hp κ c ring C p) y p (by omega) hD
    · intro i hi
      by_cases h1 : i=p
      · rw [h1,step_left,hr.1] at hi; cases hi
      · by_cases h2 : i=ring.rightNeighbor p
        · rw [h2,step_right hp κ c ring hn] at hi
          rw [hr.2,hpz,hpr,hzr] at hi; simp at hi
        · rw [step_other hp κ c ring C p i h1 h2] at hi; exact hy i hi
    · rw [step_left]
      exact pipeline_echo_walk hp κ c _ _ (hC p) hpr (by rw [hpz]; exact hzr) (by rw [hpz]; exact hz)
    · exact hpv

/-! ### Walk: a single reset travels until its responder is terminal -/

private theorem walk {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n) (hn : 1<n)
    (k : Nat) : ∀ (C : Fin n → AuthState ψ) (y : Fin n), LF C →
    (∀ i, (C i).core.reset_cmd=true → i=y) →
    ((C y).core.label.val+1+k)%ψ=ψ-1 → G hp κ c ring C := by
  induction k with
  | zero =>
    intro C y hC hy hk
    apply G_step hp κ c ring C y
    intro hD
    have hr := pipeline_follower_reset hp κ c (C y) (C (ring.rightNeighbor y)) (hC y)
    have hr2 := hr.2
    have hout : (PPLLAuthF.pipeline hp κ c (C y) (C (ring.rightNeighbor y))).2.core.leader=false := by
      have := hD (ring.rightNeighbor y); rwa [step_right hp κ c ring hn] at this
    have hlab := pipeline_follower_labels hp κ c (C y) (C (ring.rightNeighbor y)) (hC y) (hC _) hout
    have hframe : ∀ i, i≠y → i≠ring.rightNeighbor y → (S hp κ c ring C y i).core.reset_cmd=false := by
      intro i h1 h2
      rw [step_other hp κ c ring C y i h1 h2]
      cases hcc : (C i).core.reset_cmd
      · rfl
      · exact False.elim (h1 (hy i hcc))
    have hyl : (S hp κ c ring C y y).core.reset_cmd=false := by rw [step_left]; exact hr.1
    cases hyr : (C y).core.reset_cmd
    · apply G_clean
      intro i
      by_cases h1 : i=y
      · rw [h1]; exact hyl
      · by_cases h2 : i=ring.rightNeighbor y
        · rw [h2,step_right hp κ c ring hn,hr2,hyr]
          cases hcc : (C (ring.rightNeighbor y)).core.reset_cmd
          · rfl
          · exact False.elim (neighbor_ne' ring hn y (hy _ hcc))
        · exact hframe i h1 h2
    · cases hre : (C (ring.rightNeighbor y)).core.echo
      · have hE : (S hp κ c ring C y y).core.echo=true := by
          rw [step_left]
          apply pipeline_terminal_echo hp κ c (C y) (C (ring.rightNeighbor y)) (hC y)
          · rw [hlab.1]; simpa using hk
          · simp [hyr]
        apply kill hp κ c ring hn (n-2) (S hp κ c ring C y) (ring.rightNeighbor y) y (by omega) hD
        · intro i hi
          by_cases h1 : i=y
          · rw [h1,hyl] at hi; cases hi
          · by_cases h2 : i=ring.rightNeighbor y
            · exact h2
            · rw [hframe i h1 h2] at hi; cases hi
        · exact hE
        · change y.val = (((y.val+1)%n)+1+(n-2))%n
          rw [Nat.add_assoc,Nat.mod_add_mod]
          have : y.val+1+(1+(n-2)) = y.val+n := by omega
          rw [this,Nat.add_mod_right,Nat.mod_eq_of_lt y.isLt]
      · apply G_clean
        intro i
        by_cases h1 : i=y
        · rw [h1]; exact hyl
        · by_cases h2 : i=ring.rightNeighbor y
          · rw [h2,step_right hp κ c ring hn,hr2,hre]; simp
          · exact hframe i h1 h2
  | succ k ih =>
    intro C y hC hy hk
    apply G_step hp κ c ring C y
    intro hD
    have hr := pipeline_follower_reset hp κ c (C y) (C (ring.rightNeighbor y)) (hC y)
    have hout : (PPLLAuthF.pipeline hp κ c (C y) (C (ring.rightNeighbor y))).2.core.leader=false := by
      have := hD (ring.rightNeighbor y); rwa [step_right hp κ c ring hn] at this
    have hlab := pipeline_follower_labels hp κ c (C y) (C (ring.rightNeighbor y)) (hC y) (hC _) hout
    apply ih (S hp κ c ring C y) (ring.rightNeighbor y) hD
    · intro i hi
      by_cases h1 : i=y
      · rw [h1,step_left,hr.1] at hi; cases hi
      · by_cases h2 : i=ring.rightNeighbor y
        · exact h2
        · rw [step_other hp κ c ring C y i h1 h2] at hi
          exact False.elim (h1 (hy i hi))
    · rw [step_right hp κ c ring hn,hlab.2,Nat.add_assoc,Nat.mod_add_mod]
      rw [← hk]; congr 1; omega

/-! ### Sweep: serving edges `0,…,k-1` clears cells `0,…,k-1` -/

private theorem sweep {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (hC : LF C) (k : Nat) :
    k+1 ≤ n → ∃ w : List (Fin n), (∃ i, (authRun hp κ c ring C w i).core.leader=true) ∨
      (LF (authRun hp κ c ring C w) ∧ ∀ i : Fin n, i.val<k → (authRun hp κ c ring C w i).core.reset_cmd=false) := by
  induction k with
  | zero => intro _; exact ⟨[],Or.inr ⟨hC,fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨w,hw⟩ := ih (by omega)
    rcases hw with hw | ⟨hD,hc⟩
    · exact ⟨w,Or.inl hw⟩
    · classical
      generalize hDw : authRun hp κ c ring C w = D at hD hc
      obtain ⟨e,hev⟩ : ∃ e : Fin n, e.val=k := ⟨⟨k,by omega⟩,rfl⟩
      have hrun : authRun hp κ c ring C (w++[e]) = S hp κ c ring D e := by
        rw [authRun_append,hDw]; rfl
      by_cases hl : ∃ i, (S hp κ c ring D e i).core.leader=true
      · exact ⟨w++[e],Or.inl (by rw [hrun]; exact hl)⟩
      · refine ⟨w++[e],Or.inr ⟨?_,?_⟩⟩
        · intro i
          rw [hrun]
          cases hi : (S hp κ c ring D e i).core.leader
          · rfl
          · exact False.elim (hl ⟨i,hi⟩)
        · intro i hi
          rw [hrun]
          have hr := pipeline_follower_reset hp κ c (D e) (D (ring.rightNeighbor e)) (hD e)
          by_cases h1 : i=e
          · rw [h1,step_left]; exact hr.1
          · have hik : i.val<k := by
              have : i.val≠k := fun h => h1 (Fin.ext (h.trans hev.symm))
              omega
            have h2 : i≠ring.rightNeighbor e := by
              intro h
              have := congrArg Fin.val h
              change i.val=(e.val+1)%n at this
              rw [hev,Nat.mod_eq_of_lt (by omega)] at this
              omega
            rw [step_other hp κ c ring D e i h1 h2]
            exact hc i hik

/-! ### Headline -/

/-- **Reset drain for AuthF.** For every AuthF configuration `c` (in particular
`authFplusmcc`), from any configuration on a directed ring with at least two
cells some physical word reaches a configuration that has a leader or carries no
`reset_cmd` anywhere. Labels, echoes, provenance marks, κ and all ancillary
fields are arbitrary. Same word shape as for ReadyAck: sweep, walk of at most
`ψ` services, echo walk of `n-2` services and the annihilating service. -/
theorem exists_reset_free_or_positive {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : PPLLAuthF.Cfg)
    (ring : DirectedRing n) (hn : 1<n) (C : Fin n → AuthState ψ) :
    ∃ w : List (Fin n), (∃ i, (authRun hp κ c ring C w i).core.leader=true) ∨
      ∀ i, (authRun hp κ c ring C w i).core.reset_cmd=false := by
  classical
  by_cases hc : ∃ i, (C i).core.leader=true
  · exact ⟨[],Or.inl hc⟩
  have hC : LF C := by
    intro i
    cases hi : (C i).core.leader
    · rfl
    · exact False.elim (hc ⟨i,hi⟩)
  obtain ⟨w,hw⟩ := sweep hp κ c ring C hC (n-1) (by omega)
  rcases hw with hw | ⟨hD,hcl⟩
  · exact ⟨w,Or.inl hw⟩
  generalize hDw : authRun hp κ c ring C w = D at hD hcl
  let last : Fin n := ⟨n-1,by omega⟩
  have hy : ∀ i, (D i).core.reset_cmd=true → i=last := by
    intro i hi
    apply Fin.ext
    change i.val=n-1
    by_cases h : i.val<n-1
    · rw [hcl i h] at hi; cases hi
    · have := i.isLt; omega
  have hG : G hp κ c ring D := by
    have hlt := (D last).core.label.isLt
    by_cases hL : (D last).core.label.val+1 ≤ ψ-1
    · apply walk hp κ c ring hn (ψ-1-((D last).core.label.val+1)) D last hD hy
      have : (D last).core.label.val+1+(ψ-1-((D last).core.label.val+1)) = ψ-1 := by omega
      rw [this,Nat.mod_eq_of_lt (by omega)]
    · apply walk hp κ c ring hn (ψ-1) D last hD hy
      have : (D last).core.label.val+1+(ψ-1) = (ψ-1)+ψ := by omega
      rw [this,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨w2,hw2⟩ := hG
  exact ⟨w++w2,by rw [authRun_append,hDw]; exact hw2⟩

/-- Reachability form, for the Z-div target variant `authFplusmcc`. -/
theorem exists_reset_free_or_positive_authFplusmcc {n ψ : Nat} (hp : ψ>0) (κ : Nat)
    (ring : DirectedRing n) (hn : 1<n) (C : Fin n → AuthState ψ) :
    ∃ D : Fin n → AuthState ψ, (authProtocol hp κ authFplusmcc).Reachable ring C D ∧
      ((∃ i, (D i).core.leader=true) ∨ ∀ i, (D i).core.reset_cmd=false) := by
  obtain ⟨w,hw⟩ := exists_reset_free_or_positive hp κ authFplusmcc ring hn C
  exact ⟨authRun hp κ authFplusmcc ring C w,authRun_reachable hp κ authFplusmcc ring C w,hw⟩

#print axioms pipeline_follower_reset
#print axioms pipeline_terminal_echo
#print axioms pipeline_echo_walk
#print axioms pipeline_follower_labels
#print axioms exists_reset_free_or_positive
#print axioms exists_reset_free_or_positive_authFplusmcc
end PPLLAuthResetDrain
