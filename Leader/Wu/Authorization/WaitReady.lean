import Leader.Wu.Authorization.GenerationDrainLocal

/-!
# WAIT-readiness for AuthF (Q20606 §§5–9)

`waitReady_block`: on a leaderless, reset-free, perfectly labelled AuthF ring
(`echo` arbitrary), if block `g` has a pathless head, no cell in
`produce`/`done`, and terminal `count ≤ κ`, then a word of internal edges of
block `g` of length at most `(1 + κ·2^ψ)(ψ-1) + (ψ-2)` reaches a leader or
starts the generation: the head is a pathless producer (GenActive). Every
proper prefix keeps the head pathless and the block free of `produce`/`done`;
the word schedules only edges `gψ ≤ e ≤ gψ+ψ-2` and fixes every cell outside
the block. Requires `ψ ≥ 3`.

Two hypotheses beyond the coordinator's list, each forced by a counterexample
found by executable simulation before the proof:

* `ψ ≥ 3`. For `ψ = 2` the head-start row recruits the terminal, which emits
  and is `done` inside the same GENSIG; back-propagation makes the head `done`
  with a path and the final GENSIG line sends it to `depart`. The head never
  becomes a pathless producer.
* terminal `count ≤ κ` (Q20606 `inProtocolDomain`). With `κ = 0` and
  `count = 1` the terminal release test `count = κ` fails until a counter
  overflow saturates `count` back to `κ`, which takes up to `2^ψ` further
  sweeps and exceeds the bound (`ψ = 4, 5`).

Proof plan. Parts A–C: every AuthF stage except WAIT frames the WAIT
registers, and on a block row the whole AuthF interaction acts on them as
`waitSaturated` (`row_wait`), unless the row is the head start. Part C0 models
WAIT on six fields (`wsM`, exact by `ws_pi`) with a closed form `wsM_spec`.
Part E: a false `wait` walks to the head (`walk`); if every `wait` is true, a
first forward sweep clears carries and resets, and each later sweep adds one to
the counter `Φ = count·2^ψ + Σ h_i 2^i` or releases the terminal. Since
`Φ < κ·2^ψ` on a clean block, at most `κ·2^ψ` clean sweeps occur.
-/

set_option autoImplicit false

namespace PPLLAuthWaitReady

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF PPLLAuthResetDrain
open PPLLAuthGenDrain PPLLAuthGenDrainLocal

set_option linter.unusedSimpArgs false

/-! ## Part A. The WAIT view is framed by every AuthF stage except WAIT

`kv u = (wait, count, carry, h_field, reset)` are Algorithm 3's registers
(`reset` is the WAIT register, not `reset_cmd`). Outside `waitSaturated`, the
only writers are GENSIG's final head line (`wait := true` on a `done` head) and
Algorithm 14's terminal `count := 0` on a pending `reset_cmd`. The stage lemmas
follow the template of `PPLLAuthWriterFrame`. -/

/-- The WAIT view of a cell. -/
def kv {ψ : Nat} (u : AgentState ψ) : Bool × Nat × Bool × Bool × Bool :=
  (u.wait, u.count, u.carry, u.h_field, u.reset)

/-- The WAIT view of an AuthF cell is that of its core. -/
def akv {ψ : Nat} (u : AuthState ψ) := kv u.core

section Ite
variable {ψ : Nat}
theorem kwait_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).wait = if p then a.wait else b.wait := by split <;> rfl
theorem kcount_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).count = if p then a.count else b.count := by split <;> rfl
theorem kcarry_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).carry = if p then a.carry else b.carry := by split <;> rfl
theorem khf_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).h_field = if p then a.h_field else b.h_field := by split <;> rfl
theorem kreset_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).reset = if p then a.reset else b.reset := by split <;> rfl
theorem kv_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    kv (if p then a else b) = if p then kv a else kv b := by split <;> rfl
theorem akv_ite (p : Prop) [Decidable p] (a b : AuthState ψ) :
    akv (if p then a else b) = if p then akv a else akv b := by split <;> rfl
end Ite

section CoreStages
variable {ψ : Nat}

theorem clearCmp_kv (u : AgentState ψ) : kv (clearCmp u) = kv u := rfl

theorem genConnect_kv (u : AgentState ψ) : kv (cleanSigGenConnect u) = kv u := by
  cases h : u.path <;> simp only [cleanSigGenConnect, h] <;>
    simp [kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem releaseSource_kv (hψ : ψ > 0) (l r : AgentState ψ) :
    kv (releaseSource hψ l r).1 = kv l ∧ kv (releaseSource hψ l r).2 = kv r := by
  simp [releaseSource, fst_ite, snd_ite, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem eliminate_kv (hψ : ψ > 0) (l r : AgentState ψ) :
    kv (eliminateSig hψ l r).1 = kv l ∧ kv (eliminateSig hψ l r).2 = kv r := by
  simp [eliminateSig, fst_ite, snd_ite, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem control_kv (hψ : ψ > 0) (u : AgentState ψ) :
    kv (sigMoveApplyControlConsume hψ u) = kv u := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;>
    simp [kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem dropStale_kv (u : AgentState ψ) : kv (dropStale u) = kv u := by
  simp [dropStale, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem orphan_kv (u : AgentState ψ) : kv (normalizeOrphan u) = kv u := by
  cases h : u.path <;> simp [normalizeOrphan, h, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem carrier_kv (u : AgentState ψ) : kv (normalizeCarrier u) = kv u := by
  cases h : u.path <;>
    simp [normalizeCarrier, releaseCongest, h, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem ready_kv (u : AgentState ψ) : kv (normalizeReady u) = kv u := by
  generalize ho : normalizeOrphan u = o
  have vo : kv o = kv u := by rw [← ho]; exact orphan_kv u
  simp only [normalizeReady, ho]
  generalize hc : (if o.state = .none ∧ aligned o then o else normalizeCarrier o) = c
  have vc : kv c = kv o := by rw [← hc]; simp [kv_ite, carrier_kv]
  have ht := vc.trans vo
  cases hp : c.path <;> simpa [hp, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite] using ht

theorem checkReady_kv (u : AgentState ψ) : kv (checkSigSetReadyGuarded u) = kv u := by
  cases h : u.path <;>
    simp [checkSigSetReadyGuarded, checkSigSetReady, h, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem checkL_kv (hψ : ψ > 0) (u : AgentState ψ) : kv (checkSigCheckL hψ u) = kv u := by
  unfold checkSigCheckL
  split <;> simp [kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem checkR_kv (hψ : ψ > 0) (l r : AgentState ψ) : kv (checkSigCheckR hψ l r) = kv r := by
  unfold checkSigCheckR
  split <;> simp [kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem result_kv (u : AgentState ψ) : kv (checkSigSetResult u) = kv u := by
  simp [checkSigSetResult, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem disStart_kv (hψ : ψ > 0) (l r : AgentState ψ) :
    kv (disappearStartL hψ l r).1 = kv l ∧ kv (disappearStartL hψ l r).2 = kv r := by
  simp [disappearStartL, fst_ite, snd_ite, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem disCarry_kv (hψ : ψ > 0) (l r : AgentState ψ) :
    kv (disappearCarry hψ l r).1 = kv l ∧ kv (disappearCarry hψ l r).2 = kv r := by
  simp [disappearCarry, fst_ite, snd_ite, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem releaseSuffix_kv (l r : AgentState ψ) :
    kv (releaseReadySuffix l r).1 = kv l ∧ kv (releaseReadySuffix l r).2 = kv r := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [releaseReadySuffix, hl, hr, fst_ite, snd_ite, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem ackTail_kv (l r : AgentState ψ) :
    kv (ackTail l r).1 = kv l ∧ kv (ackTail l r).2 = kv r := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [ackTail, hl, hr, fst_ite, snd_ite, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem dropStray_kv (l r : AgentState ψ) :
    kv (dropStray l r).1 = kv l ∧ kv (dropStray l r).2 = kv r := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [dropStray, hl, hr, fst_ite, snd_ite, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem landBackward_kv (u : AgentState ψ) : kv (landBackward u) = kv u := by
  cases hp : u.path <;> cases ht : u.path2 <;>
    simp [landBackward, hp, ht, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]


theorem landForward_kv (κ : Nat) (u : AgentState ψ) :
    kv (landForward κ false true u) = kv u := by
  cases hp : u.path <;> cases ht : u.path2 <;>
    simp [landForward, hp, ht, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

theorem pPsi_kv (hψ : ψ > 0) (l r : AgentState ψ) :
    kv (pPsiProbeWall hψ l r).1 = kv l ∧ kv (pPsiProbeWall hψ l r).2 = kv r := by
  simp only [pPsiProbeWall, pPsi]
  simp [fst_ite, snd_ite, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

/-- Algorithm 14 writes `count` only on a pending `reset_cmd`. -/
theorem suppress_kv (hψ : ψ > 0) (l r : AgentState ψ) (h1 : l.leader = false)
    (h2 : l.reset_cmd = false) (h3 : r.reset_cmd = false) :
    kv (suppressSigResetKill hψ l r).1 = kv l ∧ kv (suppressSigResetKill hψ l r).2 = kv r := by
  cases h4 : r.echo <;>
    simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset, suppressSigTerminal,
      suppressSigEcho, suppressSigFinish, clearCmp, kv, h1, h2, h3, h4, fst_ite, snd_ite]

end CoreStages

/-! ### Lifts and small AuthF cell maps

Small maps are handled by splitting every `if`/`match` and closing each leaf,
which is a record update of the input cell (or a core function with a frame
lemma above). -/

/-- Close a leaf goal of a frame lemma. -/
syntax "kclose" : tactic
macro_rules
  | `(tactic| kclose) => `(tactic| first
      | exact ⟨rfl, rfl⟩
      | rfl
      | (simp only [akv, AuthState.withCore, AuthState.dropP2, AuthState.setState,
          AuthState.lineage, clearCmpAuth, genConnect_kv, control_kv, checkReady_kv,
          checkL_kv, checkR_kv, result_kv, landBackward_kv, and_self, and_true, true_and];
         first | done | rfl | exact ⟨rfl, rfl⟩))

/-- Split every `if`/`match` (zeta-reducing `let`s first) and close all leaves. -/
syntax "ksplit" : tactic
macro_rules
  | `(tactic| ksplit) => `(tactic| ((repeat' (first | (dsimp only) | split)) <;> kclose))

section AuthCells
variable {ψ : Nat}

theorem kv_core (u : AuthState ψ) : kv u.core = akv u := rfl
theorem kv_p4 (u : AgentState ψ) : kv { u with path4 := none } = kv u := rfl
theorem kv_p5 (u : AgentState ψ) : kv { u with path5 := none } = kv u := rfl
theorem akv_mk (c : AgentState ψ) (a b : ProvColor) (s : P2Scope) (d e f : ProvColor) :
    akv (AuthState.mk c a b s d e f) = kv c := rfl
theorem lift2_akv (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, kv (f a b).1 = kv a ∧ kv (f a b).2 = kv b) (l r : AuthState ψ) :
    akv (lift2 f l r).1 = akv l ∧ akv (lift2 f l r).2 = akv r :=
  hf l.core r.core

theorem lift2Life_akv (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, kv (f a b).1 = kv a ∧ kv (f a b).2 = kv b) (l r : AuthState ψ) :
    akv (lift2Life f l r).1 = akv l ∧ akv (lift2Life f l r).2 = akv r := by
  have h := hf l.core r.core
  unfold lift2Life
  dsimp only
  refine ⟨?_, ?_⟩ <;> split
  all_goals first | exact h.1 | exact h.2

theorem liftLife_akv (f : AgentState ψ → AgentState ψ) (hf : ∀ a, kv (f a) = kv a)
    (u : AuthState ψ) : akv (liftLife f u) = akv u := by
  unfold liftLife
  dsimp only
  split <;> exact hf u.core

theorem clearAuth_akv (u : AuthState ψ) : akv (clearCmpAuth u) = akv u := rfl
theorem dropP2_akv (u : AuthState ψ) : akv u.dropP2 = akv u := rfl
theorem setState_akv (u : AuthState ψ) (s : MainState) : akv (u.setState s) = akv u := rfl
theorem lineage_akv (u : AuthState ψ) (s : MainState) : akv (u.lineage s) = akv u := rfl
theorem withCore_akv (u : AuthState ψ) (c : AgentState ψ) : akv (u.withCore c) = kv c := rfl
theorem wipe_akv (γ : ProvColor) (u : AuthState ψ) : akv (wipeProduceAuth γ u) = akv u := rfl
theorem demote_akv (u : AuthState ψ) : akv (demote u) = akv u := rfl
theorem claimA2_akv (σ : ProvColor) (u : AuthState ψ) : akv (claimA2 σ u) = akv u := rfl

theorem receive_akv (e : Entry) (src dst : AuthState ψ) (t : Path2Info) :
    akv (receive e src dst t) = akv dst := by
  show kv (if e = .claim then claimA2 src.path2_mark dst else dst).core = kv dst.core
  split <;> rfl

theorem sanitize_akv (u : AuthState ψ) : akv (sanitizeP2 u) = akv u := by
  unfold sanitizeP2; ksplit

theorem issue_akv (u : AuthState ψ) : akv (issue u) = akv u := by
  unfold issue; ksplit

theorem readyAuth_akv (u : AuthState ψ) : akv (readyAuth u) = akv u := by
  unfold readyAuth; ksplit

theorem applyControl_akv (hψ : ψ > 0) (u : AuthState ψ) : akv (applyControlAuth hψ u) = akv u := by
  unfold applyControlAuth; ksplit

theorem genConnectAuth_akv (u : AuthState ψ) : akv (genConnectAuth u) = akv u := by
  unfold genConnectAuth; ksplit

theorem landBackwardAuth_akv (u : AuthState ψ) : akv (landBackwardAuth u) = akv u := by
  unfold landBackwardAuth; ksplit


theorem landForwardAuth_akv (κ : Nat) (u : AuthState ψ) : akv (landForwardAuth κ u) = akv u := by
  unfold landForwardAuth
  repeat' (first | (dsimp only) | split)
  all_goals first | rfl | exact landForward_kv κ u.core

theorem cleanApplyAuth_akv (u : AuthState ψ) : akv (cleanApplyAuth u) = akv u := by
  unfold cleanApplyAuth; ksplit

end AuthCells

/-! ### The AuthF comparison prefix, stage by stage -/

section AuthStages
variable {ψ : Nat}

theorem step3_akv (nbr mc : Bool) (l r : AuthState ψ) :
    akv (step3Auth nbr mc l r).1 = akv l ∧ akv (step3Auth nbr mc l r).2 = akv r := by
  unfold step3Auth; ksplit

theorem step4_akv (nbr mc : Bool) (l r : AuthState ψ) :
    akv (step4Auth nbr mc l r).1 = akv l ∧ akv (step4Auth nbr mc l r).2 = akv r := by
  unfold step4Auth; ksplit

theorem step5_akv (hψ : ψ > 0) (l r : AuthState ψ) :
    akv (step5Auth hψ l r).1 = akv l ∧ akv (step5Auth hψ l r).2 = akv r := by
  unfold step5Auth; ksplit

theorem step6_akv (hψ : ψ > 0) (l r : AuthState ψ) :
    akv (step6Auth hψ l r).1 = akv l ∧ akv (step6Auth hψ l r).2 = akv r := by
  unfold step6Auth; ksplit

/-- The simp set that rewrites a composite AuthF stage down to its input view. -/
theorem cleanSource_akv (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    akv (cleanSourceAuth hψ c l r).1 = akv l ∧ akv (cleanSourceAuth hψ c l r).2 = akv r := by
  simp only [cleanSourceAuth, fst_ite, snd_ite, akv_ite, akv_mk, kv_p4, kv_p5, kv_core, cleanApplyAuth_akv,
    step6_akv, step5_akv, step4_akv, step3_akv, genConnectAuth_akv, ite_self, and_self]

theorem validate_akv (l r : AuthState ψ) :
    akv (validateCheck l r).1 = akv l ∧ akv (validateCheck l r).2 = akv r := by
  unfold validateCheck; ksplit

theorem step1_akv (l r : AuthState ψ) :
    akv (step1Auth l r).1 = akv l ∧ akv (step1Auth l r).2 = akv r := by
  unfold step1Auth; ksplit

private theorem akvEq_ite {x a b : AuthState ψ} {p : Prop} [Decidable p] (ha : akv a = akv x)
    (hb : akv b = akv x) : akv (if p then a else b) = akv x := by
  by_cases hp : p
  · rw [if_pos hp]; exact ha
  · rw [if_neg hp]; exact hb

private theorem akvEq_dropP2 {x v : AuthState ψ} (h : akv v = akv x) : akv v.dropP2 = akv x :=
  (dropP2_akv v).trans h

private theorem akvEq_receive {x v : AuthState ψ} (e : Entry) (src : AuthState ψ)
    (t : Path2Info) (h : akv v = akv x) : akv (receive e src v t) = akv x :=
  (receive_akv e src v t).trans h

/-- Every output of the token transfer is its input, the input with `path2` dropped, a `receive`
into it or the cleared input, and each keeps `akv`; the proof follows the output terms and never
splits on the transfer guards (splitting every guard took 52 s). -/
theorem moveTokens_akv (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    akv (moveTokensAuth c l r).1 = akv l ∧ akv (moveTokensAuth c l r).2 = akv r := by
  unfold moveTokensAuth
  simp only [fst_ite, snd_ite]
  constructor
  all_goals
    repeat (first
      | with_reducible rfl
      | with_reducible exact clearAuth_akv _
      | with_reducible refine akvEq_receive _ _ _ ?_
      | with_reducible refine akvEq_dropP2 ?_
      | with_reducible refine akvEq_ite ?_ ?_
      | (simp only [fst_ite, snd_ite])
      | split)

theorem leaderWall_akv (l r : AuthState ψ) :
    akv (leaderWallAuth l r).1 = akv l ∧ akv (leaderWallAuth l r).2 = akv r := by
  unfold leaderWallAuth; ksplit

theorem moveSource_akv (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    akv (moveSourceAuth hψ c l r).1 = akv l ∧ akv (moveSourceAuth hψ c l r).2 = akv r := by
  simp only [moveSourceAuth, fst_ite, snd_ite, akv_ite, lineage_akv, applyControl_akv,
    leaderWall_akv, moveTokens_akv, step1_akv, sanitize_akv, validate_akv, clearAuth_akv,
    ite_self, and_self]

theorem preCheck_akv (l r : AuthState ψ) :
    akv (preCheckResetAuth l r).1 = akv l ∧ akv (preCheckResetAuth l r).2 = akv r := by
  unfold preCheckResetAuth; ksplit

theorem disappear_akv (hψ : ψ > 0) (l r : AuthState ψ) :
    akv (disappearAuth hψ l r).1 = akv l ∧ akv (disappearAuth hψ l r).2 = akv r := by
  have h1 := lift2_akv (disappearStartL hψ) (disStart_kv hψ)
  have h2 := lift2_akv (disappearCarry hψ) (disCarry_kv hψ)
  unfold disappearAuth
  dsimp only
  split <;> simp only [h2, h1, true_and, and_self]
  all_goals kclose

theorem repair_akv (l r : AuthState ψ) :
    akv (repairAuth l r).1 = akv l ∧ akv (repairAuth l r).2 = akv r := by
  have hc : ∀ a : AgentState ψ, kv (normalizeCarrier (normalizeOrphan a)) = kv a :=
    fun a => (carrier_kv _).trans (orphan_kv a)
  have hl := liftLife_akv _ hc
  have hr := lift2Life_akv (ψ := ψ) releaseReadySuffix releaseSuffix_kv
  have ha : ∀ a b : AuthState ψ, akv (ackTailAuth a b).1 = akv a ∧ akv (ackTailAuth a b).2 = akv b := by
    intro a b
    unfold ackTailAuth; split
    · exact lift2_akv ackTail ackTail_kv a b
    · exact ⟨rfl, rfl⟩
  simp only [repairAuth, ha, hr, hl, and_self]

theorem maintain_akv (l r : AuthState ψ) :
    akv (maintainAuth l r).1 = akv l ∧ akv (maintainAuth l r).2 = akv r := by
  unfold maintainAuth; ksplit

theorem completeWave_akv (l r : AuthState ψ) :
    akv (completeWaveAuth l r).1 = akv l ∧ akv (completeWaveAuth l r).2 = akv r := by
  unfold completeWaveAuth; ksplit

theorem wave_akv (l r : AuthState ψ) :
    akv (waveAuth l r).1 = akv l ∧ akv (waveAuth l r).2 = akv r := by
  unfold waveAuth; ksplit


/-- CHECK preserves the writer projection on both endpoints; its terminal
birth writes only `leader`. -/
theorem checkSource_akv (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    akv (checkSourceAuth hψ c l r).1 = akv l ∧ akv (checkSourceAuth hψ c l r).2 = akv r := by
  have hb : ∀ (C : Prop) [Decidable C] (B : AuthState ψ),
      akv (if C then { B with core := { B.core with leader := true } } else B) = akv B := by
    intro C _ B; split <;> rfl
  simp only [checkSourceAuth, fst_ite, snd_ite, hb, akv_ite, akv_mk, kv_core, withCore_akv,
    lineage_akv, issue_akv, readyAuth_akv, checkL_kv, checkR_kv, checkReady_kv, validate_akv,
    ite_self, and_self]

/-- The comparison lifecycle preserves the writer projection on both endpoints;
the BEQ birth in `landForward` writes only `leader` and `path2`. -/
theorem compare_akv (κ : Nat) (l r : AuthState ψ) :
    akv (compareLifecycleAuth κ l r).1 = akv l ∧ akv (compareLifecycleAuth κ l r).2 = akv r := by
  have hd := lift2_akv (ψ := ψ) dropStray dropStray_kv
  unfold compareLifecycleAuth
  dsimp only
  split
  all_goals (try split)
  all_goals simp only [landBackwardAuth_akv, landForwardAuth_akv, hd, wave_akv, completeWave_akv,
    maintain_akv, setState_akv, and_self]

end AuthStages


/-- The AuthF stages after GENSIG and before Algorithm 14 keep the WAIT view. -/
theorem restPair_akv {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ) :
    akv (restPair hψ κ c q).1 = akv q.1 ∧ akv (restPair hψ κ c q).2 = akv q.2 := by
  obtain ⟨a1, b1⟩ := q
  simp only [restPair, restLo, restHi, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11]
  have h2 := cleanSource_akv hψ c a1 b1
  generalize cleanSourceAuth hψ c a1 b1 = q2 at h2
  obtain ⟨a2, b2⟩ := q2
  simp only at h2 ⊢
  have h3 := lift2Life_akv (releaseSource hψ) (releaseSource_kv hψ) a2 b2
  generalize lift2Life (releaseSource hψ) a2 b2 = q3 at h3
  obtain ⟨a3, b3⟩ := q3
  simp only at h3 ⊢
  have h4 := lift2_akv (eliminateSig hψ) (eliminate_kv hψ) a3 b3
  generalize lift2 (eliminateSig hψ) a3 b3 = q4 at h4
  obtain ⟨a4, b4⟩ := q4
  simp only at h4 ⊢
  have h5 := moveSource_akv hψ c a4 b4
  generalize moveSourceAuth hψ c a4 b4 = q5 at h5
  obtain ⟨a5, b5⟩ := q5
  simp only at h5 ⊢
  have h6 := preCheck_akv (liftLife dropStale a5) (liftLife dropStale b5)
  rw [liftLife_akv _ dropStale_kv, liftLife_akv _ dropStale_kv] at h6
  generalize preCheckResetAuth (liftLife dropStale a5) (liftLife dropStale b5) = q6 at h6
  obtain ⟨a6, b6⟩ := q6
  simp only at h6 ⊢
  have e7 := liftLife_akv _ ready_kv a6
  have f7 := liftLife_akv _ ready_kv b6
  generalize liftLife normalizeReady a6 = a7 at e7
  generalize liftLife normalizeReady b6 = b7 at f7
  have h8 := checkSource_akv hψ c a7 b7
  generalize checkSourceAuth hψ c a7 b7 = q8 at h8
  obtain ⟨a8, b8⟩ := q8
  simp only at h8 ⊢
  have h9 := disappear_akv hψ a8 b8
  generalize disappearAuth hψ a8 b8 = q9 at h9
  obtain ⟨a9, b9⟩ := q9
  simp only at h9 ⊢
  have h10 := repair_akv a9 b9
  generalize repairAuth a9 b9 = q10 at h10
  obtain ⟨a10, b10⟩ := q10
  simp only at h10 ⊢
  have h11 := compare_akv κ a10 b10
  generalize compareLifecycleAuth κ a10 b10 = q11 at h11
  obtain ⟨a11, b11⟩ := q11
  simp only at h11 ⊢
  exact ⟨by rw [h11.1, h10.1, h9.1, h8.1, e7, h6.1, h5.1, h4.1, h3.1, h2.1],
    by rw [h11.2, h10.2, h9.2, h8.2, f7, h6.2, h5.2, h4.2, h3.2, h2.2]⟩

/-- K4 writes no WAIT register. -/
theorem kernel_kv {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    kv (k4Kernel hp l r).1 = kv l ∧ kv (k4Kernel hp l r).2 = kv r := by
  simp only [k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire, absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp [fst_ite, snd_ite, kv_ite, kv, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite]

/-! ### The writer keeps the WAIT view

Field-wise copy of `PPLLAstraReadyThree.Writer.writeSeq_frame`. -/

section Writer
variable {ψ : Nat}

/-- The five WAIT registers agree. -/
def KF (a b : AgentState ψ) : Prop :=
  a.wait = b.wait ∧ a.count = b.count ∧ a.carry = b.carry ∧ a.h_field = b.h_field ∧ a.reset = b.reset

theorem kv_of_KF {a b : AgentState ψ} (h : KF a b) : kv a = kv b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [kv, h1, h2, h3, h4, h5]

theorem writeActionApplyOverwrite_kf (u : AgentState ψ) :
    KF (writeActionApplyOverwrite u) u := by
  unfold KF writeActionApplyOverwrite
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem writeActionApplyMoveFlip_kf (u : AgentState ψ) :
    KF (writeActionApplyMoveFlip u) u := by
  unfold KF writeActionApplyMoveFlip
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem moveWsigCheckLast_kf (u : AgentState ψ) :
    KF (moveWsigCheckLast u) u := by
  unfold KF moveWsigCheckLast
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem writeSeqSetWriteReady_kf (u : AgentState ψ) :
    KF (writeSeqSetWriteReady u) u := by
  unfold KF writeSeqSetWriteReady
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem writeSeqCheckBit_kf (u : AgentState ψ) :
    KF (writeSeqCheckBit u) u := by
  unfold KF writeSeqCheckBit
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem writeSeqSetWriteAct_kf (u : AgentState ψ) :
    KF (writeSeqSetWriteAct u) u := by
  cases hp : u.path3 <;> simp only [KF, writeSeqSetWriteAct, hp] <;>
    simp [kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite, hp]

theorem writeSeqFinalR_kf (u : AgentState ψ) :
    KF (writeSeqFinalR u) u := by
  unfold KF writeSeqFinalR
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem moveWsigCheckGenWs_kf (l r : AgentState ψ) :
    KF (moveWsigCheckGenWs l r) r := by
  unfold KF moveWsigCheckGenWs
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem moveWsigTransfer_kf (l r : AgentState ψ) :
    KF (moveWsigTransfer l r).1 l ∧ KF (moveWsigTransfer l r).2 r := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp only [KF, moveWsigTransfer, hl, hr] <;>
    simp only [fst_ite, snd_ite, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite, ite_self, and_self]

theorem groupInfo_kf (hψ : ψ > 0) (l r : AgentState ψ) :
    KF (groupInfo hψ l r).1 l ∧ KF (groupInfo hψ l r).2 r := by
  simp only [KF, groupInfo]
  simp only [fst_ite, snd_ite, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite, ite_self, and_self]

theorem gensigWriteseq_kf (hψ : ψ > 0) (l r : AgentState ψ) :
    KF (gensigWriteseq hψ l r).1 l ∧ KF (gensigWriteseq hψ l r).2 r := by
  simp only [KF, gensigWriteseq]
  simp only [fst_ite, snd_ite, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite, ite_self, and_self]

theorem writeAction_kf (hψ : ψ > 0) (l r : AgentState ψ) :
    KF (writeAction hψ l r).1 l ∧ KF (writeAction hψ l r).2 r := by
  simp only [KF, writeAction]
  simp only [fst_ite, snd_ite, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite, ite_self, and_self , (writeActionApplyOverwrite_kf _).1, (writeActionApplyOverwrite_kf _).2.1, (writeActionApplyOverwrite_kf _).2.2.1, (writeActionApplyOverwrite_kf _).2.2.2.1, (writeActionApplyOverwrite_kf _).2.2.2.2, (writeActionApplyMoveFlip_kf _).1, (writeActionApplyMoveFlip_kf _).2.1, (writeActionApplyMoveFlip_kf _).2.2.1, (writeActionApplyMoveFlip_kf _).2.2.2.1, (writeActionApplyMoveFlip_kf _).2.2.2.2]

theorem moveWsig_kf (hψ : ψ > 0) (l r : AgentState ψ) :
    KF (moveWsig hψ l r).1 l ∧ KF (moveWsig hψ l r).2 r := by
  simp only [KF, moveWsig]
  simp only [fst_ite, snd_ite, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite, ite_self, and_self , (moveWsigCheckGenWs_kf _ _).1, (moveWsigCheckGenWs_kf _ _).2.1, (moveWsigCheckGenWs_kf _ _).2.2.1, (moveWsigCheckGenWs_kf _ _).2.2.2.1, (moveWsigCheckGenWs_kf _ _).2.2.2.2, (moveWsigCheckLast_kf _).1, (moveWsigCheckLast_kf _).2.1, (moveWsigCheckLast_kf _).2.2.1, (moveWsigCheckLast_kf _).2.2.2.1, (moveWsigCheckLast_kf _).2.2.2.2, (moveWsigTransfer_kf _ _).1.1, (moveWsigTransfer_kf _ _).1.2.1, (moveWsigTransfer_kf _ _).1.2.2.1, (moveWsigTransfer_kf _ _).1.2.2.2.1, (moveWsigTransfer_kf _ _).1.2.2.2.2, (moveWsigTransfer_kf _ _).2.1, (moveWsigTransfer_kf _ _).2.2.1, (moveWsigTransfer_kf _ _).2.2.2.1, (moveWsigTransfer_kf _ _).2.2.2.2.1, (moveWsigTransfer_kf _ _).2.2.2.2.2]

theorem writeSeq_kf (hψ : ψ > 0) (l r : AgentState ψ) :
    KF (writeSeq hψ l r).1 l ∧ KF (writeSeq hψ l r).2 r := by
  simp only [KF, writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands]
  simp only [fst_ite, snd_ite, kwait_ite, kcount_ite, kcarry_ite, khf_ite, kreset_ite, ite_self, and_self, (groupInfo_kf _ _ _).1.1, (groupInfo_kf _ _ _).1.2.1, (groupInfo_kf _ _ _).1.2.2.1, (groupInfo_kf _ _ _).1.2.2.2.1, (groupInfo_kf _ _ _).1.2.2.2.2, (groupInfo_kf _ _ _).2.1, (groupInfo_kf _ _ _).2.2.1, (groupInfo_kf _ _ _).2.2.2.1, (groupInfo_kf _ _ _).2.2.2.2.1, (groupInfo_kf _ _ _).2.2.2.2.2, (gensigWriteseq_kf _ _ _).1.1, (gensigWriteseq_kf _ _ _).1.2.1, (gensigWriteseq_kf _ _ _).1.2.2.1, (gensigWriteseq_kf _ _ _).1.2.2.2.1, (gensigWriteseq_kf _ _ _).1.2.2.2.2, (gensigWriteseq_kf _ _ _).2.1, (gensigWriteseq_kf _ _ _).2.2.1, (gensigWriteseq_kf _ _ _).2.2.2.1, (gensigWriteseq_kf _ _ _).2.2.2.2.1, (gensigWriteseq_kf _ _ _).2.2.2.2.2, (writeAction_kf _ _ _).1.1, (writeAction_kf _ _ _).1.2.1, (writeAction_kf _ _ _).1.2.2.1, (writeAction_kf _ _ _).1.2.2.2.1, (writeAction_kf _ _ _).1.2.2.2.2, (writeAction_kf _ _ _).2.1, (writeAction_kf _ _ _).2.2.1, (writeAction_kf _ _ _).2.2.2.1, (writeAction_kf _ _ _).2.2.2.2.1, (writeAction_kf _ _ _).2.2.2.2.2, (moveWsig_kf _ _ _).1.1, (moveWsig_kf _ _ _).1.2.1, (moveWsig_kf _ _ _).1.2.2.1, (moveWsig_kf _ _ _).1.2.2.2.1, (moveWsig_kf _ _ _).1.2.2.2.2, (moveWsig_kf _ _ _).2.1, (moveWsig_kf _ _ _).2.2.1, (moveWsig_kf _ _ _).2.2.2.1, (moveWsig_kf _ _ _).2.2.2.2.1, (moveWsig_kf _ _ _).2.2.2.2.2, (writeSeqSetWriteReady_kf _).1, (writeSeqSetWriteReady_kf _).2.1, (writeSeqSetWriteReady_kf _).2.2.1, (writeSeqSetWriteReady_kf _).2.2.2.1, (writeSeqSetWriteReady_kf _).2.2.2.2, (writeSeqCheckBit_kf _).1, (writeSeqCheckBit_kf _).2.1, (writeSeqCheckBit_kf _).2.2.1, (writeSeqCheckBit_kf _).2.2.2.1, (writeSeqCheckBit_kf _).2.2.2.2, (writeSeqSetWriteAct_kf _).1, (writeSeqSetWriteAct_kf _).2.1, (writeSeqSetWriteAct_kf _).2.2.1, (writeSeqSetWriteAct_kf _).2.2.2.1, (writeSeqSetWriteAct_kf _).2.2.2.2, (writeSeqFinalR_kf _).1, (writeSeqFinalR_kf _).2.1, (writeSeqFinalR_kf _).2.2.1, (writeSeqFinalR_kf _).2.2.2.1, (writeSeqFinalR_kf _).2.2.2.2]


theorem write_kv (hψ : ψ > 0) (l r : AgentState ψ) :
    kv (writeWithBundle hψ l r).1 = kv l ∧ kv (writeWithBundle hψ l r).2 = kv r := by
  have h := writeSeq_kf hψ l r
  unfold writeWithBundle
  generalize writeSeq hψ l r = q at h
  obtain ⟨a, b⟩ := q
  have e1 := kv_of_KF h.1
  have e2 := kv_of_KF h.2
  dsimp only at e1 e2 ⊢
  split
  · exact ⟨e1, e2⟩
  · exact ⟨e1, e2⟩

end Writer

/-! ## Part A2. A pathless initiator stays pathless

The `MonoC` machinery of `PPLLAuthGenDrain` Part B/C with the relation
`a.path = bot → b.path = bot`. -/

section Mono
variable {ψ : Nat}

/-- A pathless cell stays pathless. -/
def MonoC_P (a b : AgentState ψ) : Prop := a.path = .bot → b.path = .bot

def MonoA_P (a b : AuthState ψ) : Prop := MonoC_P a.core b.core

theorem MonoC_P.refl (a : AgentState ψ) : MonoC_P a a := id

theorem MonoC_P.trans {a b c : AgentState ψ} (h1 : MonoC_P a b) (h2 : MonoC_P b c) : MonoC_P a c :=
  fun h => h2 (h1 h)

theorem MonoA_P.refl (a : AuthState ψ) : MonoA_P a a := MonoC_P.refl _

theorem MonoA_P.trans {a b c : AuthState ψ} (h1 : MonoA_P a b) (h2 : MonoA_P b c) : MonoA_P a c :=
  MonoC_P.trans h1 h2

/-- Same path. -/
theorem MonoC_P.of_eq {a b : AgentState ψ} (h2 : b.path = a.path) : MonoC_P a b := by
  intro h; rw [h2]; exact h

/-- Path deleted. -/
theorem MonoC_P.of_bot {a b : AgentState ψ} (h2 : b.path = .bot) : MonoC_P a b := fun _ => h2

/-- Close a `MonoC_P` leaf that is a record update of the input cell. -/
syntax "mclose_P" : tactic
macro_rules
  | `(tactic| mclose_P) => `(tactic| first
      | exact MonoC_P.refl _
      | exact MonoA_P.refl _
      | (apply MonoC_P.of_eq; rfl)
      | (apply MonoC_P.of_bot; rfl)
      | trivial
      | (simp only [MonoA_P, AuthState.withCore, AuthState.dropP2, AuthState.setState,
          AuthState.lineage, clearCmpAuth, clearCmp, AuthState.st]
         first
         | exact MonoC_P.refl _
         | (apply MonoC_P.of_eq; rfl)
         | (apply MonoC_P.of_bot; rfl)))

/-- Split all `if`/`match` and close every leaf (a pair of `MonoA_P`/`MonoC_P` goals). -/
syntax "msplit_P" : tactic
macro_rules
  | `(tactic| msplit_P) => `(tactic| ((repeat' (first | (dsimp only) | split)) <;>
      (first | (constructor <;> mclose_P) | mclose_P)))

/-! ### Core functions -/

theorem genConnect_mono_P (u : AgentState ψ) : MonoC_P u (cleanSigGenConnect u) := by
  unfold cleanSigGenConnect; msplit_P

theorem releaseSource_mono_P (hψ : ψ > 0) (l r : AgentState ψ) :
    MonoC_P l (releaseSource hψ l r).1 ∧ MonoC_P r (releaseSource hψ l r).2 := by
  unfold releaseSource; msplit_P

theorem eliminate_mono_P (hψ : ψ > 0) (l r : AgentState ψ) :
    MonoC_P l (eliminateSig hψ l r).1 ∧ MonoC_P r (eliminateSig hψ l r).2 := by
  unfold eliminateSig; msplit_P

theorem control_mono_P (hψ : ψ > 0) (u : AgentState ψ) :
    MonoC_P u (sigMoveApplyControlConsume hψ u) := by
  unfold sigMoveApplyControlConsume; msplit_P

theorem dropStale_mono_P (u : AgentState ψ) : MonoC_P u (dropStale u) := by
  unfold dropStale; msplit_P

theorem orphan_mono_P (u : AgentState ψ) : MonoC_P u (normalizeOrphan u) := by
  unfold normalizeOrphan; msplit_P

theorem releaseCongest_mono_P (u : AgentState ψ) : MonoC_P u (releaseCongest u) := by
  unfold releaseCongest; msplit_P

theorem carrier_mono_P (u : AgentState ψ) : MonoC_P u (normalizeCarrier u) := by
  unfold normalizeCarrier
  split
  · exact MonoC_P.refl _
  · split
    · exact releaseCongest_mono_P u
    · split <;> mclose_P

theorem checkReady_mono_P (u : AgentState ψ) : MonoC_P u (checkSigSetReadyGuarded u) := by
  unfold checkSigSetReadyGuarded checkSigSetReady; msplit_P

theorem checkL_mono_P (hψ : ψ > 0) (u : AgentState ψ) : MonoC_P u (checkSigCheckL hψ u) := by
  unfold checkSigCheckL; msplit_P

theorem checkR_mono_P (hψ : ψ > 0) (l r : AgentState ψ) : MonoC_P r (checkSigCheckR hψ l r) := by
  unfold checkSigCheckR; msplit_P

theorem result_mono_P (u : AgentState ψ) : MonoC_P u (checkSigSetResult u) := by
  unfold checkSigSetResult; msplit_P

theorem disStart_mono_P (hψ : ψ > 0) (l r : AgentState ψ) :
    MonoC_P l (disappearStartL hψ l r).1 ∧ MonoC_P r (disappearStartL hψ l r).2 := by
  unfold disappearStartL; msplit_P

theorem disCarry_mono_P (hψ : ψ > 0) (l r : AgentState ψ) :
    MonoC_P l (disappearCarry hψ l r).1 ∧ MonoC_P r (disappearCarry hψ l r).2 := by
  unfold disappearCarry; msplit_P

theorem releaseSuffix_mono_P (l r : AgentState ψ) :
    MonoC_P l (releaseReadySuffix l r).1 ∧ MonoC_P r (releaseReadySuffix l r).2 := by
  unfold releaseReadySuffix; msplit_P

theorem ackTail_mono_P (l r : AgentState ψ) :
    MonoC_P l (ackTail l r).1 ∧ MonoC_P r (ackTail l r).2 := by
  unfold ackTail; msplit_P

theorem dropStray_mono_P (l r : AgentState ψ) :
    MonoC_P l (PPLLFableDesignR1.dropStray l r).1 ∧ MonoC_P r (PPLLFableDesignR1.dropStray l r).2 := by
  unfold PPLLFableDesignR1.dropStray; msplit_P

theorem landBackward_mono_P (u : AgentState ψ) : MonoC_P u (PPLLFableDesignR1.landBackward u) := by
  unfold PPLLFableDesignR1.landBackward; msplit_P

theorem landForward_mono_P (κ : Nat) (d e : Bool) (u : AgentState ψ) :
    MonoC_P u (PPLLFableDesignR1.landForward κ d e u) := by
  unfold PPLLFableDesignR1.landForward; msplit_P

end Mono

/-! ### AuthF stages -/

section MonoStages
variable {ψ : Nat}

/-- Both endpoints of a pair stage output are `MonoA_P`-descendants of the inputs. -/
def PM_P (q : AuthState ψ × AuthState ψ) (l r : AuthState ψ) : Prop := MonoA_P l q.1 ∧ MonoA_P r q.2

theorem PM_P.trans {l r : AuthState ψ} {q q' : AuthState ψ × AuthState ψ}
    (h1 : PM_P q l r) (h2 : PM_P q' q.1 q.2) : PM_P q' l r :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem PM_P.refl (l r : AuthState ψ) : PM_P (l, r) l r := ⟨MonoA_P.refl _, MonoA_P.refl _⟩

theorem liftLife_mono_P (f : AgentState ψ → AgentState ψ) (hf : ∀ a, MonoC_P a (f a))
    (u : AuthState ψ) : MonoA_P u (liftLife f u) := by
  unfold liftLife; dsimp only
  split
  · exact hf u.core
  · exact hf u.core

theorem lift2_pm_P (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, MonoC_P a (f a b).1 ∧ MonoC_P b (f a b).2) (l r : AuthState ψ) :
    PM_P (lift2 f l r) l r := hf l.core r.core

theorem lift2Life_pm_P (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, MonoC_P a (f a b).1 ∧ MonoC_P b (f a b).2) (l r : AuthState ψ) :
    PM_P (lift2Life f l r) l r := by
  have h := hf l.core r.core
  unfold lift2Life PM_P
  constructor
  · dsimp only
    split
    · exact h.1
    · exact h.1
  · dsimp only
    split
    · exact h.2
    · exact h.2

theorem clearAuth_mono_P (u : AuthState ψ) : MonoA_P u (clearCmpAuth u) := by
  unfold MonoA_P; first | (apply MonoC_P.of_eq; rfl) | (apply MonoC_P.of_bot; rfl)

theorem dropP2_mono_P (u : AuthState ψ) : MonoA_P u u.dropP2 := MonoC_P.of_eq rfl

theorem genConnectAuth_mono_P (u : AuthState ψ) : MonoA_P u (genConnectAuth u) := by
  unfold genConnectAuth
  split
  · exact genConnect_mono_P u.core
  · exact MonoA_P.refl u

theorem step3_pm_P (nbr mc : Bool) (l r : AuthState ψ) : PM_P (step3Auth nbr mc l r) l r := by
  unfold step3Auth PM_P; msplit_P

theorem step4_pm_P (nbr mc : Bool) (l r : AuthState ψ) : PM_P (step4Auth nbr mc l r) l r := by
  unfold step4Auth PM_P; msplit_P

theorem step5_pm_P (hψ : ψ > 0) (l r : AuthState ψ) : PM_P (step5Auth hψ l r) l r := by
  unfold step5Auth PM_P; msplit_P

theorem step6_pm_P (hψ : ψ > 0) (l r : AuthState ψ) : PM_P (step6Auth hψ l r) l r := by
  unfold step6Auth PM_P; msplit_P

theorem cleanApplyAuth_mono_P (u : AuthState ψ) : MonoA_P u (cleanApplyAuth u) := by
  unfold cleanApplyAuth; msplit_P

theorem cleanSource_pm_P (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    PM_P (cleanSourceAuth hψ c l r) l r := by
  unfold cleanSourceAuth
  dsimp only
  have g1 := genConnectAuth_mono_P l
  have g2 := genConnectAuth_mono_P r
  generalize genConnectAuth l = l1 at g1 ⊢
  generalize genConnectAuth r = r1 at g2 ⊢
  have h3 := step3_pm_P c.cleanNbr c.markClean l1 r1
  generalize step3Auth c.cleanNbr c.markClean l1 r1 = q3 at h3 ⊢
  obtain ⟨l3, r3⟩ := q3
  have h4 := step4_pm_P c.cleanNbr c.markClean l3 r3
  generalize step4Auth c.cleanNbr c.markClean l3 r3 = q4 at h4 ⊢
  obtain ⟨l4, r4⟩ := q4
  have h5 : PM_P (if isCmd l4.core.path4 = true then
      (l4, { r4 with core := { r4.core with path4 := none } }) else step5Auth hψ l4 r4) l4 r4 := by
    split
    · exact ⟨MonoA_P.refl _, MonoC_P.of_eq rfl⟩
    · exact step5_pm_P hψ l4 r4
  generalize (if isCmd l4.core.path4 = true then
      (l4, { r4 with core := { r4.core with path4 := none } }) else step5Auth hψ l4 r4) = q5 at h5 ⊢
  obtain ⟨l5, r5⟩ := q5
  have h6 : PM_P (if isCmd r5.core.path5 = true then
      ({ l5 with core := { l5.core with path5 := none } }, r5) else step6Auth hψ l5 r5) l5 r5 := by
    split
    · exact ⟨MonoC_P.of_eq rfl, MonoA_P.refl _⟩
    · exact step6_pm_P hψ l5 r5
  generalize (if isCmd r5.core.path5 = true then
      ({ l5 with core := { l5.core with path5 := none } }, r5) else step6Auth hψ l5 r5) = q6 at h6 ⊢
  obtain ⟨l6, r6⟩ := q6
  exact ⟨g1.trans (h3.1.trans (h4.1.trans (h5.1.trans (h6.1.trans (cleanApplyAuth_mono_P _))))),
    g2.trans (h3.2.trans (h4.2.trans (h5.2.trans (h6.2.trans (cleanApplyAuth_mono_P _)))))⟩

theorem validate_pm_P (l r : AuthState ψ) : PM_P (validateCheck l r) l r := by
  unfold validateCheck PM_P demote; msplit_P

theorem sanitize_mono_P (u : AuthState ψ) : MonoA_P u (sanitizeP2 u) := by
  unfold sanitizeP2; msplit_P

/-- Step 1 moves a path only into the responder. -/
theorem step1_pm_P (l r : AuthState ψ) : MonoA_P l (step1Auth l r).1 := by
  unfold step1Auth; (repeat' (first | (dsimp only) | split)) <;> mclose_P

theorem receive_mono_P (e : Entry) (src dst : AuthState ψ) (t : Path2Info) :
    MonoA_P dst (receive e src dst t) := by
  unfold receive claimA2; msplit_P

theorem receive_drop_mono_P (e : Entry) (src dst : AuthState ψ) (t : Path2Info) (b : Prop)
    [Decidable b] : MonoA_P dst (receive e src (if b then dst.dropP2 else dst) t) := by
  split
  · exact MonoA_P.trans (dropP2_mono_P dst) (receive_mono_P e src _ t)
  · exact receive_mono_P e src dst t

private theorem monoP_ite {u a b : AuthState ψ} {p : Prop} [Decidable p] (ha : MonoA_P u a)
    (hb : MonoA_P u b) : MonoA_P u (if p then a else b) := by
  by_cases hp : p
  · rw [if_pos hp]; exact ha
  · rw [if_neg hp]; exact hb

private theorem monoP_dropP2 {u v : AuthState ψ} (h : MonoA_P u v) : MonoA_P u v.dropP2 :=
  h.trans (dropP2_mono_P v)

private theorem monoP_receive {u v : AuthState ψ} (e : Entry) (src : AuthState ψ)
    (t : Path2Info) (h : MonoA_P u v) : MonoA_P u (receive e src v t) :=
  h.trans (receive_mono_P e src v t)

/-- As `moveTokens_akv`: `MonoA_P` from the input is closed under each output operation and
under `if` (splitting every guard took 57 s under a scoped 4000000-heartbeat budget). -/
theorem moveTokens_pm_P (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    PM_P (moveTokensAuth c l r) l r := by
  unfold PM_P moveTokensAuth
  simp only [fst_ite, snd_ite]
  constructor
  all_goals
    repeat (first
      | with_reducible exact MonoA_P.refl _
      | with_reducible exact clearAuth_mono_P _
      | with_reducible refine monoP_receive _ _ _ ?_
      | with_reducible refine monoP_dropP2 ?_
      | with_reducible refine monoP_ite ?_ ?_
      | (simp only [fst_ite, snd_ite])
      | split)

theorem leaderWall_pm_P (l r : AuthState ψ) : PM_P (leaderWallAuth l r) l r := by
  unfold leaderWallAuth PM_P
  dsimp only
  refine ⟨?_, ?_⟩ <;> split
  all_goals first | exact clearAuth_mono_P _ | exact MonoA_P.refl _

theorem applyControl_mono_P (hψ : ψ > 0) (u : AuthState ψ) : MonoA_P u (applyControlAuth hψ u) := by
  unfold applyControlAuth
  (repeat' (first | (dsimp only) | split))
  all_goals first
    | exact MonoA_P.refl _
    | exact dropP2_mono_P _
    | exact control_mono_P hψ u.core

theorem moveSource_pm_P (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    MonoA_P l (moveSourceAuth hψ c l r).1 := by
  unfold moveSourceAuth
  dsimp only
  have ha : MonoA_P l (if l.core.leader = true ∨ (r.core.leader = true ∧
      r.core.label ≠ ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) then clearCmpAuth l else l) := by
    split
    · exact clearAuth_mono_P l
    · exact MonoA_P.refl l
  have hb : MonoA_P r (if r.core.leader = true then clearCmpAuth r else r) := by
    split
    · exact clearAuth_mono_P r
    · exact MonoA_P.refl r
  generalize (if l.core.leader = true ∨ (r.core.leader = true ∧
      r.core.label ≠ ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) then clearCmpAuth l else l) = l0 at ha ⊢
  generalize (if r.core.leader = true then clearCmpAuth r else r) = r0 at hb ⊢
  have h1 := validate_pm_P l0 r0
  generalize validateCheck l0 r0 = q1 at h1 ⊢
  obtain ⟨l1, r1⟩ := q1
  have s1 := sanitize_mono_P l1
  have s2 := sanitize_mono_P r1
  generalize sanitizeP2 l1 = l2 at s1 ⊢
  generalize sanitizeP2 r1 = r2 at s2 ⊢
  have h3 : MonoA_P l2 (if l2.st = MainState.done then (l2, r2) else step1Auth l2 r2).1 := by
    split
    · exact MonoA_P.refl l2
    · exact step1_pm_P l2 r2
  generalize (if l2.st = MainState.done then (l2, r2) else step1Auth l2 r2) = q3 at h3 ⊢
  obtain ⟨l3, r3⟩ := q3
  have h4 := moveTokens_pm_P c l3 r3
  generalize moveTokensAuth c l3 r3 = q4 at h4 ⊢
  obtain ⟨l4, r4⟩ := q4
  have h5 := leaderWall_pm_P l4 r4
  generalize leaderWallAuth l4 r4 = q5 at h5 ⊢
  obtain ⟨l5, r5⟩ := q5
  have a1 := applyControl_mono_P hψ l5
  have a2 := applyControl_mono_P hψ r5
  generalize applyControlAuth hψ l5 = l6 at a1 ⊢
  generalize applyControlAuth hψ r5 = r6 at a2 ⊢
  have h7 : MonoA_P l6 (if r6.st = MainState.depart ∧ l6.core.label.val < ψ - 1 ∧
      l6.st = MainState.CHECK_ready then l6.lineage MainState.depart else l6) := by
    split
    · exact MonoC_P.of_eq rfl
    · exact MonoA_P.refl l6
  exact ha.trans (h1.1.trans (s1.trans (h3.trans (h4.1.trans (h5.1.trans (a1.trans h7))))))

theorem preCheck_pm_P (l r : AuthState ψ) : PM_P (preCheckResetAuth l r) l r := by
  unfold preCheckResetAuth PM_P
  dsimp only
  refine ⟨?_, ?_⟩ <;> split
  all_goals first | exact clearAuth_mono_P _ | exact MonoA_P.refl _

theorem normalizeReady_mono_P (u : AgentState ψ) : MonoC_P u (normalizeReady u) := by
  unfold normalizeReady
  dsimp only
  have h1 := orphan_mono_P u
  generalize normalizeOrphan u = u1 at h1 ⊢
  have h2 : MonoC_P u1 (if u1.state = MainState.none ∧ aligned u1 = true then u1
      else normalizeCarrier u1) := by
    split
    · exact MonoC_P.refl _
    · exact carrier_mono_P u1
  generalize (if u1.state = MainState.none ∧ aligned u1 = true then u1
      else normalizeCarrier u1) = u2 at h2 ⊢
  refine h1.trans (h2.trans ?_)
  msplit_P

theorem readyAuth_mono_P (u : AuthState ψ) : MonoA_P u (readyAuth u) := by
  unfold readyAuth
  dsimp only
  split
  · exact MonoA_P.refl u
  · have h := checkReady_mono_P u.core
    split
    · exact h
    · exact h

theorem issue_mono_P (u : AuthState ψ) : MonoA_P u (issue u) := by
  unfold issue
  split
  · exact result_mono_P u.core
  · exact MonoA_P.refl u

/-! CHECK decomposed into named cell steps (definitionally equal to `checkSourceAuth`). -/

def csA_P (c : PPLLAuthF.Cfg) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  (if (!c.strictReady || isHead l) = true then readyAuth l else l,
   if (!c.strictReady || isHead r) = true then readyAuth r else r)

def csB_P (l r : AuthState ψ) : AuthState ψ :=
  if r.st = .depart ∧ aligned r.core ∧ l.st = .equal ∧ aligned l.core ∧
      l.core.label.val < ψ - 1 then l.lineage .depart else l

def csC_P (hψ : ψ > 0) (l : AuthState ψ) : AuthState ψ := l.withCore (checkSigCheckL hψ l.core)

def csD_P (c : PPLLAuthF.Cfg) (cert : Bool) (r : AuthState ψ) : AuthState ψ :=
  if c.strictReady && cert && !isHead r then
    let v := checkSigSetReadyGuarded r.core
    if v.state = .CHECK_ready ∧ r.st ≠ .CHECK_ready ∧ ¬ waveState r.st ∧ r.st ≠ .congest ∧
        r.st ≠ .done then
      { r with core := v, ctrl_mark := r.path_mark } else r
  else r

def csE_P (hψ : ψ > 0) (cert : Bool) (l r : AuthState ψ) : AuthState ψ :=
  if cert then r.withCore (checkSigCheckR hψ l.core r.core) else r

def csF_P (l : AuthState ψ) : AuthState ψ :=
  if isHead l && l.ctrl_mark == l.path_mark then issue l else l

def csG_P (cert : Bool) (r : AuthState ψ) : AuthState ψ :=
  if (isHead r && r.ctrl_mark == r.path_mark) || (cert && r.ctrl_mark == r.path_mark) then
    issue r else r

def csH_P (hψ : ψ > 0) (cert : Bool) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let birthOK : Bool := cert || (ψ == 1 && isHead r && r.ctrl_mark == r.path_mark)
  if r.core.label = ⟨ψ - 1, by omega⟩ ∧ r.st = .equal ∧ birthOK then
    (l, { r with core := { r.core with leader := true } }) else (l, r)

theorem checkSource_eq_P (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    checkSourceAuth hψ c l r =
      (let q := validateCheck l r
       let q := csA_P c q.1 q.2
       let l2 := csC_P hψ (csB_P q.1 q.2)
       let cert := certPred l2 q.2
       csH_P hψ cert (csF_P l2) (csG_P cert (csE_P hψ cert l2 (csD_P c cert q.2)))) := by
  -- `checkSourceAuth` destructures `validateCheck` with `let (l, r) := ...`, this form projects
  -- it; `dsimp only` reduces both to one term (`rfl` timed out at the default budget).
  unfold checkSourceAuth csA_P csB_P csC_P csD_P csE_P csF_P csG_P csH_P
  dsimp only

theorem checkSource_pm_P (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    PM_P (checkSourceAuth hψ c l r) l r := by
  rw [checkSource_eq_P]
  have h1 := validate_pm_P l r
  generalize validateCheck l r = q1 at h1 ⊢
  obtain ⟨l1, r1⟩ := q1
  have h2 : PM_P (csA_P c l1 r1) l1 r1 := by
    unfold csA_P
    constructor
    · dsimp only; split
      · exact readyAuth_mono_P l1
      · exact MonoA_P.refl l1
    · dsimp only; split
      · exact readyAuth_mono_P r1
      · exact MonoA_P.refl r1
  dsimp only
  generalize csA_P c l1 r1 = q2 at h2 ⊢
  obtain ⟨l2, r2⟩ := q2
  dsimp only
  have h3 : MonoA_P l2 (csB_P l2 r2) := by
    unfold csB_P; split
    · exact MonoC_P.of_eq rfl
    · exact MonoA_P.refl l2
  have h4 : MonoA_P (csB_P l2 r2) (csC_P hψ (csB_P l2 r2)) := checkL_mono_P hψ _
  generalize csC_P hψ (csB_P l2 r2) = l4 at h4 ⊢
  generalize certPred l4 r2 = cert
  have h5 : MonoA_P r2 (csD_P c cert r2) := by
    unfold csD_P; split
    · dsimp only; split
      · exact checkReady_mono_P r2.core
      · exact MonoA_P.refl r2
    · exact MonoA_P.refl r2
  have h6 : MonoA_P (csD_P c cert r2) (csE_P hψ cert l4 (csD_P c cert r2)) := by
    unfold csE_P; split
    · exact checkR_mono_P hψ _ _
    · exact MonoA_P.refl _
  have h7 : MonoA_P l4 (csF_P l4) := by
    unfold csF_P; split
    · exact issue_mono_P l4
    · exact MonoA_P.refl l4
  have h8 : ∀ u : AuthState ψ, MonoA_P u (csG_P cert u) := by
    intro u; unfold csG_P; split
    · exact issue_mono_P u
    · exact MonoA_P.refl u
  have h9 : ∀ a b : AuthState ψ, PM_P (csH_P hψ cert a b) a b := by
    intro a b; unfold csH_P; dsimp only; split
    · exact ⟨MonoA_P.refl _, MonoC_P.of_eq rfl⟩
    · exact PM_P.refl a b
  exact PM_P.trans (q := (csF_P l4, csG_P cert (csE_P hψ cert l4 (csD_P c cert r2))))
    ⟨h1.1.trans (h2.1.trans (h3.trans (h4.trans h7))),
     h1.2.trans (h2.2.trans (h5.trans (h6.trans (h8 _))))⟩ (h9 _ _)

theorem disappear_pm_P (hψ : ψ > 0) (l r : AuthState ψ) : PM_P (disappearAuth hψ l r) l r := by
  unfold disappearAuth
  dsimp only
  have h0 : MonoA_P r (if r.st = MainState.toss ∧ r.core.label = ⟨0, hψ⟩ then
      { r with core := { r.core with state := MainState.toss_done, path2 := some ⟨0, 0, 0, 5⟩,
                                      p := false },
               path2_scope := P2Scope.line, path2_mark := r.ctrl_mark }
      else r) := by
    split
    · exact MonoC_P.of_eq rfl
    · exact MonoA_P.refl r
  generalize (if r.st = MainState.toss ∧ r.core.label = ⟨0, hψ⟩ then
      { r with core := { r.core with state := MainState.toss_done, path2 := some ⟨0, 0, 0, 5⟩,
                                      p := false },
               path2_scope := P2Scope.line, path2_mark := r.ctrl_mark }
      else r) = r0 at h0 ⊢
  have h1 := lift2_pm_P (disappearStartL hψ) (disStart_mono_P hψ) l r0
  generalize lift2 (disappearStartL hψ) l r0 = q1 at h1 ⊢
  obtain ⟨l1, r1⟩ := q1
  have h2 := lift2_pm_P (disappearCarry hψ) (disCarry_mono_P hψ) l1 r1
  exact ⟨h1.1.trans h2.1, h0.trans (h1.2.trans h2.2)⟩

theorem repair_pm_P (l r : AuthState ψ) : PM_P (repairAuth l r) l r := by
  unfold repairAuth
  dsimp only
  have hc : ∀ a : AgentState ψ, MonoC_P a (normalizeCarrier (normalizeOrphan a)) :=
    fun a => (orphan_mono_P a).trans (carrier_mono_P _)
  have h1 := liftLife_mono_P _ hc l
  have h2 := liftLife_mono_P _ hc r
  generalize liftLife (fun u => normalizeCarrier (normalizeOrphan u)) l = l1 at h1 ⊢
  generalize liftLife (fun u => normalizeCarrier (normalizeOrphan u)) r = r1 at h2 ⊢
  have h3 := lift2Life_pm_P releaseReadySuffix releaseSuffix_mono_P l1 r1
  generalize lift2Life releaseReadySuffix l1 r1 = q3 at h3 ⊢
  obtain ⟨l3, r3⟩ := q3
  have h4 : PM_P (ackTailAuth l3 r3) l3 r3 := by
    unfold ackTailAuth
    split
    · exact lift2_pm_P ackTail ackTail_mono_P l3 r3
    · exact PM_P.refl l3 r3
  exact ⟨h1.trans (h3.1.trans h4.1), h2.trans (h3.2.trans h4.2)⟩

theorem maintain_pm_P (l r : AuthState ψ) : PM_P (maintainAuth l r) l r := by
  unfold maintainAuth PM_P; msplit_P

theorem completeWave_pm_P (l r : AuthState ψ) : PM_P (completeWaveAuth l r) l r := by
  unfold completeWaveAuth PM_P; msplit_P

theorem wave_pm_P (l r : AuthState ψ) : PM_P (waveAuth l r) l r := by
  unfold waveAuth PM_P; msplit_P

theorem landBackwardAuth_mono_P (u : AuthState ψ) : MonoA_P u (landBackwardAuth u) := by
  unfold landBackwardAuth
  (repeat' (first | (dsimp only) | split))
  all_goals first
    | exact MonoA_P.refl _
    | exact dropP2_mono_P _
    | exact landBackward_mono_P u.core

theorem landForwardAuth_mono_P (κ : Nat) (u : AuthState ψ) : MonoA_P u (landForwardAuth κ u) := by
  unfold landForwardAuth
  (repeat' (first | (dsimp only) | split))
  all_goals first
    | exact MonoA_P.refl _
    | exact dropP2_mono_P _
    | exact landForward_mono_P κ false true u.core

def cmp0_P (l : AuthState ψ) : AuthState ψ :=
  match l.core.path with
  | .bot => if l.st = .produce then l else l.setState .none
  | .some _ _ => l

def cmpTail_P (κ : Nat) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let (l, r) := maintainAuth l r
  let (l, r) := completeWaveAuth l r
  let (l, r) := waveAuth l r
  let (l, r) := lift2 PPLLFableDesignR1.dropStray l r
  (landBackwardAuth l, landForwardAuth κ r)

theorem compare_eq_P (κ : Nat) (l r : AuthState ψ) :
    compareLifecycleAuth κ l r = cmpTail_P κ (cmp0_P l) r := by
  unfold compareLifecycleAuth cmpTail_P cmp0_P; rfl

theorem cmpTail_pm_P (κ : Nat) (l r : AuthState ψ) : PM_P (cmpTail_P κ l r) l r := by
  unfold cmpTail_P
  have h1 := maintain_pm_P l r
  generalize maintainAuth l r = q1 at h1 ⊢
  obtain ⟨l1, r1⟩ := q1
  dsimp only
  have h2 := completeWave_pm_P l1 r1
  generalize completeWaveAuth l1 r1 = q2 at h2 ⊢
  obtain ⟨l2, r2⟩ := q2
  dsimp only
  have h3 := wave_pm_P l2 r2
  generalize waveAuth l2 r2 = q3 at h3 ⊢
  obtain ⟨l3, r3⟩ := q3
  dsimp only
  have h4 := lift2_pm_P PPLLFableDesignR1.dropStray dropStray_mono_P l3 r3
  generalize lift2 PPLLFableDesignR1.dropStray l3 r3 = q4 at h4 ⊢
  obtain ⟨l4, r4⟩ := q4
  exact ⟨h1.1.trans (h2.1.trans (h3.1.trans (h4.1.trans (landBackwardAuth_mono_P _)))),
    h1.2.trans (h2.2.trans (h3.2.trans (h4.2.trans (landForwardAuth_mono_P κ _))))⟩

theorem cmp0_mono_P (l : AuthState ψ) : MonoA_P l (cmp0_P l) := by
  unfold cmp0_P
  split
  · split
    · exact MonoA_P.refl l
    · exact MonoC_P.of_eq rfl
  · exact MonoA_P.refl l

theorem compare_pm_P (κ : Nat) (l r : AuthState ψ) : PM_P (compareLifecycleAuth κ l r) l r := by
  rw [compare_eq_P]
  have h := cmpTail_pm_P κ (cmp0_P l) r
  exact ⟨(cmp0_mono_P l).trans h.1, h.2⟩

end MonoStages

/-- **The initiator's path.** The AuthF stages after GENSIG never give a
pathless initiator a path (only Step 1 writes a path, into the responder). -/
theorem restPair_left_bot {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ)
    (h : q.1.core.path = .bot) : (restPair hψ κ c q).1.core.path = .bot := by
  obtain ⟨a, b⟩ := q
  simp only [restPair, restLo, restHi, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11] at h ⊢
  have h1 := (cleanSource_pm_P hψ c a b).1 h
  generalize cleanSourceAuth hψ c a b = q1 at h1 ⊢
  obtain ⟨a1, b1⟩ := q1
  have h2 := (lift2Life_pm_P (releaseSource hψ) (releaseSource_mono_P hψ) a1 b1).1 h1
  generalize lift2Life (releaseSource hψ) a1 b1 = q2 at h2 ⊢
  obtain ⟨a2, b2⟩ := q2
  have h3 := (lift2_pm_P (eliminateSig hψ) (eliminate_mono_P hψ) a2 b2).1 h2
  generalize lift2 (eliminateSig hψ) a2 b2 = q3 at h3 ⊢
  obtain ⟨a3, b3⟩ := q3
  have h4 := moveSource_pm_P hψ c a3 b3 h3
  generalize moveSourceAuth hψ c a3 b3 = q4 at h4 ⊢
  obtain ⟨a4, b4⟩ := q4
  have h5 := liftLife_mono_P dropStale dropStale_mono_P a4 h4
  have h6 := (preCheck_pm_P (liftLife dropStale a4) (liftLife dropStale b4)).1 h5
  generalize preCheckResetAuth (liftLife dropStale a4) (liftLife dropStale b4) = q6 at h6 ⊢
  obtain ⟨a6, b6⟩ := q6
  have h7 := liftLife_mono_P normalizeReady normalizeReady_mono_P a6 h6
  have h8 := (checkSource_pm_P hψ c (liftLife normalizeReady a6) (liftLife normalizeReady b6)).1 h7
  generalize checkSourceAuth hψ c (liftLife normalizeReady a6) (liftLife normalizeReady b6) = q8 at h8 ⊢
  obtain ⟨a8, b8⟩ := q8
  have h9 := (disappear_pm_P hψ a8 b8).1 h8
  generalize disappearAuth hψ a8 b8 = q9 at h9 ⊢
  obtain ⟨a9, b9⟩ := q9
  have h10 := (repair_pm_P a9 b9).1 h9
  generalize repairAuth a9 b9 = q10 at h10 ⊢
  obtain ⟨a10, b10⟩ := q10
  exact (compare_pm_P κ a10 b10).1 h10


/-! ## Part B. GENSIG on a generation-free pair

On two non-generation cells whose head-start guard fails after WAIT, GENSIG is
exactly WAIT; when the guard holds on the head of a block with `ψ ≥ 3`, the head
and its (non-terminal) successor become pathless producers. -/

section GenSig
variable {ψ : Nat}

/-- GENSIG is its body applied to the WAIT output. -/
theorem gs_body (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) :
    genSigAuth hψ κ l r =
      gsBody hψ (lift2 (waitSaturated hψ κ) l r).1 (lift2 (waitSaturated hψ κ) l r).2 := by
  unfold genSigAuth
  generalize lift2 (waitSaturated hψ κ) l r = w
  obtain ⟨a, b⟩ := w
  rfl

/-- The body of GENSIG is the identity on a non-generation pair whose head-start
guard fails. -/
theorem gsBody_idle (hψ : ψ > 0) (l1 r1 : AuthState ψ) (hl : NG l1) (hr : NG r1)
    (hg : ¬ (l1.core.leader = false ∧ l1.core.label.val = 0 ∧ l1.core.wait = false ∧
      l1.core.path = .bot)) :
    gsBody hψ l1 r1 = (l1, r1) := by
  have h1 : gsH hψ l1 r1 = l1 := by
    rcases (gsH_spec hψ l1 r1).2 with ⟨_, e⟩ | ⟨a, b, c, d, _⟩
    · exact e
    · exact absurd ⟨a, b, c, d⟩ hg
  have h2 : gsR hψ l1 r1 = r1 := by
    rcases (gsR_spec hψ l1 r1).2 with ⟨_, e⟩ | ⟨_, a, _⟩
    · exact e
    · exact absurd a hl.1
  have h3 : gsE hψ r1 = r1 := by
    rcases (gsE_spec hψ r1).2 with ⟨_, e⟩ | ⟨_, a, _⟩
    · exact e
    · exact absurd a hr.1
  have h4 : gsPair hψ l1 r1 = (l1, r1) := by
    rcases (gsPair_spec hψ l1 r1).2.2.2 with ⟨_, e⟩ | ⟨_, a, _⟩
    · exact e
    · exact absurd a hl.1
  have h5 : gsF hψ l1 = l1 := by
    rcases (gsF_spec hψ l1).2 with ⟨_, e⟩ | ⟨_, a, _⟩
    · exact e
    · exact absurd a hl.2
  unfold gsBody
  rw [h1, h2, h3, h4]
  show (gsF hψ l1, r1) = (l1, r1)
  rw [h5]

/-- WAIT keeps the state (so a non-generation cell stays non-generation). -/
theorem wait_NG1 (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) (hl : NG l) :
    NG (lift2 (waitSaturated hψ κ) l r).1 := by
  have := (waitSat_fields hψ κ l.core r.core).1
  show (waitSaturated hψ κ l.core r.core).1.state ≠ _ ∧
    (waitSaturated hψ κ l.core r.core).1.state ≠ _
  rw [this]; exact hl

theorem wait_NG2 (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) (hr : NG r) :
    NG (lift2 (waitSaturated hψ κ) l r).2 := by
  obtain ⟨-, -, -, -, -, h, -⟩ := waitSat_fields hψ κ l.core r.core
  show (waitSaturated hψ κ l.core r.core).2.state ≠ _ ∧
    (waitSaturated hψ κ l.core r.core).2.state ≠ _
  rw [h]; exact hr

end GenSig


/-! ## Part C0. A six-field model of WAIT

`MS` keeps the fields WAIT reads or writes (`label`, `wait`, `count`, `carry`,
`h_field`, `reset`); `wsM` is `waitSaturated` transcribed on `MS`, and
`ws_pi` shows the transcription is exact. `wsM_spec` gives the output fields of
a block row in closed form. -/

section Model
variable {ψ : Nat}

/-- The WAIT registers of a cell. -/
structure MS (ψ : Nat) where
  label : Fin ψ
  w : Bool
  c : Nat
  y : Bool
  h : Bool
  z : Bool

/-- Project a cell onto its WAIT registers. -/
def pi (u : AgentState ψ) : MS ψ := ⟨u.label, u.wait, u.count, u.carry, u.h_field, u.reset⟩

/-- The WAIT view of a model cell. -/
def kvM (m : MS ψ) : Bool × Nat × Bool × Bool × Bool := (m.w, m.c, m.y, m.h, m.z)

theorem kv_pi (u : AgentState ψ) : kv u = kvM (pi u) := rfl

/-- `waitSaturatedPrepare` on `MS`. -/
def prepM (hψ : ψ > 0) (l r : MS ψ) : MS ψ × MS ψ :=
  let r := if r.label = ⟨0, hψ⟩ then { r with z := true, h := false } else r
  let l := if l.label = ⟨0, hψ⟩ then
    if l.h = true then { l with h := false, y := true } else { l with h := true }
  else l
  (l, r)

/-- `waitSaturatedCarry` on `MS`. -/
def carryM (hψ : ψ > 0) (κ : Nat) (l r : MS ψ) : MS ψ × MS ψ :=
  if l.y = true then
    if r.h = true then
      if r.label = ⟨ψ - 1, by omega⟩ then
        ({ l with y := false }, { r with h := false, c := satCountSucc κ r.c })
      else
        ({ l with y := false }, { r with h := false, y := true })
    else
      ({ l with y := false }, { r with h := true })
  else (l, r)

/-- `waitSaturatedReset` on `MS`. -/
def resetM (hψ : ψ > 0) (l r : MS ψ) : MS ψ × MS ψ :=
  if l.z = true then
    let r := if r.label ≠ ⟨ψ - 1, by omega⟩ then { r with z := true } else r
    ({ l with z := false }, { r with h := false })
  else (l, r)

/-- `waitSaturatedFinish` on `MS`. -/
def finishM (hψ : ψ > 0) (κ : Nat) (l r : MS ψ) : MS ψ × MS ψ :=
  let r := if r.label = ⟨ψ - 1, by omega⟩ ∧ r.c = κ then { r with w := false } else r
  if r.w = false ∧ l.label ≠ ⟨ψ - 1, by omega⟩ then
    ({ l with w := false }, { r with w := true })
  else (l, r)

/-- `waitSaturated` on `MS`. -/
def wsM (hψ : ψ > 0) (κ : Nat) (l r : MS ψ) : MS ψ × MS ψ :=
  let q := prepM hψ l r
  let q := carryM hψ κ q.1 q.2
  let q := resetM hψ q.1 q.2
  finishM hψ κ q.1 q.2

theorem prep_pi (hψ : ψ > 0) (l r : AgentState ψ) :
    pi (waitSaturatedPrepare hψ l r).1 = (prepM hψ (pi l) (pi r)).1 ∧
    pi (waitSaturatedPrepare hψ l r).2 = (prepM hψ (pi l) (pi r)).2 := by
  unfold waitSaturatedPrepare prepM pi
  by_cases h1 : r.label = ⟨0, hψ⟩ <;> by_cases h2 : l.label = ⟨0, hψ⟩ <;>
    by_cases h3 : l.h_field = true <;> simp [h1, h2, h3]

theorem carry_pi (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    pi (waitSaturatedCarry hψ κ l r).1 = (carryM hψ κ (pi l) (pi r)).1 ∧
    pi (waitSaturatedCarry hψ κ l r).2 = (carryM hψ κ (pi l) (pi r)).2 := by
  unfold waitSaturatedCarry carryM pi
  by_cases h1 : l.carry = true <;> by_cases h2 : r.h_field = true <;>
    by_cases h3 : r.label = ⟨ψ - 1, by omega⟩ <;> simp [h1, h2, h3]

theorem reset_pi (hψ : ψ > 0) (l r : AgentState ψ) :
    pi (waitSaturatedReset hψ l r).1 = (resetM hψ (pi l) (pi r)).1 ∧
    pi (waitSaturatedReset hψ l r).2 = (resetM hψ (pi l) (pi r)).2 := by
  unfold waitSaturatedReset resetM pi
  by_cases h1 : l.reset = true <;> by_cases h3 : r.label = ⟨ψ - 1, by omega⟩ <;> simp [h1, h3]

theorem finish_pi (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    pi (waitSaturatedFinish hψ κ l r).1 = (finishM hψ κ (pi l) (pi r)).1 ∧
    pi (waitSaturatedFinish hψ κ l r).2 = (finishM hψ κ (pi l) (pi r)).2 := by
  unfold waitSaturatedFinish finishM pi
  by_cases h1 : r.label = ⟨ψ - 1, by omega⟩ <;> by_cases h2 : r.count = κ <;>
    by_cases h3 : r.wait = true <;> by_cases h4 : l.label = ⟨ψ - 1, by omega⟩ <;>
    simp [h1, h2, h3, h4]

/-- The transcription is exact. -/
theorem ws_pi (hψ : ψ > 0) (κ : Nat) (a b : AgentState ψ) :
    pi (waitSaturated hψ κ a b).1 = (wsM hψ κ (pi a) (pi b)).1 ∧
    pi (waitSaturated hψ κ a b).2 = (wsM hψ κ (pi a) (pi b)).2 := by
  have e1 := prep_pi hψ a b
  have e2 := carry_pi hψ κ (waitSaturatedPrepare hψ a b).1 (waitSaturatedPrepare hψ a b).2
  have e3 := reset_pi hψ (waitSaturatedCarry hψ κ (waitSaturatedPrepare hψ a b).1
    (waitSaturatedPrepare hψ a b).2).1 (waitSaturatedCarry hψ κ (waitSaturatedPrepare hψ a b).1
    (waitSaturatedPrepare hψ a b).2).2
  have e4 := finish_pi hψ κ (waitSaturatedReset hψ (waitSaturatedCarry hψ κ
    (waitSaturatedPrepare hψ a b).1 (waitSaturatedPrepare hψ a b).2).1
    (waitSaturatedCarry hψ κ (waitSaturatedPrepare hψ a b).1
    (waitSaturatedPrepare hψ a b).2).2).1 (waitSaturatedReset hψ (waitSaturatedCarry hψ κ
    (waitSaturatedPrepare hψ a b).1 (waitSaturatedPrepare hψ a b).2).1
    (waitSaturatedCarry hψ κ (waitSaturatedPrepare hψ a b).1
    (waitSaturatedPrepare hψ a b).2).2).2
  unfold waitSaturated wsM
  dsimp only
  rw [e4.1, e4.2, e3.1, e3.2, e2.1, e2.2, e1.1, e1.2]
  exact ⟨rfl, rfl⟩

/- Closed forms of the four WAIT stages, one stage at a time (2-8 cases each).
`wsM_spec` composes them by rewriting; the former proof split all 128 cases of
the composed pipeline with a simp per case under a raised budget. -/
private theorem prepM_spec (hψ : ψ > 0) (a b : MS ψ) (hb : b.label.val ≠ 0) :
    (prepM hψ a b).1.label = a.label ∧ (prepM hψ a b).1.w = a.w ∧
    (prepM hψ a b).1.c = a.c ∧
    (prepM hψ a b).1.h = (if decide (a.label.val = 0) = true then !a.h else a.h) ∧
    (prepM hψ a b).1.y = ((decide (a.label.val = 0) && a.h) || a.y) ∧
    (prepM hψ a b).1.z = a.z ∧ (prepM hψ a b).2 = b := by
  obtain ⟨la, aw, ac, ay, ah, az⟩ := a
  have hb' : ¬ b.label = ⟨0, hψ⟩ := fun h => hb (by rw [h])
  by_cases h0 : la.val = 0 <;> cases ah <;> simp [prepM, Fin.ext_iff, h0, hb, hb']

private theorem carryM_spec (hψ : ψ > 0) (κ : Nat) (l r : MS ψ) :
    (carryM hψ κ l r).1.label = l.label ∧ (carryM hψ κ l r).1.w = l.w ∧
    (carryM hψ κ l r).1.c = l.c ∧ (carryM hψ κ l r).1.h = l.h ∧
    (carryM hψ κ l r).1.y = false ∧ (carryM hψ κ l r).1.z = l.z ∧
    (carryM hψ κ l r).2.label = r.label ∧ (carryM hψ κ l r).2.w = r.w ∧
    (carryM hψ κ l r).2.c = (if (l.y && r.h && decide (r.label.val = ψ - 1)) = true then
      satCountSucc κ r.c else r.c) ∧
    (carryM hψ κ l r).2.h = (if l.y = true then !r.h else r.h) ∧
    (carryM hψ κ l r).2.y = ((l.y && r.h && !decide (r.label.val = ψ - 1)) || r.y) ∧
    (carryM hψ κ l r).2.z = r.z := by
  obtain ⟨la, lw, lc, ly, lh, lz⟩ := l
  obtain ⟨lb, rw', rc, ry, rh, rz⟩ := r
  by_cases hT : lb.val = ψ - 1 <;> cases ly <;> cases rh <;>
    simp [carryM, Fin.ext_iff, hT]

private theorem resetM_spec (hψ : ψ > 0) (l r : MS ψ) :
    (resetM hψ l r).1.label = l.label ∧ (resetM hψ l r).1.w = l.w ∧
    (resetM hψ l r).1.c = l.c ∧ (resetM hψ l r).1.h = l.h ∧
    (resetM hψ l r).1.y = l.y ∧ (resetM hψ l r).1.z = false ∧
    (resetM hψ l r).2.label = r.label ∧ (resetM hψ l r).2.w = r.w ∧
    (resetM hψ l r).2.c = r.c ∧ (resetM hψ l r).2.h = (!l.z && r.h) ∧
    (resetM hψ l r).2.y = r.y ∧
    (resetM hψ l r).2.z = ((l.z && !decide (r.label.val = ψ - 1)) || r.z) := by
  obtain ⟨la, lw, lc, ly, lh, lz⟩ := l
  obtain ⟨lb, rw', rc, ry, rh, rz⟩ := r
  by_cases hT : lb.val = ψ - 1 <;> cases lz <;> simp [resetM, Fin.ext_iff, hT]

private theorem finishM_spec (hψ : ψ > 0) (κ : Nat) (l r : MS ψ)
    (hl : l.label.val ≠ ψ - 1) :
    (finishM hψ κ l r).1.label = l.label ∧ (finishM hψ κ l r).1.h = l.h ∧
    (finishM hψ κ l r).1.y = l.y ∧ (finishM hψ κ l r).1.z = l.z ∧
    (finishM hψ κ l r).1.c = l.c ∧
    (finishM hψ κ l r).1.w =
      ((!(decide (r.label.val = ψ - 1) && decide (r.c = κ)) && r.w) && l.w) ∧
    (finishM hψ κ l r).2.label = r.label ∧ (finishM hψ κ l r).2.h = r.h ∧
    (finishM hψ κ l r).2.y = r.y ∧ (finishM hψ κ l r).2.z = r.z ∧
    (finishM hψ κ l r).2.c = r.c ∧
    (finishM hψ κ l r).2.w =
      (!(!(decide (r.label.val = ψ - 1) && decide (r.c = κ)) && r.w) || r.w) := by
  obtain ⟨la, lw, lc, ly, lh, lz⟩ := l
  obtain ⟨lb, rw', rc, ry, rh, rz⟩ := r
  have hl' : ¬ la = ⟨ψ - 1, by omega⟩ := fun h => hl (by rw [h])
  by_cases hT : lb.val = ψ - 1 <;> by_cases hc : rc = κ <;> cases rw' <;>
    simp [finishM, Fin.ext_iff, hT, hc, hl, hl']

/-- **WAIT in closed form** on a pair whose initiator is not terminal and whose
responder is not a head. `P0`: the initiator is the head; `T`: the responder is
the terminal. -/
theorem wsM_spec (hψ : ψ > 0) (κ : Nat) (a b : MS ψ) (ha : a.label.val ≠ ψ - 1)
    (hb : b.label.val ≠ 0) :
    let o := wsM hψ κ a b
    let P0 := decide (a.label.val = 0)
    let T := decide (b.label.val = ψ - 1)
    let y1 := (P0 && a.h) || a.y
    let c2 := if (y1 && b.h && T) = true then satCountSucc κ b.c else b.c
    let bw := !(T && decide (c2 = κ)) && b.w
    o.1.label = a.label ∧ o.2.label = b.label ∧
    o.1.h = (if P0 = true then !a.h else a.h) ∧ o.1.y = false ∧ o.1.z = false ∧
    o.1.c = a.c ∧ o.1.w = (bw && a.w) ∧
    o.2.h = (!a.z && (if y1 = true then !b.h else b.h)) ∧
    o.2.y = ((y1 && b.h && !T) || b.y) ∧ o.2.z = ((a.z && !T) || b.z) ∧
    o.2.c = c2 ∧ o.2.w = (!bw || b.w) := by
  have hp := prepM_spec hψ a b hb
  dsimp only
  unfold wsM
  dsimp only
  generalize prepM hψ a b = q1 at hp ⊢
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hp
  subst p7
  have hc := carryM_spec hψ κ q1.1 q1.2
  generalize carryM hψ κ q1.1 q1.2 = q2 at hc ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := hc
  have hr := resetM_spec hψ q2.1 q2.2
  generalize resetM hψ q2.1 q2.2 = q3 at hr ⊢
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := hr
  have hl : q3.1.label.val ≠ ψ - 1 := by rw [r1, c1, p1]; exact ha
  have hf := finishM_spec hψ κ q3.1 q3.2 hl
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := hf
  rw [f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12,
    r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12,
    c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
    p1, p2, p3, p4, p5, p6]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Model


/-! ## Part C. WAIT on one block row

`wS_spec` computes the WAIT output fields of a block row in closed form;
`row_wait` lifts it through the whole AuthF row: either the row is the head
start (the head leaves as a pathless producer) or the row acts on the WAIT
view exactly as `waitSaturated` and keeps both cells outside the generation. -/

section WaitRow
variable {ψ : Nat}

open PPLLAuthResetDrain (beforeSuppressAuth)

/-- On a leaderless, reset-free pair the whole AuthF row keeps the WAIT view of
its prefix `beforeSuppressAuth`. -/
theorem pipeline_akv (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hl' : l.core.reset_cmd = false) (hr' : r.core.reset_cmd = false) :
    akv (PPLLAuthF.pipeline hψ κ c l r).1 = akv (beforeSuppressAuth hψ κ c l r).1 ∧
    akv (PPLLAuthF.pipeline hψ κ c l r).2 = akv (beforeSuppressAuth hψ κ c l r).2 := by
  have hpf := PPLLAuthResetDrain.prefix_facts hψ κ c l r
  dsimp only at hpf
  obtain ⟨b1, -, b3, -, b5, -, -⟩ := hpf
  have hc := PPLLAuthWriterFrame.pipeline_writer_compose hψ κ c l r hl hr
  dsimp only at hc
  have hs := suppress_kv hψ (beforeSuppressAuth hψ κ c l r).1.core
    (beforeSuppressAuth hψ κ c l r).2.core (b5.trans hl) (b1.trans hl') (b3.trans hr')
  have hsc := PPLLAuthResetDrain.suppress_core hψ (beforeSuppressAuth hψ κ c l r).1
    (beforeSuppressAuth hψ κ c l r).2
  rw [← PPLLAuthResetDrain.beforeElimination_eq] at hsc
  have hk := kernel_kv hψ (PPLLAuthF.beforeElimination hψ κ c l r).1.core
    (PPLLAuthF.beforeElimination hψ κ c l r).2.core
  have hw := write_kv hψ
    (k4Kernel hψ (PPLLAuthF.beforeElimination hψ κ c l r).1.core
      (PPLLAuthF.beforeElimination hψ κ c l r).2.core).1
    (k4Kernel hψ (PPLLAuthF.beforeElimination hψ κ c l r).1.core
      (PPLLAuthF.beforeElimination hψ κ c l r).2.core).2
  refine ⟨?_, ?_⟩
  · show kv _ = kv _
    rw [hc.1, hw.1, hk.1, hsc.1, hs.1]
  · show kv _ = kv _
    rw [hc.2.1, hw.2, hk.2, hsc.2, hs.2]

/-- **Head start at GENSIG** (`ψ ≥ 3`): a pathless, leaderless head outside the
generation whose WAIT output has `wait = false` becomes a pathless producer and
recruits its successor. -/
theorem gs_start (hψ : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (l r : AuthState ψ)
    (hl0 : l.core.label.val = 0) (hr1 : r.core.label.val = 1) (hL : l.core.leader = false)
    (hb : l.core.path = .bot) (hl : NG l) (hr : NG r)
    (hw : (waitSaturated hψ κ l.core r.core).1.wait = false) :
    (genSigAuth hψ κ l r).1.core.state = .produce ∧ (genSigAuth hψ κ l r).1.core.path = .bot ∧
    (genSigAuth hψ κ l r).2.core.state = .produce ∧ (genSigAuth hψ κ l r).2.core.path = .bot := by
  obtain ⟨s1, p1, -, lb1, ld1, s2, -, -, lb2, -⟩ := waitSat_fields hψ κ l.core r.core
  rw [gs_body]
  have a1 : (lift2 (waitSaturated hψ κ) l r).1.core.state = l.core.state := s1
  have a2 : (lift2 (waitSaturated hψ κ) l r).1.core.path = .bot := p1.trans hb
  have a3 : (lift2 (waitSaturated hψ κ) l r).1.core.label.val = 0 := by
    show (waitSaturated hψ κ l.core r.core).1.label.val = 0
    rw [lb1]; exact hl0
  have a4 : (lift2 (waitSaturated hψ κ) l r).1.core.leader = false := ld1.trans hL
  have a5 : (lift2 (waitSaturated hψ κ) l r).1.core.wait = false := hw
  have b1 : (lift2 (waitSaturated hψ κ) l r).2.core.state = r.core.state := s2
  have b3 : (lift2 (waitSaturated hψ κ) l r).2.core.label.val = 1 := by
    show (waitSaturated hψ κ l.core r.core).2.label.val = 1
    rw [lb2]; exact hr1
  unfold NG at hl hr
  generalize lift2 (waitSaturated hψ κ) l r = W at a1 a2 a3 a4 a5 b1 b3
  obtain ⟨l1, r1⟩ := W
  dsimp only at a1 a2 a3 a4 a5 b1 b3 ⊢
  apply gsBody_open hψ l1 r1 (fun G => G.1.core.state = .produce ∧ G.1.core.path = .bot ∧
    G.2.core.state = .produce ∧ G.2.core.path = .bot)
  intro H R E Q hH hR hE hQ
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
  clear hH hR hE hQ
  rcases sH with ⟨hn1, -⟩ | ⟨-, -, -, -, h1, h2, -, -, -, -⟩
  · exact absurd ⟨a4, a3, a5, a2⟩ hn1
  rcases sR with ⟨hn2, -⟩ | ⟨-, -, -, g1, g2, -, -⟩
  · exact absurd ⟨by rw [b3]; omega, h1,
      Or.inr (Or.inl ⟨by rw [b1]; exact hr.1, by rw [b1]; exact hr.2⟩)⟩ hn2
  have hRlab : R.core.label.val = 1 := by rw [LR.1]; exact b3
  rcases sE with ⟨-, he3⟩ | ⟨k1, -⟩
  · rcases sQ with ⟨-, he4⟩ | ⟨-, -, m3, -⟩
    · rcases sF with ⟨-, he5⟩ | ⟨-, n2, -⟩
      · dsimp only
        rw [he5, he4]
        dsimp only
        rw [he3]
        exact ⟨h1, h2, g1, g2⟩
      · rw [he4] at n2; dsimp only at n2; rw [h1] at n2; cases n2
    · rw [he3, g1] at m3; cases m3
  · omega

/-- **One WAIT row.** On a block row `k → k+1` (`ψ ≥ 3`) between two
non-generation cells whose head (if `k = 0`) is pathless, either the row is the
head start (`k = 0` and the WAIT output of the head has `wait = false`), and the
head leaves as a pathless producer, or the row acts on the WAIT view as
`waitSaturated`, both cells stay outside the generation and the head stays
pathless. -/
theorem row_wait (hψ : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (k : Nat) (h : RowH ψ l r k) (hl : NG l) (hr : NG r) (hb : k = 0 → l.core.path = .bot) :
    (k = 0 ∧ (wsM hψ κ (pi l.core) (pi r.core)).1.w = false ∧
      (PPLLAuthF.pipeline hψ κ c l r).1.core.state = .produce ∧
      (PPLLAuthF.pipeline hψ κ c l r).1.core.path = .bot) ∨
    (¬ (k = 0 ∧ (wsM hψ κ (pi l.core) (pi r.core)).1.w = false) ∧
      akv (PPLLAuthF.pipeline hψ κ c l r).1 = kvM (wsM hψ κ (pi l.core) (pi r.core)).1 ∧
      akv (PPLLAuthF.pipeline hψ κ c l r).2 = kvM (wsM hψ κ (pi l.core) (pi r.core)).2 ∧
      NG (PPLLAuthF.pipeline hψ κ c l r).1 ∧ NG (PPLLAuthF.pipeline hψ κ c l r).2 ∧
      (k = 0 → (PPLLAuthF.pipeline hψ κ c l r).1.core.path = .bot)) := by
  obtain ⟨x, y, hP⟩ := P0_frame hψ l r h.ll h.rl h.lab
  have hf := pipeline_FV hψ κ c l r h.ll h.rl h.lr h.rr
  have ha := pipeline_akv hψ κ c l r h.ll h.rl h.lr h.rr
  rw [beforeSuppress_eq] at hf ha
  generalize hq : P0 hψ l r = q at hf ha hP
  obtain ⟨l', r'⟩ := q
  dsimp only at hf ha
  have c1 : l'.core = { l.core with probe := x } := by rw [(Prod.mk.inj hP).1]
  have c2 : r'.core = { r.core with probe := y } := by rw [(Prod.mk.inj hP).2]
  have hpl : pi l'.core = pi l.core := by rw [c1]; rfl
  have hpr : pi r'.core = pi r.core := by rw [c2]; rfl
  have hwp := ws_pi hψ κ l'.core r'.core
  rw [hpl, hpr] at hwp
  have lk' : l'.core.label.val = k := by rw [c1]; exact h.lk
  have rk' : r'.core.label.val = k + 1 := by rw [c2]; exact h.rk
  have ll' : l'.core.leader = false := by rw [c1]; exact h.ll
  have rl' : r'.core.leader = false := by rw [c2]; exact h.rl
  have lr' : l'.core.reset_cmd = false := by rw [c1]; exact h.lr
  have rr' : r'.core.reset_cmd = false := by rw [c2]; exact h.rr
  have nl' : NG l' := by unfold NG; rw [c1]; exact hl
  have nr' : NG r' := by unfold NG; rw [c2]; exact hr
  have pb' : k = 0 → l'.core.path = .bot := fun h0 => by rw [c1]; exact hb h0
  have hwait : (waitSaturated hψ κ l'.core r'.core).1.wait =
      (wsM hψ κ (pi l.core) (pi r.core)).1.w := congrArg MS.w hwp.1
  have gp := genSig_pa hψ κ l' r'
  have g1 : (genSigAuth hψ κ l' r').1.core.leader = false := by rw [av_leader, gp.1]; exact ll'
  have g2 : (genSigAuth hψ κ l' r').2.core.leader = false := by rw [av_leader, gp.2]; exact rl'
  have g3 : (genSigAuth hψ κ l' r').1.core.reset_cmd = false := by rw [av_reset, gp.1]; exact lr'
  have g4 : (genSigAuth hψ κ l' r').2.core.reset_cmd = false := by rw [av_reset, gp.2]; exact rr'
  have g6 : (genSigAuth hψ κ l' r').2.core.label.val = k + 1 := by
    rw [av_label, gp.2]; exact rk'
  have hkψ := h.kψ
  by_cases hs : k = 0 ∧ (wsM hψ κ (pi l.core) (pi r.core)).1.w = false
  · left
    have hst := gs_start hψ h3 κ l' r' (by rw [lk']; exact hs.1) (by rw [rk', hs.1])
      ll' (pb' hs.1) nl' nr' (hwait.trans hs.2)
    obtain ⟨s1, s2, s3, s4⟩ := hst
    have hq := rest_Ph hψ κ c _ s1 s3 s2 s4 g1 g2 g3 g4 (by rw [g6]; omega)
    refine ⟨hs.1, hs.2, ?_, ?_⟩
    · rw [FV_state hf.1]; exact hq.1
    · rw [FV_path hf.1]; exact hq.2.1
  · right
    have hn1 := wait_NG1 hψ κ l' r' nl'
    have hn2 := wait_NG2 hψ κ l' r' nr'
    obtain ⟨-, p1, -, lb1, -, -⟩ := waitSat_fields hψ κ l'.core r'.core
    have hgs : genSigAuth hψ κ l' r' = lift2 (waitSaturated hψ κ) l' r' := by
      rw [gs_body]
      apply gsBody_idle hψ _ _ hn1 hn2
      intro ⟨_, q2, q3, _⟩
      apply hs
      have k0 : k = 0 := by
        rw [← lk']
        have : (waitSaturated hψ κ l'.core r'.core).1.label.val = 0 := q2
        rw [lb1] at this; exact this
      exact ⟨k0, hwait.symm.trans q3⟩
    rw [hgs] at hf ha
    have hra := restPair_akv hψ κ c (lift2 (waitSaturated hψ κ) l' r')
    have hpm := restPair_pm hψ κ c (lift2 (waitSaturated hψ κ) l' r')
    refine ⟨hs, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha.1, hra.1]; show kv _ = _; rw [kv_pi]; exact congrArg kvM hwp.1
    · rw [ha.2, hra.2]; show kv _ = _; rw [kv_pi]; exact congrArg kvM hwp.2
    · exact NG_of_FV hf.1 (MonoA.ng hpm.1 hn1)
    · exact NG_of_FV hf.2 (MonoA.ng hpm.2 hn2)
    · intro hk0
      rw [FV_path hf.1]
      apply restPair_left_bot
      show (waitSaturated hψ κ l'.core r'.core).1.path = .bot
      rw [p1]; exact pb' hk0

end WaitRow


/-! ## Part D. Row facts of the model and a small sum library -/

section ModelFacts
variable {ψ : Nat}

theorem pi_of {u : AgentState ψ} {o : MS ψ} (h1 : kv u = kvM o) (h2 : u.label = o.label) :
    pi u = o := by
  obtain ⟨la, w, c, y, h, z⟩ := o
  simp only [kv, kvM, Prod.mk.injEq] at h1
  obtain ⟨e1, e2, e3, e4, e5⟩ := h1
  simp only at h2
  unfold pi
  rw [e1, e2, e3, e4, e5, h2]

/-- A false `wait` on either side makes the initiator's `wait` false. -/
theorem wsM_w1 (hψ : ψ > 0) (κ : Nat) (a b : MS ψ) (ha : a.label.val ≠ ψ - 1)
    (hb : b.label.val ≠ 0) (h : a.w = false ∨ b.w = false) : (wsM hψ κ a b).1.w = false := by
  obtain ⟨-, -, -, -, -, -, s7, -⟩ := wsM_spec hψ κ a b ha hb
  rw [s7]; rcases h with h | h <;> simp [h]

/-- A non-terminal row between two waiting cells. -/
theorem wsM_nt (hψ : ψ > 0) (κ : Nat) (a b : MS ψ) {k : Nat} (ha : a.label.val = k)
    (hb : b.label.val = k + 1) (hk : k + 2 < ψ) (hw1 : a.w = true) (hw2 : b.w = true) :
    (wsM hψ κ a b).1.w = true ∧ (wsM hψ κ a b).2.w = true ∧ (wsM hψ κ a b).1.y = false ∧
    (wsM hψ κ a b).1.z = false ∧ (wsM hψ κ a b).2.z = (a.z || b.z) := by
  have hT : b.label.val ≠ ψ - 1 := by omega
  obtain ⟨-, -, -, s4, s5, -, s7, -, -, s10, -, s12⟩ := wsM_spec hψ κ a b (by omega) (by omega)
  refine ⟨?_, ?_, s4, s5, ?_⟩
  · rw [s7]; simp [hT, hw1, hw2]
  · rw [s12]; simp [hw2]
  · rw [s10]; simp [hT]

/-- The terminal row between two waiting cells: the terminal count stays at most
`κ`; reaching `κ` releases the initiator's `wait`, otherwise both keep waiting. -/
theorem wsM_term (hψ : ψ > 0) (κ : Nat) (a b : MS ψ) {k : Nat} (ha : a.label.val = k)
    (hb : b.label.val = k + 1) (hk : k + 2 = ψ) (hw1 : a.w = true) (hw2 : b.w = true)
    (hc : b.c ≤ κ) :
    (wsM hψ κ a b).1.y = false ∧ (wsM hψ κ a b).1.z = false ∧ (wsM hψ κ a b).2.c ≤ κ ∧
    ((wsM hψ κ a b).2.c = κ → (wsM hψ κ a b).1.w = false) ∧
    ((wsM hψ κ a b).2.c ≠ κ → (wsM hψ κ a b).1.w = true ∧ (wsM hψ κ a b).2.w = true) := by
  have hT : b.label.val = ψ - 1 := by omega
  obtain ⟨-, -, -, s4, s5, -, s7, -, -, -, s11, s12⟩ := wsM_spec hψ κ a b (by omega) (by omega)
  rw [← s11] at s7 s12
  refine ⟨s4, s5, ?_, ?_, ?_⟩
  · rw [s11]; split
    · exact satCountSucc_le _ _
    · exact hc
  · intro h; rw [s7]; simp [hT, h]
  · intro h; rw [s7, s12]; simp [hT, h, hw1, hw2]

/-- `0/1` value of a bit. -/
def bv (b : Bool) : Nat := if b then 1 else 0

theorem p1 (k : Nat) : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
theorem p2 (k : Nat) : 2 ^ (k + 2) = 2 ^ k * 4 := by
  rw [show k + 2 = k + 1 + 1 from rfl, Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc]

/-- **Counter arithmetic, inner row.** With no pending reset at the initiator
and no carry at the responder, a non-terminal row keeps
`h_k·2^k + carry_k·2^(k+1) + h_(k+1)·2^(k+1) + carry_(k+1)·2^(k+2)`, except that
the head row adds one. -/
theorem wsM_arith (hψ : ψ > 0) (κ : Nat) (a b : MS ψ) {k : Nat} (ha : a.label.val = k)
    (hb : b.label.val = k + 1) (hk : k + 2 < ψ) (hz : a.z = false) (hby : b.y = false)
    (hay : k = 0 → a.y = false) :
    bv (wsM hψ κ a b).1.h * 2 ^ k +
        (bv (wsM hψ κ a b).2.h * 2 ^ (k + 1) + bv (wsM hψ κ a b).2.y * 2 ^ (k + 2)) =
      bv a.h * 2 ^ k + bv a.y * 2 ^ (k + 1) + bv b.h * 2 ^ (k + 1) +
        (if k = 0 then 1 else 0) := by
  have hT : b.label.val ≠ ψ - 1 := by omega
  obtain ⟨-, -, s3, -, -, -, -, s8, s9, -⟩ := wsM_spec hψ κ a b (by omega) (by omega)
  rw [s3, s8, s9, ha, p1, p2]
  by_cases h0 : k = 0
  · subst h0
    have hy := hay rfl
    cases hh : a.h <;> cases hbh : b.h <;> simp [hT, hz, hby, hy, hh, hbh, bv]
  · generalize 2 ^ k = P
    cases hh : a.h <;> cases hy : a.y <;> cases hbh : b.h <;>
      simp [hT, hz, hby, h0, hh, hy, hbh, bv] <;> omega

/-- **Counter arithmetic, terminal row.** Without release and below the cap, the
terminal row keeps `h_k·2^k + carry_k·2^(k+1) + h_T·2^(k+1) + count·2^ψ`. -/
theorem wsM_arith_last (hψ : ψ > 0) (κ : Nat) (a b : MS ψ) {k : Nat} (ha : a.label.val = k)
    (hb : b.label.val = k + 1) (hk : k + 2 = ψ) (hk1 : 1 ≤ k) (hz : a.z = false)
    (hbc : b.c < κ) (hrel : (wsM hψ κ a b).2.c ≠ κ) :
    bv (wsM hψ κ a b).1.h * 2 ^ k +
        (bv (wsM hψ κ a b).2.h * 2 ^ (k + 1) + (wsM hψ κ a b).2.c * 2 ^ ψ) =
      bv a.h * 2 ^ k + bv a.y * 2 ^ (k + 1) + (bv b.h * 2 ^ (k + 1) + b.c * 2 ^ ψ) := by
  have hT : b.label.val = ψ - 1 := by omega
  have h0 : k ≠ 0 := by omega
  obtain ⟨-, -, s3, -, -, -, -, s8, -, -, s11, -⟩ := wsM_spec hψ κ a b (by omega) (by omega)
  have P0f : decide (a.label.val = 0) = false := by simp [ha, h0]
  have Tt : decide (b.label.val = ψ - 1) = true := by simp [hT]
  simp only [P0f, Tt] at s3 s8 s11
  have e : satCountSucc κ b.c = b.c + 1 := Nat.min_eq_left (by omega)
  subst hk
  rw [p1, p2]
  generalize 2 ^ k = P
  cases hy : a.y <;> cases hbh : b.h <;> simp [hy, hbh, hz, e] at s3 s8 s11 <;>
    rw [s11] at hrel <;> rw [s3, s8, s11] <;> simp [bv, hy, hbh, Nat.add_mul] at hrel ⊢ <;> omega

/-- `S f m = f 0 + … + f (m-1)`. -/
def S (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => S f m + f m

theorem S_congr (f g : Nat → Nat) : ∀ m, (∀ i, i < m → f i = g i) → S f m = S g m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    show S f m + f m = S g m + g m
    rw [ih (fun i hi => h i (by omega)), h m (by omega)]

/-- Changing `f` at two adjacent positions changes `S f m` by the difference. -/
theorem S_two (f f' : Nat → Nat) (k : Nat) : ∀ m, k + 1 < m →
    (∀ i, i < m → i ≠ k → i ≠ k + 1 → f' i = f i) →
    S f' m + f k + f (k + 1) = S f m + f' k + f' (k + 1) := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro hm h
    show S f' m + f' m + f k + f (k + 1) = S f m + f m + f' k + f' (k + 1)
    by_cases hkm : k + 1 < m
    · have e := ih hkm (fun i hi h1 h2 => h i (by omega) h1 h2)
      rw [h m (by omega) (by omega) (by omega)]
      omega
    · have hm' : m = k + 1 := by omega
      subst hm'
      show S f' k + f' k + f' (k + 1) + f k + f (k + 1) =
        S f k + f k + f (k + 1) + f' k + f' (k + 1)
      rw [S_congr f' f k (fun i hi => h i (by omega) (by omega) (by omega))]
      omega

theorem S_lt (f : Nat → Nat) : ∀ m, (∀ i, i < m → f i ≤ 2 ^ i) → S f m + 1 ≤ 2 ^ m := by
  intro m
  induction m with
  | zero => intro _; simp [S]
  | succ m ih =>
    intro h
    have e := ih (fun i hi => h i (by omega))
    have e2 := h m (by omega)
    show S f m + f m + 1 ≤ 2 ^ (m + 1)
    rw [Nat.pow_succ]; omega

end ModelFacts


/-! ## Part E. WAIT on the block

`RchJ C L P`: some word of internal edges of block `g`, of length at most `L`,
reaches a leader or a configuration in `P`, and every configuration strictly
before the end of the word satisfies `WJ` (pathless head, no block cell in
`produce`/`done`). The phases:

* `walk`: a `wait = false` at cell `j+1` walks to the head in `j+1` rows
  (`e_j, …, e_0`); the last row starts the generation.
* `dirty_*`: with every block `wait` true, the first forward sweep clears all
  carries and resets below the terminal.
* `clean_*`: each later forward sweep adds one to the binary counter
  `Φ = count·2^ψ + Σ h_i 2^i` (+ pending carries) or releases the terminal's
  `wait`; `Φ < κ·2^ψ` bounds the number of sweeps by `κ·2^ψ`. -/

section Block
variable {n ψ : Nat}

open PPLLAuthResetDrain (authProtocol authRun)

/-- The WAIT registers of cell `k` of block `g`. -/
def cm (ring : DirectedRing n) (g : Nat) (C : Fin n → AuthState ψ) (k : Nat) : MS ψ :=
  pi (C (bcell ring ψ g k)).core

/-- The WAIT invariant: pathless head and no generation cell in the block. -/
def WJ (ring : DirectedRing n) (ψ g : Nat) (C : Fin n → AuthState ψ) : Prop :=
  (C (bcell ring ψ g 0)).core.path = .bot ∧ AllNG ring ψ g C

/-- Standing hypotheses, locality and the WAIT invariant. -/
def WI (ring : DirectedRing n) (ψ g : Nat) (C0 C : Fin n → AuthState ψ) : Prop :=
  Std C ∧ Out ring ψ g C0 C ∧ WJ ring ψ g C

/-- Generation started at block `g`: the head is a pathless producer. -/
def GenActive (ring : DirectedRing n) (ψ g : Nat) (C : Fin n → AuthState ψ) : Prop :=
  (C (bcell ring ψ g 0)).core.state = .produce ∧ (C (bcell ring ψ g 0)).core.path = .bot

/-- Reachability by internal edges of block `g` with the WAIT invariant on every
proper prefix. -/
def RchJ (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n) (g : Nat)
    (C : Fin n → AuthState ψ) (L : Nat) (P : (Fin n → AuthState ψ) → Prop) : Prop :=
  ∃ w : List (Fin n), w.length ≤ L ∧ (∀ e ∈ w, InBlk ring ψ g e) ∧
    (∀ m, m < w.length → WJ ring ψ g (authRun hp κ c ring C (w.take m))) ∧
    (Ldr (authRun hp κ c ring C w) ∨ P (authRun hp κ c ring C w))

theorem RchJ_now (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} {C : Fin n → AuthState ψ} {L : Nat} {P : (Fin n → AuthState ψ) → Prop} (h : P C) :
    RchJ hp κ c ring g C L P :=
  ⟨[], Nat.zero_le _, fun _ he => absurd he List.not_mem_nil,
    fun _ hm => absurd hm (Nat.not_lt_zero _), Or.inr h⟩

theorem RchJ_mono (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} {C : Fin n → AuthState ψ} {L L' : Nat} {P Q : (Fin n → AuthState ψ) → Prop}
    (hL : L ≤ L') (hPQ : ∀ D, P D → Q D) (h : RchJ hp κ c ring g C L P) :
    RchJ hp κ c ring g C L' Q := by
  obtain ⟨w, hw, he, hj, h⟩ := h
  exact ⟨w, Nat.le_trans hw hL, he, hj, h.imp id (hPQ _)⟩

theorem RchJ_bind (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} {C : Fin n → AuthState ψ} {L1 L2 : Nat} {P Q : (Fin n → AuthState ψ) → Prop}
    (h1 : RchJ hp κ c ring g C L1 (fun D => Q D ∨ P D))
    (h2 : ∀ D, P D → WJ ring ψ g D ∧ RchJ hp κ c ring g D L2 Q) :
    RchJ hp κ c ring g C (L1 + L2) Q := by
  obtain ⟨w1, hw1, he1, hj1, h1⟩ := h1
  rcases h1 with hL | hQ | hP
  · exact ⟨w1, by omega, he1, hj1, Or.inl hL⟩
  · exact ⟨w1, by omega, he1, hj1, Or.inr hQ⟩
  · obtain ⟨hJ, w2, hw2, he2, hj2, h2⟩ := h2 _ hP
    refine ⟨w1 ++ w2, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append]; omega
    · intro e he
      rcases List.mem_append.mp he with h | h
      · exact he1 e h
      · exact he2 e h
    · intro m hm
      rw [List.length_append] at hm
      rw [List.take_append]
      by_cases hm1 : m < w1.length
      · rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hm1), List.take_zero, List.append_nil]
        exact hj1 m hm1
      · rw [List.take_of_length_le (by omega), authRun_app]
        by_cases hm2 : m = w1.length
        · rw [hm2, Nat.sub_self, List.take_zero]; exact hJ
        · exact hj2 (m - w1.length) (by omega)
    · rw [authRun_app]; exact h2

/-- `RchJ_bind` with an early exit `Q0 ⊆ Q`. -/
theorem RchJ_bind' (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} {C : Fin n → AuthState ψ} {L1 L2 : Nat} {P Q0 Q : (Fin n → AuthState ψ) → Prop}
    (h1 : RchJ hp κ c ring g C L1 (fun D => Q0 D ∨ P D)) (hQ : ∀ D, Q0 D → Q D)
    (h2 : ∀ D, P D → WJ ring ψ g D ∧ RchJ hp κ c ring g D L2 Q) :
    RchJ hp κ c ring g C (L1 + L2) Q :=
  RchJ_bind hp κ c ring (P := P) (Q := Q)
    (RchJ_mono hp κ c ring (Q := fun D => Q D ∨ P D) (Nat.le_refl _)
      (fun D h => h.imp_left (hQ D)) h1) h2

/-- One block edge with the WAIT invariant on the starting configuration. -/
theorem stepJ (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} (hS : Std C)
    (hO : Out ring ψ g C0 C) (hJ : WJ ring ψ g C) {k : Nat} (hk : k + 1 < ψ) :
    RchJ hp κ c ring g C 1 (StepPost hp κ c ring g C0 C k) := by
  obtain ⟨w, hw, he, h⟩ := stepL_block hp κ c ring hg hS hO hk
  refine ⟨w, hw, he, ?_, h⟩
  intro m hm
  have : m = 0 := by omega
  subst this
  rw [List.take_zero]; exact hJ

theorem cm_lab (ring : DirectedRing n) {g k : Nat} (hg : g * ψ + ψ ≤ n) (hk : k < ψ)
    {C : Fin n → AuthState ψ} (hS : Std C) : (cm ring g C k).label.val = k := by
  have a := (hS (bcell ring ψ g k)).2.2
  rw [bcell_val ring hg hk, bcell_mod g k hk] at a
  exact a

/-- **One WAIT row on the block.** -/
theorem row_cfg (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} (hI : WI ring ψ g C0 C)
    {k : Nat} (hk : k + 1 < ψ) :
    RchJ hp κ c ring g C 1 (fun D => (k = 0 ∧ GenActive ring ψ g D) ∨
      (WI ring ψ g C0 D ∧
        ¬ (k = 0 ∧ (wsM hp κ (cm ring g C k) (cm ring g C (k + 1))).1.w = false) ∧
        cm ring g D k = (wsM hp κ (cm ring g C k) (cm ring g C (k + 1))).1 ∧
        cm ring g D (k + 1) = (wsM hp κ (cm ring g C k) (cm ring g C (k + 1))).2 ∧
        ∀ k', k' < ψ → k' ≠ k → k' ≠ k + 1 →
          D (bcell ring ψ g k') = C (bcell ring ψ g k'))) := by
  obtain ⟨hS, hO, hb0, hNG⟩ := hI
  apply RchJ_mono hp κ c ring (Nat.le_refl _) _ (stepJ hp κ c ring hg hS hO ⟨hb0, hNG⟩ hk)
  intro D ⟨hSD, hOD, e1, e2, eo⟩
  have hR := std_row ring hg hk hS
  rcases row_wait hp h3 κ c _ _ k hR (hNG k (by omega)) (hNG (k + 1) hk)
      (fun h0 => by subst h0; exact hb0) with ⟨k0, -, s1, p1⟩ | ⟨hns, a1, a2, n1, n2, pb⟩
  · left
    subst k0
    refine ⟨rfl, ?_, ?_⟩
    · rw [e1]; exact s1
    · rw [e1]; exact p1
  · right
    have la := cm_lab ring hg (k := k) (by omega) hS
    have lb := cm_lab ring hg (k := k + 1) hk hS
    obtain ⟨l1, l2, -⟩ := wsM_spec hp κ (cm ring g C k) (cm ring g C (k + 1))
      (by rw [la]; omega) (by rw [lb]; omega)
    refine ⟨⟨hSD, hOD, ?_, ?_⟩, hns, ?_, ?_, eo⟩
    · by_cases h0 : k = 0
      · subst h0; rw [e1]; exact pb rfl
      · rw [eo 0 (by omega) (Ne.symm h0) (by omega)]; exact hb0
    · intro k' hk'
      by_cases h1 : k' = k
      · rw [h1, e1]; exact n1
      · by_cases h2 : k' = k + 1
        · rw [h2, e2]; exact n2
        · rw [eo k' hk' h1 h2]; exact hNG k' hk'
    · apply pi_of
      · rw [e1]; exact a1
      · rw [l1]; apply Fin.ext
        show (D (bcell ring ψ g k)).core.label.val = (C (bcell ring ψ g k)).core.label.val
        have := cm_lab ring hg (k := k) (by omega) hSD
        exact this.trans la.symm
    · apply pi_of
      · rw [e2]; exact a2
      · rw [l2]; apply Fin.ext
        show (D (bcell ring ψ g (k + 1))).core.label.val =
          (C (bcell ring ψ g (k + 1))).core.label.val
        have := cm_lab ring hg (k := k + 1) hk hSD
        exact this.trans lb.symm

theorem cm_frame (ring : DirectedRing n) {g : Nat} {C D : Fin n → AuthState ψ} {k : Nat}
    (eo : ∀ k', k' < ψ → k' ≠ k → k' ≠ k + 1 → D (bcell ring ψ g k') = C (bcell ring ψ g k'))
    (i : Nat) (hi : i < ψ) (h1 : i ≠ k) (h2 : i ≠ k + 1) : cm ring g D i = cm ring g C i := by
  unfold cm; rw [eo i hi h1 h2]

/-! ### Walking a released `wait` to the head -/

/-- A false `wait` at the head starts the generation in one row. -/
theorem walk0 (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} (hI : WI ring ψ g C0 C)
    (h0 : (cm ring g C 0).w = false) : RchJ hp κ c ring g C 1 (GenActive ring ψ g) := by
  apply RchJ_mono hp κ c ring (Nat.le_refl _) _ (row_cfg hp h3 κ c ring hg hI (k := 0) (by omega))
  rintro D (⟨-, hA⟩ | ⟨-, hns, -⟩)
  · exact hA
  · exfalso; apply hns; refine ⟨rfl, ?_⟩
    exact wsM_w1 hp κ _ _ (by rw [cm_lab ring hg (by omega) hI.1]; omega)
      (by rw [cm_lab ring hg (by omega) hI.1]; omega) (Or.inl h0)

/-- **Walk.** A false `wait` at cell `j+1` reaches the head in the `j+1` rows
`e_j, …, e_0`; the last one starts the generation. -/
theorem walk (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) (C0 : Fin n → AuthState ψ) : ∀ j, j + 1 < ψ →
    ∀ C : Fin n → AuthState ψ, WI ring ψ g C0 C → (cm ring g C (j + 1)).w = false →
    RchJ hp κ c ring g C (j + 1) (GenActive ring ψ g) := by
  intro j
  induction j with
  | zero =>
    intro hj C hI hw
    apply RchJ_mono hp κ c ring (Nat.le_refl _) _
      (row_cfg hp h3 κ c ring hg hI (k := 0) (by omega))
    rintro D (⟨-, hA⟩ | ⟨-, hns, -⟩)
    · exact hA
    · exfalso; apply hns; refine ⟨rfl, ?_⟩
      exact wsM_w1 hp κ _ _ (by rw [cm_lab ring hg (by omega) hI.1]; omega)
        (by rw [cm_lab ring hg (by omega) hI.1]; omega) (Or.inr hw)
  | succ j ih =>
    intro hj C hI hw
    have hs := row_cfg hp h3 κ c ring hg hI (k := j + 1) (by omega)
    have h1 : RchJ hp κ c ring g C 1 (fun D => GenActive ring ψ g D ∨
        (WI ring ψ g C0 D ∧ (cm ring g D (j + 1)).w = false)) := by
      apply RchJ_mono hp κ c ring (Nat.le_refl _) _ hs
      rintro D (⟨h0, -⟩ | ⟨hI', -, e1, -, -⟩)
      · omega
      · right; refine ⟨hI', ?_⟩; rw [e1]
        exact wsM_w1 hp κ _ _ (by rw [cm_lab ring hg (by omega) hI.1]; omega)
          (by rw [cm_lab ring hg (by omega) hI.1]; omega) (Or.inr hw)
    have hb := RchJ_bind hp κ c ring h1 (fun D hD => ⟨hD.1.2.2, ih (by omega) D hD.1 hD.2⟩)
    exact RchJ_mono hp κ c ring (by omega) (fun _ h => h) hb

/-! ### The first forward sweep -/

/-- Every `wait` of the block is true. -/
def AllW (ring : DirectedRing n) (g : Nat) (C : Fin n → AuthState ψ) : Prop :=
  ∀ i, i < ψ → (cm ring g C i).w = true

/-- After rows `0, …, m-1` of the first sweep. -/
def DS (ring : DirectedRing n) (g κ : Nat) (C0 : Fin n → AuthState ψ) (m : Nat)
    (D : Fin n → AuthState ψ) : Prop :=
  WI ring ψ g C0 D ∧ AllW ring g D ∧
    (∀ i, i < m → (cm ring g D i).y = false ∧ (cm ring g D i).z = false) ∧
    (cm ring g D (ψ - 1)).c ≤ κ

/-- The terminal released its `wait`, now at cell `ψ-2`. -/
def Rel (ring : DirectedRing n) (ψ g : Nat) (C0 D : Fin n → AuthState ψ) : Prop :=
  WI ring ψ g C0 D ∧ (cm ring g D (ψ - 2)).w = false

/-- A clean waiting block: every `wait` true, no carry or reset below the
terminal, terminal count below `κ`. -/
def CS (ring : DirectedRing n) (g κ : Nat) (C0 D : Fin n → AuthState ψ) : Prop :=
  DS ring g κ C0 (ψ - 1) D ∧ (cm ring g D (ψ - 1)).c < κ

theorem dirty_step (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg)
    (ring : DirectedRing n) {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ}
    (m : Nat) (hm : m + 2 < ψ) (hD : DS ring g κ C0 m C) :
    RchJ hp κ c ring g C 1 (fun D => GenActive ring ψ g D ∨ DS ring g κ C0 (m + 1) D) := by
  obtain ⟨hI, hW, hC, hc⟩ := hD
  apply RchJ_mono hp κ c ring (Nat.le_refl _) _ (row_cfg hp h3 κ c ring hg hI (k := m) (by omega))
  rintro D (⟨-, hA⟩ | ⟨hI', -, e1, e2, eo⟩)
  · left; exact hA
  · right
    have la := cm_lab ring hg (k := m) (by omega) hI.1
    have lb := cm_lab ring hg (k := m + 1) (by omega) hI.1
    obtain ⟨w1, w2, y1, z1, -⟩ :=
      wsM_nt hp κ _ _ la lb hm (hW m (by omega)) (hW (m + 1) (by omega))
    have fr := cm_frame ring eo
    refine ⟨hI', ?_, ?_, ?_⟩
    · intro i hi
      by_cases h1 : i = m
      · rw [h1, e1]; exact w1
      · by_cases h2 : i = m + 1
        · rw [h2, e2]; exact w2
        · rw [fr i hi h1 h2]; exact hW i hi
    · intro i hi
      by_cases h1 : i = m
      · rw [h1, e1]; exact ⟨y1, z1⟩
      · rw [fr i (by omega) h1 (by omega)]; exact hC i (by omega)
    · rw [fr (ψ - 1) (by omega) (by omega) (by omega)]; exact hc

theorem dirty_iter (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg)
    (ring : DirectedRing n) {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ}
    (hD : DS ring g κ C0 0 C) : ∀ t, t ≤ ψ - 2 →
    RchJ hp κ c ring g C t (fun D => GenActive ring ψ g D ∨ DS ring g κ C0 t D) := by
  intro t
  induction t with
  | zero => intro _; exact RchJ_now hp κ c ring (Or.inr hD)
  | succ t ih =>
    intro ht
    exact RchJ_bind' hp κ c ring (ih (by omega)) (fun _ h => Or.inl h)
      (fun D hD => ⟨hD.1.2.2, dirty_step hp h3 κ c ring hg t (by omega) hD⟩)

theorem dirty_last (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg)
    (ring : DirectedRing n) {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ}
    (hD : DS ring g κ C0 (ψ - 2) C) :
    RchJ hp κ c ring g C 1 (fun D => GenActive ring ψ g D ∨
      (Rel ring ψ g C0 D ∨ CS ring g κ C0 D)) := by
  obtain ⟨hI, hW, hC, hc⟩ := hD
  have e : ψ - 2 + 1 = ψ - 1 := by omega
  apply RchJ_mono hp κ c ring (Nat.le_refl _) _
    (row_cfg hp h3 κ c ring hg hI (k := ψ - 2) (by omega))
  rintro D (⟨-, hA⟩ | ⟨hI', -, e1, e2, eo⟩)
  · left; exact hA
  · right
    have la := cm_lab ring hg (k := ψ - 2) (by omega) hI.1
    have lb := cm_lab ring hg (k := ψ - 2 + 1) (by omega) hI.1
    have hc' : (cm ring g C (ψ - 2 + 1)).c ≤ κ := by rw [e]; exact hc
    obtain ⟨y1, z1, cle, crel, cnrel⟩ := wsM_term hp κ _ _ la lb (by omega)
      (hW _ (by omega)) (hW _ (by omega)) hc'
    have fr := cm_frame ring eo
    by_cases hrel : (wsM hp κ (cm ring g C (ψ - 2)) (cm ring g C (ψ - 2 + 1))).2.c = κ
    · left; exact ⟨hI', by rw [e1]; exact crel hrel⟩
    · right
      obtain ⟨w1, w2⟩ := cnrel hrel
      refine ⟨⟨hI', ?_, ?_, ?_⟩, ?_⟩
      · intro i hi
        by_cases h1 : i = ψ - 2
        · rw [h1, e1]; exact w1
        · by_cases h2 : i = ψ - 2 + 1
          · rw [h2, e2]; exact w2
          · rw [fr i hi h1 h2]; exact hW i hi
      · intro i hi
        by_cases h1 : i = ψ - 2
        · rw [h1, e1]; exact ⟨y1, z1⟩
        · rw [fr i (by omega) h1 (by omega)]; exact hC i (by omega)
      · rw [← e, e2]; exact cle
      · rw [← e, e2]; omega

/-! ### Clean sweeps: a binary counter -/

/-- Weight of cell `i` in the counter: `h_i·2^i` plus a pending carry
`carry_i·2^(i+1)` below the terminal. -/
def fM (ring : DirectedRing n) (g : Nat) (D : Fin n → AuthState ψ) (i : Nat) : Nat :=
  bv (cm ring g D i).h * 2 ^ i + (if i + 1 < ψ then bv (cm ring g D i).y * 2 ^ (i + 1) else 0)

/-- The counter `Φ = count_T·2^ψ + Σ_{i<ψ} fM i`. -/
def Phi (ring : DirectedRing n) (g : Nat) (D : Fin n → AuthState ψ) : Nat :=
  (cm ring g D (ψ - 1)).c * 2 ^ ψ + S (fM ring g D) ψ

/-- Inside a clean sweep, before row `m`: the only possible carry is at cell `m`. -/
def CPre (ring : DirectedRing n) (g : Nat) (C0 : Fin n → AuthState ψ) (m : Nat)
    (D : Fin n → AuthState ψ) : Prop :=
  WI ring ψ g C0 D ∧ AllW ring g D ∧ (∀ i, i < ψ - 1 → (cm ring g D i).z = false) ∧
    (∀ i, i < ψ - 1 → i ≠ m → (cm ring g D i).y = false) ∧ (m = 0 → (cm ring g D 0).y = false)

theorem clean_row (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg)
    (ring : DirectedRing n) {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ}
    (m : Nat) (hm : m + 2 < ψ) (hD : CPre ring g C0 m C) :
    RchJ hp κ c ring g C 1 (fun D => GenActive ring ψ g D ∨
      (CPre ring g C0 (m + 1) D ∧ (cm ring g D (ψ - 1)).c = (cm ring g C (ψ - 1)).c ∧
        Phi ring g D = Phi ring g C + (if m = 0 then 1 else 0))) := by
  obtain ⟨hI, hW, hZ, hY, hY0⟩ := hD
  apply RchJ_mono hp κ c ring (Nat.le_refl _) _ (row_cfg hp h3 κ c ring hg hI (k := m) (by omega))
  rintro D (⟨-, hA⟩ | ⟨hI', -, e1, e2, eo⟩)
  · left; exact hA
  · right
    have la := cm_lab ring hg (k := m) (by omega) hI.1
    have lb := cm_lab ring hg (k := m + 1) (by omega) hI.1
    obtain ⟨w1, w2, y1, z1, z2⟩ :=
      wsM_nt hp κ _ _ la lb hm (hW m (by omega)) (hW (m + 1) (by omega))
    have hby : (cm ring g C (m + 1)).y = false := hY (m + 1) (by omega) (by omega)
    have ar := wsM_arith hp κ _ _ la lb hm (hZ m (by omega)) hby
      (fun h0 => by rw [h0]; exact hY0 h0)
    have fr := cm_frame ring eo
    refine ⟨⟨hI', ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro i hi
      by_cases h1 : i = m
      · rw [h1, e1]; exact w1
      · by_cases h2 : i = m + 1
        · rw [h2, e2]; exact w2
        · rw [fr i hi h1 h2]; exact hW i hi
    · intro i hi
      by_cases h1 : i = m
      · rw [h1, e1]; exact z1
      · by_cases h2 : i = m + 1
        · rw [h2, e2, z2, hZ m (by omega), hZ (m + 1) (by omega)]; rfl
        · rw [fr i (by omega) h1 h2]; exact hZ i hi
    · intro i hi hne
      by_cases h1 : i = m
      · rw [h1, e1]; exact y1
      · rw [fr i (by omega) h1 hne]; exact hY i hi h1
    · intro h; omega
    · rw [fr (ψ - 1) (by omega) (by omega) (by omega)]
    · unfold Phi
      rw [fr (ψ - 1) (by omega) (by omega) (by omega)]
      have hS := S_two (fM ring g C) (fM ring g D) m ψ (by omega)
        (fun i hi h1 h2 => by unfold fM; rw [fr i hi h1 h2])
      have f1 : fM ring g D m =
          bv (wsM hp κ (cm ring g C m) (cm ring g C (m + 1))).1.h * 2 ^ m := by
        unfold fM; rw [if_pos (by omega), e1, y1]; simp [bv]
      have f2 : fM ring g D (m + 1) =
          bv (wsM hp κ (cm ring g C m) (cm ring g C (m + 1))).2.h * 2 ^ (m + 1) +
            bv (wsM hp κ (cm ring g C m) (cm ring g C (m + 1))).2.y * 2 ^ (m + 2) := by
        unfold fM; rw [if_pos (by omega), e2]
      have f3 : fM ring g C m =
          bv (cm ring g C m).h * 2 ^ m + bv (cm ring g C m).y * 2 ^ (m + 1) := by
        unfold fM; rw [if_pos (by omega)]
      have f4 : fM ring g C (m + 1) = bv (cm ring g C (m + 1)).h * 2 ^ (m + 1) := by
        unfold fM; rw [if_pos (by omega), hby]; simp [bv]
      by_cases h0 : m = 0
      · rw [if_pos h0] at ar ⊢; omega
      · rw [if_neg h0] at ar ⊢; omega

theorem clean_iter (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg)
    (ring : DirectedRing n) {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ}
    (hD : CPre ring g C0 0 C) : ∀ t, t ≤ ψ - 2 →
    RchJ hp κ c ring g C t (fun D => GenActive ring ψ g D ∨
      (CPre ring g C0 t D ∧ (cm ring g D (ψ - 1)).c = (cm ring g C (ψ - 1)).c ∧
        Phi ring g D = Phi ring g C + (if t = 0 then 0 else 1))) := by
  intro t
  induction t with
  | zero => intro _; exact RchJ_now hp κ c ring (Or.inr ⟨hD, rfl, by simp⟩)
  | succ t ih =>
    intro ht
    refine RchJ_bind' hp κ c ring (ih (by omega)) (fun _ h => Or.inl h) ?_
    intro D ⟨hD', hc, hΦ⟩
    refine ⟨hD'.1.2.2, ?_⟩
    apply RchJ_mono hp κ c ring (Nat.le_refl _) _ (clean_row hp h3 κ c ring hg t (by omega) hD')
    rintro E (hA | ⟨hE, hcE, hΦE⟩)
    · left; exact hA
    · right
      refine ⟨hE, hcE.trans hc, ?_⟩
      rw [hΦE, hΦ, if_neg (Nat.succ_ne_zero t)]
      by_cases h0 : t = 0
      · rw [if_pos h0, if_pos h0]
      · rw [if_neg h0, if_neg h0]

theorem clean_last (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg)
    (ring : DirectedRing n) {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ}
    (hD : CPre ring g C0 (ψ - 2) C) (hc : (cm ring g C (ψ - 1)).c < κ) :
    RchJ hp κ c ring g C 1 (fun D => GenActive ring ψ g D ∨
      (Rel ring ψ g C0 D ∨ (CS ring g κ C0 D ∧ Phi ring g D = Phi ring g C))) := by
  obtain ⟨hI, hW, hZ, hY, -⟩ := hD
  have e : ψ - 2 + 1 = ψ - 1 := by omega
  apply RchJ_mono hp κ c ring (Nat.le_refl _) _
    (row_cfg hp h3 κ c ring hg hI (k := ψ - 2) (by omega))
  rintro D (⟨-, hA⟩ | ⟨hI', -, e1, e2, eo⟩)
  · left; exact hA
  · right
    have la := cm_lab ring hg (k := ψ - 2) (by omega) hI.1
    have lb := cm_lab ring hg (k := ψ - 2 + 1) (by omega) hI.1
    have hc' : (cm ring g C (ψ - 2 + 1)).c < κ := by rw [e]; exact hc
    obtain ⟨y1, z1, cle, crel, cnrel⟩ := wsM_term hp κ _ _ la lb (by omega)
      (hW _ (by omega)) (hW _ (by omega)) (Nat.le_of_lt hc')
    have fr := cm_frame ring eo
    by_cases hrel : (wsM hp κ (cm ring g C (ψ - 2)) (cm ring g C (ψ - 2 + 1))).2.c = κ
    · left; exact ⟨hI', by rw [e1]; exact crel hrel⟩
    · right
      obtain ⟨w1, w2⟩ := cnrel hrel
      have ar := wsM_arith_last hp κ _ _ la lb (by omega) (by omega) (hZ (ψ - 2) (by omega))
        hc' hrel
      refine ⟨⟨⟨hI', ?_, ?_, ?_⟩, ?_⟩, ?_⟩
      · intro i hi
        by_cases h1 : i = ψ - 2
        · rw [h1, e1]; exact w1
        · by_cases h2 : i = ψ - 2 + 1
          · rw [h2, e2]; exact w2
          · rw [fr i hi h1 h2]; exact hW i hi
      · intro i hi
        by_cases h1 : i = ψ - 2
        · rw [h1, e1]; exact ⟨y1, z1⟩
        · rw [fr i (by omega) h1 (by omega)]
          exact ⟨hY i (by omega) h1, hZ i (by omega)⟩
      · rw [← e, e2]; exact cle
      · rw [← e, e2]; omega
      · unfold Phi
        rw [← e, e2]
        have hS := S_two (fM ring g C) (fM ring g D) (ψ - 2) ψ (by omega)
          (fun i hi h1 h2 => by unfold fM; rw [fr i hi h1 h2])
        have f1 : fM ring g D (ψ - 2) =
            bv (wsM hp κ (cm ring g C (ψ - 2)) (cm ring g C (ψ - 2 + 1))).1.h * 2 ^ (ψ - 2) := by
          unfold fM; rw [if_pos (by omega), e1, y1]; simp [bv]
        have f2 : fM ring g D (ψ - 2 + 1) =
            bv (wsM hp κ (cm ring g C (ψ - 2)) (cm ring g C (ψ - 2 + 1))).2.h *
              2 ^ (ψ - 2 + 1) := by
          unfold fM; rw [if_neg (by omega), e2]; simp
        have f3 : fM ring g C (ψ - 2) =
            bv (cm ring g C (ψ - 2)).h * 2 ^ (ψ - 2) +
              bv (cm ring g C (ψ - 2)).y * 2 ^ (ψ - 2 + 1) := by
          unfold fM; rw [if_pos (by omega)]
        have f4 : fM ring g C (ψ - 2 + 1) = bv (cm ring g C (ψ - 2 + 1)).h * 2 ^ (ψ - 2 + 1) := by
          unfold fM; rw [if_neg (by omega)]; simp
        omega

/-- `Φ < κ·2^ψ` on a clean waiting block. -/
theorem Phi_bound (ring : DirectedRing n) {g κ : Nat} {C0 D : Fin n → AuthState ψ}
    (hD : CS ring g κ C0 D) : Phi ring g D + 1 ≤ κ * 2 ^ ψ := by
  obtain ⟨⟨-, -, hYZ, -⟩, hc⟩ := hD
  have hs := S_lt (fM ring g D) ψ (fun i hi => by
    unfold fM
    by_cases h : i + 1 < ψ
    · rw [if_pos h, (hYZ i (by omega)).1]
      cases (cm ring g D i).h <;> simp [bv]
    · rw [if_neg h]
      cases (cm ring g D i).h <;> simp [bv])
  unfold Phi
  have hm := Nat.mul_le_mul_right (2 ^ ψ) (Nat.succ_le_of_lt hc)
  rw [Nat.succ_mul] at hm
  omega

theorem clean_sweep (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg)
    (ring : DirectedRing n) {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ}
    (hD : CS ring g κ C0 C) :
    RchJ hp κ c ring g C (ψ - 1) (fun D => GenActive ring ψ g D ∨
      (Rel ring ψ g C0 D ∨ (CS ring g κ C0 D ∧ Phi ring g D = Phi ring g C + 1))) := by
  obtain ⟨⟨hI, hW, hYZ, -⟩, hc⟩ := hD
  have hpre : CPre ring g C0 0 C :=
    ⟨hI, hW, fun i hi => (hYZ i hi).2, fun i hi _ => (hYZ i hi).1,
      fun _ => (hYZ 0 (by omega)).1⟩
  have h1 := clean_iter hp h3 κ c ring hg hpre (ψ - 2) (Nat.le_refl _)
  have h2 := RchJ_bind' hp κ c ring (L2 := 1) (Q := fun D => GenActive ring ψ g D ∨
      (Rel ring ψ g C0 D ∨ (CS ring g κ C0 D ∧ Phi ring g D = Phi ring g C + 1)))
    h1 (fun _ h => Or.inl h) (fun D hD => ⟨hD.1.1.2.2,
    RchJ_mono hp κ c ring (Nat.le_refl _) (fun E hE => by
      rcases hE with hA | hR | ⟨hC, hΦ⟩
      · exact Or.inl hA
      · exact Or.inr (Or.inl hR)
      · refine Or.inr (Or.inr ⟨hC, ?_⟩)
        rw [hΦ, hD.2.2, if_neg (by omega)])
      (clean_last hp h3 κ c ring hg hD.1 (by rw [hD.2.1]; exact hc))⟩)
  exact RchJ_mono hp κ c ring (by omega) (fun _ h => h) h2

theorem clean_sweeps (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg)
    (ring : DirectedRing n) {g : Nat} (hg : g * ψ + ψ ≤ n) (C0 : Fin n → AuthState ψ) :
    ∀ N (D : Fin n → AuthState ψ), CS ring g κ C0 D → κ * 2 ^ ψ ≤ Phi ring g D + N →
    RchJ hp κ c ring g D (N * (ψ - 1)) (fun E => GenActive ring ψ g E ∨ Rel ring ψ g C0 E) := by
  intro N
  induction N with
  | zero =>
    intro D hD hN
    have := Phi_bound ring hD
    omega
  | succ N ih =>
    intro D hD hN
    have h1 := clean_sweep hp h3 κ c ring hg hD
    have h1' : RchJ hp κ c ring g D (ψ - 1) (fun E => (GenActive ring ψ g E ∨ Rel ring ψ g C0 E) ∨
        (CS ring g κ C0 E ∧ Phi ring g E = Phi ring g D + 1)) := by
      apply RchJ_mono hp κ c ring (Nat.le_refl _) _ h1
      rintro E (hA | hR | hC)
      · exact Or.inl (Or.inl hA)
      · exact Or.inl (Or.inr hR)
      · exact Or.inr hC
    have h2 := RchJ_bind hp κ c ring h1'
      (fun E hE => ⟨hE.1.1.1.2.2, ih E hE.1 (by rw [hE.2]; omega)⟩)
    apply RchJ_mono hp κ c ring _ (fun _ h => h) h2
    rw [Nat.add_mul, Nat.one_mul]; omega

/-! ### Assembly -/

theorem waitReady_core (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg)
    (ring : DirectedRing n) {g : Nat} (hg : g * ψ + ψ ≤ n) (C : Fin n → AuthState ψ)
    (hI : WI ring ψ g C C) (hκ : (cm ring g C (ψ - 1)).c ≤ κ) :
    RchJ hp κ c ring g C ((1 + κ * 2 ^ ψ) * (ψ - 1) + (ψ - 2)) (GenActive ring ψ g) := by
  have hT : (1 + κ * 2 ^ ψ) * (ψ - 1) + (ψ - 2) = (ψ - 1) + κ * 2 ^ ψ * (ψ - 1) + (ψ - 2) := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hT]
  by_cases hex : ∃ i, i < ψ ∧ (cm ring g C i).w = false
  · obtain ⟨i, hi, hw⟩ := hex
    cases i with
    | zero =>
      exact RchJ_mono hp κ c ring (by omega) (fun _ h => h) (walk0 hp h3 κ c ring hg hI hw)
    | succ j =>
      exact RchJ_mono hp κ c ring (by omega) (fun _ h => h)
        (walk hp h3 κ c ring hg C j hi C hI hw)
  · have hW : AllW ring g C := fun i hi => by
      cases h : (cm ring g C i).w
      · exact absurd ⟨i, hi, h⟩ hex
      · rfl
    have hd : DS ring g κ C 0 C := ⟨hI, hW, fun i hi => absurd hi (Nat.not_lt_zero _), hκ⟩
    have h1 := dirty_iter hp h3 κ c ring hg hd (ψ - 2) (Nat.le_refl _)
    have hwalk : ∀ D, Rel ring ψ g C D → RchJ hp κ c ring g D (ψ - 2) (GenActive ring ψ g) := by
      intro D hR
      have e : ψ - 3 + 1 = ψ - 2 := by omega
      have := walk hp h3 κ c ring hg C (ψ - 3) (by omega) D hR.1 (by rw [e]; exact hR.2)
      rw [e] at this; exact this
    have hrest : ∀ E, (Rel ring ψ g C E ∨ CS ring g κ C E) → WJ ring ψ g E ∧
        RchJ hp κ c ring g E (κ * 2 ^ ψ * (ψ - 1) + (ψ - 2)) (GenActive ring ψ g) := by
      intro D hD
      rcases hD with hR | hC
      · exact ⟨hR.1.2.2, RchJ_mono hp κ c ring (by omega) (fun _ h => h) (hwalk D hR)⟩
      · refine ⟨hC.1.1.2.2, ?_⟩
        have hs := clean_sweeps hp h3 κ c ring hg C (κ * 2 ^ ψ) D hC (by omega)
        exact RchJ_bind hp κ c ring hs (fun E hE => ⟨hE.1.2.2, hwalk E hE⟩)
    have hlast : ∀ D, DS ring g κ C (ψ - 2) D → WJ ring ψ g D ∧
        RchJ hp κ c ring g D (1 + (κ * 2 ^ ψ * (ψ - 1) + (ψ - 2))) (GenActive ring ψ g) :=
      fun D hD => ⟨hD.1.2.2, RchJ_bind hp κ c ring (dirty_last hp h3 κ c ring hg hD) hrest⟩
    have h4 := RchJ_bind hp κ c ring h1 hlast
    exact RchJ_mono hp κ c ring (by omega) (fun _ h => h) h4

end Block


/-! ## Part F. Headline -/

section Headline
variable {n ψ : Nat}

open PPLLAuthResetDrain (authProtocol authRun)

/-- **WAIT-readiness leaf (Q20606 §§5–9), AuthF, block `g`, `ψ ≥ 3`.**
Hypotheses: leaderless, `reset_cmd = false`, perfect labels, `echo` arbitrary;
the head of block `g` is pathless; no cell of block `g` is in `produce` or
`done`; the terminal `count` is at most `κ` (`inProtocolDomain`); `wait` fields
arbitrary. Then a word of internal edges of block `g` of length at most
`(1 + κ·2^ψ)(ψ-1) + (ψ-2)` reaches a leader or starts the generation (the head
is a pathless producer). Every configuration strictly before the end of the
word keeps the head pathless and the block free of `produce`/`done`; the word
only schedules edges `gψ ≤ e ≤ gψ+ψ-2` and never changes a cell outside the
block. -/
theorem waitReady_block (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg)
    (ring : DirectedRing n) (g : Nat) (hg : g * ψ + ψ ≤ n) (C : Fin n → AuthState ψ)
    (hL : ∀ i, (C i).core.leader = false) (hR : ∀ i, (C i).core.reset_cmd = false)
    (hPL : ∀ i, (C i).core.label.val = i.val % ψ)
    (hb : (C (bcell ring ψ g 0)).core.path = .bot)
    (hNG : ∀ k, k < ψ → (C (bcell ring ψ g k)).core.state ≠ .produce ∧
      (C (bcell ring ψ g k)).core.state ≠ .done)
    (hκ : (C (bcell ring ψ g (ψ - 1))).core.count ≤ κ) :
    ∃ w : List (Fin n), w.length ≤ (1 + κ * 2 ^ ψ) * (ψ - 1) + (ψ - 2) ∧
      (∀ e ∈ w, g * ψ ≤ e.val ∧ e.val ≤ g * ψ + ψ - 2) ∧
      (∀ i : Fin n, (i.val < g * ψ ∨ g * ψ + ψ ≤ i.val) → authRun hp κ c ring C w i = C i) ∧
      (∀ m, m < w.length →
        (authRun hp κ c ring C (w.take m) (bcell ring ψ g 0)).core.path = .bot ∧
        ∀ k, k < ψ →
          (authRun hp κ c ring C (w.take m) (bcell ring ψ g k)).core.state ≠ .produce ∧
          (authRun hp κ c ring C (w.take m) (bcell ring ψ g k)).core.state ≠ .done) ∧
      ((∃ i, (authRun hp κ c ring C w i).core.leader = true) ∨
        ((authRun hp κ c ring C w (bcell ring ψ g 0)).core.state = .produce ∧
          (authRun hp κ c ring C w (bcell ring ψ g 0)).core.path = .bot)) := by
  have hI : WI ring ψ g C C := ⟨fun i => ⟨hL i, hR i, hPL i⟩, fun _ _ => rfl, hb, hNG⟩
  obtain ⟨w, hw, he, hj, hfin⟩ := waitReady_core hp h3 κ c ring hg C hI hκ
  have loc := inBlk_local hp κ c ring hg C w he
  exact ⟨w, hw, loc.1, loc.2, hj, hfin⟩

/-- `waitReady_block` on the published `authFplusmcc` configuration. -/
theorem waitReady_block_mcc (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat)
    (ring : DirectedRing n) (g : Nat) (hg : g * ψ + ψ ≤ n) (C : Fin n → AuthState ψ)
    (hL : ∀ i, (C i).core.leader = false) (hR : ∀ i, (C i).core.reset_cmd = false)
    (hPL : ∀ i, (C i).core.label.val = i.val % ψ)
    (hb : (C (bcell ring ψ g 0)).core.path = .bot)
    (hNG : ∀ k, k < ψ → (C (bcell ring ψ g k)).core.state ≠ .produce ∧
      (C (bcell ring ψ g k)).core.state ≠ .done)
    (hκ : (C (bcell ring ψ g (ψ - 1))).core.count ≤ κ) :
    ∃ w : List (Fin n), w.length ≤ (1 + κ * 2 ^ ψ) * (ψ - 1) + (ψ - 2) ∧
      (∀ e ∈ w, g * ψ ≤ e.val ∧ e.val ≤ g * ψ + ψ - 2) ∧
      (∀ i : Fin n, (i.val < g * ψ ∨ g * ψ + ψ ≤ i.val) →
        authRun hp κ PPLLAuthResetDrain.authFplusmcc ring C w i = C i) ∧
      ((∃ i, (authRun hp κ PPLLAuthResetDrain.authFplusmcc ring C w i).core.leader = true) ∨
        ((authRun hp κ PPLLAuthResetDrain.authFplusmcc ring C w (bcell ring ψ g 0)).core.state
            = .produce ∧
          (authRun hp κ PPLLAuthResetDrain.authFplusmcc ring C w (bcell ring ψ g 0)).core.path
            = .bot)) := by
  obtain ⟨w, hw, he, ho, -, hfin⟩ :=
    waitReady_block hp h3 κ PPLLAuthResetDrain.authFplusmcc ring g hg C hL hR hPL hb hNG hκ
  exact ⟨w, hw, he, ho, hfin⟩

end Headline

#print axioms waitReady_block
#print axioms waitReady_block_mcc

end PPLLAuthWaitReady
