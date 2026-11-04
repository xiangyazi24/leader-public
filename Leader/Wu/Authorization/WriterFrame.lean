import Leader.Wu.Authorization.ResetDrain
/-! Writer frame of the AuthF comparison prefix (Z-div liveness, stage 2).

Every stage of `PPLLAuthF.pipeline` before `k4Kernel` (P′, GENSIG, CLEAN,
release, eliminate, SIGMOVE, dropStale, pre-CHECK reset, normalizeReady, CHECK,
DISAPPEAR, repair, comparison lifecycle, Algorithm 14) preserves the complete
writer projection `wp` of both endpoints, for every `Cfg` and every input: no
leaderless or other hypothesis is needed for the frame itself.

## The writer projection

`writeSeq` and all its callees (`writeSeqLeaderMove`, `groupInfo*`,
`gensigWriteseq*`, `writeSeqReady`/`SetWriteReady`, `writeSeqCompare`/
`CheckBit`/`checkBitWS`, `writeSeqCommands`/`SetWriteAct`/`FinalR`,
`writeAction*`/`writeActionToState`, `moveWsig*`; `Leader/Wu/Protocol/Algorithm.lean`
632-1075) read exactly the fields
`bit, path3, write, write_state, gen_ws, ws_echo, signal_ws, last, last_set,
last_unset, b_carry, label, leader` (exhaustive grep of every field access in
that range). `wp` is the first eleven; `label` and `leader` are the comparison
control fields handled by `PPLLAuthResetDrain` (`prefix_writer_inputs` below
states what the suffix sees). `writeWithBundle` additionally copies
`shield/bullet/signal_B` and reads `r.leader, r.label, l.leader`.

## Proof

The same stage decomposition as `PPLLAuthResetDrain`, with the writer view in
place of the drain view. No prefix stage writes any writer field: the only
writes are to comparison fields (`state, path, path2, path4, path5, p, p_carry`),
WAIT fields (`reset, h_field, carry, count, wait`), P′ fields (`label, phase,
probe, leader`), `reset_cmd, echo, count` (Algorithm 14), the CHECK/BEQ births
(`leader`) and provenance marks; `clearCmp`/`clearCmpAuth` keep the writer
fields.
-/
namespace PPLLAuthWriterFrame
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
  PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF PPLLAuthResetDrain
set_option linter.unusedSimpArgs false

/-- The writer projection: every field `writeSeq` reads except `label/leader`. -/
def wp {ψ : Nat} (u : AgentState ψ) :
    Bool × Option Path3Info × WriteAction × WriteState × Bool × Bool × Bool × Bool × Bool ×
      Bool × Bool :=
  (u.bit, u.path3, u.write, u.write_state, u.gen_ws, u.ws_echo, u.signal_ws, u.last,
    u.last_set, u.last_unset, u.b_carry)

/-- The writer projection of an AuthF cell is that of its core. -/
def aw {ψ : Nat} (u : AuthState ψ) := wp u.core

section Ite
variable {ψ : Nat}
theorem bit_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).bit = if p then a.bit else b.bit := by split <;> rfl
theorem path3_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path3 = if p then a.path3 else b.path3 := by split <;> rfl
theorem write_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).write = if p then a.write else b.write := by split <;> rfl
theorem wst_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).write_state = if p then a.write_state else b.write_state := by split <;> rfl
theorem genws_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).gen_ws = if p then a.gen_ws else b.gen_ws := by split <;> rfl
theorem wsecho_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).ws_echo = if p then a.ws_echo else b.ws_echo := by split <;> rfl
theorem sigws_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).signal_ws = if p then a.signal_ws else b.signal_ws := by split <;> rfl
theorem last_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).last = if p then a.last else b.last := by split <;> rfl
theorem lastset_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).last_set = if p then a.last_set else b.last_set := by split <;> rfl
theorem lastunset_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).last_unset = if p then a.last_unset else b.last_unset := by split <;> rfl
theorem bcarry_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).b_carry = if p then a.b_carry else b.b_carry := by split <;> rfl
theorem wp_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    wp (if p then a else b) = if p then wp a else wp b := by split <;> rfl
theorem aw_ite (p : Prop) [Decidable p] (a b : AuthState ψ) :
    aw (if p then a else b) = if p then aw a else aw b := by split <;> rfl
end Ite

section CoreStages
variable {ψ : Nat}

theorem clearCmp_wp (u : AgentState ψ) : wp (clearCmp u) = wp u := rfl

theorem wait_wp (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    wp (waitSaturated hψ κ l r).1 = wp l ∧ wp (waitSaturated hψ κ l r).2 = wp r := by
  simp only [waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish]
  simp only [fst_ite, snd_ite, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite,
    ite_self, and_self]

theorem genConnect_wp (u : AgentState ψ) : wp (cleanSigGenConnect u) = wp u := by
  cases h : u.path <;> simp only [cleanSigGenConnect, h] <;>
    simp [wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem releaseSource_wp (hψ : ψ > 0) (l r : AgentState ψ) :
    wp (releaseSource hψ l r).1 = wp l ∧ wp (releaseSource hψ l r).2 = wp r := by
  simp [releaseSource, fst_ite, snd_ite, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem eliminate_wp (hψ : ψ > 0) (l r : AgentState ψ) :
    wp (eliminateSig hψ l r).1 = wp l ∧ wp (eliminateSig hψ l r).2 = wp r := by
  simp [eliminateSig, fst_ite, snd_ite, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem control_wp (hψ : ψ > 0) (u : AgentState ψ) :
    wp (sigMoveApplyControlConsume hψ u) = wp u := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;>
    simp [wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem dropStale_wp (u : AgentState ψ) : wp (dropStale u) = wp u := by
  simp [dropStale, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem orphan_wp (u : AgentState ψ) : wp (normalizeOrphan u) = wp u := by
  cases h : u.path <;> simp [normalizeOrphan, h, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem carrier_wp (u : AgentState ψ) : wp (normalizeCarrier u) = wp u := by
  cases h : u.path <;>
    simp [normalizeCarrier, releaseCongest, h, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem ready_wp (u : AgentState ψ) : wp (normalizeReady u) = wp u := by
  generalize ho : normalizeOrphan u = o
  have vo : wp o = wp u := by rw [← ho]; exact orphan_wp u
  simp only [normalizeReady, ho]
  generalize hc : (if o.state = .none ∧ aligned o then o else normalizeCarrier o) = c
  have vc : wp c = wp o := by rw [← hc]; simp [wp_ite, carrier_wp]
  have ht := vc.trans vo
  cases hp : c.path <;> simpa [hp, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite] using ht

theorem checkReady_wp (u : AgentState ψ) : wp (checkSigSetReadyGuarded u) = wp u := by
  cases h : u.path <;>
    simp [checkSigSetReadyGuarded, checkSigSetReady, h, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem checkL_wp (hψ : ψ > 0) (u : AgentState ψ) : wp (checkSigCheckL hψ u) = wp u := by
  unfold checkSigCheckL
  split <;> simp [wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem checkR_wp (hψ : ψ > 0) (l r : AgentState ψ) : wp (checkSigCheckR hψ l r) = wp r := by
  unfold checkSigCheckR
  split <;> simp [wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem result_wp (u : AgentState ψ) : wp (checkSigSetResult u) = wp u := by
  simp [checkSigSetResult, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem disStart_wp (hψ : ψ > 0) (l r : AgentState ψ) :
    wp (disappearStartL hψ l r).1 = wp l ∧ wp (disappearStartL hψ l r).2 = wp r := by
  simp [disappearStartL, fst_ite, snd_ite, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem disCarry_wp (hψ : ψ > 0) (l r : AgentState ψ) :
    wp (disappearCarry hψ l r).1 = wp l ∧ wp (disappearCarry hψ l r).2 = wp r := by
  simp [disappearCarry, fst_ite, snd_ite, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem releaseSuffix_wp (l r : AgentState ψ) :
    wp (releaseReadySuffix l r).1 = wp l ∧ wp (releaseReadySuffix l r).2 = wp r := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [releaseReadySuffix, hl, hr, fst_ite, snd_ite, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem ackTail_wp (l r : AgentState ψ) :
    wp (ackTail l r).1 = wp l ∧ wp (ackTail l r).2 = wp r := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [ackTail, hl, hr, fst_ite, snd_ite, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem dropStray_wp (l r : AgentState ψ) :
    wp (dropStray l r).1 = wp l ∧ wp (dropStray l r).2 = wp r := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [dropStray, hl, hr, fst_ite, snd_ite, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem landBackward_wp (u : AgentState ψ) : wp (landBackward u) = wp u := by
  cases hp : u.path <;> cases ht : u.path2 <;>
    simp [landBackward, hp, ht, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]


theorem landForward_wp (κ : Nat) (u : AgentState ψ) :
    wp (landForward κ false true u) = wp u := by
  cases hp : u.path <;> cases ht : u.path2 <;>
    simp [landForward, hp, ht, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem pPsi_wp (hψ : ψ > 0) (l r : AgentState ψ) :
    wp (pPsiProbeWall hψ l r).1 = wp l ∧ wp (pPsiProbeWall hψ l r).2 = wp r := by
  simp only [pPsiProbeWall, pPsi]
  simp [fst_ite, snd_ite, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

theorem suppress_wp (hψ : ψ > 0) (l r : AgentState ψ) :
    wp (suppressSigResetKill hψ l r).1 = wp l ∧ wp (suppressSigResetKill hψ l r).2 = wp r := by
  cases h1 : l.leader <;> cases h2 : l.reset_cmd <;> cases h3 : r.reset_cmd <;>
    cases h4 : r.echo <;>
    simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset, suppressSigTerminal,
      suppressSigEcho, suppressSigFinish, clearCmp, wp, h1, h2, h3, h4, fst_ite, snd_ite]

end CoreStages

/-! ### Lifts and small AuthF cell maps

Small maps are handled by splitting every `if`/`match` and closing each leaf,
which is a record update of the input cell (or a core function with a frame
lemma above). -/

/-- Close a leaf goal of a frame lemma. -/
syntax "wclose" : tactic
macro_rules
  | `(tactic| wclose) => `(tactic| first
      | exact ⟨rfl, rfl⟩
      | rfl
      | (simp only [aw, AuthState.withCore, AuthState.dropP2, AuthState.setState,
          AuthState.lineage, clearCmpAuth, genConnect_wp, control_wp, checkReady_wp,
          checkL_wp, checkR_wp, result_wp, landBackward_wp, and_self, and_true, true_and];
         first | done | rfl | exact ⟨rfl, rfl⟩))

/-- Split every `if`/`match` (zeta-reducing `let`s first) and close all leaves. -/
syntax "wsplit" : tactic
macro_rules
  | `(tactic| wsplit) => `(tactic| ((repeat' (first | (dsimp only) | split)) <;> wclose))

section AuthCells
variable {ψ : Nat}

theorem wp_core (u : AuthState ψ) : wp u.core = aw u := rfl
theorem wp_p4 (u : AgentState ψ) : wp { u with path4 := none } = wp u := rfl
theorem wp_p5 (u : AgentState ψ) : wp { u with path5 := none } = wp u := rfl
theorem aw_mk (c : AgentState ψ) (a b : ProvColor) (s : P2Scope) (d e f : ProvColor) :
    aw (AuthState.mk c a b s d e f) = wp c := rfl
theorem lift2_aw (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, wp (f a b).1 = wp a ∧ wp (f a b).2 = wp b) (l r : AuthState ψ) :
    aw (lift2 f l r).1 = aw l ∧ aw (lift2 f l r).2 = aw r :=
  hf l.core r.core

theorem lift2Life_aw (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, wp (f a b).1 = wp a ∧ wp (f a b).2 = wp b) (l r : AuthState ψ) :
    aw (lift2Life f l r).1 = aw l ∧ aw (lift2Life f l r).2 = aw r := by
  have h := hf l.core r.core
  unfold lift2Life
  dsimp only
  refine ⟨?_, ?_⟩ <;> split
  all_goals first | exact h.1 | exact h.2

theorem liftLife_aw (f : AgentState ψ → AgentState ψ) (hf : ∀ a, wp (f a) = wp a)
    (u : AuthState ψ) : aw (liftLife f u) = aw u := by
  unfold liftLife
  dsimp only
  split <;> exact hf u.core

theorem clearAuth_aw (u : AuthState ψ) : aw (clearCmpAuth u) = aw u := rfl
theorem dropP2_aw (u : AuthState ψ) : aw u.dropP2 = aw u := rfl
theorem setState_aw (u : AuthState ψ) (s : MainState) : aw (u.setState s) = aw u := rfl
theorem lineage_aw (u : AuthState ψ) (s : MainState) : aw (u.lineage s) = aw u := rfl
theorem withCore_aw (u : AuthState ψ) (c : AgentState ψ) : aw (u.withCore c) = wp c := rfl
theorem wipe_aw (γ : ProvColor) (u : AuthState ψ) : aw (wipeProduceAuth γ u) = aw u := rfl
theorem demote_aw (u : AuthState ψ) : aw (demote u) = aw u := rfl
theorem claimA2_aw (σ : ProvColor) (u : AuthState ψ) : aw (claimA2 σ u) = aw u := rfl

theorem receive_aw (e : Entry) (src dst : AuthState ψ) (t : Path2Info) :
    aw (receive e src dst t) = aw dst := by
  show wp (if e = .claim then claimA2 src.path2_mark dst else dst).core = wp dst.core
  split <;> rfl

theorem sanitize_aw (u : AuthState ψ) : aw (sanitizeP2 u) = aw u := by
  unfold sanitizeP2; wsplit

theorem issue_aw (u : AuthState ψ) : aw (issue u) = aw u := by
  unfold issue; wsplit

theorem readyAuth_aw (u : AuthState ψ) : aw (readyAuth u) = aw u := by
  unfold readyAuth; wsplit

theorem applyControl_aw (hψ : ψ > 0) (u : AuthState ψ) : aw (applyControlAuth hψ u) = aw u := by
  unfold applyControlAuth; wsplit

theorem genConnectAuth_aw (u : AuthState ψ) : aw (genConnectAuth u) = aw u := by
  unfold genConnectAuth; wsplit

theorem landBackwardAuth_aw (u : AuthState ψ) : aw (landBackwardAuth u) = aw u := by
  unfold landBackwardAuth; wsplit


theorem landForwardAuth_aw (κ : Nat) (u : AuthState ψ) : aw (landForwardAuth κ u) = aw u := by
  unfold landForwardAuth
  repeat' (first | (dsimp only) | split)
  all_goals first | rfl | exact landForward_wp κ u.core

theorem cleanApplyAuth_aw (u : AuthState ψ) : aw (cleanApplyAuth u) = aw u := by
  unfold cleanApplyAuth; wsplit

end AuthCells

/-! ### The AuthF comparison prefix, stage by stage -/

section AuthStages
variable {ψ : Nat}

/- GENSIG after the WAIT lift, one stage per definition (LP-0157).  Splitting
every `if` of the composed stage at once duplicates the later stages in each
branch (46 s); each stage below is one `if` around record updates that keep
the writer projection. -/
private def gsHead (hψ : ψ > 0) (l r : AuthState ψ) : AuthState ψ :=
  if l.core.leader = false ∧ l.core.label = ⟨0, hψ⟩ ∧ l.core.wait = false ∧
      l.core.path = .bot then
    wipeProduceAuth (if l.st = .produce then l.ctrl_mark else fresh3 l.path_mark r.path_mark) l
  else l

private def gsWave (hψ : ψ > 0) (l r : AuthState ψ) : AuthState ψ :=
  if r.core.label ≠ ⟨0, hψ⟩ ∧ l.st = .produce ∧
      (r.core.path = .bot ∨ (r.st ≠ .produce ∧ r.st ≠ .done) ∨ r.ctrl_mark ≠ l.ctrl_mark) then
    wipeProduceAuth l.ctrl_mark r
  else r

private def gsEmit (hψ : ψ > 0) (r : AuthState ψ) : AuthState ψ :=
  if r.core.label = ⟨ψ - 1, by omega⟩ ∧ r.st = .produce then
    { r with core := { r.core with state := .done,
                                   path := .some r.core.label.val (if r.core.bit then 1 else 0) },
             path_mark := r.ctrl_mark }
  else r

private def gsBack (hψ : ψ > 0) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  if l.core.label ≠ ⟨ψ - 1, by omega⟩ ∧ l.st = .produce ∧ r.st = .done then
    ({ l with core := { l.core with state := .done,
                                    path := .some l.core.label.val (if l.core.bit then 1 else 0) },
              path_mark := r.path_mark, ctrl_mark := r.path_mark },
     r.setState .depart)
  else (l, r)

private def gsDone (hψ : ψ > 0) (l : AuthState ψ) : AuthState ψ :=
  if l.core.label = ⟨0, hψ⟩ ∧ l.st = .done then
    { l with core := { l.core with state := .depart, wait := true } }
  else l

private theorem genSigAuth_split (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) :
    genSigAuth hψ κ l r =
      (gsDone hψ (gsBack hψ (gsHead hψ (lift2 (waitSaturated hψ κ) l r).1
          (lift2 (waitSaturated hψ κ) l r).2)
        (gsEmit hψ (gsWave hψ (gsHead hψ (lift2 (waitSaturated hψ κ) l r).1
          (lift2 (waitSaturated hψ κ) l r).2) (lift2 (waitSaturated hψ κ) l r).2))).1,
       (gsBack hψ (gsHead hψ (lift2 (waitSaturated hψ κ) l r).1
          (lift2 (waitSaturated hψ κ) l r).2)
        (gsEmit hψ (gsWave hψ (gsHead hψ (lift2 (waitSaturated hψ κ) l r).1
          (lift2 (waitSaturated hψ κ) l r).2) (lift2 (waitSaturated hψ κ) l r).2))).2) := by
  unfold genSigAuth gsDone gsBack gsHead gsEmit gsWave
  dsimp only

private theorem gsHead_aw (hψ : ψ > 0) (l r : AuthState ψ) : aw (gsHead hψ l r) = aw l := by
  unfold gsHead; split <;> rfl
private theorem gsWave_aw (hψ : ψ > 0) (l r : AuthState ψ) : aw (gsWave hψ l r) = aw r := by
  unfold gsWave; split <;> rfl
private theorem gsEmit_aw (hψ : ψ > 0) (r : AuthState ψ) : aw (gsEmit hψ r) = aw r := by
  unfold gsEmit; split <;> rfl
private theorem gsBack_aw (hψ : ψ > 0) (l r : AuthState ψ) :
    aw (gsBack hψ l r).1 = aw l ∧ aw (gsBack hψ l r).2 = aw r := by
  unfold gsBack; split <;> exact ⟨rfl, rfl⟩
private theorem gsDone_aw (hψ : ψ > 0) (l : AuthState ψ) : aw (gsDone hψ l) = aw l := by
  unfold gsDone; split <;> rfl

theorem genSig_aw (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) :
    aw (genSigAuth hψ κ l r).1 = aw l ∧ aw (genSigAuth hψ κ l r).2 = aw r := by
  have hw := lift2_aw (waitSaturated hψ κ) (wait_wp hψ κ) l r
  rw [genSigAuth_split]
  generalize lift2 (waitSaturated hψ κ) l r = q at hw ⊢
  have h1 := gsHead_aw hψ q.1 q.2
  have h2 := gsWave_aw hψ (gsHead hψ q.1 q.2) q.2
  have h3 := gsEmit_aw hψ (gsWave hψ (gsHead hψ q.1 q.2) q.2)
  have h4 := gsBack_aw hψ (gsHead hψ q.1 q.2) (gsEmit hψ (gsWave hψ (gsHead hψ q.1 q.2) q.2))
  exact ⟨(gsDone_aw hψ _).trans (h4.1.trans (h1.trans hw.1)),
    h4.2.trans (h3.trans (h2.trans hw.2))⟩

theorem step3_aw (nbr mc : Bool) (l r : AuthState ψ) :
    aw (step3Auth nbr mc l r).1 = aw l ∧ aw (step3Auth nbr mc l r).2 = aw r := by
  unfold step3Auth; wsplit

theorem step4_aw (nbr mc : Bool) (l r : AuthState ψ) :
    aw (step4Auth nbr mc l r).1 = aw l ∧ aw (step4Auth nbr mc l r).2 = aw r := by
  unfold step4Auth; wsplit

theorem step5_aw (hψ : ψ > 0) (l r : AuthState ψ) :
    aw (step5Auth hψ l r).1 = aw l ∧ aw (step5Auth hψ l r).2 = aw r := by
  unfold step5Auth; wsplit

theorem step6_aw (hψ : ψ > 0) (l r : AuthState ψ) :
    aw (step6Auth hψ l r).1 = aw l ∧ aw (step6Auth hψ l r).2 = aw r := by
  unfold step6Auth; wsplit

/-- The simp set that rewrites a composite AuthF stage down to its input view. -/
theorem cleanSource_aw (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    aw (cleanSourceAuth hψ c l r).1 = aw l ∧ aw (cleanSourceAuth hψ c l r).2 = aw r := by
  simp only [cleanSourceAuth, fst_ite, snd_ite, aw_ite, aw_mk, wp_p4, wp_p5, wp_core, cleanApplyAuth_aw,
    step6_aw, step5_aw, step4_aw, step3_aw, genConnectAuth_aw, ite_self, and_self]

theorem validate_aw (l r : AuthState ψ) :
    aw (validateCheck l r).1 = aw l ∧ aw (validateCheck l r).2 = aw r := by
  unfold validateCheck; wsplit

theorem step1_aw (l r : AuthState ψ) :
    aw (step1Auth l r).1 = aw l ∧ aw (step1Auth l r).2 = aw r := by
  unfold step1Auth; wsplit

private theorem wf_fst_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem wf_snd_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl

/- Closure facts for `aw v = aw u`: the token move is built from `if`,
`dropP2`, `receive` and `clearCmpAuth` around its inputs, so the frame
follows constructor by constructor instead of from a joint case split. -/
private theorem AW_ite {u a b : AuthState ψ} {p : Prop} [Decidable p]
    (ha : aw a = aw u) (hb : aw b = aw u) : aw (if p then a else b) = aw u := by
  split
  · exact ha
  · exact hb
private theorem AW_dropP2 {u v : AuthState ψ} (h : aw v = aw u) : aw v.dropP2 = aw u := h
private theorem AW_receive {u v : AuthState ψ} (e : Entry) (src : AuthState ψ) (t : Path2Info)
    (h : aw v = aw u) : aw (receive e src v t) = aw u := (receive_aw e src v t).trans h
private theorem AW_clear (u : AuthState ψ) : aw (clearCmpAuth u) = aw u := rfl
private theorem AW_refl (u : AuthState ψ) : aw u = aw u := rfl

theorem moveTokens_aw (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    aw (moveTokensAuth c l r).1 = aw l ∧ aw (moveTokensAuth c l r).2 = aw r := by
  unfold moveTokensAuth
  simp only [wf_fst_ite, wf_snd_ite]
  constructor
  all_goals
    repeat (first
      | with_reducible exact AW_refl _
      | with_reducible exact AW_clear _
      | with_reducible refine AW_receive _ _ _ ?_
      | with_reducible refine AW_dropP2 ?_
      | with_reducible refine AW_ite ?_ ?_
      | (simp only [wf_fst_ite, wf_snd_ite])
      | split)

theorem leaderWall_aw (l r : AuthState ψ) :
    aw (leaderWallAuth l r).1 = aw l ∧ aw (leaderWallAuth l r).2 = aw r := by
  unfold leaderWallAuth; wsplit

theorem moveSource_aw (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    aw (moveSourceAuth hψ c l r).1 = aw l ∧ aw (moveSourceAuth hψ c l r).2 = aw r := by
  simp only [moveSourceAuth, fst_ite, snd_ite, aw_ite, lineage_aw, applyControl_aw,
    leaderWall_aw, moveTokens_aw, step1_aw, sanitize_aw, validate_aw, clearAuth_aw,
    ite_self, and_self]

theorem preCheck_aw (l r : AuthState ψ) :
    aw (preCheckResetAuth l r).1 = aw l ∧ aw (preCheckResetAuth l r).2 = aw r := by
  unfold preCheckResetAuth; wsplit

theorem disappear_aw (hψ : ψ > 0) (l r : AuthState ψ) :
    aw (disappearAuth hψ l r).1 = aw l ∧ aw (disappearAuth hψ l r).2 = aw r := by
  have h1 := lift2_aw (disappearStartL hψ) (disStart_wp hψ)
  have h2 := lift2_aw (disappearCarry hψ) (disCarry_wp hψ)
  unfold disappearAuth
  dsimp only
  split <;> simp only [h2, h1, true_and, and_self]
  all_goals wclose

theorem repair_aw (l r : AuthState ψ) :
    aw (repairAuth l r).1 = aw l ∧ aw (repairAuth l r).2 = aw r := by
  have hc : ∀ a : AgentState ψ, wp (normalizeCarrier (normalizeOrphan a)) = wp a :=
    fun a => (carrier_wp _).trans (orphan_wp a)
  have hl := liftLife_aw _ hc
  have hr := lift2Life_aw (ψ := ψ) releaseReadySuffix releaseSuffix_wp
  have ha : ∀ a b : AuthState ψ, aw (ackTailAuth a b).1 = aw a ∧ aw (ackTailAuth a b).2 = aw b := by
    intro a b
    unfold ackTailAuth; split
    · exact lift2_aw ackTail ackTail_wp a b
    · exact ⟨rfl, rfl⟩
  simp only [repairAuth, ha, hr, hl, and_self]

theorem maintain_aw (l r : AuthState ψ) :
    aw (maintainAuth l r).1 = aw l ∧ aw (maintainAuth l r).2 = aw r := by
  unfold maintainAuth; wsplit

theorem completeWave_aw (l r : AuthState ψ) :
    aw (completeWaveAuth l r).1 = aw l ∧ aw (completeWaveAuth l r).2 = aw r := by
  unfold completeWaveAuth; wsplit

theorem wave_aw (l r : AuthState ψ) :
    aw (waveAuth l r).1 = aw l ∧ aw (waveAuth l r).2 = aw r := by
  unfold waveAuth; wsplit


/-- CHECK preserves the writer projection on both endpoints; its terminal
birth writes only `leader`. -/
theorem checkSource_aw (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    aw (checkSourceAuth hψ c l r).1 = aw l ∧ aw (checkSourceAuth hψ c l r).2 = aw r := by
  have hb : ∀ (C : Prop) [Decidable C] (B : AuthState ψ),
      aw (if C then { B with core := { B.core with leader := true } } else B) = aw B := by
    intro C _ B; split <;> rfl
  simp only [checkSourceAuth, fst_ite, snd_ite, hb, aw_ite, aw_mk, wp_core, withCore_aw,
    lineage_aw, issue_aw, readyAuth_aw, checkL_wp, checkR_wp, checkReady_wp, validate_aw,
    ite_self, and_self]

/-- The comparison lifecycle preserves the writer projection on both endpoints;
the BEQ birth in `landForward` writes only `leader` and `path2`. -/
theorem compare_aw (κ : Nat) (l r : AuthState ψ) :
    aw (compareLifecycleAuth κ l r).1 = aw l ∧ aw (compareLifecycleAuth κ l r).2 = aw r := by
  have hd := lift2_aw (ψ := ψ) dropStray dropStray_wp
  unfold compareLifecycleAuth
  dsimp only
  split
  all_goals (try split)
  all_goals simp only [landBackwardAuth_aw, landForwardAuth_aw, hd, wave_aw, completeWave_aw,
    maintain_aw, setState_aw, and_self]

end AuthStages

theorem mid_aw {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    aw (mid hψ κ c l r).1 = aw l ∧ aw (mid hψ κ c l r).2 = aw r := by
  simp only [mid]
  have h1 := genSig_aw hψ κ l r
  generalize genSigAuth hψ κ l r = q1 at h1
  obtain ⟨a1, b1⟩ := q1
  simp only at h1 ⊢
  have h2 := cleanSource_aw hψ c a1 b1
  generalize cleanSourceAuth hψ c a1 b1 = q2 at h2
  obtain ⟨a2, b2⟩ := q2
  simp only at h2 ⊢
  have h3 := lift2Life_aw (releaseSource hψ) (releaseSource_wp hψ) a2 b2
  generalize lift2Life (releaseSource hψ) a2 b2 = q3 at h3
  obtain ⟨a3, b3⟩ := q3
  simp only at h3 ⊢
  have h4 := lift2_aw (eliminateSig hψ) (eliminate_wp hψ) a3 b3
  generalize lift2 (eliminateSig hψ) a3 b3 = q4 at h4
  obtain ⟨a4, b4⟩ := q4
  simp only at h4 ⊢
  have h5 := moveSource_aw hψ c a4 b4
  generalize moveSourceAuth hψ c a4 b4 = q5 at h5
  obtain ⟨a5, b5⟩ := q5
  simp only at h5 ⊢
  have h6 := preCheck_aw (liftLife dropStale a5) (liftLife dropStale b5)
  rw [liftLife_aw _ dropStale_wp, liftLife_aw _ dropStale_wp] at h6
  generalize preCheckResetAuth (liftLife dropStale a5) (liftLife dropStale b5) = q6 at h6
  obtain ⟨a6, b6⟩ := q6
  simp only at h6 ⊢
  have e7 := liftLife_aw _ ready_wp a6
  have f7 := liftLife_aw _ ready_wp b6
  generalize liftLife normalizeReady a6 = a7 at e7
  generalize liftLife normalizeReady b6 = b7 at f7
  have h8 := checkSource_aw hψ c a7 b7
  generalize checkSourceAuth hψ c a7 b7 = q8 at h8
  obtain ⟨a8, b8⟩ := q8
  simp only at h8 ⊢
  have h9 := disappear_aw hψ a8 b8
  generalize disappearAuth hψ a8 b8 = q9 at h9
  obtain ⟨a9, b9⟩ := q9
  simp only at h9 ⊢
  have h10 := repair_aw a9 b9
  generalize repairAuth a9 b9 = q10 at h10
  obtain ⟨a10, b10⟩ := q10
  simp only at h10 ⊢
  have h11 := compare_aw κ a10 b10
  generalize compareLifecycleAuth κ a10 b10 = q11 at h11
  obtain ⟨a11, b11⟩ := q11
  simp only at h11 ⊢
  exact ⟨by rw [h11.1, h10.1, h9.1, h8.1, e7, h6.1, h5.1, h4.1, h3.1, h2.1, h1.1],
    by rw [h11.2, h10.2, h9.2, h8.2, f7, h6.2, h5.2, h4.2, h3.2, h2.2, h1.2]⟩


/-- Algorithm 14 keeps the initiator's label and leader bit. -/
theorem suppress_left {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    (suppressSigResetKill hψ l r).1.label = l.label ∧
    (suppressSigResetKill hψ l r).1.leader = l.leader := by
  simp only [suppressSigResetKill, suppressSigStart, suppressSigMoveReset, suppressSigTerminal,
    suppressSigEcho, suppressSigFinish, clearCmp]
  simp only [fst_ite, snd_ite, label_ite, leader_ite, ite_self, and_self]

/-- **AuthF prefix writer frame.** For every `Cfg` and all inputs, the pair that
`PPLLAuthF.pipeline` hands to `k4Kernel` carries the writer projection of the
original endpoints. -/
theorem prefix_writer {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    wp (PPLLAuthF.beforeElimination hp κ c l r).1.core = wp l.core ∧
    wp (PPLLAuthF.beforeElimination hp κ c l r).2.core = wp r.core := by
  rw [beforeElimination_eq, (suppress_core hp _ _).1, (suppress_core hp _ _).2,
    (suppress_wp hp _ _).1, (suppress_wp hp _ _).2]
  have hm := mid_aw hp κ c (lift2 (pPsiProbeWall hp) l r).1 (lift2 (pPsiProbeWall hp) l r).2
  have hq := pPsi_wp hp l.core r.core
  have e1 : aw (lift2 (pPsiProbeWall hp) l r).1 = wp l.core := hq.1
  have e2 : aw (lift2 (pPsiProbeWall hp) l r).2 = wp r.core := hq.2
  have f1 : aw (beforeSuppressAuth hp κ c l r).1 = wp l.core := hm.1.trans e1
  have f2 : aw (beforeSuppressAuth hp κ c l r).2 = wp r.core := hm.2.trans e2
  exact ⟨f1, f2⟩

private theorem av_label {ψ : Nat} (u : AuthState ψ) : (av u).2.2.1 = u.core.label := rfl

private theorem lift2_fst_core {ψ : Nat}
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ) (l r : AuthState ψ) :
    (lift2 f l r).1.core = (f l.core r.core).1 := rfl

/-- The remaining fields `writeSeq` reads, on a leaderless interaction: the
initiator keeps label and (false) leader bit; the responder carries P′'s label,
which on a successor-aligned pair is its own label. -/
theorem prefix_writer_inputs {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hnext : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hp⟩) :
    (PPLLAuthF.beforeElimination hp κ c l r).1.core.label = l.core.label ∧
    (PPLLAuthF.beforeElimination hp κ c l r).1.core.leader = false ∧
    (PPLLAuthF.beforeElimination hp κ c l r).2.core.label = r.core.label := by
  have hpf := prefix_facts hp κ c l r
  dsimp only at hpf
  obtain ⟨_, _, _, _, b5, b6, _⟩ := hpf
  have hm := mid_FR hp κ c (lift2 (pPsiProbeWall hp) l r).1 (lift2 (pPsiProbeWall hp) l r).2
  have hm0 : av (beforeSuppressAuth hp κ c l r).1 = av (lift2 (pPsiProbeWall hp) l r).1 := hm.1
  -- Read the label through named one-step facts: checking `congrArg _ hm0`
  -- directly against the label equation is a definitional-unfolding search
  -- through the prefix (LP-0157).
  have hm1 : (beforeSuppressAuth hp κ c l r).1.core.label =
      (pPsiProbeWall hp l.core r.core).1.label :=
    (av_label _).symm.trans ((congrArg (fun x => x.2.2.1) hm0).trans
      ((av_label _).trans (congrArg AgentState.label (lift2_fst_core _ l r))))
  have hpl : (pPsiProbeWall hp l.core r.core).1.label = l.core.label := by
    simp only [pPsiProbeWall, pPsi]
    simp [fst_ite, label_ite]
  have hpr : (pPsiProbeWall hp l.core r.core).2.label = r.core.label := by
    simp [pPsiProbeWall, pPsi, hl, hr, hnext]
  have hs := suppress_left hp (beforeSuppressAuth hp κ c l r).1.core
    (beforeSuppressAuth hp κ c l r).2.core
  rw [beforeElimination_eq, (suppress_core hp _ _).1, (suppress_core hp _ _).2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs.1]; exact hm1.trans hpl
  · rw [hs.2, b5, hl]
  · rw [suppress_label hp _ _ (b5.trans hl), b6, hpr]

/-- K4 writes no writer field. -/
theorem kernel_wp {ψ : Nat} (hp : ψ > 0) (l r : AgentState ψ) :
    wp (k4Kernel hp l r).1 = wp l ∧ wp (k4Kernel hp l r).2 = wp r := by
  simp only [k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire, absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp [fst_ite, snd_ite, wp_ite, wp, bit_ite, path3_ite, write_ite, wst_ite, genws_ite, wsecho_ite, sigws_ite, last_ite, lastset_ite, lastunset_ite, bcarry_ite]

/-- **Composition.** On an interaction with two follower inputs, the AuthF
transition is exactly `writeWithBundle` applied to the K4 output of the prefix
pair (`conserveAuth` cannot fire), and the pair entering `writeWithBundle`
carries the writer projection of the original endpoints. Together with
`prefix_writer_inputs` (labels, initiator leader) every field `writeSeq` reads
is the original one, except the responder leader bit, which the stage-2
statement assumes false (`(beforeElimination …).2.core.leader = false`). -/
theorem pipeline_writer_compose {ψ : Nat} (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) (hl : l.core.leader = false) (hr : r.core.leader = false) :
    let E := PPLLAuthF.beforeElimination hp κ c l r
    let K := k4Kernel hp E.1.core E.2.core
    (PPLLAuthF.pipeline hp κ c l r).1.core = (writeWithBundle hp K.1 K.2).1 ∧
    (PPLLAuthF.pipeline hp κ c l r).2.core = (writeWithBundle hp K.1 K.2).2 ∧
    wp K.1 = wp l.core ∧ wp K.2 = wp r.core := by
  intro E K
  have hc := pipeline_core hp κ c l r
  have hw := prefix_writer hp κ c l r
  have hk := kernel_wp hp E.1.core E.2.core
  refine ⟨?_, ?_, hk.1.trans hw.1, hk.2.trans hw.2⟩
  · rw [hc.1]; simp [conserve, hl, hr]; rfl
  · rw [hc.2]; simp [conserve, hl, hr]; rfl

#print axioms prefix_writer
#print axioms prefix_writer_inputs
#print axioms kernel_wp
#print axioms pipeline_writer_compose

end PPLLAuthWriterFrame

