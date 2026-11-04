import Leader.Wu.Authorization.WriterFrame
/-! One-step closure of `LeaderlessBitFrozen` for AuthF (Z-div liveness, stage 2).

On a leaderless perfectly labelled ring with `ψ ∣ n` we define

* `TerminalSafe_g`: the terminal `T_g` of group `g` has no `path3`, or its
  `path3 = some p` has `target p = (p.bit = 1)` equal to the physical bit;
* `HeadOW_g`: the head `H_g` holds `path3 = some p` with `p.label = 0`,
  `p.flag = 1`, `bit = true`, `p.bit = 0`;
* `PendingOW_g`: some cell of group `g` has `write = overwrite`;
* `NoInc`: no cell has `write = increment_group` or `write_state = increment_group`;
* `LeaderlessBitFrozen := NoInc ∧ ∀ g, TerminalSafe_g ∨ (¬HeadOW_g ∧ ¬PendingOW_g)`.

`LBF` below is this predicate with the indexing of the reference Bool
definition `leaderlessBitFrozen` (`Leader/Wu/Sim/AuthWriterNormalisation.lean`): group `g`
is the cells `gψ … gψ+ψ-1`, head `gψ`, terminal `gψ+ψ-1`. Groups are indexed
here by their terminal `t` (`t % ψ = ψ-1`); the head is the cell `h` with
`h + (ψ-1) = t`, and the group is `{j | j / ψ = t / ψ}`.

## Result

`step_closed`: on a leaderless configuration with perfect labels satisfying
`LBF`, for every edge `e` whose served interaction leaves both output cores
followers, the successor configuration has the same bit vector, perfect
labels and `LBF` again. Hypotheses beyond the controller's list: `2 ≤ ψ`
(`ψ ≥ 2` is an ambient assumption; for `ψ = 1` head and terminal
coincide) and `1 < n`. `inProtocolDomain` is not needed: `checkBitWS` returns
`larger` only for `bit = true, p.bit = 0`, and the overwrite target is
`p.bit == 1` literally. No condition was added to `LBF`: `NoInc` (already part
of it) is what kills Algorithm 19's `depart` source, so the `path3` transfer
of `moveWsigTransfer` never fires on these rows.

## Proof

By `PPLLAuthWriterFrame.pipeline_writer_compose` the served pair is
`writeWithBundle` (= `writeSeq`, the responder being a follower) on inputs
with the original writer projection and labels. On a leaderless `writeSeq`
with `NoInc` (`writeSeq_local`):

* LeaderMove, GENSIG_WRITESEQ are identities, GROUP_INFO writes only `last*`;
* after `writeSeqReady` the initiator is `ready`/`none`, so the second CHECK
  branch and `writeSeqFinalR` are dead; a fresh `overwrite` command arises only
  at a label-0 responder satisfying `HeadOW`;
* Algorithm 19 changes a bit only through `writeActionApplyOverwrite` at a
  terminal responder with `write = overwrite` (increment excluded by `NoInc`);
  that terminal is `TerminalSafe` by `LBF` (its group has a pending overwrite),
  so the bit is unchanged; `path3` only has its flag toggled there;
* `moveWsig` only deletes the initiator's `path3`/`write` and moves `write`
  forward inside a group; the transfer needs `write_state = depart`, which
  Algorithm 19 gives the initiator only through the excluded increment branch.

Hence `TerminalSafe` and `¬HeadOW` persist, and a new pending overwrite in
group `g` needs an old one in `g` or an old `HeadOW_g`.
-/
namespace PPLLAuthBitFrozen
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
  PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF PPLLAuthResetDrain
  PPLLAuthWriterFrame
set_option linter.unusedSimpArgs false

/-! ### Cell predicates -/

/-- `TerminalSafe` of one core. -/
abbrev TSc {ψ : Nat} (u : AgentState ψ) : Prop := ∀ p, u.path3 = some p → u.bit = (p.bit == 1)

/-- `HeadOW` of one core. -/
abbrev HOWc {ψ : Nat} (u : AgentState ψ) : Prop :=
  ∃ p, u.path3 = some p ∧ p.label = 0 ∧ p.flag = 1 ∧ u.bit = true ∧ p.bit = 0

/-- `NoInc` of one core. -/
abbrev NIc {ψ : Nat} (u : AgentState ψ) : Prop :=
  u.write ≠ .increment_group ∧ u.write_state ≠ .increment_group

/-- Frame of the writer-relevant fields. -/
abbrev Fr {ψ : Nat} (u v : AgentState ψ) : Prop :=
  v.bit = u.bit ∧ v.path3 = u.path3 ∧ v.write = u.write ∧ v.write_state = u.write_state ∧
    v.label = u.label ∧ v.leader = u.leader

/-! ### Leaderless `writeSeq`, stage by stage -/

section Local
variable {ψ : Nat} (hψ : ψ > 0)

theorem leaderMove_id (l r : AgentState ψ) (hr : r.leader = false) :
    writeSeqLeaderMove hψ l r = (l, r) := by
  simp [writeSeqLeaderMove, hr]

theorem generate_id (l r : AgentState ψ) (hl : l.leader = false) :
    writeSeqGenerate hψ l r = (l, r) := by
  simp [writeSeqGenerate, hl]

/-- Close a `Fr`/`Fr` goal on untouched writer fields. -/
syntax "frfl" : tactic
macro_rules
  | `(tactic| frfl) =>
    `(tactic| exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩)

theorem groupInfo_frame (l r : AgentState ψ) :
    Fr l (groupInfo hψ l r).1 ∧ Fr r (groupInfo hψ l r).2 := by
  rw [groupInfo_eq_staged]
  unfold groupInfoStaged
  have h1 : Fr l (groupInfoStart hψ l r).1 ∧ Fr r (groupInfoStart hψ l r).2 := by
    unfold groupInfoStart
    repeat' (first | (dsimp only) | split)
    all_goals frfl
  generalize groupInfoStart hψ l r = q at h1 ⊢
  obtain ⟨l1, r1⟩ := q
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩⟩ := h1
  dsimp only at a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 ⊢
  have h2 : Fr l1 (groupInfoSet hψ l1 r1).1 ∧ Fr r1 (groupInfoSet hψ l1 r1).2 := by
    unfold groupInfoSet
    repeat' (first | (dsimp only) | split)
    all_goals frfl
  generalize groupInfoSet hψ l1 r1 = q at h2 ⊢
  obtain ⟨l2, r2⟩ := q
  obtain ⟨⟨c1, c2, c3, c4, c5, c6⟩, ⟨d1, d2, d3, d4, d5, d6⟩⟩ := h2
  dsimp only at c1 c2 c3 c4 c5 c6 d1 d2 d3 d4 d5 d6 ⊢
  have h3 : Fr l2 (groupInfoUnset l2 r2).1 ∧ Fr r2 (groupInfoUnset l2 r2).2 := by
    unfold groupInfoUnset
    repeat' (first | (dsimp only) | split)
    all_goals frfl
  obtain ⟨⟨e1, e2, e3, e4, e5, e6⟩, ⟨f1, f2, f3, f4, f5, f6⟩⟩ := h3
  exact ⟨⟨e1.trans (c1.trans a1), e2.trans (c2.trans a2), e3.trans (c3.trans a3),
      e4.trans (c4.trans a4), e5.trans (c5.trans a5), e6.trans (c6.trans a6)⟩,
    ⟨f1.trans (d1.trans b1), f2.trans (d2.trans b2), f3.trans (d3.trans b3),
      f4.trans (d4.trans b4), f5.trans (d5.trans b5), f6.trans (d6.trans b6)⟩⟩

/-! #### CHECK (Algorithm 16 lines 5–12) -/

theorem checkBitWS_cases (b : Bool) (pb : Nat) :
    checkBitWS b pb = .equal ∨ checkBitWS b pb = .less ∨
      (checkBitWS b pb = .larger ∧ b = true ∧ pb = 0) := by
  unfold checkBitWS
  dsimp only
  by_cases h1 : (if b = true then 1 else 0) = pb
  · left; rw [if_pos h1]
  · right
    rw [if_neg h1]
    by_cases h3 : (if b = true then 1 else 0) > pb
    · right
      rw [if_pos h3]
      refine ⟨rfl, ?_⟩
      cases b
      · exact absurd h3 (Nat.not_lt_zero _)
      · have : pb < 1 := h3
        exact ⟨rfl, by omega⟩
    · left; rw [if_neg h3]

theorem ready_facts (u : AgentState ψ) :
    (writeSeqSetWriteReady u).bit = u.bit ∧ (writeSeqSetWriteReady u).path3 = u.path3 ∧
    (writeSeqSetWriteReady u).label = u.label ∧ (writeSeqSetWriteReady u).leader = u.leader ∧
    (writeSeqSetWriteReady u).write = u.write ∧
    ((writeSeqSetWriteReady u).write_state = .ready ∨
      (writeSeqSetWriteReady u).write_state = .none) ∧
    ((writeSeqSetWriteReady u).write_state = .ready →
      ∃ p, u.path3 = some p ∧ u.label.val = p.label) := by
  unfold writeSeqSetWriteReady
  split
  · next p hp =>
    split
    · next hc => exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl, fun _ => ⟨p, hp, hc.1⟩⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr rfl, fun h => by simp at h⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr rfl, fun h => by simp at h⟩

/-- The five possible write states after the comparison. -/
abbrev WS5 (w : WriteState) : Prop :=
  w = .ready ∨ w = .none ∨ w = .equal ∨ w = .less ∨ w = .larger

theorem compare_facts (l r : AgentState ψ)
    (hl : l.write_state = .ready ∨ l.write_state = .none)
    (hr : r.write_state = .ready ∨ r.write_state = .none) :
    (writeSeqCompare hψ l r).1 = l ∧
    (writeSeqCompare hψ l r).2.bit = r.bit ∧ (writeSeqCompare hψ l r).2.path3 = r.path3 ∧
    (writeSeqCompare hψ l r).2.label = r.label ∧ (writeSeqCompare hψ l r).2.leader = r.leader ∧
    (writeSeqCompare hψ l r).2.write = r.write ∧
    WS5 (writeSeqCompare hψ l r).2.write_state ∧
    ((writeSeqCompare hψ l r).2.write_state = .larger →
      r.label.val = 0 ∧ r.write_state = .ready ∧
        ∃ p, r.path3 = some p ∧ r.bit = true ∧ p.bit = 0) ∧
    (r.label.val ≠ 0 → (writeSeqCompare hψ l r).2.write_state = r.write_state) := by
  have hne : l.write_state ≠ .equal := by rcases hl with h | h <;> rw [h] <;> simp
  unfold writeSeqCompare writeSeqCheckBit
  dsimp only
  simp only [hne, false_and, and_false, ↓reduceIte]
  rcases hr with hr | hr
  all_goals
    split
    · next hc =>
      split
      · next p hp =>
        rcases checkBitWS_cases r.bit p.bit with h | h | ⟨h, hb, hpb⟩ <;> simp_all [WS5]
      · simp_all [WS5]
    · next hc => simp_all [WS5]

theorem act_facts (u : AgentState ψ) :
    (writeSeqSetWriteAct u).bit = u.bit ∧ (writeSeqSetWriteAct u).path3 = u.path3 ∧
    (writeSeqSetWriteAct u).label = u.label ∧ (writeSeqSetWriteAct u).leader = u.leader ∧
    (writeSeqSetWriteAct u).write_state = u.write_state ∧
    (u.write_state ≠ .larger → u.write_state ≠ .less → (writeSeqSetWriteAct u).write = u.write) ∧
    ((writeSeqSetWriteAct u).write = .overwrite → u.write = .overwrite ∨
      (u.write_state = .larger ∧ ∃ p, u.path3 = some p ∧ p.flag = 1)) ∧
    (u.write ≠ .increment_group → (writeSeqSetWriteAct u).write ≠ .increment_group) := by
  unfold writeSeqSetWriteAct
  dsimp only
  by_cases h1 : u.write_state = .larger <;> by_cases h2 : u.write_state = .less <;>
    simp only [h1, h2, ↓reduceIte] <;> (repeat' split) <;> simp_all

/-- Command preparation on a leaderless pair (`ψ ≥ 2`). -/
theorem prepare_facts (h2 : 2 ≤ ψ) (l r : AgentState ψ) :
    let q := writeSeqPrepare hψ l r
    (q.1.bit = l.bit ∧ q.1.path3 = l.path3 ∧ q.1.label = l.label ∧ q.1.leader = l.leader ∧
      q.1.write = l.write ∧ (q.1.write_state = .ready ∨ q.1.write_state = .none)) ∧
    (q.2.bit = r.bit ∧ q.2.path3 = r.path3 ∧ q.2.label = r.label ∧ q.2.leader = r.leader ∧
      q.2.write_state ≠ .depart ∧ q.2.write_state ≠ .overwrite ∧
      q.2.write_state ≠ .move_flip ∧ q.2.write_state ≠ .increment_group ∧
      (r.write ≠ .increment_group → q.2.write ≠ .increment_group) ∧
      (q.2.write = .overwrite → r.write = .overwrite ∨ (r.label.val = 0 ∧ HOWc r)) ∧
      (r.label.val ≠ 0 → q.2.write = r.write)) := by
  dsimp only
  unfold writeSeqPrepare writeSeqReady writeSeqCommands
  dsimp only
  obtain ⟨a1, a2, a3, a4, a5, a6, _⟩ := ready_facts l
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := ready_facts r
  have hc := compare_facts hψ (writeSeqSetWriteReady l) (writeSeqSetWriteReady r) a6 b6
  generalize writeSeqSetWriteReady l = l1 at a1 a2 a3 a4 a5 a6 hc ⊢
  generalize writeSeqSetWriteReady r = r1 at b1 b2 b3 b4 b5 b6 b7 hc ⊢
  generalize writeSeqCompare hψ l1 r1 = cq at hc ⊢
  obtain ⟨l2, r2⟩ := cq
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hc
  dsimp only at c1 c2 c3 c4 c5 c6 c7 c8 c9 ⊢
  subst l2
  obtain ⟨x1, x2, x3, x4, x5, x6, _, _⟩ := act_facts l1
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8⟩ := act_facts r2
  generalize writeSeqSetWriteAct l1 = l3 at x1 x2 x3 x4 x5 x6 ⊢
  generalize writeSeqSetWriteAct r2 = r3 at y1 y2 y3 y4 y5 y6 y7 y8 ⊢
  have hnf : ¬ (r3.label = ⟨ψ - 1, by omega⟩ ∧ r3.write_state = .equal) := by
    rintro ⟨hl3, he⟩
    have hv : r.label.val = ψ - 1 := by rw [← b3, ← c4, ← y3, hl3]
    rw [y5] at he
    have := c9 (by rw [b3, hv]; omega)
    rw [this] at he
    rcases b6 with h | h <;> rw [h] at he <;> cases he
  rw [if_neg hnf]
  try dsimp only
  have hl1 : l1.write_state ≠ .larger ∧ l1.write_state ≠ .less := by
    rcases a6 with h | h <;> rw [h] <;> simp
  have hr2 : r2.write_state ≠ .depart ∧ r2.write_state ≠ .overwrite ∧
      r2.write_state ≠ .move_flip ∧ r2.write_state ≠ .increment_group := by
    rcases c7 with h | h | h | h | h <;> rw [h] <;> simp
  refine ⟨⟨x1.trans a1, x2.trans a2, x3.trans a3, x4.trans a4,
      (x6 hl1.1 hl1.2).trans a5, by rw [x5]; exact a6⟩, ⟨y1.trans (c2.trans b1),
      y2.trans (c3.trans b2), y3.trans (c4.trans b3), y4.trans (c5.trans b4),
      by rw [y5]; exact hr2.1, by rw [y5]; exact hr2.2.1, by rw [y5]; exact hr2.2.2.1,
      by rw [y5]; exact hr2.2.2.2, fun h => y8 (by rw [c6, b5]; exact h), ?_, ?_⟩⟩
  · intro h
    rcases y7 h with h' | ⟨hl, p, hp, hf⟩
    · left; rw [← b5, ← c6]; exact h'
    · right
      obtain ⟨hz, hrd, p', hp', hbit, hpb⟩ := c8 hl
      obtain ⟨p'', hp'', hlab⟩ := b7 hrd
      have hrp : r.path3 = some p := by rw [← b2, ← c3]; exact hp
      have e1 : p' = p := by
        rw [c3] at hp; rw [hp] at hp'; exact (Option.some.inj hp').symm
      have e2 : p'' = p := by rw [hrp] at hp''; exact (Option.some.inj hp'').symm
      refine ⟨by rw [← b3]; exact hz, p, hrp, ?_, hf, by rw [← b1]; exact hbit,
        by rw [← e1]; exact hpb⟩
      rw [← e2]; rw [b3] at hz; omega
  · intro hz
    have hw := c9 (by rw [b3]; exact hz)
    have hn : r2.write_state ≠ .larger ∧ r2.write_state ≠ .less := by
      rw [hw]; rcases b6 with h | h <;> rw [h] <;> simp
    rw [y6 hn.1 hn.2, c6, b5]

/-! #### Algorithm 19 -/

theorem toState_ne_depart (w : WriteAction) : writeActionToState w ≠ .depart := by
  cases w <;> simp [writeActionToState]

theorem toState_ne_inc {w : WriteAction} (h : w ≠ .increment_group) :
    writeActionToState w ≠ .increment_group := by
  cases w <;> simp_all [writeActionToState]

theorem toState_overwrite {w : WriteAction} (h : writeActionToState w = .overwrite) :
    w = .overwrite := by
  cases w <;> simp_all [writeActionToState]

theorem activate_facts (u : AgentState ψ) :
    (writeActionActivate hψ u).bit = u.bit ∧ (writeActionActivate hψ u).path3 = u.path3 ∧
    (writeActionActivate hψ u).label = u.label ∧ (writeActionActivate hψ u).leader = u.leader ∧
    ((writeActionActivate hψ u).write = u.write ∨ (writeActionActivate hψ u).write = .none) ∧
    (u.label.val ≠ ψ - 1 → (writeActionActivate hψ u).write_state = u.write_state) ∧
    (u.label.val = ψ - 1 →
      (writeActionActivate hψ u).write_state = writeActionToState u.write) := by
  unfold writeActionActivate
  split
  · next h =>
    exact ⟨rfl, rfl, rfl, rfl, Or.inr rfl, fun hn => absurd (by rw [h]) hn, fun _ => rfl⟩
  · next h => exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl, fun _ => rfl, fun hv => absurd (Fin.ext hv) h⟩

/-- Algorithm 19, overwrite stage. -/
def owS (r : AgentState ψ) : AgentState ψ :=
  if r.write_state = .overwrite then writeActionApplyOverwrite r else r

/-- Algorithm 19, move-flip stage. -/
def mfS (r : AgentState ψ) : AgentState ψ :=
  if r.write_state = .move_flip then writeActionApplyMoveFlip r else r

/-- Algorithm 19, increment stage. -/
def incS (r : AgentState ψ) : AgentState ψ :=
  if r.write_state = .increment_group then
    if r.bit = true then { r with bit := false }
    else { r with bit := true, write_state := .depart }
  else r

theorem execute_eq (l r : AgentState ψ) (h : l.label < r.label ∨ r.label = ⟨0, hψ⟩) :
    writeActionExecute hψ l r =
      (if (incS (mfS (owS r))).label ≠ ⟨0, hψ⟩ then
          { l with write_state := (incS (mfS (owS r))).write_state } else l,
       { incS (mfS (owS r)) with write_state := .depart }) := by
  unfold writeActionExecute
  rw [if_pos h]
  rfl

theorem owS_facts (r : AgentState ψ)
    (hsafe : r.write_state = .overwrite → ∀ p, r.path3 = some p → r.bit = (p.bit == 1)) :
    (owS r).bit = r.bit ∧ (owS r).label = r.label ∧ (owS r).leader = r.leader ∧
    (owS r).write = r.write ∧ (owS r).write_state = r.write_state ∧
    (r.write_state ≠ .overwrite → (owS r).path3 = r.path3) ∧
    (∀ p', (owS r).path3 = some p' →
      ∃ p, r.path3 = some p ∧ p'.bit = p.bit ∧ p'.label = p.label) := by
  unfold owS writeActionApplyOverwrite
  split
  · next hw =>
    split
    · next p hp =>
      refine ⟨(hsafe hw p hp).symm, rfl, rfl, rfl, rfl, fun h => absurd hw h, ?_⟩
      intro p' hp'
      simp only [Option.some.injEq] at hp'
      subst hp'
      exact ⟨p, hp, rfl, rfl⟩
    · next hp =>
      refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, ?_⟩
      intro p' hp'; rw [hp] at hp'; cases hp'
  · refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, ?_⟩
    intro p' hp'; exact ⟨p', hp', rfl, rfl⟩

theorem mfS_facts (r : AgentState ψ) :
    (mfS r).bit = r.bit ∧ (mfS r).label = r.label ∧ (mfS r).leader = r.leader ∧
    (mfS r).write = r.write ∧ (mfS r).write_state = r.write_state ∧
    (r.write_state ≠ .move_flip → (mfS r).path3 = r.path3) ∧
    (∀ p', (mfS r).path3 = some p' →
      ∃ p, r.path3 = some p ∧ p'.bit = p.bit ∧ p'.label = p.label) := by
  unfold mfS writeActionApplyMoveFlip
  split
  · next hw =>
    split
    · next p hp =>
      refine ⟨rfl, rfl, rfl, rfl, rfl, fun h => absurd hw h, ?_⟩
      intro p' hp'
      simp only [Option.some.injEq] at hp'
      subst hp'
      exact ⟨p, hp, rfl, rfl⟩
    · next hp =>
      refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, ?_⟩
      intro p' hp'; rw [hp] at hp'; cases hp'
  · refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, ?_⟩
    intro p' hp'; exact ⟨p', hp', rfl, rfl⟩

theorem incS_id (r : AgentState ψ) (h : r.write_state ≠ .increment_group) : incS r = r := by
  unfold incS; rw [if_neg h]

/-- Algorithm 19 on a prepared leaderless pair of consecutive labels. -/
theorem action_facts (h2 : 2 ≤ ψ) (l r : AgentState ψ)
    (hlr : l.label < r.label ∨ r.label = ⟨0, hψ⟩)
    (hlws : l.write_state = .ready ∨ l.write_state = .none)
    (hrws : r.write_state ≠ .depart ∧ r.write_state ≠ .overwrite ∧
      r.write_state ≠ .move_flip ∧ r.write_state ≠ .increment_group)
    (hlw : l.write ≠ .increment_group) (hrw : r.write ≠ .increment_group)
    (hsafe : r.label.val = ψ - 1 → r.write = .overwrite → TSc r) :
    let q := writeAction hψ l r
    (q.1.bit = l.bit ∧ q.1.path3 = l.path3 ∧ q.1.label = l.label ∧ q.1.leader = l.leader ∧
      (q.1.write = l.write ∨ q.1.write = .none) ∧
      q.1.write_state ≠ .depart ∧ q.1.write_state ≠ .increment_group) ∧
    (q.2.bit = r.bit ∧ q.2.label = r.label ∧ q.2.leader = r.leader ∧
      (r.label.val ≠ ψ - 1 → q.2.path3 = r.path3) ∧
      (∀ p', q.2.path3 = some p' → ∃ p, r.path3 = some p ∧ p'.bit = p.bit ∧ p'.label = p.label) ∧
      (q.2.write = r.write ∨ q.2.write = .none) ∧ q.2.write_state = .depart) := by
  dsimp only
  rw [writeAction_eq_staged]
  unfold writeActionStaged
  obtain ⟨la1, la2, la3, la4, la5, la6, la7⟩ := activate_facts hψ l
  obtain ⟨ra1, ra2, ra3, ra4, ra5, ra6, ra7⟩ := activate_facts hψ r
  have hlr1 : (writeActionActivate hψ l).label < (writeActionActivate hψ r).label ∨
      (writeActionActivate hψ r).label = ⟨0, hψ⟩ := by rw [la3, ra3]; exact hlr
  have hl1ws : (writeActionActivate hψ l).write_state ≠ .depart ∧
      (writeActionActivate hψ l).write_state ≠ .increment_group := by
    by_cases ht : l.label.val = ψ - 1
    · rw [la7 ht]; exact ⟨toState_ne_depart _, toState_ne_inc hlw⟩
    · rw [la6 ht]; rcases hlws with h | h <;> rw [h] <;> simp
  have hr1ws : (writeActionActivate hψ r).write_state ≠ .depart ∧
      (writeActionActivate hψ r).write_state ≠ .increment_group := by
    by_cases ht : r.label.val = ψ - 1
    · rw [ra7 ht]; exact ⟨toState_ne_depart _, toState_ne_inc hrw⟩
    · rw [ra6 ht]; exact ⟨hrws.1, hrws.2.2.2⟩
  have hr1safe : (writeActionActivate hψ r).write_state = .overwrite →
      ∀ p, (writeActionActivate hψ r).path3 = some p →
        (writeActionActivate hψ r).bit = (p.bit == 1) := by
    intro hw p hp
    by_cases ht : r.label.val = ψ - 1
    · rw [ra7 ht] at hw
      rw [ra1]; exact hsafe ht (toState_overwrite hw) p (by rw [← ra2]; exact hp)
    · rw [ra6 ht] at hw; exact absurd hw hrws.2.1
  have hr1nt : r.label.val ≠ ψ - 1 →
      (writeActionActivate hψ r).write_state ≠ .overwrite ∧
        (writeActionActivate hψ r).write_state ≠ .move_flip := by
    intro ht; rw [ra6 ht]; exact ⟨hrws.2.1, hrws.2.2.1⟩
  generalize writeActionActivate hψ l = l1 at la1 la2 la3 la4 la5 la6 la7 hlr1 hl1ws ⊢
  generalize writeActionActivate hψ r = r1 at ra1 ra2 ra3 ra4 ra5 ra6 ra7 hlr1 hr1ws hr1safe hr1nt ⊢
  rw [execute_eq hψ l1 r1 hlr1]
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := owS_facts r1 hr1safe
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := mfS_facts (owS r1)
  have hinc : incS (mfS (owS r1)) = mfS (owS r1) := incS_id _ (by rw [m5, o5]; exact hr1ws.2)
  rw [hinc]
  generalize mfS (owS r1) = r3 at m1 m2 m3 m4 m5 m6 m7 ⊢
  generalize owS r1 = r2 at o1 o2 o3 o4 o5 o6 o7 m1 m2 m3 m4 m5 m6 m7
  have hr3ws : r3.write_state ≠ .depart ∧ r3.write_state ≠ .increment_group := by
    rw [m5, o5]; exact hr1ws
  have hb3 : r3.bit = r.bit := m1.trans (o1.trans ra1)
  have hl3 : r3.label = r.label := m2.trans (o2.trans ra3)
  have hd3 : r3.leader = r.leader := m3.trans (o3.trans ra4)
  have hp3 : r.label.val ≠ ψ - 1 → r3.path3 = r.path3 := by
    intro ht
    obtain ⟨n1, n2⟩ := hr1nt ht
    rw [m6 (by rw [o5]; exact n2), o6 n1, ra2]
  have he3 : ∀ p', r3.path3 = some p' →
      ∃ p, r.path3 = some p ∧ p'.bit = p.bit ∧ p'.label = p.label := by
    intro p' hp'
    obtain ⟨p1, hp1, e1, e2⟩ := m7 p' hp'
    obtain ⟨p0, hp0, e3, e4⟩ := o7 p1 hp1
    exact ⟨p0, by rw [← ra2]; exact hp0, e1.trans e3, e2.trans e4⟩
  have hw3 : r3.write = r.write ∨ r3.write = .none := by rw [m4, o4]; exact ra5
  split
  · exact ⟨⟨la1, la2, la3, la4, la5, hr3ws.1, hr3ws.2⟩, ⟨hb3, hl3, hd3, hp3, he3, hw3, rfl⟩⟩
  · exact ⟨⟨la1, la2, la3, la4, la5, hl1ws.1, hl1ws.2⟩, ⟨hb3, hl3, hd3, hp3, he3, hw3, rfl⟩⟩

/-! #### Algorithm 20 -/

theorem start_id (l r : AgentState ψ) (hr : r.leader = false) : moveWsigStart l r = (l, r) := by
  simp [moveWsigStart, hr]

theorem checkLast_facts (l : AgentState ψ) :
    (moveWsigCheckLast l).bit = l.bit ∧
    ((moveWsigCheckLast l).path3 = l.path3 ∨ (moveWsigCheckLast l).path3 = none) ∧
    (moveWsigCheckLast l).label = l.label ∧ (moveWsigCheckLast l).leader = l.leader ∧
    ((moveWsigCheckLast l).write = l.write ∨ (moveWsigCheckLast l).write = .none) ∧
    ((moveWsigCheckLast l).write_state = l.write_state ∨
      (moveWsigCheckLast l).write_state = .none) := by
  unfold moveWsigCheckLast
  split
  · split
    · exact ⟨rfl, Or.inr rfl, rfl, rfl, Or.inr rfl, Or.inr rfl⟩
    · exact ⟨rfl, Or.inl rfl, rfl, rfl, Or.inl rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inl rfl, rfl, rfl, Or.inl rfl, Or.inl rfl⟩

theorem transfer_id (l r : AgentState ψ) (h : l.write_state ≠ .depart) :
    moveWsigTransfer l r = (l, r) := by
  unfold moveWsigTransfer
  split
  · rw [if_neg h]
  · rfl

theorem moveWrite_facts (l r : AgentState ψ) :
    let q := moveWsigMoveWrite l r
    q.1.bit = l.bit ∧ q.1.path3 = l.path3 ∧ q.1.label = l.label ∧ q.1.leader = l.leader ∧
    q.1.write_state = l.write_state ∧ (q.1.write = l.write ∨ q.1.write = .none) ∧
    q.2.bit = r.bit ∧ q.2.path3 = r.path3 ∧ q.2.label = r.label ∧ q.2.leader = r.leader ∧
    q.2.write_state = r.write_state ∧ (l.label < r.label → q.2.write = l.write) ∧
    (¬ l.label < r.label → q.2.write = r.write) := by
  dsimp only
  unfold moveWsigMoveWrite
  split
  · next h => exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ => rfl, fun h' => absurd h h'⟩
  · next h => exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl, rfl, rfl, rfl, rfl, rfl,
      fun h' => absurd h' h, fun _ => rfl⟩

theorem leaderSignal_frame (l r : AgentState ψ) :
    Fr l (moveWsigLeaderSignal l r).1 ∧ Fr r (moveWsigLeaderSignal l r).2 := by
  unfold moveWsigLeaderSignal
  repeat' (first | (dsimp only) | split)
  all_goals frfl

theorem signalMove_frame (l r : AgentState ψ) :
    Fr l (moveWsigSignalMove l r).1 ∧ Fr r (moveWsigSignalMove l r).2 := by
  unfold moveWsigSignalMove
  repeat' (first | (dsimp only) | split)
  all_goals frfl

theorem echoMove_frame (l r : AgentState ψ) :
    Fr l (moveWsigEchoMove l r).1 ∧ Fr r (moveWsigEchoMove l r).2 := by
  unfold moveWsigEchoMove
  repeat' (first | (dsimp only) | split)
  all_goals frfl

/-- Algorithm 20 on a leaderless pair whose initiator is not `depart`. -/
theorem move_facts (l r : AgentState ψ) (hr : r.leader = false)
    (hws : l.write_state ≠ .depart) :
    let q := moveWsig hψ l r
    (q.1.bit = l.bit ∧ (q.1.path3 = l.path3 ∨ q.1.path3 = none) ∧ q.1.label = l.label ∧
      q.1.leader = l.leader ∧ (q.1.write = l.write ∨ q.1.write = .none) ∧
      (q.1.write_state = l.write_state ∨ q.1.write_state = .none)) ∧
    (q.2.bit = r.bit ∧ q.2.path3 = r.path3 ∧ q.2.label = r.label ∧ q.2.leader = r.leader ∧
      (l.label < r.label → (q.2.write = l.write ∨ q.2.write = .none)) ∧
      (¬ l.label < r.label → q.2.write = r.write) ∧ q.2.write_state = r.write_state) := by
  dsimp only
  rw [moveWsig_eq_staged]
  unfold moveWsigStaged
  dsimp only
  rw [start_id l r hr]
  dsimp only
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := checkLast_facts l
  have hk : (moveWsigCheckLast l).write_state ≠ .depart := by
    rcases k6 with h | h <;> rw [h]
    · exact hws
    · simp
  rw [transfer_id _ r hk]
  dsimp only
  generalize moveWsigCheckLast l = l1 at k1 k2 k3 k4 k5 k6 hk ⊢
  unfold moveWsigFinish
  dsimp only
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13⟩ := moveWrite_facts l1 r
  generalize moveWsigMoveWrite l1 r = q1 at w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ⊢
  obtain ⟨l2, r2⟩ := q1
  dsimp only at w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 ⊢
  have f1 := leaderSignal_frame l2 r2
  generalize moveWsigLeaderSignal l2 r2 = q2 at f1 ⊢
  obtain ⟨l3, r3⟩ := q2
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩⟩ := f1
  dsimp only at a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 ⊢
  have f2 := signalMove_frame l3 r3
  generalize moveWsigSignalMove l3 r3 = q3 at f2 ⊢
  obtain ⟨l4, r4⟩ := q3
  obtain ⟨⟨c1, c2, c3, c4, c5, c6⟩, ⟨e1, e2, e3, e4, e5, e6⟩⟩ := f2
  dsimp only at c1 c2 c3 c4 c5 c6 e1 e2 e3 e4 e5 e6 ⊢
  have f3 := echoMove_frame l4 r4
  obtain ⟨⟨d1, d2, d3, d4, d5, d6⟩, ⟨g1, g2, g3, g4, g5, g6⟩⟩ := f3
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [d1, c1, a1, w1, k1]
  · rw [d2, c2, a2, w2]; exact k2
  · rw [d5, c5, a5, w3, k3]
  · rw [d6, c6, a6, w4, k4]
  · rw [d3, c3, a3]
    rcases w6 with h | h
    · rw [h]; exact k5
    · right; exact h
  · rw [d4, c4, a4, w5]; exact k6
  · rw [g1, e1, b1, w7]
  · rw [g2, e2, b2, w8]
  · rw [g5, e5, b5, w9]
  · rw [g6, e6, b6, w10]
  · intro h
    rw [g3, e3, b3, w12 (by rw [k3]; exact h)]; exact k5
  · intro h
    rw [g3, e3, b3, w13 (by rw [k3]; exact h)]
  · rw [g4, e4, b4, w11]

/-- **Leaderless `writeSeq` with `NoInc` on consecutive labels.** -/
theorem writeSeq_local (h2 : 2 ≤ ψ) (a b : AgentState ψ) (ha : a.leader = false)
    (hb : b.leader = false) (hlab : b.label.val = (a.label.val + 1) % ψ)
    (haw : a.write ≠ .increment_group) (hbw : b.write ≠ .increment_group)
    (hsafe : b.label.val = ψ - 1 → b.write = .overwrite → TSc b) :
    let q := writeSeq hψ a b
    q.1.bit = a.bit ∧ q.2.bit = b.bit ∧
    (q.1.path3 = a.path3 ∨ q.1.path3 = none) ∧
    (b.label.val ≠ ψ - 1 → q.2.path3 = b.path3) ∧
    (∀ p', q.2.path3 = some p' → ∃ p, b.path3 = some p ∧ p'.bit = p.bit) ∧
    NIc q.1 ∧ NIc q.2 ∧
    (q.1.write = .overwrite → a.write = .overwrite) ∧
    (q.2.write = .overwrite → (b.label.val ≠ 0 ∧ a.write = .overwrite) ∨
      (b.label.val = 0 ∧ (b.write = .overwrite ∨ HOWc b))) := by
  dsimp only
  rw [writeSeq_eq_afterPrepare]
  unfold writeSeqThroughPrepare writeSeqAfterPrepare
  dsimp only
  rw [leaderMove_id hψ a b hb]
  dsimp only
  have hg := groupInfo_frame hψ a b
  generalize groupInfo hψ a b = g at hg
  obtain ⟨a1, b1⟩ := g
  obtain ⟨⟨g1, g2, g3, g4, g5, g6⟩, ⟨g7, g8, g9, g10, g11, g12⟩⟩ := hg
  dsimp only at g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 ⊢
  rw [generate_id hψ a1 b1 (g6.trans ha)]
  dsimp only
  have hp := prepare_facts hψ h2 a1 b1
  dsimp only at hp
  generalize writeSeqPrepare hψ a1 b1 = p at hp
  obtain ⟨a4, b4⟩ := p
  obtain ⟨⟨p1, p2, p3, p4, p5, p6⟩, ⟨p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17⟩⟩ := hp
  dsimp only at p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 ⊢
  -- consecutive labels
  have hlt : a.label < b.label ↔ b.label.val ≠ 0 := by
    have hal := a.label.isLt
    rw [Fin.lt_def]
    by_cases hc : a.label.val + 1 < ψ
    · rw [hlab, Nat.mod_eq_of_lt hc]
      exact ⟨fun _ => Nat.succ_ne_zero _, fun _ => Nat.lt_succ_self _⟩
    · have : a.label.val + 1 = ψ := Nat.le_antisymm hal (Nat.le_of_not_lt hc)
      rw [hlab, this, Nat.mod_self]
      exact ⟨fun h => absurd h (Nat.not_lt_zero _), fun h => absurd rfl h⟩
  have hlr : a4.label < b4.label ∨ b4.label = ⟨0, hψ⟩ := by
    rw [p3, p9, g5, g11]
    by_cases hz : b.label.val = 0
    · right; exact Fin.ext hz
    · left; exact hlt.2 hz
  have hsafe4 : b4.label.val = ψ - 1 → b4.write = .overwrite → TSc b4 := by
    intro ht hw
    have hz : b.label.val ≠ 0 := fun h0 => by rw [p9, g11, h0] at ht; omega
    rw [p17 (by rw [g11]; exact hz), g9] at hw
    have hts := hsafe (by rw [p9, g11] at ht; exact ht) hw
    intro p hp
    rw [p8, g8] at hp
    rw [p7, g7]; exact hts p hp
  have hw4 : b4.write ≠ .increment_group := p15 (by rw [g9]; exact hbw)
  have hact := action_facts hψ h2 a4 b4 hlr p6 ⟨p11, p12, p13, p14⟩ (by rw [p5, g3]; exact haw)
    hw4 hsafe4
  dsimp only at hact
  generalize writeAction hψ a4 b4 = w at hact
  obtain ⟨a5, b5⟩ := w
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7⟩, ⟨w8, w9, w10, w11, w12, w13, w14⟩⟩ := hact
  dsimp only at w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ⊢
  have hm := move_facts hψ a5 b5 (by rw [w10, p10, g12, hb]) w6
  dsimp only at hm
  generalize moveWsig hψ a5 b5 = m at hm
  obtain ⟨a6, b6⟩ := m
  obtain ⟨⟨m1, m2, m3, m4, m5, m6⟩, ⟨m7, m8, m9, m10, m11, m12, m13⟩⟩ := hm
  dsimp only at m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 ⊢
  have hlt5 : a5.label < b5.label ↔ b.label.val ≠ 0 := by
    rw [Fin.lt_def, w3, w9, p3, p9, g5, g11, ← Fin.lt_def]; exact hlt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m1, w1, p1, g1]
  · rw [m7, w8, p7, g7]
  · rcases m2 with h | h
    · left; rw [h, w2, p2, g2]
    · right; exact h
  · intro hb'
    rw [m8, w11 (by rw [p9, g11]; exact hb'), p8, g8]
  · intro p' hp'
    rw [m8] at hp'
    obtain ⟨p, hp, hb1, _⟩ := w12 p' hp'
    exact ⟨p, by rw [← g8, ← p8]; exact hp, hb1⟩
  · constructor
    · rcases m5 with h | h
      · rw [h]; rcases w5 with h' | h'
        · rw [h', p5, g3]; exact haw
        · rw [h']; simp
      · rw [h]; simp
    · rcases m6 with h | h
      · rw [h]; exact w7
      · rw [h]; simp
  · constructor
    · by_cases hz : b.label.val = 0
      · rw [m12 (by rw [hlt5]; exact fun h => h hz)]
        rcases w13 with h | h
        · rw [h]; exact hw4
        · rw [h]; simp
      · rcases m11 (hlt5.2 hz) with h | h
        · rw [h]; rcases w5 with h' | h'
          · rw [h', p5, g3]; exact haw
          · rw [h']; simp
        · rw [h]; simp
    · rw [m13, w14]; simp
  · intro h
    rcases m5 with h1 | h1
    · rw [h1] at h; rcases w5 with h' | h'
      · rw [h', p5, g3] at h; exact h
      · rw [h'] at h; cases h
    · rw [h1] at h; cases h
  · intro h
    by_cases hz : b.label.val = 0
    · right
      refine ⟨hz, ?_⟩
      rw [m12 (by rw [hlt5]; exact fun h => h hz)] at h
      rcases w13 with h' | h'
      · rw [h'] at h
        rcases p16 h with h'' | ⟨_, hh⟩
        · left; rw [← g9]; exact h''
        · right
          obtain ⟨p, hp, x1, x2, x3, x4⟩ := hh
          exact ⟨p, by rw [← g8]; exact hp, x1, x2, by rw [← g7]; exact x3, x4⟩
      · rw [h'] at h; cases h
    · left
      refine ⟨hz, ?_⟩
      rcases m11 (hlt5.2 hz) with h' | h'
      · rw [h'] at h; rcases w5 with h'' | h''
        · rw [h'', p5, g3] at h; exact h
        · rw [h''] at h; cases h
      · rw [h'] at h; cases h

end Local

/-! ### Ring-level predicate -/

/-- Perfect labels: cell `i` carries label `i mod ψ`. -/
def PL {n ψ : Nat} (C : Fin n → AuthState ψ) : Prop := ∀ i, (C i).core.label.val = i.val % ψ

/-- `LeaderlessBitFrozen` (indexing of `ZZSimClaimsAuth.leaderlessBitFrozen`):
`NoInc` everywhere, and for every group, given by its terminal `t`,
`TerminalSafe` at `t` or (no `HeadOW` at the head `t-(ψ-1)` and no pending
overwrite in the group `{j | j/ψ = t/ψ}`). -/
def LBF {n ψ : Nat} (C : Fin n → AuthState ψ) : Prop :=
  (∀ i, NIc (C i).core) ∧
  ∀ t : Fin n, t.val % ψ = ψ - 1 →
    TSc (C t).core ∨
    ((∀ h : Fin n, h.val + (ψ - 1) = t.val → ¬ HOWc (C h).core) ∧
      ∀ j : Fin n, j.val / ψ = t.val / ψ → (C j).core.write ≠ .overwrite)

/-! ### Arithmetic on the ring -/

section Arith

theorem succ_mod_of_dvd {n ψ : Nat} (hd : ψ ∣ n) (x : Nat) :
    ((x + 1) % n) % ψ = (x % ψ + 1) % ψ := by
  have h1 := Nat.add_mod x 1 ψ
  have h2 := Nat.add_mod (x % ψ) 1 ψ
  rw [Nat.mod_mod] at h2
  rw [Nat.mod_mod_of_dvd _ hd]
  exact h1.trans h2.symm

/-- Same quotient when the successor is not a multiple of ψ. -/
theorem div_succ_eq {ψ x : Nat} (hψ : 0 < ψ) (h : (x + 1) % ψ ≠ 0) :
    (x + 1) / ψ = x / ψ := by
  have e1 := Nat.div_add_mod (x + 1) ψ
  have e0 := Nat.div_add_mod x ψ
  have r1 := Nat.mod_lt (x + 1) hψ
  have r0 := Nat.mod_lt x hψ
  rcases Nat.lt_trichotomy ((x + 1) / ψ) (x / ψ) with hc | hc | hc
  · have := Nat.mul_le_mul_left ψ (Nat.succ_le_of_lt hc)
    rw [Nat.mul_succ] at this
    omega
  · exact hc
  · have := Nat.mul_le_mul_left ψ (Nat.succ_le_of_lt hc)
    rw [Nat.mul_succ] at this
    have hpos : 0 < (x + 1) % ψ := Nat.pos_of_ne_zero h
    omega

/-- A label-0 cell of the group of a terminal is its head. -/
theorem head_of_group {ψ j t : Nat} (hψ : 0 < ψ) (hj : j % ψ = 0) (ht : t % ψ = ψ - 1)
    (hg : j / ψ = t / ψ) : j + (ψ - 1) = t := by
  have e1 := Nat.div_add_mod j ψ
  have e0 := Nat.div_add_mod t ψ
  rw [hg] at e1
  omega

end Arith

/-! ### One served interaction -/

section Ring
variable {n ψ : Nat}

private theorem neighbor_ne (ring : DirectedRing n) (hn : 1 < n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have he := congrArg Fin.val h
  change (e.val + 1) % n = e.val at he
  by_cases hk : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hk] at he; omega
  · have hlast : e.val + 1 = n := by omega
    rw [hlast, Nat.mod_self] at he; omega

/-- One served interaction of the AuthF protocol. -/
abbrev S (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e : Fin n) : Fin n → AuthState ψ :=
  (authProtocol hp κ c).step ring C e

private theorem step_left (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e : Fin n) :
    S hp κ c ring C e e = (PPLLAuthF.pipeline hp κ c (C e) (C (ring.rightNeighbor e))).1 := by
  simp [S, PopulationProtocol.step, authProtocol]

private theorem step_right (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (hn : 1 < n) (C : Fin n → AuthState ψ) (e : Fin n) :
    S hp κ c ring C e (ring.rightNeighbor e) =
      (PPLLAuthF.pipeline hp κ c (C e) (C (ring.rightNeighbor e))).2 := by
  have ne := neighbor_ne ring hn e
  simp [S, PopulationProtocol.step, authProtocol, ne]

private theorem step_other (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) (e i : Fin n) (h1 : i ≠ e) (h2 : i ≠ ring.rightNeighbor e) :
    S hp κ c ring C e i = C i := by
  simp [S, PopulationProtocol.step, authProtocol, h1, h2]

private theorem kernel_labels (hp : ψ > 0) (l r : AgentState ψ) :
    (k4Kernel hp l r).1.label = l.label ∧ (k4Kernel hp l r).2.label = r.label := by
  simp only [k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire, absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp only [fst_ite, snd_ite, label_ite, ite_self, and_self]

private theorem wwb_leader (hp : ψ > 0) (l r : AgentState ψ) :
    (writeWithBundle hp l r).1.leader = (writeSeq hp l r).1.leader ∧
      (writeWithBundle hp l r).2.leader = (writeSeq hp l r).2.leader := by
  unfold writeWithBundle
  dsimp only
  -- Keep `writeSeq` opaque: with it concrete, each `rfl` below made the
  -- elaborator reduce `writeSeq hp l r` before the structure projection on
  -- the other side (791 s).
  generalize writeSeq hp l r = q
  split <;> exact ⟨rfl, rfl⟩

/-- The served pair of a leaderless edge whose outputs stay followers is
`writeSeq` on inputs with the original writer projection and labels. -/
theorem served_pair (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hnext : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hp⟩)
    (ho1 : (PPLLAuthF.pipeline hp κ c l r).1.core.leader = false)
    (ho2 : (PPLLAuthF.pipeline hp κ c l r).2.core.leader = false) :
    ∃ a b : AgentState ψ, wp a = wp l.core ∧ wp b = wp r.core ∧
      a.label = l.core.label ∧ b.label = r.core.label ∧
      a.leader = false ∧ b.leader = false ∧
      (PPLLAuthF.pipeline hp κ c l r).1.core = (writeSeq hp a b).1 ∧
      (PPLLAuthF.pipeline hp κ c l r).2.core = (writeSeq hp a b).2 := by
  have hc := pipeline_writer_compose hp κ c l r hl hr
  dsimp only at hc
  have hi := prefix_writer_inputs hp κ c l r hl hr hnext
  generalize PPLLAuthF.beforeElimination hp κ c l r = E at hc hi
  have hk := kernel_labels hp E.1.core E.2.core
  generalize k4Kernel hp E.1.core E.2.core = K at hc hk
  obtain ⟨c1, c2, c3, c4⟩ := hc
  rw [c1] at ho1
  rw [c2] at ho2
  have hwl := wwb_leader hp K.1 K.2
  have hK2 : K.2.leader = false := by
    cases h : K.2.leader
    · rfl
    · exfalso
      by_cases hz : K.2.label = ⟨0, hp⟩
      · have := PPLLVerify.writeSeq_responder_leader_of_label_zero hp K.1 K.2 h hz
        rw [hwl.2, this] at ho2; cases ho2
      · have := PPLLVerify.writeSeq_initiator_true_of_nonzero_responder_leader hp K.1 K.2 ⟨h, hz⟩
        rw [hwl.1, this] at ho1; cases ho1
  have hw : writeWithBundle hp K.1 K.2 = writeSeq hp K.1 K.2 := by
    simp [writeWithBundle, hK2]
  rw [hw] at ho1 c1 c2
  have hK1 : K.1.leader = false := by
    cases h : K.1.leader
    · rfl
    · have := PPLLVerify.writeSeq_initiator_leader_of_true hp K.1 K.2 h
      rw [this] at ho1; cases ho1
  exact ⟨K.1, K.2, c3, c4, hk.1.trans hi.1, hk.2.trans hi.2.2, hK1, hK2, c1, c2⟩

private theorem wp_fields {a b : AgentState ψ} (h : wp a = wp b) :
    a.bit = b.bit ∧ a.path3 = b.path3 ∧ a.write = b.write := by
  simp only [wp, Prod.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- **One-step closure of `LeaderlessBitFrozen`.** On a leaderless configuration
with perfect labels (`ψ ∣ n`, `2 ≤ ψ`, `1 < n`) satisfying `LBF`, serving any
edge `e` whose two output cores are followers keeps every bit, keeps perfect
labels and re-establishes `LBF`. Holds for every AuthF `Cfg`. -/
theorem step_closed (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) (C : Fin n → AuthState ψ)
    (hC : ∀ i, (C i).core.leader = false) (hpl : PL C) (hP : LBF C) (e : Fin n)
    (hout : ∀ i, (S hp κ c ring C e i).core.leader = false) :
    (∀ i, (S hp κ c ring C e i).core.bit = (C i).core.bit) ∧
    PL (S hp κ c ring C e) ∧ LBF (S hp κ c ring C e) := by
  have hDe := step_left hp κ c ring C e
  have hDe' := step_right hp κ c ring hn C e
  have hDo := step_other hp κ c ring C e
  have hne := neighbor_ne ring hn e
  have he'v : (ring.rightNeighbor e).val = (e.val + 1) % n := rfl
  generalize ring.rightNeighbor e = e' at hDe hDe' hDo hne he'v
  generalize S hp κ c ring C e = D at hDe hDe' hDo hout ⊢
  -- labels of the served pair
  have hlabv : (C e').core.label.val = ((C e).core.label.val + 1) % ψ := by
    rw [hpl e', hpl e, he'v]; exact succ_mod_of_dvd hd e.val
  have hnext : (C e').core.label = ⟨((C e).core.label.val + 1) % ψ, Nat.mod_lt _ hp⟩ :=
    Fin.ext hlabv
  obtain ⟨a, b, hwa, hwb, hla, hlb, hal, hbl, hq1, hq2⟩ :=
    served_pair hp κ c (C e) (C e') (hC e) (hC e') hnext
      (by have := hout e; rw [hDe] at this; exact this)
      (by have := hout e'; rw [hDe'] at this; exact this)
  obtain ⟨fa1, fa2, fa3⟩ := wp_fields hwa
  obtain ⟨fb1, fb2, fb3⟩ := wp_fields hwb
  -- the terminal safety of the served responder
  have hsafe : b.label.val = ψ - 1 → b.write = .overwrite → TSc b := by
    intro ht hw
    have ht' : e'.val % ψ = ψ - 1 := by rw [← hpl e', ← hlb]; exact ht
    rcases hP.2 e' ht' with hs | ⟨_, hno⟩
    · intro p hp3; rw [fb1]; exact hs p (by rw [← fb2]; exact hp3)
    · exact (hno e' rfl (by rw [← fb3]; exact hw)).elim
  have hloc := writeSeq_local hp h2 a b hal hbl (by rw [hla, hlb]; exact hlabv)
    (by rw [fa3]; exact (hP.1 e).1) (by rw [fb3]; exact (hP.1 e').1) hsafe
  dsimp only at hloc
  rw [← hq1, ← hq2, ← hDe, ← hDe'] at hloc
  obtain ⟨L1, L2, L3, L4, L5, L6, L7, L8, L9⟩ := hloc
  rw [fa1] at L1
  rw [fb1] at L2
  rw [fa2] at L3
  rw [hlb, fb2] at L4
  rw [fb2] at L5
  rw [fa3] at L8
  rw [hlb, fa3, fb3] at L9
  -- labels
  have hlabD : (D e).core.label = (C e).core.label ∧ (D e').core.label = (C e').core.label := by
    rw [hDe, hDe', hq1, hq2, PPLLVerify.writeSeq_l_label, PPLLVerify.writeSeq_r_label, hla, hlb]
    exact ⟨rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases h1 : i = e
    · subst i; exact L1
    · by_cases h2' : i = e'
      · subst i; exact L2
      · rw [hDo i h1 h2']
  · intro i
    by_cases h1 : i = e
    · subst i; rw [hlabD.1]; exact hpl e
    · by_cases h2' : i = e'
      · subst i; rw [hlabD.2]; exact hpl e'
      · rw [hDo i h1 h2']; exact hpl i
  · refine ⟨?_, ?_⟩
    · intro i
      by_cases h1 : i = e
      · subst i; exact L6
      · by_cases h2' : i = e'
        · subst i; exact L7
        · rw [hDo i h1 h2']; exact hP.1 i
    · intro t ht
      -- TerminalSafe persists
      have tsD : TSc (C t).core → TSc (D t).core := by
        intro hs
        by_cases h1 : t = e
        · subst t
          intro p hp3
          rw [L1]
          rcases L3 with h | h
          · exact hs p (by rw [← h]; exact hp3)
          · rw [h] at hp3; cases hp3
        · by_cases h2' : t = e'
          · subst t
            intro p hp3
            obtain ⟨p0, hp0, hbit⟩ := L5 p hp3
            rw [L2, hs p0 hp0, hbit]
          · rw [hDo t h1 h2']; exact hs
      rcases hP.2 t ht with hs | ⟨hno, hpend⟩
      · exact Or.inl (tsD hs)
      · right
        refine ⟨?_, ?_⟩
        · intro h hh hhow
          apply hno h hh
          by_cases h1 : h = e
          · subst h
            obtain ⟨p, hp3, x1, x2, x3, x4⟩ := hhow
            rcases L3 with h' | h'
            · exact ⟨p, by rw [← h']; exact hp3, x1, x2, by rw [← L1]; exact x3, x4⟩
            · rw [h'] at hp3; cases hp3
          · by_cases h2' : h = e'
            · subst h
              obtain ⟨p, hp3, x1, x2, x3, x4⟩ := hhow
              have hnt : (C e').core.label.val ≠ ψ - 1 := by
                rw [hpl e']
                have h0 : e'.val % ψ = 0 := by
                  have e0 := Nat.div_add_mod t.val ψ
                  have : e'.val = ψ * (t.val / ψ) := by omega
                  rw [this, Nat.mul_mod_right]
                rw [h0]
                exact fun h => by omega
              exact ⟨p, by rw [← L4 hnt]; exact hp3, x1, x2, by rw [← L2]; exact x3, x4⟩
            · rw [hDo h h1 h2'] at hhow; exact hhow
        · intro j hj hw
          by_cases h1 : j = e
          · subst j; exact hpend e hj (L8 hw)
          · by_cases h2' : j = e'
            · subst j
              rcases L9 hw with ⟨hz, hwa'⟩ | ⟨hz, hw' | hhow⟩
              · -- same group as the initiator
                apply hpend e _ hwa'
                rw [← hj, he'v]
                have hz' : ((e.val + 1) % n) % ψ ≠ 0 := by
                  rw [← he'v, ← hpl e']; exact hz
                have hlt : e.val + 1 < n := by
                  apply Nat.lt_of_not_le
                  intro hc
                  have := e.isLt
                  have : e.val + 1 = n := by omega
                  rw [this, Nat.mod_self, Nat.zero_mod] at hz'; exact hz' rfl
                rw [Nat.mod_eq_of_lt hlt] at hz' ⊢
                exact (div_succ_eq hp hz').symm
              · exact hpend e' hj hw'
              · obtain ⟨p, hp3, x1, x2, x3, x4⟩ := hhow
                apply hno e' _ ⟨p, by rw [← fb2]; exact hp3, x1, x2, by rw [← fb1]; exact x3, x4⟩
                apply head_of_group hp _ ht hj
                rw [← hpl e']; exact hz
            · rw [hDo j h1 h2'] at hw; exact hpend j hj hw

#print axioms writeSeq_local
#print axioms served_pair
#print axioms step_closed
end Ring
end PPLLAuthBitFrozen
