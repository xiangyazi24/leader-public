import Leader.Wu.Authorization.WaitReady
import Leader.Wu.Authorization.SerialDischarge

/-!
# GEN-COMPLETE: a running generation completes, `ψ ≥ 3`

Continuation of `PPLLAuthWaitReady.waitReady_block`.  Start: block `g` is
leaderless, `reset_cmd = false`, perfect labels, `echo`/`wait` arbitrary; the
head is a pathless producer whose `path4` is not a CLEAN command; every other
block cell is not `done`, and pathless if it is a producer.

`genComplete_block`: the word `0,1,…,ψ-2, ψ-3,…,0` (`2ψ-3` internal edges)
reaches a leader, or a block in which every cell `k` is
`PPLLAuthSerialDischarge.SerialPlusCell _ k γ` (`γ` = the head's initial
`ctrl_mark`); `Npath` rises from `≤ ψ-1` to `ψ`; no `produce`/`done`.

The endpoint is SerialPlus directly: cells `1..ψ-2` keep non-command
`path5 = (k,1)` records and the head keeps its `path4`, which SerialPlus
allows.  Cells that already carried paths are overwritten by the recruitment
(`gsR`), so they never block it.

The hypothesis `isCmd head.path4 = false` is needed: with a command `path4`,
`cleanApplyAuth` can delete the head's fresh path.
-/

set_option autoImplicit false

namespace PPLLAuthGenComplete

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF PPLLAuthResetDrain
open PPLLAuthGenDrain PPLLAuthGenDrainLocal PPLLAuthWaitReady

set_option linter.unusedSimpArgs false

section Rest
variable {ψ : Nat}

/-- A settled generation cell: state `s`, aligned path label `k`, no `path2`,
leaderless, no pending reset, both marks `γ`, no CLEAN command records. -/
def Cell (s : MainState) (k : Nat) (γ : ProvColor) (u : AuthState ψ) : Prop :=
  u.core.state = s ∧ (∃ x, u.core.path = .some k x) ∧ u.core.label.val = k ∧
  u.core.path2 = none ∧ u.core.leader = false ∧ u.core.reset_cmd = false ∧
  u.path_mark = γ ∧ u.ctrl_mark = γ ∧ isCmd u.core.path4 = false ∧ isCmd u.core.path5 = false

/-- A row pair after GENSIG: initiator `Cell s k γ`, responder `Cell depart (k+1) γ`;
with `z`, a terminal responder has `p = false` (no DISAPPEAR elimination). -/
def CP (s : MainState) (k : Nat) (γ : ProvColor) (z : Bool) (q : Pair ψ) : Prop :=
  Cell s k γ q.1 ∧ Cell .depart (k + 1) γ q.2 ∧
  (z = true → q.2.core.label.val = ψ - 1 → q.2.core.p = false)

set_option hygiene false in
macro "cpget" : tactic => `(tactic| (
  obtain ⟨a, b⟩ := q
  obtain ⟨⟨a1, ⟨xa, a2⟩, a3, a4, a5, a6, a7, a8, a9, a10⟩,
    ⟨b1, ⟨xb, b2⟩, b3, b4, b5, b6, b7, b8, b9, b10⟩, hz⟩ := h
  simp only at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 hz))

variable {s : MainState} {k : Nat} {γ : ProvColor} {z : Bool}

/-- Stages T2..T11 fix a settled row pair (`CP`), except T9, which clears the
terminal `p` bit. -/
theorem T2_cp (hψ : ψ > 0) (q : Pair ψ) (h : CP s k γ z q) : T2 hψ q = q :=
  T2_id hψ q (by rw [h.2.1.1]; nofun)

theorem T3_cp (hψ : ψ > 0) (q : Pair ψ) (h : CP s k γ z q) : T3 hψ q = q :=
  T3_id hψ q (by rw [h.2.1.1]; nofun)

/-- T4 fixes a settled row pair. -/
theorem T4_cp (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) (h : CP s k γ z q)
    (hs : s = .done ∨ s = .depart) : T4 hψ c q = q := by
  cpget
  have ca : checkState a = false := by
    rcases hs with rfl | rfl <;> simp [checkState, verdict, AuthState.st, a1]
  have cb : checkState b = false := by simp [checkState, verdict, AuthState.st, b1]
  unfold T4 moveSourceAuth
  simp only [a5, b5, Bool.false_eq_true, false_or, false_and, ite_false]
  rw [validate_quiet a b ca cb]
  dsimp only
  rw [sanitize_none a a4, sanitize_none b b4]
  have e1 : (if a.st = MainState.done then (a, b) else step1Auth a b) = (a, b) := by
    split
    · rfl
    · simp [step1Auth, a2, b2]
  simp only [e1, moveTokens_none c a b a4 b4, leaderWall_id a b a5 b5,
    applyControl_none hψ a a4, applyControl_none hψ b b4]
  rw [if_neg]
  intro hc
  have h3 := hc.2.2
  simp only [AuthState.st] at h3
  rcases hs with rfl | rfl <;> rw [a1] at h3 <;> cases h3

theorem T5_cp (q : Pair ψ) (h : CP s k γ z q) : T5 q = q := by
  cpget
  simp [T5, liftLife, dropStale, aligned, a2, a3, b2, b3]

theorem T6_cp (q : Pair ψ) (h : CP s k γ z q) : T6 q = q :=
  T6_id q h.1.2.2.2.2.1 h.1.2.2.2.2.2.1 h.2.1.2.2.2.2.2.1

theorem T7_cp (q : Pair ψ) (h : CP s k γ z q) (hs : s = .done ∨ s = .depart) : T7 q = q := by
  cpget
  rcases hs with rfl | rfl <;>
    simp [T7, liftLife, normalizeReady, normalizeOrphan, normalizeCarrier, aligned,
      a1, a2, a3, a5, b1, b2, b3, b5]

/-- T8 (checkSig) fixes a settled row pair. -/
theorem T8_cp (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) (h : CP s k γ z q)
    (hs : s = .done ∨ s = .depart) : T8 hψ c q = q := by
  cpget
  have ca : checkState a = false := by
    rcases hs with rfl | rfl <;> simp [checkState, verdict, AuthState.st, a1]
  have cb : checkState b = false := by simp [checkState, verdict, AuthState.st, b1]
  unfold T8
  rw [checkSource_eq]
  dsimp only
  rw [validate_quiet a b ca cb]
  dsimp only
  have ra : readyAuth a = a := by
    rcases hs with rfl | rfl <;>
    simp [readyAuth, AuthState.st, a1, a2, waveState, checkSigSetReadyGuarded, controlPending,
      checkSigSetReady]
  have rb : readyAuth b = b := by
    simp [readyAuth, AuthState.st, b1, b2, waveState, checkSigSetReadyGuarded, controlPending,
      checkSigSetReady]
  have eA : csA c a b = (a, b) := by
    unfold csA; rw [ra, rb]; simp
  rw [eA]
  dsimp only
  have eB : csB a b = a := by
    unfold csB; rw [if_neg]; rcases hs with rfl | rfl <;> simp [AuthState.st, a1]
  have eC : csC hψ a = a := by
    have hc : checkSigCheckL hψ a.core = a.core := by
      unfold checkSigCheckL
      rw [a2]
      split
      · rw [if_neg]; intro hc; rcases hs with rfl | rfl <;> rw [a1] at hc <;> cases hc.2
      · rfl
    unfold csC AuthState.withCore; rw [hc]
  rw [eB, eC]
  have ecert : certPred a b = false := by
    rcases hs with rfl | rfl <;> simp [certPred, a2, b2, AuthState.st, a1]
  rw [ecert]
  have eD : csD c false b = b := by unfold csD; simp
  have eE : csE hψ false a b = b := by unfold csE; simp
  have eF : csF a = a := by
    unfold csF issue; rcases hs with rfl | rfl <;> simp [AuthState.st, a1]
  have eG : csG false b = b := by unfold csG issue; simp [AuthState.st, b1]
  have eH : csH hψ false a b = (a, b) := by unfold csH; simp [AuthState.st, b1]
  rw [eD, eE, eG, eF, eH]

/-- T9 (DISAPPEAR) keeps a settled row pair and drops the `p` side condition. -/
theorem T9_cp (hψ : ψ > 0) (q : Pair ψ) (h : CP s k γ true q)
    (hs : s = .done ∨ s = .depart) : CP s k γ false (T9 hψ q) := by
  cpget
  have hsa : a.core.state ≠ .toss := by rcases hs with rfl | rfl <;> rw [a1] <;> nofun
  unfold T9 disappearAuth lift2 disappearStartL disappearCarry
  simp only [AuthState.st, b1, hsa, false_and, if_false]
  refine ⟨?_, ?_, by simp⟩
  · (repeat' split) <;> exact ⟨a1, ⟨xa, a2⟩, a3, a4, a5, a6, a7, a8, a9, a10⟩
  · (repeat' split) <;> (try exact ⟨b1, ⟨xb, b2⟩, b3, b4, b5, b6, b7, b8, b9, b10⟩)
    all_goals first
      | exact ⟨rfl, ⟨xb, b2⟩, b3, b4, b5, b6, b7, b8, b9, b10⟩
      | (exfalso; simp_all [Fin.ext_iff])

theorem T10_cp (q : Pair ψ) (h : CP s k γ z q) (hs : s = .done ∨ s = .depart) : T10 q = q := by
  cpget
  have am : (a.ctrl_mark = a.path_mark) = True := eq_true (a8.trans a7.symm)
  have bm : (b.ctrl_mark = b.path_mark) = True := eq_true (b8.trans b7.symm)
  have abm : (a.ctrl_mark = b.ctrl_mark) = True := eq_true (a8.trans b8.symm)
  have abm' : (b.ctrl_mark = a.ctrl_mark) = True := eq_true (b8.trans a8.symm)
  rcases hs with rfl | rfl <;>
  simp [T10, repairAuth, liftLife, normalizeOrphan, normalizeCarrier, lift2Life,
    releaseReadySuffix, ackTailAuth, lift2, ackTail, lockedState,
    a1, a2, a3, a4, a5, a6, am, bm, abm, abm', b1, b2, b3, b4, b5, b6]

theorem T11_cp (κ : Nat) (q : Pair ψ) (h : CP s k γ z q) (hs : s = .done ∨ s = .depart)
    (hk : k + 1 < ψ) : T11 κ q = q := by
  cpget
  have hne : k ≠ ψ - 1 := by omega
  have am : (a.ctrl_mark = a.path_mark) = True := eq_true (a8.trans a7.symm)
  have bm : (b.ctrl_mark = b.path_mark) = True := eq_true (b8.trans b7.symm)
  have abm : (a.ctrl_mark = b.ctrl_mark) = True := eq_true (a8.trans b8.symm)
  have abm' : (b.ctrl_mark = a.ctrl_mark) = True := eq_true (b8.trans a8.symm)
  rcases hs with rfl | rfl <;>
  simp [T11, compareLifecycleAuth, AuthState.st, AuthState.setState, AuthState.lineage,
    maintainAuth, completeWaveAuth, waveAuth, lift2, dropStray, landBackwardAuth,
    landForwardAuth, lockedState, lockerState, waveState, sessionTokenOn, hne,
    a1, a2, a3, a4, a5, a6, am, bm, abm, abm', b1, b2, b3, b4, b5, b6]


end Rest

/-! ### CLEAN on a new link -/

section Clean
variable {ψ : Nat}

/-- `genConnectAuth` on an occupied cell, field by field. -/
theorem gc_eq (h2 : 2 ≤ ψ) (u : AuthState ψ) (p x : Nat) (h : u.core.path = .some p x) :
    genConnectAuth u =
      { u with core := { u.core with path4 := (if p ≠ 0 then some (Int.ofNat p, 1) else u.core.path4), path5 := (if p ≠ ψ - 1 then some (Int.ofNat p, 1) else u.core.path5) }, path4_mark := (if p ≠ 0 then u.path_mark else u.path4_mark), path5_mark := (if p ≠ ψ - 1 then u.path_mark else u.path5_mark) } := by
  unfold genConnectAuth cleanSigGenConnect
  rw [h]
  by_cases h0 : p = 0
  · subst h0
    have h1 : ¬ (0 = ψ - 1) := by omega
    simp [h1, h]
  · by_cases h1 : p = ψ - 1
    · have h3 : ψ - 1 ≠ 0 := by omega
      subst h1; simp [h3, h]
    · simp [h0, h1, h]

/-- `cleanApplyAuth` without command records is the identity. -/
theorem cleanApply_nc (u : AuthState ψ) (h4 : isCmd u.core.path4 = false)
    (h5 : isCmd u.core.path5 = false) : cleanApplyAuth u = u := by
  unfold cleanApplyAuth
  rcases hp : u.core.path with _ | ⟨pl, pb⟩
  · rfl
  · rcases e4 : u.core.path4 with _ | ⟨l4, b4⟩ <;> rcases e5 : u.core.path5 with _ | ⟨l5, b5⟩ <;>
      simp only [e4, e5, isCmd, decide_eq_false_iff_not] at h4 h5 <;> simp [e4, e5, h4, h5]

/-- Clearing an absent `path4` is the identity. -/
theorem clear4_id (u : AuthState ψ) (h : u.core.path4 = none) :
    { u with core := { u.core with path4 := none } } = u := by
  obtain ⟨core, a, b, c, d, e, f⟩ := u
  simp only at h
  cases core
  simp only at h
  simp [h]

/-- Clearing an absent `path5` is the identity. -/
theorem clear5_id (u : AuthState ψ) (h : u.core.path5 = none) :
    { u with core := { u.core with path5 := none } } = u := by
  obtain ⟨core, a, b, c, d, e, f⟩ := u
  simp only at h
  cases core
  simp only at h
  simp [h]

/-- CLEAN on a new link `k → k+1` of one path colour: each side's connection
record is consumed by the other, no command is issued, nothing is deleted. -/
theorem T1_link (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (a b : AuthState ψ) (k xa xb : Nat)
    (ha : a.core.path = .some k xa) (hb : b.core.path = .some (k + 1) xb) (hk : k + 1 < ψ)
    (hm : b.path_mark = a.path_mark) (h0 : k = 0 → isCmd a.core.path4 = false)
    (hT : k + 1 = ψ - 1 → isCmd b.core.path5 = false) :
    T1 hψ c (a, b) =
      ({ genConnectAuth a with core := { (genConnectAuth a).core with path5 := none } },
       { genConnectAuth b with core := { (genConnectAuth b).core with path4 := none } }) := by
  obtain ⟨ga1, ga2, ga3, ga4⟩ := genConnect_link a k xa ha
  obtain ⟨gb1, gb2, gb3, gb4⟩ := genConnect_link b (k + 1) xb hb
  obtain ⟨ga7, ga8⟩ := ga4 (by omega)
  obtain ⟨gb5, gb6⟩ := gb3 (by omega)
  have ga4' : isCmd (genConnectAuth a).core.path4 = false := by
    rw [gc_eq (by omega) a k xa ha]
    by_cases hk0 : k = 0
    · simp [hk0]; exact h0 hk0
    · have hne : ¬ ((k : Int) = -1) := by omega
      simp [hk0, isCmd, hne]
  have gb5' : isCmd (genConnectAuth b).core.path5 = false := by
    rw [gc_eq (by omega) b (k + 1) xb hb]
    by_cases hkT : k + 1 = ψ - 1
    · simp [hkT]; exact hT hkT
    · have hne : ¬ ((k : Int) + 1 = -1) := by omega
      simp [hkT, isCmd, hne]
  unfold T1 cleanSourceAuth
  dsimp only
  generalize genConnectAuth a = a1 at ga1 ga2 ga4' ga7 ga8 ⊢
  generalize genConnectAuth b = b1 at gb1 gb2 gb5 gb6 gb5' ⊢
  rw [step3_link c.cleanNbr c.markClean a1 b1 k xa gb5 ga1 (by rw [gb6, ga2, hm])]
  dsimp only
  rw [step4_link c.cleanNbr c.markClean a1 { b1 with core := { b1.core with path4 := none } } k xb
    ga7 (by exact gb1) (by show a1.path5_mark = b1.path_mark; rw [ga8, gb2, hm])]
  dsimp only
  simp only [ga4', Bool.false_eq_true, ite_false, if_false]
  rw [step5_none hψ _ _ rfl]
  dsimp only
  simp only [gb5', Bool.false_eq_true, ite_false, if_false]
  rw [step6_none hψ _ _ rfl]
  dsimp only
  rw [cleanApply_nc _ (by simp [ga4']) (by simp [isCmd]),
    cleanApply_nc _ (by simp [isCmd]) (by simp [gb5'])]

end Clean

section Clean2
variable {ψ : Nat} {s : MainState} {k : Nat} {γ : ProvColor}

/-- `Cell` without the CLEAN-record clauses (a GENSIG output). -/
def Cell1 (s : MainState) (k : Nat) (γ : ProvColor) (u : AuthState ψ) : Prop :=
  u.core.state = s ∧ (∃ x, u.core.path = .some k x) ∧ u.core.label.val = k ∧
  u.core.path2 = none ∧ u.core.leader = false ∧ u.core.reset_cmd = false ∧
  u.path_mark = γ ∧ u.ctrl_mark = γ

/-- A row pair after GENSIG, before CLEAN: only the records CLEAN does not
overwrite are required to be non-commands (the head's `path4`, the terminal's
`path5`); a terminal responder has `p = false`. -/
def CP1 (s : MainState) (k : Nat) (γ : ProvColor) (q : Pair ψ) : Prop :=
  Cell1 s k γ q.1 ∧ Cell1 .depart (k + 1) γ q.2 ∧
  (k = 0 → isCmd q.1.core.path4 = false) ∧ (k + 1 = ψ - 1 → isCmd q.2.core.path5 = false) ∧
  (q.2.core.label.val = ψ - 1 → q.2.core.p = false)

/-- CLEAN (T1) on a freshly linked pair yields a settled row pair. -/
theorem T1_cp (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) (h : CP1 s k γ q) (hk : k + 1 < ψ) :
    CP s k γ true (T1 hψ c q) := by
  obtain ⟨a, b⟩ := q
  obtain ⟨⟨a1, ⟨xa, a2⟩, a3, a4, a5, a6, a7, a8⟩, ⟨b1, ⟨xb, b2⟩, b3, b4, b5, b6, b7, b8⟩,
    h0, hT, hz⟩ := h
  simp only at a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 h0 hT hz
  rw [T1_link hψ c a b k xa xb a2 b2 hk (b7.trans a7.symm) h0 hT,
    gc_eq (by omega) a k xa a2, gc_eq (by omega) b (k + 1) xb b2]
  have hne0 : ¬ ((k : Int) = -1) := by omega
  have hne1 : ¬ ((k : Int) + 1 = -1) := by omega
  have hkT : k ≠ ψ - 1 := by omega
  refine ⟨⟨?_, ⟨xa, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ⟨xb, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8]
  · by_cases hk0 : k = 0
    · simp [hk0]; exact h0 hk0
    · simp [hk0, isCmd, hne0]
  · simp [isCmd]
  · simp [isCmd]
  · by_cases hT' : k + 1 = ψ - 1
    · simp [hT']; exact hT hT'
    · simp [hT', isCmd, hne1]
  · intro _ hl; exact hz (by rw [b3]; exact hl)

end Clean2

section RestAll
variable {ψ : Nat} {s : MainState} {k : Nat} {γ : ProvColor}

/-- The stages of the AuthF row after GENSIG on a new link. -/
theorem rest_cp (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ) (h : CP1 s k γ q)
    (hs : s = .done ∨ s = .depart) (hk : k + 1 < ψ) :
    CP s k γ false (restPair hψ κ c q) := by
  have h1 := T1_cp hψ c q h hk
  unfold restPair restLo restHi
  rw [T2_cp hψ _ h1, T3_cp hψ _ h1, T4_cp hψ c _ h1 hs, T5_cp _ h1, T6_cp _ h1, T7_cp _ h1 hs,
    T8_cp hψ c _ h1 hs]
  have h9 := T9_cp hψ _ h1 hs
  rw [T10_cp _ h9 hs, T11_cp κ _ h9 hs hk]
  exact h9

end RestAll

/-! ### GENSIG on the rows that emit and propagate `done` -/

section GenSig
variable {ψ : Nat}

/-- `path4` of an `if` of agent states. -/
theorem ag4_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path4 = if p then a.path4 else b.path4 := by split <;> rfl
theorem ag5_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path5 = if p then a.path5 else b.path5 := by split <;> rfl
theorem agp_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).p = if p then a.p else b.p := by split <;> rfl

/-- `none` is not a CLEAN command. -/
theorem isCmd_none : isCmd (none : Option (Int × Nat)) = false := rfl

/-- WAIT keeps the CLEAN records and the lottery bit. -/
theorem waitSat_45 (hψ : ψ > 0) (κ : Nat) (a b : AgentState ψ) :
    (waitSaturated hψ κ a b).1.path4 = a.path4 ∧ (waitSaturated hψ κ a b).1.path5 = a.path5 ∧
    (waitSaturated hψ κ a b).2.path4 = b.path4 ∧ (waitSaturated hψ κ a b).2.path5 = b.path5 ∧
    (waitSaturated hψ κ a b).2.p = b.p := by
  simp only [waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish]
  simp only [gfst_ite, gsnd_ite, ag4_ite, ag5_ite, agp_ite, ite_self, and_self]

/-- The generation body on a pathless producer `H` (the output of the head
line) and its successor, which is either the terminal outside the generation
(emission) or the `done` link `k+1` of `H`'s colour (propagation). -/
theorem gs_tail (hψ : ψ > 0) (H r : AuthState ψ) (k : Nat) (hk : k + 1 ≤ ψ - 1)
    (a1 : H.core.state = .produce) (a2 : H.core.path = .bot) (a3 : H.core.path2 = none)
    (a4 : H.core.label.val = k) (a5 : H.core.leader = false) (a6 : H.core.reset_cmd = false)
    (a9 : k = 0 → isCmd H.core.path4 = false)
    (b3 : r.core.label.val = k + 1) (b5 : r.core.leader = false) (b6 : r.core.reset_cmd = false)
    (hr : (k + 1 = ψ - 1 ∧ r.core.state ≠ .done ∧ (r.core.state = .produce → r.core.path = .bot)) ∨
      (k + 1 < ψ - 1 ∧ r.core.state = .done ∧ (∃ y, r.core.path = .some (k + 1) y) ∧
        r.core.path2 = none ∧ r.path_mark = H.ctrl_mark ∧ r.ctrl_mark = H.ctrl_mark)) :
    CP1 (if k = 0 then .depart else .done) k H.ctrl_mark
      (gsF hψ (gsPair hψ H (gsE hψ (gsR hψ H r))).1, (gsPair hψ H (gsE hψ (gsR hψ H r))).2) := by
  have hl0 : ¬ (r.core.label = ⟨0, hψ⟩) := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have hlT : ¬ (H.core.label = ⟨ψ - 1, by omega⟩) := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rcases hr with ⟨hT, hd, hp⟩ | ⟨hT, hd, ⟨y, hy⟩, h2, hm, hc⟩
  · -- emission: recruit and wipe the terminal, it emits, `H` becomes the next link
    have eR : gsR hψ H r = wipeProduceAuth H.ctrl_mark r := by
      unfold gsR
      rw [if_pos]
      refine ⟨hl0, a1, ?_⟩
      by_cases hq : r.core.state = .produce
      · exact Or.inl (hp hq)
      · exact Or.inr (Or.inl ⟨hq, hd⟩)
    rw [eR]
    have hrT : r.core.label = ⟨ψ - 1, by omega⟩ := Fin.ext (by rw [b3]; exact hT)
    by_cases hk0 : k = 0
    · subst hk0
      have hH0 : H.core.label = ⟨0, hψ⟩ := Fin.ext a4
      have h0T : ¬ (0 = ψ - 1) := by omega
      simp [h0T, gsE, gsPair, gsF, wipeProduceAuth, AuthState.st, AuthState.setState, CP1, Cell1,
        hlT, hrT, hH0, a1, a2, a3, a4, a5, a6, b3, b5, b6, hT, a9 rfl, isCmd_none]
    · have hH0 : ¬ H.core.label = ⟨0, hψ⟩ := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp [gsE, gsPair, gsF, wipeProduceAuth, AuthState.st, AuthState.setState, CP1, Cell1,
        hlT, hrT, hH0, a1, a2, a3, a4, a5, a6, b3, b5, b6, hT, hk0, isCmd]
  · -- propagation: the `done` successor is left alone by recruitment and emission
    have eR : gsR hψ H r = r := by
      unfold gsR
      rw [if_neg]
      intro h
      rcases h.2.2 with h' | h' | h'
      · rw [hy] at h'; cases h'
      · exact h'.2 hd
      · exact h' hc
    have eE : gsE hψ r = r := by
      unfold gsE
      rw [if_neg]
      intro h; have := congrArg Fin.val h.1; simp at this; omega
    rw [eR, eE]
    have hTne : ¬ (k + 1 = ψ - 1) := by omega
    have hTne' : ¬ (r.core.label = ⟨ψ - 1, by omega⟩) := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    by_cases hk0 : k = 0
    · subst hk0
      have hH0 : H.core.label = ⟨0, hψ⟩ := Fin.ext a4
      have h0T : ¬ (0 = ψ - 1) := by omega
      simp [h0T, gsPair, gsF, AuthState.st, AuthState.setState, CP1, Cell1,
        hlT, hH0, a1, a2, a3, a4, a5, a6, b3, b5, b6, hd, hy, h2, hm, hc, hTne, hTne', a9 rfl, isCmd_none]
    · have hH0 : ¬ H.core.label = ⟨0, hψ⟩ := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp [gsPair, gsF, AuthState.st, AuthState.setState, CP1, Cell1,
        hlT, hH0, a1, a2, a3, a4, a5, a6, b3, b5, b6, hd, hy, h2, hm, hc, hTne, hTne', hk0, isCmd]

/-- **GENSIG on an emission or propagation row.** A pathless producer `l` with
label `k` (no `path2`; the head's `path4` no command) next to the terminal
outside the generation, or next to the `done` link `k+1` of `l`'s colour,
leaves GENSIG as a new link: `l` in `done` (the head: `depart`) with path `k`,
the successor in `depart` with path `k+1`, both of colour `l.ctrl_mark`. -/
theorem gs_row (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) (k : Nat) (hk : k + 1 ≤ ψ - 1)
    (a1 : l.core.state = .produce) (a2 : l.core.path = .bot) (a3 : l.core.path2 = none)
    (a4 : l.core.label.val = k) (a5 : l.core.leader = false) (a6 : l.core.reset_cmd = false)
    (a9 : k = 0 → isCmd l.core.path4 = false)
    (b3 : r.core.label.val = k + 1) (b5 : r.core.leader = false) (b6 : r.core.reset_cmd = false)
    (hr : (k + 1 = ψ - 1 ∧ r.core.state ≠ .done ∧ (r.core.state = .produce → r.core.path = .bot)) ∨
      (k + 1 < ψ - 1 ∧ r.core.state = .done ∧ (∃ y, r.core.path = .some (k + 1) y) ∧
        r.core.path2 = none ∧ r.path_mark = l.ctrl_mark ∧ r.ctrl_mark = l.ctrl_mark)) :
    CP1 (if k = 0 then .depart else .done) k l.ctrl_mark (genSigAuth hψ κ l r) := by
  obtain ⟨s1, p1, q1, lb1, ld1, s2, p2, q2, lb2, ld2⟩ := waitSat_fields hψ κ l.core r.core
  obtain ⟨w4, -, -, -, -⟩ := waitSat_45 hψ κ l.core r.core
  have dv := wait_dv hψ κ l.core r.core
  have rs1 : (waitSaturated hψ κ l.core r.core).1.reset_cmd = l.core.reset_cmd :=
    congrArg Prod.fst dv.1
  have rs2 : (waitSaturated hψ κ l.core r.core).2.reset_cmd = r.core.reset_cmd :=
    congrArg Prod.fst dv.2
  rw [gs_body]
  apply gsBody_open hψ _ _ (CP1 (if k = 0 then .depart else .done) k l.ctrl_mark)
  intro H R E Q hH hR hE hQ
  subst hR hE hQ
  -- the WAIT outputs
  generalize e1 : (lift2 (waitSaturated hψ κ) l r).1 = l1 at hH
  generalize e2 : (lift2 (waitSaturated hψ κ) l r).2 = r1
  have f1 : l1.core = (waitSaturated hψ κ l.core r.core).1 := by rw [← e1]; rfl
  have f2 : r1.core = (waitSaturated hψ κ l.core r.core).2 := by rw [← e2]; rfl
  have m1 : l1.ctrl_mark = l.ctrl_mark := by rw [← e1]; rfl
  have m2 : r1.ctrl_mark = r.ctrl_mark := by rw [← e2]; rfl
  have m3 : r1.path_mark = r.path_mark := by rw [← e2]; rfl
  -- the head line
  have hHf : H.core.state = .produce ∧ H.core.path = .bot ∧ H.core.path2 = none ∧
      H.core.label.val = k ∧ H.core.leader = false ∧ H.core.reset_cmd = false ∧
      (k = 0 → isCmd H.core.path4 = false) ∧ H.ctrl_mark = l.ctrl_mark := by
    subst hH
    unfold gsH
    split
    · simp [wipeProduceAuth, AuthState.st, f1, s1, a1, lb1, a4, ld1, a5, rs1, a6, m1, isCmd_none]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, m1⟩
      · rw [f1, s1, a1]
      · rw [f1, p1, a2]
      · rw [f1, q1, a3]
      · rw [f1, lb1, a4]
      · rw [f1, ld1, a5]
      · rw [f1, rs1, a6]
      · intro h0; rw [f1, w4]; exact a9 h0
  obtain ⟨h1, h2, h3, h4, h5, h6, h9, hc⟩ := hHf
  rw [← hc]
  apply gs_tail hψ H r1 k hk h1 h2 h3 h4 h5 h6 h9
    (by rw [f2, lb2, b3]) (by rw [f2, ld2, b5]) (by rw [f2, rs2, b6])
  rcases hr with ⟨x1, x2, x3⟩ | ⟨x1, x2, ⟨y, x3⟩, x4, x5, x6⟩
  · refine Or.inl ⟨x1, by rw [f2, s2]; exact x2, ?_⟩
    rw [f2, s2, p2]; exact x3
  · refine Or.inr ⟨x1, by rw [f2, s2]; exact x2, ⟨y, by rw [f2, p2]; exact x3⟩,
      by rw [f2, q2]; exact x4, by rw [m3, hc]; exact x5, by rw [m2, hc]; exact x6⟩

end GenSig

/-! ### The suffix keeps the CLEAN records -/

namespace F45

/-- Two cells agree on the CLEAN records. -/
def F {ψ : Nat} (a b : AgentState ψ) : Prop := a.path4 = b.path4 ∧ a.path5 = b.path5

theorem writeActionApplyOverwrite_f {ψ : Nat} (u : AgentState ψ) :
    F (writeActionApplyOverwrite u) u := by
  unfold F writeActionApplyOverwrite
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem writeActionApplyMoveFlip_f {ψ : Nat} (u : AgentState ψ) :
    F (writeActionApplyMoveFlip u) u := by
  unfold F writeActionApplyMoveFlip
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem moveWsigCheckLast_f {ψ : Nat} (u : AgentState ψ) : F (moveWsigCheckLast u) u := by
  unfold F moveWsigCheckLast
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem writeSeqSetWriteReady_f {ψ : Nat} (u : AgentState ψ) : F (writeSeqSetWriteReady u) u := by
  unfold F writeSeqSetWriteReady
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem writeSeqCheckBit_f {ψ : Nat} (u : AgentState ψ) : F (writeSeqCheckBit u) u := by
  unfold F writeSeqCheckBit
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem writeSeqSetWriteAct_f {ψ : Nat} (u : AgentState ψ) : F (writeSeqSetWriteAct u) u := by
  cases hp : u.path3 <;> simp only [F, writeSeqSetWriteAct, hp] <;>
    simp [ag4_ite, ag5_ite, hp]

theorem writeSeqFinalR_f {ψ : Nat} (u : AgentState ψ) : F (writeSeqFinalR u) u := by
  unfold F writeSeqFinalR
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem moveWsigCheckGenWs_f {ψ : Nat} (l r : AgentState ψ) : F (moveWsigCheckGenWs l r) r := by
  unfold F moveWsigCheckGenWs
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem moveWsigTransfer_f {ψ : Nat} (l r : AgentState ψ) :
    F (moveWsigTransfer l r).1 l ∧ F (moveWsigTransfer l r).2 r := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp only [F, moveWsigTransfer, hl, hr] <;>
    simp only [gfst_ite, gsnd_ite, ag4_ite, ag5_ite, ite_self, and_self]

theorem groupInfo_f {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    F (groupInfo hψ l r).1 l ∧ F (groupInfo hψ l r).2 r := by
  simp only [F, groupInfo]
  simp only [gfst_ite, gsnd_ite, ag4_ite, ag5_ite, ite_self, and_self]

theorem gensigWriteseq_f {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    F (gensigWriteseq hψ l r).1 l ∧ F (gensigWriteseq hψ l r).2 r := by
  simp only [F, gensigWriteseq]
  simp only [gfst_ite, gsnd_ite, ag4_ite, ag5_ite, ite_self, and_self]

theorem writeAction_f {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    F (writeAction hψ l r).1 l ∧ F (writeAction hψ l r).2 r := by
  simp only [F, writeAction]
  simp only [gfst_ite, gsnd_ite, ag4_ite, ag5_ite, ite_self, and_self,
    (writeActionApplyOverwrite_f _).1, (writeActionApplyOverwrite_f _).2,
    (writeActionApplyMoveFlip_f _).1, (writeActionApplyMoveFlip_f _).2]

theorem moveWsig_f {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    F (moveWsig hψ l r).1 l ∧ F (moveWsig hψ l r).2 r := by
  simp only [F, moveWsig]
  simp only [gfst_ite, gsnd_ite, ag4_ite, ag5_ite, ite_self, and_self,
    (moveWsigCheckGenWs_f _ _).1, (moveWsigCheckGenWs_f _ _).2,
    (moveWsigCheckLast_f _).1, (moveWsigCheckLast_f _).2,
    (moveWsigTransfer_f _ _).1.1, (moveWsigTransfer_f _ _).1.2,
    (moveWsigTransfer_f _ _).2.1, (moveWsigTransfer_f _ _).2.2]

theorem writeSeq_f {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    F (writeSeq hψ l r).1 l ∧ F (writeSeq hψ l r).2 r := by
  simp only [F, writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands]
  simp only [gfst_ite, gsnd_ite, ag4_ite, ag5_ite, ite_self, and_self,
    (groupInfo_f _ _ _).1.1, (groupInfo_f _ _ _).1.2, (groupInfo_f _ _ _).2.1, (groupInfo_f _ _ _).2.2,
    (gensigWriteseq_f _ _ _).1.1, (gensigWriteseq_f _ _ _).1.2,
    (gensigWriteseq_f _ _ _).2.1, (gensigWriteseq_f _ _ _).2.2,
    (writeAction_f _ _ _).1.1, (writeAction_f _ _ _).1.2,
    (writeAction_f _ _ _).2.1, (writeAction_f _ _ _).2.2,
    (moveWsig_f _ _ _).1.1, (moveWsig_f _ _ _).1.2, (moveWsig_f _ _ _).2.1, (moveWsig_f _ _ _).2.2,
    (writeSeqSetWriteReady_f _).1, (writeSeqSetWriteReady_f _).2,
    (writeSeqCheckBit_f _).1, (writeSeqCheckBit_f _).2,
    (writeSeqSetWriteAct_f _).1, (writeSeqSetWriteAct_f _).2,
    (writeSeqFinalR_f _).1, (writeSeqFinalR_f _).2]

theorem write_f {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    F (writeWithBundle hψ l r).1 l ∧ F (writeWithBundle hψ l r).2 r := by
  have h := writeSeq_f hψ l r
  unfold writeWithBundle
  split
  · simp only [F] at h ⊢; exact h
  · exact h

theorem kernel_f {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    F (k4Kernel hψ l r).1 l ∧ F (k4Kernel hψ l r).2 r := by
  simp only [F, k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire, absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  simp only [gfst_ite, gsnd_ite, ag4_ite, ag5_ite, ite_self, and_self]

/-- The suppression stage keeps `path4` and `path5` on a leaderless pair. -/
theorem suppress_f {ψ : Nat} (hψ : ψ > 0) (l r : AuthState ψ) (hl : l.core.leader = false)
    (h1 : l.core.reset_cmd = false) (h2 : r.core.reset_cmd = false) :
    F (suppressSigResetKillAuth hψ l r).1.core l.core ∧
      F (suppressSigResetKillAuth hψ l r).2.core r.core := by
  unfold suppressSigResetKillAuth lift2
  simp only [suppressSigStart, suppressSigMoveReset, suppressSigTerminal, suppressSigFinish,
    hl, h1, h2]
  by_cases he : r.core.echo = true <;>
    simp [suppressSigEcho, he, h1, h2, hl, F]

/-- **Suffix frame of the CLEAN records.** Algorithm 14, K4, WRITE and the
conservation guard keep `path4` and `path5` of both cells. -/
theorem post_f {ψ : Nat} (hψ : ψ > 0) (l r : AuthState ψ) (hl : l.core.leader = false)
    (hr : r.core.leader = false) (q : AuthState ψ × AuthState ψ)
    (hq1 : q.1.core.leader = false) (h1 : q.1.core.reset_cmd = false)
    (h2 : q.2.core.reset_cmd = false) :
    F (PPLLAuthSerialDischarge.post hψ l r q).1.core q.1.core ∧
      F (PPLLAuthSerialDischarge.post hψ l r q).2.core q.2.core := by
  unfold PPLLAuthSerialDischarge.post
  dsimp only
  rw [PPLLAuthSerialDischarge.conserve_id l r hl hr]
  have hs := suppress_f hψ q.1 q.2 hq1 h1 h2
  generalize suppressSigResetKillAuth hψ q.1 q.2 = t at hs
  obtain ⟨t1, t2⟩ := t
  have hk := kernel_f hψ t1.core t2.core
  have hw := write_f hψ (k4Kernel hψ t1.core t2.core).1 (k4Kernel hψ t1.core t2.core).2
  simp only [lift2]
  simp only [F] at hs hk hw ⊢
  exact ⟨⟨hw.1.1.trans (hk.1.1.trans hs.1.1), hw.1.2.trans (hk.1.2.trans hs.1.2)⟩,
    ⟨hw.2.1.trans (hk.2.1.trans hs.2.1), hw.2.2.trans (hk.2.2.trans hs.2.2)⟩⟩

end F45

/-! ### One emission or propagation row of the AuthF pipeline -/

section RowFill
variable {ψ : Nat}

/-- A finished generation cell as a pipeline output: state `s`, aligned path
label `k`, no `path2`, both marks `γ`, no CLEAN command records. -/
def GC (s : MainState) (k : Nat) (γ : ProvColor) (u : AuthState ψ) : Prop :=
  u.core.state = s ∧ (∃ x, u.core.path = .some k x) ∧ u.core.label.val = k ∧
  u.core.path2 = none ∧ u.path_mark = γ ∧ u.ctrl_mark = γ ∧
  isCmd u.core.path4 = false ∧ isCmd u.core.path5 = false

/-- The AuthF pipeline as `post` of the pre-suppression stages. -/
theorem pipeline_post (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    PPLLAuthF.pipeline hψ κ c l r =
      PPLLAuthSerialDischarge.post hψ l r (restPair hψ κ c (genSigAuth hψ κ (P0 hψ l r).1 (P0 hψ l r).2)) :=
  rfl

/-- A settled row pair crosses `post` as settled cells. -/
theorem GC_of_post (hψ : ψ > 0) (l r : AuthState ψ) (hl : l.core.leader = false)
    (hr : r.core.leader = false) {s : MainState} {k : Nat} {γ : ProvColor}
    (q : Pair ψ) (h : CP s k γ false q) :
    GC s k γ (PPLLAuthSerialDischarge.post hψ l r q).1 ∧
      GC .depart (k + 1) γ (PPLLAuthSerialDischarge.post hψ l r q).2 := by
  obtain ⟨⟨a1, ⟨xa, a2⟩, a3, a4, a5, a6, a7, a8, a9, a10⟩,
    ⟨b1, ⟨xb, b2⟩, b3, b4, b5, b6, b7, b8, b9, b10⟩, -⟩ := h
  have hp := PPLLAuthSerialDischarge.post_frame hψ l r hl hr q a5 a6 b6
  have hf := F45.post_f hψ l r hl hr q a5 a6 b6
  obtain ⟨⟨w1, w2, w3, -, w5⟩, ⟨v1, v2, v3, -, v5⟩, ⟨m1, m2, -, -⟩, ⟨n1, n2, -, -⟩, -⟩ := hp
  obtain ⟨⟨f1, f2⟩, ⟨g1, g2⟩⟩ := hf
  refine ⟨⟨?_, ⟨xa, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ⟨xb, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [w1, a1]
  · rw [w2, a2]
  · rw [w5, a3]
  · rw [w3, a4]
  · rw [m1, a7]
  · rw [m2, a8]
  · rw [f1, a9]
  · rw [f2, a10]
  · rw [v1, b1]
  · rw [v2, b2]
  · rw [v5, b3]
  · rw [v3, b4]
  · rw [n1, b7]
  · rw [n2, b8]
  · rw [g1, b9]
  · rw [g2, b10]

/-- **Emission / propagation row.** A pathless producer `l` with label `k`
(no `path2`; the head's `path4` no command), next to the terminal outside the
generation (`k+1 = ψ-1`) or to the `done` link `k+1` of `l`'s colour, leaves the
AuthF row with `l` the `done` link `k` (the head: `depart`) and its successor a
finished `depart` cell with path `k+1`, both of colour `l.ctrl_mark`, no `path2`
and no command records. -/
theorem row_fill (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (k : Nat)
    (h : RowH ψ l r k)
    (a1 : l.core.state = .produce) (a2 : l.core.path = .bot) (a3 : l.core.path2 = none)
    (a9 : k = 0 → isCmd l.core.path4 = false)
    (hr : (k + 1 = ψ - 1 ∧ r.core.state ≠ .done ∧ (r.core.state = .produce → r.core.path = .bot)) ∨
      (k + 1 < ψ - 1 ∧ r.core.state = .done ∧ (∃ y, r.core.path = .some (k + 1) y) ∧
        r.core.path2 = none ∧ r.path_mark = l.ctrl_mark ∧ r.ctrl_mark = l.ctrl_mark)) :
    GC (if k = 0 then .depart else .done) k l.ctrl_mark (PPLLAuthF.pipeline hψ κ c l r).1 ∧
      GC .depart (k + 1) l.ctrl_mark (PPLLAuthF.pipeline hψ κ c l r).2 := by
  obtain ⟨x, y, hP⟩ := P0_frame hψ l r h.ll h.rl h.lab
  rw [pipeline_post, hP]
  have hk : k + 1 < ψ := by have := h.kψ; omega
  have G := gs_row hψ κ { l with core := { l.core with probe := x } }
    { r with core := { r.core with probe := y } } k h.kψ a1 a2 a3 h.lk h.ll h.lr a9 h.rk h.rl h.rr hr
  have hs : (if k = 0 then MainState.depart else MainState.done) = .done ∨
      (if k = 0 then MainState.depart else MainState.done) = .depart := by
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have R := rest_cp hψ κ c _ G hs hk
  exact GC_of_post hψ l r h.ll h.rl _ R

end RowFill

/-! ### The head's `path4` through the first recruitment row -/

section Head
variable {ψ : Nat}

/-- The GENSIG tail of the first recruitment row keeps a non-command head `path4`. -/
theorem gs_tail0 (hψ : ψ > 0) (H r : AuthState ψ) (h3 : 3 ≤ ψ)
    (a1 : H.core.state = .produce) (a4 : H.core.label.val = 0) (a9 : isCmd H.core.path4 = false)
    (b3 : r.core.label.val = 1) (hd : r.core.state ≠ .done)
    (hp : r.core.state = .produce → r.core.path = .bot) :
    isCmd (gsF hψ (gsPair hψ H (gsE hψ (gsR hψ H r))).1).core.path4 = false ∧
      (gsPair hψ H (gsE hψ (gsR hψ H r))).2.core.path4 = none := by
  have hl0 : ¬ (r.core.label = ⟨0, hψ⟩) := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have eR : gsR hψ H r = wipeProduceAuth H.ctrl_mark r := by
    unfold gsR
    rw [if_pos]
    refine ⟨hl0, a1, ?_⟩
    by_cases hq : r.core.state = .produce
    · exact Or.inl (hp hq)
    · exact Or.inr (Or.inl ⟨hq, hd⟩)
  have eE : gsE hψ (wipeProduceAuth H.ctrl_mark r) = wipeProduceAuth H.ctrl_mark r := by
    unfold gsE
    rw [if_neg]
    intro h; have := congrArg Fin.val h.1; simp [wipeProduceAuth] at this; omega
  have eP : gsPair hψ H (wipeProduceAuth H.ctrl_mark r) = (H, wipeProduceAuth H.ctrl_mark r) := by
    unfold gsPair
    rw [if_neg]
    intro h; simp [wipeProduceAuth, AuthState.st] at h
  have eF : gsF hψ H = H := by
    unfold gsF
    rw [if_neg]
    intro h; simp [AuthState.st, a1] at h
  rw [eR, eE, eP]
  exact ⟨by rw [eF]; exact a9, rfl⟩

/-- GENSIG on the head row of a running generation: the head keeps a
non-command `path4` (or loses it to the head line's wipe), the recruited
successor has no `path4`. -/
theorem gs_F0 (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) (h3 : 3 ≤ ψ)
    (a1 : l.core.state = .produce) (a4 : l.core.label.val = 0) (a9 : isCmd l.core.path4 = false)
    (b3 : r.core.label.val = 1) (hd : r.core.state ≠ .done)
    (hp : r.core.state = .produce → r.core.path = .bot) :
    isCmd (genSigAuth hψ κ l r).1.core.path4 = false ∧ (genSigAuth hψ κ l r).2.core.path4 = none := by
  obtain ⟨s1, -, -, lb1, -, s2, p2, -, lb2, -⟩ := waitSat_fields hψ κ l.core r.core
  obtain ⟨w4, -, -, -, -⟩ := waitSat_45 hψ κ l.core r.core
  rw [gs_body]
  apply gsBody_open hψ _ _ (fun G => isCmd G.1.core.path4 = false ∧ G.2.core.path4 = none)
  intro H R E Q hH hR hE hQ
  subst hR hE hQ
  generalize e1 : (lift2 (waitSaturated hψ κ) l r).1 = l1 at hH
  generalize e2 : (lift2 (waitSaturated hψ κ) l r).2 = r1
  have f1 : l1.core = (waitSaturated hψ κ l.core r.core).1 := by rw [← e1]; rfl
  have f2 : r1.core = (waitSaturated hψ κ l.core r.core).2 := by rw [← e2]; rfl
  have hHf : H.core.state = .produce ∧ H.core.label.val = 0 ∧ isCmd H.core.path4 = false := by
    subst hH
    unfold gsH
    split
    · simp [wipeProduceAuth, f1, lb1, a4, isCmd_none]
    · exact ⟨by rw [f1, s1, a1], by rw [f1, lb1, a4], by rw [f1, w4]; exact a9⟩
  obtain ⟨h1, h4, h9⟩ := hHf
  exact gs_tail0 hψ H r1 h3 h1 h4 h9 (by rw [f2, lb2, b3]) (by rw [f2, s2]; exact hd)
    (by rw [f2, s2, p2]; exact hp)

/-- `sanitizeP2` keeps `path4`. -/
theorem sanitize_4 (u : AuthState ψ) : (sanitizeP2 u).core.path4 = u.core.path4 := by
  unfold sanitizeP2; split <;> rfl

/-- T9 keeps the initiator's `path4`. -/
theorem T9_4 (hψ : ψ > 0) (q : Pair ψ) : (T9 hψ q).1.core.path4 = q.1.core.path4 := by
  obtain ⟨a, b⟩ := q
  unfold T9 disappearAuth lift2 disappearStartL disappearCarry
  (repeat' (first | (dsimp only) | split)) <;> rfl

/-- `genConnectAuth` fixes a pathless cell. -/
theorem genConnect_bot (u : AuthState ψ) (h : u.core.path = .bot) : genConnectAuth u = u := by
  simp [genConnectAuth, h]

/-- CLEAN (T1) keeps the initiator's `path4` on two pathless cells whose responder
has no `path4`. -/
theorem T1_bot4 (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : Pair ψ) (h1 : q.1.core.path = .bot)
    (h2 : q.2.core.path = .bot) (h4 : q.2.core.path4 = none) :
    (T1 hψ c q).1.core.path4 = q.1.core.path4 := by
  obtain ⟨a, b⟩ := q
  simp only at h1 h2 h4
  have e3 : step3Auth c.cleanNbr c.markClean a b = (a, b) := by simp [step3Auth, h4]
  have e4 : step4Auth c.cleanNbr c.markClean a b = (a, b) := by
    unfold step4Auth; split <;> simp_all
  have e5 : (if isCmd a.core.path4 = true then (a, { b with core := { b.core with path4 := none } })
      else step5Auth hψ a b) = (a, b) := by
    split
    · rw [clear4_id b h4]
    · exact step5_none hψ a b h4
  have hca : ∀ v : AuthState ψ, v.core.path = .bot → cleanApplyAuth v = v := by
    intro v hv; simp [cleanApplyAuth, hv]
  unfold T1 cleanSourceAuth
  dsimp only
  rw [genConnect_bot a h1, genConnect_bot b h2, e3]
  dsimp only
  rw [e4]
  dsimp only
  rw [e5]
  dsimp only
  split
  · rw [hca _ (by exact h1)]
  · unfold step6Auth
    split
    · dsimp only
      split
      · split <;> rw [hca _ (by exact h1)]
      · rw [hca _ (by exact h1)]
    · rw [hca _ h1]

/-- The head's `path4` crosses `restPair` on a pair of pathless producers whose
responder has no `path4`. -/
theorem rest_Ph4 (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (q : Pair ψ)
    (s1 : q.1.core.state = .produce) (s2 : q.2.core.state = .produce)
    (h1 : q.1.core.path = .bot) (h2 : q.2.core.path = .bot)
    (k1 : q.1.core.leader = false) (k2 : q.2.core.leader = false)
    (r1 : q.1.core.reset_cmd = false) (r2 : q.2.core.reset_cmd = false)
    (hT : q.2.core.label.val ≠ ψ - 1) (h4 : q.2.core.path4 = none) :
    (restPair hψ κ c q).1.core.path4 = q.1.core.path4 := by
  have t1 := T1_cv hψ c q
  have a1 := T1_pa hψ c q
  have t4 := T1_bot4 hψ c q h1 h2 h4
  unfold restPair
  generalize T1 hψ c q = q1 at t1 a1 t4 ⊢
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
  have g4 := sanitize_4 q1.1
  generalize sanitizeP2 q1.1 = x1 at f1 n1 g4 ⊢
  generalize sanitizeP2 q1.2 = x2 at f2 n2 ⊢
  obtain ⟨g1, g2, g3, g4', g5, -, g7, -⟩ := f1
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
  have t94 := T9_4 hψ (x1, x2)
  generalize T9 hψ (x1, x2) = q9 at t9 t94 ⊢
  obtain ⟨⟨u1, u2, u3, u4, u5⟩, ⟨v1, v2, v3, v4, v5⟩⟩ := t9
  simp only at u1 u2 u3 u4 u5 v1 v2 v3 v4 v5 t94
  rw [T10_Ph q9 (u1.trans xs1) (v1.trans xs2) (u2.trans xb1) (v2.trans xb2),
    T11_Ph κ q9 (u1.trans xs1) (v1.trans xs2) (u2.trans xb1) (v2.trans xb2) (u5.trans n1)
      (v5.trans n2)]
  rw [t94, g4, t4]

/-- The whole row keeps the CLEAN records of `beforeSuppressAuth` on a
leaderless, reset-free pair. -/
theorem pipeline_45 (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hl' : l.core.reset_cmd = false) (hr' : r.core.reset_cmd = false) :
    (PPLLAuthF.pipeline hψ κ c l r).1.core.path4 =
      (PPLLAuthResetDrain.beforeSuppressAuth hψ κ c l r).1.core.path4 := by
  have hpf := PPLLAuthResetDrain.prefix_facts hψ κ c l r
  obtain ⟨b1, -, b3, -, b5, -, -⟩ := hpf
  rw [pipeline_post, ← beforeSuppress_eq]
  exact (F45.post_f hψ l r hl hr _ (b5.trans hl) (b1.trans hl') (b3.trans hr')).1.1

/-- The head's `path4` after the row is the one after `restPair`, on the probed pair. -/
theorem head4_rest (hψ : ψ > 0) (κ k : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (h : RowH ψ l r k) (x y : Bool) (hP : P0 hψ l r = (withProbe l x, withProbe r y)) :
    (PPLLAuthF.pipeline hψ κ c l r).1.core.path4 =
      (restPair hψ κ c (genSigAuth hψ κ (withProbe l x) (withProbe r y))).1.core.path4 := by
  rw [pipeline_45 hψ κ c l r h.ll h.rl h.lr h.rr, beforeSuppress_eq, hP]

/-- `restPair` keeps a non-command head `path4` on the first recruitment row. -/
theorem head4_gs (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (h : RowH ψ l r 0) (h3 : 3 ≤ ψ) (hlP : l.core.state = .produce) (hlb : l.core.path = .bot)
    (hl4 : isCmd l.core.path4 = false)
    (hrD : r.core.state ≠ .done) (hrP : r.core.state = .produce → r.core.path = .bot) (x y : Bool) :
    isCmd (restPair hψ κ c (genSigAuth hψ κ (withProbe l x) (withProbe r y))).1.core.path4 = false := by
  obtain ⟨g1, g2, g3, g4, -, g6⟩ := genSig_row hψ κ l r 0 h x y
  have G := gs_F0 hψ κ (withProbe l x) (withProbe r y) h3 hlP h.lk hl4 h.rk hrD hrP
  obtain ⟨s1, s2, -, s4, s5, -⟩ := gs_recruit hψ κ (withProbe l x) (withProbe r y) hlP hlb hrD hrP
    (by show r.core.label.val ≠ 0; rw [h.rk]; omega)
    (by show r.core.label.val ≠ ψ - 1; rw [h.rk]; omega)
    (by show l.core.label.val ≠ ψ - 1; rw [h.lk]; omega)
  rw [rest_Ph4 hψ κ c _ s1 s4 s2 s5 g1 g2 g3 g4 (by rw [g6]; omega) G.2]
  exact G.1

/-- **Head row of a running generation.** The head keeps a non-command `path4`. -/
theorem row_head4 (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (h : RowH ψ l r 0) (h3 : 3 ≤ ψ) (hlP : l.core.state = .produce) (hlb : l.core.path = .bot)
    (hl4 : isCmd l.core.path4 = false)
    (hrD : r.core.state ≠ .done) (hrP : r.core.state = .produce → r.core.path = .bot) :
    isCmd (PPLLAuthF.pipeline hψ κ c l r).1.core.path4 = false := by
  obtain ⟨x, y, hP⟩ := P0_frame hψ l r h.ll h.rl h.lab
  rw [head4_rest hψ κ 0 c l r h x y hP]
  exact head4_gs hψ κ c l r h h3 hlP hlb hl4 hrD hrP x y

end Head

/-! ## The block word -/

section Config
variable {n ψ : Nat}

/-- Forward invariant after `t` recruitment edges: GEN-DRAIN's `Fw` with origin
`j = 0`, and the head keeps a non-command `path4`. -/
def FI (ring : DirectedRing n) (ψ g : Nat) (C0 C : Fin n → AuthState ψ) (γ : ProvColor)
    (t : Nat) : Prop :=
  Fw ring ψ g C0 C 0 γ t ∧ isCmd (C (bcell ring ψ g 0)).core.path4 = false

/-- Backward invariant: cells `< s` are pathless producers of colour `γ` with no
`path2`, cell `s` is a settled `done` link, cells `> s` are settled `depart`
links; the head keeps a non-command `path4`. -/
def BI (ring : DirectedRing n) (ψ g : Nat) (C0 C : Fin n → AuthState ψ) (γ : ProvColor)
    (s : Nat) : Prop :=
  1 ≤ s ∧ s + 2 ≤ ψ ∧ Std C ∧ Out ring ψ g C0 C ∧
  isCmd (C (bcell ring ψ g 0)).core.path4 = false ∧
  (∀ k, k < s → (C (bcell ring ψ g k)).core.state = .produce ∧
    (C (bcell ring ψ g k)).core.path = .bot ∧ (C (bcell ring ψ g k)).ctrl_mark = γ ∧
    (C (bcell ring ψ g k)).core.path2 = none) ∧
  GC .done s γ (C (bcell ring ψ g s)) ∧
  (∀ k, s < k → k < ψ → GC .depart k γ (C (bcell ring ψ g k)))

/-- End of the word: every block cell is a settled `depart` link of colour `γ`. -/
def Fil (ring : DirectedRing n) (ψ g : Nat) (C0 : Fin n → AuthState ψ) (γ : ProvColor)
    (C : Fin n → AuthState ψ) : Prop :=
  Std C ∧ Out ring ψ g C0 C ∧ ∀ k, k < ψ → GC .depart k γ (C (bcell ring ψ g k))

/-- **Recruitment edge.** Edge `t` (`t+3 ≤ ψ`) recruits cell `t+1`. -/
theorem FI_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {t : Nat} {γ : ProvColor}
    (ht : t + 3 ≤ ψ) (hI : FI ring ψ g C0 C γ t) :
    RchL hp κ c ring g C 1 (fun D => FI ring ψ g C0 D γ (t + 1)) := by
  obtain ⟨⟨hS, hO, -, hM, hRt⟩, h4⟩ := hI
  apply RchL_mono hp κ c ring (Nat.le_refl _) _ (stepL_block hp κ c ring hg hS hO (k := t) (by omega))
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg (k := t) (by omega) hS
  obtain ⟨m1, m2, m3, -⟩ := hM t (Nat.zero_le _) (Nat.le_refl _)
  obtain ⟨r1, r2⟩ := hRt (t + 1) (by omega) (by omega)
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ :=
    row_recruit hp κ c _ _ t hR (by omega) m1 m2 r2 (bot_of_noPo r1)
  refine ⟨⟨hS', hO', fun k hk => absurd hk (Nat.not_lt_zero _), ?_, ?_⟩, ?_⟩
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
  · by_cases z : t = 0
    · subst z; rw [e1]
      exact row_head4 hp κ c _ _ hR (by omega) m1 m2 h4 r2 (bot_of_noPo r1)
    · rw [eo 0 (by omega) (Ne.symm z) (by omega)]; exact h4

/-- `d` recruitment edges. -/
theorem FI_iter (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 : Fin n → AuthState ψ} {γ : ProvColor} :
    ∀ (d t : Nat) (C : Fin n → AuthState ψ), t + d + 2 ≤ ψ →
      FI ring ψ g C0 C γ t → RchL hp κ c ring g C d (fun D => FI ring ψ g C0 D γ (t + d)) := by
  intro d
  induction d with
  | zero => intro t C _ hI; exact RchL_now hp κ c ring hI
  | succ d ih =>
    intro t C hd hI
    have h := RchL_bind hp κ c ring (FI_step hp κ c ring hg (by omega) hI)
      (fun D hD => ih (t + 1) D (by omega) hD)
    apply RchL_mono hp κ c ring (by omega) _ h
    intro D hD
    rwa [show t + 1 + d = t + (d + 1) by omega] at hD

/-- **Emission edge.** The last producer emits into the terminal cell. -/
theorem em_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {t : Nat} {γ : ProvColor}
    (ht : t + 2 = ψ) (h3 : 3 ≤ ψ) (hI : FI ring ψ g C0 C γ t) :
    RchL hp κ c ring g C 1 (fun D => BI ring ψ g C0 D γ t) := by
  obtain ⟨⟨hS, hO, -, hM, hRt⟩, h4⟩ := hI
  apply RchL_mono hp κ c ring (Nat.le_refl _) _ (stepL_block hp κ c ring hg hS hO (k := t) (by omega))
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg (k := t) (by omega) hS
  obtain ⟨m1, m2, m3, m4⟩ := hM t (Nat.zero_le _) (Nat.le_refl _)
  obtain ⟨r1, r2⟩ := hRt (t + 1) (by omega) (by omega)
  have F := row_fill hp κ c _ _ t hR m1 m2 (m4 (by omega)) (fun h => absurd h (by omega))
    (Or.inl ⟨by omega, r2, bot_of_noPo r1⟩)
  rw [if_neg (show ¬ t = 0 by omega), m3] at F
  refine ⟨by omega, by omega, hS', hO', ?_, ?_, ?_, ?_⟩
  · rw [eo 0 (by omega) (by omega) (by omega)]; exact h4
  · intro k hk
    rw [eo k (by omega) (by omega) (by omega)]
    obtain ⟨s1, s2, s3, s4⟩ := hM k (Nat.zero_le _) (by omega)
    exact ⟨s1, s2, s3, s4 (by omega)⟩
  · rw [e1]; exact F.1
  · intro k hk1 hk2
    obtain rfl : k = t + 1 := by omega
    rw [e2]; exact F.2

/-- **Backward edge.** The `done` link moves from `s+1` to `s ≥ 1`. -/
theorem back_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {s : Nat} {γ : ProvColor}
    (hs : 1 ≤ s) (hI : BI ring ψ g C0 C γ (s + 1)) :
    RchL hp κ c ring g C 1 (fun D => BI ring ψ g C0 D γ s) := by
  obtain ⟨_, hs2, hS, hO, h4, hM, hG, hRt⟩ := hI
  apply RchL_mono hp κ c ring (Nat.le_refl _) _ (stepL_block hp κ c ring hg hS hO (k := s) (by omega))
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg (k := s) (by omega) hS
  obtain ⟨m1, m2, m3, m4⟩ := hM s (by omega)
  obtain ⟨g1, ⟨y, g2⟩, -, g4, g5, g6, -, -⟩ := hG
  have F := row_fill hp κ c _ _ s hR m1 m2 m4 (fun h => absurd h (by omega))
    (Or.inr ⟨by omega, g1, ⟨y, g2⟩, g4, g5.trans m3.symm, g6.trans m3.symm⟩)
  rw [if_neg (show ¬ s = 0 by omega), m3] at F
  refine ⟨hs, by omega, hS', hO', ?_, ?_, ?_, ?_⟩
  · rw [eo 0 (by omega) (by omega) (by omega)]; exact h4
  · intro k hk; rw [eo k (by omega) (by omega) (by omega)]; exact hM k (by omega)
  · rw [e1]; exact F.1
  · intro k hk1 hk2
    by_cases a : k = s + 1
    · subst a; rw [e2]; exact F.2
    · rw [eo k hk2 (by omega) a]; exact hRt k (by omega) hk2

/-- `d` backward edges bring the `done` link from `1+d` to `1`. -/
theorem back_iter (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 : Fin n → AuthState ψ} {γ : ProvColor} :
    ∀ (d : Nat) (C : Fin n → AuthState ψ), BI ring ψ g C0 C γ (1 + d) →
      RchL hp κ c ring g C d (fun D => BI ring ψ g C0 D γ 1) := by
  intro d
  induction d with
  | zero => intro C hI; exact RchL_now hp κ c ring hI
  | succ d ih =>
    intro C hI
    have hI' : BI ring ψ g C0 C γ ((1 + d) + 1) := by
      rwa [show 1 + d + 1 = 1 + (d + 1) by omega]
    have h := RchL_bind hp κ c ring (back_step hp κ c ring hg (by omega) hI')
      (fun D hD => ih D hD)
    exact RchL_mono hp κ c ring (by omega) (fun _ h => h) h

/-- **Final edge.** The head joins: every block cell is a settled `depart` link. -/
theorem final_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) {C0 C : Fin n → AuthState ψ} {γ : ProvColor}
    (hI : BI ring ψ g C0 C γ 1) :
    RchL hp κ c ring g C 1 (Fil ring ψ g C0 γ) := by
  obtain ⟨_, hs2, hS, hO, h4, hM, hG, hRt⟩ := hI
  apply RchL_mono hp κ c ring (Nat.le_refl _) _ (stepL_block hp κ c ring hg hS hO (k := 0) (by omega))
  intro D ⟨hS', hO', e1, e2, eo⟩
  have hR := std_row ring hg (k := 0) (by omega) hS
  obtain ⟨m1, m2, m3, m4⟩ := hM 0 (by omega)
  obtain ⟨g1, ⟨y, g2⟩, -, g4, g5, g6, -, -⟩ := hG
  have F := row_fill hp κ c _ _ 0 hR m1 m2 m4 (fun _ => h4)
    (Or.inr ⟨by omega, g1, ⟨y, g2⟩, g4, g5.trans m3.symm, g6.trans m3.symm⟩)
  rw [if_pos rfl, m3] at F
  refine ⟨hS', hO', fun k hk => ?_⟩
  by_cases a : k = 0
  · subst a; rw [e1]; exact F.1
  · by_cases b : k = 0 + 1
    · subst b; rw [e2]; exact F.2
    · rw [eo k hk a b]; exact hRt k (by omega) hk

/-- The whole word: `ψ-2` recruitment edges, the emission edge, `ψ-3` backward
edges and the head edge, `2ψ-3` edges in all. -/
theorem genComplete_core (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    {g : Nat} (hg : g * ψ + ψ ≤ n) (h3 : 3 ≤ ψ) {C0 C : Fin n → AuthState ψ} {γ : ProvColor}
    (hI : FI ring ψ g C0 C γ 0) :
    RchL hp κ c ring g C (2 * ψ - 3) (Fil ring ψ g C0 γ) := by
  have h1 := FI_iter hp κ c ring hg (ψ - 2) 0 C (by omega) hI
  have h2 := RchL_bind hp κ c ring h1
    (fun D hD => em_step hp κ c ring hg (t := 0 + (ψ - 2)) (by omega) h3 hD)
  have h3' := RchL_bind hp κ c ring h2 (fun D hD => back_iter hp κ c ring hg (ψ - 3) D
    (by rwa [show 1 + (ψ - 3) = 0 + (ψ - 2) by omega]))
  have h4 := RchL_bind hp κ c ring h3' (fun D hD => final_step hp κ c ring hg hD)
  exact RchL_mono hp κ c ring (by omega) (fun _ h => h) h4

end Config

/-! ## Headline -/

section Headline
variable {n ψ : Nat}

/-- Number of cells of block `g` that carry a main path (as in
`PPLLAuthWaitReadyPsi2.Npath`). -/
def Npath (ring : DirectedRing n) (ψ g : Nat) (C : Fin n → AuthState ψ) : Nat :=
  S (fun k => if (C (bcell ring ψ g k)).core.path = .bot then 0 else 1) ψ

/-- A 0/1 sum whose first term is `0` is at most `m-1`. -/
theorem S_head0 (f : Nat → Nat) : ∀ m, 1 ≤ m → (∀ i, i < m → f i ≤ 1) → f 0 = 0 →
    S f m ≤ m - 1 := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _ hf h0
    show S f m + f m ≤ m + 1 - 1
    by_cases z : m = 0
    · subst z
      have : S f 0 = 0 := rfl
      rw [h0]; omega
    · have := ih (by omega) (fun i hi => hf i (by omega)) h0
      have := hf m (by omega)
      omega

/-- A sum of ones. -/
theorem S_one (f : Nat → Nat) : ∀ m, (∀ i, i < m → f i = 1) → S f m = m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hf
    show S f m + f m = m + 1
    rw [ih (fun i hi => hf i (by omega)), hf m (by omega)]

/-- **Generation completion, block `g`, `ψ ≥ 3`.**
Leaderless, `reset_cmd = false`, perfect labels, `echo` and `wait` arbitrary.
The head of block `g` is a pathless producer whose `path4` is not a CLEAN
command; every other block cell is not `done`, and pathless if it is a
producer (so existing aligned or misaligned paths are allowed).  Then a word
of `2ψ-3` internal edges of block `g` (`0..ψ-2`, then `ψ-3..0`) reaches a
leader, or a configuration where every block cell `k` is
`SerialPlusCell _ k γ` with `γ` the head's initial `ctrl_mark`: the block
carries `ψ` main paths (at most `ψ-1` before) and no `produce`/`done`.
The word only schedules edges `gψ ≤ e ≤ gψ+ψ-2` and fixes every cell outside
the block. -/
theorem genComplete_block (hp : ψ > 0) (h3 : 3 ≤ ψ) (κ : Nat) (c : PPLLAuthF.Cfg)
    (ring : DirectedRing n) (g : Nat) (hg : g * ψ + ψ ≤ n) (C : Fin n → AuthState ψ)
    (hL : ∀ i, (C i).core.leader = false) (hR : ∀ i, (C i).core.reset_cmd = false)
    (hPL : ∀ i, (C i).core.label.val = i.val % ψ)
    (hhP : (C (bcell ring ψ g 0)).core.state = .produce)
    (hhb : (C (bcell ring ψ g 0)).core.path = .bot)
    (hh4 : isCmd (C (bcell ring ψ g 0)).core.path4 = false)
    (hB : ∀ k, 1 ≤ k → k < ψ → (C (bcell ring ψ g k)).core.state ≠ .done ∧
      ((C (bcell ring ψ g k)).core.state = .produce → (C (bcell ring ψ g k)).core.path = .bot)) :
    ∃ w : List (Fin n), w.length ≤ 2 * ψ - 3 ∧
      (∀ e ∈ w, g * ψ ≤ e.val ∧ e.val ≤ g * ψ + ψ - 2) ∧
      (∀ i : Fin n, (i.val < g * ψ ∨ g * ψ + ψ ≤ i.val) → authRun hp κ c ring C w i = C i) ∧
      ((∃ i, (authRun hp κ c ring C w i).core.leader = true) ∨
        ((∀ k, k < ψ → PPLLAuthSerialDischarge.SerialPlusCell
            (authRun hp κ c ring C w (bcell ring ψ g k)) k (C (bcell ring ψ g 0)).ctrl_mark) ∧
         Npath ring ψ g C ≤ ψ - 1 ∧ Npath ring ψ g (authRun hp κ c ring C w) = ψ ∧
         Npath ring ψ g C < Npath ring ψ g (authRun hp κ c ring C w) ∧
         ∀ k, k < ψ →
           (authRun hp κ c ring C w (bcell ring ψ g k)).core.state ≠ .produce ∧
           (authRun hp κ c ring C w (bcell ring ψ g k)).core.state ≠ .done)) := by
  have hS : Std C := fun i => ⟨hL i, hR i, hPL i⟩
  have hI : FI ring ψ g C C (C (bcell ring ψ g 0)).ctrl_mark 0 := by
    refine ⟨⟨hS, fun _ _ => rfl, fun k hk => absurd hk (Nat.not_lt_zero _), ?_, ?_⟩, hh4⟩
    · intro k _ hk
      obtain rfl : k = 0 := by omega
      exact ⟨hhP, hhb, rfl, fun h => absurd h (Nat.lt_irrefl _)⟩
    · intro k hk1 hk2
      obtain ⟨d, p⟩ := hB k hk1 hk2
      exact ⟨fun ⟨a, b⟩ => b (p a), d⟩
  obtain ⟨w, hw, he, hfin⟩ := genComplete_core hp κ c ring hg h3 hI
  have loc := inBlk_local hp κ c ring hg C w he
  refine ⟨w, hw, loc.1, loc.2, ?_⟩
  rcases hfin with hLd | ⟨_, _, hG⟩
  · exact Or.inl hLd
  · right
    have hN0 : Npath ring ψ g C ≤ ψ - 1 := by
      apply S_head0 _ ψ (by omega)
      · intro i _; split <;> omega
      · show (if (C (bcell ring ψ g 0)).core.path = .bot then 0 else 1) = 0
        rw [if_pos hhb]
    have hN1 : Npath ring ψ g (authRun hp κ c ring C w) = ψ := by
      apply S_one
      intro i hi
      obtain ⟨-, ⟨x, p⟩, -⟩ := hG i hi
      show (if (authRun hp κ c ring C w (bcell ring ψ g i)).core.path = .bot then 0 else 1) = 1
      rw [if_neg (by rw [p]; nofun)]
    refine ⟨fun k hk => ?_, hN0, hN1, by omega, fun k hk => ?_⟩
    · obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hG k hk
      exact ⟨s3, s2, s1, s4, s5, s6, s7, s8⟩
    · obtain ⟨s1, -⟩ := hG k hk
      rw [s1]; exact ⟨nofun, nofun⟩

end Headline

#print axioms genComplete_block

end PPLLAuthGenComplete
