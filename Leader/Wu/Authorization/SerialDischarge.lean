import Leader.Wu.Authorization.BitFrozenClosure

/-!
# SERIAL-DISCHARGE for `authFplusmcc` (Q20610)

Headline `serialPlus_discharge`: for `ψ ≥ 2`, `ψ ∣ n`, `1 < n`, a leaderless ring with perfect
labels, no `reset_cmd`, and every block SerialPlus (Q20610 §1 serial with `p`/`p_carry`
arbitrary; `echo` and the other auxiliary fields arbitrary), some physical word of length at
most `2ψ² + 2ψ - 1` drives `authRun` under `authFplusmcc` to a leader or a deleted main path.
`serial_discharge` is the exact Q20610 §1 statement (`p = p_carry = false`).

Route (Q20610 §2): the word P sets up a session between block 0 (source) and block 1
(target; for `m = 1` the block compares with itself), W emits the BEQ tokens, and each
round `j` moves A2 left and A1 right.  On a mismatch the landing emits A4 (walks right) or
A3 (walks left), which is applied at a terminal cell, leaving it in `eliminate_signal`; one
more service of the incoming edge of that cell deletes a main path
(`pipeline_HP_of_elim`).  Any interaction may also end early: a hole, a leader, or a
DISAPPEAR `eliminate_signal` responder (same exit).

Proof layers: stage decomposition and frames; hole persistence through the pipeline;
SIGMOVE as token transfer; inertness of the wave stages on the settled cell kinds;
per-interaction `midS` outcomes; ring-level descriptor invariants (`Inv`, `RD`); token
walks; rounds; set-up; headline.
-/

namespace PPLLAuthSerialDischarge
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
  PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF PPLLAuthResetDrain
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Stage decomposition of the AuthF pipeline -/

section Decomp
variable {ψ : Nat}

/-- Stages before SIGMOVE: P′ (with probe wall), GENSIG, CLEAN, source release,
ELIMINATE_SIG. -/
def pre (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := lift2 (pPsiProbeWall hψ) l r
  let q := genSigAuth hψ κ q.1 q.2
  let q := cleanSourceAuth hψ c q.1 q.2
  let q := lift2Life (releaseSource hψ) q.1 q.2
  lift2 (eliminateSig hψ) q.1 q.2

/-- The six stages between SIGMOVE and the comparison lifecycle. -/
def quietStages (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := (liftLife dropStale l, liftLife dropStale r)
  let q := preCheckResetAuth q.1 q.2
  let q := (liftLife normalizeReady q.1, liftLife normalizeReady q.2)
  let q := checkSourceAuth hψ c q.1 q.2
  let q := disappearAuth hψ q.1 q.2
  repairAuth q.1 q.2

/-- SIGMOVE through the comparison lifecycle. -/
def midS (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := moveSourceAuth hψ c l r
  let q := quietStages hψ c q.1 q.2
  compareLifecycleAuth κ q.1 q.2

/-- Algorithm 14, K4, WRITE and the conservation guard. -/
def post (hψ : ψ > 0) (l r : AuthState ψ) (q : AuthState ψ × AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let q := suppressSigResetKillAuth hψ q.1 q.2
  let q := lift2 (k4Kernel hψ) q.1 q.2
  let q := lift2 (writeWithBundle hψ) q.1 q.2
  conserveAuth l r q

theorem pipeline_eq (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    pipeline hψ κ c l r =
      post hψ l r (midS hψ κ c (pre hψ κ c l r).1 (pre hψ κ c l r).2) := rfl

end Decomp

/-! ## Frames -/

section Frames
variable {ψ : Nat}

/-- Core fields the comparison route reads (besides provenance marks). -/
def cp (u : AgentState ψ) :=
  (u.state, u.path, u.path2, u.label, u.leader, u.reset_cmd, u.p_carry, u.bit)

theorem cp_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    cp (if p then a else b) = if p then cp a else cp b := by split <;> rfl
theorem pfst_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
theorem psnd_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl

theorem state_ite' (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).state = if p then a.state else b.state := by split <;> rfl
theorem path_ite' (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by split <;> rfl
theorem path2_ite' (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path2 = if p then a.path2 else b.path2 := by split <;> rfl
theorem label_ite' (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).label = if p then a.label else b.label := by split <;> rfl
theorem leader_ite' (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).leader = if p then a.leader else b.leader := by split <;> rfl
theorem reset_cmd_ite' (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).reset_cmd = if p then a.reset_cmd else b.reset_cmd := by split <;> rfl
theorem p_carry_ite' (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).p_carry = if p then a.p_carry else b.p_carry := by split <;> rfl
theorem bit_ite' (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).bit = if p then a.bit else b.bit := by split <;> rfl

theorem wait_cp (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    cp (waitSaturated hψ κ l r).1 = cp l ∧ cp (waitSaturated hψ κ l r).2 = cp r := by
  simp only [waitSaturated, waitSaturatedPrepare, waitSaturatedCarry, waitSaturatedReset,
    waitSaturatedFinish]
  simp only [pfst_ite, psnd_ite, cp, state_ite', path_ite', path2_ite', label_ite', leader_ite',
    reset_cmd_ite', p_carry_ite', bit_ite', ite_self, and_self]

/-- Every field of the route view, on the cell with its marks. -/
def SameF (u v : AuthState ψ) : Prop :=
  cp v.core = cp u.core ∧ v.path_mark = u.path_mark ∧ v.ctrl_mark = u.ctrl_mark ∧
    v.path2_scope = u.path2_scope ∧ v.path2_mark = u.path2_mark

theorem SameF.refl (u : AuthState ψ) : SameF u u := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem SameF.trans {u v w : AuthState ψ} (h1 : SameF u v) (h2 : SameF v w) : SameF u w :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.trans h1.2.2.2.2⟩


theorem SameF.of_cp {u v : AuthState ψ} (h : cp v.core = cp u.core) (h1 : v.path_mark = u.path_mark)
    (h2 : v.ctrl_mark = u.ctrl_mark) (h3 : v.path2_scope = u.path2_scope)
    (h4 : v.path2_mark = u.path2_mark) : SameF u v := ⟨h, h1, h2, h3, h4⟩

theorem SameF.state {u v : AuthState ψ} (h : SameF u v) : v.core.state = u.core.state :=
  congrArg (fun x => x.1) h.1
theorem SameF.path {u v : AuthState ψ} (h : SameF u v) : v.core.path = u.core.path :=
  congrArg (fun x => x.2.1) h.1
theorem SameF.path2 {u v : AuthState ψ} (h : SameF u v) : v.core.path2 = u.core.path2 :=
  congrArg (fun x => x.2.2.1) h.1
theorem SameF.label {u v : AuthState ψ} (h : SameF u v) : v.core.label = u.core.label :=
  congrArg (fun x => x.2.2.2.1) h.1
theorem SameF.leader {u v : AuthState ψ} (h : SameF u v) : v.core.leader = u.core.leader :=
  congrArg (fun x => x.2.2.2.2.1) h.1
theorem SameF.reset {u v : AuthState ψ} (h : SameF u v) : v.core.reset_cmd = u.core.reset_cmd :=
  congrArg (fun x => x.2.2.2.2.2.1) h.1
theorem SameF.pc {u v : AuthState ψ} (h : SameF u v) : v.core.p_carry = u.core.p_carry :=
  congrArg (fun x => x.2.2.2.2.2.2.1) h.1
theorem SameF.bit {u v : AuthState ψ} (h : SameF u v) : v.core.bit = u.core.bit :=
  congrArg (fun x => x.2.2.2.2.2.2.2) h.1

/-! ### P′ -/

theorem pPsi_same (hψ : ψ > 0) (l r : AuthState ψ) (hl : l.core.leader = false)
    (hr : r.core.leader = false)
    (hnext : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) :
    SameF l (lift2 (pPsiProbeWall hψ) l r).1 ∧ SameF r (lift2 (pPsiProbeWall hψ) l r).2 := by
  by_cases hp : r.core.probe = true <;>
    simp [SameF, cp, lift2, pPsiProbeWall, pPsi, hl, hr, hnext, hp]

/-! ### GENSIG on occupied non-generation cells -/

theorem genSig_same (hψ : ψ > 0) (κ : Nat) (l r : AuthState ψ) (hl : l.core.leader = false)
    (hlp : l.core.path ≠ .bot) (hls : l.core.state ≠ .produce) (hld : l.core.state ≠ .done)
    (hrs : r.core.state ≠ .produce) :
    SameF l (genSigAuth hψ κ l r).1 ∧ SameF r (genSigAuth hψ κ l r).2 := by
  have hw := wait_cp hψ κ l.core r.core
  unfold genSigAuth lift2
  generalize waitSaturated hψ κ l.core r.core = w at hw
  obtain ⟨wl, wr⟩ := w
  simp only [cp, Prod.mk.injEq] at hw
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩⟩ := hw
  simp [AuthState.st, a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8, hl, hlp, hls, hld, hrs,
    SameF, cp]

/-! ### CLEAN: only records, record marks, and deletion of a main path -/

/-- `v` agrees with `u` on the route view, except that its main path may be deleted. -/
def SameOrHole (u v : AuthState ψ) : Prop :=
  (v.core.path = .bot ∧ v.core.state = u.core.state) ∨ SameF u v

theorem genConnect_same (u : AuthState ψ) : SameF u (genConnectAuth u) := by
  unfold genConnectAuth
  split <;> simp [SameF, cp, cleanSigGenConnect, *] <;> split <;> simp_all <;> split <;> simp_all

theorem step3_same (nbr mc : Bool) (l r : AuthState ψ) :
    SameF l (step3Auth nbr mc l r).1 ∧ SameF r (step3Auth nbr mc l r).2 := by
  unfold step3Auth
  repeat' split
  all_goals simp [SameF, cp]

theorem step4_same (nbr mc : Bool) (l r : AuthState ψ) :
    SameF l (step4Auth nbr mc l r).1 ∧ SameF r (step4Auth nbr mc l r).2 := by
  unfold step4Auth
  repeat' split
  all_goals simp [SameF, cp]

theorem step5_same (hψ : ψ > 0) (l r : AuthState ψ) :
    SameF l (step5Auth hψ l r).1 ∧ SameF r (step5Auth hψ l r).2 := by
  unfold step5Auth
  repeat' split
  all_goals simp [SameF, cp]

theorem step6_same (hψ : ψ > 0) (l r : AuthState ψ) :
    SameF l (step6Auth hψ l r).1 ∧ SameF r (step6Auth hψ l r).2 := by
  unfold step6Auth
  repeat' split
  all_goals simp [SameF, cp]

theorem cleanApply_cases (u : AuthState ψ) : SameOrHole u (cleanApplyAuth u) := by
  unfold cleanApplyAuth SameOrHole
  rcases hp : u.core.path with _ | ⟨pl, pb⟩
  · exact Or.inr (SameF.refl u)
  · rcases h4 : u.core.path4 with _ | ⟨l4, b4⟩ <;> rcases h5 : u.core.path5 with _ | ⟨l5, b5⟩ <;>
      simp only [h4, h5] <;> (repeat' split) <;> simp_all [SameF, cp]

theorem SameOrHole.of_same {u v w : AuthState ψ} (h1 : SameF u v) (h2 : SameOrHole v w) :
    SameOrHole u w := by
  rcases h2 with h | h
  · exact Or.inl ⟨h.1, h.2.trans h1.state⟩
  · exact Or.inr (h1.trans h)

theorem cleanSource_cases (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    SameOrHole l (cleanSourceAuth hψ c l r).1 ∧ SameOrHole r (cleanSourceAuth hψ c l r).2 := by
  unfold cleanSourceAuth
  dsimp only
  have g1 := genConnect_same l
  have g2 := genConnect_same r
  generalize genConnectAuth l = l1 at g1
  generalize genConnectAuth r = r1 at g2
  have h3 := step3_same c.cleanNbr c.markClean l1 r1
  generalize step3Auth c.cleanNbr c.markClean l1 r1 = q3 at h3
  obtain ⟨l3, r3⟩ := q3
  have h4 := step4_same c.cleanNbr c.markClean l3 r3
  generalize step4Auth c.cleanNbr c.markClean l3 r3 = q4 at h4
  obtain ⟨l4, r4⟩ := q4
  have h5 : SameF l4 (if isCmd l4.core.path4 = true then
      (l4, { r4 with core := { r4.core with path4 := none } }) else step5Auth hψ l4 r4).1 ∧
      SameF r4 (if isCmd l4.core.path4 = true then
      (l4, { r4 with core := { r4.core with path4 := none } }) else step5Auth hψ l4 r4).2 := by
    split
    · exact ⟨SameF.refl _, by simp [SameF, cp]⟩
    · exact step5_same hψ l4 r4
  generalize (if isCmd l4.core.path4 = true then
      (l4, { r4 with core := { r4.core with path4 := none } }) else step5Auth hψ l4 r4) = q5 at h5
  obtain ⟨l5, r5⟩ := q5
  have h6 : SameF l5 (if isCmd r5.core.path5 = true then
      ({ l5 with core := { l5.core with path5 := none } }, r5) else step6Auth hψ l5 r5).1 ∧
      SameF r5 (if isCmd r5.core.path5 = true then
      ({ l5 with core := { l5.core with path5 := none } }, r5) else step6Auth hψ l5 r5).2 := by
    split
    · exact ⟨by simp [SameF, cp], SameF.refl _⟩
    · exact step6_same hψ l5 r5
  generalize (if isCmd r5.core.path5 = true then
      ({ l5 with core := { l5.core with path5 := none } }, r5) else step6Auth hψ l5 r5) = q6 at h6
  obtain ⟨l6, r6⟩ := q6
  dsimp only at h3 h4 h5 h6 ⊢
  exact ⟨SameOrHole.of_same (g1.trans (h3.1.trans (h4.1.trans (h5.1.trans h6.1))))
      (cleanApply_cases l6),
    SameOrHole.of_same (g2.trans (h3.2.trans (h4.2.trans (h5.2.trans h6.2))))
      (cleanApply_cases r6)⟩

/-! ### Source release and ELIMINATE_SIG -/

theorem release_id (hψ : ψ > 0) (l r : AuthState ψ) (hr : r.core.state ≠ .done) :
    lift2Life (releaseSource hψ) l r = (l, r) := by
  simp [lift2Life, releaseSource, hr]

theorem elim_id (hψ : ψ > 0) (l r : AuthState ψ) (hr : r.core.state ≠ .eliminate_signal) :
    lift2 (eliminateSig hψ) l r = (l, r) := by
  simp [lift2, eliminateSig, hr]

theorem elim_hole (hψ : ψ > 0) (l r : AuthState ψ) (hr : r.core.state = .eliminate_signal) :
    (lift2 (eliminateSig hψ) l r).2.core.path = .bot := by
  simp [lift2, eliminateSig, hr]

theorem elim_left_path (hψ : ψ > 0) (l r : AuthState ψ) :
    (lift2 (eliminateSig hψ) l r).1.core.path = l.core.path := by
  unfold lift2 eliminateSig; split <;> (try split) <;> rfl

/-- The prefix before SIGMOVE: a main path is deleted, or both cells keep the route view. -/
theorem pre_frame (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hnext : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlp : l.core.path ≠ .bot) (hls : l.core.state ≠ .produce) (hld : l.core.state ≠ .done)
    (hrs : r.core.state ≠ .produce) (hrd : r.core.state ≠ .done) :
    (pre hψ κ c l r).1.core.path = .bot ∨ (pre hψ κ c l r).2.core.path = .bot ∨
      (SameF l (pre hψ κ c l r).1 ∧ SameF r (pre hψ κ c l r).2) := by
  unfold pre
  dsimp only
  have p1 := pPsi_same hψ l r hl hr hnext
  generalize lift2 (pPsiProbeWall hψ) l r = q1 at p1
  obtain ⟨a1, b1⟩ := q1
  obtain ⟨p1a, p1b⟩ := p1
  have p2 := genSig_same hψ κ a1 b1 (by rw [p1a.leader]; exact hl) (by rw [p1a.path]; exact hlp)
    (by rw [p1a.state]; exact hls) (by rw [p1a.state]; exact hld) (by rw [p1b.state]; exact hrs)
  generalize genSigAuth hψ κ a1 b1 = q2 at p2
  obtain ⟨a2, b2⟩ := q2
  obtain ⟨p2a, p2b⟩ := p2
  have p3 := cleanSource_cases hψ c a2 b2
  generalize cleanSourceAuth hψ c a2 b2 = q3 at p3
  obtain ⟨a3, b3⟩ := q3
  obtain ⟨p3a, p3b⟩ := p3
  dsimp only at p3a p3b ⊢
  have sb : b3.core.state = r.core.state := by
    rcases p3b with h | h
    · rw [h.2, p2b.state, p1b.state]
    · rw [h.state, p2b.state, p1b.state]
  rw [release_id hψ a3 b3 (by rw [sb]; exact hrd)]
  by_cases hE : b3.core.state = .eliminate_signal
  · exact Or.inr (Or.inl (elim_hole hψ a3 b3 hE))
  · rw [elim_id hψ a3 b3 hE]
    dsimp only
    rcases p3a with h | h
    · exact Or.inl h.1
    rcases p3b with h' | h'
    · exact Or.inr (Or.inl h'.1)
    exact Or.inr (Or.inr ⟨p1a.trans (p2a.trans h), p1b.trans (p2b.trans h')⟩)

/-! ### WRITE frames the route fields (after `PPLLAstraCarry`) -/

def WFrame {ψ : Nat} (a b : AgentState ψ) : Prop :=
  a.state = b.state ∧ a.path = b.path ∧ a.path2 = b.path2 ∧ a.p_carry = b.p_carry ∧ a.label = b.label

theorem wwriteActionApplyOverwrite_frame {ψ : Nat} (u : AgentState ψ) :
    WFrame (writeActionApplyOverwrite u) u := by
  unfold WFrame writeActionApplyOverwrite
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem wwriteActionApplyMoveFlip_frame {ψ : Nat} (u : AgentState ψ) :
    WFrame (writeActionApplyMoveFlip u) u := by
  unfold WFrame writeActionApplyMoveFlip
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem wmoveWsigCheckLast_frame {ψ : Nat} (u : AgentState ψ) :
    WFrame (moveWsigCheckLast u) u := by
  unfold WFrame moveWsigCheckLast
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem wwriteSeqSetWriteReady_frame {ψ : Nat} (u : AgentState ψ) :
    WFrame (writeSeqSetWriteReady u) u := by
  unfold WFrame writeSeqSetWriteReady
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem wwriteSeqCheckBit_frame {ψ : Nat} (u : AgentState ψ) :
    WFrame (writeSeqCheckBit u) u := by
  unfold WFrame writeSeqCheckBit
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem wwriteSeqSetWriteAct_frame {ψ : Nat} (u : AgentState ψ) :
    WFrame (writeSeqSetWriteAct u) u := by
  cases hp : u.path3 <;> simp only [WFrame, writeSeqSetWriteAct, hp] <;>
    simp [state_ite', path_ite', path2_ite', p_carry_ite', label_ite', hp]

theorem wwriteSeqFinalR_frame {ψ : Nat} (u : AgentState ψ) :
    WFrame (writeSeqFinalR u) u := by
  unfold WFrame writeSeqFinalR
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem wmoveWsigCheckGenWs_frame {ψ : Nat} (l r : AgentState ψ) :
    WFrame (moveWsigCheckGenWs l r) r := by
  unfold WFrame moveWsigCheckGenWs
  repeat (first | constructor | rfl | split)
  all_goals simp

theorem wmoveWsigTransfer_frame {ψ : Nat} (l r : AgentState ψ) :
    WFrame (moveWsigTransfer l r).1 l ∧ WFrame (moveWsigTransfer l r).2 r := by
  cases hl : l.path3 <;> cases hr : r.path3 <;>
    simp only [WFrame, moveWsigTransfer, hl, hr] <;>
    simp only [pfst_ite, psnd_ite, state_ite', path_ite', path2_ite', p_carry_ite', label_ite', ite_self, and_self]

theorem wgroupInfo_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WFrame (groupInfo hψ l r).1 l ∧ WFrame (groupInfo hψ l r).2 r := by
  simp only [WFrame, groupInfo]
  simp only [pfst_ite, psnd_ite, state_ite', path_ite', path2_ite', p_carry_ite', label_ite', ite_self, and_self]

theorem wgensigWriteseq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WFrame (gensigWriteseq hψ l r).1 l ∧ WFrame (gensigWriteseq hψ l r).2 r := by
  simp only [WFrame, gensigWriteseq]
  simp only [pfst_ite, psnd_ite, state_ite', path_ite', path2_ite', p_carry_ite', label_ite', ite_self, and_self]

theorem wwriteAction_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WFrame (writeAction hψ l r).1 l ∧ WFrame (writeAction hψ l r).2 r := by
  simp only [WFrame, writeAction]
  simp only [pfst_ite, psnd_ite, state_ite', path_ite', path2_ite', p_carry_ite', label_ite', ite_self, and_self, (wwriteActionApplyOverwrite_frame _).1, (wwriteActionApplyOverwrite_frame _).2.1, (wwriteActionApplyOverwrite_frame _).2.2.1, (wwriteActionApplyOverwrite_frame _).2.2.2.1, (wwriteActionApplyOverwrite_frame _).2.2.2.2, (wwriteActionApplyMoveFlip_frame _).1, (wwriteActionApplyMoveFlip_frame _).2.1, (wwriteActionApplyMoveFlip_frame _).2.2.1, (wwriteActionApplyMoveFlip_frame _).2.2.2.1, (wwriteActionApplyMoveFlip_frame _).2.2.2.2]

theorem wmoveWsig_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WFrame (moveWsig hψ l r).1 l ∧ WFrame (moveWsig hψ l r).2 r := by
  simp only [WFrame, moveWsig]
  simp only [pfst_ite, psnd_ite, state_ite', path_ite', path2_ite', p_carry_ite', label_ite', ite_self, and_self, (wmoveWsigCheckGenWs_frame _ _).1, (wmoveWsigCheckGenWs_frame _ _).2.1, (wmoveWsigCheckGenWs_frame _ _).2.2.1, (wmoveWsigCheckGenWs_frame _ _).2.2.2.1, (wmoveWsigCheckGenWs_frame _ _).2.2.2.2, (wmoveWsigCheckLast_frame _).1, (wmoveWsigCheckLast_frame _).2.1, (wmoveWsigCheckLast_frame _).2.2.1, (wmoveWsigCheckLast_frame _).2.2.2.1, (wmoveWsigCheckLast_frame _).2.2.2.2, (wmoveWsigTransfer_frame _ _).1.1, (wmoveWsigTransfer_frame _ _).1.2.1, (wmoveWsigTransfer_frame _ _).1.2.2.1, (wmoveWsigTransfer_frame _ _).1.2.2.2.1, (wmoveWsigTransfer_frame _ _).1.2.2.2.2, (wmoveWsigTransfer_frame _ _).2.1, (wmoveWsigTransfer_frame _ _).2.2.1, (wmoveWsigTransfer_frame _ _).2.2.2.1, (wmoveWsigTransfer_frame _ _).2.2.2.2.1, (wmoveWsigTransfer_frame _ _).2.2.2.2.2]


theorem wwriteSeq_frame {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    WFrame (writeSeq hψ l r).1 l ∧ WFrame (writeSeq hψ l r).2 r := by
  simp only [WFrame, writeSeq, writeSeqThroughPrepare, writeSeqAfterPrepare,
    writeSeqLeaderMove, writeSeqGenerate, writeSeqPrepare, writeSeqReady,
    writeSeqCompare, writeSeqCommands]
  simp only [pfst_ite, psnd_ite, state_ite', path_ite', path2_ite', p_carry_ite', label_ite', ite_self, and_self, (wgroupInfo_frame _ _ _).1.1, (wgroupInfo_frame _ _ _).1.2.1, (wgroupInfo_frame _ _ _).1.2.2.1, (wgroupInfo_frame _ _ _).1.2.2.2.1, (wgroupInfo_frame _ _ _).1.2.2.2.2, (wgroupInfo_frame _ _ _).2.1, (wgroupInfo_frame _ _ _).2.2.1, (wgroupInfo_frame _ _ _).2.2.2.1, (wgroupInfo_frame _ _ _).2.2.2.2.1, (wgroupInfo_frame _ _ _).2.2.2.2.2, (wgensigWriteseq_frame _ _ _).1.1, (wgensigWriteseq_frame _ _ _).1.2.1, (wgensigWriteseq_frame _ _ _).1.2.2.1, (wgensigWriteseq_frame _ _ _).1.2.2.2.1, (wgensigWriteseq_frame _ _ _).1.2.2.2.2, (wgensigWriteseq_frame _ _ _).2.1, (wgensigWriteseq_frame _ _ _).2.2.1, (wgensigWriteseq_frame _ _ _).2.2.2.1, (wgensigWriteseq_frame _ _ _).2.2.2.2.1, (wgensigWriteseq_frame _ _ _).2.2.2.2.2, (wwriteAction_frame _ _ _).1.1, (wwriteAction_frame _ _ _).1.2.1, (wwriteAction_frame _ _ _).1.2.2.1, (wwriteAction_frame _ _ _).1.2.2.2.1, (wwriteAction_frame _ _ _).1.2.2.2.2, (wwriteAction_frame _ _ _).2.1, (wwriteAction_frame _ _ _).2.2.1, (wwriteAction_frame _ _ _).2.2.2.1, (wwriteAction_frame _ _ _).2.2.2.2.1, (wwriteAction_frame _ _ _).2.2.2.2.2, (wmoveWsig_frame _ _ _).1.1, (wmoveWsig_frame _ _ _).1.2.1, (wmoveWsig_frame _ _ _).1.2.2.1, (wmoveWsig_frame _ _ _).1.2.2.2.1, (wmoveWsig_frame _ _ _).1.2.2.2.2, (wmoveWsig_frame _ _ _).2.1, (wmoveWsig_frame _ _ _).2.2.1, (wmoveWsig_frame _ _ _).2.2.2.1, (wmoveWsig_frame _ _ _).2.2.2.2.1, (wmoveWsig_frame _ _ _).2.2.2.2.2, (wwriteSeqSetWriteReady_frame _).1, (wwriteSeqSetWriteReady_frame _).2.1, (wwriteSeqSetWriteReady_frame _).2.2.1, (wwriteSeqSetWriteReady_frame _).2.2.2.1, (wwriteSeqSetWriteReady_frame _).2.2.2.2, (wwriteSeqCheckBit_frame _).1, (wwriteSeqCheckBit_frame _).2.1, (wwriteSeqCheckBit_frame _).2.2.1, (wwriteSeqCheckBit_frame _).2.2.2.1, (wwriteSeqCheckBit_frame _).2.2.2.2, (wwriteSeqSetWriteAct_frame _).1, (wwriteSeqSetWriteAct_frame _).2.1, (wwriteSeqSetWriteAct_frame _).2.2.1, (wwriteSeqSetWriteAct_frame _).2.2.2.1, (wwriteSeqSetWriteAct_frame _).2.2.2.2, (wwriteSeqFinalR_frame _).1, (wwriteSeqFinalR_frame _).2.1, (wwriteSeqFinalR_frame _).2.2.1, (wwriteSeqFinalR_frame _).2.2.2.1, (wwriteSeqFinalR_frame _).2.2.2.2]

/-! ### Algorithm 14, K4, WRITE, conservation -/

theorem kernel_frame (hψ : ψ > 0) (l r : AgentState ψ) :
    WFrame (k4Kernel hψ l r).1 l ∧ WFrame (k4Kernel hψ l r).2 r ∧
      (l.leader = false → (k4Kernel hψ l r).1.leader = false) ∧
      (k4Kernel hψ l r).2.leader = r.leader := by
  simp only [WFrame, k4Kernel, k3Kernel, eliminateLeadersNoCollisionFire, absorbAnyMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [pfst_ite, psnd_ite, state_ite', path_ite', path2_ite', p_carry_ite', label_ite',
      ite_self, and_self]
  · simp only [pfst_ite, psnd_ite, state_ite', path_ite', path2_ite', p_carry_ite', label_ite',
      ite_self, and_self]
  · intro h; simp [h, pfst_ite, psnd_ite, leader_ite']
  · simp only [pfst_ite, psnd_ite, leader_ite', ite_self]

def MarksEq (u v : AuthState ψ) : Prop :=
  v.path_mark = u.path_mark ∧ v.ctrl_mark = u.ctrl_mark ∧ v.path2_scope = u.path2_scope ∧
    v.path2_mark = u.path2_mark

theorem suppress_frame (hψ : ψ > 0) (l r : AuthState ψ) (hl : l.core.leader = false)
    (h1 : l.core.reset_cmd = false) (h2 : r.core.reset_cmd = false) :
    WFrame (suppressSigResetKillAuth hψ l r).1.core l.core ∧
      WFrame (suppressSigResetKillAuth hψ l r).2.core r.core ∧
      MarksEq l (suppressSigResetKillAuth hψ l r).1 ∧ MarksEq r (suppressSigResetKillAuth hψ l r).2 ∧
      (suppressSigResetKillAuth hψ l r).1.core.leader = l.core.leader ∧
      (suppressSigResetKillAuth hψ l r).2.core.leader = r.core.leader := by
  unfold suppressSigResetKillAuth lift2
  simp only [suppressSigStart, suppressSigMoveReset, suppressSigTerminal, suppressSigFinish,
    hl, h1, h2]
  by_cases he : r.core.echo = true <;>
    simp [suppressSigEcho, he, h1, h2, hl, WFrame, MarksEq]

theorem conserve_id (l r : AuthState ψ) (hl : l.core.leader = false) (hr : r.core.leader = false)
    (q : AuthState ψ × AuthState ψ) : conserveAuth l r q = q := by
  simp [conserveAuth, conserve, hl, hr]

theorem wwb_frame (hψ : ψ > 0) (l r : AgentState ψ) :
    WFrame (writeWithBundle hψ l r).1 l ∧ WFrame (writeWithBundle hψ l r).2 r := by
  have h := wwriteSeq_frame hψ l r
  unfold writeWithBundle
  split
  · simp only [WFrame] at h ⊢; exact h
  · exact h

theorem wwb_leader' (hψ : ψ > 0) (l r : AgentState ψ) :
    (writeWithBundle hψ l r).1.leader = (writeSeq hψ l r).1.leader ∧
      (writeWithBundle hψ l r).2.leader = (writeSeq hψ l r).2.leader := by
  unfold writeWithBundle
  dsimp only
  -- Keep `writeSeq` opaque: with it concrete, each `rfl` below made the elaborator reduce
  -- `writeSeq hψ l r` before the structure projection on the other side (369 s).
  generalize writeSeq hψ l r = q
  split <;> exact ⟨rfl, rfl⟩

/-- A responder leader survives WRITE on the pair (it may migrate to the initiator). -/
theorem wwb_keeps_leader (hψ : ψ > 0) (l r : AgentState ψ) (h : r.leader = true ∨ l.leader = true) :
    (writeWithBundle hψ l r).1.leader = true ∨ (writeWithBundle hψ l r).2.leader = true := by
  rw [(wwb_leader' hψ l r).1, (wwb_leader' hψ l r).2]
  rcases h with h | h
  · by_cases hz : r.label = ⟨0, hψ⟩
    · exact Or.inr (PPLLVerify.writeSeq_responder_leader_of_label_zero hψ l r h hz)
    · exact Or.inl (PPLLVerify.writeSeq_initiator_true_of_nonzero_responder_leader hψ l r ⟨h, hz⟩)
  · exact Or.inl (PPLLVerify.writeSeq_initiator_leader_of_true hψ l r h)

/-- The suffix after the comparison lifecycle frames the route fields and marks, and keeps a
responder leader in the pair. -/
theorem post_frame (hψ : ψ > 0) (l r : AuthState ψ) (hl : l.core.leader = false)
    (hr : r.core.leader = false) (q : AuthState ψ × AuthState ψ)
    (hq1 : q.1.core.leader = false) (h1 : q.1.core.reset_cmd = false)
    (h2 : q.2.core.reset_cmd = false) :
    WFrame (post hψ l r q).1.core q.1.core ∧ WFrame (post hψ l r q).2.core q.2.core ∧
      MarksEq q.1 (post hψ l r q).1 ∧ MarksEq q.2 (post hψ l r q).2 ∧
      (q.2.core.leader = true →
        (post hψ l r q).1.core.leader = true ∨ (post hψ l r q).2.core.leader = true) := by
  unfold post
  dsimp only
  rw [conserve_id l r hl hr]
  have hs := suppress_frame hψ q.1 q.2 hq1 h1 h2
  generalize suppressSigResetKillAuth hψ q.1 q.2 = s at hs
  obtain ⟨s1, s2⟩ := s
  obtain ⟨hs1, hs2, hm1, hm2, hl1, hl2⟩ := hs
  have hk := kernel_frame hψ s1.core s2.core
  simp only [lift2]
  have hw := wwb_frame hψ (k4Kernel hψ s1.core s2.core).1 (k4Kernel hψ s1.core s2.core).2
  simp only [WFrame] at hs1 hs2 hk hw ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hw.1.1, hw.1.2.1, hw.1.2.2.1, hw.1.2.2.2.1, hw.1.2.2.2.2,
        hk.1.1, hk.1.2.1, hk.1.2.2.1, hk.1.2.2.2.1, hk.1.2.2.2.2,
        hs1.1, hs1.2.1, hs1.2.2.1, hs1.2.2.2.1, hs1.2.2.2.2]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2,
        hk.2.1.1, hk.2.1.2.1, hk.2.1.2.2.1, hk.2.1.2.2.2.1, hk.2.1.2.2.2.2,
        hs2.1, hs2.2.1, hs2.2.2.1, hs2.2.2.2.1, hs2.2.2.2.2]
  · exact hm1
  · exact hm2
  · intro hq
    apply wwb_keeps_leader
    left
    rw [hk.2.2.2, hl2, hq]

end Frames

variable {ψ : Nat}


/-- States met on the comparison route. -/
def RouteSt (s : MainState) : Prop :=
  s = .depart ∨ s = .lock ∨ s = .compare1 ∨ s = .compare2 ∨ s = .eliminate_signal

/-- A cell on which the stages between SIGMOVE and the comparison lifecycle act trivially. -/
def QCell (u : AuthState ψ) : Prop :=
  u.core.leader = false ∧ u.core.reset_cmd = false ∧
    (∃ b, u.core.path = .some u.core.label.val b) ∧ RouteSt u.core.state ∧
    (u.core.state = .lock → u.core.label.val ≠ ψ - 1)

theorem liftLife_id (f : AgentState ψ → AgentState ψ) (u : AuthState ψ) (h : f u.core = u.core) :
    liftLife f u = u := by
  simp [liftLife, h]

theorem dropStale_id (u : AgentState ψ) (b : Nat) (h : u.path = .some u.label.val b) :
    dropStale u = u := by
  simp [dropStale, aligned, h]

theorem normalizeReady_id (u : AgentState ψ) (hl : u.leader = false) (b : Nat)
    (h : u.path = .some u.label.val b) (hs : RouteSt u.state) : normalizeReady u = u := by
  unfold RouteSt at hs
  rcases hs with hs | hs | hs | hs | hs <;>
    simp [normalizeReady, normalizeOrphan, normalizeCarrier, hl, h, hs, aligned]

theorem checkL_id (hψ : ψ > 0) (u : AgentState ψ) (h : u.state ≠ .CHECK_ready) :
    checkSigCheckL hψ u = u := by
  unfold checkSigCheckL; split <;> simp_all

theorem readyAuth_id (u : AuthState ψ) (hs : RouteSt u.core.state) : readyAuth u = u := by
  unfold RouteSt at hs
  rcases hs with hs | hs | hs | hs | hs <;>
    simp [readyAuth, AuthState.st, hs, waveState, checkSigSetReadyGuarded, controlPending,
      checkSigSetReady] <;> split <;> simp_all

/-- The status flags a route cell shows to the CHECK stage (one case split per cell). -/
private theorem route_flags (u : AuthState ψ) (hs : RouteSt u.core.state) :
    (u.st == .equal) = false ∧ (u.st == .larger) = false ∧ (u.st == .less) = false ∧
      (u.st == .CHECK_ready) = false ∧ u.st ≠ .equal ∧ u.st ≠ .larger ∧ u.st ≠ .less ∧
      u.core.state ≠ .CHECK_ready := by
  unfold RouteSt at hs
  rcases hs with h | h | h | h | h <;> simp [AuthState.st, h]

theorem checkSource_id (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (hc : c.strictReady = false)
    (l r : AuthState ψ) (hl : QCell l) (hr : QCell r) :
    checkSourceAuth hψ c l r = (l, r) := by
  obtain ⟨l1, l2, ⟨lb, l4⟩, l5, l6⟩ := hl
  obtain ⟨r1, r2, ⟨rb, r4⟩, r5, r6⟩ := hr
  -- The flags of each cell once, instead of a joint 5 x 5 case split under the whole stage
  -- (198 s).
  obtain ⟨fl1, fl2, fl3, fl4, fl5, fl6, fl7, fl8⟩ := route_flags l l5
  obtain ⟨fr1, fr2, fr3, fr4, fr5, fr6, fr7, fr8⟩ := route_flags r r5
  have hvl : validateCheck l r = (l, r) := by
    simp [validateCheck, headBad, checkState, verdict, fl1, fl2, fl3, fl4, fr1, fr2, fr3, fr4]
  unfold checkSourceAuth
  rw [hvl]
  -- One `simp` call (`dsimp only` and then `rw [readyAuth_id ..]` on the let-expanded stage
  -- spent the whole heartbeat budget in the rewrite).
  simp [hc, readyAuth_id l l5, readyAuth_id r r5, checkL_id, certPred, issue, isHead,
    AuthState.withCore, l4, r4, aligned, AuthState.lineage, fl1, fl5, fl6, fl7, fl8, fr5, fr6, fr7]


theorem preCheck_id (l r : AuthState ψ) (hl : l.core.leader = false) (h1 : l.core.reset_cmd = false)
    (h2 : r.core.reset_cmd = false) : preCheckResetAuth l r = (l, r) := by
  simp [preCheckResetAuth, hl, h1, h2]

theorem repair_id (l r : AuthState ψ) (hl : QCell l) (hr : QCell r) : repairAuth l r = (l, r) := by
  obtain ⟨l1, l2, ⟨lb, l4⟩, l5, l6⟩ := hl
  obtain ⟨r1, r2, ⟨rb, r4⟩, r5, r6⟩ := hr
  have hn : ∀ u : AuthState ψ, u.core.leader = false → ∀ b, u.core.path = .some u.core.label.val b →
      RouteSt u.core.state → normalizeCarrier (normalizeOrphan u.core) = u.core := by
    intro u h1 b h4 h5
    unfold RouteSt at h5
    rcases h5 with h | h | h | h | h <;> simp [normalizeOrphan, normalizeCarrier, h1, h4, h]
  unfold repairAuth
  rw [liftLife_id _ l (hn l l1 lb l4 l5), liftLife_id _ r (hn r r1 rb r4 r5)]
  have hrs : releaseReadySuffix l.core r.core = (l.core, r.core) := by
    unfold RouteSt at r5
    simp only [releaseReadySuffix, l4, r4]
    rcases r5 with h | h | h | h | h <;> simp [h]
  have h2 : lift2Life releaseReadySuffix l r = (l, r) := by
    simp [lift2Life, hrs]
  dsimp only
  rw [h2]
  dsimp only
  unfold ackTailAuth
  split
  · have ha : ackTail l.core r.core = (l.core, r.core) := by
      simp only [ackTail, l4, r4]
      split
      · rename_i h
        exfalso
        exact r6 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
      · rfl
    simp [lift2, ha]
  · rfl

/-- The route view: every field the comparison route reads, except the main state. -/
def RV (u : AuthState ψ) :=
  (u.core.path, u.core.path2, u.core.label, u.core.leader, u.core.reset_cmd, u.core.bit,
    u.path_mark, u.ctrl_mark, u.path2_scope, u.path2_mark)

/-- DISAPPEAR on route cells: only the lottery bits move, except that a carry reaching a
terminal responder turns it into `eliminate_signal` (a deletion exit). -/
theorem disappear_char (hψ : ψ > 0) (l r : AuthState ψ) (hl : l.core.state ≠ .toss)
    (hr : r.core.state ≠ .toss) :
    RV (disappearAuth hψ l r).1 = RV l ∧ (disappearAuth hψ l r).1.core.state = l.core.state ∧
      RV (disappearAuth hψ l r).2 = RV r ∧
      ((disappearAuth hψ l r).2.core.state = r.core.state ∨
        ((disappearAuth hψ l r).2.core.state = .eliminate_signal ∧ r.core.label.val = ψ - 1)) := by
  unfold disappearAuth lift2 disappearStartL disappearCarry
  simp only [AuthState.st, hl, hr, false_and, if_false]
  split
  · split
    · split
      · rename_i _ _ h
        simp [RV, h]
      · simp [RV]
    · simp [RV]
  · simp [RV]

theorem QCell.of_RV {u v : AuthState ψ} (h : QCell u) (hv : RV v = RV u)
    (hs : v.core.state = u.core.state ∨ v.core.state = .eliminate_signal) : QCell v := by
  obtain ⟨h1, h2, ⟨b, h4⟩, h5, h6⟩ := h
  simp only [RV, Prod.mk.injEq] at hv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hv
  refine ⟨by rw [e4]; exact h1, by rw [e5]; exact h2, ⟨b, by rw [e1, e3]; exact h4⟩, ?_, ?_⟩
  · rcases hs with hs | hs
    · rw [hs]; exact h5
    · rw [hs]; right; right; right; right; rfl
  · intro hl
    rcases hs with hs | hs
    · rw [e3]; exact h6 (hs ▸ hl)
    · rw [hs] at hl; cases hl

/-- On route cells the six middle stages reduce to DISAPPEAR. -/
theorem quiet_eq (hψ : ψ > 0) (l r : AuthState ψ) (hl : QCell l) (hr : QCell r) :
    quietStages hψ { retire := true, markClean := true, claimCheck := true } l r =
      disappearAuth hψ l r := by
  have hl' := hl
  have hr' := hr
  obtain ⟨l1, l2, ⟨lb, l4⟩, l5, l6⟩ := hl
  obtain ⟨r1, r2, ⟨rb, r4⟩, r5, r6⟩ := hr
  unfold quietStages
  rw [liftLife_id _ l (dropStale_id _ lb l4), liftLife_id _ r (dropStale_id _ rb r4)]
  dsimp only
  rw [preCheck_id l r l1 l2 r2]
  dsimp only
  rw [liftLife_id _ l (normalizeReady_id _ l1 lb l4 l5),
    liftLife_id _ r (normalizeReady_id _ r1 rb r4 r5)]
  rw [checkSource_id hψ _ rfl l r hl' hr']
  dsimp only
  have hnt : ∀ u : AuthState ψ, RouteSt u.core.state → u.core.state ≠ .toss := by
    intro u h; unfold RouteSt at h; rcases h with h | h | h | h | h <;> rw [h] <;> decide
  have hd := disappear_char hψ l r (hnt l l5) (hnt r r5)
  generalize disappearAuth hψ l r = d at hd
  obtain ⟨d1, d2⟩ := d
  obtain ⟨e1, e2, e3, e4⟩ := hd
  apply repair_id
  · exact QCell.of_RV hl' e1 (Or.inl e2)
  · exact QCell.of_RV hr' e3 (by rcases e4 with h | h; exact Or.inl h; exact Or.inr h.1)

/-! ## A deleted main path survives the rest of the interaction

A hole (`core.path = bot`) created anywhere in the prefix is still present, in one of the
two cells, at the end of the pipeline: every later stage keeps or deletes main paths, and
the only transfer (SIGMOVE step 1) moves a path into an empty responder and empties the
initiator. -/

section Paths
variable {ψ : Nat}

theorem control_path (hψ : ψ > 0) (u : AgentState ψ) :
    (sigMoveApplyControlConsume hψ u).path = u.path := by
  cases h : u.path2 <;> simp only [sigMoveApplyControlConsume, h] <;> simp [path_ite']

theorem orphan_path (u : AgentState ψ) : (normalizeOrphan u).path = u.path := by
  cases h : u.path <;> simp [normalizeOrphan, h, path_ite']

theorem carrier_path (u : AgentState ψ) : (normalizeCarrier u).path = u.path := by
  cases h : u.path <;> simp [normalizeCarrier, releaseCongest, h, path_ite']

theorem ready_path (u : AgentState ψ) : (normalizeReady u).path = u.path := by
  generalize ho : normalizeOrphan u = o
  have vo : o.path = u.path := by rw [← ho]; exact orphan_path u
  simp only [normalizeReady, ho]
  generalize hc : (if o.state = .none ∧ aligned o then o else normalizeCarrier o) = c
  have vc : c.path = o.path := by rw [← hc]; simp [path_ite', carrier_path]
  have ht := vc.trans vo
  cases hp : c.path <;> simp [hp, path_ite'] <;> (try split) <;> simp_all

theorem checkReady_path (u : AgentState ψ) : (checkSigSetReadyGuarded u).path = u.path := by
  cases h : u.path <;> simp [checkSigSetReadyGuarded, checkSigSetReady, h, path_ite']

theorem checkL_path (hψ : ψ > 0) (u : AgentState ψ) : (checkSigCheckL hψ u).path = u.path := by
  unfold checkSigCheckL; split <;> simp [path_ite']

theorem checkR_path (hψ : ψ > 0) (l r : AgentState ψ) : (checkSigCheckR hψ l r).path = r.path := by
  unfold checkSigCheckR; split <;> simp [path_ite']

theorem result_path (u : AgentState ψ) : (checkSigSetResult u).path = u.path := by
  simp [checkSigSetResult, path_ite']

theorem disStart_path (hψ : ψ > 0) (l r : AgentState ψ) :
    (disappearStartL hψ l r).1.path = l.path ∧ (disappearStartL hψ l r).2.path = r.path := by
  simp [disappearStartL, fst_ite, snd_ite, path_ite']

theorem disCarry_path (hψ : ψ > 0) (l r : AgentState ψ) :
    (disappearCarry hψ l r).1.path = l.path ∧ (disappearCarry hψ l r).2.path = r.path := by
  simp [disappearCarry, fst_ite, snd_ite, path_ite']

theorem releaseSuffix_path (l r : AgentState ψ) :
    (releaseReadySuffix l r).1.path = l.path ∧ (releaseReadySuffix l r).2.path = r.path := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [releaseReadySuffix, hl, hr, fst_ite, snd_ite, path_ite']

theorem ackTail_path (l r : AgentState ψ) :
    (ackTail l r).1.path = l.path ∧ (ackTail l r).2.path = r.path := by
  cases hl : l.path <;> cases hr : r.path <;>
    simp [ackTail, hl, hr, fst_ite, snd_ite, path_ite']

theorem dropStray_path (l r : AgentState ψ) :
    (dropStray l r).1.path = l.path ∧ (dropStray l r).2.path = r.path := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [dropStray, hl, hr, fst_ite, snd_ite, path_ite']

theorem landBackward_path (u : AgentState ψ) : (landBackward u).path = u.path := by
  cases hp : u.path <;> cases ht : u.path2 <;> simp [landBackward, hp, ht, path_ite']

theorem landForward_path (κ : Nat) (u : AgentState ψ) :
    (landForward κ false true u).path = u.path := by
  cases hp : u.path <;> cases ht : u.path2 <;> simp [landForward, hp, ht, path_ite']

/-- Close a leaf goal of a path lemma. -/
syntax "pclose" : tactic
macro_rules
  | `(tactic| pclose) => `(tactic| first
      | exact ⟨rfl, rfl⟩
      | rfl
      | (simp only [AuthState.withCore, AuthState.dropP2, AuthState.setState,
          AuthState.lineage, control_path, checkReady_path,
          checkL_path, checkR_path, result_path, landBackward_path, landForward_path,
          and_self, and_true, true_and];
         first | done | rfl | exact ⟨rfl, rfl⟩))

syntax "psplit" : tactic
macro_rules
  | `(tactic| psplit) => `(tactic| ((repeat' (first | (dsimp only) | split)) <;> pclose))

theorem sanitize_path (u : AuthState ψ) : (sanitizeP2 u).core.path = u.core.path := by
  unfold sanitizeP2; psplit

theorem issue_path (u : AuthState ψ) : (issue u).core.path = u.core.path := by
  unfold issue; psplit

theorem readyAuth_path (u : AuthState ψ) : (readyAuth u).core.path = u.core.path := by
  unfold readyAuth; psplit

theorem applyControl_path (hψ : ψ > 0) (u : AuthState ψ) :
    (applyControlAuth hψ u).core.path = u.core.path := by
  unfold applyControlAuth; psplit

theorem landBackwardAuth_path (u : AuthState ψ) :
    (landBackwardAuth u).core.path = u.core.path := by
  unfold landBackwardAuth; psplit

theorem landForwardAuth_path (κ : Nat) (u : AuthState ψ) :
    (landForwardAuth κ u).core.path = u.core.path := by
  unfold landForwardAuth; psplit

theorem validate_path (l r : AuthState ψ) :
    (validateCheck l r).1.core.path = l.core.path ∧ (validateCheck l r).2.core.path = r.core.path := by
  unfold validateCheck demote; psplit

theorem lift2_path (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, (f a b).1.path = a.path ∧ (f a b).2.path = b.path) (l r : AuthState ψ) :
    (lift2 f l r).1.core.path = l.core.path ∧ (lift2 f l r).2.core.path = r.core.path :=
  hf l.core r.core

theorem lift2Life_path (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, (f a b).1.path = a.path ∧ (f a b).2.path = b.path) (l r : AuthState ψ) :
    (lift2Life f l r).1.core.path = l.core.path ∧ (lift2Life f l r).2.core.path = r.core.path := by
  have h := hf l.core r.core
  unfold lift2Life
  dsimp only
  constructor <;> split <;> simp only [h]

theorem liftLife_path (f : AgentState ψ → AgentState ψ) (hf : ∀ a, (f a).path = a.path)
    (u : AuthState ψ) : (liftLife f u).core.path = u.core.path := by
  unfold liftLife; dsimp only; split <;> exact hf u.core

theorem checkSource_path (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    (checkSourceAuth hψ c l r).1.core.path = l.core.path ∧
      (checkSourceAuth hψ c l r).2.core.path = r.core.path := by
  simp only [checkSourceAuth, fst_ite, snd_ite, core_ite, path_ite', issue_path, readyAuth_path,
    validate_path, AuthState.withCore, AuthState.lineage, checkL_path, checkR_path,
    checkReady_path, ite_self, and_self]

theorem disappear_path (hψ : ψ > 0) (l r : AuthState ψ) :
    (disappearAuth hψ l r).1.core.path = l.core.path ∧
      (disappearAuth hψ l r).2.core.path = r.core.path := by
  have h1 := lift2_path (disappearStartL hψ) (disStart_path hψ)
  have h2 := lift2_path (disappearCarry hψ) (disCarry_path hψ)
  unfold disappearAuth
  dsimp only
  split <;> simp only [h2, h1, true_and, and_self] <;> pclose

theorem repair_path (l r : AuthState ψ) :
    (repairAuth l r).1.core.path = l.core.path ∧ (repairAuth l r).2.core.path = r.core.path := by
  have hc : ∀ a : AgentState ψ, (normalizeCarrier (normalizeOrphan a)).path = a.path :=
    fun a => (carrier_path _).trans (orphan_path a)
  have hl := liftLife_path _ hc
  have hr := lift2Life_path (ψ := ψ) releaseReadySuffix releaseSuffix_path
  have ha : ∀ a b : AuthState ψ, (ackTailAuth a b).1.core.path = a.core.path ∧
      (ackTailAuth a b).2.core.path = b.core.path := by
    intro a b
    unfold ackTailAuth; split
    · exact lift2_path ackTail ackTail_path a b
    · exact ⟨rfl, rfl⟩
  simp only [repairAuth, ha, hr, hl, and_self]

theorem maintain_path (l r : AuthState ψ) :
    (maintainAuth l r).1.core.path = l.core.path ∧ (maintainAuth l r).2.core.path = r.core.path := by
  unfold maintainAuth; psplit

theorem completeWave_path (l r : AuthState ψ) :
    (completeWaveAuth l r).1.core.path = l.core.path ∧
      (completeWaveAuth l r).2.core.path = r.core.path := by
  unfold completeWaveAuth; psplit

theorem wave_path (l r : AuthState ψ) :
    (waveAuth l r).1.core.path = l.core.path ∧ (waveAuth l r).2.core.path = r.core.path := by
  unfold waveAuth; psplit

theorem compare_path (κ : Nat) (l r : AuthState ψ) :
    (compareLifecycleAuth κ l r).1.core.path = l.core.path ∧
      (compareLifecycleAuth κ l r).2.core.path = r.core.path := by
  have hd := lift2_path (ψ := ψ) dropStray dropStray_path
  unfold compareLifecycleAuth
  dsimp only
  split
  all_goals (try split)
  all_goals simp only [landBackwardAuth_path, landForwardAuth_path, hd, wave_path,
    completeWave_path, maintain_path, AuthState.setState, and_self]

end Paths

section Holes
variable {ψ : Nat}

/-- One of the two cells of a pair has no main path. -/
def HP (q : AuthState ψ × AuthState ψ) : Prop := q.1.core.path = .bot ∨ q.2.core.path = .bot

/-- `v` keeps the main path of `u` or has none. -/
def PK (u v : AuthState ψ) : Prop := v.core.path = u.core.path ∨ v.core.path = .bot

theorem HP.of_PK {q q' : AuthState ψ × AuthState ψ} (h1 : PK q.1 q'.1) (h2 : PK q.2 q'.2)
    (h : HP q) : HP q' := by
  unfold HP PK at *
  rcases h with h | h
  · rcases h1 with h1 | h1
    · exact Or.inl (h1.trans h)
    · exact Or.inl h1
  · rcases h2 with h2 | h2
    · exact Or.inr (h2.trans h)
    · exact Or.inr h2

theorem HP.of_eq {q q' : AuthState ψ × AuthState ψ} (h1 : q'.1.core.path = q.1.core.path)
    (h2 : q'.2.core.path = q.2.core.path) (h : HP q) : HP q' :=
  HP.of_PK (Or.inl h1) (Or.inl h2) h

theorem receive_path (e : Entry) (src dst : AuthState ψ) (t : Path2Info) :
    (receive e src dst t).core.path = dst.core.path := by
  unfold receive; dsimp only; split <;> rfl

theorem PK_ite_clear (p : Prop) [Decidable p] (u : AuthState ψ) :
    PK u (if p then clearCmpAuth u else u) := by
  unfold PK; split
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem PK_refl (u : AuthState ψ) : PK u u := Or.inl rfl

private theorem PK_ite {u a b : AuthState ψ} {p : Prop} [Decidable p] (ha : PK u a)
    (hb : PK u b) : PK u (if p then a else b) := by
  by_cases hp : p
  · rw [if_pos hp]; exact ha
  · rw [if_neg hp]; exact hb

private theorem PK_dropP2 {u v : AuthState ψ} (h : PK u v) : PK u v.dropP2 := h

private theorem PK_receive {u v : AuthState ψ} (e : Entry) (src : AuthState ψ) (t : Path2Info)
    (h : PK u v) : PK u (receive e src v t) := by
  unfold PK; rw [receive_path]; exact h

private theorem PK_clear (u : AuthState ψ) : PK u (clearCmpAuth u) := by
  have h := PK_ite_clear True u
  rw [if_pos trivial] at h
  exact h

/-- Each output of the token transfer is its input, the input with `path2` dropped, a
`receive` into it, or the cleared input; `PK` is closed under each and under `if`.  The proof
follows the output terms and never splits on the transfer conditions (splitting every condition
took 41 s). -/
theorem moveTokens_PK (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    PK l (moveTokensAuth c l r).1 ∧ PK r (moveTokensAuth c l r).2 := by
  unfold moveTokensAuth
  simp only [pfst_ite, psnd_ite]
  constructor
  all_goals
    repeat (first
      | with_reducible exact PK_refl _
      | with_reducible exact PK_clear _
      | with_reducible refine PK_receive _ _ _ ?_
      | with_reducible refine PK_dropP2 ?_
      | with_reducible refine PK_ite ?_ ?_
      | (simp only [pfst_ite, psnd_ite])
      | split)

theorem leaderWall_PK (l r : AuthState ψ) :
    PK l (leaderWallAuth l r).1 ∧ PK r (leaderWallAuth l r).2 := by
  unfold leaderWallAuth
  dsimp only
  exact ⟨PK_ite_clear _ _, PK_ite_clear _ _⟩

theorem step1_HP (l r : AuthState ψ) (h : HP (l, r)) : HP (step1Auth l r) := by
  unfold step1Auth
  split
  · dsimp only
    split
    · split
      · exact Or.inl rfl
      · exact h
    · exact h
  · exact h

/-! ### SIGMOVE in three named parts -/

def msA (hψ : ψ > 0) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let nextLabel : Fin ψ := ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  (if l.core.leader = true ∨ (r.core.leader = true ∧ r.core.label ≠ nextLabel) then
    clearCmpAuth l else l,
   if r.core.leader = true then clearCmpAuth r else r)

def msB (c : PPLLAuthF.Cfg) (q : AuthState ψ × AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := validateCheck q.1 q.2
  let q := (sanitizeP2 q.1, sanitizeP2 q.2)
  let q := if q.1.st = .done then q else step1Auth q.1 q.2
  let q := moveTokensAuth c q.1 q.2
  leaderWallAuth q.1 q.2

def msC (hψ : ψ > 0) (q : AuthState ψ × AuthState ψ) : AuthState ψ × AuthState ψ :=
  let l := applyControlAuth hψ q.1
  let r := applyControlAuth hψ q.2
  let l := if r.st = .depart ∧ l.core.label.val < ψ - 1 ∧ l.st = .CHECK_ready then
    l.lineage .depart else l
  (l, r)

theorem moveSource_split (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    moveSourceAuth hψ c l r = msC hψ (msB c (msA hψ l r)) := by
  -- `moveSourceAuth` destructures each stage output with `let (l, r) := ...`, the split form
  -- projects it; `dsimp only` reduces both to the same term (`rfl` made the elaborator evaluate
  -- the stages instead: 70 s).
  unfold moveSourceAuth msC msB msA
  dsimp only

theorem msA_HP (hψ : ψ > 0) (l r : AuthState ψ) (h : HP (l, r)) : HP (msA hψ l r) :=
  HP.of_PK (q := (l, r)) (PK_ite_clear _ _) (PK_ite_clear _ _) h

def mb1 (q : AuthState ψ × AuthState ψ) : AuthState ψ × AuthState ψ := validateCheck q.1 q.2
def mb2 (q : AuthState ψ × AuthState ψ) : AuthState ψ × AuthState ψ := (sanitizeP2 q.1, sanitizeP2 q.2)
def mb3 (q : AuthState ψ × AuthState ψ) : AuthState ψ × AuthState ψ :=
  if q.1.st = .done then q else step1Auth q.1 q.2
def mb4 (c : PPLLAuthF.Cfg) (q : AuthState ψ × AuthState ψ) : AuthState ψ × AuthState ψ :=
  moveTokensAuth c q.1 q.2
def mb5 (q : AuthState ψ × AuthState ψ) : AuthState ψ × AuthState ψ := leaderWallAuth q.1 q.2

theorem msB_split (c : PPLLAuthF.Cfg) (q : AuthState ψ × AuthState ψ) :
    msB c q = mb5 (mb4 c (mb3 (mb2 (mb1 q)))) := rfl

theorem msB_HP (c : PPLLAuthF.Cfg) (q : AuthState ψ × AuthState ψ) (h : HP q) : HP (msB c q) := by
  rw [msB_split]
  have h1 : HP (mb1 q) := HP.of_eq (validate_path q.1 q.2).1 (validate_path q.1 q.2).2 h
  have h2 : HP (mb2 (mb1 q)) := HP.of_eq (sanitize_path _) (sanitize_path _) h1
  have h3 : HP (mb3 (mb2 (mb1 q))) := by
    unfold mb3
    split
    · exact h2
    · exact step1_HP _ _ h2
  have h4 : HP (mb4 c (mb3 (mb2 (mb1 q)))) :=
    HP.of_PK (moveTokens_PK c _ _).1 (moveTokens_PK c _ _).2 h3
  exact HP.of_PK (leaderWall_PK _ _).1 (leaderWall_PK _ _).2 h4

theorem msC_HP (hψ : ψ > 0) (q : AuthState ψ × AuthState ψ) (h : HP q) : HP (msC hψ q) := by
  unfold msC
  dsimp only
  refine HP.of_eq ?_ (applyControl_path hψ q.2) h
  dsimp only
  split
  · exact applyControl_path hψ q.1
  · exact applyControl_path hψ q.1

theorem moveSource_HP (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (h : HP (l, r)) :
    HP (moveSourceAuth hψ c l r) := by
  rw [moveSource_split]
  exact msC_HP hψ _ (msB_HP c _ (msA_HP hψ l r h))

theorem dropStale_PK (u : AgentState ψ) : (dropStale u).path = u.path ∨ (dropStale u).path = .bot := by
  unfold dropStale; split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem liftDropStale_PK (u : AuthState ψ) : PK u (liftLife dropStale u) := by
  have h := dropStale_PK u.core
  unfold liftLife PK; dsimp only; split <;> exact h

theorem preCheck_PK (l r : AuthState ψ) :
    PK l (preCheckResetAuth l r).1 ∧ PK r (preCheckResetAuth l r).2 := by
  unfold preCheckResetAuth
  dsimp only
  exact ⟨PK_ite_clear _ _, PK_ite_clear _ _⟩

def qs1 (q : AuthState ψ × AuthState ψ) : AuthState ψ × AuthState ψ :=
  (liftLife dropStale q.1, liftLife dropStale q.2)
def qs2 (q : AuthState ψ × AuthState ψ) : AuthState ψ × AuthState ψ := preCheckResetAuth q.1 q.2
def qs3 (q : AuthState ψ × AuthState ψ) : AuthState ψ × AuthState ψ :=
  (liftLife normalizeReady q.1, liftLife normalizeReady q.2)
def qs4 (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : AuthState ψ × AuthState ψ) :
    AuthState ψ × AuthState ψ := checkSourceAuth hψ c q.1 q.2
def qs5 (hψ : ψ > 0) (q : AuthState ψ × AuthState ψ) : AuthState ψ × AuthState ψ :=
  disappearAuth hψ q.1 q.2
def qs6 (q : AuthState ψ × AuthState ψ) : AuthState ψ × AuthState ψ := repairAuth q.1 q.2

theorem quiet_split (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    quietStages hψ c l r = qs6 (qs5 hψ (qs4 hψ c (qs3 (qs2 (qs1 (l, r)))))) := rfl

theorem quiet_HP (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (q : AuthState ψ × AuthState ψ) (h : HP q) :
    HP (quietStages hψ c q.1 q.2) := by
  rw [quiet_split]
  -- One stage at a time, each stage output generalized before the next lemma is applied
  -- (applying the lemmas to the nested stage terms took 304 s of unification).
  have h1 : HP (qs1 (q.1, q.2)) := HP.of_PK (liftDropStale_PK q.1) (liftDropStale_PK q.2) h
  revert h1; generalize qs1 (q.1, q.2) = q1; intro h1
  have h2 : HP (qs2 q1) := HP.of_PK (preCheck_PK q1.1 q1.2).1 (preCheck_PK q1.1 q1.2).2 h1
  revert h2; generalize qs2 q1 = q2; intro h2
  have h3 : HP (qs3 q2) :=
    HP.of_eq (liftLife_path _ ready_path q2.1) (liftLife_path _ ready_path q2.2) h2
  revert h3; generalize qs3 q2 = q3; intro h3
  have h4 : HP (qs4 hψ c q3) :=
    HP.of_eq (checkSource_path hψ c q3.1 q3.2).1 (checkSource_path hψ c q3.1 q3.2).2 h3
  revert h4; generalize qs4 hψ c q3 = q4; intro h4
  have h5 : HP (qs5 hψ q4) :=
    HP.of_eq (disappear_path hψ q4.1 q4.2).1 (disappear_path hψ q4.1 q4.2).2 h4
  revert h5; generalize qs5 hψ q4 = q5; intro h5
  exact HP.of_eq (repair_path q5.1 q5.2).1 (repair_path q5.1 q5.2).2 h5

theorem midS_HP (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (h : HP (l, r)) :
    HP (midS hψ κ c l r) := by
  have e : midS hψ κ c l r = compareLifecycleAuth κ
      (quietStages hψ c (moveSourceAuth hψ c l r).1 (moveSourceAuth hψ c l r).2).1
      (quietStages hψ c (moveSourceAuth hψ c l r).1 (moveSourceAuth hψ c l r).2).2 := rfl
  rw [e]
  have h2 := quiet_HP hψ c _ (moveSource_HP hψ c l r h)
  exact HP.of_eq (compare_path κ _ _).1 (compare_path κ _ _).2 h2

/-- ELIMINATE_SIG on a responder in `eliminate_signal` leaves a hole already in the prefix. -/
theorem pre_hole_of_elim (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hnext : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlp : l.core.path ≠ .bot) (hls : l.core.state ≠ .produce) (hld : l.core.state ≠ .done)
    (hre : r.core.state = .eliminate_signal) :
    HP (pre hψ κ c l r) := by
  have hrs : r.core.state ≠ .produce := by rw [hre]; decide
  have hrd : r.core.state ≠ .done := by rw [hre]; decide
  unfold pre HP
  dsimp only
  have p1 := pPsi_same hψ l r hl hr hnext
  generalize lift2 (pPsiProbeWall hψ) l r = q1 at p1
  obtain ⟨a1, b1⟩ := q1
  obtain ⟨p1a, p1b⟩ := p1
  have p2 := genSig_same hψ κ a1 b1 (by rw [p1a.leader]; exact hl) (by rw [p1a.path]; exact hlp)
    (by rw [p1a.state]; exact hls) (by rw [p1a.state]; exact hld) (by rw [p1b.state]; exact hrs)
  generalize genSigAuth hψ κ a1 b1 = q2 at p2
  obtain ⟨a2, b2⟩ := q2
  obtain ⟨p2a, p2b⟩ := p2
  have p3 := cleanSource_cases hψ c a2 b2
  generalize cleanSourceAuth hψ c a2 b2 = q3 at p3
  obtain ⟨a3, b3⟩ := q3
  obtain ⟨p3a, p3b⟩ := p3
  dsimp only at p3a p3b ⊢
  have sb : b3.core.state = r.core.state := by
    rcases p3b with h | h
    · rw [h.2, p2b.state, p1b.state]
    · rw [h.state, p2b.state, p1b.state]
  rw [release_id hψ a3 b3 (by rw [sb]; exact hrd)]
  exact Or.inr (elim_hole hψ a3 b3 (sb.trans hre))

theorem beforeSuppress_eq (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    beforeSuppressAuth hψ κ c l r = midS hψ κ c (pre hψ κ c l r).1 (pre hψ κ c l r).2 := rfl

/-- A hole in the prefix is still a hole after the interaction. -/
theorem pipeline_HP_of_pre (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (h1 : l.core.reset_cmd = false) (h2 : r.core.reset_cmd = false)
    (h : HP (pre hψ κ c l r)) : HP (pipeline hψ κ c l r) := by
  obtain ⟨b1, -, b3, -, b5, -, -⟩ := prefix_facts hψ κ c l r
  rw [beforeSuppress_eq] at b1 b3 b5
  have hm := midS_HP hψ κ c _ _ h
  rw [pipeline_eq]
  obtain ⟨w1, w2, -, -, -⟩ := post_frame hψ l r hl hr
    (midS hψ κ c (pre hψ κ c l r).1 (pre hψ κ c l r).2) (b5.trans hl) (b1.trans h1) (b3.trans h2)
  exact HP.of_eq w1.2.1 w2.2.1 hm

/-- Deletion exit: serving the incoming edge of a cell in `eliminate_signal` deletes a path. -/
theorem pipeline_HP_of_elim (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (h1 : l.core.reset_cmd = false) (h2 : r.core.reset_cmd = false)
    (hnext : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlp : l.core.path ≠ .bot) (hls : l.core.state ≠ .produce) (hld : l.core.state ≠ .done)
    (hre : r.core.state = .eliminate_signal) :
    HP (pipeline hψ κ c l r) :=
  pipeline_HP_of_pre hψ κ c l r hl hr h1 h2
    (pre_hole_of_elim hψ κ c l r hl hr hnext hlp hls hld hre)

end Holes

/-- `x == x` for a `DecidableEq` type, without the classical `LawfulBEq` route. -/
@[simp high] theorem beq_self_dec {α : Type} [DecidableEq α] (x : α) : (x == x) = true :=
  decide_eq_true rfl

theorem beq_ne_dec {α : Type} [DecidableEq α] {x y : α} (h : x ≠ y) : (x == y) = false :=
  decide_eq_false h

section Wrapper
variable {ψ : Nat}

/-- The fields the comparison route reads and writes, as they leave an interaction. -/
def V (u : AuthState ψ) :=
  (u.core.state, u.core.path, u.core.path2, u.core.label, u.path_mark, u.ctrl_mark,
    u.path2_scope, u.path2_mark)

theorem V_of_frames {a b : AuthState ψ} (h1 : WFrame a.core b.core) (h2 : MarksEq b a) :
    V a = V b := by
  obtain ⟨e1, e2, e3, _, e5⟩ := h1
  obtain ⟨m1, m2, m3, m4⟩ := h2
  simp only [V, e1, e2, e3, e5, m1, m2, m3, m4]

/-- One interaction on a pair whose prefix is a frame: either a main path is deleted, a
leader appears, or the pair leaves with exactly the route view computed by SIGMOVE through
the comparison lifecycle (`midS`), no leader and no reset. -/
theorem pipe_step (hψ : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (h1 : l.core.reset_cmd = false) (h2 : r.core.reset_cmd = false)
    (hnext : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlp : l.core.path ≠ .bot) (hls : l.core.state ≠ .produce) (hld : l.core.state ≠ .done)
    (hrs : r.core.state ≠ .produce) (hrd : r.core.state ≠ .done)
    (S : AuthState ψ × AuthState ψ → Prop)
    (hSV : ∀ m m' : AuthState ψ × AuthState ψ, V m'.1 = V m.1 → V m'.2 = V m.2 → S m → S m')
    (hS : ∀ l' r', SameF l l' → SameF r r' →
      HP (midS hψ κ c l' r') ∨ (midS hψ κ c l' r').2.core.leader = true ∨ S (midS hψ κ c l' r')) :
    HP (pipeline hψ κ c l r) ∨ (pipeline hψ κ c l r).1.core.leader = true ∨
      (pipeline hψ κ c l r).2.core.leader = true ∨
      (S (pipeline hψ κ c l r) ∧ (pipeline hψ κ c l r).1.core.leader = false ∧
        (pipeline hψ κ c l r).2.core.leader = false ∧
        (pipeline hψ κ c l r).1.core.reset_cmd = false ∧
        (pipeline hψ κ c l r).2.core.reset_cmd = false) := by
  have hres := pipeline_follower_reset hψ κ c l r hl
  rw [h1, h2] at hres
  simp only [Bool.or_self, Bool.false_and] at hres
  by_cases hq1 : (pipeline hψ κ c l r).1.core.leader = true
  · exact Or.inr (Or.inl hq1)
  by_cases hq2 : (pipeline hψ κ c l r).2.core.leader = true
  · exact Or.inr (Or.inr (Or.inl hq2))
  have hq1' : (pipeline hψ κ c l r).1.core.leader = false := by simpa using hq1
  have hq2' : (pipeline hψ κ c l r).2.core.leader = false := by simpa using hq2
  rcases pre_frame hψ κ c l r hl hr hnext hlp hls hld hrs hrd with hp | hp | ⟨s1, s2⟩
  · exact Or.inl (pipeline_HP_of_pre hψ κ c l r hl hr h1 h2 (Or.inl hp))
  · exact Or.inl (pipeline_HP_of_pre hψ κ c l r hl hr h1 h2 (Or.inr hp))
  obtain ⟨b1, -, b3, -, b5, -, -⟩ := prefix_facts hψ κ c l r
  rw [beforeSuppress_eq] at b1 b3 b5
  have hfr := post_frame hψ l r hl hr
    (midS hψ κ c (pre hψ κ c l r).1 (pre hψ κ c l r).2) (b5.trans hl) (b1.trans h1) (b3.trans h2)
  rw [← pipeline_eq] at hfr
  obtain ⟨w1, w2, m1, m2, wl⟩ := hfr
  rcases hS _ _ s1 s2 with hh | hh | hh
  · exact Or.inl (HP.of_eq w1.2.1 w2.2.1 hh)
  · exact absurd (wl hh) (by simp [hq1', hq2'])
  · exact Or.inr (Or.inr (Or.inr
      ⟨hSV _ _ (V_of_frames w1 m1) (V_of_frames w2 m2) hh, hq1', hq2', hres.1, hres.2⟩))

end Wrapper

/-! ## SIGMOVE on route cells -/

section Move
variable {ψ : Nat}

theorem checkState_route {u : AuthState ψ} (h : RouteSt u.core.state) :
    checkState u = false ∧ verdict u = false := by
  unfold RouteSt at h
  rcases h with h | h | h | h | h <;> simp [checkState, verdict, AuthState.st, h]

theorem validate_id (l r : AuthState ψ) (hl : RouteSt l.core.state) (hr : RouteSt r.core.state) :
    validateCheck l r = (l, r) := by
  have h1 := checkState_route hl
  have h2 := checkState_route hr
  simp [validateCheck, headBad, h1.1, h2.1, h2.2]

theorem sanitize_id (u : AuthState ψ) (h : p2Valid u = true) : sanitizeP2 u = u := by
  simp [sanitizeP2, h]

theorem step1_id (l r : AuthState ψ) (a b : Nat) (h : r.core.path = .some a b) :
    step1Auth l r = (l, r) := by
  unfold step1Auth
  split
  · rename_i h'
    rw [h] at h'
    cases h'
  · rfl

theorem moveTokens_leader (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    (moveTokensAuth c l r).1.core.leader = l.core.leader ∧
      (moveTokensAuth c l r).2.core.leader = r.core.leader := by
  have hav := moveTokens_av c l r
  rw [leader_av, hav.1, ← leader_av, leader_av (moveTokensAuth c l r).2, hav.2, ← leader_av]
  exact ⟨rfl, rfl⟩

/-- On route cells without leaders, with valid tokens and occupied responder, SIGMOVE is
token transfer followed by control application. -/
theorem moveSource_eq (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hls : RouteSt l.core.state) (hrs : RouteSt r.core.state)
    (hlv : p2Valid l = true) (hrv : p2Valid r = true) (a b : Nat) (hrp : r.core.path = .some a b)
    (hck : (applyControlAuth hψ (moveTokensAuth c l r).1).core.state ≠ .CHECK_ready) :
    moveSourceAuth hψ c l r =
      (applyControlAuth hψ (moveTokensAuth c l r).1, applyControlAuth hψ (moveTokensAuth c l r).2) := by
  rw [moveSource_split]
  have hA : msA hψ l r = (l, r) := by simp [msA, hl, hr]
  have hdone : ¬ (l.st = .done) := by
    unfold RouteSt at hls
    simp only [AuthState.st]
    rcases hls with h | h | h | h | h <;> rw [h] <;> decide
  have e1 := moveTokens_leader c l r
  rw [hl] at e1
  rw [hr] at e1
  have hB : msB c (l, r) = moveTokensAuth c l r := by
    rw [msB_split]
    simp only [mb1, validate_id l r hls hrs, mb2, sanitize_id l hlv, sanitize_id r hrv, mb3, hdone,
      if_false, step1_id l r a b hrp, mb4, mb5]
    simp [leaderWallAuth, e1.1, e1.2]
  rw [hA, hB]
  simp [msC, AuthState.st, hck]

/-! ### Token transfer -/

theorem mt_none (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (h1 : l.core.path2 = none)
    (h2 : r.core.path2 = none) : moveTokensAuth c l r = (l, r) := by
  simp [moveTokensAuth, h1, h2]

theorem mt_stay (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (t : Path2Info) (h1 : l.core.path2 = none)
    (h2 : r.core.path2 = some t) (hmv : canMoveL r.core t = false) :
    moveTokensAuth c l r = (l, r) := by
  simp [moveTokensAuth, h1, h2, hmv]

theorem mt_stayR (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (t : Path2Info) (h1 : l.core.path2 = some t)
    (h2 : r.core.path2 = none) (hmv : canMoveR l.core t = false) :
    moveTokensAuth c l r = (l, r) := by
  simp [moveTokensAuth, h1, h2, hmv]

theorem entry_ok (cc : Bool) (src dst : AuthState ψ) (t : Path2Info) (hh : dst.hasPath = true)
    (hs : src.path2_scope = .session) (ha : t.action ≠ 2) (hc : dst.ctrl_mark = src.path2_mark) :
    entry cc src dst t = .ok := by
  simp [entry, hh, hs, ha, hc]

theorem entry_ok2 (cc : Bool) (src dst : AuthState ψ) (t : Path2Info) (hh : dst.hasPath = true)
    (hs : src.path2_scope = .session) (ha : t.action = 2) (hc : dst.ctrl_mark = src.path2_mark)
    (hw : waveState dst.core.state = true ∨ dst.core.state = .depart) :
    entry cc src dst t = .ok := by
  rcases hw with hw | hw <;> simp [entry, hh, hs, ha, hc, AuthState.st, hw]

theorem entry_claim (cc : Bool) (src dst : AuthState ψ) (t : Path2Info) (hh : dst.hasPath = true)
    (hs : src.path2_scope = .session) (ha : t.action = 2) (hc : dst.ctrl_mark ≠ src.path2_mark)
    (hd : dst.core.state = .depart) : entry cc src dst t = .claim := by
  simp [entry, hh, hs, ha, hc, claimable, AuthState.st, hd]

theorem mt_R (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (t : Path2Info)
    (hl2 : l.core.path2 = some t) (hr2 : r.core.path2 = none) (hsc : l.path2_scope = .session)
    (hmv : canMoveR l.core t = true) (hrh : r.hasPath = true) (ha : t.action ≠ 2)
    (hok : r.ctrl_mark = l.path2_mark) :
    moveTokensAuth c l r = (l.dropP2, receive .ok l r (dec t)) := by
  have he : entry c.claimCheck l r t = .ok := entry_ok _ _ _ _ hrh hsc ha hok
  simp [moveTokensAuth, hl2, hr2, hsc, hmv, he]

theorem mt_L (c : PPLLAuthF.Cfg) (l r : AuthState ψ) (t : Path2Info) (e : Entry)
    (hl2 : l.core.path2 = none) (hr2 : r.core.path2 = some t)
    (hmv : canMoveL r.core t = true) (he : entry c.claimCheck r l t = e) (hne : e ≠ .reject)
    (hf : l.ctrl_mark = r.path2_mark ∨ claimable c.claimCheck l = true) :
    moveTokensAuth c l r = (receive e r l (dec t), r.dropP2) := by
  rcases hf with hf | hf <;> simp [moveTokensAuth, hl2, hr2, hmv, he, hne, hf]

/-! ### Control application -/

theorem ac_none (hψ : ψ > 0) (u : AuthState ψ) (h : u.core.path2 = none) :
    applyControlAuth hψ u = u := by
  simp [applyControlAuth, h]

theorem ac_12 (hψ : ψ > 0) (u : AuthState ψ) (t : Path2Info) (h : u.core.path2 = some t)
    (ha : t.action = 1 ∨ t.action = 2) : applyControlAuth hψ u = u := by
  rcases ha with ha | ha <;> simp [applyControlAuth, h, ha]

theorem ac_34_mid (hψ : ψ > 0) (u : AuthState ψ) (t : Path2Info) (h : u.core.path2 = some t)
    (ha : t.action = 3 ∨ t.action = 4) (hs : u.path2_scope = .session)
    (hm : u.path2_mark = u.ctrl_mark) (hlab : u.core.label.val ≠ ψ - 1) :
    applyControlAuth hψ u = u := by
  have h1 : ¬ u.core.label = ⟨ψ - 1, by omega⟩ := by
    intro e; exact hlab (congrArg Fin.val e)
  rcases ha with ha | ha <;>
    simp [applyControlAuth, h, ha, hs, hm, sigMoveApplyControlConsume, h1] <;>
    (cases u; simp_all)

theorem ac_34_last (hψ : ψ > 0) (u : AuthState ψ) (t : Path2Info) (h : u.core.path2 = some t)
    (ha : t.action = 3 ∨ t.action = 4) (hs : u.path2_scope = .session)
    (hm : u.path2_mark = u.ctrl_mark) (hlab : u.core.label.val = ψ - 1) :
    applyControlAuth hψ u =
      { u with core := { u.core with state := .eliminate_signal, path2 := none } } := by
  have h1 : u.core.label = ⟨ψ - 1, by omega⟩ := Fin.ext hlab
  have h0 : ¬ u.core.label = ⟨0, hψ⟩ ∨ t.action ≠ 6 := by
    right; rcases ha with ha | ha <;> rw [ha] <;> decide
  rcases ha with ha | ha <;>
    simp [applyControlAuth, h, ha, hs, hm, sigMoveApplyControlConsume, h1]

end Move

/-! ## The comparison lifecycle on settled session pairs

Once a session is set up, every served edge joins two cells of one of five kinds
(`sd` = session-stamped `depart`, `c1` = `compare1`, `c2` = `compare2`, all with control mark
`σ`): (sd,sd), (sd,c2), (c2,c1) across the boundary, (c1,c1), (c1,c2).  On these pairs the
release, acknowledgement and wave rules are all inert; only token landing acts. -/

theorem bne_ne_dec {α : Type} [DecidableEq α] {x y : α} (h : x ≠ y) : (x != y) = true := by
  simp only [bne, beq_ne_dec h]; rfl

section Kinds
variable {ψ : Nat}

/-- The three wave stages are inert. -/
def Inert (l r : AuthState ψ) : Prop :=
  maintainAuth l r = (l, r) ∧ completeWaveAuth l r = (l, r) ∧ waveAuth l r = (l, r)

theorem inert_sd_sd (l r : AuthState ψ) (a b b' : Nat) (σ : ProvColor)
    (hlp : l.core.path = .some a b) (hrp : r.core.path = .some (a + 1) b')
    (hls : l.core.state = .depart) (hrs : r.core.state = .depart)
    (hlc : l.ctrl_mark = σ) (hrc : r.ctrl_mark = σ) (hlm : σ ≠ l.path_mark)
    (hrm : σ ≠ r.path_mark) : Inert l r := by
  refine ⟨?_, ?_, ?_⟩
  · simp [maintainAuth, hlp, hrp, hls, hrs, hlc, hrc, hlm, bne_ne_dec hrm, AuthState.st,
      lockedState, waveState, AuthState.lineage, AuthState.setState]
  · simp [completeWaveAuth, hlp, hrp, hls, hrs, AuthState.st, lockedState]
  · simp [waveAuth, hlp, hrp, hls, hrs, hlc, hrc, beq_ne_dec hlm, AuthState.st, lockedState]

theorem inert_sd_c2 (l r : AuthState ψ) (a b b' : Nat) (σ : ProvColor)
    (hlp : l.core.path = .some a b) (hrp : r.core.path = .some (a + 1) b')
    (hls : l.core.state = .depart) (hrs : r.core.state = .compare2)
    (hlc : l.ctrl_mark = σ) (hrc : r.ctrl_mark = σ) (hlm : σ ≠ l.path_mark) : Inert l r := by
  refine ⟨?_, ?_, ?_⟩
  · simp [maintainAuth, hlp, hrp, hls, hrs, hlc, hrc, hlm, AuthState.st,
      lockedState, waveState, AuthState.lineage, AuthState.setState]
  · simp [completeWaveAuth, hlp, hrp, hls, hrs, AuthState.st, lockedState]
  · simp [waveAuth, hlp, hrp, hls, hrs, hlc, hrc, beq_ne_dec hlm, AuthState.st, lockedState]

theorem inert_c2_c1 (hψ : ψ > 0) (l r : AuthState ψ) (b b' : Nat) (σ : ProvColor)
    (hlp : l.core.path = .some (ψ - 1) b) (hrp : r.core.path = .some 0 b')
    (hls : l.core.state = .compare2) (hrs : r.core.state = .compare1)
    (hlc : l.ctrl_mark = σ) (hrc : r.ctrl_mark = σ)
    (htok : l.core.path2 ≠ none ∨ r.core.path2 ≠ none) : Inert l r := by
  have hm : (ψ - 1) % ψ = ψ - 1 := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp [-Nat.right_eq_add, -Nat.left_eq_add, maintainAuth, hlp, hrp, hls, hrs, hlc, hrc, hm, AuthState.st,
      lockedState, lockerState, waveState, AuthState.lineage, AuthState.setState]
  · simp [-Nat.right_eq_add, -Nat.left_eq_add, completeWaveAuth, hlp, hrp, hls, hrs, AuthState.st, lockedState]
  · rcases htok with h | h <;>
      simp [-Nat.right_eq_add, -Nat.left_eq_add, waveAuth, hlp, hrp, hls, hrs, hlc, hrc, h, AuthState.st, lockedState]

theorem inert_c1_c1 (l r : AuthState ψ) (a b b' : Nat) (σ : ProvColor)
    (hlp : l.core.path = .some a b) (hrp : r.core.path = .some (a + 1) b')
    (hls : l.core.state = .compare1) (hrs : r.core.state = .compare1)
    (hlc : l.ctrl_mark = σ) (hrc : r.ctrl_mark = σ) (hne : a ≠ ψ - 1)
    (hlt : a < ψ) : Inert l r := by
  have hmod : a % ψ = a := Nat.mod_eq_of_lt hlt
  refine ⟨?_, ?_, ?_⟩
  · simp [maintainAuth, hlp, hrp, hls, hrs, hlc, hrc, hne, hmod, AuthState.st,
      lockedState, lockerState, waveState, AuthState.lineage, AuthState.setState]
  · simp [completeWaveAuth, hlp, hrp, hls, hrs, AuthState.st, lockedState]
  · simp [waveAuth, hlp, hrp, hls, hrs, hlc, hrc, hne, AuthState.st, lockedState]

theorem inert_c1_c2 (l r : AuthState ψ) (a b b' : Nat) (σ : ProvColor)
    (hlp : l.core.path = .some a b) (hrp : r.core.path = .some (a + 1) b')
    (hls : l.core.state = .compare1) (hrs : r.core.state = .compare2)
    (hlc : l.ctrl_mark = σ) (hrc : r.ctrl_mark = σ) (hne : a ≠ ψ - 1) : Inert l r := by
  refine ⟨?_, ?_, ?_⟩
  · simp [maintainAuth, hlp, hrp, hls, hrs, hlc, hrc, hne, AuthState.st,
      lockedState, lockerState, waveState, AuthState.lineage, AuthState.setState]
  · simp [completeWaveAuth, hlp, hrp, hls, hrs, AuthState.st, lockedState]
  · simp [waveAuth, hlp, hrp, hls, hrs, hlc, hrc, hne, AuthState.st, lockedState]

/-! ### Stray drops and landings -/

theorem ds_id (l r : AuthState ψ)
    (hl : ∀ t, l.core.path2 = some t → ¬ (t.action = 1 ∧ t.position = 0))
    (hr : ∀ t, r.core.path2 = some t → ¬ (t.action = 2 ∧ t.position = 0)) :
    lift2 dropStray l r = (l, r) := by
  unfold lift2 dropStray
  dsimp only
  rcases h1 : l.core.path2 with _ | t1 <;> rcases h2 : r.core.path2 with _ | t2 <;>
    simp only [h1, h2] <;> (try rw [if_neg (hl _ h1)]) <;> (try rw [if_neg (hr _ h2)])

theorem compare_inert (κ : Nat) (l r : AuthState ψ) (a b : Nat) (hlp : l.core.path = .some a b)
    (hin : Inert l r) (hds : lift2 dropStray l r = (l, r)) :
    compareLifecycleAuth κ l r = (landBackwardAuth l, landForwardAuth κ r) := by
  obtain ⟨hm, hc, hw⟩ := hin
  unfold compareLifecycleAuth
  simp only [hlp]
  rw [hm]
  dsimp only
  rw [hc]
  dsimp only
  rw [hw]
  dsimp only
  rw [hds]

theorem lb_none (l : AuthState ψ) (h : l.core.path2 = none) : landBackwardAuth l = l := by
  simp [landBackwardAuth, h]

theorem lb_other (l : AuthState ψ) (t : Path2Info) (h : l.core.path2 = some t)
    (hn : ¬ (t.action = 2 ∧ t.position = 0)) : landBackwardAuth l = l := by
  unfold landBackwardAuth
  simp only [h]
  cases hp : l.core.path <;> simp [hn]

theorem lb_land (l : AuthState ψ) (j lb : Nat) (hlp : l.core.path = .some j lb)
    (ht : l.core.path2 = some ⟨j, 0, 0, 2⟩) (hs : l.path2_scope = .session)
    (hm : l.path2_mark = l.ctrl_mark) :
    landBackwardAuth l = { l with core := { l.core with path2 := some ⟨j, lb, ψ, 1⟩ } } := by
  simp [landBackwardAuth, hlp, ht, hs, hm, landBackward, AuthState.withCore]

theorem lf_none (κ : Nat) (r : AuthState ψ) (h : r.core.path2 = none) : landForwardAuth κ r = r := by
  simp [landForwardAuth, h]

theorem lf_other (κ : Nat) (r : AuthState ψ) (t : Path2Info) (h : r.core.path2 = some t)
    (hn : ¬ (t.action = 1 ∧ t.position = 0)) : landForwardAuth κ r = r := by
  unfold landForwardAuth
  simp only [h]
  cases hp : r.core.path <;> simp [hn]

/-- BEQ landing of a forward token on its target: equality elects (last position) or
emits the next backward token; a strict comparison emits A4 or A3. -/
theorem lf_land (κ : Nat) (r : AuthState ψ) (j lb b : Nat) (hrp : r.core.path = .some j b)
    (ht : r.core.path2 = some ⟨j, lb, 0, 1⟩) (hw : waveState r.core.state = true)
    (hs : r.path2_scope = .session) (hm : r.path2_mark = r.ctrl_mark) :
    (j = ψ - 1 ∧ landForwardAuth κ r =
        { r with core := { r.core with leader := true, path2 := none } }) ∨
      (j ≠ ψ - 1 ∧ landForwardAuth κ r =
        { r with core := { r.core with path2 := some ⟨j + 1, 0, ψ - 1, 2⟩ } }) ∨
      landForwardAuth κ r = { r with core := { r.core with path2 := some ⟨0, 0, 0, 4⟩ } } ∨
      landForwardAuth κ r = { r with core := { r.core with path2 := some ⟨0, 0, 0, 3⟩ } } := by
  have e : landForwardAuth κ r = r.withCore (landForward κ false true r.core) := by
    simp [landForwardAuth, hrp, ht, hs, hm, hw, AuthState.st]
  rw [e]
  simp only [landForward, hrp, ht, hw, AuthState.withCore]
  by_cases h1 : lb = (if r.core.bit = true then 1 else 0)
  · by_cases h2 : j = ψ - 1
    · left; simp [h1, h2]
    · right; left; simp [h1, h2]
  · by_cases h3 : lb > (if r.core.bit = true then 1 else 0)
    · right; right; left; simp [h1, h3]
    · right; right; right; simp [h1, h3]

end Kinds

/-! ## SIGMOVE through the comparison lifecycle -/

section MidS
variable {ψ : Nat}

theorem notToss_of_route {u : AuthState ψ} (h : RouteSt u.core.state) : u.core.state ≠ .toss := by
  unfold RouteSt at h
  rcases h with h | h | h | h | h <;> rw [h] <;> decide

/-- `midS` after a computed SIGMOVE: DISAPPEAR only moves lottery bits, except that the
responder may become `eliminate_signal` at the terminal label. -/
theorem midS_via (hψ : ψ > 0) (κ : Nat) (l r l2 r2 : AuthState ψ)
    (hms : moveSourceAuth hψ authFplusmcc l r = (l2, r2)) (hq1 : QCell l2) (hq2 : QCell r2)
    (P : AuthState ψ × AuthState ψ → Prop)
    (hP : ∀ d1 d2 : AuthState ψ, RV d1 = RV l2 → d1.core.state = l2.core.state → RV d2 = RV r2 →
      (d2.core.state = r2.core.state ∨
        (d2.core.state = .eliminate_signal ∧ r2.core.label.val = ψ - 1)) →
      P (compareLifecycleAuth κ d1 d2)) :
    P (midS hψ κ authFplusmcc l r) := by
  have e : midS hψ κ authFplusmcc l r = compareLifecycleAuth κ
      (quietStages hψ authFplusmcc (moveSourceAuth hψ authFplusmcc l r).1
        (moveSourceAuth hψ authFplusmcc l r).2).1
      (quietStages hψ authFplusmcc (moveSourceAuth hψ authFplusmcc l r).1
        (moveSourceAuth hψ authFplusmcc l r).2).2 := rfl
  rw [e, hms]
  have hq : quietStages hψ authFplusmcc l2 r2 = disappearAuth hψ l2 r2 := quiet_eq hψ l2 r2 hq1 hq2
  rw [hq]
  obtain ⟨e1, e2, e3, e4⟩ := disappear_char hψ l2 r2 (notToss_of_route hq1.2.2.2.1)
    (notToss_of_route hq2.2.2.2.1)
  exact hP _ _ e1 e2 e3 e4

/-! ### Terminal `eliminate_signal` survives the lifecycle; no stage creates `produce`/`done` -/

def NPD (s : MainState) : Prop := s ≠ .produce ∧ s ≠ .done

theorem maintain_state (l r : AuthState ψ) :
    ((maintainAuth l r).1.core.state = l.core.state ∨ (maintainAuth l r).1.core.state = .none ∨
      (maintainAuth l r).1.core.state = .depart) ∧
    ((maintainAuth l r).2.core.state = r.core.state ∨ (maintainAuth l r).2.core.state = .none ∨
      (maintainAuth l r).2.core.state = .depart) := by
  unfold maintainAuth
  constructor
  all_goals (repeat' (first | (dsimp only) | split)) <;> simp [AuthState.setState, AuthState.lineage]

theorem maintain_elim (l r : AuthState ψ) :
    (l.core.state = .eliminate_signal → (maintainAuth l r).1.core.state = .eliminate_signal) ∧
    (r.core.state = .eliminate_signal → (maintainAuth l r).2.core.state = .eliminate_signal) := by
  unfold maintainAuth
  constructor
  all_goals intro h
  all_goals (repeat' (first | (dsimp only) | split)) <;>
    simp_all [AuthState.setState, AuthState.lineage, AuthState.st, lockedState, waveState]

theorem completeWave_state (l r : AuthState ψ) :
    ((completeWaveAuth l r).1.core.state = l.core.state ∨
      (completeWaveAuth l r).1.core.state = .compare1) ∧
    ((completeWaveAuth l r).2.core.state = r.core.state ∨
      (completeWaveAuth l r).2.core.state = .compare1 ∨
      (completeWaveAuth l r).2.core.state = .lock) := by
  unfold completeWaveAuth
  constructor
  all_goals (repeat' (first | (dsimp only) | split)) <;> simp [AuthState.setState]

theorem completeWave_elim (l r : AuthState ψ) :
    (l.core.state = .eliminate_signal → (completeWaveAuth l r).1.core.state = .eliminate_signal) ∧
    (r.core.state = .eliminate_signal → (completeWaveAuth l r).2.core.state = .eliminate_signal) := by
  unfold completeWaveAuth
  constructor
  all_goals intro h
  all_goals (repeat' (first | (dsimp only) | split)) <;>
    simp_all [AuthState.setState, AuthState.st]

theorem wave_state (l r : AuthState ψ) :
    ((waveAuth l r).1.core.state = l.core.state ∨ (waveAuth l r).1.core.state = .compare1 ∨
      (waveAuth l r).1.core.state = .compare2) ∧
    ((waveAuth l r).2.core.state = r.core.state ∨ (waveAuth l r).2.core.state = .compare1 ∨
      (waveAuth l r).2.core.state = .lock) := by
  unfold waveAuth
  constructor
  all_goals (repeat' (first | (dsimp only) | split)) <;> simp [AuthState.setState]

theorem wave_elim (l r : AuthState ψ) :
    (l.core.state = .eliminate_signal → (waveAuth l r).1.core.state = .eliminate_signal) ∧
    (r.core.state = .eliminate_signal → (waveAuth l r).2.core.state = .eliminate_signal) := by
  unfold waveAuth
  constructor
  all_goals intro h
  all_goals (repeat' (first | (dsimp only) | split)) <;>
    simp_all [AuthState.setState, AuthState.st, lockedState, -Nat.right_eq_add, -Nat.left_eq_add]

end MidS

/-! ## Cell descriptions -/

section Cells
variable {ψ : Nat}

/-- Route view of a cell at label `a`, block colour `γ`, state `st`, control mark `cm`,
BEQ token `tok` (a token is always a session token of colour `σ`). -/
def CV (σ : ProvColor) (u : AuthState ψ) (a : Nat) (γ : ProvColor) (st : MainState)
    (cm : ProvColor) (tok : Option Path2Info) : Prop :=
  u.core.label.val = a ∧ (∃ b, u.core.path = .some a b) ∧ u.path_mark = γ ∧ u.core.state = st ∧
    u.ctrl_mark = cm ∧ u.core.path2 = tok ∧
    (tok ≠ none → u.path2_scope = .session ∧ u.path2_mark = σ)

/-- A route cell: its view, no leader, no reset. -/
def Cell (σ : ProvColor) (u : AuthState ψ) (a : Nat) (γ : ProvColor) (st : MainState)
    (cm : ProvColor) (tok : Option Path2Info) : Prop :=
  CV σ u a γ st cm tok ∧ u.core.leader = false ∧ u.core.reset_cmd = false

theorem CV.of_V {σ : ProvColor} {u v : AuthState ψ} {a γ st cm tok}
    (h : CV σ u a γ st cm tok) (hv : V v = V u) : CV σ v a γ st cm tok := by
  simp only [V, Prod.mk.injEq] at hv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hv
  obtain ⟨h1, ⟨b, h2⟩, h3, h4, h5, h6, h7⟩ := h
  refine ⟨by rw [e4]; exact h1, ⟨b, by rw [e2]; exact h2⟩, by rw [e5]; exact h3, by rw [e1]; exact h4,
    by rw [e6]; exact h5, by rw [e3]; exact h6, ?_⟩
  intro ht
  rw [e7, e8]; exact h7 ht

theorem CV.of_RV {σ : ProvColor} {u v : AuthState ψ} {a γ st cm tok}
    (h : CV σ u a γ st cm tok) (hv : RV v = RV u) (hs : v.core.state = u.core.state) :
    CV σ v a γ st cm tok := by
  simp only [RV, Prod.mk.injEq] at hv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hv
  apply CV.of_V h
  simp only [V, e1, e2, e3, e7, e8, e9, e10, hs]

theorem Cell.of_RV {σ : ProvColor} {u v : AuthState ψ} {a γ st cm tok}
    (h : Cell σ u a γ st cm tok) (hv : RV v = RV u) (hs : v.core.state = u.core.state) :
    Cell σ v a γ st cm tok := by
  refine ⟨h.1.of_RV hv hs, ?_, ?_⟩
  · have : v.core.leader = u.core.leader := by simp only [RV, Prod.mk.injEq] at hv; exact hv.2.2.2.1
    rw [this]; exact h.2.1
  · have : v.core.reset_cmd = u.core.reset_cmd := by
      simp only [RV, Prod.mk.injEq] at hv; exact hv.2.2.2.2.1
    rw [this]; exact h.2.2

theorem Cell.of_same {σ : ProvColor} {u v : AuthState ψ} {a γ st cm tok}
    (h : Cell σ u a γ st cm tok) (hs : SameF u v) : Cell σ v a γ st cm tok := by
  obtain ⟨hc, hm1, hm2, hm3, hm4⟩ := hs
  simp only [cp, Prod.mk.injEq] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := hc
  obtain ⟨⟨h1, ⟨b, h2⟩, h3, h4, h5, h6, h7⟩, h8, h9⟩ := h
  refine ⟨⟨by rw [c4]; exact h1, ⟨b, by rw [c2]; exact h2⟩, by rw [hm1]; exact h3,
    by rw [c1]; exact h4, by rw [hm2]; exact h5, by rw [c3]; exact h6, ?_⟩,
    by rw [c5]; exact h8, by rw [c6]; exact h9⟩
  intro ht; rw [hm3, hm4]; exact h7 ht

theorem Cell.qcell {σ : ProvColor} {u : AuthState ψ} {a γ st cm tok}
    (h : Cell σ u a γ st cm tok) (hr : RouteSt st) (hlk : st = .lock → a ≠ ψ - 1) : QCell u := by
  obtain ⟨⟨h1, ⟨b, h2⟩, h3, h4, h5, h6, h7⟩, h8, h9⟩ := h
  refine ⟨h8, h9, ⟨b, by rw [h1]; exact h2⟩, by rw [h4]; exact hr, ?_⟩
  intro hl; rw [h1]; exact hlk (h4 ▸ hl)

theorem Cell.valid {σ : ProvColor} {u : AuthState ψ} {a γ st cm tok}
    (h : Cell σ u a γ st cm tok) (hcm : tok ≠ none → cm = σ) : p2Valid u = true := by
  obtain ⟨⟨h1, ⟨b, h2⟩, h3, h4, h5, h6, h7⟩, h8, h9⟩ := h
  unfold p2Valid
  rcases htok : tok with _ | t
  · rw [h6, htok]
  · have hs := h7 (by rw [htok]; exact Option.some_ne_none t)
    have hc := hcm (by rw [htok]; exact Option.some_ne_none t)
    rw [h6, htok]
    simp [AuthState.hasPath, h2, hs.1, hs.2, h5, hc]

end Cells

/-! ## Setting up the session: boundary start, lock propagation, acknowledgement, emission -/

section Setup
variable {ψ : Nat}

theorem compare_seq (κ : Nat) (l r l1 r1 l2 r2 l3 r3 : AuthState ψ) (a b : Nat)
    (hlp : l.core.path = .some a b) (hm : maintainAuth l r = (l1, r1))
    (hc : completeWaveAuth l1 r1 = (l2, r2)) (hw : waveAuth l2 r2 = (l3, r3))
    (hds : lift2 dropStray l3 r3 = (l3, r3)) :
    compareLifecycleAuth κ l r = (landBackwardAuth l3, landForwardAuth κ r3) := by
  unfold compareLifecycleAuth
  simp only [hlp]
  rw [hm]
  dsimp only
  rw [hc]
  dsimp only
  rw [hw]
  dsimp only
  rw [hds]

theorem route_ne_ready {s : MainState} (h : RouteSt s) : s ≠ .CHECK_ready := by
  unfold RouteSt at h
  rcases h with h | h | h | h | h <;> rw [h] <;> decide

/-- SIGMOVE without tokens on route cells is the identity. -/
theorem ms_quiet (hψ : ψ > 0) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hls : RouteSt l.core.state) (hrs : RouteSt r.core.state)
    (h1 : l.core.path2 = none) (h2 : r.core.path2 = none) (a b : Nat)
    (hrp : r.core.path = .some a b) : moveSourceAuth hψ c l r = (l, r) := by
  have hv1 : p2Valid l = true := by simp [p2Valid, h1]
  have hv2 : p2Valid r = true := by simp [p2Valid, h2]
  rw [moveSource_eq hψ c l r hl hr hls hrs hv1 hv2 a b hrp
    (by rw [mt_none c l r h1 h2, ac_none hψ l h1]; exact route_ne_ready hls)]
  rw [mt_none c l r h1 h2, ac_none hψ l h1, ac_none hψ r h2]

theorem ds_none (l r : AuthState ψ) (h1 : l.core.path2 = none) (h2 : r.core.path2 = none) :
    lift2 dropStray l r = (l, r) :=
  ds_id l r (fun t h => by rw [h1] at h; cases h) (fun t h => by rw [h2] at h; cases h)

/-- P, first edge: the boundary start of a fresh session `σ = fresh3 γ₀ γ₁`. -/
theorem compare_start (hψ2 : 2 ≤ ψ) (κ : Nat) (l r : AuthState ψ) (b b' : Nat)
    (hlp : l.core.path = .some (ψ - 1) b) (hrp : r.core.path = .some 0 b')
    (hls : l.core.state = .depart) (hrs : r.core.state = .depart)
    (hlc : l.ctrl_mark = l.path_mark) (hrc : r.ctrl_mark = r.path_mark)
    (hl2 : l.core.path2 = none) (hr2 : r.core.path2 = none) :
    compareLifecycleAuth κ l r =
      ({ l with ctrl_mark := fresh3 l.ctrl_mark r.ctrl_mark },
       { r with core := { r.core with state := .lock, path2 := none, path4 := none, path5 := none },
                ctrl_mark := fresh3 l.ctrl_mark r.ctrl_mark }) := by
  have hne : ψ - 1 ≠ 0 := by omega
  rw [compare_seq κ l r l r l r { l with ctrl_mark := fresh3 l.ctrl_mark r.ctrl_mark }
    { r with core := { r.core with state := .lock, path2 := none, path4 := none, path5 := none },
             ctrl_mark := fresh3 l.ctrl_mark r.ctrl_mark } (ψ - 1) b hlp
    (by simp [-Nat.right_eq_add, -Nat.left_eq_add, maintainAuth, hlp, hrp, hls, hrs, hlc, AuthState.st, lockedState])
    (by simp [-Nat.right_eq_add, -Nat.left_eq_add, completeWaveAuth, hlp, hrp, hls, hrs, AuthState.st, lockedState])
    (by simp [-Nat.right_eq_add, -Nat.left_eq_add, waveAuth, hlp, hrp, hls, hrs, hlc, hrc, sessionTokenOn, hl2, hr2, AuthState.st,
          lockedState, hne])
    (ds_none _ _ hl2 rfl)]
  simp [-Nat.right_eq_add, -Nat.left_eq_add, landBackwardAuth, landForwardAuth, hl2]

/-- P, second part: lock propagation into a `depart` successor below the terminal. -/
theorem compare_lockprop (κ : Nat) (l r : AuthState ψ) (k b b' : Nat) (σ : ProvColor)
    (hk : k + 1 < ψ - 1)
    (hlp : l.core.path = .some k b) (hrp : r.core.path = .some (k + 1) b')
    (hls : l.core.state = .lock) (hrs : r.core.state = .depart)
    (hlc : l.ctrl_mark = σ) (hl2 : l.core.path2 = none) (hr2 : r.core.path2 = none) :
    compareLifecycleAuth κ l r =
      (l, { r with core := { r.core with state := .lock }, ctrl_mark := σ }) := by
  have hne : k ≠ ψ - 1 := by omega
  have hne' : k + 1 ≠ ψ - 1 := by omega
  rw [compare_seq κ l r l r l { r with core := { r.core with state := .lock }, ctrl_mark := σ }
    l { r with core := { r.core with state := .lock }, ctrl_mark := σ } k b hlp
    (by simp [-Nat.right_eq_add, -Nat.left_eq_add, maintainAuth, hlp, hrp, hls, hrs, hne, AuthState.st, lockedState, waveState])
    (by simp [-Nat.right_eq_add, -Nat.left_eq_add, completeWaveAuth, hlp, hrp, hls, hrs, hlc, hne', AuthState.st, lockedState,
          AuthState.setState])
    (by simp [-Nat.right_eq_add, -Nat.left_eq_add, waveAuth, hlp, hrp, hls, hne, AuthState.st, lockedState])
    (ds_none _ _ hl2 hr2)]
  simp [-Nat.right_eq_add, -Nat.left_eq_add, landBackwardAuth, landForwardAuth, hl2, hr2]

/-- P, last lock step: the terminal successor is locked straight into `compare1`, which
acknowledges its predecessor at once. -/
theorem compare_lockprop_last (κ : Nat) (l r : AuthState ψ) (k b b' : Nat) (σ : ProvColor)
    (hk : k + 1 = ψ - 1)
    (hlp : l.core.path = .some k b) (hrp : r.core.path = .some (k + 1) b')
    (hls : l.core.state = .lock) (hrs : r.core.state = .depart)
    (hlc : l.ctrl_mark = σ) (hl2 : l.core.path2 = none) (hr2 : r.core.path2 = none) :
    compareLifecycleAuth κ l r =
      ({ l with core := { l.core with state := .compare1 } },
       { r with core := { r.core with state := .compare1 }, ctrl_mark := σ }) := by
  have hne : k ≠ ψ - 1 := by omega
  rw [compare_seq κ l r l r l { r with core := { r.core with state := .compare1 }, ctrl_mark := σ }
    { l with core := { l.core with state := .compare1 } }
    { r with core := { r.core with state := .compare1 }, ctrl_mark := σ } k b hlp
    (by simp [-Nat.right_eq_add, -Nat.left_eq_add, maintainAuth, hlp, hrp, hls, hrs, hne, AuthState.st, lockedState, waveState])
    (by simp [-Nat.right_eq_add, -Nat.left_eq_add, completeWaveAuth, hlp, hrp, hls, hrs, hlc, hk, AuthState.st, lockedState,
          AuthState.setState])
    (by simp [-Nat.right_eq_add, -Nat.left_eq_add, waveAuth, hlp, hrp, hls, hne, hlc, AuthState.st, lockedState, AuthState.setState])
    (ds_none _ _ hl2 hr2)]
  simp [-Nat.right_eq_add, -Nat.left_eq_add, landBackwardAuth, landForwardAuth, hl2, hr2]

/-- P, acknowledgement: a locked cell before a `compare1` successor becomes `compare1`. -/
theorem compare_ack (κ : Nat) (l r : AuthState ψ) (k b b' : Nat) (σ : ProvColor)
    (hk : k + 1 < ψ)
    (hlp : l.core.path = .some k b) (hrp : r.core.path = .some (k + 1) b')
    (hls : l.core.state = .lock) (hrs : r.core.state = .compare1)
    (hlc : l.ctrl_mark = σ) (hrc : r.ctrl_mark = σ)
    (hl2 : l.core.path2 = none) (hr2 : r.core.path2 = none) :
    compareLifecycleAuth κ l r = ({ l with core := { l.core with state := .compare1 } }, r) := by
  have hne : k ≠ ψ - 1 := by omega
  have hmod : k % ψ = k := Nat.mod_eq_of_lt (by omega)
  rw [compare_seq κ l r l r l r { l with core := { l.core with state := .compare1 } } r k b hlp
    (by simp [-Nat.right_eq_add, -Nat.left_eq_add, maintainAuth, hlp, hrp, hls, hrs, hne, hmod, hlc, hrc, AuthState.st, lockedState,
          waveState])
    (by simp [-Nat.right_eq_add, -Nat.left_eq_add, completeWaveAuth, hlp, hrp, hls, hrs, AuthState.st, lockedState])
    (by simp [-Nat.right_eq_add, -Nat.left_eq_add, waveAuth, hlp, hrp, hls, hrs, hne, hlc, hrc, AuthState.st, lockedState,
          AuthState.setState])
    (ds_none _ _ hl2 hr2)]
  simp [-Nat.right_eq_add, -Nat.left_eq_add, landBackwardAuth, landForwardAuth, hl2, hr2]

/-- W, first edge: the tail facing the acknowledged head becomes `compare2` and emits the
first backward token. `hl0` covers the two tail kinds (a session `depart` when the head is in
the next block, `compare1` when the block is its own successor). -/
theorem compare_emit (hψ2 : 2 ≤ ψ) (κ : Nat) (l r : AuthState ψ) (b b' : Nat) (σ : ProvColor)
    (hlp : l.core.path = .some (ψ - 1) b) (hrp : r.core.path = .some 0 b')
    (hl0 : (l.core.state = .depart ∧ σ ≠ l.path_mark) ∨ l.core.state = .compare1)
    (hrs : r.core.state = .compare1)
    (hlc : l.ctrl_mark = σ) (hrc : r.ctrl_mark = σ)
    (hl2 : l.core.path2 = none) (hr2 : r.core.path2 = none) :
    compareLifecycleAuth κ l r =
      ({ l with core := { l.core with state := .compare2, path2 := some ⟨0, 0, ψ - 1, 2⟩ },
                path2_scope := .session, path2_mark := σ }, r) := by
  have hne : ψ - 1 ≠ 0 := by omega
  have hm : (ψ - 1) % ψ = ψ - 1 := Nat.mod_eq_of_lt (by omega)
  have hne2 : ψ - 1 + 1 ≠ 0 := by omega
  have hds : lift2 dropStray
      ({ l with core := { l.core with state := .compare2, path2 := some ⟨0, 0, ψ - 1, 2⟩ },
                path2_scope := .session, path2_mark := σ }) r =
      ({ l with core := { l.core with state := .compare2, path2 := some ⟨0, 0, ψ - 1, 2⟩ },
                path2_scope := .session, path2_mark := σ }, r) :=
    ds_id _ _ (fun t h => by
      simp only [Option.some.injEq] at h; subst h; simp)
      (fun t h => by rw [hr2] at h; cases h)
  rcases hl0 with ⟨hls, hlm⟩ | hls
  · rw [compare_seq κ l r l r l r
      { l with core := { l.core with state := .compare2, path2 := some ⟨0, 0, ψ - 1, 2⟩ },
                path2_scope := .session, path2_mark := σ } r (ψ - 1) b hlp
      (by simp [-Nat.right_eq_add, -Nat.left_eq_add, maintainAuth, hlp, hrp, hls, hrs, hm, hlc, hrc, hlm, AuthState.st, lockedState,
            lockerState, waveState])
      (by simp [-Nat.right_eq_add, -Nat.left_eq_add, completeWaveAuth, hlp, hrp, hls, hrs, hne2, AuthState.st, lockedState])
      (by simp [-Nat.right_eq_add, -Nat.left_eq_add, waveAuth, hlp, hrp, hls, hrs, hlc, hrc, beq_ne_dec hlm, hl2, hr2, AuthState.st,
            lockedState, a2Token])
      hds]
    simp [-Nat.right_eq_add, -Nat.left_eq_add, landBackwardAuth, landForwardAuth, hr2, hne, hlp]
  · rw [compare_seq κ l r l r l r
      { l with core := { l.core with state := .compare2, path2 := some ⟨0, 0, ψ - 1, 2⟩ },
                path2_scope := .session, path2_mark := σ } r (ψ - 1) b hlp
      (by simp [-Nat.right_eq_add, -Nat.left_eq_add, maintainAuth, hlp, hrp, hls, hrs, hm, hlc, hrc, AuthState.st, lockedState,
            lockerState, waveState])
      (by simp [-Nat.right_eq_add, -Nat.left_eq_add, completeWaveAuth, hlp, hrp, hls, hrs, hne2, AuthState.st, lockedState])
      (by simp [-Nat.right_eq_add, -Nat.left_eq_add, waveAuth, hlp, hrp, hls, hrs, hlc, hrc, hl2, hr2, AuthState.st,
            lockedState, a2Token])
      hds]
    simp [-Nat.right_eq_add, -Nat.left_eq_add, landBackwardAuth, landForwardAuth, hr2, hne, hlp]

end Setup

section Steps
variable {ψ : Nat}

/-- `midS` after a computed SIGMOVE, as an equation. -/
theorem midS_eq (hψ : ψ > 0) (κ : Nat) (l r l2 r2 : AuthState ψ)
    (hms : moveSourceAuth hψ authFplusmcc l r = (l2, r2)) (hq1 : QCell l2) (hq2 : QCell r2) :
    ∃ d1 d2 : AuthState ψ, midS hψ κ authFplusmcc l r = compareLifecycleAuth κ d1 d2 ∧
      RV d1 = RV l2 ∧ d1.core.state = l2.core.state ∧ RV d2 = RV r2 ∧
      (d2.core.state = r2.core.state ∨
        (d2.core.state = .eliminate_signal ∧ r2.core.label.val = ψ - 1)) :=
  midS_via hψ κ l r l2 r2 hms hq1 hq2
    (fun q => ∃ d1 d2 : AuthState ψ, q = compareLifecycleAuth κ d1 d2 ∧
      RV d1 = RV l2 ∧ d1.core.state = l2.core.state ∧ RV d2 = RV r2 ∧
      (d2.core.state = r2.core.state ∨
        (d2.core.state = .eliminate_signal ∧ r2.core.label.val = ψ - 1)))
    (fun d1 d2 e1 e2 e3 e4 => ⟨d1, d2, rfl, e1, e2, e3, e4⟩)

/-- The pair leaves an interaction with the two given route views. -/
def Out (σ : ProvColor) (q : AuthState ψ × AuthState ψ)
    (a : Nat) (γl : ProvColor) (stl : MainState) (cml : ProvColor) (tokl : Option Path2Info)
    (a' : Nat) (γr : ProvColor) (str : MainState) (cmr : ProvColor) (tokr : Option Path2Info) :
    Prop :=
  CV σ q.1 a γl stl cml tokl ∧ CV σ q.2 a' γr str cmr tokr

theorem NPD_of_route {s : MainState} (h : RouteSt s) : NPD s := by
  unfold RouteSt at h
  rcases h with h | h | h | h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩

/-- An interaction on two route cells, given what `midS` does on any cells with the same
views: a deletion, a leader, or the predicted views (as cells: no leader, no reset). -/
theorem pipe_cells (hψ : ψ > 0) (κ : Nat) (σ : ProvColor) (l r : AuthState ψ)
    {a γl stl cml tokl a' γr str cmr tokr}
    (hl : Cell σ l a γl stl cml tokl) (hr : Cell σ r a' γr str cmr tokr)
    (hnext : a' = (a + 1) % ψ) (hNl : NPD stl) (hNr : NPD str)
    (Q : AuthState ψ × AuthState ψ → Prop)
    (hQV : ∀ m m' : AuthState ψ × AuthState ψ, V m'.1 = V m.1 → V m'.2 = V m.2 → Q m → Q m')
    (hmid : ∀ l' r', Cell σ l' a γl stl cml tokl → Cell σ r' a' γr str cmr tokr →
      HP (midS hψ κ authFplusmcc l' r') ∨ (midS hψ κ authFplusmcc l' r').2.core.leader = true ∨
        Q (midS hψ κ authFplusmcc l' r')) :
    HP (pipeline hψ κ authFplusmcc l r) ∨ (pipeline hψ κ authFplusmcc l r).1.core.leader = true ∨
      (pipeline hψ κ authFplusmcc l r).2.core.leader = true ∨
      (Q (pipeline hψ κ authFplusmcc l r) ∧ (pipeline hψ κ authFplusmcc l r).1.core.leader = false ∧
        (pipeline hψ κ authFplusmcc l r).2.core.leader = false ∧
        (pipeline hψ κ authFplusmcc l r).1.core.reset_cmd = false ∧
        (pipeline hψ κ authFplusmcc l r).2.core.reset_cmd = false) := by
  have hl0 := hl
  have hr0 := hr
  obtain ⟨⟨la, ⟨lb, lp⟩, -, ls, -, -, -⟩, lL, lR⟩ := hl0
  obtain ⟨⟨ra, ⟨rb, rp⟩, -, rs, -, -, -⟩, rL, rR⟩ := hr0
  refine pipe_step hψ κ authFplusmcc l r lL rL lR rR ?_ (by rw [lp]; exact PathInfo.noConfusion)
    (by rw [ls]; exact hNl.1) (by rw [ls]; exact hNl.2) (by rw [rs]; exact hNr.1)
    (by rw [rs]; exact hNr.2) Q hQV (fun l' r' s1 s2 => hmid l' r' (hl.of_same s1) (hr.of_same s2))
  apply Fin.ext
  simp only [ra, la, hnext]

theorem Out.of_V {σ : ProvColor} {a γl stl cml tokl a' γr str cmr tokr}
    (m m' : AuthState ψ × AuthState ψ) (h1 : V m'.1 = V m.1) (h2 : V m'.2 = V m.2)
    (h : Out σ m a γl stl cml tokl a' γr str cmr tokr) :
    Out σ m' a γl stl cml tokl a' γr str cmr tokr :=
  ⟨h.1.of_V h1, h.2.of_V h2⟩

/-- Step form: deletion, leader, or two cells with the predicted views. -/
def StepRes (σ : ProvColor) (q : AuthState ψ × AuthState ψ)
    (a : Nat) (γl : ProvColor) (stl : MainState) (cml : ProvColor) (tokl : Option Path2Info)
    (a' : Nat) (γr : ProvColor) (str : MainState) (cmr : ProvColor) (tokr : Option Path2Info) :
    Prop :=
  HP q ∨ q.1.core.leader = true ∨ q.2.core.leader = true ∨
    (Cell σ q.1 a γl stl cml tokl ∧ Cell σ q.2 a' γr str cmr tokr)

theorem step_of_mid (hψ : ψ > 0) (κ : Nat) (σ σ' : ProvColor) (l r : AuthState ψ)
    {a γl stl cml tokl a' γr str cmr tokr stl' cml' tokl' str' cmr' tokr'}
    (hl : Cell σ l a γl stl cml tokl) (hr : Cell σ r a' γr str cmr tokr)
    (hnext : a' = (a + 1) % ψ) (hNl : NPD stl) (hNr : NPD str)
    (hmid : ∀ l' r', Cell σ l' a γl stl cml tokl → Cell σ r' a' γr str cmr tokr →
      Out σ' (midS hψ κ authFplusmcc l' r') a γl stl' cml' tokl' a' γr str' cmr' tokr') :
    StepRes σ' (pipeline hψ κ authFplusmcc l r) a γl stl' cml' tokl' a' γr str' cmr' tokr' := by
  rcases pipe_cells hψ κ σ l r hl hr hnext hNl hNr
    (fun q => Out σ' q a γl stl' cml' tokl' a' γr str' cmr' tokr')
    (fun m m' h1 h2 h => Out.of_V m m' h1 h2 h)
    (fun l' r' h1 h2 => Or.inr (Or.inr (hmid l' r' h1 h2))) with h | h | h | ⟨h, h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨h.1, h1, h3⟩, ⟨h.2, h2, h4⟩⟩))

/-! ### The setup steps -/

theorem route_depart : RouteSt .depart := Or.inl rfl
theorem route_lock : RouteSt .lock := Or.inr (Or.inl rfl)
theorem route_c1 : RouteSt .compare1 := Or.inr (Or.inr (Or.inl rfl))
theorem route_c2 : RouteSt .compare2 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
theorem route_elim : RouteSt .eliminate_signal := Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem mid_start (hψ : ψ > 0) (hψ2 : 2 ≤ ψ) (κ : Nat) (σ γ0 γ1 : ProvColor) (l r : AuthState ψ)
    (hl : Cell σ l (ψ - 1) γ0 .depart γ0 none) (hr : Cell σ r 0 γ1 .depart γ1 none) :
    Out (fresh3 γ0 γ1) (midS hψ κ authFplusmcc l r) (ψ - 1) γ0 .depart (fresh3 γ0 γ1) none
      0 γ1 .lock (fresh3 γ0 γ1) none := by
  obtain ⟨rb0, rp0⟩ := hr.1.2.1
  have hms : moveSourceAuth hψ authFplusmcc l r = (l, r) :=
    ms_quiet hψ _ l r hl.2.1 hr.2.1 (hl.1.2.2.2.1 ▸ route_depart) (hr.1.2.2.2.1 ▸ route_depart)
      hl.1.2.2.2.2.2.1 hr.1.2.2.2.2.2.1 0 rb0 rp0
  obtain ⟨d1, d2, he, e1, e2, e3, e4⟩ := midS_eq hψ κ l r l r hms
    (hl.qcell route_depart (by intro h; cases h)) (hr.qcell route_depart (by intro h; cases h))
  rw [he]
  have hd1 := hl.of_RV e1 e2
  have e4' : d2.core.state = r.core.state := by
    rcases e4 with h | h
    · exact h
    · exfalso; have := h.2; rw [hr.1.1] at this; omega
  have hd2 := hr.of_RV e3 e4'
  obtain ⟨⟨a1, ⟨b1, p1⟩, m1, s1, c1, t1, -⟩, -, -⟩ := hd1
  obtain ⟨⟨a2, ⟨b2, p2⟩, m2, s2, c2, t2, -⟩, -, -⟩ := hd2
  rw [compare_start hψ2 κ d1 d2 b1 b2 p1 p2 s1 s2 (c1.trans m1.symm) (c2.trans m2.symm) t1 t2]
  rw [c1, c2]
  exact ⟨⟨a1, ⟨b1, p1⟩, m1, s1, rfl, t1, fun h => absurd rfl h⟩,
    ⟨a2, ⟨b2, p2⟩, m2, rfl, rfl, rfl, fun h => absurd rfl h⟩⟩

theorem ds_state (l r : AuthState ψ) :
    (lift2 dropStray l r).1.core.state = l.core.state ∧
      (lift2 dropStray l r).2.core.state = r.core.state := by
  unfold lift2 dropStray
  dsimp only
  constructor <;> split <;> (try split) <;> rfl

theorem lbA_state (u : AuthState ψ) : (landBackwardAuth u).core.state = u.core.state := by
  unfold landBackwardAuth landBackward AuthState.withCore AuthState.dropP2
  repeat' (first | (dsimp only) | split)
  all_goals rfl

theorem lfA_state (κ : Nat) (u : AuthState ψ) : (landForwardAuth κ u).core.state = u.core.state := by
  unfold landForwardAuth landForward AuthState.withCore AuthState.dropP2
  repeat' (first | (dsimp only) | split)
  all_goals rfl

theorem NPD_none : NPD MainState.none := ⟨by decide, by decide⟩
theorem NPD_depart : NPD MainState.depart := ⟨by decide, by decide⟩
theorem NPD_c1 : NPD MainState.compare1 := ⟨by decide, by decide⟩
theorem NPD_c2 : NPD MainState.compare2 := ⟨by decide, by decide⟩
theorem NPD_elim : NPD MainState.eliminate_signal := ⟨by decide, by decide⟩

/-- The comparison lifecycle keeps a responder in `eliminate_signal` and creates no
`produce`/`done` initiator. -/
theorem compare_elimR (κ : Nat) (l r : AuthState ψ) (a b : Nat) (hlp : l.core.path = .some a b)
    (hl : NPD l.core.state) (hr : r.core.state = .eliminate_signal) :
    NPD (compareLifecycleAuth κ l r).1.core.state ∧
      (compareLifecycleAuth κ l r).2.core.state = .eliminate_signal := by
  unfold compareLifecycleAuth
  simp only [hlp]
  have hm1 := (maintain_state l r).1
  have hm2 := (maintain_elim l r).2 hr
  generalize maintainAuth l r = M at hm1 hm2
  obtain ⟨m1, m2⟩ := M
  dsimp only at hm1 hm2 ⊢
  have n1 : NPD m1.core.state := by
    rcases hm1 with h | h | h <;> rw [h]
    · exact hl
    · exact NPD_none
    · exact NPD_depart
  have hc1 := (completeWave_state m1 m2).1
  have hc2 := (completeWave_elim m1 m2).2 hm2
  generalize completeWaveAuth m1 m2 = Cw at hc1 hc2
  obtain ⟨c1, c2⟩ := Cw
  dsimp only at hc1 hc2 ⊢
  have n2 : NPD c1.core.state := by
    rcases hc1 with h | h <;> rw [h]
    · exact n1
    · exact NPD_c1
  have hw1 := (wave_state c1 c2).1
  have hw2 := (wave_elim c1 c2).2 hc2
  generalize waveAuth c1 c2 = W at hw1 hw2
  obtain ⟨w1, w2⟩ := W
  dsimp only at hw1 hw2 ⊢
  have n3 : NPD w1.core.state := by
    rcases hw1 with h | h | h <;> rw [h]
    · exact n2
    · exact NPD_c1
    · exact NPD_c2
  have hd := ds_state w1 w2
  generalize lift2 dropStray w1 w2 = D at hd
  obtain ⟨d1, d2⟩ := D
  dsimp only at hd ⊢
  rw [lbA_state, lfA_state, hd.1, hd.2]
  exact ⟨n3, hw2⟩

/-- The comparison lifecycle keeps an initiator in `eliminate_signal`. -/
theorem compare_elimL (κ : Nat) (l r : AuthState ψ) (a b : Nat) (hlp : l.core.path = .some a b)
    (hl : l.core.state = .eliminate_signal) :
    (compareLifecycleAuth κ l r).1.core.state = .eliminate_signal := by
  unfold compareLifecycleAuth
  simp only [hlp]
  have hm1 := (maintain_elim l r).1 hl
  generalize maintainAuth l r = M at hm1
  obtain ⟨m1, m2⟩ := M
  dsimp only at hm1 ⊢
  have hc1 := (completeWave_elim m1 m2).1 hm1
  generalize completeWaveAuth m1 m2 = Cw at hc1
  obtain ⟨c1, c2⟩ := Cw
  dsimp only at hc1 ⊢
  have hw1 := (wave_elim c1 c2).1 hc1
  generalize waveAuth c1 c2 = W at hw1
  obtain ⟨w1, w2⟩ := W
  dsimp only at hw1 ⊢
  have hd := ds_state w1 w2
  generalize lift2 dropStray w1 w2 = D at hd
  obtain ⟨d1, d2⟩ := D
  dsimp only at hd ⊢
  rw [lbA_state, hd.1]
  exact hw1

theorem compare_label (κ : Nat) (l r : AuthState ψ) :
    (compareLifecycleAuth κ l r).1.core.label = l.core.label ∧
      (compareLifecycleAuth κ l r).2.core.label = r.core.label := by
  obtain ⟨h1, h2, -⟩ := compare_FR κ l r
  simp only [av, dv, wv, Prod.mk.injEq] at h1 h2
  exact ⟨h1.2.2.1, h2.2.2⟩

/-- A responder deletion exit: the responder is in `eliminate_signal` at label `a'`, the
initiator at label `a` holds its path in a state other than `produce`/`done`. -/
def EQ (q : AuthState ψ × AuthState ψ) (a a' : Nat) : Prop :=
  q.1.core.label.val = a ∧ (∃ b, q.1.core.path = .some a b) ∧ NPD q.1.core.state ∧
    q.2.core.label.val = a' ∧ (∃ b, q.2.core.path = .some a' b) ∧
    q.2.core.state = .eliminate_signal

theorem EQ.of_V {a a' : Nat} (m m' : AuthState ψ × AuthState ψ) (h1 : V m'.1 = V m.1)
    (h2 : V m'.2 = V m.2) (h : EQ m a a') : EQ m' a a' := by
  simp only [V, Prod.mk.injEq] at h1 h2
  obtain ⟨h1a, ⟨b, h1b⟩, h1c, h1d, ⟨b', h1e⟩, h1f⟩ := h
  exact ⟨by rw [h1.2.2.2.1]; exact h1a, ⟨b, by rw [h1.2.1]; exact h1b⟩, by rw [h1.1]; exact h1c,
    by rw [h2.2.2.2.1]; exact h1d, ⟨b', by rw [h2.2.1]; exact h1e⟩, by rw [h2.1]; exact h1f⟩

theorem compare_EQ (κ : Nat) (l r : AuthState ψ) (a a' b b' : Nat) (hla : l.core.label.val = a)
    (hlp : l.core.path = .some a b) (hl : NPD l.core.state) (hra : r.core.label.val = a')
    (hrp : r.core.path = .some a' b') (hr : r.core.state = .eliminate_signal) :
    EQ (compareLifecycleAuth κ l r) a a' := by
  have he := compare_elimR κ l r a b hlp hl hr
  have hp := compare_path κ l r
  have hL := compare_label κ l r
  exact ⟨by rw [hL.1]; exact hla, ⟨b, by rw [hp.1]; exact hlp⟩, he.1,
    by rw [hL.2]; exact hra, ⟨b', by rw [hp.2]; exact hrp⟩, he.2⟩

/-! ### Token moves -/

/-- The wave stages are inert on every pair with the given views. -/
def InertV (σ : ProvColor) (a : Nat) (γl : ProvColor) (stl : MainState) (cml : ProvColor)
    (tokl : Option Path2Info) (a' : Nat) (γr : ProvColor) (str : MainState) (cmr : ProvColor)
    (tokr : Option Path2Info) : Prop :=
  ∀ d1 d2 : AuthState ψ, CV σ d1 a γl stl cml tokl → CV σ d2 a' γr str cmr tokr → Inert d1 d2

theorem inertV_sd_sd (σ γl γr : ProvColor) (a : Nat) (tl tr : Option Path2Info)
    (hl : σ ≠ γl) (hr : σ ≠ γr) :
    InertV (ψ := ψ) σ a γl .depart σ tl (a + 1) γr .depart σ tr := by
  intro d1 d2 h1 h2
  obtain ⟨-, ⟨b1, p1⟩, m1, s1, c1, -, -⟩ := h1
  obtain ⟨-, ⟨b2, p2⟩, m2, s2, c2, -, -⟩ := h2
  exact inert_sd_sd d1 d2 a b1 b2 σ p1 p2 s1 s2 c1 c2 (m1 ▸ hl) (m2 ▸ hr)

theorem inertV_sd_c2 (σ γl γr : ProvColor) (a : Nat) (tl tr : Option Path2Info)
    (hl : σ ≠ γl) :
    InertV (ψ := ψ) σ a γl .depart σ tl (a + 1) γr .compare2 σ tr := by
  intro d1 d2 h1 h2
  obtain ⟨-, ⟨b1, p1⟩, m1, s1, c1, -, -⟩ := h1
  obtain ⟨-, ⟨b2, p2⟩, m2, s2, c2, -, -⟩ := h2
  exact inert_sd_c2 d1 d2 a b1 b2 σ p1 p2 s1 s2 c1 c2 (m1 ▸ hl)

theorem inertV_c2_c1 (hψ : ψ > 0) (σ γl γr : ProvColor) (tl tr : Option Path2Info)
    (htok : tl ≠ none ∨ tr ≠ none) :
    InertV (ψ := ψ) σ (ψ - 1) γl .compare2 σ tl 0 γr .compare1 σ tr := by
  intro d1 d2 h1 h2
  obtain ⟨-, ⟨b1, p1⟩, m1, s1, c1, t1, -⟩ := h1
  obtain ⟨-, ⟨b2, p2⟩, m2, s2, c2, t2, -⟩ := h2
  exact inert_c2_c1 hψ d1 d2 b1 b2 σ p1 p2 s1 s2 c1 c2 (by rw [t1, t2]; exact htok)

theorem inertV_c1_c1 (σ γl γr : ProvColor) (a : Nat) (tl tr : Option Path2Info)
    (hne : a ≠ ψ - 1) (hlt : a < ψ) :
    InertV (ψ := ψ) σ a γl .compare1 σ tl (a + 1) γr .compare1 σ tr := by
  intro d1 d2 h1 h2
  obtain ⟨-, ⟨b1, p1⟩, m1, s1, c1, -, -⟩ := h1
  obtain ⟨-, ⟨b2, p2⟩, m2, s2, c2, -, -⟩ := h2
  exact inert_c1_c1 d1 d2 a b1 b2 σ p1 p2 s1 s2 c1 c2 hne hlt

theorem inertV_c1_c2 (σ γl γr : ProvColor) (a : Nat) (tl tr : Option Path2Info)
    (hne : a ≠ ψ - 1) :
    InertV (ψ := ψ) σ a γl .compare1 σ tl (a + 1) γr .compare2 σ tr := by
  intro d1 d2 h1 h2
  obtain ⟨-, ⟨b1, p1⟩, m1, s1, c1, -, -⟩ := h1
  obtain ⟨-, ⟨b2, p2⟩, m2, s2, c2, -, -⟩ := h2
  exact inert_c1_c2 d1 d2 a b1 b2 σ p1 p2 s1 s2 c1 c2 hne

theorem Cell.dropP2 {σ : ProvColor} {u : AuthState ψ} {a γ st cm tok}
    (h : Cell σ u a γ st cm tok) : Cell σ u.dropP2 a γ st cm none := by
  obtain ⟨⟨h1, h2, h3, h4, h5, -, -⟩, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, rfl, fun h => absurd rfl h⟩, h8, h9⟩

theorem Cell.recv {σ : ProvColor} {l r : AuthState ψ} {a γ st cm} (e : Entry) (t : Path2Info)
    (h : Cell σ l a γ st cm none) (hs : r.path2_scope = .session) (hm : r.path2_mark = σ)
    (he : (e = .ok ∧ cm = σ) ∨ (e = .claim ∧ st = .depart)) :
    Cell σ (receive e r l t) a γ st σ (some t) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, -, -⟩, h8, h9⟩ := h
  rcases he with ⟨he, hc⟩ | ⟨he, hd⟩
  · subst he
    exact ⟨⟨h1, h2, h3, h4, h5.trans hc, rfl, fun _ => ⟨hs, hm⟩⟩, h8, h9⟩
  · subst he
    refine ⟨⟨h1, h2, h3, ?_, ?_, rfl, fun _ => ⟨hs, hm⟩⟩, h8, h9⟩
    · unfold receive
      dsimp only
      rw [if_pos rfl]
      unfold claimA2
      dsimp only
      split
      · exact h4
      · exact hd.symm
    · unfold receive
      dsimp only
      rw [if_pos rfl]
      exact hm

theorem dec_action (t : Path2Info) : (dec t).action = t.action := by
  unfold dec; split <;> rfl

/-- A left-moving token (A2 in transit, or A3 below the terminal) crosses the edge; the
receiving cell is entered normally or claimed (a lineage `depart` in round 0). -/
theorem ms_left (hψ : ψ > 0) (σ : ProvColor) (l r : AuthState ψ) {a γl stl cml a' γr str}
    (t : Path2Info) (e : Entry)
    (hl : Cell σ l a γl stl cml none) (hr : Cell σ r a' γr str σ (some t))
    (hsl : RouteSt stl) (hsr : RouteSt str)
    (ht : (t.action = 2 ∧ t.position ≠ 0) ∨ (t.action = 3 ∧ a' ≠ ψ - 1 ∧ a ≠ ψ - 1))
    (hent : (e = .ok ∧ cml = σ ∧ (waveState stl = true ∨ stl = .depart)) ∨
      (e = .claim ∧ cml ≠ σ ∧ stl = .depart ∧ t.action = 2)) :
    moveSourceAuth hψ authFplusmcc l r = (receive e r l (dec t), r.dropP2) := by
  have hl0 := hl
  have hr0 := hr
  obtain ⟨⟨la, ⟨lb, lp⟩, lm, ls, lc, l2, -⟩, lL, lR⟩ := hl0
  obtain ⟨⟨ra, ⟨rb, rp⟩, rm, rs, rc, r2, rt⟩, rL, rR⟩ := hr0
  obtain ⟨rsc, rmk⟩ := rt (Option.some_ne_none t)
  have hmv : canMoveL r.core t = true := by
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2, -⟩
    · simp [canMoveL, h1, h2]
    · simp [canMoveL, h1, ra, h2]
  have hhp : l.hasPath = true := by simp [AuthState.hasPath, lp]
  have hentry : entry authFplusmcc.claimCheck r l t = e := by
    rcases hent with ⟨he, hc, hw⟩ | ⟨he, hc, hd, ha⟩
    · subst he
      rcases ht with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact entry_ok2 _ r l t hhp rsc h1 (by rw [lc, hc, rmk]) (by rw [ls]; exact hw)
      · exact entry_ok _ r l t hhp rsc (by rw [h1]; decide) (by rw [lc, hc, rmk])
    · subst he
      exact entry_claim _ r l t hhp rsc ha (by rw [lc, rmk]; exact hc) (by rw [ls]; exact hd)
  have hne : e ≠ .reject := by
    rcases hent with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;> decide
  have hf : l.ctrl_mark = r.path2_mark ∨ claimable authFplusmcc.claimCheck l = true := by
    rcases hent with ⟨-, hc, -⟩ | ⟨-, -, hd, -⟩
    · left; rw [lc, hc, rmk]
    · right; simp [claimable, AuthState.st, ls, hd]
  have hmt := mt_L authFplusmcc l r t e l2 r2 hmv hentry hne hf
  have hrc : Cell σ (receive e r l (dec t)) a γl stl σ (some (dec t)) :=
    hl.recv e (dec t) rsc rmk (by
      rcases hent with ⟨he, hc, -⟩ | ⟨he, -, hd, -⟩
      · exact Or.inl ⟨he, hc⟩
      · exact Or.inr ⟨he, hd⟩)
  have hac : applyControlAuth hψ (receive e r l (dec t)) = receive e r l (dec t) := by
    obtain ⟨⟨qa, -, -, -, qc, q2, qt⟩, -, -⟩ := hrc
    obtain ⟨qs, qm⟩ := qt (Option.some_ne_none _)
    rcases ht with ⟨h1, -⟩ | ⟨h1, -, h3⟩
    · exact ac_12 hψ _ (dec t) q2 (Or.inr ((dec_action t).trans h1))
    · exact ac_34_mid hψ _ (dec t) q2 (Or.inl ((dec_action t).trans h1)) qs (qm.trans qc.symm)
        (by rw [qa]; exact h3)
  have hck : (applyControlAuth hψ (moveTokensAuth authFplusmcc l r).1).core.state ≠
      .CHECK_ready := by
    rw [hmt]
    dsimp only
    rw [hac, hrc.1.2.2.2.1]
    exact route_ne_ready hsl
  have hv1 := hl.valid (fun h => absurd rfl h)
  have hv2 := hr.valid (fun _ => rfl)
  rw [moveSource_eq hψ authFplusmcc l r lL rL (ls ▸ hsl) (rs ▸ hsr) hv1 hv2 a' rb rp hck]
  rw [hmt]
  dsimp only
  rw [hac, ac_none hψ _ rfl]

theorem RV_pl {u v : AuthState ψ} (h : RV v = RV u) :
    v.core.path = u.core.path ∧ v.core.label = u.core.label := by
  simp only [RV, Prod.mk.injEq] at h
  exact ⟨h.1, h.2.2.1⟩

theorem Cell.npd {σ : ProvColor} {u : AuthState ψ} {a γ st cm tok}
    (h : Cell σ u a γ st cm tok) (hs : RouteSt st) : NPD u.core.state := by
  rw [h.1.2.2.2.1]; exact NPD_of_route hs

/-- The deletion exit of a pair whose responder turned `eliminate_signal` in DISAPPEAR. -/
theorem EQ_of_elim (κ : Nat) {σ : ProvColor} (d1 d2 l2 r2 : AuthState ψ)
    {a γl stl cml tokl a' γr str cmr tokr}
    (h1 : Cell σ l2 a γl stl cml tokl) (h2 : Cell σ r2 a' γr str cmr tokr) (hs : RouteSt stl)
    (e1 : RV d1 = RV l2) (e2 : d1.core.state = l2.core.state) (e3 : RV d2 = RV r2)
    (e4 : d2.core.state = .eliminate_signal) : EQ (compareLifecycleAuth κ d1 d2) a a' := by
  have hd1 := h1.of_RV e1 e2
  obtain ⟨⟨a1, ⟨b1, p1⟩, -, -, -, -, -⟩, -, -⟩ := id hd1
  obtain ⟨⟨a2, ⟨b2, p2⟩, -, -, -, -, -⟩, -, -⟩ := id h2
  obtain ⟨q1, q2⟩ := RV_pl e3
  exact compare_EQ κ d1 d2 a a' b1 b2 a1 p1 (hd1.npd hs) (by rw [q2]; exact a2)
    (by rw [q1]; exact p2) e4

/-- A2/A3 crossing leftwards, not landing and not applied. -/
theorem mid_left (hψ : ψ > 0) (κ : Nat) (σ : ProvColor) (l r : AuthState ψ)
    {a γl stl cml a' γr str} (t : Path2Info) (e : Entry)
    (hl : Cell σ l a γl stl cml none) (hr : Cell σ r a' γr str σ (some t))
    (hsl : RouteSt stl) (hsr : RouteSt str) (hlk : stl ≠ .lock) (hrk : str ≠ .lock)
    (ht : (t.action = 2 ∧ t.position ≠ 0) ∨ (t.action = 3 ∧ a' ≠ ψ - 1 ∧ a ≠ ψ - 1))
    (hent : (e = .ok ∧ cml = σ ∧ (waveState stl = true ∨ stl = .depart)) ∨
      (e = .claim ∧ cml ≠ σ ∧ stl = .depart ∧ t.action = 2))
    (hnl : ¬ ((dec t).action = 2 ∧ (dec t).position = 0))
    (hin : InertV (ψ := ψ) σ a γl stl σ (some (dec t)) a' γr str σ none) :
    Out σ (midS hψ κ authFplusmcc l r) a γl stl σ (some (dec t)) a' γr str σ none ∨
      EQ (midS hψ κ authFplusmcc l r) a a' := by
  have hms := ms_left hψ σ l r t e hl hr hsl hsr ht hent
  have hc1 : Cell σ (receive e r l (dec t)) a γl stl σ (some (dec t)) := by
    obtain ⟨rsc, rmk⟩ := hr.1.2.2.2.2.2.2 (Option.some_ne_none t)
    exact hl.recv e (dec t) rsc rmk (by
      rcases hent with ⟨he, hc, -⟩ | ⟨he, -, hd, -⟩
      · exact Or.inl ⟨he, hc⟩
      · exact Or.inr ⟨he, hd⟩)
  have hc2 := hr.dropP2
  obtain ⟨d1, d2, he, e1, e2, e3, e4⟩ := midS_eq hψ κ l r _ _ hms
    (hc1.qcell hsl (fun h => absurd h hlk)) (hc2.qcell hsr (fun h => absurd h hrk))
  rw [he]
  rcases e4 with e4 | ⟨e4, -⟩
  · left
    have hd1 := hc1.of_RV e1 e2
    have hd2 := hc2.of_RV e3 e4
    have ha1 : (dec t).action ≠ 1 := by
      rw [dec_action]; rcases ht with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
    obtain ⟨⟨a1, ⟨b1, p1⟩, m1, s1, c1, t1, -⟩, -, -⟩ := id hd1
    obtain ⟨⟨a2, ⟨b2, p2⟩, m2, s2, c2, t2, -⟩, -, -⟩ := id hd2
    rw [compare_inert κ d1 d2 a b1 p1 (hin d1 d2 hd1.1 hd2.1)
      (ds_id d1 d2 (fun t' h => by rw [t1] at h; cases h; exact fun h' => ha1 h'.1)
        (fun t' h => by rw [t2] at h; cases h))]
    rw [lb_other d1 (dec t) t1 hnl, lf_none κ d2 t2]
    exact ⟨hd1.1, hd2.1⟩
  · right
    exact EQ_of_elim κ d1 d2 _ _ hc1 hc2 hsl e1 e2 e3 e4

/-- A2 landing on its target: the next forward token carries the target's path bit. -/
theorem mid_left_land (hψ : ψ > 0) (κ : Nat) (σ : ProvColor) (l r : AuthState ψ)
    {a γl stl cml a' γr str} (e : Entry)
    (hl : Cell σ l a γl stl cml none) (hr : Cell σ r a' γr str σ (some ⟨a, 0, 1, 2⟩))
    (hsl : RouteSt stl) (hsr : RouteSt str) (hlk : stl ≠ .lock) (hrk : str ≠ .lock)
    (hent : (e = .ok ∧ cml = σ ∧ (waveState stl = true ∨ stl = .depart)) ∨
      (e = .claim ∧ cml ≠ σ ∧ stl = .depart))
    (hin : InertV (ψ := ψ) σ a γl stl σ (some ⟨a, 0, 0, 2⟩) a' γr str σ none) :
    (∃ lb, Out σ (midS hψ κ authFplusmcc l r) a γl stl σ (some ⟨a, lb, ψ, 1⟩) a' γr str σ none) ∨
      EQ (midS hψ κ authFplusmcc l r) a a' := by
  have hdec : dec (⟨a, 0, 1, 2⟩ : Path2Info) = ⟨a, 0, 0, 2⟩ := by simp [dec]
  have hent' : (e = .ok ∧ cml = σ ∧ (waveState stl = true ∨ stl = .depart)) ∨
      (e = .claim ∧ cml ≠ σ ∧ stl = .depart ∧ (⟨a, 0, 1, 2⟩ : Path2Info).action = 2) := by
    rcases hent with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3, rfl⟩
  have hms := ms_left hψ σ l r ⟨a, 0, 1, 2⟩ e hl hr hsl hsr (Or.inl ⟨rfl, Nat.one_ne_zero⟩) hent'
  rw [hdec] at hms
  have hc1 : Cell σ (receive e r l ⟨a, 0, 0, 2⟩) a γl stl σ (some ⟨a, 0, 0, 2⟩) := by
    obtain ⟨rsc, rmk⟩ := hr.1.2.2.2.2.2.2 (Option.some_ne_none _)
    exact hl.recv e _ rsc rmk (by
      rcases hent with ⟨he, hc, -⟩ | ⟨he, -, hd⟩
      · exact Or.inl ⟨he, hc⟩
      · exact Or.inr ⟨he, hd⟩)
  have hc2 := hr.dropP2
  obtain ⟨d1, d2, he, e1, e2, e3, e4⟩ := midS_eq hψ κ l r _ _ hms
    (hc1.qcell hsl (fun h => absurd h hlk)) (hc2.qcell hsr (fun h => absurd h hrk))
  rw [he]
  rcases e4 with e4 | ⟨e4, -⟩
  · left
    have hd1 := hc1.of_RV e1 e2
    have hd2 := hc2.of_RV e3 e4
    obtain ⟨⟨a1, ⟨b1, p1⟩, m1, s1, c1, t1, tt1⟩, -, -⟩ := id hd1
    obtain ⟨⟨a2, ⟨b2, p2⟩, m2, s2, c2, t2, -⟩, -, -⟩ := id hd2
    obtain ⟨sc1, mk1⟩ := tt1 (Option.some_ne_none _)
    rw [compare_inert κ d1 d2 a b1 p1 (hin d1 d2 hd1.1 hd2.1)
      (ds_id d1 d2 (fun t' h => by rw [t1] at h; cases h; simp)
        (fun t' h => by rw [t2] at h; cases h))]
    rw [lb_land d1 a b1 p1 t1 sc1 (mk1.trans c1.symm), lf_none κ d2 t2]
    exact ⟨b1, ⟨a1, ⟨b1, p1⟩, m1, s1, c1, rfl, fun _ => ⟨sc1, mk1⟩⟩, hd2.1⟩
  · right
    exact EQ_of_elim κ d1 d2 _ _ hc1 hc2 hsl e1 e2 e3 e4

/-- An initiator deletion exit: the initiator is in `eliminate_signal` at label `a`; the
responder at label `a'` holds its path in a state other than `produce`/`done`. -/
def EQL (q : AuthState ψ × AuthState ψ) (a a' : Nat) : Prop :=
  q.1.core.label.val = a ∧ (∃ b, q.1.core.path = .some a b) ∧
    q.1.core.state = .eliminate_signal ∧
    q.2.core.label.val = a' ∧ (∃ b, q.2.core.path = .some a' b) ∧ NPD q.2.core.state

theorem EQL.of_V {a a' : Nat} (m m' : AuthState ψ × AuthState ψ) (h1 : V m'.1 = V m.1)
    (h2 : V m'.2 = V m.2) (h : EQL m a a') : EQL m' a a' := by
  simp only [V, Prod.mk.injEq] at h1 h2
  obtain ⟨h1a, ⟨b, h1b⟩, h1c, h1d, ⟨b', h1e⟩, h1f⟩ := h
  exact ⟨by rw [h1.2.2.2.1]; exact h1a, ⟨b, by rw [h1.2.1]; exact h1b⟩, by rw [h1.1]; exact h1c,
    by rw [h2.2.2.2.1]; exact h1d, ⟨b', by rw [h2.2.1]; exact h1e⟩, by rw [h2.1]; exact h1f⟩

/-- No stage of the comparison lifecycle creates a `produce`/`done` cell. -/
theorem compare_NPD (κ : Nat) (l r : AuthState ψ) (a b : Nat) (hlp : l.core.path = .some a b)
    (hl : NPD l.core.state) (hr : NPD r.core.state) :
    NPD (compareLifecycleAuth κ l r).1.core.state ∧
      NPD (compareLifecycleAuth κ l r).2.core.state := by
  unfold compareLifecycleAuth
  simp only [hlp]
  have hm := maintain_state l r
  generalize maintainAuth l r = M at hm
  obtain ⟨m1, m2⟩ := M
  dsimp only at hm ⊢
  have n1 : NPD m1.core.state := by
    rcases hm.1 with h | h | h <;> rw [h]
    · exact hl
    · exact NPD_none
    · exact NPD_depart
  have n1' : NPD m2.core.state := by
    rcases hm.2 with h | h | h <;> rw [h]
    · exact hr
    · exact NPD_none
    · exact NPD_depart
  have hc := completeWave_state m1 m2
  generalize completeWaveAuth m1 m2 = Cw at hc
  obtain ⟨c1, c2⟩ := Cw
  dsimp only at hc ⊢
  have n2 : NPD c1.core.state := by
    rcases hc.1 with h | h <;> rw [h]
    · exact n1
    · exact NPD_c1
  have n2' : NPD c2.core.state := by
    rcases hc.2 with h | h | h <;> rw [h]
    · exact n1'
    · exact NPD_c1
    · exact ⟨by decide, by decide⟩
  have hw := wave_state c1 c2
  generalize waveAuth c1 c2 = W at hw
  obtain ⟨w1, w2⟩ := W
  dsimp only at hw ⊢
  have n3 : NPD w1.core.state := by
    rcases hw.1 with h | h | h <;> rw [h]
    · exact n2
    · exact NPD_c1
    · exact NPD_c2
  have n3' : NPD w2.core.state := by
    rcases hw.2 with h | h | h <;> rw [h]
    · exact n2'
    · exact NPD_c1
    · exact ⟨by decide, by decide⟩
  have hd := ds_state w1 w2
  generalize lift2 dropStray w1 w2 = D at hd
  obtain ⟨d1, d2⟩ := D
  dsimp only at hd ⊢
  rw [lbA_state, lfA_state, hd.1, hd.2]
  exact ⟨n3, n3'⟩

/-- A3 entering the terminal cell of the tail block is applied there. -/
theorem mid_left_apply (hψ : ψ > 0) (κ : Nat) (σ : ProvColor) (l r : AuthState ψ)
    {γl stl a' γr str} (t : Path2Info)
    (hl : Cell σ l (ψ - 1) γl stl σ none) (hr : Cell σ r a' γr str σ (some t))
    (hsl : RouteSt stl) (hsr : RouteSt str) (hrk : str ≠ .lock)
    (hw : waveState stl = true ∨ stl = .depart)
    (ht : t.action = 3) (ha' : a' ≠ ψ - 1) :
    EQL (midS hψ κ authFplusmcc l r) (ψ - 1) a' := by
  have hl0 := hl
  have hr0 := hr
  obtain ⟨⟨la, ⟨lb, lp⟩, lm, ls, lc, l2, -⟩, lL, lR⟩ := hl0
  obtain ⟨⟨ra, ⟨rb, rp⟩, rm, rs, rc, r2, rt⟩, rL, rR⟩ := hr0
  obtain ⟨rsc, rmk⟩ := rt (Option.some_ne_none t)
  have hmv : canMoveL r.core t = true := by simp [canMoveL, ht, ra, ha']
  have hhp : l.hasPath = true := by simp [AuthState.hasPath, lp]
  have hentry : entry authFplusmcc.claimCheck r l t = .ok :=
    entry_ok _ r l t hhp rsc (by rw [ht]; decide) (by rw [lc, rmk])
  have hmt := mt_L authFplusmcc l r t .ok l2 r2 hmv hentry (by decide)
    (Or.inl (by rw [lc, rmk]))
  have hc1 : Cell σ (receive .ok r l (dec t)) (ψ - 1) γl stl σ (some (dec t)) :=
    hl.recv .ok (dec t) rsc rmk (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨⟨qa, ⟨qb, qp⟩, -, qs, qc, q2, qt⟩, qL, qR⟩ := id hc1
  obtain ⟨qsc, qmk⟩ := qt (Option.some_ne_none _)
  have hac := ac_34_last hψ _ (dec t) q2 (Or.inl ((dec_action t).trans ht)) qsc (qmk.trans qc.symm) qa
  have hck : (applyControlAuth hψ (moveTokensAuth authFplusmcc l r).1).core.state ≠
      .CHECK_ready := by
    rw [hmt]; dsimp only; rw [hac]; intro h; cases h
  have hv1 := hl.valid (fun h => absurd rfl h)
  have hv2 := hr.valid (fun _ => rfl)
  have hms := moveSource_eq hψ authFplusmcc l r lL rL (ls ▸ hsl) (rs ▸ hsr) hv1 hv2 a' rb rp hck
  rw [hmt] at hms
  dsimp only at hms
  rw [ac_none hψ r.dropP2 rfl] at hms
  have hq1 : QCell (applyControlAuth hψ (receive .ok r l (dec t))) := by
    rw [hac]
    exact ⟨qL, qR, ⟨qb, by rw [qa]; exact qp⟩, route_elim, fun h => by cases h⟩
  have hc2 := hr.dropP2
  obtain ⟨d1, d2, he, e1, e2, e3, e4⟩ := midS_eq hψ κ l r _ _ hms hq1
    (hc2.qcell hsr (fun h => absurd h hrk))
  rw [he]
  obtain ⟨g1, g2⟩ := RV_pl e1
  obtain ⟨g3, g4⟩ := RV_pl e3
  have hs1 : d1.core.state = .eliminate_signal := by rw [e2, hac]
  have hp1 : d1.core.path = .some (ψ - 1) qb := by rw [g1, hac]; exact qp
  have hp2 : d2.core.path = .some a' rb := by rw [g3]; exact rp
  have hn2 : NPD d2.core.state := by
    rcases e4 with h | ⟨h, -⟩
    · rw [h]; exact hc2.npd hsr
    · rw [h]; exact NPD_elim
  refine ⟨?_, ⟨qb, by rw [(compare_path κ d1 d2).1]; exact hp1⟩,
    compare_elimL κ d1 d2 _ _ hp1 hs1, ?_, ⟨rb, by rw [(compare_path κ d1 d2).2]; exact hp2⟩,
    (compare_NPD κ d1 d2 _ _ hp1 (by rw [hs1]; exact NPD_elim) hn2).2⟩
  · rw [(compare_label κ d1 d2).1, g2, hac]
    exact qa
  · rw [(compare_label κ d1 d2).2, g4]
    exact ra

/-- A1/A4 crossing rightwards, not landing and not applied. -/
theorem ms_right (hψ : ψ > 0) (σ : ProvColor) (l r : AuthState ψ) {a γl stl a' γr str}
    (t : Path2Info)
    (hl : Cell σ l a γl stl σ (some t)) (hr : Cell σ r a' γr str σ none)
    (hsl : RouteSt stl) (hsr : RouteSt str)
    (ht : (t.action = 1 ∧ t.position ≠ 0) ∨ (t.action = 4 ∧ a ≠ ψ - 1 ∧ a' ≠ ψ - 1)) :
    moveSourceAuth hψ authFplusmcc l r = (l.dropP2, receive .ok l r (dec t)) := by
  have hl0 := hl
  have hr0 := hr
  obtain ⟨⟨la, ⟨lb, lp⟩, lm, ls, lc, l2, lt⟩, lL, lR⟩ := hl0
  obtain ⟨⟨ra, ⟨rb, rp⟩, rm, rs, rc, r2, -⟩, rL, rR⟩ := hr0
  obtain ⟨lsc, lmk⟩ := lt (Option.some_ne_none t)
  have hmv : canMoveR l.core t = true := by
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2, -⟩
    · simp [canMoveR, h1, h2]
    · simp [canMoveR, h1, la, h2]
  have hrh : r.hasPath = true := by simp [AuthState.hasPath, rp]
  have hmt := mt_R authFplusmcc l r t l2 r2 lsc hmv hrh
    (by rcases ht with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> decide) (by rw [rc, lmk])
  have hc2 : Cell σ (receive .ok l r (dec t)) a' γr str σ (some (dec t)) :=
    hr.recv .ok (dec t) lsc lmk (Or.inl ⟨rfl, rfl⟩)
  have hac : applyControlAuth hψ (receive .ok l r (dec t)) = receive .ok l r (dec t) := by
    obtain ⟨⟨qa, -, -, -, qc, q2, qt⟩, -, -⟩ := id hc2
    obtain ⟨qs, qm⟩ := qt (Option.some_ne_none _)
    rcases ht with ⟨h1, -⟩ | ⟨h1, -, h3⟩
    · exact ac_12 hψ _ (dec t) q2 (Or.inl ((dec_action t).trans h1))
    · exact ac_34_mid hψ _ (dec t) q2 (Or.inr ((dec_action t).trans h1)) qs (qm.trans qc.symm)
        (by rw [qa]; exact h3)
  have hck : (applyControlAuth hψ (moveTokensAuth authFplusmcc l r).1).core.state ≠
      .CHECK_ready := by
    rw [hmt]; dsimp only; rw [ac_none hψ _ rfl]; exact ls ▸ route_ne_ready hsl
  have hv1 := hl.valid (fun _ => rfl)
  have hv2 := hr.valid (fun h => absurd rfl h)
  rw [moveSource_eq hψ authFplusmcc l r lL rL (ls ▸ hsl) (rs ▸ hsr) hv1 hv2 a' rb rp hck]
  rw [hmt]
  dsimp only
  rw [hac, ac_none hψ _ rfl]

theorem mid_right (hψ : ψ > 0) (κ : Nat) (σ : ProvColor) (l r : AuthState ψ)
    {a γl stl a' γr str} (t : Path2Info)
    (hl : Cell σ l a γl stl σ (some t)) (hr : Cell σ r a' γr str σ none)
    (hsl : RouteSt stl) (hsr : RouteSt str) (hlk : stl ≠ .lock) (hrk : str ≠ .lock)
    (ht : (t.action = 1 ∧ t.position ≠ 0) ∨ (t.action = 4 ∧ a ≠ ψ - 1 ∧ a' ≠ ψ - 1))
    (hnl : ¬ ((dec t).action = 1 ∧ (dec t).position = 0))
    (hin : InertV (ψ := ψ) σ a γl stl σ none a' γr str σ (some (dec t))) :
    Out σ (midS hψ κ authFplusmcc l r) a γl stl σ none a' γr str σ (some (dec t)) ∨
      EQ (midS hψ κ authFplusmcc l r) a a' := by
  have hms := ms_right hψ σ l r t hl hr hsl hsr ht
  have hc1 := hl.dropP2
  have hc2 : Cell σ (receive .ok l r (dec t)) a' γr str σ (some (dec t)) := by
    obtain ⟨lsc, lmk⟩ := hl.1.2.2.2.2.2.2 (Option.some_ne_none t)
    exact hr.recv .ok (dec t) lsc lmk (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨d1, d2, he, e1, e2, e3, e4⟩ := midS_eq hψ κ l r _ _ hms
    (hc1.qcell hsl (fun h => absurd h hlk)) (hc2.qcell hsr (fun h => absurd h hrk))
  rw [he]
  rcases e4 with e4 | ⟨e4, -⟩
  · left
    have hd1 := hc1.of_RV e1 e2
    have hd2 := hc2.of_RV e3 e4
    have ha2 : (dec t).action ≠ 2 := by
      rw [dec_action]; rcases ht with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
    obtain ⟨⟨a1, ⟨b1, p1⟩, m1, s1, c1, t1, -⟩, -, -⟩ := id hd1
    obtain ⟨⟨a2, ⟨b2, p2⟩, m2, s2, c2, t2, -⟩, -, -⟩ := id hd2
    rw [compare_inert κ d1 d2 a b1 p1 (hin d1 d2 hd1.1 hd2.1)
      (ds_id d1 d2 (fun t' h => by rw [t1] at h; cases h)
        (fun t' h => by rw [t2] at h; cases h; exact fun h' => ha2 h'.1))]
    rw [lb_none d1 t1, lf_other κ d2 (dec t) t2 hnl]
    exact ⟨hd1.1, hd2.1⟩
  · right
    exact EQ_of_elim κ d1 d2 _ _ hc1 hc2 hsl e1 e2 e3 e4

/-- A1 landing on its target: BEQ elects, emits the next A2, or emits A4/A3. -/
theorem mid_right_land (hψ : ψ > 0) (κ : Nat) (σ : ProvColor) (l r : AuthState ψ)
    {a γl stl j γr str} (lb : Nat)
    (hl : Cell σ l a γl stl σ (some ⟨j, lb, 1, 1⟩)) (hr : Cell σ r j γr str σ none)
    (hsl : RouteSt stl) (hsr : RouteSt str) (hlk : stl ≠ .lock) (hrk : str ≠ .lock)
    (hw : waveState str = true)
    (hin : InertV (ψ := ψ) σ a γl stl σ none j γr str σ (some ⟨j, lb, 0, 1⟩)) :
    (midS hψ κ authFplusmcc l r).2.core.leader = true ∨
      (j ≠ ψ - 1 ∧
        Out σ (midS hψ κ authFplusmcc l r) a γl stl σ none j γr str σ (some ⟨j + 1, 0, ψ - 1, 2⟩)) ∨
      Out σ (midS hψ κ authFplusmcc l r) a γl stl σ none j γr str σ (some ⟨0, 0, 0, 4⟩) ∨
      Out σ (midS hψ κ authFplusmcc l r) a γl stl σ none j γr str σ (some ⟨0, 0, 0, 3⟩) ∨
      EQ (midS hψ κ authFplusmcc l r) a j := by
  have hdec : dec (⟨j, lb, 1, 1⟩ : Path2Info) = ⟨j, lb, 0, 1⟩ := by simp [dec]
  have hms := ms_right hψ σ l r ⟨j, lb, 1, 1⟩ hl hr hsl hsr (Or.inl ⟨rfl, Nat.one_ne_zero⟩)
  rw [hdec] at hms
  have hc1 := hl.dropP2
  have hc2 : Cell σ (receive .ok l r ⟨j, lb, 0, 1⟩) j γr str σ (some ⟨j, lb, 0, 1⟩) := by
    obtain ⟨lsc, lmk⟩ := hl.1.2.2.2.2.2.2 (Option.some_ne_none _)
    exact hr.recv .ok _ lsc lmk (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨d1, d2, he, e1, e2, e3, e4⟩ := midS_eq hψ κ l r _ _ hms
    (hc1.qcell hsl (fun h => absurd h hlk)) (hc2.qcell hsr (fun h => absurd h hrk))
  rw [he]
  rcases e4 with e4 | ⟨e4, -⟩
  · have hd1 := hc1.of_RV e1 e2
    have hd2 := hc2.of_RV e3 e4
    obtain ⟨⟨a1, ⟨b1, p1⟩, m1, s1, c1, t1, -⟩, L1, R1⟩ := id hd1
    obtain ⟨⟨a2, ⟨b2, p2⟩, m2, s2, c2, t2, tt2⟩, L2, R2⟩ := id hd2
    obtain ⟨sc2, mk2⟩ := tt2 (Option.some_ne_none _)
    rw [compare_inert κ d1 d2 a b1 p1 (hin d1 d2 hd1.1 hd2.1)
      (ds_id d1 d2 (fun t' h => by rw [t1] at h; cases h)
        (fun t' h => by rw [t2] at h; cases h; simp))]
    rw [lb_none d1 t1]
    rcases lf_land κ d2 j lb b2 p2 t2 (by rw [s2]; exact hw) sc2 (mk2.trans c2.symm) with
      ⟨-, h⟩ | ⟨hj, h⟩ | h | h
    · left; rw [h]
    · right; left; rw [h]
      exact ⟨hj, hd1.1, a2, ⟨b2, p2⟩, m2, s2, c2, rfl, fun _ => ⟨sc2, mk2⟩⟩
    · right; right; left; rw [h]
      exact ⟨hd1.1, a2, ⟨b2, p2⟩, m2, s2, c2, rfl, fun _ => ⟨sc2, mk2⟩⟩
    · right; right; right; left; rw [h]
      exact ⟨hd1.1, a2, ⟨b2, p2⟩, m2, s2, c2, rfl, fun _ => ⟨sc2, mk2⟩⟩
  · right; right; right; right
    exact EQ_of_elim κ d1 d2 _ _ hc1 hc2 hsl e1 e2 e3 e4

/-- A4 entering the terminal cell of the target block is applied there. -/
theorem mid_right_apply (hψ : ψ > 0) (κ : Nat) (σ : ProvColor) (l r : AuthState ψ)
    {a γl stl γr str} (t : Path2Info)
    (hl : Cell σ l a γl stl σ (some t)) (hr : Cell σ r (ψ - 1) γr str σ none)
    (hsl : RouteSt stl) (hsr : RouteSt str) (hlk : stl ≠ .lock)
    (ht : t.action = 4) (ha : a ≠ ψ - 1) :
    EQ (midS hψ κ authFplusmcc l r) a (ψ - 1) := by
  have hl0 := hl
  have hr0 := hr
  obtain ⟨⟨la, ⟨lb, lp⟩, lm, ls, lc, l2, lt⟩, lL, lR⟩ := hl0
  obtain ⟨⟨ra, ⟨rb, rp⟩, rm, rs, rc, r2, -⟩, rL, rR⟩ := hr0
  obtain ⟨lsc, lmk⟩ := lt (Option.some_ne_none t)
  have hmv : canMoveR l.core t = true := by simp [canMoveR, ht, la, ha]
  have hrh : r.hasPath = true := by simp [AuthState.hasPath, rp]
  have hmt := mt_R authFplusmcc l r t l2 r2 lsc hmv hrh (by rw [ht]; decide) (by rw [rc, lmk])
  have hc2 : Cell σ (receive .ok l r (dec t)) (ψ - 1) γr str σ (some (dec t)) :=
    hr.recv .ok (dec t) lsc lmk (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨⟨qa, ⟨qb, qp⟩, -, qs, qc, q2, qt⟩, qL, qR⟩ := id hc2
  obtain ⟨qsc, qmk⟩ := qt (Option.some_ne_none _)
  have hac := ac_34_last hψ _ (dec t) q2 (Or.inr ((dec_action t).trans ht)) qsc
    (qmk.trans qc.symm) qa
  have hck : (applyControlAuth hψ (moveTokensAuth authFplusmcc l r).1).core.state ≠
      .CHECK_ready := by
    rw [hmt]; dsimp only; rw [ac_none hψ l.dropP2 rfl]; exact ls ▸ route_ne_ready hsl
  have hv1 := hl.valid (fun _ => rfl)
  have hv2 := hr.valid (fun h => absurd rfl h)
  have hms := moveSource_eq hψ authFplusmcc l r lL rL (ls ▸ hsl) (rs ▸ hsr) hv1 hv2 _ rb rp hck
  rw [hmt] at hms
  dsimp only at hms
  rw [ac_none hψ l.dropP2 rfl] at hms
  have hq2 : QCell (applyControlAuth hψ (receive .ok l r (dec t))) := by
    rw [hac]
    exact ⟨qL, qR, ⟨qb, by rw [qa]; exact qp⟩, route_elim, fun h => by cases h⟩
  have hc1 := hl.dropP2
  obtain ⟨d1, d2, he, e1, e2, e3, e4⟩ := midS_eq hψ κ l r _ _ hms
    (hc1.qcell hsl (fun h => absurd h hlk)) hq2
  rw [he]
  obtain ⟨g1, g2⟩ := RV_pl e1
  obtain ⟨g3, g4⟩ := RV_pl e3
  have hs2 : d2.core.state = .eliminate_signal := by
    rcases e4 with h | ⟨h, -⟩
    · rw [h, hac]
    · exact h
  exact compare_EQ κ d1 d2 a (ψ - 1) lb qb (by rw [g2]; exact la) (by rw [g1]; exact lp)
    (by rw [e2]; exact hc1.npd hsl) (by rw [g4, hac]; exact qa) (by rw [g3, hac]; exact qp) hs2

/-- A3/A4 standing in the terminal cell (born there) is applied at the next service of its
incoming edge. -/
theorem mid_stay_apply (hψ : ψ > 0) (κ : Nat) (σ : ProvColor) (l r : AuthState ψ)
    {a γl stl γr str} (t : Path2Info)
    (hl : Cell σ l a γl stl σ none) (hr : Cell σ r (ψ - 1) γr str σ (some t))
    (hsl : RouteSt stl) (hsr : RouteSt str) (hlk : stl ≠ .lock)
    (ht : t.action = 3 ∨ t.action = 4) :
    EQ (midS hψ κ authFplusmcc l r) a (ψ - 1) := by
  have hl0 := hl
  have hr0 := hr
  obtain ⟨⟨la, ⟨lb, lp⟩, lm, ls, lc, l2, -⟩, lL, lR⟩ := hl0
  obtain ⟨⟨ra, ⟨rb, rp⟩, rm, rs, rc, r2, rt⟩, rL, rR⟩ := hr0
  obtain ⟨rsc, rmk⟩ := rt (Option.some_ne_none t)
  have hmv : canMoveL r.core t = false := by
    rcases ht with h | h <;> simp [canMoveL, h, ra]
  have hmt := mt_stay authFplusmcc l r t l2 r2 hmv
  have hac := ac_34_last hψ r t r2 ht rsc (rmk.trans rc.symm) ra
  have hck : (applyControlAuth hψ (moveTokensAuth authFplusmcc l r).1).core.state ≠
      .CHECK_ready := by
    rw [hmt]; dsimp only; rw [ac_none hψ l l2]; exact ls ▸ route_ne_ready hsl
  have hv1 := hl.valid (fun h => absurd rfl h)
  have hv2 := hr.valid (fun _ => rfl)
  have hms := moveSource_eq hψ authFplusmcc l r lL rL (ls ▸ hsl) (rs ▸ hsr) hv1 hv2 _ rb rp hck
  rw [hmt] at hms
  dsimp only at hms
  rw [ac_none hψ l l2] at hms
  have hq2 : QCell (applyControlAuth hψ r) := by
    rw [hac]
    exact ⟨rL, rR, ⟨rb, by rw [ra]; exact rp⟩, route_elim, fun h => by cases h⟩
  obtain ⟨d1, d2, he, e1, e2, e3, e4⟩ := midS_eq hψ κ l r _ _ hms
    (hl.qcell hsl (fun h => absurd h hlk)) hq2
  rw [he]
  obtain ⟨g1, g2⟩ := RV_pl e1
  obtain ⟨g3, g4⟩ := RV_pl e3
  have hs2 : d2.core.state = .eliminate_signal := by
    rcases e4 with h | ⟨h, -⟩
    · rw [h, hac]
    · exact h
  exact compare_EQ κ d1 d2 a (ψ - 1) lb rb (by rw [g2]; exact la) (by rw [g1]; exact lp)
    (by rw [e2]; exact hl.npd hsl) (by rw [g4, hac]; exact ra) (by rw [g3, hac]; exact rp) hs2

/-! ### Setup steps as `midS` outcomes -/

theorem mid_lockprop (hψ : ψ > 0) (κ : Nat) (σ : ProvColor) (l r : AuthState ψ)
    {k γl γr cmr} (hk : k + 1 < ψ - 1)
    (hl : Cell σ l k γl .lock σ none) (hr : Cell σ r (k + 1) γr .depart cmr none) :
    Out σ (midS hψ κ authFplusmcc l r) k γl .lock σ none (k + 1) γr .lock σ none := by
  obtain ⟨rb0, rp0⟩ := hr.1.2.1
  have hms : moveSourceAuth hψ authFplusmcc l r = (l, r) :=
    ms_quiet hψ _ l r hl.2.1 hr.2.1 (hl.1.2.2.2.1 ▸ route_lock) (hr.1.2.2.2.1 ▸ route_depart)
      hl.1.2.2.2.2.2.1 hr.1.2.2.2.2.2.1 _ rb0 rp0
  obtain ⟨d1, d2, he, e1, e2, e3, e4⟩ := midS_eq hψ κ l r l r hms
    (hl.qcell route_lock (fun _ => by omega)) (hr.qcell route_depart (by intro h; cases h))
  rw [he]
  have hd1 := hl.of_RV e1 e2
  have e4' : d2.core.state = r.core.state := by
    rcases e4 with h | h
    · exact h
    · exfalso; have := h.2; rw [hr.1.1] at this; omega
  have hd2 := hr.of_RV e3 e4'
  obtain ⟨⟨a1, ⟨b1, p1⟩, m1, s1, c1, t1, -⟩, -, -⟩ := hd1
  obtain ⟨⟨a2, ⟨b2, p2⟩, m2, s2, c2, t2, -⟩, -, -⟩ := hd2
  rw [compare_lockprop κ d1 d2 k b1 b2 σ hk p1 p2 s1 s2 c1 t1 t2]
  exact ⟨⟨a1, ⟨b1, p1⟩, m1, s1, c1, t1, fun h => absurd t1 (by simp at h)⟩,
    ⟨a2, ⟨b2, p2⟩, m2, rfl, rfl, t2, fun h => absurd rfl h⟩⟩

theorem mid_lockprop_last (hψ : ψ > 0) (κ : Nat) (σ : ProvColor) (l r : AuthState ψ)
    {k γl γr cmr} (hk : k + 1 = ψ - 1)
    (hl : Cell σ l k γl .lock σ none) (hr : Cell σ r (k + 1) γr .depart cmr none) :
    Out σ (midS hψ κ authFplusmcc l r) k γl .compare1 σ none (k + 1) γr .compare1 σ none ∨
      EQ (midS hψ κ authFplusmcc l r) k (k + 1) := by
  obtain ⟨rb0, rp0⟩ := hr.1.2.1
  have hms : moveSourceAuth hψ authFplusmcc l r = (l, r) :=
    ms_quiet hψ _ l r hl.2.1 hr.2.1 (hl.1.2.2.2.1 ▸ route_lock) (hr.1.2.2.2.1 ▸ route_depart)
      hl.1.2.2.2.2.2.1 hr.1.2.2.2.2.2.1 _ rb0 rp0
  obtain ⟨d1, d2, he, e1, e2, e3, e4⟩ := midS_eq hψ κ l r l r hms
    (hl.qcell route_lock (fun _ => by omega)) (hr.qcell route_depart (by intro h; cases h))
  rw [he]
  rcases e4 with e4 | ⟨e4, -⟩
  · left
    have hd1 := hl.of_RV e1 e2
    have hd2 := hr.of_RV e3 e4
    obtain ⟨⟨a1, ⟨b1, p1⟩, m1, s1, c1, t1, -⟩, -, -⟩ := hd1
    obtain ⟨⟨a2, ⟨b2, p2⟩, m2, s2, c2, t2, -⟩, -, -⟩ := hd2
    rw [compare_lockprop_last κ d1 d2 k b1 b2 σ hk p1 p2 s1 s2 c1 t1 t2]
    exact ⟨⟨a1, ⟨b1, p1⟩, m1, rfl, c1, t1, fun h => absurd rfl h⟩,
      ⟨a2, ⟨b2, p2⟩, m2, rfl, rfl, t2, fun h => absurd rfl h⟩⟩
  · right
    exact EQ_of_elim κ d1 d2 _ _ hl hr route_lock e1 e2 e3 e4

theorem mid_ack (hψ : ψ > 0) (κ : Nat) (σ : ProvColor) (l r : AuthState ψ)
    {k γl γr} (hk : k + 1 < ψ - 1)
    (hl : Cell σ l k γl .lock σ none) (hr : Cell σ r (k + 1) γr .compare1 σ none) :
    Out σ (midS hψ κ authFplusmcc l r) k γl .compare1 σ none (k + 1) γr .compare1 σ none := by
  obtain ⟨rb0, rp0⟩ := hr.1.2.1
  have hms : moveSourceAuth hψ authFplusmcc l r = (l, r) :=
    ms_quiet hψ _ l r hl.2.1 hr.2.1 (hl.1.2.2.2.1 ▸ route_lock) (hr.1.2.2.2.1 ▸ route_c1)
      hl.1.2.2.2.2.2.1 hr.1.2.2.2.2.2.1 _ rb0 rp0
  obtain ⟨d1, d2, he, e1, e2, e3, e4⟩ := midS_eq hψ κ l r l r hms
    (hl.qcell route_lock (fun _ => by omega)) (hr.qcell route_c1 (by intro h; cases h))
  rw [he]
  have hd1 := hl.of_RV e1 e2
  have e4' : d2.core.state = r.core.state := by
    rcases e4 with h | h
    · exact h
    · exfalso; have := h.2; rw [hr.1.1] at this; omega
  have hd2 := hr.of_RV e3 e4'
  obtain ⟨⟨a1, ⟨b1, p1⟩, m1, s1, c1, t1, -⟩, -, -⟩ := hd1
  obtain ⟨⟨a2, ⟨b2, p2⟩, m2, s2, c2, t2, -⟩, -, -⟩ := hd2
  rw [compare_ack κ d1 d2 k b1 b2 σ (by omega) p1 p2 s1 s2 c1 c2 t1 t2]
  exact ⟨⟨a1, ⟨b1, p1⟩, m1, rfl, c1, t1, fun h => absurd rfl h⟩,
    ⟨a2, ⟨b2, p2⟩, m2, s2, c2, t2, fun h => absurd rfl h⟩⟩

theorem mid_emit (hψ : ψ > 0) (hψ2 : 2 ≤ ψ) (κ : Nat) (σ : ProvColor) (l r : AuthState ψ)
    {γl stl γr} (hst : (stl = .depart ∧ σ ≠ γl) ∨ stl = .compare1)
    (hl : Cell σ l (ψ - 1) γl stl σ none) (hr : Cell σ r 0 γr .compare1 σ none) :
    Out σ (midS hψ κ authFplusmcc l r) (ψ - 1) γl .compare2 σ (some ⟨0, 0, ψ - 1, 2⟩)
      0 γr .compare1 σ none := by
  have hsl : RouteSt stl := by
    rcases hst with ⟨h, -⟩ | h <;> rw [h]
    · exact route_depart
    · exact route_c1
  obtain ⟨rb0, rp0⟩ := hr.1.2.1
  have hms : moveSourceAuth hψ authFplusmcc l r = (l, r) :=
    ms_quiet hψ _ l r hl.2.1 hr.2.1 (hl.1.2.2.2.1 ▸ hsl) (hr.1.2.2.2.1 ▸ route_c1)
      hl.1.2.2.2.2.2.1 hr.1.2.2.2.2.2.1 _ rb0 rp0
  obtain ⟨d1, d2, he, e1, e2, e3, e4⟩ := midS_eq hψ κ l r l r hms
    (hl.qcell hsl (fun h => by rcases hst with ⟨h', -⟩ | h' <;> rw [h'] at h <;> cases h))
    (hr.qcell route_c1 (by intro h; cases h))
  rw [he]
  have hd1 := hl.of_RV e1 e2
  have e4' : d2.core.state = r.core.state := by
    rcases e4 with h | h
    · exact h
    · exfalso; have := h.2; rw [hr.1.1] at this; omega
  have hd2 := hr.of_RV e3 e4'
  obtain ⟨⟨a1, ⟨b1, p1⟩, m1, s1, c1, t1, -⟩, -, -⟩ := hd1
  obtain ⟨⟨a2, ⟨b2, p2⟩, m2, s2, c2, t2, -⟩, -, -⟩ := hd2
  have hl0 : (d1.core.state = .depart ∧ σ ≠ d1.path_mark) ∨ d1.core.state = .compare1 := by
    rcases hst with ⟨h, h'⟩ | h
    · left; exact ⟨s1.trans h, m1 ▸ h'⟩
    · right; exact s1.trans h
  rw [compare_emit hψ2 κ d1 d2 b1 b2 σ p1 p2 hl0 s2 c1 c2 t1 t2]
  exact ⟨⟨a1, ⟨b1, p1⟩, m1, rfl, c1, rfl, fun _ => ⟨rfl, rfl⟩⟩,
    ⟨a2, ⟨b2, p2⟩, m2, s2, c2, t2, fun h => absurd rfl h⟩⟩

end Steps

/-! ## Ring level: served edges, exits, and reachability with a length budget -/

section RingLevel
variable {n ψ : Nat}

/-- One served interaction of `authFplusmcc`. -/
abbrev stp (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (C : Fin n → AuthState ψ) (e : Fin n) :
    Fin n → AuthState ψ :=
  (authProtocol hψ κ authFplusmcc).step ring C e

/-- The right neighbour differs from the cell on a ring of at least two cells. -/
theorem rn_ne (ring : DirectedRing n) (hn : 1 < n) (e : Fin n) : ring.rightNeighbor e ≠ e := by
  intro h
  have he := congrArg Fin.val h
  change (e.val + 1) % n = e.val at he
  by_cases hk : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt hk] at he; omega
  · have hlast : e.val + 1 = n := by omega
    rw [hlast, Nat.mod_self] at he; omega

theorem stp_left (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (C : Fin n → AuthState ψ)
    (e : Fin n) :
    stp hψ κ ring C e e = (pipeline hψ κ authFplusmcc (C e) (C (ring.rightNeighbor e))).1 := by
  simp [stp, PopulationProtocol.step, authProtocol]

theorem stp_right (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → AuthState ψ) (e : Fin n) :
    stp hψ κ ring C e (ring.rightNeighbor e) =
      (pipeline hψ κ authFplusmcc (C e) (C (ring.rightNeighbor e))).2 := by
  have ne := rn_ne ring hn e
  simp [stp, PopulationProtocol.step, authProtocol, ne]

theorem stp_other (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (C : Fin n → AuthState ψ)
    (e i : Fin n) (h1 : i ≠ e) (h2 : i ≠ ring.rightNeighbor e) : stp hψ κ ring C e i = C i := by
  simp [stp, PopulationProtocol.step, authProtocol, h1, h2]

theorem authRun_append (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (w1 w2 : List (Fin n)) : ∀ C : Fin n → AuthState ψ,
    authRun hψ κ authFplusmcc ring C (w1 ++ w2) =
      authRun hψ κ authFplusmcc ring (authRun hψ κ authFplusmcc ring C w1) w2 := by
  induction w1 with
  | nil => intro C; rfl
  | cons e es ih => intro C; exact ih _

/-- The target: a leader, or a deleted main path. -/
def Done (C : Fin n → AuthState ψ) : Prop :=
  ∃ i, (C i).core.leader = true ∨ (C i).core.path = .bot

/-- A cell in `eliminate_signal` behind a fine predecessor: one more service of edge `e`
deletes a path (`pipeline_HP_of_elim`). -/
def ElimAt (ring : DirectedRing n) (C : Fin n → AuthState ψ) (e : Fin n) : Prop :=
  (C e).core.leader = false ∧ (C (ring.rightNeighbor e)).core.leader = false ∧
    (C e).core.reset_cmd = false ∧ (C (ring.rightNeighbor e)).core.reset_cmd = false ∧
    (C (ring.rightNeighbor e)).core.label.val = ((C e).core.label.val + 1) % ψ ∧
    (C e).core.path ≠ .bot ∧ NPD (C e).core.state ∧
    (C (ring.rightNeighbor e)).core.state = .eliminate_signal

def DoneE (ring : DirectedRing n) (C : Fin n → AuthState ψ) : Prop :=
  Done C ∨ ∃ e, ElimAt ring C e

/-- Within `L` served edges, the run reaches `Done`, an elimination exit, or `P`. -/
def Reach (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (C : Fin n → AuthState ψ) (L : Nat)
    (P : (Fin n → AuthState ψ) → Prop) : Prop :=
  ∃ w : List (Fin n), w.length ≤ L ∧
    (DoneE ring (authRun hψ κ authFplusmcc ring C w) ∨ P (authRun hψ κ authFplusmcc ring C w))

theorem Reach.pure (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) {C : Fin n → AuthState ψ}
    {P : (Fin n → AuthState ψ) → Prop} (h : P C) : Reach hψ κ ring C 0 P :=
  ⟨[], Nat.le_refl 0, Or.inr h⟩

theorem Reach.done (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) {C : Fin n → AuthState ψ}
    {L : Nat} {P : (Fin n → AuthState ψ) → Prop} (h : DoneE ring C) : Reach hψ κ ring C L P :=
  ⟨[], Nat.zero_le L, Or.inl h⟩

theorem Reach.mono {hψ : ψ > 0} {κ : Nat} {ring : DirectedRing n} {C : Fin n → AuthState ψ}
    {L L' : Nat} {P Q : (Fin n → AuthState ψ) → Prop} (h : Reach hψ κ ring C L P) (hL : L ≤ L')
    (hPQ : ∀ C', P C' → Q C') : Reach hψ κ ring C L' Q := by
  obtain ⟨w, hw, h⟩ := h
  exact ⟨w, Nat.le_trans hw hL, h.imp id (hPQ _)⟩

theorem Reach.bind {hψ : ψ > 0} {κ : Nat} {ring : DirectedRing n} {C : Fin n → AuthState ψ}
    {L1 L2 : Nat} {P Q : (Fin n → AuthState ψ) → Prop} (h : Reach hψ κ ring C L1 P)
    (hk : ∀ C', P C' → Reach hψ κ ring C' L2 Q) : Reach hψ κ ring C (L1 + L2) Q := by
  obtain ⟨w1, hw1, h1⟩ := h
  rcases h1 with h1 | h1
  · exact ⟨w1, by omega, Or.inl h1⟩
  · obtain ⟨w2, hw2, h2⟩ := hk _ h1
    refine ⟨w1 ++ w2, by rw [List.length_append]; omega, ?_⟩
    rw [authRun_append]
    exact h2

theorem Reach.one (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) {C : Fin n → AuthState ψ}
    {P : (Fin n → AuthState ψ) → Prop} (e : Fin n)
    (h : DoneE ring (stp hψ κ ring C e) ∨ P (stp hψ κ ring C e)) : Reach hψ κ ring C 1 P :=
  ⟨[e], Nat.le_refl 1, h⟩

theorem Done_of_ElimAt (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → AuthState ψ) (e : Fin n) (h : ElimAt ring C e) : Done (stp hψ κ ring C e) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hp := pipeline_HP_of_elim hψ κ authFplusmcc (C e) (C (ring.rightNeighbor e)) h1 h2 h3 h4
    (Fin.ext h5) h6 h7.1 h7.2 h8
  rcases hp with hp | hp
  · exact ⟨e, Or.inr (by rw [stp_left]; exact hp)⟩
  · exact ⟨ring.rightNeighbor e, Or.inr (by rw [stp_right hψ κ ring hn]; exact hp)⟩

/-- The final conversion: an elimination exit costs one more served edge. -/
theorem Reach.final (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n)
    {C : Fin n → AuthState ψ} {L : Nat} (h : Reach hψ κ ring C L (fun _ => False)) :
    ∃ w : List (Fin n), w.length ≤ L + 1 ∧ Done (authRun hψ κ authFplusmcc ring C w) := by
  obtain ⟨w, hw, h⟩ := h
  rcases h with (h | ⟨e, he⟩) | h
  · exact ⟨w, by omega, h⟩
  · refine ⟨w ++ [e], by rw [List.length_append]; simp; omega, ?_⟩
    rw [authRun_append]
    exact Done_of_ElimAt hψ κ ring hn _ e he
  · exact h.elim

/-- One interaction on two route cells, at ring level. -/
theorem ring_mid (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n) (σ : ProvColor)
    (C : Fin n → AuthState ψ) (e : Fin n) {a γl stl cml tokl a' γr str cmr tokr}
    (hl : Cell σ (C e) a γl stl cml tokl) (hr : Cell σ (C (ring.rightNeighbor e)) a' γr str cmr tokr)
    (hnext : a' = (a + 1) % ψ) (hNl : NPD stl) (hNr : NPD str)
    (Q : AuthState ψ × AuthState ψ → Prop)
    (hQV : ∀ m m' : AuthState ψ × AuthState ψ, V m'.1 = V m.1 → V m'.2 = V m.2 → Q m → Q m')
    (hmid : ∀ l' r', Cell σ l' a γl stl cml tokl → Cell σ r' a' γr str cmr tokr →
      HP (midS hψ κ authFplusmcc l' r') ∨ (midS hψ κ authFplusmcc l' r').2.core.leader = true ∨
        Q (midS hψ κ authFplusmcc l' r')) :
    Done (stp hψ κ ring C e) ∨
      (Q (stp hψ κ ring C e e, stp hψ κ ring C e (ring.rightNeighbor e)) ∧
        (stp hψ κ ring C e e).core.leader = false ∧
        (stp hψ κ ring C e (ring.rightNeighbor e)).core.leader = false ∧
        (stp hψ κ ring C e e).core.reset_cmd = false ∧
        (stp hψ κ ring C e (ring.rightNeighbor e)).core.reset_cmd = false) := by
  have hL := stp_left hψ κ ring C e
  have hR := stp_right hψ κ ring hn C e
  rcases pipe_cells hψ κ σ (C e) (C (ring.rightNeighbor e)) hl hr hnext hNl hNr Q hQV hmid with
    h | h | h | ⟨h, h1, h2, h3, h4⟩
  · rcases h with h | h
    · exact Or.inl ⟨e, Or.inr (by rw [hL]; exact h)⟩
    · exact Or.inl ⟨ring.rightNeighbor e, Or.inr (by rw [hR]; exact h)⟩
  · exact Or.inl ⟨e, Or.inl (by rw [hL]; exact h)⟩
  · exact Or.inl ⟨ring.rightNeighbor e, Or.inl (by rw [hR]; exact h)⟩
  · right
    rw [hL, hR]
    exact ⟨h, h1, h2, h3, h4⟩

end RingLevel

/-! ## Descriptor invariants -/

section Inv
variable {n ψ : Nat}

/-- A cell descriptor: block colour, state, control mark, BEQ token. -/
structure Desc where
  γ : ProvColor
  st : MainState
  cm : ProvColor
  tok : Option Path2Info

/-- Cells below `N` are route cells with the given descriptors (label = index mod ψ). -/
def Inv (σ : ProvColor) (C : Fin n → AuthState ψ) (N : Nat) (D : Nat → Desc) : Prop :=
  ∀ c : Fin n, c.val < N →
    Cell σ (C c) (c.val % ψ) (D c.val).γ (D c.val).st (D c.val).cm (D c.val).tok

theorem Inv.cell {σ : ProvColor} {C : Fin n → AuthState ψ} {N : Nat} {D : Nat → Desc}
    (h : Inv σ C N D) (c : Fin n) (hc : c.val < N) (x : Desc) (hx : D c.val = x) :
    Cell σ (C c) (c.val % ψ) x.γ x.st x.cm x.tok := by
  rw [← hx]; exact h c hc

/-- Updating the two cells of a served edge. -/
theorem Inv.update {σ : ProvColor} {C C' : Fin n → AuthState ψ} {N : Nat} {D : Nat → Desc}
    (ring : DirectedRing n) (e : Fin n) (h : Inv σ C N D) (D' : Nat → Desc)
    (h1 : Cell σ (C' e) (e.val % ψ) (D' e.val).γ (D' e.val).st (D' e.val).cm (D' e.val).tok)
    (h2 : Cell σ (C' (ring.rightNeighbor e)) ((ring.rightNeighbor e).val % ψ)
      (D' (ring.rightNeighbor e).val).γ (D' (ring.rightNeighbor e).val).st
      (D' (ring.rightNeighbor e).val).cm (D' (ring.rightNeighbor e).val).tok)
    (hoth : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → C' i = C i)
    (hD : ∀ c, c < N → c ≠ e.val → c ≠ (ring.rightNeighbor e).val → D' c = D c) :
    Inv σ C' N D' := by
  intro c hc
  by_cases he : c = e
  · subst he; exact h1
  · by_cases hr : c = ring.rightNeighbor e
    · subst hr; exact h2
    · rw [hoth c he hr, hD c.val hc (fun h' => he (Fin.ext h')) (fun h' => hr (Fin.ext h'))]
      exact h c hc

end Inv

/-! ## Token walks over fixed cell kinds

During the comparison rounds every cell keeps its kind (block colour and state); only the
single BEQ token moves.  In round 0 the source cells below the token are not yet claimed:
their control mark is still the block colour.  `RD K σ u q t` describes this: kinds `K`,
cells below `u` unclaimed, the token `t` at cell `q`. -/

section Walk
variable {n ψ : Nat}

def RD (K : Nat → ProvColor × MainState) (σ : ProvColor) (u q : Nat) (t : Option Path2Info) :
    Nat → Desc :=
  fun c => ⟨(K c).1, (K c).2, if c < u then (K c).1 else σ, if c = q then t else none⟩

/-- Round kinds: `depart`, `compare1` or `compare2`. -/
def KR (s : MainState) : Prop := s = .depart ∨ s = .compare1 ∨ s = .compare2

theorem KR.route {s : MainState} (h : KR s) : RouteSt s := by
  rcases h with h | h | h <;> rw [h]
  · exact route_depart
  · exact route_c1
  · exact route_c2

theorem KR.nlock {s : MainState} (h : KR s) : s ≠ .lock := by
  rcases h with h | h | h <;> rw [h] <;> decide

theorem KR.npd {s : MainState} (h : KR s) : NPD s := NPD_of_route h.route

theorem KR.wd {s : MainState} (h : KR s) : waveState s = true ∨ s = .depart := by
  rcases h with h | h | h <;> rw [h]
  · right; rfl
  · left; rfl
  · left; rfl

theorem label_next (hd : ψ ∣ n) (ring : DirectedRing n) (e : Fin n) :
    (ring.rightNeighbor e).val % ψ = (e.val % ψ + 1) % ψ :=
  PPLLAuthBitFrozen.succ_mod_of_dvd hd e.val

theorem rn_val_ne (ring : DirectedRing n) (hn : 1 < n) (e : Fin n) :
    e.val ≠ (ring.rightNeighbor e).val := fun h => rn_ne ring hn e (Fin.ext h).symm

/-- A responder deletion exit after a served edge. -/
theorem elim_of_EQ (ring : DirectedRing n) (C : Fin n → AuthState ψ) (e : Fin n) {a a' : Nat}
    (h : EQ (C e, C (ring.rightNeighbor e)) a a') (hnext : a' = (a + 1) % ψ)
    (h1 : (C e).core.leader = false) (h2 : (C (ring.rightNeighbor e)).core.leader = false)
    (h3 : (C e).core.reset_cmd = false) (h4 : (C (ring.rightNeighbor e)).core.reset_cmd = false) :
    ElimAt ring C e := by
  obtain ⟨la, ⟨b, lp⟩, ln, ra, -, rs⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, ln, rs⟩
  · dsimp only at la ra; rw [ra, la, hnext]
  · dsimp only at lp; rw [lp]; exact PathInfo.noConfusion

/-- The two cells of a served edge, read off a round descriptor. -/
theorem RD_at (K : Nat → ProvColor × MainState) (σ : ProvColor) (u q : Nat) (t : Option Path2Info)
    (c : Nat) :
    RD K σ u q t c = ⟨(K c).1, (K c).2, if c < u then (K c).1 else σ, if c = q then t else none⟩ :=
  rfl

/-- The new cells after a move make the new round descriptor. -/
theorem RD_update (ring : DirectedRing n) (hn : 1 < n) {σ : ProvColor} {C C' : Fin n → AuthState ψ}
    {N : Nat} (K : Nat → ProvColor × MainState) (u u' q q' : Nat) (t t' : Option Path2Info)
    (e : Fin n) (h : Inv σ C N (RD K σ u q t))
    (hq : q = e.val ∨ q = (ring.rightNeighbor e).val)
    (hq' : q' = e.val ∨ q' = (ring.rightNeighbor e).val)
    (h1 : Cell σ (C' e) (e.val % ψ) (K e.val).1 (K e.val).2 (if e.val < u' then (K e.val).1 else σ)
      (if e.val = q' then t' else none))
    (h2 : Cell σ (C' (ring.rightNeighbor e)) ((ring.rightNeighbor e).val % ψ)
      (K (ring.rightNeighbor e).val).1 (K (ring.rightNeighbor e).val).2
      (if (ring.rightNeighbor e).val < u' then (K (ring.rightNeighbor e).val).1 else σ)
      (if (ring.rightNeighbor e).val = q' then t' else none))
    (hoth : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → C' i = C i)
    (huu : ∀ c, c < N → c ≠ e.val → c ≠ (ring.rightNeighbor e).val → (c < u ↔ c < u')) :
    Inv σ C' N (RD K σ u' q' t') := by
  refine Inv.update ring e h _ h1 h2 hoth ?_
  intro c hc h1 h2
  have hcq : c ≠ q := by rcases hq with hq | hq <;> rw [hq] <;> assumption
  have hcq' : c ≠ q' := by rcases hq' with hq | hq <;> rw [hq] <;> assumption
  simp only [RD, if_neg hcq, if_neg hcq', Desc.mk.injEq, true_and, and_true]
  by_cases hu : c < u
  · rw [if_pos hu, if_pos ((huu c hc h1 h2).1 hu)]
  · rw [if_neg hu, if_neg (fun h' => hu ((huu c hc h1 h2).2 h'))]

/-- A left move (A2 in transit, or A3 below the terminal) across edge `e`. -/
theorem left_move (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n) (hd : ψ ∣ n)
    (σ : ProvColor) (K : Nat → ProvColor × MainState) (N u u' : Nat) (C : Fin n → AuthState ψ)
    (e : Fin n) (t : Path2Info)
    (hinv : Inv σ C N (RD K σ u (ring.rightNeighbor e).val (some t)))
    (he : e.val < N) (hr : (ring.rightNeighbor e).val < N)
    (hKe : KR (K e.val).2) (hKr : KR (K (ring.rightNeighbor e).val).2)
    (hin : InertV (ψ := ψ) σ (e.val % ψ) (K e.val).1 (K e.val).2 σ (some (dec t))
      ((ring.rightNeighbor e).val % ψ) (K (ring.rightNeighbor e).val).1
      (K (ring.rightNeighbor e).val).2 σ none)
    (ht : (t.action = 2 ∧ 2 ≤ t.position) ∨
      (t.action = 3 ∧ (ring.rightNeighbor e).val % ψ ≠ ψ - 1 ∧ e.val % ψ ≠ ψ - 1))
    (hur : ¬ (ring.rightNeighbor e).val < u)
    (hue : e.val < u → (K e.val).1 ≠ σ ∧ (K e.val).2 = .depart ∧ t.action = 2)
    (hu' : ¬ e.val < u') (huu : ∀ c, c < N → c ≠ e.val → (c < u ↔ c < u')) :
    Reach hψ κ ring C 1 (fun C' => Inv σ C' N (RD K σ u' e.val (some (dec t)))) := by
  have hne := rn_val_ne ring hn e
  have hl := hinv e he
  have hr0 := hinv _ hr
  simp only [RD_at, if_neg hne, if_neg hur, if_pos rfl] at hl hr0
  have hnext := label_next hd ring e
  apply Reach.one hψ κ ring e
  have ht' : (t.action = 2 ∧ t.position ≠ 0) ∨
      (t.action = 3 ∧ (ring.rightNeighbor e).val % ψ ≠ ψ - 1 ∧ e.val % ψ ≠ ψ - 1) := by
    rcases ht with ⟨h1, h2⟩ | h
    · left; exact ⟨h1, by omega⟩
    · right; exact h
  have hnl : ¬ ((dec t).action = 2 ∧ (dec t).position = 0) := by
    rcases ht with ⟨h1, h2⟩ | ⟨h1, -⟩
    · simp [dec, h1]; omega
    · rw [dec_action, h1]; simp
  have key : Done (stp hψ κ ring C e) ∨
      ((Out σ (stp hψ κ ring C e e, stp hψ κ ring C e (ring.rightNeighbor e)) (e.val % ψ)
          (K e.val).1 (K e.val).2 σ (some (dec t)) ((ring.rightNeighbor e).val % ψ)
          (K (ring.rightNeighbor e).val).1 (K (ring.rightNeighbor e).val).2 σ none ∨
        EQ (stp hψ κ ring C e e, stp hψ κ ring C e (ring.rightNeighbor e)) (e.val % ψ)
          ((ring.rightNeighbor e).val % ψ)) ∧
        (stp hψ κ ring C e e).core.leader = false ∧
        (stp hψ κ ring C e (ring.rightNeighbor e)).core.leader = false ∧
        (stp hψ κ ring C e e).core.reset_cmd = false ∧
        (stp hψ κ ring C e (ring.rightNeighbor e)).core.reset_cmd = false) := by
    by_cases hc : e.val < u
    · rw [if_pos hc] at hl
      obtain ⟨hg, hdp, ha2⟩ := hue hc
      exact ring_mid hψ κ ring hn σ C e hl hr0 hnext hKe.npd hKr.npd
        (fun q => Out σ q (e.val % ψ) (K e.val).1 (K e.val).2 σ (some (dec t))
          ((ring.rightNeighbor e).val % ψ) (K (ring.rightNeighbor e).val).1
          (K (ring.rightNeighbor e).val).2 σ none ∨
          EQ q (e.val % ψ) ((ring.rightNeighbor e).val % ψ))
        (fun m m' h1 h2 h => Or.imp (Out.of_V m m' h1 h2) (EQ.of_V m m' h1 h2) h)
        (fun l' r' h1 h2 => Or.inr (Or.inr (mid_left hψ κ σ l' r' t .claim h1 h2 hKe.route
          hKr.route hKe.nlock hKr.nlock ht' (Or.inr ⟨rfl, hg, hdp, ha2⟩) hnl hin)))
    · rw [if_neg hc] at hl
      exact ring_mid hψ κ ring hn σ C e hl hr0 hnext hKe.npd hKr.npd
        (fun q => Out σ q (e.val % ψ) (K e.val).1 (K e.val).2 σ (some (dec t))
          ((ring.rightNeighbor e).val % ψ) (K (ring.rightNeighbor e).val).1
          (K (ring.rightNeighbor e).val).2 σ none ∨
          EQ q (e.val % ψ) ((ring.rightNeighbor e).val % ψ))
        (fun m m' h1 h2 h => Or.imp (Out.of_V m m' h1 h2) (EQ.of_V m m' h1 h2) h)
        (fun l' r' h1 h2 => Or.inr (Or.inr (mid_left hψ κ σ l' r' t .ok h1 h2 hKe.route
          hKr.route hKe.nlock hKr.nlock ht' (Or.inl ⟨rfl, rfl, hKe.wd⟩) hnl hin)))
  rcases key with h | ⟨h | h, L1, L2, R1, R2⟩
  · exact Or.inl (Or.inl h)
  · right
    refine RD_update ring hn K u u' _ e.val (some t) (some (dec t)) e hinv (Or.inr rfl)
      (Or.inl rfl) ?_ ?_ (fun i h1 h2 => stp_other hψ κ ring C e i h1 h2)
      (fun c hc h1 _ => huu c hc h1)
    · rw [if_neg hu', if_pos rfl]; exact ⟨h.1, L1, R1⟩
    · rw [if_neg (fun h' => hur ((huu _ hr (Ne.symm hne)).2 h')), if_neg (Ne.symm hne)]
      exact ⟨h.2, L2, R2⟩
  · exact Or.inl (Or.inr ⟨e, elim_of_EQ ring _ e h hnext L1 L2 R1 R2⟩)

/-- The landing of A2 on its target cell `e` (label `e mod ψ`). -/
theorem left_land (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n) (hd : ψ ∣ n)
    (σ : ProvColor) (K : Nat → ProvColor × MainState) (N u u' : Nat) (C : Fin n → AuthState ψ)
    (e : Fin n)
    (hinv : Inv σ C N (RD K σ u (ring.rightNeighbor e).val (some ⟨e.val % ψ, 0, 1, 2⟩)))
    (he : e.val < N) (hr : (ring.rightNeighbor e).val < N)
    (hKe : KR (K e.val).2) (hKr : KR (K (ring.rightNeighbor e).val).2)
    (hin : InertV (ψ := ψ) σ (e.val % ψ) (K e.val).1 (K e.val).2 σ (some ⟨e.val % ψ, 0, 0, 2⟩)
      ((ring.rightNeighbor e).val % ψ) (K (ring.rightNeighbor e).val).1
      (K (ring.rightNeighbor e).val).2 σ none)
    (hur : ¬ (ring.rightNeighbor e).val < u)
    (hue : e.val < u → (K e.val).1 ≠ σ ∧ (K e.val).2 = .depart)
    (hu' : ¬ e.val < u') (huu : ∀ c, c < N → c ≠ e.val → (c < u ↔ c < u')) :
    Reach hψ κ ring C 1 (fun C' => ∃ lb,
      Inv σ C' N (RD K σ u' e.val (some ⟨e.val % ψ, lb, ψ, 1⟩))) := by
  have hne := rn_val_ne ring hn e
  have hl := hinv e he
  have hr0 := hinv _ hr
  simp only [RD_at, if_neg hne, if_neg hur, if_pos rfl] at hl hr0
  have hnext := label_next hd ring e
  apply Reach.one hψ κ ring e
  have key : Done (stp hψ κ ring C e) ∨
      (((∃ lb, Out σ (stp hψ κ ring C e e, stp hψ κ ring C e (ring.rightNeighbor e)) (e.val % ψ)
          (K e.val).1 (K e.val).2 σ (some ⟨e.val % ψ, lb, ψ, 1⟩) ((ring.rightNeighbor e).val % ψ)
          (K (ring.rightNeighbor e).val).1 (K (ring.rightNeighbor e).val).2 σ none) ∨
        EQ (stp hψ κ ring C e e, stp hψ κ ring C e (ring.rightNeighbor e)) (e.val % ψ)
          ((ring.rightNeighbor e).val % ψ)) ∧
        (stp hψ κ ring C e e).core.leader = false ∧
        (stp hψ κ ring C e (ring.rightNeighbor e)).core.leader = false ∧
        (stp hψ κ ring C e e).core.reset_cmd = false ∧
        (stp hψ κ ring C e (ring.rightNeighbor e)).core.reset_cmd = false) := by
    have hQV : ∀ m m' : AuthState ψ × AuthState ψ, V m'.1 = V m.1 → V m'.2 = V m.2 →
        ((∃ lb, Out σ m (e.val % ψ) (K e.val).1 (K e.val).2 σ (some ⟨e.val % ψ, lb, ψ, 1⟩)
          ((ring.rightNeighbor e).val % ψ) (K (ring.rightNeighbor e).val).1
          (K (ring.rightNeighbor e).val).2 σ none) ∨
          EQ m (e.val % ψ) ((ring.rightNeighbor e).val % ψ)) →
        ((∃ lb, Out σ m' (e.val % ψ) (K e.val).1 (K e.val).2 σ (some ⟨e.val % ψ, lb, ψ, 1⟩)
          ((ring.rightNeighbor e).val % ψ) (K (ring.rightNeighbor e).val).1
          (K (ring.rightNeighbor e).val).2 σ none) ∨
          EQ m' (e.val % ψ) ((ring.rightNeighbor e).val % ψ)) :=
      fun m m' h1 h2 h => Or.imp (fun ⟨lb, hh⟩ => ⟨lb, Out.of_V m m' h1 h2 hh⟩)
        (EQ.of_V m m' h1 h2) h
    by_cases hc : e.val < u
    · rw [if_pos hc] at hl
      obtain ⟨hg, hdp⟩ := hue hc
      exact ring_mid hψ κ ring hn σ C e hl hr0 hnext hKe.npd hKr.npd _ hQV
        (fun l' r' h1 h2 => Or.inr (Or.inr (mid_left_land hψ κ σ l' r' .claim h1 h2 hKe.route
          hKr.route hKe.nlock hKr.nlock (Or.inr ⟨rfl, hg, hdp⟩) hin)))
    · rw [if_neg hc] at hl
      exact ring_mid hψ κ ring hn σ C e hl hr0 hnext hKe.npd hKr.npd _ hQV
        (fun l' r' h1 h2 => Or.inr (Or.inr (mid_left_land hψ κ σ l' r' .ok h1 h2 hKe.route
          hKr.route hKe.nlock hKr.nlock (Or.inl ⟨rfl, rfl, hKe.wd⟩) hin)))
  rcases key with h | ⟨⟨lb, h⟩ | h, L1, L2, R1, R2⟩
  · exact Or.inl (Or.inl h)
  · right
    refine ⟨lb, RD_update ring hn K u u' _ e.val (some _) (some ⟨e.val % ψ, lb, ψ, 1⟩) e hinv
      (Or.inr rfl) (Or.inl rfl) ?_ ?_ (fun i h1 h2 => stp_other hψ κ ring C e i h1 h2)
      (fun c hc h1 _ => huu c hc h1)⟩
    · rw [if_neg hu', if_pos rfl]; exact ⟨h.1, L1, R1⟩
    · rw [if_neg (fun h' => hur ((huu _ hr (Ne.symm hne)).2 h')), if_neg (Ne.symm hne)]
      exact ⟨h.2, L2, R2⟩
  · exact Or.inl (Or.inr ⟨e, elim_of_EQ ring _ e h hnext L1 L2 R1 R2⟩)

/-- A right move (A1 in transit, or A4 below the terminal) across edge `e`. -/
theorem right_move (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n) (hd : ψ ∣ n)
    (σ : ProvColor) (K : Nat → ProvColor × MainState) (N u : Nat) (C : Fin n → AuthState ψ)
    (e : Fin n) (t : Path2Info)
    (hinv : Inv σ C N (RD K σ u e.val (some t)))
    (he : e.val < N) (hr : (ring.rightNeighbor e).val < N)
    (hKe : KR (K e.val).2) (hKr : KR (K (ring.rightNeighbor e).val).2)
    (hin : InertV (ψ := ψ) σ (e.val % ψ) (K e.val).1 (K e.val).2 σ none
      ((ring.rightNeighbor e).val % ψ) (K (ring.rightNeighbor e).val).1
      (K (ring.rightNeighbor e).val).2 σ (some (dec t)))
    (ht : (t.action = 1 ∧ 2 ≤ t.position) ∨
      (t.action = 4 ∧ e.val % ψ ≠ ψ - 1 ∧ (ring.rightNeighbor e).val % ψ ≠ ψ - 1))
    (hue : ¬ e.val < u) (hur : ¬ (ring.rightNeighbor e).val < u) :
    Reach hψ κ ring C 1 (fun C' => Inv σ C' N (RD K σ u (ring.rightNeighbor e).val (some (dec t)))) := by
  have hne := rn_val_ne ring hn e
  have hl := hinv e he
  have hr0 := hinv _ hr
  simp only [RD_at, if_neg hne, if_neg (Ne.symm hne), if_neg hur, if_neg hue, if_pos rfl] at hl hr0
  have hnext := label_next hd ring e
  apply Reach.one hψ κ ring e
  have ht' : (t.action = 1 ∧ t.position ≠ 0) ∨
      (t.action = 4 ∧ e.val % ψ ≠ ψ - 1 ∧ (ring.rightNeighbor e).val % ψ ≠ ψ - 1) := by
    rcases ht with ⟨h1, h2⟩ | h
    · left; exact ⟨h1, by omega⟩
    · right; exact h
  have hnl : ¬ ((dec t).action = 1 ∧ (dec t).position = 0) := by
    rcases ht with ⟨h1, h2⟩ | ⟨h1, -⟩
    · simp [dec, h1]; omega
    · rw [dec_action, h1]; simp
  have key := ring_mid hψ κ ring hn σ C e hl hr0 hnext hKe.npd hKr.npd
    (fun q => Out σ q (e.val % ψ) (K e.val).1 (K e.val).2 σ none
      ((ring.rightNeighbor e).val % ψ) (K (ring.rightNeighbor e).val).1
      (K (ring.rightNeighbor e).val).2 σ (some (dec t)) ∨
      EQ q (e.val % ψ) ((ring.rightNeighbor e).val % ψ))
    (fun m m' h1 h2 h => Or.imp (Out.of_V m m' h1 h2) (EQ.of_V m m' h1 h2) h)
    (fun l' r' h1 h2 => Or.inr (Or.inr (mid_right hψ κ σ l' r' t h1 h2 hKe.route
      hKr.route hKe.nlock hKr.nlock ht' hnl hin)))
  rcases key with h | ⟨h | h, L1, L2, R1, R2⟩
  · exact Or.inl (Or.inl h)
  · right
    refine RD_update ring hn K u u _ _ (some t) (some (dec t)) e hinv
      (Or.inl rfl) (Or.inr rfl) ?_ ?_ (fun i h1 h2 => stp_other hψ κ ring C e i h1 h2)
      (fun c _ _ _ => Iff.rfl)
    · rw [if_neg hue, if_neg hne]; exact ⟨h.1, L1, R1⟩
    · rw [if_neg hur, if_pos rfl]
      exact ⟨h.2, L2, R2⟩
  · exact Or.inl (Or.inr ⟨e, elim_of_EQ ring _ e h hnext L1 L2 R1 R2⟩)

/-- The landing of A1 on its target cell `rn e`: a leader, the next A2, or A4/A3. -/
theorem right_land (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n) (hd : ψ ∣ n)
    (σ : ProvColor) (K : Nat → ProvColor × MainState) (N u : Nat) (C : Fin n → AuthState ψ)
    (e : Fin n) (lb : Nat)
    (hinv : Inv σ C N (RD K σ u e.val (some ⟨(ring.rightNeighbor e).val % ψ, lb, 1, 1⟩)))
    (he : e.val < N) (hr : (ring.rightNeighbor e).val < N)
    (hKe : KR (K e.val).2) (hKr : KR (K (ring.rightNeighbor e).val).2)
    (hw : waveState (K (ring.rightNeighbor e).val).2 = true)
    (hin : InertV (ψ := ψ) σ (e.val % ψ) (K e.val).1 (K e.val).2 σ none
      ((ring.rightNeighbor e).val % ψ) (K (ring.rightNeighbor e).val).1
      (K (ring.rightNeighbor e).val).2 σ (some ⟨(ring.rightNeighbor e).val % ψ, lb, 0, 1⟩))
    (hue : ¬ e.val < u) (hur : ¬ (ring.rightNeighbor e).val < u) :
    Reach hψ κ ring C 1 (fun C' =>
      ((ring.rightNeighbor e).val % ψ ≠ ψ - 1 ∧ Inv σ C' N (RD K σ u (ring.rightNeighbor e).val
        (some ⟨(ring.rightNeighbor e).val % ψ + 1, 0, ψ - 1, 2⟩))) ∨
      Inv σ C' N (RD K σ u (ring.rightNeighbor e).val (some ⟨0, 0, 0, 4⟩)) ∨
      Inv σ C' N (RD K σ u (ring.rightNeighbor e).val (some ⟨0, 0, 0, 3⟩))) := by
  have hne := rn_val_ne ring hn e
  have hl := hinv e he
  have hr0 := hinv _ hr
  simp only [RD_at, if_neg hne, if_neg (Ne.symm hne), if_neg hur, if_neg hue, if_pos rfl] at hl hr0
  have hnext := label_next hd ring e
  apply Reach.one hψ κ ring e
  have key := ring_mid hψ κ ring hn σ C e hl hr0 hnext hKe.npd hKr.npd
    (fun q => ((ring.rightNeighbor e).val % ψ ≠ ψ - 1 ∧
        Out σ q (e.val % ψ) (K e.val).1 (K e.val).2 σ none
        ((ring.rightNeighbor e).val % ψ) (K (ring.rightNeighbor e).val).1
        (K (ring.rightNeighbor e).val).2 σ (some ⟨(ring.rightNeighbor e).val % ψ + 1, 0, ψ - 1, 2⟩)) ∨
      Out σ q (e.val % ψ) (K e.val).1 (K e.val).2 σ none
        ((ring.rightNeighbor e).val % ψ) (K (ring.rightNeighbor e).val).1
        (K (ring.rightNeighbor e).val).2 σ (some ⟨0, 0, 0, 4⟩) ∨
      Out σ q (e.val % ψ) (K e.val).1 (K e.val).2 σ none
        ((ring.rightNeighbor e).val % ψ) (K (ring.rightNeighbor e).val).1
        (K (ring.rightNeighbor e).val).2 σ (some ⟨0, 0, 0, 3⟩) ∨
      EQ q (e.val % ψ) ((ring.rightNeighbor e).val % ψ))
    (fun m m' h1 h2 h => Or.imp (And.imp id (Out.of_V m m' h1 h2))
      (Or.imp (Out.of_V m m' h1 h2) (Or.imp (Out.of_V m m' h1 h2) (EQ.of_V m m' h1 h2))) h)
    (fun l' r' h1 h2 => by
      rcases mid_right_land hψ κ σ l' r' lb h1 h2 hKe.route hKr.route hKe.nlock hKr.nlock hw hin
        with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
  have upd : ∀ tk : Path2Info, Out σ (stp hψ κ ring C e e, stp hψ κ ring C e (ring.rightNeighbor e))
      (e.val % ψ) (K e.val).1 (K e.val).2 σ none
      ((ring.rightNeighbor e).val % ψ) (K (ring.rightNeighbor e).val).1
      (K (ring.rightNeighbor e).val).2 σ (some tk) →
      (stp hψ κ ring C e e).core.leader = false →
      (stp hψ κ ring C e (ring.rightNeighbor e)).core.leader = false →
      (stp hψ κ ring C e e).core.reset_cmd = false →
      (stp hψ κ ring C e (ring.rightNeighbor e)).core.reset_cmd = false →
      Inv σ (stp hψ κ ring C e) N (RD K σ u (ring.rightNeighbor e).val (some tk)) := by
    intro tk h L1 L2 R1 R2
    refine RD_update ring hn K u u _ _ _ (some tk) e hinv
      (Or.inl rfl) (Or.inr rfl) ?_ ?_ (fun i h1 h2 => stp_other hψ κ ring C e i h1 h2)
      (fun c _ _ _ => Iff.rfl)
    · rw [if_neg hue, if_neg hne]; exact ⟨h.1, L1, R1⟩
    · rw [if_neg hur, if_pos rfl]
      exact ⟨h.2, L2, R2⟩
  rcases key with h | ⟨⟨hj, h⟩ | h | h | h, L1, L2, R1, R2⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl ⟨hj, upd _ h L1 L2 R1 R2⟩)
  · exact Or.inr (Or.inr (Or.inl (upd _ h L1 L2 R1 R2)))
  · exact Or.inr (Or.inr (Or.inr (upd _ h L1 L2 R1 R2)))
  · exact Or.inl (Or.inr ⟨e, elim_of_EQ ring _ e h hnext L1 L2 R1 R2⟩)

/-- A4 entering the terminal cell `rn e` of its block: deletion exit. -/
theorem right_apply (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n) (hd : ψ ∣ n)
    (σ : ProvColor) (K : Nat → ProvColor × MainState) (N u : Nat) (C : Fin n → AuthState ψ)
    (e : Fin n) (t : Path2Info)
    (hinv : Inv σ C N (RD K σ u e.val (some t)))
    (he : e.val < N) (hr : (ring.rightNeighbor e).val < N)
    (hKe : KR (K e.val).2) (hKr : KR (K (ring.rightNeighbor e).val).2)
    (ht : t.action = 4) (hle : e.val % ψ ≠ ψ - 1) (hlr : (ring.rightNeighbor e).val % ψ = ψ - 1)
    (hue : ¬ e.val < u) (hur : ¬ (ring.rightNeighbor e).val < u) :
    Reach hψ κ ring C 1 (fun _ => False) := by
  have hne := rn_val_ne ring hn e
  have hl := hinv e he
  have hr0 := hinv _ hr
  simp only [RD_at, if_neg hne, if_neg (Ne.symm hne), if_neg hur, if_neg hue, if_pos rfl] at hl hr0
  rw [hlr] at hr0
  have hnext := label_next hd ring e
  rw [hlr] at hnext
  apply Reach.one hψ κ ring e
  have key := ring_mid hψ κ ring hn σ C e hl hr0 hnext hKe.npd hKr.npd
    (fun q => EQ q (e.val % ψ) (ψ - 1)) (fun m m' h1 h2 h => EQ.of_V m m' h1 h2 h)
    (fun l' r' h1 h2 => Or.inr (Or.inr (mid_right_apply hψ κ σ l' r' t h1 h2 hKe.route
      hKr.route hKe.nlock ht hle)))
  rcases key with h | ⟨h, L1, L2, R1, R2⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr ⟨e, elim_of_EQ ring _ e h hnext L1 L2 R1 R2⟩)

/-- A3/A4 standing in the terminal cell `rn e`: deletion exit. -/
theorem stay_apply (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n) (hd : ψ ∣ n)
    (σ : ProvColor) (K : Nat → ProvColor × MainState) (N u : Nat) (C : Fin n → AuthState ψ)
    (e : Fin n) (t : Path2Info)
    (hinv : Inv σ C N (RD K σ u (ring.rightNeighbor e).val (some t)))
    (he : e.val < N) (hr : (ring.rightNeighbor e).val < N)
    (hKe : KR (K e.val).2) (hKr : KR (K (ring.rightNeighbor e).val).2)
    (ht : t.action = 3 ∨ t.action = 4) (hlr : (ring.rightNeighbor e).val % ψ = ψ - 1)
    (hue : ¬ e.val < u) (hur : ¬ (ring.rightNeighbor e).val < u) :
    Reach hψ κ ring C 1 (fun _ => False) := by
  have hne := rn_val_ne ring hn e
  have hl := hinv e he
  have hr0 := hinv _ hr
  simp only [RD_at, if_neg hne, if_neg hur, if_neg hue, if_pos rfl] at hl hr0
  rw [hlr] at hr0
  have hnext := label_next hd ring e
  rw [hlr] at hnext
  apply Reach.one hψ κ ring e
  have key := ring_mid hψ κ ring hn σ C e hl hr0 hnext hKe.npd hKr.npd
    (fun q => EQ q (e.val % ψ) (ψ - 1)) (fun m m' h1 h2 h => EQ.of_V m m' h1 h2 h)
    (fun l' r' h1 h2 => Or.inr (Or.inr (mid_stay_apply hψ κ σ l' r' t h1 h2 hKe.route
      hKr.route hKe.nlock ht)))
  rcases key with h | ⟨h, L1, L2, R1, R2⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr ⟨e, elim_of_EQ ring _ e h hnext L1 L2 R1 R2⟩)

/-- A3 entering the terminal cell `e` of the source block: deletion exit behind its
predecessor `p`. -/
theorem left_apply (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n) (hd : ψ ∣ n)
    (σ : ProvColor) (K : Nat → ProvColor × MainState) (N u : Nat) (C : Fin n → AuthState ψ)
    (e p : Fin n) (t : Path2Info)
    (hinv : Inv σ C N (RD K σ u (ring.rightNeighbor e).val (some t)))
    (he : e.val < N) (hr : (ring.rightNeighbor e).val < N) (hp : p.val < N)
    (hpe : ring.rightNeighbor p = e)
    (hKe : KR (K e.val).2) (hKr : KR (K (ring.rightNeighbor e).val).2) (hKp : KR (K p.val).2)
    (ht : t.action = 3) (hle : e.val % ψ = ψ - 1) (hlr : (ring.rightNeighbor e).val % ψ ≠ ψ - 1)
    (hue : ¬ e.val < u) (hur : ¬ (ring.rightNeighbor e).val < u) :
    Reach hψ κ ring C 1 (fun _ => False) := by
  have hne := rn_val_ne ring hn e
  have hl := hinv e he
  have hr0 := hinv _ hr
  simp only [RD_at, if_neg hne, if_neg hur, if_neg hue, if_pos rfl] at hl hr0
  rw [hle] at hl
  have hnext := label_next hd ring e
  rw [hle] at hnext
  apply Reach.one hψ κ ring e
  have key := ring_mid hψ κ ring hn σ C e hl hr0 hnext hKe.npd hKr.npd
    (fun q => EQL q (ψ - 1) ((ring.rightNeighbor e).val % ψ))
    (fun m m' h1 h2 h => EQL.of_V m m' h1 h2 h)
    (fun l' r' h1 h2 => Or.inr (Or.inr (mid_left_apply hψ κ σ l' r' t h1 h2 hKe.route
      hKr.route hKr.nlock hKe.wd ht hlr)))
  rcases key with h | ⟨h, L1, L2, R1, R2⟩
  · exact Or.inl (Or.inl h)
  · left; right
    refine ⟨p, ?_⟩
    obtain ⟨la, ⟨b, lp⟩, ls, ra, ⟨b', rp⟩, rn'⟩ := h
    dsimp only at la lp ls ra rp rn'
    have hpl := label_next hd ring p
    rw [hpe, hle] at hpl
    by_cases hpr : p = ring.rightNeighbor e
    · subst hpr
      unfold ElimAt
      rw [hpe]
      refine ⟨L2, L1, R2, R1, ?_, ?_, rn', ls⟩
      · rw [la, ra]; exact hpl
      · rw [rp]; exact PathInfo.noConfusion
    · have hpe' : p ≠ e := by
        intro h'; rw [h'] at hpe; exact rn_ne ring hn e hpe
      have hc := hinv p hp
      unfold ElimAt
      rw [stp_other hψ κ ring C e p hpe' hpr]
      rw [hpe]
      obtain ⟨⟨pa, ⟨pb, pp⟩, -, ps, -, -, -⟩, pL, pR⟩ := hc
      refine ⟨pL, L1, pR, R1, ?_, ?_, ?_, ls⟩
      · rw [la, pa]; exact hpl
      · rw [pp]; exact PathInfo.noConfusion
      · rw [ps]; exact hKp.npd

end Walk

/-! ## Walks: iterated token moves along ring positions -/

section Walks
variable {n ψ : Nat}

/-- `k` applications of `dec`. -/
def decN : Nat → Path2Info → Path2Info
  | 0, t => t
  | k + 1, t => decN k (dec t)

/-- The cell at ring position `x` (taken mod `n`). -/
def cellAt (hn0 : 0 < n) (x : Nat) : Fin n := ⟨x % n, Nat.mod_lt _ hn0⟩

theorem rn_cellAt (ring : DirectedRing n) (hn0 : 0 < n) (x : Nat) :
    ring.rightNeighbor (cellAt hn0 x) = cellAt hn0 (x + 1) := by
  apply Fin.ext
  change (x % n + 1) % n = (x + 1) % n
  exact Nat.mod_add_mod x n 1

/-- An admissible edge for the round kinds: both cells tracked, of round kind, and the
wave stages inert on them whenever one of them holds a token. -/
def AdmE (ring : DirectedRing n) (σ : ProvColor) (K : Nat → ProvColor × MainState) (N : Nat)
    (e : Fin n) : Prop :=
  e.val < N ∧ (ring.rightNeighbor e).val < N ∧ KR (K e.val).2 ∧
    KR (K (ring.rightNeighbor e).val).2 ∧
    ∀ tl tr : Option Path2Info, (tl ≠ none ∨ tr ≠ none) →
      InertV (ψ := ψ) σ (e.val % ψ) (K e.val).1 (K e.val).2 σ tl
        ((ring.rightNeighbor e).val % ψ) (K (ring.rightNeighbor e).val).1
        (K (ring.rightNeighbor e).val).2 σ tr

/-- Frontier bookkeeping of a left move at edge `e` from frontier `u` to `u'`. -/
def FL (ring : DirectedRing n) (σ : ProvColor) (K : Nat → ProvColor × MainState) (N : Nat)
    (e : Fin n) (u u' : Nat) (t : Path2Info) : Prop :=
  ¬ (ring.rightNeighbor e).val < u ∧
    (e.val < u → (K e.val).1 ≠ σ ∧ (K e.val).2 = .depart ∧ t.action = 2) ∧
    ¬ e.val < u' ∧ (∀ c, c < N → c ≠ e.val → (c < u ↔ c < u'))

/-- The token condition of a left move at edge `e`. -/
def TL (ring : DirectedRing n) (e : Fin n) (t : Path2Info) : Prop :=
  (t.action = 2 ∧ 2 ≤ t.position) ∨
    (t.action = 3 ∧ (ring.rightNeighbor e).val % ψ ≠ ψ - 1 ∧ e.val % ψ ≠ ψ - 1)

/-- The token condition of a right move at edge `e`. -/
def TR (ring : DirectedRing n) (e : Fin n) (t : Path2Info) : Prop :=
  (t.action = 1 ∧ 2 ≤ t.position) ∨
    (t.action = 4 ∧ e.val % ψ ≠ ψ - 1 ∧ (ring.rightNeighbor e).val % ψ ≠ ψ - 1)

/-- `k` left moves from position `x`: the token ends at `x - k`, decremented `k` times. -/
theorem left_walk (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n) (hd : ψ ∣ n)
    (σ : ProvColor) (K : Nat → ProvColor × MainState) (N : Nat) (U : Nat → Nat) :
    ∀ (k x : Nat) (C : Fin n → AuthState ψ) (t : Path2Info), k ≤ x →
    (∀ i, i < k → AdmE (ψ := ψ) ring σ K N (cellAt (by omega) (x - 1 - i))) →
    (∀ i, i < k → TL (ψ := ψ) ring (cellAt (by omega) (x - 1 - i)) (decN i t)) →
    (∀ i, i < k → FL ring σ K N (cellAt (by omega) (x - 1 - i)) (U (x - i)) (U (x - 1 - i))
      (decN i t)) →
    Inv σ C N (RD K σ (U x) (x % n) (some t)) →
    Reach hψ κ ring C k (fun C' => Inv σ C' N (RD K σ (U (x - k)) ((x - k) % n)
      (some (decN k t)))) := by
  have hn0 : 0 < n := by omega
  intro k
  induction k with
  | zero =>
    intro x C t _ _ _ _ h
    exact Reach.pure hψ κ ring h
  | succ k ih =>
    intro x C t hk hA hT hF h
    have hx : x - 1 + 1 = x := by omega
    have hrn : ring.rightNeighbor (cellAt hn0 (x - 1)) = cellAt hn0 x := by
      rw [rn_cellAt, hx]
    obtain ⟨a1, a2, a3, a4, a5⟩ := hA 0 (by omega)
    have hT0 := hT 0 (by omega)
    obtain ⟨f1, f2, f3, f4⟩ := hF 0 (by omega)
    simp only [Nat.sub_zero, decN] at a1 a2 a3 a4 a5 hT0 f1 f2 f3 f4
    have step := left_move hψ κ ring hn hd σ K N (U x) (U (x - 1)) C (cellAt hn0 (x - 1)) t
      (by rw [hrn]; exact h) a1 a2 a3 a4 (a5 _ _ (Or.inl (by simp))) hT0 f1 f2 f3 f4
    have hk' := Nat.add_comm 1 k ▸ Reach.bind step (fun C' hC' => ih (x - 1) C' (dec t) (by omega)
      (fun i hi => by have := hA (i + 1) (by omega); rwa [show x - 1 - (i + 1) = x - 1 - 1 - i by omega] at this)
      (fun i hi => by
        have := hT (i + 1) (by omega)
        rwa [show x - 1 - (i + 1) = x - 1 - 1 - i by omega] at this)
      (fun i hi => by
        have := hF (i + 1) (by omega)
        rwa [show x - 1 - (i + 1) = x - 1 - 1 - i by omega, show x - (i + 1) = x - 1 - i by omega] at this)
      hC')
    rw [show x - (k + 1) = x - 1 - k by omega]
    exact hk'

/-- `k` right moves from position `x` with a fixed frontier. -/
theorem right_walk (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n) (hd : ψ ∣ n)
    (σ : ProvColor) (K : Nat → ProvColor × MainState) (N u : Nat) :
    ∀ (k x : Nat) (C : Fin n → AuthState ψ) (t : Path2Info),
    (∀ i, i < k → AdmE (ψ := ψ) ring σ K N (cellAt (by omega) (x + i))) →
    (∀ i, i < k → TR (ψ := ψ) ring (cellAt (by omega) (x + i)) (decN i t)) →
    (∀ i, i ≤ k → ¬ (cellAt (n := n) (by omega) (x + i)).val < u) →
    Inv σ C N (RD K σ u (x % n) (some t)) →
    Reach hψ κ ring C k (fun C' => Inv σ C' N (RD K σ u ((x + k) % n) (some (decN k t)))) := by
  have hn0 : 0 < n := by omega
  intro k
  induction k with
  | zero =>
    intro x C t _ _ _ h
    exact Reach.pure hψ κ ring h
  | succ k ih =>
    intro x C t hA hT hF h
    have hrn : ring.rightNeighbor (cellAt hn0 x) = cellAt hn0 (x + 1) := rn_cellAt ring hn0 x
    obtain ⟨a1, a2, a3, a4, a5⟩ := hA 0 (by omega)
    have hT0 := hT 0 (by omega)
    have f0 := hF 0 (by omega)
    have f1 := hF 1 (by omega)
    simp only [Nat.add_zero, decN] at a1 a2 a3 a4 a5 hT0 f0 f1
    have step := right_move hψ κ ring hn hd σ K N u C (cellAt hn0 x) t h a1 a2 a3 a4
      (a5 _ _ (Or.inr (by simp))) hT0 f0 (by rw [hrn]; exact f1)
    rw [hrn] at step
    have hk' := Nat.add_comm 1 k ▸ Reach.bind step (fun C' hC' => ih (x + 1) C' (dec t)
      (fun i hi => by have := hA (i + 1) (by omega); rwa [show x + (i + 1) = x + 1 + i by omega] at this)
      (fun i hi => by
        have := hT (i + 1) (by omega)
        rwa [show x + (i + 1) = x + 1 + i by omega] at this)
      (fun i hi => by
        have := hF (i + 1) (by omega)
        rwa [show x + (i + 1) = x + 1 + i by omega] at this)
      hC')
    rw [show x + (k + 1) = x + 1 + k by omega]
    exact hk'

theorem dec_iter_A2 (j : Nat) : ∀ i s, decN i (⟨j, 0, s, 2⟩ : Path2Info) = ⟨j, 0, s - i, 2⟩
  | 0, s => rfl
  | i + 1, s => by
    show decN i (dec ⟨j, 0, s, 2⟩) = _
    rw [show dec (⟨j, 0, s, 2⟩ : Path2Info) = ⟨j, 0, s - 1, 2⟩ by simp [dec], dec_iter_A2 j i]
    simp only [Path2Info.mk.injEq, true_and, and_true]; omega

theorem dec_iter_A1 (j lb : Nat) : ∀ i s, decN i (⟨j, lb, s, 1⟩ : Path2Info) = ⟨j, lb, s - i, 1⟩
  | 0, s => rfl
  | i + 1, s => by
    show decN i (dec ⟨j, lb, s, 1⟩) = _
    rw [show dec (⟨j, lb, s, 1⟩ : Path2Info) = ⟨j, lb, s - 1, 1⟩ by simp [dec], dec_iter_A1 j lb i]
    simp only [Path2Info.mk.injEq, true_and, and_true]; omega

theorem dec_fix (t : Path2Info) (h : t.action = 3 ∨ t.action = 4) : dec t = t := by
  unfold dec
  rw [if_neg]
  rcases h with h | h <;> rw [h] <;> decide

theorem dec_iter_fix (t : Path2Info) (h : t.action = 3 ∨ t.action = 4) : ∀ i, decN i t = t
  | 0 => rfl
  | i + 1 => by
    show decN i (dec t) = t
    rw [dec_fix t h, dec_iter_fix t h i]

end Walks

/-! ## The comparison rounds

Positions are ring positions `x` (cell `x mod n`).  The source block occupies positions
`0..ψ-1`, the target block positions `ψ..2ψ-1` (for `m = 1` both are the same block).
Round `j` starts with `A2⟨j,0,ψ-1,2⟩` at position `j+ψ-1`; B_j moves it left to position `j`
(landing: `A1⟨j,lb,ψ,1⟩`), F_j moves that right to position `j+ψ` (landing: a leader, the next
A2 at `j+ψ`, or A4/A3 at `j+ψ`).  A4 walks right and is applied at position `2ψ-1`; A3
walks left and is applied at position `ψ-1`. -/

section Rounds
variable {n ψ : Nat}

theorem cellAt_val (hn0 : 0 < n) (y : Nat) : (cellAt hn0 y).val = y % n := rfl

theorem cellAt_lab (hd : ψ ∣ n) (hn0 : 0 < n) (y : Nat) : (cellAt hn0 y).val % ψ = y % ψ :=
  Nat.mod_mod_of_dvd y hd

theorem rn_val (ring : DirectedRing n) (hn0 : 0 < n) (y : Nat) :
    (ring.rightNeighbor (cellAt hn0 y)).val = (y + 1) % n := by
  rw [rn_cellAt]; rfl

/-- The hypotheses on the round kinds. -/
structure RoundKinds (ring : DirectedRing n) (hn0 : 0 < n) (σ : ProvColor)
    (K : Nat → ProvColor × MainState) (N : Nat) (r0 : Bool) : Prop where
  adm : ∀ y, y ≤ 2 * ψ - 2 → AdmE (ψ := ψ) ring σ K N (cellAt hn0 y)
  wave : ∀ j, j < ψ → waveState (K ((j + ψ) % n)).2 = true
  claim : r0 = true → 2 * ψ ≤ n ∧ ∀ y, y < ψ - 1 → (K y).1 ≠ σ ∧ (K y).2 = .depart

/-- A4 born at position `ψ+j`: deletion exit within `ψ-1` edges. -/
theorem suffix4 (hψ : ψ > 0) (hψ2 : 2 ≤ ψ) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n)
    (hd : ψ ∣ n) (σ : ProvColor) (K : Nat → ProvColor × MainState) (N : Nat) (r0 : Bool)
    (hK : RoundKinds (ψ := ψ) ring (by omega) σ K N r0) (C : Fin n → AuthState ψ) (j : Nat)
    (hj : j < ψ) (h : Inv σ C N (RD K σ 0 ((ψ + j) % n) (some ⟨0, 0, 0, 4⟩))) :
    Reach hψ κ ring C (ψ - 1) (fun _ => False) := by
  have hn0 : 0 < n := by omega
  have hz : ∀ c : Nat, ¬ c < 0 := fun c => Nat.not_lt_zero c
  by_cases hjl : j = ψ - 1
  · subst hjl
    obtain ⟨a1, a2, a3, a4, -⟩ := hK.adm (2 * ψ - 2) (Nat.le_refl _)
    have hq : (ψ + (ψ - 1)) % n = (ring.rightNeighbor (cellAt hn0 (2 * ψ - 2))).val := by
      rw [rn_val]; congr 1; omega
    rw [hq] at h
    have hr := stay_apply hψ κ ring hn hd σ K N 0 C (cellAt hn0 (2 * ψ - 2)) ⟨0, 0, 0, 4⟩ h a1 a2 a3 a4
      (Or.inr rfl) (by rw [rn_val, Nat.mod_mod_of_dvd _ hd]; rw [show 2 * ψ - 2 + 1 = ψ + (ψ - 1) by omega,
        Nat.add_mod_left]; exact Nat.mod_eq_of_lt (by omega)) (hz _) (hz _)
    exact hr.mono (by omega) (fun _ h => h)
  · have hw := right_walk hψ κ ring hn hd σ K N 0 (ψ - 2 - j) (ψ + j) C ⟨0, 0, 0, 4⟩
      (fun i hi => hK.adm _ (by omega))
      (fun i hi => by
        rw [dec_iter_fix _ (Or.inr rfl)]
        refine Or.inr ⟨rfl, ?_, ?_⟩
        · rw [cellAt_lab hd, show ψ + j + i = ψ + (j + i) by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt (by omega)]; omega
        · rw [rn_val, Nat.mod_mod_of_dvd _ hd, show ψ + j + i + 1 = ψ + (j + i + 1) by omega,
            Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]; omega)
      (fun i hi => hz _) h
    rw [dec_iter_fix _ (Or.inr rfl), show ψ + j + (ψ - 2 - j) = 2 * ψ - 2 by omega] at hw
    have hk := Reach.bind hw (fun C' hC' => by
      obtain ⟨a1, a2, a3, a4, -⟩ := hK.adm (2 * ψ - 2) (Nat.le_refl _)
      exact right_apply hψ κ ring hn hd σ K N 0 C' (cellAt hn0 (2 * ψ - 2)) ⟨0, 0, 0, 4⟩ hC' a1 a2 a3 a4
        rfl (by rw [cellAt_lab hd, show 2 * ψ - 2 = ψ + (ψ - 2) by omega, Nat.add_mod_left,
          Nat.mod_eq_of_lt (by omega)]; omega)
        (by rw [rn_val, Nat.mod_mod_of_dvd _ hd, show 2 * ψ - 2 + 1 = ψ + (ψ - 1) by omega,
          Nat.add_mod_left]; exact Nat.mod_eq_of_lt (by omega)) (hz _) (hz _))
    exact hk.mono (by omega) (fun _ h => h)

/-- A3 born at position `ψ+j`: deletion exit within `ψ-1` edges. -/
theorem suffix3 (hψ : ψ > 0) (hψ2 : 2 ≤ ψ) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n)
    (hd : ψ ∣ n) (σ : ProvColor) (K : Nat → ProvColor × MainState) (N : Nat) (r0 : Bool)
    (hK : RoundKinds (ψ := ψ) ring (by omega) σ K N r0) (C : Fin n → AuthState ψ) (j : Nat)
    (hj : j < ψ) (h : Inv σ C N (RD K σ 0 ((ψ + j) % n) (some ⟨0, 0, 0, 3⟩))) :
    Reach hψ κ ring C (ψ - 1) (fun _ => False) := by
  have hn0 : 0 < n := by omega
  have hz : ∀ c : Nat, ¬ c < 0 := fun c => Nat.not_lt_zero c
  by_cases hjl : j = ψ - 1
  · subst hjl
    obtain ⟨a1, a2, a3, a4, -⟩ := hK.adm (2 * ψ - 2) (Nat.le_refl _)
    have hq : (ψ + (ψ - 1)) % n = (ring.rightNeighbor (cellAt hn0 (2 * ψ - 2))).val := by
      rw [rn_val]; congr 1; omega
    rw [hq] at h
    have hr := stay_apply hψ κ ring hn hd σ K N 0 C (cellAt hn0 (2 * ψ - 2)) ⟨0, 0, 0, 3⟩ h a1 a2 a3 a4
      (Or.inl rfl) (by rw [rn_val, Nat.mod_mod_of_dvd _ hd]; rw [show 2 * ψ - 2 + 1 = ψ + (ψ - 1) by omega,
        Nat.add_mod_left]; exact Nat.mod_eq_of_lt (by omega)) (hz _) (hz _)
    exact hr.mono (by omega) (fun _ h => h)
  · have hw := left_walk hψ κ ring hn hd σ K N (fun _ => 0) j (ψ + j) C ⟨0, 0, 0, 3⟩ (by omega)
      (fun i hi => hK.adm _ (by omega))
      (fun i hi => by
        rw [dec_iter_fix _ (Or.inl rfl)]
        refine Or.inr ⟨rfl, ?_, ?_⟩
        · rw [rn_val, Nat.mod_mod_of_dvd _ hd, show ψ + j - 1 - i + 1 = ψ + (j - i) by omega,
            Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]; omega
        · rw [cellAt_lab hd, show ψ + j - 1 - i = ψ + (j - 1 - i) by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt (by omega)]; omega)
      (fun i hi => ⟨hz _, fun h => absurd h (hz _), hz _, fun _ _ _ => Iff.rfl⟩) h
    rw [dec_iter_fix _ (Or.inl rfl), show ψ + j - j = ψ by omega] at hw
    have hk := Reach.bind hw (fun C' hC' => by
      obtain ⟨a1, a2, a3, a4, -⟩ := hK.adm (ψ - 1) (by omega)
      obtain ⟨p1, -, p3, -, -⟩ := hK.adm (ψ - 2) (by omega)
      have hq : ψ % n = (ring.rightNeighbor (cellAt hn0 (ψ - 1))).val := by
        rw [rn_val]; congr 1; omega
      rw [hq] at hC'
      exact left_apply hψ κ ring hn hd σ K N 0 C' (cellAt hn0 (ψ - 1)) (cellAt hn0 (ψ - 2))
        ⟨0, 0, 0, 3⟩ hC' a1 a2 p1 (by rw [rn_cellAt, show ψ - 2 + 1 = ψ - 1 by omega]) a3 a4 p3 rfl
        (by rw [cellAt_lab hd]; exact Nat.mod_eq_of_lt (by omega))
        (by rw [rn_val, Nat.mod_mod_of_dvd _ hd, show ψ - 1 + 1 = ψ by omega, Nat.mod_self]; omega)
        (hz _) (hz _))
    exact hk.mono (by omega) (fun _ h => h)

/-- The frontier of round `j`: in round 0 (when the source block is still unclaimed) the
cells below the token are unclaimed. -/
def U0 (r0 : Bool) (j : Nat) (x : Nat) : Nat := if r0 = true ∧ j = 0 then x else 0

theorem U0_zero (r0 : Bool) (j x : Nat) (h : ¬ (r0 = true ∧ j = 0)) : U0 r0 j x = 0 := by
  simp only [U0, if_neg h]

/-- One comparison round: B_j, landing, F_j, landing (`2ψ - 1` edges). -/
theorem round_step (hψ : ψ > 0) (hψ2 : 2 ≤ ψ) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n)
    (hd : ψ ∣ n) (σ : ProvColor) (K : Nat → ProvColor × MainState) (N : Nat) (r0 : Bool)
    (hK : RoundKinds (ψ := ψ) ring (by omega) σ K N r0) (C : Fin n → AuthState ψ) (j : Nat)
    (hj : j < ψ)
    (h : Inv σ C N (RD K σ (U0 r0 j (j + ψ - 1)) ((j + ψ - 1) % n) (some ⟨j, 0, ψ - 1, 2⟩))) :
    Reach hψ κ ring C (2 * ψ - 1) (fun C' =>
      (j ≠ ψ - 1 ∧ Inv σ C' N (RD K σ 0 ((j + ψ) % n) (some ⟨j + 1, 0, ψ - 1, 2⟩))) ∨
      Inv σ C' N (RD K σ 0 ((ψ + j) % n) (some ⟨0, 0, 0, 4⟩)) ∨
      Inv σ C' N (RD K σ 0 ((ψ + j) % n) (some ⟨0, 0, 0, 3⟩))) := by
  have hn0 : 0 < n := by omega
  have hz : ∀ c : Nat, ¬ c < 0 := fun c => Nat.not_lt_zero c
  have hjm : j % ψ = j := Nat.mod_eq_of_lt hj
  -- B_j: ψ - 2 left moves
  have hB := left_walk hψ κ ring hn hd σ K N (U0 r0 j) (ψ - 2) (j + ψ - 1) C ⟨j, 0, ψ - 1, 2⟩
    (by omega) (fun i hi => hK.adm _ (by omega))
    (fun i hi => by rw [dec_iter_A2]; exact Or.inl ⟨rfl, show 2 ≤ ψ - 1 - i by omega⟩)
    (fun i hi => by
      rw [dec_iter_A2]
      by_cases hc : r0 = true ∧ j = 0
      · obtain ⟨hr, hj0⟩ := hc
        subst hj0
        obtain ⟨hn2, hcl⟩ := hK.claim hr
        simp only [U0, hr, and_self, if_true]
        unfold FL
        rw [rn_val, cellAt_val, Nat.mod_eq_of_lt (show 0 + ψ - 1 - 1 - i < n by omega),
          show 0 + ψ - 1 - 1 - i + 1 = 0 + ψ - 1 - i by omega,
          Nat.mod_eq_of_lt (show 0 + ψ - 1 - i < n by omega)]
        refine ⟨by omega, fun _ => ⟨(hcl _ (by omega)).1, (hcl _ (by omega)).2, rfl⟩, by omega,
          fun c _ hc => ⟨fun _ => by omega, fun _ => by omega⟩⟩
      · simp only [U0_zero r0 j _ hc]
        exact ⟨hz _, fun h => absurd h (hz _), hz _, fun _ _ _ => Iff.rfl⟩) h
  rw [dec_iter_A2, show j + ψ - 1 - (ψ - 2) = j + 1 by omega,
    show ψ - 1 - (ψ - 2) = 1 by omega] at hB
  -- landing on position j
  have hL : ∀ C1 : Fin n → AuthState ψ,
      Inv σ C1 N (RD K σ (U0 r0 j (j + 1)) ((j + 1) % n) (some ⟨j, 0, 1, 2⟩)) →
      Reach hψ κ ring C1 1 (fun C2 => ∃ lb, Inv σ C2 N (RD K σ 0 (j % n) (some ⟨j, lb, ψ, 1⟩))) := by
    intro C1 h1
    obtain ⟨a1, a2, a3, a4, a5⟩ := hK.adm j (by omega)
    have hq : (j + 1) % n = (ring.rightNeighbor (cellAt hn0 j)).val := (rn_val ring hn0 j).symm
    have hl : j = (cellAt hn0 j).val % ψ := by rw [cellAt_lab hd, hjm]
    rw [hq] at h1
    conv at h1 => rhs; rhs; rhs; rw [hl]
    have hU : U0 r0 j j = 0 := by
      by_cases hc : r0 = true ∧ j = 0
      · simp only [U0, if_pos hc]; exact hc.2
      · exact U0_zero r0 j j hc
    have hr' := left_land hψ κ ring hn hd σ K N (U0 r0 j (j + 1)) (U0 r0 j j) C1 (cellAt hn0 j) h1
      a1 a2 a3 a4 (a5 _ _ (Or.inl (by simp)))
      (by
        by_cases hc : r0 = true ∧ j = 0
        · obtain ⟨hr, hj0⟩ := hc; subst hj0
          simp only [U0, hr, and_self, if_true]
          rw [rn_val, Nat.mod_eq_of_lt hn]; omega
        · rw [U0_zero r0 j _ hc]; exact hz _)
      (by
        intro hlt
        by_cases hc : r0 = true ∧ j = 0
        · obtain ⟨hr, hj0⟩ := hc; subst hj0
          obtain ⟨-, hcl⟩ := hK.claim hr
          simp only [cellAt_val, Nat.zero_mod]
          exact hcl 0 (by omega)
        · rw [U0_zero r0 j _ hc] at hlt; exact absurd hlt (hz _))
      (by rw [hU]; exact hz _)
      (by
        intro c hc hne
        by_cases hc' : r0 = true ∧ j = 0
        · obtain ⟨hr, hj0⟩ := hc'; subst hj0
          simp only [U0, hr, and_self, if_true]
          simp only [cellAt_val, Nat.zero_mod] at hne
          exact ⟨fun _ => by omega, fun _ => by omega⟩
        · rw [U0_zero r0 j _ hc', U0_zero r0 j _ hc'])
    rw [hU, ← hl, cellAt_val] at hr'
    exact hr'
  -- F_j: ψ - 1 right moves
  have hF : ∀ (C2 : Fin n → AuthState ψ) (lb : Nat),
      Inv σ C2 N (RD K σ 0 (j % n) (some ⟨j, lb, ψ, 1⟩)) →
      Reach hψ κ ring C2 (ψ - 1) (fun C3 =>
        Inv σ C3 N (RD K σ 0 ((j + ψ - 1) % n) (some ⟨j, lb, 1, 1⟩))) := by
    intro C2 lb h2
    have hw := right_walk hψ κ ring hn hd σ K N 0 (ψ - 1) j C2 ⟨j, lb, ψ, 1⟩
      (fun i hi => hK.adm _ (by omega))
      (fun i hi => by rw [dec_iter_A1]; exact Or.inl ⟨rfl, show 2 ≤ ψ - i by omega⟩)
      (fun i hi => hz _) h2
    rw [dec_iter_A1, show j + (ψ - 1) = j + ψ - 1 by omega,
      show ψ - (ψ - 1) = 1 by omega] at hw
    exact hw
  -- landing on position j + ψ
  have hR : ∀ (C3 : Fin n → AuthState ψ) (lb : Nat),
      Inv σ C3 N (RD K σ 0 ((j + ψ - 1) % n) (some ⟨j, lb, 1, 1⟩)) →
      Reach hψ κ ring C3 1 (fun C' =>
        (j ≠ ψ - 1 ∧ Inv σ C' N (RD K σ 0 ((j + ψ) % n) (some ⟨j + 1, 0, ψ - 1, 2⟩))) ∨
        Inv σ C' N (RD K σ 0 ((ψ + j) % n) (some ⟨0, 0, 0, 4⟩)) ∨
        Inv σ C' N (RD K σ 0 ((ψ + j) % n) (some ⟨0, 0, 0, 3⟩))) := by
    intro C3 lb h3
    obtain ⟨a1, a2, a3, a4, a5⟩ := hK.adm (j + ψ - 1) (by omega)
    have hrv : (ring.rightNeighbor (cellAt hn0 (j + ψ - 1))).val = (j + ψ) % n := by
      rw [rn_val, show j + ψ - 1 + 1 = j + ψ by omega]
    have hlab : (ring.rightNeighbor (cellAt hn0 (j + ψ - 1))).val % ψ = j := by
      rw [hrv, Nat.mod_mod_of_dvd _ hd, Nat.add_mod_right, hjm]
    have h3' : Inv σ C3 N (RD K σ 0 (cellAt hn0 (j + ψ - 1)).val
        (some ⟨(ring.rightNeighbor (cellAt hn0 (j + ψ - 1))).val % ψ, lb, 1, 1⟩)) := by
      rw [hlab, cellAt_val]; exact h3
    have hw : waveState (K (ring.rightNeighbor (cellAt hn0 (j + ψ - 1))).val).2 = true := by
      rw [hrv]; exact hK.wave j hj
    have hr' := right_land hψ κ ring hn hd σ K N 0 C3 (cellAt hn0 (j + ψ - 1)) lb h3' a1 a2 a3 a4 hw
      (a5 _ _ (Or.inr (by simp))) (hz _) (hz _)
    rw [hlab, hrv, show j + ψ = ψ + j by omega] at hr'
    refine hr'.mono (Nat.le_refl 1) (fun C' hC' => ?_)
    rw [show ψ + j = j + ψ by omega] at hC'
    rcases hC' with ⟨h1, h2⟩ | h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · right; left; rw [show ψ + j = j + ψ by omega]; exact h2
    · right; right; rw [show ψ + j = j + ψ by omega]; exact h2
  have hall := Reach.bind (Reach.bind hB hL) (fun C2 ⟨lb, h2⟩ => Reach.bind (hF C2 lb h2) (fun C3 h3 => hR C3 lb h3))
  exact hall.mono (by omega) (fun _ h => h)

/-- All rounds from round `j` (with `j + d = ψ - 1`): a leader or a deletion exit within
`(d+1)(2ψ-1) + ψ - 1` edges. -/
theorem rounds (hψ : ψ > 0) (hψ2 : 2 ≤ ψ) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n)
    (hd : ψ ∣ n) (σ : ProvColor) (K : Nat → ProvColor × MainState) (N : Nat) (r0 : Bool)
    (hK : RoundKinds (ψ := ψ) ring (by omega) σ K N r0) :
    ∀ (d j : Nat) (C : Fin n → AuthState ψ), j + d = ψ - 1 →
    Inv σ C N (RD K σ (U0 r0 j (j + ψ - 1)) ((j + ψ - 1) % n) (some ⟨j, 0, ψ - 1, 2⟩)) →
    Reach hψ κ ring C ((d + 1) * (2 * ψ - 1) + (ψ - 1)) (fun _ => False) := by
  intro d
  induction d with
  | zero =>
    intro j C hjd h
    have hs := round_step hψ hψ2 κ ring hn hd σ K N r0 hK C j (by omega) h
    have hall := Reach.bind hs (fun C' hC' => by
      rcases hC' with ⟨hne, -⟩ | h4 | h3
      · exact absurd (by omega : j = ψ - 1) hne
      · exact suffix4 hψ hψ2 κ ring hn hd σ K N r0 hK C' j (by omega) h4
      · exact suffix3 hψ hψ2 κ ring hn hd σ K N r0 hK C' j (by omega) h3)
    exact hall.mono (by omega) (fun _ h => h)
  | succ d ih =>
    intro j C hjd h
    have hs := round_step hψ hψ2 κ ring hn hd σ K N r0 hK C j (by omega) h
    have hall := Reach.bind hs (fun C' hC' => by
      rcases hC' with ⟨-, h2⟩ | h4 | h3
      · have hU : U0 r0 (j + 1) (j + 1 + ψ - 1) = 0 := U0_zero r0 _ _ (fun h => by omega)
        have h2' : Inv σ C' N (RD K σ (U0 r0 (j + 1) (j + 1 + ψ - 1)) ((j + 1 + ψ - 1) % n)
            (some ⟨j + 1, 0, ψ - 1, 2⟩)) := by
          rw [hU, show j + 1 + ψ - 1 = j + ψ by omega]; exact h2
        exact ih (j + 1) C' (by omega) h2'
      · exact (suffix4 hψ hψ2 κ ring hn hd σ K N r0 hK C' j (by omega) h4).mono
          (Nat.le_add_left _ _) (fun _ h => h)
      · exact (suffix3 hψ hψ2 κ ring hn hd σ K N r0 hK C' j (by omega) h3).mono
          (Nat.le_add_left _ _) (fun _ h => h))
    refine hall.mono ?_ (fun _ h => h)
    rw [Nat.succ_mul (d + 1)]
    omega

end Rounds

/-! ## The session set-up (word P of Q20610 §2) and the first emission -/

section Setup
variable {n ψ : Nat}

/-- One served edge with explicit old and new descriptors. -/
theorem gen_step (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n) (σ : ProvColor)
    (N : Nat) (C : Fin n → AuthState ψ) (e : Fin n) (D D' : Nat → Desc) (hinv : Inv σ C N D)
    (he : e.val < N) (hr : (ring.rightNeighbor e).val < N) {a a' : Nat}
    (ha : e.val % ψ = a) (ha' : (ring.rightNeighbor e).val % ψ = a') (hnext : a' = (a + 1) % ψ)
    {γl stl cml tokl γr str cmr tokr stl' cml' tokl' str' cmr' tokr'}
    (hx : D e.val = ⟨γl, stl, cml, tokl⟩) (hy : D (ring.rightNeighbor e).val = ⟨γr, str, cmr, tokr⟩)
    (hx' : D' e.val = ⟨γl, stl', cml', tokl'⟩)
    (hy' : D' (ring.rightNeighbor e).val = ⟨γr, str', cmr', tokr'⟩)
    (hoth : ∀ c, c < N → c ≠ e.val → c ≠ (ring.rightNeighbor e).val → D' c = D c)
    (hNl : NPD stl) (hNr : NPD str)
    (hmid : ∀ l' r', Cell σ l' a γl stl cml tokl → Cell σ r' a' γr str cmr tokr →
      Out σ (midS hψ κ authFplusmcc l' r') a γl stl' cml' tokl' a' γr str' cmr' tokr' ∨
        EQ (midS hψ κ authFplusmcc l' r') a a') :
    Reach hψ κ ring C 1 (fun C' => Inv σ C' N D') := by
  have hl : Cell σ (C e) a γl stl cml tokl := by
    have := hinv e he; rw [hx, ha] at this; exact this
  have hr0 : Cell σ (C (ring.rightNeighbor e)) a' γr str cmr tokr := by
    have := hinv _ hr; rw [hy, ha'] at this; exact this
  apply Reach.one hψ κ ring e
  have key := ring_mid hψ κ ring hn σ C e hl hr0 hnext hNl hNr
    (fun q => Out σ q a γl stl' cml' tokl' a' γr str' cmr' tokr' ∨ EQ q a a')
    (fun m m' h1 h2 h => Or.imp (Out.of_V m m' h1 h2) (EQ.of_V m m' h1 h2) h)
    (fun l' r' h1 h2 => Or.inr (Or.inr (hmid l' r' h1 h2)))
  rcases key with h | ⟨h | h, L1, L2, R1, R2⟩
  · exact Or.inl (Or.inl h)
  · right
    refine Inv.update ring e hinv D' ?_ ?_ (fun i h1 h2 => stp_other hψ κ ring C e i h1 h2) hoth
    · rw [hx', ha]; exact ⟨h.1, L1, R1⟩
    · rw [hy', ha']; exact ⟨h.2, L2, R2⟩
  · exact Or.inl (Or.inr ⟨e, elim_of_EQ ring _ e h hnext L1 L2 R1 R2⟩)

/-! ### Two blocks (`m ≥ 2`): cells `0..ψ-1` (source, colour `γ₀`) and `ψ..2ψ-1` (target,
colour `γ₁`) -/

/-- Initial descriptors: both blocks serial. -/
def DI (γ0 γ1 : ProvColor) (ψ : Nat) (c : Nat) : Desc :=
  if c < ψ then ⟨γ0, .depart, γ0, none⟩ else ⟨γ1, .depart, γ1, none⟩

/-- After the boundary start and `k` lock steps: target cells up to `ψ+k` locked. -/
def DA (σ γ0 γ1 : ProvColor) (ψ k : Nat) (c : Nat) : Desc :=
  if c < ψ - 1 then ⟨γ0, .depart, γ0, none⟩
  else if c = ψ - 1 then ⟨γ0, .depart, σ, none⟩
  else if c ≤ ψ + k then ⟨γ1, .lock, σ, none⟩
  else ⟨γ1, .depart, γ1, none⟩

/-- After the last lock step, with `h` target cells still locked. -/
def DB (σ γ0 γ1 : ProvColor) (ψ h : Nat) (c : Nat) : Desc :=
  if c < ψ - 1 then ⟨γ0, .depart, γ0, none⟩
  else if c = ψ - 1 then ⟨γ0, .depart, σ, none⟩
  else if c < ψ + h then ⟨γ1, .lock, σ, none⟩
  else ⟨γ1, .compare1, σ, none⟩

/-- Round kinds for two blocks. -/
def K2 (γ0 γ1 : ProvColor) (ψ : Nat) (c : Nat) : ProvColor × MainState :=
  if c < ψ then (γ0, if c = ψ - 1 then .compare2 else .depart) else (γ1, .compare1)

/-! ### One block (`m = 1`, `n = ψ`): the block compares with itself -/

def DA1 (σ γ : ProvColor) (ψ k : Nat) (c : Nat) : Desc :=
  if c = ψ - 1 then ⟨γ, .depart, σ, none⟩
  else if c ≤ k then ⟨γ, .lock, σ, none⟩
  else ⟨γ, .depart, γ, none⟩

def DB1 (σ γ : ProvColor) (h : Nat) (c : Nat) : Desc :=
  if c < h then ⟨γ, .lock, σ, none⟩ else ⟨γ, .compare1, σ, none⟩

/-- Round kinds for one block. -/
def K1 (γ : ProvColor) (ψ : Nat) (c : Nat) : ProvColor × MainState :=
  (γ, if c = ψ - 1 then .compare2 else .compare1)

/-- Evaluate a descriptor table at a concrete cell. -/
syntax "dtac" : tactic
macro_rules
  | `(tactic| dtac) => `(tactic| ((simp only [DA, DB, DI, RD, K2, DA1, DB1, K1]; repeat' split) <;>
      first | rfl | (exfalso; omega) | contradiction | (exfalso; simp_all; omega) | omega))

theorem cellAt_small (hn0 : 0 < n) {y : Nat} (h : y < n) : (cellAt hn0 y).val = y :=
  Nat.mod_eq_of_lt h

theorem setup2 (hψ : ψ > 0) (hψ2 : 2 ≤ ψ) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n)
    (hd : ψ ∣ n) (h2 : 2 * ψ ≤ n) (γ0 γ1 : ProvColor) (C : Fin n → AuthState ψ)
    (h : Inv (fresh3 γ0 γ1) C (2 * ψ) (DI γ0 γ1 ψ)) :
    Reach hψ κ ring C (2 * ψ - 1) (fun C' => Inv (fresh3 γ0 γ1) C' (2 * ψ)
      (RD (K2 γ0 γ1 ψ) (fresh3 γ0 γ1) (ψ - 1) (ψ - 1) (some ⟨0, 0, ψ - 1, 2⟩))) := by
  have hn0 : 0 < n := by omega
  have hs0 : fresh3 γ0 γ1 ≠ γ0 := fresh3_ne_left γ0 γ1
  have hs1 : fresh3 γ0 γ1 ≠ γ1 := fresh3_ne_right γ0 γ1
  generalize hσ : fresh3 γ0 γ1 = σ at h hs0 hs1 ⊢
  have cv : ∀ y, y < 2 * ψ → (cellAt hn0 y).val = y := fun y hy => cellAt_small hn0 (by omega)
  have rv : ∀ y, y + 1 < 2 * ψ → (ring.rightNeighbor (cellAt hn0 y)).val = y + 1 := by
    intro y hy; rw [rn_cellAt]; exact cellAt_small hn0 (by omega)
  -- P1: boundary start on edge ψ-1
  have hP1 : Reach hψ κ ring C 1 (fun C' => Inv σ C' (2 * ψ) (DA σ γ0 γ1 ψ 0)) := by
    have e1 := cv (ψ - 1) (by omega)
    have e2 := rv (ψ - 1) (by omega)
    rw [show ψ - 1 + 1 = ψ by omega] at e2
    refine gen_step hψ κ ring hn σ (2 * ψ) C (cellAt hn0 (ψ - 1)) (DI γ0 γ1 ψ) (DA σ γ0 γ1 ψ 0) h
      (by omega) (by omega) (a := ψ - 1) (a' := 0) (γl := γ0) (stl := .depart) (cml := γ0)
      (tokl := none) (γr := γ1) (str := .depart) (cmr := γ1) (tokr := none) (stl' := .depart)
      (cml' := σ) (tokl' := none) (str' := .lock) (cmr' := σ) (tokr' := none) (by rw [e1]; exact Nat.mod_eq_of_lt (by omega))
      (by rw [e2, Nat.mod_self]) (by rw [show ψ - 1 + 1 = ψ by omega, Nat.mod_self])
      (by rw [e1]; dtac) (by rw [e2]; dtac) (by rw [e1]; dtac) (by rw [e2]; dtac)
      (by
        intro c hc h1 h2
        rw [e1] at h1; rw [e2] at h2
        dtac)
      NPD_depart NPD_depart
      (fun l' r' h1 h2 => by
        have := mid_start hψ hψ2 κ σ γ0 γ1 l' r' h1 h2
        rw [hσ] at this
        exact Or.inl this)
  -- P2: lock propagation, ψ - 2 steps
  have hP2 : ∀ k, k ≤ ψ - 2 → ∀ C1 : Fin n → AuthState ψ, Inv σ C1 (2 * ψ) (DA σ γ0 γ1 ψ 0) →
      Reach hψ κ ring C1 k (fun C' => Inv σ C' (2 * ψ) (DA σ γ0 γ1 ψ k)) := by
    intro k
    induction k with
    | zero => intro _ C1 h1; exact Reach.pure hψ κ ring h1
    | succ k ih =>
      intro hk C1 h1
      refine Reach.bind (ih (by omega) C1 h1) (fun C2 h2 => ?_)
      clear ih
      have e1 := cv (ψ + k) (by omega)
      have e2 := rv (ψ + k) (by omega)
      refine gen_step hψ κ ring hn σ (2 * ψ) C2 (cellAt hn0 (ψ + k)) (DA σ γ0 γ1 ψ k)
        (DA σ γ0 γ1 ψ (k + 1)) h2 (by omega) (by omega) (a := k) (a' := k + 1)
        (γl := γ1) (stl := .lock) (cml := σ) (tokl := none) (γr := γ1) (str := .depart)
        (cmr := γ1) (tokr := none) (stl' := .lock) (cml' := σ) (tokl' := none) (str' := .lock)
        (cmr' := σ) (tokr' := none)
        (by rw [e1, Nat.add_mod_left]; exact Nat.mod_eq_of_lt (by omega))
        (by rw [e2, show ψ + k + 1 = ψ + (k + 1) by omega, Nat.add_mod_left];
            exact Nat.mod_eq_of_lt (by omega))
        (Nat.mod_eq_of_lt (by omega)).symm
        (by rw [e1]; dtac) (by rw [e2]; dtac) (by rw [e1]; dtac) (by rw [e2]; dtac)
        (by intro c hc h1 h2; rw [e1] at h1; rw [e2] at h2; dtac)
        ⟨by decide, by decide⟩ NPD_depart
        (fun l' r' h1 h2 => Or.inl (mid_lockprop hψ κ σ l' r' (by omega) h1 h2))
  -- P2, last step: both terminal-side cells become compare1
  have hP2l : ∀ C1 : Fin n → AuthState ψ, Inv σ C1 (2 * ψ) (DA σ γ0 γ1 ψ (ψ - 2)) →
      Reach hψ κ ring C1 1 (fun C' => Inv σ C' (2 * ψ) (DB σ γ0 γ1 ψ (ψ - 2))) := by
    intro C1 h1
    have e1 := cv (2 * ψ - 2) (by omega)
    have e2 := rv (2 * ψ - 2) (by omega)
    refine gen_step hψ κ ring hn σ (2 * ψ) C1 (cellAt hn0 (2 * ψ - 2)) (DA σ γ0 γ1 ψ (ψ - 2))
      (DB σ γ0 γ1 ψ (ψ - 2)) h1 (by omega) (by omega) (a := ψ - 2) (a' := ψ - 2 + 1)
      (γl := γ1) (stl := .lock) (cml := σ) (tokl := none) (γr := γ1) (str := .depart)
      (cmr := γ1) (tokr := none) (stl' := .compare1) (cml' := σ) (tokl' := none)
      (str' := .compare1) (cmr' := σ) (tokr' := none)
      (by rw [e1, show 2 * ψ - 2 = ψ + (ψ - 2) by omega, Nat.add_mod_left];
          exact Nat.mod_eq_of_lt (by omega))
      (by rw [e2, show 2 * ψ - 2 + 1 = ψ + (ψ - 2 + 1) by omega, Nat.add_mod_left];
          exact Nat.mod_eq_of_lt (by omega))
      (Nat.mod_eq_of_lt (by omega)).symm
      (by rw [e1]; dtac) (by rw [e2]; dtac) (by rw [e1]; dtac) (by rw [e2]; dtac)
      (by intro c hc h1 h2; rw [e1] at h1; rw [e2] at h2; dtac)
      ⟨by decide, by decide⟩ NPD_depart
      (fun l' r' h1 h2 => mid_lockprop_last hψ κ σ l' r' (by omega) h1 h2)
  -- P3: acknowledgements, ψ - 2 steps
  have hP3 : ∀ i, i ≤ ψ - 2 → ∀ C1 : Fin n → AuthState ψ,
      Inv σ C1 (2 * ψ) (DB σ γ0 γ1 ψ (ψ - 2)) →
      Reach hψ κ ring C1 i (fun C' => Inv σ C' (2 * ψ) (DB σ γ0 γ1 ψ (ψ - 2 - i))) := by
    intro i
    induction i with
    | zero => intro _ C1 h1; exact Reach.pure hψ κ ring h1
    | succ i ih =>
      intro hi C1 h1
      refine Reach.bind (ih (by omega) C1 h1) (fun C2 h2 => ?_)
      clear ih
      have hh : ψ - 2 - i = ψ - 2 - (i + 1) + 1 := by omega
      rw [hh] at h2
      generalize hH : ψ - 2 - (i + 1) = H at h2 ⊢
      have hH' : H + 1 < ψ - 1 := by omega
      have e1 := cv (ψ + H) (by omega)
      have e2 := rv (ψ + H) (by omega)
      refine gen_step hψ κ ring hn σ (2 * ψ) C2 (cellAt hn0 (ψ + H)) (DB σ γ0 γ1 ψ (H + 1))
        (DB σ γ0 γ1 ψ H) h2 (by omega) (by omega) (a := H) (a' := H + 1)
        (γl := γ1) (stl := .lock) (cml := σ) (tokl := none) (γr := γ1) (str := .compare1)
        (cmr := σ) (tokr := none) (stl' := .compare1) (cml' := σ) (tokl' := none)
        (str' := .compare1) (cmr' := σ) (tokr' := none)
        (by rw [e1, Nat.add_mod_left]; exact Nat.mod_eq_of_lt (by omega))
        (by rw [e2, show ψ + H + 1 = ψ + (H + 1) by omega, Nat.add_mod_left];
            exact Nat.mod_eq_of_lt (by omega))
        (Nat.mod_eq_of_lt (by omega)).symm
        (by rw [e1]; dtac) (by rw [e2]; dtac) (by rw [e1]; dtac) (by rw [e2]; dtac)
        (by intro c hc h1 h2; rw [e1] at h1; rw [e2] at h2; dtac)
        ⟨by decide, by decide⟩ NPD_c1
        (fun l' r' h1 h2 => Or.inl (mid_ack hψ κ σ l' r' hH' h1 h2))
  -- W0: the first emission
  have hW : ∀ C1 : Fin n → AuthState ψ, Inv σ C1 (2 * ψ) (DB σ γ0 γ1 ψ 0) →
      Reach hψ κ ring C1 1 (fun C' => Inv σ C' (2 * ψ)
        (RD (K2 γ0 γ1 ψ) σ (ψ - 1) (ψ - 1) (some ⟨0, 0, ψ - 1, 2⟩))) := by
    intro C1 h1
    have e1 := cv (ψ - 1) (by omega)
    have e2 := rv (ψ - 1) (by omega)
    rw [show ψ - 1 + 1 = ψ by omega] at e2
    refine gen_step hψ κ ring hn σ (2 * ψ) C1 (cellAt hn0 (ψ - 1)) (DB σ γ0 γ1 ψ 0)
      _ h1 (by omega) (by omega) (a := ψ - 1) (a' := 0)
      (γl := γ0) (stl := .depart) (cml := σ) (tokl := none) (γr := γ1) (str := .compare1)
      (cmr := σ) (tokr := none) (stl' := .compare2) (cml' := σ) (tokl' := some ⟨0, 0, ψ - 1, 2⟩)
      (str' := .compare1) (cmr' := σ) (tokr' := none)
      (by rw [e1]; exact Nat.mod_eq_of_lt (by omega)) (by rw [e2, Nat.mod_self])
      (by rw [show ψ - 1 + 1 = ψ by omega, Nat.mod_self])
      (by rw [e1]; dtac) (by rw [e2]; dtac) (by rw [e1]; dtac) (by rw [e2]; dtac)
      (by intro c hc h1 h2; rw [e1] at h1; rw [e2] at h2; dtac)
      NPD_depart NPD_c1
      (fun l' r' h1 h2 => Or.inl (mid_emit hψ hψ2 κ σ l' r' (Or.inl ⟨rfl, hs0⟩) h1 h2))
  have hall := Reach.bind (Reach.bind (Reach.bind (Reach.bind hP1 (hP2 (ψ - 2) (Nat.le_refl _)))
    hP2l) (hP3 (ψ - 2) (Nat.le_refl _))) (fun C' h' => hW C' (by rw [Nat.sub_self] at h'; exact h'))
  exact hall.mono (by omega) (fun _ h => h)

theorem setup1 (hψ : ψ > 0) (hψ2 : 2 ≤ ψ) (κ : Nat) (ring : DirectedRing n) (hn : 1 < n)
    (hnψ : n = ψ) (γ : ProvColor) (C : Fin n → AuthState ψ)
    (h : Inv (fresh3 γ γ) C ψ (fun _ => ⟨γ, .depart, γ, none⟩)) :
    Reach hψ κ ring C (2 * ψ - 1) (fun C' => Inv (fresh3 γ γ) C' ψ
      (RD (K1 γ ψ) (fresh3 γ γ) 0 (ψ - 1) (some ⟨0, 0, ψ - 1, 2⟩))) := by
  have hn0 : 0 < n := by omega
  have hs0 : fresh3 γ γ ≠ γ := fresh3_ne_left γ γ
  generalize hσ : fresh3 γ γ = σ at h hs0 ⊢
  have cv : ∀ y, y < ψ → (cellAt hn0 y).val = y := fun y hy => cellAt_small hn0 (by omega)
  have rv : ∀ y, y + 1 < ψ → (ring.rightNeighbor (cellAt hn0 y)).val = y + 1 := by
    intro y hy; rw [rn_cellAt]; exact cellAt_small hn0 (by omega)
  have r0 : (ring.rightNeighbor (cellAt hn0 (ψ - 1))).val = 0 := by
    rw [rn_val, show ψ - 1 + 1 = ψ by omega, hnψ, Nat.mod_self]
  have e0 := cv (ψ - 1) (by omega)
  -- P1
  have hP1 : Reach hψ κ ring C 1 (fun C' => Inv σ C' ψ (DA1 σ γ ψ 0)) := by
    refine gen_step hψ κ ring hn σ ψ C (cellAt hn0 (ψ - 1)) _ (DA1 σ γ ψ 0) h
      (by omega) (by omega) (a := ψ - 1) (a' := 0) (γl := γ) (stl := .depart) (cml := γ)
      (tokl := none) (γr := γ) (str := .depart) (cmr := γ) (tokr := none) (stl' := .depart)
      (cml' := σ) (tokl' := none) (str' := .lock) (cmr' := σ) (tokr' := none)
      (by rw [e0]; exact Nat.mod_eq_of_lt (by omega)) (by rw [r0]; exact Nat.zero_mod ψ)
      (by rw [show ψ - 1 + 1 = ψ by omega, Nat.mod_self])
      rfl rfl (by rw [e0]; dtac) (by rw [r0]; dtac)
      (by intro c hc h1 h2; rw [e0] at h1; rw [r0] at h2; dtac)
      NPD_depart NPD_depart
      (fun l' r' h1 h2 => by
        have := mid_start hψ hψ2 κ σ γ γ l' r' h1 h2
        rw [hσ] at this
        exact Or.inl this)
  -- P2
  have hP2 : ∀ k, k ≤ ψ - 2 → ∀ C1 : Fin n → AuthState ψ, Inv σ C1 ψ (DA1 σ γ ψ 0) →
      Reach hψ κ ring C1 k (fun C' => Inv σ C' ψ (DA1 σ γ ψ k)) := by
    intro k
    induction k with
    | zero => intro _ C1 h1; exact Reach.pure hψ κ ring h1
    | succ k ih =>
      intro hk C1 h1
      refine Reach.bind (ih (by omega) C1 h1) (fun C2 h2 => ?_)
      clear ih
      have e1 := cv k (by omega)
      have e2 := rv k (by omega)
      refine gen_step hψ κ ring hn σ ψ C2 (cellAt hn0 k) (DA1 σ γ ψ k)
        (DA1 σ γ ψ (k + 1)) h2 (by omega) (by omega) (a := k) (a' := k + 1)
        (γl := γ) (stl := .lock) (cml := σ) (tokl := none) (γr := γ) (str := .depart)
        (cmr := γ) (tokr := none) (stl' := .lock) (cml' := σ) (tokl' := none) (str' := .lock)
        (cmr' := σ) (tokr' := none)
        (by rw [e1]; exact Nat.mod_eq_of_lt (by omega)) (by rw [e2]; exact Nat.mod_eq_of_lt (by omega))
        (Nat.mod_eq_of_lt (by omega)).symm
        (by rw [e1]; dtac) (by rw [e2]; dtac) (by rw [e1]; dtac) (by rw [e2]; dtac)
        (by intro c hc h1 h2; rw [e1] at h1; rw [e2] at h2; dtac)
        ⟨by decide, by decide⟩ NPD_depart
        (fun l' r' h1 h2 => Or.inl (mid_lockprop hψ κ σ l' r' (by omega) h1 h2))
  -- P2, last
  have hP2l : ∀ C1 : Fin n → AuthState ψ, Inv σ C1 ψ (DA1 σ γ ψ (ψ - 2)) →
      Reach hψ κ ring C1 1 (fun C' => Inv σ C' ψ (DB1 σ γ (ψ - 2))) := by
    intro C1 h1
    have e1 := cv (ψ - 2) (by omega)
    have e2 := rv (ψ - 2) (by omega)
    refine gen_step hψ κ ring hn σ ψ C1 (cellAt hn0 (ψ - 2)) (DA1 σ γ ψ (ψ - 2))
      (DB1 σ γ (ψ - 2)) h1 (by omega) (by omega) (a := ψ - 2) (a' := ψ - 2 + 1)
      (γl := γ) (stl := .lock) (cml := σ) (tokl := none) (γr := γ) (str := .depart)
      (cmr := σ) (tokr := none) (stl' := .compare1) (cml' := σ) (tokl' := none)
      (str' := .compare1) (cmr' := σ) (tokr' := none)
      (by rw [e1]; exact Nat.mod_eq_of_lt (by omega)) (by rw [e2]; exact Nat.mod_eq_of_lt (by omega))
      (Nat.mod_eq_of_lt (by omega)).symm
      (by rw [e1]; dtac) (by rw [e2]; dtac) (by rw [e1]; dtac) (by rw [e2]; dtac)
      (by intro c hc h1 h2; rw [e1] at h1; rw [e2] at h2; dtac)
      ⟨by decide, by decide⟩ NPD_depart
      (fun l' r' h1 h2 => mid_lockprop_last hψ κ σ l' r' (by omega) h1 h2)
  -- P3
  have hP3 : ∀ i, i ≤ ψ - 2 → ∀ C1 : Fin n → AuthState ψ, Inv σ C1 ψ (DB1 σ γ (ψ - 2)) →
      Reach hψ κ ring C1 i (fun C' => Inv σ C' ψ (DB1 σ γ (ψ - 2 - i))) := by
    intro i
    induction i with
    | zero => intro _ C1 h1; exact Reach.pure hψ κ ring h1
    | succ i ih =>
      intro hi C1 h1
      refine Reach.bind (ih (by omega) C1 h1) (fun C2 h2 => ?_)
      clear ih
      have hh : ψ - 2 - i = ψ - 2 - (i + 1) + 1 := by omega
      rw [hh] at h2
      generalize hH : ψ - 2 - (i + 1) = H at h2 ⊢
      have hH' : H + 1 < ψ - 1 := by omega
      have e1 := cv H (by omega)
      have e2 := rv H (by omega)
      refine gen_step hψ κ ring hn σ ψ C2 (cellAt hn0 H) (DB1 σ γ (H + 1))
        (DB1 σ γ H) h2 (by omega) (by omega) (a := H) (a' := H + 1)
        (γl := γ) (stl := .lock) (cml := σ) (tokl := none) (γr := γ) (str := .compare1)
        (cmr := σ) (tokr := none) (stl' := .compare1) (cml' := σ) (tokl' := none)
        (str' := .compare1) (cmr' := σ) (tokr' := none)
        (by rw [e1]; exact Nat.mod_eq_of_lt (by omega)) (by rw [e2]; exact Nat.mod_eq_of_lt (by omega))
        (Nat.mod_eq_of_lt (by omega)).symm
        (by rw [e1]; dtac) (by rw [e2]; dtac) (by rw [e1]; dtac) (by rw [e2]; dtac)
        (by intro c hc h1 h2; rw [e1] at h1; rw [e2] at h2; dtac)
        ⟨by decide, by decide⟩ NPD_c1
        (fun l' r' h1 h2 => Or.inl (mid_ack hψ κ σ l' r' hH' h1 h2))
  -- W0
  have hW : ∀ C1 : Fin n → AuthState ψ, Inv σ C1 ψ (DB1 σ γ 0) →
      Reach hψ κ ring C1 1 (fun C' => Inv σ C' ψ
        (RD (K1 γ ψ) σ 0 (ψ - 1) (some ⟨0, 0, ψ - 1, 2⟩))) := by
    intro C1 h1
    refine gen_step hψ κ ring hn σ ψ C1 (cellAt hn0 (ψ - 1)) (DB1 σ γ 0)
      _ h1 (by omega) (by omega) (a := ψ - 1) (a' := 0)
      (γl := γ) (stl := .compare1) (cml := σ) (tokl := none) (γr := γ) (str := .compare1)
      (cmr := σ) (tokr := none) (stl' := .compare2) (cml' := σ) (tokl' := some ⟨0, 0, ψ - 1, 2⟩)
      (str' := .compare1) (cmr' := σ) (tokr' := none)
      (by rw [e0]; exact Nat.mod_eq_of_lt (by omega)) (by rw [r0]; exact Nat.zero_mod ψ)
      (by rw [show ψ - 1 + 1 = ψ by omega, Nat.mod_self])
      (by rw [e0]; dtac) (by rw [r0]; dtac) (by rw [e0]; dtac) (by rw [r0]; dtac)
      (by intro c hc h1 h2; rw [e0] at h1; rw [r0] at h2; dtac)
      NPD_c1 NPD_c1
      (fun l' r' h1 h2 => Or.inl (mid_emit hψ hψ2 κ σ l' r' (Or.inr rfl) h1 h2))
  have hall := Reach.bind (Reach.bind (Reach.bind (Reach.bind hP1 (hP2 (ψ - 2) (Nat.le_refl _)))
    hP2l) (hP3 (ψ - 2) (Nat.le_refl _))) (fun C' h' => hW C' (by rw [Nat.sub_self] at h'; exact h'))
  exact hall.mono (by omega) (fun _ h => h)

end Setup

/-! ## Round kinds are admissible, and the headline -/

section Headline
variable {n ψ : Nat}

theorem AdmE_of (ring : DirectedRing n) (σ : ProvColor) (K : Nat → ProvColor × MainState)
    (N : Nat) (e : Fin n) (c c' a a' : Nat) (hc : e.val = c)
    (hc' : (ring.rightNeighbor e).val = c') (hN1 : c < N) (hN2 : c' < N)
    (ha : c % ψ = a) (ha' : c' % ψ = a') (hK1 : KR (K c).2) (hK2 : KR (K c').2)
    (hin : ∀ tl tr : Option Path2Info, (tl ≠ none ∨ tr ≠ none) →
      InertV (ψ := ψ) σ a (K c).1 (K c).2 σ tl a' (K c').1 (K c').2 σ tr) :
    AdmE (ψ := ψ) ring σ K N e := by
  unfold AdmE
  rw [hc, hc', ha, ha']
  exact ⟨hN1, hN2, hK1, hK2, hin⟩

theorem KR_dep : KR .depart := Or.inl rfl
theorem KR_c1 : KR .compare1 := Or.inr (Or.inl rfl)
theorem KR_c2 : KR .compare2 := Or.inr (Or.inr rfl)

theorem K2_S (γ0 γ1 : ProvColor) {c : Nat} (h : c < ψ - 1) : K2 γ0 γ1 ψ c = (γ0, .depart) := by
  simp only [K2, if_pos (show c < ψ by omega), if_neg (show c ≠ ψ - 1 by omega)]
theorem K2_E (γ0 γ1 : ProvColor) (hψ : 0 < ψ) : K2 γ0 γ1 ψ (ψ - 1) = (γ0, .compare2) := by
  simp [K2, show ψ - 1 < ψ by omega]
theorem K2_T (γ0 γ1 : ProvColor) {c : Nat} (h : ψ ≤ c) : K2 γ0 γ1 ψ c = (γ1, .compare1) := by
  simp only [K2, if_neg (show ¬ c < ψ by omega)]

theorem kinds2 (hψ2 : 2 ≤ ψ) (ring : DirectedRing n) (hn0 : 0 < n) (hd : ψ ∣ n) (h2 : 2 * ψ ≤ n)
    (γ0 γ1 : ProvColor) (hs0 : fresh3 γ0 γ1 ≠ γ0) :
    RoundKinds (ψ := ψ) ring hn0 (fresh3 γ0 γ1) (K2 γ0 γ1 ψ) (2 * ψ) true := by
  generalize fresh3 γ0 γ1 = σ at hs0 ⊢
  refine ⟨fun y hy => ?_, fun j hj => ?_, fun _ => ⟨h2, fun y hy => ?_⟩⟩
  · have hc : (cellAt hn0 y).val = y := cellAt_small hn0 (by omega)
    have hc' : (ring.rightNeighbor (cellAt hn0 y)).val = y + 1 := by
      rw [rn_cellAt]; exact cellAt_small hn0 (by omega)
    by_cases h1 : y + 1 < ψ - 1
    · refine AdmE_of ring σ _ _ _ y (y + 1) y (y + 1) hc hc' (by omega) (by omega)
        (Nat.mod_eq_of_lt (by omega)) (Nat.mod_eq_of_lt (by omega)) ?_ ?_ ?_
      · rw [K2_S γ0 γ1 (by omega)]; exact KR_dep
      · rw [K2_S γ0 γ1 (by omega)]; exact KR_dep
      · intro tl tr _
        rw [K2_S γ0 γ1 (show y < ψ - 1 by omega), K2_S γ0 γ1 h1]
        exact inertV_sd_sd σ γ0 γ0 y tl tr hs0 hs0
    by_cases h2' : y + 1 = ψ - 1
    · refine AdmE_of ring σ _ _ _ y (y + 1) y (y + 1) hc hc' (by omega) (by omega)
        (Nat.mod_eq_of_lt (by omega)) (Nat.mod_eq_of_lt (by omega)) ?_ ?_ ?_
      · rw [K2_S γ0 γ1 (by omega)]; exact KR_dep
      · rw [h2', K2_E γ0 γ1 (by omega)]; exact KR_c2
      · intro tl tr _
        rw [K2_S γ0 γ1 (show y < ψ - 1 by omega), h2', K2_E γ0 γ1 (by omega)]
        have := inertV_sd_c2 (ψ := ψ) σ γ0 γ0 y tl tr hs0
        rw [h2'] at this; exact this
    by_cases h3 : y = ψ - 1
    · refine AdmE_of ring σ _ _ _ y (y + 1) (ψ - 1) 0 hc hc' (by omega) (by omega)
        (by rw [h3]; exact Nat.mod_eq_of_lt (by omega))
        (by rw [h3, show ψ - 1 + 1 = ψ by omega, Nat.mod_self]) ?_ ?_ ?_
      · rw [h3, K2_E γ0 γ1 (by omega)]; exact KR_c2
      · rw [K2_T γ0 γ1 (by omega)]; exact KR_c1
      · intro tl tr ht
        rw [h3, K2_E γ0 γ1 (by omega), K2_T γ0 γ1 (by omega)]
        exact inertV_c2_c1 (by omega) σ γ0 γ1 tl tr ht
    · refine AdmE_of ring σ _ _ _ y (y + 1) (y - ψ) (y - ψ + 1) hc hc' (by omega) (by omega)
        ?_ ?_ ?_ ?_ ?_
      · rw [show y = ψ + (y - ψ) by omega, Nat.add_mod_left]
        rw [show ψ + (y - ψ) - ψ = y - ψ by omega]; exact Nat.mod_eq_of_lt (by omega)
      · rw [show y + 1 = ψ + (y - ψ + 1) by omega, Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      · rw [K2_T γ0 γ1 (by omega)]; exact KR_c1
      · rw [K2_T γ0 γ1 (by omega)]; exact KR_c1
      · intro tl tr _
        rw [K2_T γ0 γ1 (show ψ ≤ y by omega), K2_T γ0 γ1 (show ψ ≤ y + 1 by omega)]
        exact inertV_c1_c1 σ γ1 γ1 (y - ψ) tl tr (by omega) (by omega)
  · rw [Nat.mod_eq_of_lt (by omega), K2_T γ0 γ1 (by omega)]; rfl
  · rw [K2_S γ0 γ1 hy]; exact ⟨hs0.symm, rfl⟩

theorem K1_E (γ : ProvColor) : K1 γ ψ (ψ - 1) = (γ, .compare2) := by
  simp [K1]
theorem K1_O (γ : ProvColor) {c : Nat} (h : c ≠ ψ - 1) : K1 γ ψ c = (γ, .compare1) := by
  simp only [K1, if_neg h]

theorem kinds1 (hψ2 : 2 ≤ ψ) (ring : DirectedRing n) (hn0 : 0 < n) (hnψ : n = ψ)
    (γ : ProvColor) :
    RoundKinds (ψ := ψ) ring hn0 (fresh3 γ γ) (K1 γ ψ) ψ false := by
  generalize fresh3 γ γ = σ
  refine ⟨fun y hy => ?_, fun j hj => ?_, fun h => absurd h (by decide)⟩
  · have hc : (cellAt hn0 y).val = y % ψ := by rw [cellAt_val, hnψ]
    have hc' : (ring.rightNeighbor (cellAt hn0 y)).val = (y + 1) % ψ := by rw [rn_val, hnψ]
    have hlt : y % ψ < ψ := Nat.mod_lt _ (by omega)
    have hlt' : (y + 1) % ψ < ψ := Nat.mod_lt _ (by omega)
    have hsucc : (y + 1) % ψ = (y % ψ + 1) % ψ := by rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < ψ by omega)]
    by_cases h1 : y % ψ = ψ - 1
    · have h0 : (y + 1) % ψ = 0 := by rw [hsucc, h1, show ψ - 1 + 1 = ψ by omega, Nat.mod_self]
      refine AdmE_of ring σ _ _ _ (y % ψ) ((y + 1) % ψ) (ψ - 1) 0 hc hc' hlt hlt'
        (by rw [Nat.mod_mod, h1]) (by rw [Nat.mod_mod, h0]) ?_ ?_ ?_
      · rw [h1, K1_E]; exact KR_c2
      · rw [h0, K1_O γ (by omega)]; exact KR_c1
      · intro tl tr ht
        rw [h1, h0, K1_E, K1_O γ (show 0 ≠ ψ - 1 by omega)]
        exact inertV_c2_c1 (by omega) σ γ γ tl tr ht
    · have hs : (y + 1) % ψ = y % ψ + 1 := by rw [hsucc]; exact Nat.mod_eq_of_lt (by omega)
      refine AdmE_of ring σ _ _ _ (y % ψ) ((y + 1) % ψ) (y % ψ) (y % ψ + 1) hc hc' hlt hlt'
        (Nat.mod_mod _ _) (by rw [Nat.mod_mod, hs]) ?_ ?_ ?_
      · rw [K1_O γ h1]; exact KR_c1
      · by_cases h2 : (y + 1) % ψ = ψ - 1
        · rw [h2, K1_E]; exact KR_c2
        · rw [K1_O γ h2]; exact KR_c1
      · intro tl tr _
        rw [K1_O γ h1]
        by_cases h2 : (y + 1) % ψ = ψ - 1
        · rw [h2, K1_E]
          exact inertV_c1_c2 (ψ := ψ) σ γ γ (y % ψ) tl tr h1
        · rw [K1_O γ h2]
          exact inertV_c1_c1 σ γ γ (y % ψ) tl tr h1 hlt
  · simp only [K1]; split <;> rfl

/-! ### Serial blocks (Q20610 §1) -/

/-- A serial cell at physical role `j` of a block of colour `γ` with `p`/`p_carry`
arbitrary: label `j`, main path `some j b`, `depart`, no BEQ token, `path_mark = ctrl_mark = γ`,
no `-1` command in `path4`/`path5`. -/
def SerialPlusCell (u : AuthState ψ) (j : Nat) (γ : ProvColor) : Prop :=
  u.core.label.val = j ∧ (∃ b, u.core.path = .some j b) ∧ u.core.state = .depart ∧
    u.core.path2 = none ∧ u.path_mark = γ ∧ u.ctrl_mark = γ ∧
    isCmd u.core.path4 = false ∧ isCmd u.core.path5 = false

/-- The serial cell of Q20610 §1 exactly: in addition `p = p_carry = false`. -/
def SerialCell (u : AuthState ψ) (j : Nat) (γ : ProvColor) : Prop :=
  SerialPlusCell u j γ ∧ u.core.p = false ∧ u.core.p_carry = false

/-- Every block `g` (cells `gψ .. gψ+ψ-1`) is SerialPlus with one colour `Γ g`. -/
def SerialPlus (C : Fin n → AuthState ψ) : Prop :=
  ∃ Γ : Nat → ProvColor, ∀ i : Fin n, SerialPlusCell (C i) (i.val % ψ) (Γ (i.val / ψ))

/-- Every block is serial (Q20610 §1). -/
def Serial (C : Fin n → AuthState ψ) : Prop :=
  ∃ Γ : Nat → ProvColor, ∀ i : Fin n, SerialCell (C i) (i.val % ψ) (Γ (i.val / ψ))

theorem Serial.plus {C : Fin n → AuthState ψ} (h : Serial C) : SerialPlus C := by
  obtain ⟨Γ, hΓ⟩ := h
  exact ⟨Γ, fun i => (hΓ i).1⟩

theorem cell_of_serial (σ : ProvColor) (u : AuthState ψ) (j : Nat) (γ : ProvColor)
    (h : SerialPlusCell u j γ) (hL : u.core.leader = false) (hR : u.core.reset_cmd = false) :
    Cell σ u j γ .depart γ none := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := h
  exact ⟨⟨h1, h2, h5, h3, h6, h4, fun h => absurd rfl h⟩, hL, hR⟩

/-- SERIAL-DISCHARGE (Q20610 §1), for SerialPlus blocks (`p`, `p_carry`, `echo` arbitrary):
from a leaderless, perfectly labelled, reset-free ring whose blocks are all SerialPlus, some
physical word of length at most `2ψ² + 2ψ - 1` ends in a leader or a deleted main path. -/
theorem serialPlus_discharge (hψ : ψ > 0) (hψ2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AuthState ψ)
    (hLF : ∀ i, (C i).core.leader = false) (hPL : PPLLAuthBitFrozen.PL C)
    (hR : ∀ i, (C i).core.reset_cmd = false) (hS : SerialPlus C) :
    ∃ w : List (Fin n), w.length ≤ 2 * ψ * ψ + 2 * ψ - 1 ∧
      ((∃ i, (authRun hψ κ authFplusmcc ring C w i).core.leader = true) ∨
        (∃ i, (authRun hψ κ authFplusmcc ring C w i).core.path = .bot)) := by
  have hn0 : 0 < n := by omega
  obtain ⟨Γ, hΓ⟩ := hS
  have arith : (2 * ψ - 1) + ((ψ - 1 + 1) * (2 * ψ - 1) + (ψ - 1)) + 1 = 2 * ψ * ψ + 2 * ψ - 1 := by
    rw [show ψ - 1 + 1 = ψ by omega, Nat.mul_sub_one, show ψ * (2 * ψ) = 2 * ψ * ψ by
      rw [Nat.mul_comm, Nat.mul_assoc]]
    have : ψ ≤ 2 * ψ * ψ := by
      calc ψ = 1 * ψ := (Nat.one_mul ψ).symm
        _ ≤ 2 * ψ * ψ := Nat.mul_le_mul_right ψ (by omega)
    omega
  have fin : ∀ {L : Nat}, L + 1 ≤ 2 * ψ * ψ + 2 * ψ - 1 →
      Reach hψ κ ring C L (fun _ => False) →
      ∃ w : List (Fin n), w.length ≤ 2 * ψ * ψ + 2 * ψ - 1 ∧
        ((∃ i, (authRun hψ κ authFplusmcc ring C w i).core.leader = true) ∨
          (∃ i, (authRun hψ κ authFplusmcc ring C w i).core.path = .bot)) := by
    intro L hL h
    obtain ⟨w, hw, i, hi⟩ := Reach.final hψ κ ring hn h
    refine ⟨w, by omega, ?_⟩
    rcases hi with hi | hi
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨i, hi⟩
  obtain ⟨m, hm⟩ := hd
  by_cases hm1 : m = 1
  · -- one block
    subst hm1
    have hnψ : n = ψ := by rw [hm, Nat.mul_one]
    have h0 : Inv (fresh3 (Γ 0) (Γ 0)) C ψ (fun _ => ⟨Γ 0, .depart, Γ 0, none⟩) := by
      intro c hc
      have := hΓ c
      rw [Nat.div_eq_of_lt hc] at this
      exact cell_of_serial _ _ _ _ this (hLF c) (hR c)
    have hs := setup1 hψ hψ2 κ ring hn hnψ (Γ 0) C h0
    have hr := Reach.bind hs (fun C' h' => by
      have h'' : Inv (fresh3 (Γ 0) (Γ 0)) C' ψ (RD (K1 (Γ 0) ψ) (fresh3 (Γ 0) (Γ 0))
          (U0 false 0 (0 + ψ - 1)) ((0 + ψ - 1) % n) (some ⟨0, 0, ψ - 1, 2⟩)) := by
        rw [show U0 false 0 (0 + ψ - 1) = 0 from rfl, show 0 + ψ - 1 = ψ - 1 by omega,
          Nat.mod_eq_of_lt (by omega)]
        exact h'
      exact rounds hψ hψ2 κ ring hn ⟨1, hm⟩ (fresh3 (Γ 0) (Γ 0)) (K1 (Γ 0) ψ) ψ false
        (kinds1 hψ2 ring hn0 hnψ (Γ 0)) (ψ - 1) 0 C' (by omega) h'')
    exact fin (Nat.le_of_eq arith) hr
  · -- two or more blocks: the first two
    have h2 : 2 * ψ ≤ n := by
      rw [hm]
      have : 2 ≤ m := by
        rcases m with _ | _ | m
        · rw [Nat.mul_zero] at hm; omega
        · exact absurd rfl hm1
        · omega
      rw [Nat.mul_comm 2 ψ]; exact Nat.mul_le_mul_left ψ this
    have h0 : Inv (fresh3 (Γ 0) (Γ 1)) C (2 * ψ) (DI (Γ 0) (Γ 1) ψ) := by
      intro c hc
      have := hΓ c
      have hcell := cell_of_serial (fresh3 (Γ 0) (Γ 1)) _ _ _ this (hLF c) (hR c)
      by_cases hlt : c.val < ψ
      · rw [Nat.div_eq_of_lt hlt] at hcell
        simp only [DI, if_pos hlt]; exact hcell
      · have hq : c.val / ψ = 1 := by
          exact Nat.div_eq_of_lt_le (by omega) (by omega)
        rw [hq] at hcell
        simp only [DI, if_neg hlt]; exact hcell
    have hs := setup2 hψ hψ2 κ ring hn ⟨m, hm⟩ h2 (Γ 0) (Γ 1) C h0
    have hr := Reach.bind hs (fun C' h' => by
      have h'' : Inv (fresh3 (Γ 0) (Γ 1)) C' (2 * ψ) (RD (K2 (Γ 0) (Γ 1) ψ) (fresh3 (Γ 0) (Γ 1))
          (U0 true 0 (0 + ψ - 1)) ((0 + ψ - 1) % n) (some ⟨0, 0, ψ - 1, 2⟩)) := by
        rw [show U0 true 0 (0 + ψ - 1) = 0 + ψ - 1 from rfl, show 0 + ψ - 1 = ψ - 1 by omega,
          Nat.mod_eq_of_lt (by omega)]
        exact h'
      exact rounds hψ hψ2 κ ring hn ⟨m, hm⟩ (fresh3 (Γ 0) (Γ 1)) (K2 (Γ 0) (Γ 1) ψ) (2 * ψ) true
        (kinds2 hψ2 ring hn0 ⟨m, hm⟩ h2 (Γ 0) (Γ 1) (fresh3_ne_left _ _)) (ψ - 1) 0 C'
        (by omega) h'')
    exact fin (Nat.le_of_eq arith) hr

/-- SERIAL-DISCHARGE for the exact serial blocks of Q20610 §1. -/
theorem serial_discharge (hψ : ψ > 0) (hψ2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AuthState ψ)
    (hLF : ∀ i, (C i).core.leader = false) (hPL : PPLLAuthBitFrozen.PL C)
    (hR : ∀ i, (C i).core.reset_cmd = false) (hS : Serial C) :
    ∃ w : List (Fin n), w.length ≤ 2 * ψ * ψ + 2 * ψ - 1 ∧
      ((∃ i, (authRun hψ κ authFplusmcc ring C w i).core.leader = true) ∨
        (∃ i, (authRun hψ κ authFplusmcc ring C w i).core.path = .bot)) :=
  serialPlus_discharge hψ hψ2 hd hn κ ring C hLF hPL hR hS.plus

end Headline

end PPLLAuthSerialDischarge
