import Leader.Wu.Authorization.WriterReach
/-! Z-div stages 1 and 2 composed.

* `reset_free_step`: a step whose initiator is a follower keeps `reset_cmd = false`
  everywhere; with `echo = false` everywhere as well it keeps both
  (`reset_echo_free_step`). The only reset source in the AuthF pipeline is the
  leader-gated `suppressSigStart`, and the only echo source without a reset is the
  echo walk, which needs an echo on the responder (`pipeline_echo_free`).
* `pl_step`: perfect labels survive every step with leaderless inputs and outputs
  (`ψ ∣ n`, `1 < n`); no `LBF` hypothesis.
* `stage12` (headline): from any configuration with perfect labels (leaders allowed),
  the word `w₁ ++ W_wr` (stage-1 drain word, then the writer word) either has a prefix
  with a leader, or ends leaderless, reset-free, in `LBF`, with perfect labels.
* `checkpoint_step`: `Checkpoint = leaderless ∧ reset_cmd = echo = false ∧ LBF ∧ PL` is
  closed under every step with leaderless output; `stage2_checkpoint` reaches a
  `Checkpoint` (or a leader prefix) from a leaderless, reset/echo-free, labelled ring.
* `echo_persists` (obstruction): in a leaderless reset-free ring, an echo can never
  disappear along a leaderless run (the echo walk moves it to the initiator, and only a
  reset or a leader consumes it). Stage 1 (`exists_reset_free_or_positive`) states only
  `reset_cmd = false` at its endpoint, so `stage12` cannot promise `echo = false`:
  from a leaderless, reset-free, perfectly labelled ring with one echo, reaching a
  `Checkpoint` requires producing a leader first.
-/

namespace PPLLAuthStage12
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
  PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF PPLLAuthResetDrain
  PPLLAuthWriterFrame PPLLAuthBitFrozen PPLLAuthWriterReach
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ### Algorithm 14 on reset-free follower pairs -/

section Pair
variable {ψ : Nat}

theorem suppress_echo_free (hp : ψ > 0) (x y : AgentState ψ) (hx : x.leader = false)
    (ha : x.reset_cmd = false) (hb : y.reset_cmd = false)
    (hea : x.echo = false) (heb : y.echo = false) :
    (suppressSigResetKill hp x y).1.echo = false ∧ (suppressSigResetKill hp x y).2.echo = false := by
  simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset, suppressSigTerminal,
    suppressSigEcho, suppressSigFinish, hx, ha, hb, hea, heb]

theorem suppress_echo_keep (hp : ψ > 0) (x y : AgentState ψ) (hx : x.leader = false)
    (ha : x.reset_cmd = false) (hb : y.reset_cmd = false)
    (he : (x.echo || y.echo) = true) :
    (suppressSigResetKill hp x y).1.echo = true := by
  cases hxe : x.echo <;> cases hye : y.echo <;> rw [hxe, hye] at he <;>
    simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset, suppressSigTerminal,
      suppressSigEcho, suppressSigFinish, hx, ha, hb, hxe, hye] at he ⊢

/-- On a reset-free, echo-free pair with a follower initiator, the AuthF interaction
writes no echo. -/
theorem pipeline_echo_free (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (ha : l.core.reset_cmd = false) (hb : r.core.reset_cmd = false)
    (hea : l.core.echo = false) (heb : r.core.echo = false) :
    (PPLLAuthF.pipeline hp κ c l r).1.core.echo = false ∧
    (PPLLAuthF.pipeline hp κ c l r).2.core.echo = false := by
  have hpf := prefix_facts hp κ c l r
  dsimp only at hpf
  obtain ⟨b1, b2, b3, b4, b5, -, -⟩ := hpf
  have hc := pipeline_core hp κ c l r
  have hsx := PPLLAstraReadyResetDebtR.Writer.suffix_fields hp l.core r.core
    ((PPLLAuthF.beforeElimination hp κ c l r).1.core, (PPLLAuthF.beforeElimination hp κ c l r).2.core)
  dsimp only at hsx
  rw [hc.1, hc.2, hsx.2.1, hsx.2.2.2, beforeElimination_eq, (suppress_core hp _ _).1,
    (suppress_core hp _ _).2]
  exact suppress_echo_free hp _ _ (b5.trans hl) (b1.trans ha) (b3.trans hb) (b2.trans hea)
    (b4.trans heb)

/-- On a reset-free pair with a follower initiator, an echo on either endpoint leaves
an echo on the initiator. -/
theorem pipeline_echo_keep (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (hl : l.core.leader = false) (ha : l.core.reset_cmd = false) (hb : r.core.reset_cmd = false)
    (he : (l.core.echo || r.core.echo) = true) :
    (PPLLAuthF.pipeline hp κ c l r).1.core.echo = true := by
  have hpf := prefix_facts hp κ c l r
  dsimp only at hpf
  obtain ⟨b1, b2, b3, b4, b5, -, -⟩ := hpf
  have hc := pipeline_core hp κ c l r
  have hsx := PPLLAstraReadyResetDebtR.Writer.suffix_fields hp l.core r.core
    ((PPLLAuthF.beforeElimination hp κ c l r).1.core, (PPLLAuthF.beforeElimination hp κ c l r).2.core)
  dsimp only at hsx
  rw [hc.1, hsx.2.1, beforeElimination_eq, (suppress_core hp _ _).1]
  apply suppress_echo_keep hp _ _ (b5.trans hl) (b1.trans ha) (b3.trans hb)
  rw [b2, b4]; exact he

end Pair

/-! ### Configuration level -/

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

/-- Leaderless configuration. -/
def LL (C : Fin n → AuthState ψ) : Prop := ∀ i, (C i).core.leader = false
/-- No `reset_cmd` anywhere. -/
def RF (C : Fin n → AuthState ψ) : Prop := ∀ i, (C i).core.reset_cmd = false
/-- No `echo` anywhere. -/
def EF (C : Fin n → AuthState ψ) : Prop := ∀ i, (C i).core.echo = false

/-- **Reset-freeness is closed under follower-initiated steps.** Only the initiator
must be a follower; the output may contain a leader. -/
theorem reset_free_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (hn : 1 < n) (C : Fin n → AuthState ψ) (e : Fin n) (hl : (C e).core.leader = false)
    (hR : RF C) : RF (S hp κ c ring C e) := by
  intro i
  have hr := pipeline_follower_reset hp κ c (C e) (C (ring.rightNeighbor e)) hl
  by_cases h1 : i = e
  · subst i; rw [step_left]; exact hr.1
  · by_cases h2 : i = ring.rightNeighbor e
    · subst i; rw [step_right hp κ c ring hn, hr.2, hR e, hR _]; rfl
    · rw [step_other hp κ c ring C e i h1 h2]; exact hR i

/-- **Reset- and echo-freeness together are closed under follower-initiated steps.** -/
theorem reset_echo_free_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (hn : 1 < n) (C : Fin n → AuthState ψ) (e : Fin n) (hl : (C e).core.leader = false)
    (hR : RF C) (hE : EF C) : RF (S hp κ c ring C e) ∧ EF (S hp κ c ring C e) := by
  refine ⟨reset_free_step hp κ c ring hn C e hl hR, fun i => ?_⟩
  have he := pipeline_echo_free hp κ c (C e) (C (ring.rightNeighbor e)) hl (hR e) (hR _)
    (hE e) (hE _)
  by_cases h1 : i = e
  · subst i; rw [step_left]; exact he.1
  · by_cases h2 : i = ring.rightNeighbor e
    · subst i; rw [step_right hp κ c ring hn]; exact he.2
    · rw [step_other hp κ c ring C e i h1 h2]; exact hE i

/-- **Perfect labels survive every leaderless step** (no `LBF` needed). -/
theorem pl_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (hd : ψ ∣ n) (hn : 1 < n) (C : Fin n → AuthState ψ) (hC : LL C) (hpl : PL C) (e : Fin n)
    (hout : LL (S hp κ c ring C e)) : PL (S hp κ c ring C e) :=
  (step_pair hp κ c ring hd hn C ⟨hC, hpl⟩ e hout).1.2

/-- An echo survives any follower-initiated step on a reset-free ring. -/
theorem echo_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (hn : 1 < n) (C : Fin n → AuthState ψ) (e : Fin n) (hl : (C e).core.leader = false)
    (hR : RF C) (j : Fin n) (hj : (C j).core.echo = true) :
    ∃ j', (S hp κ c ring C e j').core.echo = true := by
  by_cases h1 : j = e
  · subst j
    refine ⟨e, ?_⟩
    rw [step_left]
    exact pipeline_echo_keep hp κ c _ _ hl (hR _) (hR _) (by rw [hj]; rfl)
  · by_cases h2 : j = ring.rightNeighbor e
    · subst j
      refine ⟨e, ?_⟩
      rw [step_left]
      exact pipeline_echo_keep hp κ c _ _ hl (hR _) (hR _) (by rw [hj]; cases (C e).core.echo <;> rfl)
    · exact ⟨j, by rw [step_other hp κ c ring C e j h1 h2]; exact hj⟩

/-- An invariant closed under leaderless steps holds at the end of a leaderless run. -/
theorem run_inv (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (I : (Fin n → AuthState ψ) → Prop)
    (hI : ∀ (C : Fin n → AuthState ψ) (e : Fin n), LL C → I C → LL (S hp κ c ring C e) →
      I (S hp κ c ring C e)) :
    ∀ (w : List (Fin n)) (C : Fin n → AuthState ψ), LL C → I C → LLRun hp κ c ring C w →
      LL (authRun hp κ c ring C w) ∧ I (authRun hp κ c ring C w) := by
  intro w
  induction w with
  | nil => intro C h1 h2 _; exact ⟨h1, h2⟩
  | cons e es ih =>
    intro C h1 h2 hL
    exact ih _ hL.1 (hI C e h1 h2 hL.1) hL.2

/-- **Obstruction.** On a leaderless reset-free ring carrying an echo, every leaderless
run ends with an echo somewhere. -/
theorem echo_persists (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (hn : 1 < n) (w : List (Fin n)) (C : Fin n → AuthState ψ) (hC : LL C) (hR : RF C)
    (hE : ∃ j, (C j).core.echo = true) (hL : LLRun hp κ c ring C w) :
    ∃ j, (authRun hp κ c ring C w j).core.echo = true :=
  (run_inv hp κ c ring (fun D => RF D ∧ ∃ j, (D j).core.echo = true)
    (fun D e hD ⟨hRD, j, hj⟩ _ =>
      ⟨reset_free_step hp κ c ring hn D e (hD e) hRD, echo_step hp κ c ring hn D e (hD e) hRD j hj⟩)
    w C hC ⟨hR, hE⟩ hL).2.2

/-- Boolean leaderlessness test. -/
def lfB (C : Fin n → AuthState ψ) : Bool :=
  (List.range n).all (fun k => if h : k < n then !(C ⟨k, h⟩).core.leader else true)

theorem lfB_true (C : Fin n → AuthState ψ) (h : lfB C = true) : LL C := by
  intro i
  have := List.all_eq_true.1 h i.val (List.mem_range.2 i.isLt)
  rw [dif_pos i.isLt] at this
  cases hx : (C i).core.leader
  · rfl
  · rw [hx] at this; cases this

theorem lfB_false (C : Fin n → AuthState ψ) (h : lfB C = false) :
    ∃ i, (C i).core.leader = true := by
  obtain ⟨k, hk, hpk⟩ := all_false _ _ h
  have hkn := List.mem_range.1 hk
  rw [dif_pos hkn] at hpk
  refine ⟨⟨k, hkn⟩, ?_⟩
  cases hx : (C ⟨k, hkn⟩).core.leader
  · rw [hx] at hpk; cases hpk
  · rfl

/-- The target of the composed stages. -/
def Checkpoint (C : Fin n → AuthState ψ) : Prop := LL C ∧ RF C ∧ EF C ∧ LBF C ∧ PL C

/-- **Invariance under continuation.** Every step from a `Checkpoint` whose output is
leaderless lands in a `Checkpoint`. -/
theorem checkpoint_step (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) (C : Fin n → AuthState ψ) (hK : Checkpoint C)
    (e : Fin n) (hout : LL (S hp κ c ring C e)) : Checkpoint (S hp κ c ring C e) := by
  obtain ⟨hC, hR, hE, hB, hP⟩ := hK
  obtain ⟨-, hP', hB'⟩ := step_closed hp κ c ring h2 hd hn C hC hP hB e hout
  obtain ⟨hR', hE'⟩ := reset_echo_free_step hp κ c ring hn C e (hC e) hR hE
  exact ⟨hout, hR', hE', hB', hP'⟩

/-- A `Checkpoint` persists along any leaderless run. -/
theorem checkpoint_run (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) (w : List (Fin n)) (C : Fin n → AuthState ψ)
    (hK : Checkpoint C) (hL : LLRun hp κ c ring C w) : Checkpoint (authRun hp κ c ring C w) :=
  (run_inv hp κ c ring Checkpoint
    (fun D e _ hD hout => checkpoint_step hp κ c ring h2 hd hn D hD e hout) w C hK.1 hK hL).2

private theorem take_app (w1 w2 : List (Fin n)) (k : Nat) :
    (w1 ++ w2).take (w1.length + k) = w1 ++ w2.take k := by
  induction w1 with
  | nil => simp
  | cons a as ih => simp [Nat.succ_add]; exact ih

/-- **Stage 2 with reset/echo carried.** From a leaderless, reset- and echo-free ring with
perfect labels, `W_wr` either produces a leader after some prefix or ends in a
`Checkpoint`. -/
theorem stage2_checkpoint (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) (C : Fin n → AuthState ψ)
    (hC : LL C) (hR : RF C) (hE : EF C) (hpl : PL C) :
    (∃ k, k ≤ (wWr ring ψ (n / ψ)).length ∧
      ∃ i, (authRun hp κ c ring C ((wWr ring ψ (n / ψ)).take k) i).core.leader = true) ∨
    Checkpoint (authRun hp κ c ring C (wWr ring ψ (n / ψ))) := by
  have hmn : n = n / ψ * ψ := (Nat.div_mul_cancel hd).symm
  cases h : llB hp κ c ring C (wWr ring ψ (n / ψ))
  · exact Or.inl (llB_false hp κ c ring _ C h)
  · have hL := llB_true hp κ c ring _ C h
    have hW := reach_of_LLRun hp κ c ring h2 hd hn hmn C ⟨hC, hpl⟩ hL
    have hI := run_inv hp κ c ring (fun D => RF D ∧ EF D)
      (fun D e hD ⟨a, b⟩ _ => reset_echo_free_step hp κ c ring hn D e (hD e) a b)
      _ C hC ⟨hR, hE⟩ hL
    exact Or.inr ⟨hI.1, hI.2.1, hI.2.2, hW.1, hW.2⟩

/-- **Stages 1 and 2 composed (headline).** For `2 ≤ ψ`, `ψ ∣ n`, `1 < n` and a
configuration with perfect labels (leaders allowed), some word — the stage-1 drain word
followed by `W_wr` — either has a prefix after which some cell is a leader, or ends
leaderless, reset-free, in `LBF`, with perfect labels. Holds for every `κ` and `Cfg`.
`echo = false` is not claimed; see `echo_persists`. -/
theorem stage12 (hp : ψ > 0) (κ : Nat) (c : PPLLAuthF.Cfg) (ring : DirectedRing n)
    (h2 : 2 ≤ ψ) (hd : ψ ∣ n) (hn : 1 < n) (C : Fin n → AuthState ψ) (hpl : PL C) :
    ∃ w : List (Fin n),
      (∃ k, k ≤ w.length ∧ ∃ i, (authRun hp κ c ring C (w.take k) i).core.leader = true) ∨
      (LL (authRun hp κ c ring C w) ∧ RF (authRun hp κ c ring C w) ∧
        LBF (authRun hp κ c ring C w) ∧ PL (authRun hp κ c ring C w)) := by
  have hmn : n = n / ψ * ψ := (Nat.div_mul_cancel hd).symm
  -- a leader at the start is the empty prefix
  cases h0 : lfB C
  · exact ⟨[], Or.inl ⟨0, Nat.le_refl _, lfB_false C h0⟩⟩
  have hC := lfB_true C h0
  obtain ⟨w1, h1⟩ := exists_reset_free_or_positive hp κ c ring hn C
  -- a leader during stage 1
  cases hb1 : llB hp κ c ring C w1
  · obtain ⟨k, hk, hlead⟩ := llB_false hp κ c ring w1 C hb1
    exact ⟨w1, Or.inl ⟨k, hk, hlead⟩⟩
  have hL1 := llB_true hp κ c ring w1 C hb1
  have hS1 := run_inv hp κ c ring PL
    (fun D e hD hP hout => pl_step hp κ c ring hd hn D hD hP e hout) w1 C hC hpl hL1
  generalize hD1 : authRun hp κ c ring C w1 = D1 at h1 hS1
  obtain ⟨hLD, hPD⟩ := hS1
  have hRD : RF D1 := by
    rcases h1 with ⟨i, hi⟩ | h1
    · rw [hLD i] at hi; cases hi
    · exact h1
  let w2 := wWr ring ψ (n / ψ)
  refine ⟨w1 ++ w2, ?_⟩
  cases hb2 : llB hp κ c ring D1 w2
  · obtain ⟨k, hk, i, hi⟩ := llB_false hp κ c ring w2 D1 hb2
    refine Or.inl ⟨w1.length + k, by rw [List.length_append]; omega, i, ?_⟩
    rw [take_app, authRun_append, hD1]; exact hi
  · have hL2 := llB_true hp κ c ring w2 D1 hb2
    have hW := reach_of_LLRun hp κ c ring h2 hd hn hmn D1 ⟨hLD, hPD⟩ hL2
    have hI := run_inv hp κ c ring RF
      (fun D e hD hR _ => reset_free_step hp κ c ring hn D e (hD e) hR) w2 D1 hLD hRD hL2
    rw [authRun_append, hD1]
    exact Or.inr ⟨hI.1, hI.2, hW.1, hW.2⟩

#print axioms pipeline_echo_free
#print axioms pipeline_echo_keep
#print axioms reset_free_step
#print axioms reset_echo_free_step
#print axioms pl_step
#print axioms echo_persists
#print axioms checkpoint_step
#print axioms checkpoint_run
#print axioms stage2_checkpoint
#print axioms stage12
end Ring
end PPLLAuthStage12
