import Leader.PPL.PsiAtLeastN.SmallNReach
import Leader.PPL.MainTheorem.GeneralExhaustive

/-!
# Theorem 1 on `n ≤ psi` with the safe target, and the whole-window paper form

This file proves `Theorem1PsiAtLeastNStatement s` for every `s` and hence
`Theorem1PaperFormSafeTarget s` (paper Theorem 1 on the whole window
`log n ≤ psi ≤ log n + s`, with the safe target of `SafeTarget.lean`).

Route.

* **whp** (`theorem1SafeWhp_proved`): the five-event splice of the
  `psi < n` proof, with the L18 event replaced by the safe L18 event
  (`SafeRows.lean` … `SafeSplice.lean`).  It holds on all of `n ≤ psi`
  (every `n ≥ 3`), with the constant 64.
* **pointwise reachability** (`theorem1PossibleSafe`): from every
  configuration some word visits the safe target.  For `n ≤ 64` a
  deterministic schedule (`SmallNReach.lean`); for `n ≥ 65` the whp bound
  leaves fewer than `n ^ H` failing words, so some word succeeds.
* **cost**: pointwise reachability plus the exhaustive configuration list
  give one producer length `L` per pair `(n, psi)`; the producer gives a
  half-failure block (`boundedSafeProducer_explicitOneOverNPhase`) and the
  closed target turns it into the expected-cost bound
  (`cost_le_two_blocks`).  This is the tiny-`n` cost argument of
  `Theorem1CostTiny.lean`, with `Theorem1SafeTarget` in place of `S_PL`.
* **finiteness in `s`**: `n ≤ psi ≤ log2 n + s` forces `n ≤ 2 s` and
  `psi ≤ 3 s` (`2 log2 n ≤ n`), so the domain of
  `Theorem1PsiAtLeastNStatement s` is finite and the per-pair constants have
  a maximum.  The constant `cExpected` depends on `s`; the statement allows
  this (it is quantified inside `s`).

P_PL
Theorem 1 cleanup, phase 2, step 6e: `theorem1ReachesSafeTarget_endpoint_prefix`
and `theorem1PossibleSafeUniformBound_of_exhaustive` are the safe-target
cases of `Leader/PPL/MainTheorem/GeneralExhaustive.lean` (statements unchanged).
-/

namespace PPL.PsiAtLeastN

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail
open PPLLResearchFormulation
open PPLLTraceConvergence
open PPLLSchedulerBlocks
open PPLLClosedDomainSchedulerAmplificationSol

/-! ## whp on `n ≤ psi` -/

/-- **Safe whp on `n ≤ psi`.**  For `3 ≤ n ≤ psi` (and `n ≤ 2 ^ psi`), at
most a `64 / n` fraction of the `theorem1Horizon n psi`-letter words never
visit `Theorem1SafeTarget`. -/
theorem theorem1SafeWhp_proved
    {n psi : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi) (hnpow : n ≤ 2 ^ psi) (hge : n ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    n * theorem1SafeFailureNumerator ring C0 (theorem1Horizon n psi) ≤
      64 * n ^ theorem1Horizon n psi :=
  theorem1SafeWhp_of_splice
    theorem1SafeFiveEventSplice_proved
    theorem1L16PaddedBound_proved
    theorem1L5iPaddedBound_proved
    theorem1L5iiDynamicPaddedBound_proved
    theorem1L17DynamicPaddedBound_proved
    theorem1L18SafeDynamicPaddedBound_proved
    hn3 hpsi hnpow hge ring C0

/-! ## Pointwise reachability on `n ≤ psi` -/

/-- A failure count below the number of words leaves a successful word. -/
theorem exists_reachesSafe_of_failure_lt
    {n psi kappa : Nat} (ring : DirectedRing n) (C : Config n psi kappa)
    (T : Nat)
    (h : theorem1SafeFailureNumerator ring C T < n ^ T) :
    ∃ word : DetSchedule n, theorem1ReachesSafeTarget ring C word = true := by
  classical
  refine Classical.byContradiction fun hno => ?_
  have hall :
      ∀ w ∈ allSchedules n T, (!(theorem1ReachesSafeTarget ring C w)) = true := by
    intro w _
    cases hw : theorem1ReachesSafeTarget ring C w with
    | false => rfl
    | true => exact absurd ⟨w, hw⟩ hno
  have heq :
      theorem1SafeFailureNumerator ring C T = (allSchedules n T).length := by
    unfold theorem1SafeFailureNumerator
    exact List.countP_eq_length.mpr hall
  rw [heq, allSchedules_length] at h
  exact Nat.lt_irrefl _ h

/-- **Possible convergence to the safe target on `3 ≤ n ≤ psi`.**  From
every configuration some word visits `Theorem1SafeTarget`: deterministically
for `n ≤ 64` (`theorem1PossibleSafe_smallN`), and from the whp bound for
`n ≥ 65` (`64 n^H < n · n^H`). -/
theorem theorem1PossibleSafe
    {n psi : Nat}
    (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi) (hge : n ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    ∃ word : DetSchedule n,
      theorem1ReachesSafeTarget ring C0 word = true := by
  by_cases hn64 : n ≤ 64
  · exact theorem1PossibleSafe_smallN hn3 hn64 hpsi hge ring C0
  · have hnpow : n ≤ 2 ^ psi :=
      Nat.le_trans hge (Nat.le_of_lt (lt_two_pow_self' psi))
    have hwhp := theorem1SafeWhp_proved hn3 hpsi hnpow hge ring C0
    apply exists_reachesSafe_of_failure_lt ring C0 (theorem1Horizon n psi)
    have hpos : 0 < n ^ theorem1Horizon n psi := Nat.pow_pos (by omega)
    have h65 : 65 * n ^ theorem1Horizon n psi ≤ n * n ^ theorem1Horizon n psi :=
      Nat.mul_le_mul_right _ (by omega)
    apply Nat.lt_of_not_le
    intro hle
    have := Nat.mul_le_mul_left n hle
    omega

/-! ## From pointwise reachability to a producer -/

/-- A safe prefix hit yields an endpoint witness no longer than the word. -/
theorem theorem1ReachesSafeTarget_endpoint_prefix
    {n psi kappa : Nat} (ring : DirectedRing n) :
    ∀ (C : Config n psi kappa) (word : DetSchedule n),
      theorem1ReachesSafeTarget ring C word = true →
        ∃ pre : DetSchedule n,
          pre.length ≤ word.length ∧
          Theorem1SafeTarget ring
            (runLocalSchedule ring (PPL.protocol psi kappa).transition C pre) := by
  intro C word hhit
  rw [theorem1ReachesSafeTarget_eq] at hhit
  obtain ⟨pre, hlen, h⟩ :=
    PPL.Theorem1General.theorem1ReachesB_endpoint_prefix ring _ C word hhit
  exact ⟨pre, hlen, by simpa using h⟩

/-- Finite maximum over an exhaustive configuration list. -/
theorem theorem1PossibleSafeUniformBound_of_exhaustive
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (e : ExhaustiveList (Config n psi kappa))
    (hpoint :
      ∀ C : Config n psi kappa,
        ∃ word : DetSchedule n, theorem1ReachesSafeTarget ring C word = true) :
    ∃ L : Nat,
      ∀ C : Config n psi kappa,
        ∃ word : DetSchedule n,
          word.length ≤ L ∧ theorem1ReachesSafeTarget ring C word = true :=
  PPL.Theorem1General.theorem1UniformBound_of_exhaustive e
    (theorem1ReachesSafeTarget ring) hpoint

private theorem psiGe_directedRing_eq {n : Nat} (R R' : DirectedRing n) :
    R = R' := by
  cases R
  cases R'
  rfl

/-- **Producer on `3 ≤ n ≤ psi`.**  One positive length `L` such that, on
every ring, every configuration outside the safe target reaches it by a word
of length at most `L`. -/
theorem theorem1SafeProducer
    {n psi : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi) (hge : n ≤ psi) :
    ∃ L : Nat, 0 < L ∧
      ∀ ring : DirectedRing n,
        BoundedSafeScheduleProducer ring
          (PPL.protocol psi (theorem1Kappa psi)).transition
          (fun _ => True) (Theorem1SafeTarget ring) L := by
  let ring0 : DirectedRing n := ⟨by omega⟩
  obtain ⟨L, hL⟩ :=
    theorem1PossibleSafeUniformBound_of_exhaustive ring0
      (theorem1ConfigStates n psi (theorem1Kappa psi))
      (fun C => theorem1PossibleSafe hn3 hpsi hge ring0 C)
  refine ⟨L + 1, by omega, ?_⟩
  intro ring
  have hring : ring = ring0 := psiGe_directedRing_eq ring ring0
  subst hring
  intro C _hTrue _hnot
  obtain ⟨word, hlen, hhit⟩ := hL C
  obtain ⟨pre, hprelen, hsafe⟩ :=
    theorem1ReachesSafeTarget_endpoint_prefix ring0 C word hhit
  exact ⟨pre, by omega, hsafe⟩

/-! ## From a producer to the expected cost (copy of `Theorem1CostTiny.lean`) -/

/-- Block length of the amplified producer. -/
def theorem1SafeBlock (n L : Nat) : Nat :=
  ((n - 1) * (n ^ L - 1) + 1) * L

/-- Boolean test for the safe target. -/
def theorem1SafeTest {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) : Bool :=
  decide (Theorem1SafeTarget ring C)

theorem theorem1SafeTest_spec {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) :
    theorem1SafeTest ring C = true ↔ Theorem1SafeTarget ring C := by
  simp [theorem1SafeTest]

/-- The safe prefix Boolean is the generic local hitting Boolean. -/
theorem theorem1ReachesSafeTarget_eq_hits
    {n psi kappa : Nat} (ring : DirectedRing n) :
    ∀ (C : Config n psi kappa) (word : DetSchedule n),
      theorem1ReachesSafeTarget ring C word =
        hitsWithinLocal ring (PPL.protocol psi kappa).transition
          (theorem1SafeTest ring) C word := by
  intro C word
  induction word generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [theorem1ReachesSafeTarget, hitsWithinLocal]
      rw [theorem1SmallN_localStep_eq_protocolStep ring C e, ih]
      rfl

/-- On a closed target, the prefix miss count is the endpoint miss
`wordSum` (copy of `PPL.theorem1FailureNumerator_eq_wordSum_miss`). -/
theorem theorem1SafeFailureNumerator_eq_wordSum_miss
    {n psi kappa : Nat} (ring : DirectedRing n)
    (hclosed :
      ∀ (D : Config n psi kappa) (e : Fin n),
        Theorem1SafeTarget ring D →
          Theorem1SafeTarget ring
            (PopulationProtocol.step (protocol psi kappa) ring D e))
    (C : Config n psi kappa) (T : Nat) :
    theorem1SafeFailureNumerator ring C T =
      wordSum
        (fun D e => PopulationProtocol.step (protocol psi kappa) ring D e)
        (miss (Theorem1SafeTarget ring)) C T := by
  classical
  have hcur :
      ∀ (D : Config n psi kappa) (w : DetSchedule n),
        Theorem1SafeTarget ring D → theorem1ReachesSafeTarget ring D w = true := by
    intro D w hD
    cases w with
    | nil => simp [theorem1ReachesSafeTarget, hD]
    | cons e rest => simp [theorem1ReachesSafeTarget, hD]
  have hend :
      ∀ (D : Config n psi kappa) (w : DetSchedule n),
        theorem1ReachesSafeTarget ring D w =
          decide (Theorem1SafeTarget ring
            (LDSinkBoundedKernel.run
              (fun D e => PopulationProtocol.step (protocol psi kappa) ring D e)
              D w)) := by
    intro D w
    induction w generalizing D with
    | nil => rfl
    | cons e rest ih =>
        simp only [theorem1ReachesSafeTarget, LDSinkBoundedKernel.run]
        by_cases hD : Theorem1SafeTarget ring D
        · have hrec := hcur _ rest (hclosed D e hD)
          rw [show decide (Theorem1SafeTarget ring D) = true by simp [hD],
            Bool.true_or]
          exact hrec.symm.trans (ih _)
        · rw [show decide (Theorem1SafeTarget ring D) = false by simp [hD],
            Bool.false_or]
          exact ih _
  unfold theorem1SafeFailureNumerator
  rw [theorem1L17CountP_eq_fixedWordSum]
  rw [← K2FiniteSafeEliminationExpected.wordSum_run]
  apply congrArg
    (fun f : DetSchedule n → Nat => FixedSpanRenewalPayload.wordSum n T f)
  funext word
  rw [hend C word]
  unfold miss
  by_cases h :
      Theorem1SafeTarget ring
        (LDSinkBoundedKernel.run
          (fun D e => PopulationProtocol.step (protocol psi kappa) ring D e)
          C word)
  · simp [h]
  · simp [h]

/-- One-step closure of the safe target, in the form used by the cost
lemmas. -/
theorem theorem1SafeTarget_step_closed
    {n psi : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi) (ring : DirectedRing n) :
    ∀ (D : Config n psi (theorem1Kappa psi)) (e : Fin n),
      Theorem1SafeTarget ring D →
        Theorem1SafeTarget ring
          (PopulationProtocol.step (protocol psi (theorem1Kappa psi)) ring D e) := by
  intro D e hD
  exact theorem1SafeTarget_closedPred hn3 hpsi ring D hD _ ⟨e, rfl⟩

/-- A producer of length `L` gives a half-failure block of length
`theorem1SafeBlock n L` for the endpoint miss (copy of the private
`theorem1TinyHalfFailure_of_producer`). -/
theorem theorem1SafeHalfFailure_of_producer
    {n psi : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi)
    (L : Nat) (hL : 0 < L)
    (ring : DirectedRing n)
    (hproducer :
      BoundedSafeScheduleProducer ring
        (PPL.protocol psi (theorem1Kappa psi)).transition
        (fun _ => True) (Theorem1SafeTarget ring) L)
    (C : Config n psi (theorem1Kappa psi)) :
    2 * wordSum
        (fun D e =>
          PopulationProtocol.step (PPL.protocol psi (theorem1Kappa psi)) ring D e)
        (miss (Theorem1SafeTarget ring)) C (theorem1SafeBlock n L) ≤
      n ^ theorem1SafeBlock n L := by
  let k : Nat := (n - 1) * (n ^ L - 1) + 1
  let B : Nat := k * L
  have hk : 0 < k := by simp [k]
  have hB : 0 < B := Nat.mul_pos hk hL
  have hDomainClosed :
      LocalStepClosed ring (PPL.protocol psi (theorem1Kappa psi)).transition
        (fun _ => True) := by
    intro D _hD e
    exact True.intro
  have hphase0 :=
    boundedSafeProducer_explicitOneOverNPhase ring
      (PPL.protocol psi (theorem1Kappa psi)).transition
      (fun _ => True) (Theorem1SafeTarget ring) (theorem1SafeTest ring)
      (theorem1SafeTest_spec ring) hDomainClosed (by omega : 1 < n) L hL
      hproducer
  dsimp only at hphase0
  have hphase :
      UniformFinitePhase ring (PPL.protocol psi (theorem1Kappa psi)).transition
        (fun _ => True) (Theorem1SafeTarget ring) (theorem1SafeTest ring)
        B (n ^ (B - 1)) := by
    simpa [B, k] using hphase0.2
  have hcount := hphase.2 C True.intro
  have hpartition :=
    localMissCount_add_localHitCount ring
      (PPL.protocol psi (theorem1Kappa psi)).transition
      (theorem1SafeTest ring) C B
  rw [allSchedules_length] at hcount hpartition
  have hmiss :
      localMissCount ring (PPL.protocol psi (theorem1Kappa psi)).transition
          (theorem1SafeTest ring) C B ≤ n ^ (B - 1) := by
    omega
  have hBsucc : B = (B - 1) + 1 := by omega
  have hpow : 2 * n ^ (B - 1) ≤ n ^ B := by
    calc
      2 * n ^ (B - 1) = n ^ (B - 1) * 2 := Nat.mul_comm _ _
      _ ≤ n ^ (B - 1) * n := Nat.mul_le_mul_left _ (by omega)
      _ = n ^ ((B - 1) + 1) := by rw [Nat.pow_succ]
      _ = n ^ B := by rw [← hBsucc]
  have hmissEq :
      wordSum
          (fun D e =>
            PopulationProtocol.step (PPL.protocol psi (theorem1Kappa psi)) ring D e)
          (miss (Theorem1SafeTarget ring)) C B =
        localMissCount ring (PPL.protocol psi (theorem1Kappa psi)).transition
          (theorem1SafeTest ring) C B := by
    rw [← theorem1SafeFailureNumerator_eq_wordSum_miss ring
      (theorem1SafeTarget_step_closed hn3 hpsi ring) C B]
    unfold theorem1SafeFailureNumerator localMissCount
    apply congrArg (fun p : DetSchedule n → Bool => (allSchedules n B).countP p)
    funext word
    rw [theorem1ReachesSafeTarget_eq_hits ring C word]
  have hhalf :
      2 * wordSum
          (fun D e =>
            PopulationProtocol.step (PPL.protocol psi (theorem1Kappa psi)) ring D e)
          (miss (Theorem1SafeTarget ring)) C B ≤ n ^ B := by
    rw [hmissEq]
    exact Nat.le_trans (Nat.mul_le_mul_left 2 hmiss) hpow
  simpa [theorem1SafeBlock, B, k] using hhalf

/-- The Theorem-1 horizon is positive. -/
theorem theorem1Horizon_pos {n psi : Nat} (hn3 : 3 ≤ n) :
    0 < theorem1Horizon n psi := by
  have hnpos : 0 < n := by omega
  have h15 : 0 < PPL.Convergence.ReachCPB.lemma16H15 n := by
    unfold PPL.Convergence.ReachCPB.lemma16H15
    exact Nat.mul_pos (Nat.mul_pos (by omega) hnpos) (by omega)
  have h16 :
      0 < PPL.Convergence.ReachCPB.lemma16Horizon n psi (theorem1Kappa psi) := by
    unfold PPL.Convergence.ReachCPB.lemma16Horizon
    omega
  unfold theorem1Horizon
  omega

/-- **Expected cost for one pair `(n, psi)` with `3 ≤ n ≤ psi`.**  Some
constant `c` bounds the truncated first-hit cost numerator of the safe
target by `n ^ T · (c · H)` for every ring, start and truncation `T`. -/
theorem theorem1SafeCost_pair
    {n psi : Nat} (hn3 : 3 ≤ n) (hpsi : 2 ≤ psi) (hge : n ≤ psi) :
    ∃ c : Nat,
      ∀ (ring : DirectedRing n) (C0 : Config n psi (theorem1Kappa psi)) (T : Nat),
        theorem1SafeCostNumerator ring C0 T ≤
          n ^ T * (c * theorem1Horizon n psi) := by
  obtain ⟨L, hL, hprod⟩ := theorem1SafeProducer hn3 hpsi hge
  refine ⟨2 * theorem1SafeBlock n L, ?_⟩
  intro ring C0 T
  have hB : 0 < theorem1SafeBlock n L := by
    unfold theorem1SafeBlock
    exact Nat.mul_pos (by omega) hL
  have hcost :=
    cost_le_two_blocks
      (fun D e =>
        PopulationProtocol.step (PPL.protocol psi (theorem1Kappa psi)) ring D e)
      (Theorem1SafeTarget ring)
      (theorem1SafeTarget_step_closed hn3 hpsi ring)
      (theorem1SafeBlock n L) hB
      (fun D => theorem1SafeHalfFailure_of_producer hn3 hpsi L hL ring
        (hprod ring) D)
  have hraw :
      theorem1SafeCostNumerator ring C0 T ≤
        n ^ T * (2 * theorem1SafeBlock n L) := by
    simpa [theorem1SafeCostNumerator] using hcost T C0
  have hH : 1 ≤ theorem1Horizon n psi := theorem1Horizon_pos hn3
  refine Nat.le_trans hraw (Nat.mul_le_mul_left _ ?_)
  have := Nat.mul_le_mul_left (2 * theorem1SafeBlock n L) hH
  simpa using this

/-! ## Finiteness of the domain for fixed `s` -/

/-- `2 k ≤ 2 ^ k`. -/
theorem two_mul_le_two_pow : ∀ k : Nat, 2 * k ≤ 2 ^ k
  | 0 => by decide
  | k + 1 => by
      have ih := two_mul_le_two_pow k
      rw [Nat.pow_succ]
      cases k with
      | zero => decide
      | succ k =>
          have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
          omega

/-- `2 · log2 n ≤ n`. -/
theorem two_mul_log2_le (n : Nat) : 2 * Nat.log2 n ≤ n := by
  by_cases hn : n = 0
  · subst hn
    simp
  · exact Nat.le_trans (two_mul_le_two_pow _) (Nat.log2_self_le hn)

/-- On the window `n ≤ psi ≤ log2 n + s`: `n ≤ 2 s` and `psi ≤ 3 s`. -/
theorem psiGe_window_bounds {n psi s : Nat}
    (hge : n ≤ psi) (hwin : psi ≤ Nat.log2 n + s) :
    n ≤ 2 * s ∧ psi ≤ 3 * s := by
  have h := two_mul_log2_le n
  omega

/-- Uniform bound over `k ≤ N` from pointwise bounds, for a family monotone
in the bound. -/
theorem exists_uniform_le
    (Q : Nat → Nat → Prop)
    (hmono : ∀ k c c', c ≤ c' → Q k c → Q k c')
    (h : ∀ k, ∃ c, Q k c) :
    ∀ N : Nat, ∃ c, ∀ k, k ≤ N → Q k c := by
  intro N
  induction N with
  | zero =>
      obtain ⟨c, hc⟩ := h 0
      refine ⟨c, fun k hk => ?_⟩
      have : k = 0 := by omega
      subst this
      exact hc
  | succ N ih =>
      obtain ⟨c1, hc1⟩ := ih
      obtain ⟨c2, hc2⟩ := h (N + 1)
      refine ⟨Nat.max c1 c2, fun k hk => ?_⟩
      by_cases hkN : k ≤ N
      · exact hmono k c1 _ (Nat.le_max_left _ _) (hc1 k hkN)
      · have : k = N + 1 := by omega
        subst this
        exact hmono _ c2 _ (Nat.le_max_right _ _) hc2

/-! ## The statement -/

/-- **`Theorem1PsiAtLeastNStatement s`, proved for every `s`.**  whp from
`theorem1SafeWhp_proved`; the cost constant is the maximum of the per-pair
constants `theorem1SafeCost_pair` over the finite domain `n ≤ 2 s`,
`psi ≤ 3 s`. -/
theorem theorem1PsiAtLeastNStatement_proved (s : Nat) :
    Theorem1PsiAtLeastNStatement s := by
  classical
  let R : Nat → Nat → Nat → Prop := fun n psi c =>
    3 ≤ n → 2 ≤ psi → n ≤ psi →
      ∀ (ring : DirectedRing n) (C0 : Config n psi (theorem1Kappa psi)) (T : Nat),
        theorem1SafeCostNumerator ring C0 T ≤
          n ^ T * (c * theorem1Horizon n psi)
  have hmono : ∀ n psi c c', c ≤ c' → R n psi c → R n psi c' := by
    intro n psi c c' hcc hR hn3 hpsi hge ring C0 T
    exact Nat.le_trans (hR hn3 hpsi hge ring C0 T)
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcc))
  have hpoint : ∀ n psi, ∃ c, R n psi c := by
    intro n psi
    by_cases hdom : 3 ≤ n ∧ 2 ≤ psi ∧ n ≤ psi
    · obtain ⟨c, hc⟩ := theorem1SafeCost_pair hdom.1 hdom.2.1 hdom.2.2
      exact ⟨c, fun _ _ _ => hc⟩
    · exact ⟨0, fun hn3 hpsi hge => absurd ⟨hn3, hpsi, hge⟩ hdom⟩
  have hinner : ∀ n, ∃ c, ∀ psi, psi ≤ 3 * s → R n psi c := fun n =>
    exists_uniform_le (fun psi c => R n psi c)
      (fun psi c c' h => hmono n psi c c' h) (hpoint n) (3 * s)
  obtain ⟨c, hc⟩ :=
    exists_uniform_le (fun n c => ∀ psi, psi ≤ 3 * s → R n psi c)
      (fun n c c' h hQ psi hpsi => hmono n psi c c' h (hQ psi hpsi))
      hinner (2 * s)
  refine ⟨c + 1, by omega, ?_⟩
  intro n psi hn3 hpsi hge hwin ring C0
  have hb := psiGe_window_bounds hge hwin
  have hnpow : n ≤ 2 ^ psi :=
    Nat.le_trans hge (Nat.le_of_lt (lt_two_pow_self' psi))
  refine ⟨theorem1SafeWhp_proved hn3 hpsi hnpow hge ring C0, ?_⟩
  intro T
  exact hmono n psi c (c + 1) (by omega) (hc n hb.1 psi hb.2) hn3 hpsi hge ring C0 T

/-- **Paper-form Theorem 1 on the whole window `psi ≤ log2 n + s`, with the
safe target, proved for every `s`.** -/
theorem theorem1PaperFormSafeTarget_proved (s : Nat) :
    Theorem1PaperFormSafeTarget s :=
  theorem1PaperFormSafeTarget_of_psiAtLeastN s
    (theorem1PsiAtLeastNStatement_proved s)

end PPL.PsiAtLeastN

#print axioms PPL.PsiAtLeastN.theorem1SafeWhp_proved
#print axioms PPL.PsiAtLeastN.theorem1PossibleSafe
#print axioms PPL.PsiAtLeastN.theorem1SafeCost_pair
#print axioms PPL.PsiAtLeastN.theorem1PsiAtLeastNStatement_proved
#print axioms PPL.PsiAtLeastN.theorem1PaperFormSafeTarget_proved
