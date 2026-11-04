import Leader.Wu.PartialProtocol.RawZeroLeaderClosedClass

/-!
# Raw `P_partial`: an all-size zero-leader counterfamily

The four endpoint states `N`, `R`, `H`, and `RH` from the exact two-agent
closed class are in fact a transition-closed alphabet.  For every responder in
the alphabet, the raw transition table depends only on the initiator:

* `N  _ ↦ (H, R)`;
* `R  _ ↦ (H, R)`;
* `H  _ ↦ (N, RH)`;
* `RH _ ↦ (N, R)`.

Thus the full cyclic shift over these four states is closed under every edge
on every positive ring size.  All four states emit follower.  This is an
all-schedules closed counterfamily, not merely one weak-fair bad execution.
Restricting to `1 < n` gives an unbounded family inside `OperationalRegime`.
-/

namespace PPLLCompleteMultiLeaderCleanup

open PPLL PPLLResearchFormulation
open PPLLExpiringComparisonRepair

set_option autoImplicit false

variable {n : Nat}

abbrev RawZeroAlphabetState := ExpiringAgentState 1 0 0

/-- Exact membership in the four-state zero-output alphabet. -/
inductive InRawZeroAlphabet : RawZeroAlphabetState → Prop where
  | ofN : InRawZeroAlphabet rawZeroClosedN
  | ofR : InRawZeroAlphabet rawZeroClosedR
  | ofH : InRawZeroAlphabet rawZeroClosedH
  | ofRH : InRawZeroAlphabet rawZeroClosedRH

/-! ## Exact `4 × 4` raw transition table -/

theorem rawZeroAlphabet_transition_N
    (r : RawZeroAlphabetState) (hr : InRawZeroAlphabet r) :
    P_partialUnconditional rawZeroClosed_hpsi 0 0 rawZeroClosedN r =
      (rawZeroClosedH, rawZeroClosedR) := by
  cases hr <;> rfl

theorem rawZeroAlphabet_transition_R
    (r : RawZeroAlphabetState) (hr : InRawZeroAlphabet r) :
    P_partialUnconditional rawZeroClosed_hpsi 0 0 rawZeroClosedR r =
      (rawZeroClosedH, rawZeroClosedR) := by
  cases hr <;> rfl

theorem rawZeroAlphabet_transition_H
    (r : RawZeroAlphabetState) (hr : InRawZeroAlphabet r) :
    P_partialUnconditional rawZeroClosed_hpsi 0 0 rawZeroClosedH r =
      (rawZeroClosedN, rawZeroClosedRH) := by
  cases hr <;> rfl

theorem rawZeroAlphabet_transition_RH
    (r : RawZeroAlphabetState) (hr : InRawZeroAlphabet r) :
    P_partialUnconditional rawZeroClosed_hpsi 0 0 rawZeroClosedRH r =
      (rawZeroClosedN, rawZeroClosedR) := by
  cases hr <;> rfl

/-- Every one of the sixteen exact table entries remains in the alphabet. -/
theorem rawZeroAlphabet_transition_closed
    (l r : RawZeroAlphabetState)
    (hl : InRawZeroAlphabet l) (hr : InRawZeroAlphabet r) :
    let q := P_partialUnconditional rawZeroClosed_hpsi 0 0 l r
    InRawZeroAlphabet q.1 ∧ InRawZeroAlphabet q.2 := by
  cases hl with
  | ofN =>
      rw [rawZeroAlphabet_transition_N r hr]
      exact ⟨.ofH, .ofR⟩
  | ofR =>
      rw [rawZeroAlphabet_transition_R r hr]
      exact ⟨.ofH, .ofR⟩
  | ofH =>
      rw [rawZeroAlphabet_transition_H r hr]
      exact ⟨.ofN, .ofRH⟩
  | ofRH =>
      rw [rawZeroAlphabet_transition_RH r hr]
      exact ⟨.ofN, .ofR⟩

/-! ## Full-shift closure on an arbitrary ring -/

def RawZeroAlphabetConfig
    (C : PPartialConfig n 1 0 0) : Prop :=
  ∀ i : Fin n, InRawZeroAlphabet (C i)

theorem RawZeroAlphabetConfig.localStep
    (ring : DirectedRing n) (C : PPartialConfig n 1 0 0)
    (hC : RawZeroAlphabetConfig C) (e : Fin n) :
    RawZeroAlphabetConfig
      (localStep ring
        (P_partialUnconditional rawZeroClosed_hpsi 0 0) C e) := by
  let j := ring.rightNeighbor e
  have hq := rawZeroAlphabet_transition_closed
    (C e) (C j) (hC e) (hC j)
  intro i
  by_cases hie : i = e
  · subst i
    simpa only [PPLLResearchFormulation.localStep, if_pos] using hq.1
  · by_cases hij : i = j
    · subst i
      simpa only [PPLLResearchFormulation.localStep, j,
        if_neg hie, if_pos] using hq.2
    · simpa only [PPLLResearchFormulation.localStep, j,
        if_neg hie, if_neg hij] using hC i

/-- The full four-letter shift is closed under the packaged raw protocol on
every positive ring. -/
theorem rawZeroAlphabet_closedPred
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
      (P_partialProtocolUnconditional rawZeroClosed_hpsi 0 0)
      ring RawZeroAlphabetConfig := by
  intro C hC C' hstep
  rcases hstep with ⟨e, rfl⟩
  rw [← localStep_eq_protocol_step]
  exact RawZeroAlphabetConfig.localStep ring C hC e

/-- Direct finite-word closure, with no scheduler restriction. -/
theorem rawZeroAlphabet_run
    (ring : DirectedRing n) (C : PPartialConfig n 1 0 0)
    (hC : RawZeroAlphabetConfig C) (word : DetSchedule n) :
    RawZeroAlphabetConfig
      (runLocalSchedule ring
        (P_partialUnconditional rawZeroClosed_hpsi 0 0) C word) := by
  induction word generalizing C with
  | nil =>
      exact hC
  | cons e rest ih =>
      simp only [runLocalSchedule]
      exact ih _ (RawZeroAlphabetConfig.localStep ring C hC e)

/-! ## Zero output on the whole closed shift -/

theorem InRawZeroAlphabet.leader_false
    (s : RawZeroAlphabetState) (hs : InRawZeroAlphabet s) :
    s.core.core.leader = false := by
  cases hs <;> rfl

theorem RawZeroAlphabetConfig.leader_false
    (C : PPartialConfig n 1 0 0)
    (hC : RawZeroAlphabetConfig C) (i : Fin n) :
    (C i).core.core.leader = false :=
  (hC i).leader_false (C i)

theorem rawZeroAlphabet_not_legit
    (C : PPartialConfig n 1 0 0)
    (hC : RawZeroAlphabetConfig C) :
    ¬ PPartialLegitUnconditional rawZeroClosed_hpsi 0 0 C := by
  intro hlegit
  rcases hlegit with ⟨i, hi, _⟩
  have hfalse := hC.leader_false C i
  simp [P_partialProtocol, hfalse, isLeaderOutput] at hi

/-- No finite word from the four-letter shift reaches one-leader output. -/
theorem rawZeroAlphabet_no_finite_birth
    (ring : DirectedRing n) (C : PPartialConfig n 1 0 0)
    (hC : RawZeroAlphabetConfig C) :
    ¬ ∃ word : DetSchedule n,
      PPartialLegitUnconditional rawZeroClosed_hpsi 0 0
        (runLocalSchedule ring
          (P_partialUnconditional rawZeroClosed_hpsi 0 0) C word) := by
  rintro ⟨word, hlegit⟩
  exact rawZeroAlphabet_not_legit _
    (rawZeroAlphabet_run ring C hC word) hlegit

/-! ## An unbounded operational-regime counterfamily -/

def rawZeroAllNConfig (n : Nat) : PPartialConfig n 1 0 0 :=
  fun _ => rawZeroClosedN

theorem rawZeroAllNConfig_inAlphabet (n : Nat) :
    RawZeroAlphabetConfig (rawZeroAllNConfig n) := by
  intro i
  exact .ofN

theorem rawZeroAllNConfig_leaderCount_zero (n : Nat) :
    P_partialLeaderCount (rawZeroAllNConfig n) = 0 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [P_partialLeaderCount, List.ofFn_succ, List.sum_cons]
      change 0 + P_partialLeaderCount (rawZeroAllNConfig n) = 0
      rw [ih]

/-- On every positive ring, the homogeneous `N` configuration refutes every
finite rank-zero/rank-one producer bound. -/
theorem rawZeroAlphabet_not_baseProducer
    (ring : DirectedRing n) (baseBound : Nat) :
    ¬ PPartialBaseProducerUnconditional rawZeroClosed_hpsi 0 0
      ring baseBound := by
  intro hproducer
  obtain ⟨word, _hLength, hlegit⟩ :=
    hproducer (rawZeroAllNConfig n) (by
      rw [rawZeroAllNConfig_leaderCount_zero]
      omega)
  exact rawZeroAlphabet_no_finite_birth ring
    (rawZeroAllNConfig n) (rawZeroAllNConfig_inAlphabet n)
    ⟨word, hlegit⟩

/-- Every size `n ≥ 2` supplies an `OperationalRegime` whose exact raw
protocol has the all-schedules closed zero-output counterfamily. -/
theorem rawZeroCounterfamily_all_nontrivial_sizes
    (n : Nat) (hn : 1 < n) (baseBound : Nat) :
    let regime := operationalRegime_of rawZeroClosed_hpsi hn
    RawZeroAlphabetConfig (rawZeroAllNConfig n) ∧
      PopulationProtocol.ClosedPred
        (P_partialProtocolUnconditional rawZeroClosed_hpsi 0 0)
        regime.ring RawZeroAlphabetConfig ∧
      ¬ PPartialBaseProducerUnconditional rawZeroClosed_hpsi 0 0
        regime.ring baseBound := by
  dsimp only
  exact ⟨rawZeroAllNConfig_inAlphabet n,
    rawZeroAlphabet_closedPred _,
    rawZeroAlphabet_not_baseProducer _ baseBound⟩

#print axioms rawZeroAlphabet_transition_closed
#print axioms rawZeroAlphabet_closedPred
#print axioms rawZeroAlphabet_run
#print axioms rawZeroAlphabet_no_finite_birth
#print axioms rawZeroAlphabet_not_baseProducer
#print axioms rawZeroCounterfamily_all_nontrivial_sizes

end PPLLCompleteMultiLeaderCleanup
