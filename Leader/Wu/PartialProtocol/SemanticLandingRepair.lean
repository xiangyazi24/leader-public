import Leader.Wu.PartialProtocol.OutputKernelNoGo

/-!
# Minimal semantic landing repair for `P_partial`

The exact terminal predicate is the existing `PPartialStableLegit`: current
unique-leader output together with `OutputStableFrom`.  Its closure is already
proved generically and needs no protocol-specific local-legitimacy premise.

What remains between the existing rank producers and that terminal predicate
is stated as a bounded semantic landing producer.  This file composes the
three producer bounds without changing or copying the `P_partial` transition.
It also records both sides of the old-local-premise comparison: full
`PPartialLocalLegitimacy` supplies a zero-length landing, while the concrete T1
configuration proves that a bare `PPartialLegit` snapshot does not.
-/

namespace PPLLCompleteMultiLeaderCleanup

open PPLL PPLLResearchFormulation
open PPartialOutputKernelNoGoSol
open PPLLCounterexample

set_option autoImplicit false

variable {n psi : Nat}

/-- The residual producer needed after the existing rank composition: from
every current unique-leader snapshot, use at most `landingBound` exact
`P_partial` interactions to reach Definition-1 semantic safety. -/
def PPartialSemanticLandingProducerQ6348
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (landingBound : Nat) : Prop :=
  ∀ C : PPartialConfig n psi kappa tau,
    PPartialLegitUnconditional hpsi kappa tau C →
      ∃ word : DetSchedule n,
        word.length ≤ landingBound ∧
          PPartialStableLegit hpsi kappa tau ring
            (runLocalSchedule ring
              (P_partialUnconditional hpsi kappa tau) C word)

/-- The refuted old local premise would discharge semantic landing with the
empty schedule.  This is a comparison bridge, not a premise of the composed
repair theorem below. -/
theorem PPartialSemanticLandingProducerQ6348_of_localLegitimacy
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (hLocal : PPartialLocalLegitimacyUnconditional
      hpsi kappa tau ring) :
    PPartialSemanticLandingProducerQ6348
      hpsi kappa tau ring 0 := by
  intro C hC
  refine ⟨[], by simp, ?_⟩
  change PPartialStableLegit hpsi kappa tau ring C
  apply (PPartialStableLegit_iff_isSafe
    hpsi kappa tau ring C).2
  change PopulationProtocol.IsSafe
    (P_partialProtocol hpsi kappa tau
      (PPartialAuthorizedDomainClosure_q5776 hpsi kappa))
    ring C isLeaderOutput
  exact PPartialLegit_isSafe
    hpsi kappa tau
    (PPartialAuthorizedDomainClosure_q5776 hpsi kappa)
    ring hLocal C hC

/-- Concrete separation required by the bridge audit: T1 has exactly one
current leader output, but it is not in the semantic stable predicate. -/
theorem PPartialLegit_not_imply_stable_t1
    (hpsi : (2 : Nat) > 0) :
    ∃ C : PPartialConfig 4 2 10 0,
      PPartialLegitUnconditional hpsi 10 0 C ∧
        ¬ PPartialStableLegit hpsi 10 0 ring4 C := by
  refine ⟨t1FiniteConfig, ?_, ?_⟩
  · exact PPartialOutputLegit.toLegit
      hpsi 10 0 ring4 t1FiniteConfig t1FiniteConfig_outputLegit
  · exact t1FiniteConfig_not_stableLegit

/-- In particular, bare current legitimacy cannot supply even a bound-zero
semantic landing producer on the concrete T1 instance. -/
theorem PPartialSemanticLandingProducerQ6348_zero_false_t1
    (hpsi : (2 : Nat) > 0) :
    ¬ PPartialSemanticLandingProducerQ6348
      hpsi 10 0 ring4 0 := by
  intro hLanding
  obtain ⟨C, hLegit, hNotStable⟩ :=
    PPartialLegit_not_imply_stable_t1 hpsi
  obtain ⟨word, hLength, hStable⟩ :=
    hLanding C hLegit
  have hLengthZero : word.length = 0 :=
    Nat.eq_zero_of_le_zero hLength
  have hWord : word = [] :=
    List.eq_nil_of_length_eq_zero hLengthZero
  subst word
  exact hNotStable hStable

/-- Schedule concatenation for the exact explicit-transition runner. -/
private theorem runLocalSchedule_appendQ6348
    {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q)
    (C : Fin n → Q) (xs ys : DetSchedule n) :
    runLocalSchedule ring T C (xs ++ ys) =
      runLocalSchedule ring T
        (runLocalSchedule ring T C xs) ys := by
  induction xs generalizing C with
  | nil =>
      rfl
  | cons e xs ih =>
      simp only [List.cons_append, runLocalSchedule]
      exact ih (localStep ring T C e)

/-- Closest deterministic semantic repair available from the current
interfaces.  Closure is proved, while all three convergence producers remain
explicit.  The claimed schedule bound and state enumeration are literal. -/
theorem P_partial_minimal_semantic_repairQ6348
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (baseBound roundBound landingBound : Nat)
    (hBase : PPartialBaseProducerUnconditional
      hpsi kappa tau ring baseBound)
    (hDescent : PPartialStrictDescentProducerUnconditional
      hpsi kappa tau ring roundBound)
    (hLanding : PPartialSemanticLandingProducerQ6348
      hpsi kappa tau ring landingBound) :
    PopulationProtocol.ClosedPred
        (P_partialProtocolUnconditional hpsi kappa tau)
        ring
        (PPartialStableLegit hpsi kappa tau ring) ∧
      (∀ C : PPartialConfig n psi kappa tau,
        ∃ word : DetSchedule n,
          word.length ≤
            baseBound + n * roundBound + landingBound ∧
          ReachesSafeWithinSchedule
            (P_partialProtocolUnconditional hpsi kappa tau)
            ring isLeaderOutput C word) ∧
      (P_partialStateCertificate psi kappa tau).values.length =
        (2 * (PPLLFinite.boundedAgentState
          psi kappa).values.length) * (tau + 1) := by
  constructor
  · change PopulationProtocol.ClosedPred
      (P_partialProtocol hpsi kappa tau
        (PPartialAuthorizedDomainClosure_q5776 hpsi kappa))
      ring
      (PPartialStableLegit hpsi kappa tau ring)
    exact PPartialStableLegit_closed hpsi kappa tau ring
  constructor
  · intro C
    obtain ⟨head, hHead, hHeadLegit⟩ :=
      P_partial_exists_legit_schedule
        hpsi kappa tau
        (PPartialAuthorizedDomainClosure_q5776 hpsi kappa)
        ring baseBound roundBound hBase hDescent C
    have hHeadLegit' : PPartialLegitUnconditional hpsi kappa tau
        (runLocalSchedule ring
          (P_partialUnconditional hpsi kappa tau) C head) := by
      exact hHeadLegit
    obtain ⟨tail, hTail, hSemanticTail⟩ :=
      hLanding _ hHeadLegit'
    refine ⟨head ++ tail, ?_, ?_⟩
    · simp only [List.length_append]
      omega
    · refine ⟨(head ++ tail).length,
        Nat.le_refl (head ++ tail).length, ?_⟩
      simp only [List.take_length]
      have hSemanticFull :
          PPartialStableLegit hpsi kappa tau ring
            (runLocalSchedule ring
              (P_partialUnconditional hpsi kappa tau)
              C (head ++ tail)) := by
        rw [runLocalSchedule_appendQ6348]
        exact hSemanticTail
      have hSafeLocal : PopulationProtocol.IsSafe
          (P_partialProtocolUnconditional hpsi kappa tau)
          ring
          (runLocalSchedule ring
            (P_partialUnconditional hpsi kappa tau)
            C (head ++ tail))
          isLeaderOutput := by
        exact (PPartialStableLegit_iff_isSafe
          hpsi kappa tau ring _).1 hSemanticFull
      rw [← P_partial_runLocalSchedule_eq_runSchedule_unconditional
        hpsi kappa tau ring C (head ++ tail)]
      exact hSafeLocal
  · exact P_partialStateCertificate_values_length psi kappa tau

end PPLLCompleteMultiLeaderCleanup
