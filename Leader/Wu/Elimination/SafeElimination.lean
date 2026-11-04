import Leader.Wu.Elimination.SafeEliminationExpectedCost

/-!
# Finite label-free safe elimination on the proved physical domain

The initial state satisfies the actual SignalGlobal and PeacefulGlobal
predicates. Both are closed under the original finite-cell elimination row.
The same scheduler words produce every count drop, the final count-one hit,
and semantic output safety. The physical label modulus is arbitrary positive
and is never replaced; modulus one occurs only in the exact signal observation.

Let Q = 32*2^14127 and Q2 = 16*2^1263. At
  (732*Q + 240*Q2)*n²*floor(log2 n)
the actual semantic IsSafe failure mass is at most 1/n. Every finite raw
prefix has expected first-safe cost at most
  (120*Q + 20*Q2)*n²*floor(log2 n).
The finite numerators include every unfinished prefix and every actual full
endpoint. No probability law, readiness, ordering, event budget, or final
service is a premise of the headline theorem.

This is the elimination component from the stated separated signal and
nearest-peaceful domain. Entry from adjacent or arbitrary protocol states,
and an assembled protocol dispatcher, are separate components.
-/

set_option autoImplicit false
set_option exponentiation.threshold 16384

open StateBoundUnifiedCell LDSinkBoundedKernel LabelFreeElimination K2FiniteProgress
open FiniteUniformStoppingTree LeaderCountDyadicTail LeaderCountExpectedCost
open K2FiniteSafeEliminationCore K2FiniteSafeEliminationTail K2FiniteSafeEliminationExpected

namespace K2FiniteSafeElimination

variable {n ψ κ : Nat}

/-- Literal full-word semantic failure numerator; its uniform denominator
is exactly n^T in the existing finite-product scheduler enumeration. -/
noncomputable def failureNumerator (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T
    (fun es => safeMiss hψ ring (run (step hψ ring) C es))

theorem failureNumerator_eq (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) :
    failureNumerator hψ ring C T = wordSum (step hψ ring) (safeMiss hψ ring) C T :=
  wordSum_run (step hψ ring) (safeMiss hψ ring) C T

theorem higher_denominator_exact : higherDenominator = 32 * 2 ^ 14127 := by
  unfold higherDenominator LDSinkTwoGapRaceEntranceUniformAll.deletionDenominator
  exact congrArg (fun b : Nat => 32 * 2 ^ b)
    (show LDSinkTwoGapRaceEntranceModerateMass.moderateCollapseBudget = 14127 from rfl)

theorem final_denominator_exact : finalDenominator = 16 * 2 ^ 1263 := by
  unfold finalDenominator
  exact congrArg (fun b : Nat => 16 * 2 ^ b)
    (show K2TwoLeaderEntranceMass.uniformCollapseBudget = 1263 from rfl)

theorem whp_constant_exact :
    whpConstant = 732 * (32 * 2 ^ 14127) + 240 * (16 * 2 ^ 1263) := by
  unfold whpConstant
  rw [higher_denominator_exact, final_denominator_exact]

theorem expected_constant_exact :
    expectedConstant = 120 * (32 * 2 ^ 14127) + 20 * (16 * 2 ^ 1263) := by
  unfold expectedConstant
  rw [higher_denominator_exact, final_denominator_exact]

/-- A first-success payload is the first genuinely safe physical prefix,
retaining that exact configuration. No later suffix is substituted for it. -/
theorem first_safe_payload (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C D : Fin n → UCell ψ κ) (hC : Domain ring C) (es : List (Fin n))
    (hy : FixedSpanRenewalPayload.runPayload (physicalPayload (step hψ ring) count)
      (haltAt count C) es = .success D) :
    ∃ u v, es = u ++ v ∧ D = run (step hψ ring) C u ∧
      PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring D id ∧
      ∀ t, t < u.length →
        ¬ PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring
          (run (step hψ ring) C (u.take t)) id := by
  obtain ⟨u, v, huv, hD, hd, hp⟩ := payload_first_hit (step hψ ring) count C D es hy
  have hDom : Domain ring D := hD ▸ domain_run hψ hn ring C hC u
  exact ⟨u, v, huv, hD, (isSafe_iff_count_one hψ hn ring D hDom).mpr hd,
    fun t ht hs => hp t ht (isSafe_count_one hψ ring _ hs)⟩

/-- The first-hit erasure and literal full endpoint have the same semantic
success event. The actual raw process executes all remaining interactions. -/
theorem stopped_success_iff_full_safe (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (es : List (Fin n)) :
    FixedSpanRenewalPayload.runStopped (oneStep hψ ring) (oneStart C) es = .success ↔
      PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring
        (run (step hψ ring) C es) id := by
  have he := first_hit_full_endpoint hψ hn ring C hC es
  have hs := isSafe_iff_count_one hψ hn ring _ (domain_run hψ hn ring C hC es)
  constructor
  · intro hh
    rw [he] at hh
    apply hs.mpr
    by_cases hc : count (run (step hψ ring) C es) = 1
    · exact hc
    · simp only [oneStart, if_neg hc] at hh
      cases hh
  · intro hh
    rw [he, oneStart, if_pos (hs.mp hh)]

/-- The original final-two mass, as actual full-word endpoint count one.
Both physical invariants are initial-state predicates, not service records. -/
theorem final_two_endpoint_mass (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hSig : SignalGlobal ring C)
    (hPeace : K2PeacefulGlobal.PeacefulGlobal ring C) (hc : count C = 2) :
    n ^ (20 * n * n) ≤ finalDenominator * FixedSpanRenewalPayload.wordSum n (20 * n * n)
      (fun es => if count (run (step hψ ring) C es) = 1 then 1 else 0) := by
  rw [wordSum_run (step hψ ring) (fun D : Fin n → UCell ψ κ => if count D = 1 then 1 else 0)
    C (20 * n * n)]
  exact two_leader_endpoint_mass hψ hn ring C ⟨hSig, hPeace⟩ hc

/-- Final semantic failure tail derived by the actual m=1 bin iteration.
It includes initially safe states and all early physical deletions. -/
theorem final_semantic_tail (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hSig : SignalGlobal ring C)
    (hPeace : K2PeacefulGlobal.PeacefulGlobal ring C) (hc : count C ≤ 2) :
    2 ^ logSlack n * failureNumerator hψ ring C (finalTime n) ≤ n ^ finalTime n := by
  rw [failureNumerator_eq, safe_wordSum_eq_count hψ hn ring C ⟨hSig, hPeace⟩]
  exact final_tail hψ hn ring C ⟨hSig, hPeace⟩ hc

/-- Complete finite elimination bound on the stated physical domain:
semantic failure at the explicit horizon, and exact first-safe cost at
every finite raw horizon, under the original label-free finite-cell step. -/
theorem safe_elimination (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hSig : SignalGlobal ring C)
    (hPeace : K2PeacefulGlobal.PeacefulGlobal ring C) :
    n * failureNumerator hψ ring C (safeHorizon n) ≤ n ^ safeHorizon n ∧
      ∀ T, FixedSpanRenewalPayload.wordSum n T (rawCostToSafe hψ ring C) ≤
        n ^ T * expectedBound n := by
  constructor
  · rw [failureNumerator_eq]
    exact safe_failure_whp hψ hn ring C ⟨hSig, hPeace⟩
  · intro T
    exact expected_safe_prefix hψ hn ring C ⟨hSig, hPeace⟩ T

/-- A real two-leader physical member with ψ=2, n=5, initially outside IsSafe.
Its stored labels remain in Fin 2, and the actual two-edge word reaches safety. -/
theorem nondivisible_domain_witness :
    ¬ 2 ∣ 5 ∧
      Domain NondivisibleExample.ring5 NondivisibleExample.seed5 ∧
      count NondivisibleExample.seed5 = 2 ∧
      ¬ PopulationProtocol.IsSafe (LabelFreeElimination.protocol (by decide) 1)
        NondivisibleExample.ring5 NondivisibleExample.seed5 id ∧
      PopulationProtocol.IsSafe (LabelFreeElimination.protocol (by decide) 1)
        NondivisibleExample.ring5
        (run (step (by decide) NondivisibleExample.ring5) NondivisibleExample.seed5 [3, 2]) id := by
  refine ⟨NondivisibleExample.nondivisible5,
    ⟨NondivisibleExample.seed5_global, K2PeacefulGlobal.seed5_peaceful⟩,
    seed5_true_count_deletion.1, ?_, K2PeacefulGlobal.seed5_two_edges_safe⟩
  intro hs
  have hc := isSafe_count_one (by decide) NondivisibleExample.ring5 NondivisibleExample.seed5 hs
  have ht := seed5_true_count_deletion.1
  omega

end K2FiniteSafeElimination

#check K2FiniteSafeElimination.safe_elimination
#check K2FiniteSafeElimination.final_semantic_tail
#check K2FiniteSafeEliminationExpected.semanticChargedPrefix_succ
#print axioms K2FiniteSafeEliminationCore.domain_step
#print axioms K2FiniteSafeEliminationCore.isSafe_iff_count_one
#print axioms K2FiniteSafeEliminationCore.observe_stopped_word
#print axioms K2FiniteSafeElimination.higher_denominator_exact
#print axioms K2FiniteSafeElimination.final_denominator_exact
#print axioms K2FiniteSafeElimination.whp_constant_exact
#print axioms K2FiniteSafeElimination.expected_constant_exact
#print axioms K2FiniteSafeElimination.first_safe_payload
#print axioms K2FiniteSafeElimination.stopped_success_iff_full_safe
#print axioms K2FiniteSafeElimination.final_two_endpoint_mass
#print axioms K2FiniteSafeElimination.final_semantic_tail
#print axioms K2FiniteSafeEliminationTail.count_whp_and_clock
#print axioms K2FiniteSafeEliminationExpected.unfinished_word_cost
#print axioms K2FiniteSafeEliminationExpected.chargedPrefix_le_exactTariff
#print axioms K2FiniteSafeElimination.safe_elimination
#print axioms K2FiniteSafeElimination.nondivisible_domain_witness
