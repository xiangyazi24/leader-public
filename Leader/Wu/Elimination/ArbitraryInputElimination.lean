import Leader.Wu.Elimination.ArbitraryInputPreparation
import Leader.Wu.Elimination.ArbitraryInputSignalEntry
import Leader.Wu.Elimination.ArbitraryInputExpectedCost

/-!
# Arbitrary-input elimination/collision component: safety or extinction

For n >= 2, every existing UCell configuration reaches actual semantic IsSafe
or physical count zero with nonentry mass at most 1/n by B interactions.
Here B <= (40 + 3*K)n² floor(log₂ n), where K is the published safe-elimination
constant. All finite raw prefixes have expected first-target cost at most 2B.
The real transition is unchanged throughout every word; the four intervals
are proof accounting only. No birth-enabled self-stabilization is asserted.
-/

namespace K2ArbitraryElimination

open StateBoundUnifiedCell LDSinkBoundedKernel LabelFreeElimination K2FiniteProgress
  FiniteUniformStoppingTree LeaderCountDyadicTail FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

variable {n ψ κ : Nat}

/-- The four deterministic accounting intervals on one unchanged process. -/
def horizon (n : Nat) : Nat := nearestTime n + separationTime n + signalTime n +
  3 * K2FiniteSafeEliminationTail.safeHorizon n

/-- Explicit O(n² log n) coefficient, using the frozen actual service constant. -/
def componentConstant : Nat := 40 + 3 * K2FiniteSafeEliminationTail.whpConstant

/-- Literal semantic-or-extinction failure numerator on full physical words. -/
noncomputable def failureNumerator (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T
    (fun es => miss (Goal hψ ring) (run (AdjacentLeaderElimination.step hψ ring) C es))

/-- Literal physical first-target cost, including unfinished finite prefixes. -/
noncomputable def rawWordCost (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n)) : Nat :=
  costWord (AdjacentLeaderElimination.step hψ ring) (Goal hψ ring) C es

theorem failureNumerator_eq (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) :
    failureNumerator hψ ring C T =
      wordSum (AdjacentLeaderElimination.step hψ ring) (miss (Goal hψ ring)) C T :=
  K2FiniteSafeEliminationExpected.wordSum_run _ _ C T

/-- All four actual entry estimates are now supplied, with no remaining
mass, invariant-producer, readiness, or phase-distribution hypothesis. -/
theorem arbitrary_goal_four_tail (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) :
    n ^ 3 * wordSum (AdjacentLeaderElimination.step hψ ring) (miss (Goal hψ ring)) C
      (horizon n) ≤ 4 * n ^ horizon n := by
  have hready := compose_miss (AdjacentLeaderElimination.step hψ ring)
    (Prepared ring) (Ready hψ ring) (nearestTime n + separationTime n) (signalTime n)
    (n ^ 3) 2 1 C (arbitrary_prepared_tail hψ hn ring C)
    (fun D hD => by simpa only [Nat.one_mul] using prepared_ready_tail hψ hn ring D hD)
  exact compose_miss (AdjacentLeaderElimination.step hψ ring)
    (Ready hψ ring) (Goal hψ ring) (nearestTime n + separationTime n + signalTime n)
    (3 * K2FiniteSafeEliminationTail.safeHorizon n) (n ^ 3) 3 1 C hready
    (fun D hD => by simpa only [Nat.one_mul] using ready_goal_tail hψ hn ring D hD)

/-- Since n² >= 4, the four n⁻³ failure allowances sum to at most n⁻¹. -/
theorem arbitrary_goal_whp (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) :
    n * wordSum (AdjacentLeaderElimination.step hψ ring) (miss (Goal hψ ring)) C
      (horizon n) ≤ n ^ horizon n := by
  have h4 : 4 ≤ n * n := Nat.mul_le_mul hn hn
  have h := Nat.le_trans (arbitrary_goal_four_tail hψ hn ring C)
    (Nat.mul_le_mul_right (n ^ horizon n) h4)
  have he : n ^ 3 = (n * n) * n := by simp [Nat.pow_succ]
  rw [he, Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_left h (Nat.mul_pos ring.hn ring.hn)

/-- A uniform actual half-success block on all starting configurations. -/
theorem arbitrary_goal_half (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) :
    2 * wordSum (AdjacentLeaderElimination.step hψ ring) (miss (Goal hψ ring)) C
      (horizon n) ≤ n ^ horizon n :=
  Nat.le_trans (Nat.mul_le_mul_right _ hn) (arbitrary_goal_whp hψ hn ring C)

/-- The accounting block always contains a positive number of raw interactions. -/
theorem horizon_pos (n : Nat) (hn : 0 < n) : 0 < horizon n := by
  have h : 0 < nearestTime n := Nat.mul_pos
    (Nat.mul_pos (by decide : 0 < (4 : Nat)) (Nat.succ_pos _))
    (Nat.mul_pos (by decide : 0 < (2 : Nat)) (Nat.mul_pos hn hn))
  unfold horizon
  omega

private theorem clock_algebra (K n L : Nat) :
    (4 + 3 + 3) * ((2 * (n * n)) * (2 * L)) + 3 * (K * n * n * L) =
      (40 + 3 * K) * n * n * L := by
  change 10 * ((2 * (n * n)) * (2 * L)) + 3 * (K * n * n * L) =
    (40 + 3 * K) * n * n * L
  simp only [Nat.add_mul]
  rw [show (40 : Nat) = 10 * 2 * 2 from rfl]
  ac_rfl

/-- A concrete logarithmic upper bound on the complete physical clock. -/
theorem horizon_le (n : Nat) (hn : 2 ≤ n) :
    horizon n ≤ componentConstant * n * n * Nat.log2 n := by
  have hl := (log_parameters n hn).1
  have hlog : Nat.log2 n + 1 ≤ 2 * Nat.log2 n := by omega
  calc
    horizon n = (4 + 3 + 3) * ((2 * (n * n)) * (Nat.log2 n + 1)) +
        3 * K2FiniteSafeEliminationTail.safeHorizon n := by
      unfold horizon nearestTime separationTime signalTime
      rw [Nat.add_mul, Nat.add_mul]
      ac_rfl
    _ ≤ (4 + 3 + 3) * ((2 * (n * n)) * (2 * Nat.log2 n)) +
        3 * K2FiniteSafeEliminationTail.safeHorizon n :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlog)) _
    _ = componentConstant * n * n * Nat.log2 n :=
      clock_algebra K2FiniteSafeEliminationTail.whpConstant n (Nat.log2 n)

/-- Every finite prefix pays at most two complete accounting blocks in
expectation, including all words still unfinished at its final symbol. -/
theorem arbitrary_expected_prefix (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) :
    FixedSpanRenewalPayload.wordSum n T (rawWordCost hψ ring C) ≤ n ^ T * (2 * horizon n) :=
  cost_le_two_blocks (AdjacentLeaderElimination.step hψ ring) (Goal hψ ring)
    (goal_step hψ ring) (horizon n) (horizon_pos n ring.hn) (arbitrary_goal_half hψ hn ring) T C

/-- Full arbitrary-input component theorem, in literal raw-word numerators. -/
theorem arbitrary_elimination (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) :
    n * failureNumerator hψ ring C (horizon n) ≤ n ^ horizon n ∧
      ∀ T, FixedSpanRenewalPayload.wordSum n T (rawWordCost hψ ring C) ≤
        n ^ T * (2 * horizon n) := by
  constructor
  · rw [failureNumerator_eq]
    exact arbitrary_goal_whp hψ hn ring C
  · exact arbitrary_expected_prefix hψ hn ring C

/-- An explicit O(n² log n) bound for every finite-prefix expected cost. -/
theorem arbitrary_expected_log (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) :
    FixedSpanRenewalPayload.wordSum n T (rawWordCost hψ ring C) ≤
      n ^ T * ((2 * componentConstant) * n * n * Nat.log2 n) := by
  have h := Nat.mul_le_mul_left 2 (horizon_le n hn)
  have he : 2 * (componentConstant * n * n * Nat.log2 n) =
      (2 * componentConstant) * n * n * Nat.log2 n := by simp only [Nat.mul_assoc]
  rw [he] at h
  exact Nat.le_trans (arbitrary_expected_prefix hψ hn ring C T) (Nat.mul_le_mul_left _ h)

/-- Restart on the actual physical endpoint gives any fixed polynomial
failure exponent c at c times the same O(n² log n) accounting block. -/
theorem arbitrary_polynomial_tail (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (c : Nat) :
    n ^ c * failureNumerator hψ ring C (c * horizon n) ≤ n ^ (c * horizon n) := by
  rw [failureNumerator_eq]
  exact repeat_miss (AdjacentLeaderElimination.step hψ ring) (Goal hψ ring) (fun _ => True)
    (fun _ _ _ => True.intro) (goal_step hψ ring) (horizon n) n
    (fun D _ => arbitrary_goal_whp hψ hn ring D) C True.intro c

/-- The singleton case uses the literal aliasing row and retains extinction. -/
theorem singleton_goal (hψ : 0 < ψ) (ring : DirectedRing 1)
    (C : Fin 1 → UCell ψ κ) (e : Fin 1) :
    Goal hψ ring (AdjacentLeaderElimination.step hψ ring C e) :=
  Or.inr (K2NearestSupportEntry.singleton_count_zero hψ ring C e)

end K2ArbitraryElimination

#print axioms K2ArbitraryElimination.arbitrary_goal_four_tail
#print axioms K2ArbitraryElimination.arbitrary_goal_whp
#print axioms K2ArbitraryElimination.horizon_le
#print axioms K2ArbitraryElimination.arbitrary_expected_prefix
#print axioms K2ArbitraryElimination.arbitrary_elimination
#print axioms K2ArbitraryElimination.arbitrary_expected_log
#print axioms K2ArbitraryElimination.arbitrary_polynomial_tail
#print axioms K2ArbitraryElimination.singleton_goal
