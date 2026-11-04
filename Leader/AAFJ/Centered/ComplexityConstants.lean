import Leader.AAFJ.LeastNonDivisor

/-!
# Arithmetic constants for the conditional centered AAFJ theorem

This file proves only the deterministic arithmetic in the corrected theorem.
It deliberately does not assert the still-open state-uniform centered
coalescence or one-barrier stochastic hypotheses.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace ComplexityConstants

set_option autoImplicit false

/-- The complete exact-size family, including the two dedicated small rings,
retains the logarithmic carrier envelope. -/
theorem exactFamilyStateCount_le_log2 {n : Nat} (hn : 0 < n) :
    AAFJExactN.exactFamilyStateCount n ≤ 16 * Nat.log2 n + 32 :=
  AAFJExactN.exactFamilyStateCount_le_log2 hn

/-- Paper-level state-uniform one-barrier budget, conditional on the block and
terminal stopping-time theorems. -/
def oneBarrierBudget (n : Nat) : Nat :=
  512 * n ^ 3 + 72 * n ^ 2 + 9 * n

/-- Conservative physical horizon used by one fixed-rank trial.  The current
three-stage bind is expected to prove the stronger `12*n^2+2*n` horizon; this
larger value keeps the published restart constants stable by suffix padding. -/
def rankBlockHorizon (n : Nat) : Nat :=
  16 * n ^ 2 + 2 * n

/-- A denominator-`32` block repeated across at most `n` strict rank drops. -/
def rankDescentBudget (n : Nat) : Nat :=
  32 * n * rankBlockHorizon n

/-- Final `Phi = 1` sanitation and leader-production budget. -/
def terminalBudget (n : Nat) : Nat :=
  8 * n ^ 2 + 9 * n

theorem rankDescentBudget_eq (n : Nat) :
    rankDescentBudget n = 512 * n ^ 3 + 64 * n ^ 2 := by
  simp [rankDescentBudget, rankBlockHorizon, Nat.mul_add, Nat.pow_succ]
  calc
    32 * n * (16 * (n * n)) + 32 * n * (2 * n) =
        (32 * 16) * (n * n * n) + (32 * 2) * (n * n) := by ac_rfl
    _ = 512 * (n * n * n) + 64 * (n * n) := by rfl

/-- The displayed one-barrier polynomial is exactly the strict-rank restart
budget followed by the terminal `Phi = 1` budget. -/
theorem oneBarrierBudget_eq_rankDescent_add_terminal (n : Nat) :
    oneBarrierBudget n = rankDescentBudget n + terminalBudget n := by
  rw [rankDescentBudget_eq]
  simp [oneBarrierBudget, terminalBudget]
  omega

/-- All-state budget obtained after prepending a `3*n^3` centered coalescence
certificate. -/
def allStateBudget (n : Nat) : Nat :=
  3 * n ^ 3 + oneBarrierBudget n

theorem allStateBudget_eq (n : Nat) :
    allStateBudget n = 515 * n ^ 3 + 72 * n ^ 2 + 9 * n := by
  simp [allStateBudget, oneBarrierBudget]
  omega

/-- Explicit conditional composition seam: a uniform centered coalescence
certificate and a uniform one-barrier certificate add to the advertised
all-state budget. -/
theorem compose_uniform_budgets (n coalescence cleanup : Nat)
    (hcoalescence : coalescence ≤ 3 * n ^ 3)
    (hcleanup : cleanup ≤ oneBarrierBudget n) :
    coalescence + cleanup ≤ allStateBudget n := by
  exact Nat.add_le_add hcoalescence hcleanup

/-- The advertised `540*n^3` envelope is valid exactly on the large-ring
branch `n>=3`; equality occurs at its lower endpoint. -/
theorem allStateBudget_le_540_cube (n : Nat) (hn3 : 3 ≤ n) :
    allStateBudget n ≤ 540 * n ^ 3 := by
  have hthreeSquare : 3 * n ≤ n ^ 2 := by
    calc
      3 * n ≤ n * n := Nat.mul_le_mul_right n hn3
      _ = n ^ 2 := by simp [Nat.pow_two]
  have hnine : 9 * n ≤ 3 * n ^ 2 := by
    calc
      9 * n = 3 * (3 * n) := by omega
      _ ≤ 3 * n ^ 2 := Nat.mul_le_mul_left 3 hthreeSquare
  have hlower : 72 * n ^ 2 + 9 * n ≤ 75 * n ^ 2 := by omega
  have hthreeCube : 3 * n ^ 2 ≤ n ^ 3 := by
    calc
      3 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right (n ^ 2) hn3
      _ = n ^ 3 := by simp [Nat.pow_succ, Nat.mul_comm]
  have hcubic : 75 * n ^ 2 ≤ 25 * n ^ 3 := by
    calc
      75 * n ^ 2 = 25 * (3 * n ^ 2) := by omega
      _ ≤ 25 * n ^ 3 := Nat.mul_le_mul_left 25 hthreeCube
  rw [allStateBudget_eq]
  omega

theorem allStateBudget_three_eq : allStateBudget 3 = 540 * 3 ^ 3 := by
  decide

/-- Doubling a uniform expectation envelope gives the Markov half-failure
block length used by the restart tail. -/
theorem doubled_allStateBudget_le_1080_cube (n : Nat) (hn3 : 3 ≤ n) :
    2 * allStateBudget n ≤ 1080 * n ^ 3 := by
  have h := Nat.mul_le_mul_left 2 (allStateBudget_le_540_cube n hn3)
  calc
    2 * allStateBudget n ≤ 2 * (540 * n ^ 3) := h
    _ = 1080 * n ^ 3 := by omega

end ComplexityConstants
end CenteredRenewal
end AAFJPK
