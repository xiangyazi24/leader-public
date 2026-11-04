import Leader.Wu.Birth.ReacquireReentryMass


set_option autoImplicit false
set_option Elab.async false


namespace BirthB4TwoPhaseComplexity


open BirthB1ReacquireReentryMass


variable {n kappa : Nat}


/-- The Carrier quarter-budget logarithm. -/
def carrierLog (n : Nat) : Nat :=
  Nat.log2 n + 3


/-- Closed form of the current Carrier-trial budget:
`renewalK 128 (log2 n + 3) * (kappa + 1)`. -/
def carrierTrials (n kappa : Nat) : Nat :=
  256 * (carrierLog n * (kappa + 1))


/-- Check that the closed form is exactly the definition already on main. -/
theorem carrierTrials_eq_fallback (n kappa : Nat) :
    carrierTrials n kappa = fallbackCarrierTrials n kappa := by
  simp [carrierTrials, carrierLog, fallbackCarrierTrials,
    quarterBudgetK, BirthPhaseGenericRenewal.renewalK,
    BirthPhaseWait2BlockProgress.Q,
    BirthPhaseWait2BlockProgress.R, Nat.mul_assoc]


/-- The existing physical Carrier block is exactly six scheduler letters per
agent. -/
theorem carrierBlock_eq_six_n (n : Nat) :
    BirthPhaseWait2BlockProgress.L n = 6 * n := by
  rw [L_eq_reentry_add_local3]
  unfold reentryHorizon local3Horizon
  omega


/-- The old accounting: every possible Reacquire excursion receives its
own logarithmically amplified failure budget. -/
def perExcursionReacquireBlocks (n kappa : Nat) : Nat :=
  16 * (Nat.log2 (n * (carrierTrials n kappa + 1)) + 3)


/-- Exact closed-form horizon of the conservative per-excursion accounting. -/
def perExcursionHorizon (n kappa : Nat) : Nat :=
  carrierTrials n kappa * (6 * n) +
    carrierTrials n kappa * perExcursionReacquireBlocks n kappa *
      (16 * n * n)


/-- Aggregate Reacquire budget.  The `M+1` exits are paid for together; the
extra `8*s` trials are the fixed Chernoff slack. -/
def aggregateReacquireBlocks (n kappa : Nat) : Nat :=
  16 * (carrierTrials n kappa + 1 + 8 * carrierLog n)


/-- Phase-adaptive first-cap horizon after replacing the per-excursion union
bound by one aggregate Reacquire lower-tail bound. -/
def aggregateTwoPhaseHorizon (n kappa : Nat) : Nat :=
  carrierTrials n kappa * (6 * n) +
    aggregateReacquireBlocks n kappa * (16 * n * n)


/-- Explicit target-shape envelope.  Algebraically this is
`68352 * n^2 * (log2 n + 3) * (kappa + 1)`; it is left factorized so the proof
uses only monotonicity of Nat multiplication. -/
def targetShape (n kappa : Nat) : Nat :=
  carrierTrials n kappa * (2 * n * n) +
    (16 * (265 * (carrierLog n * (kappa + 1)))) * (16 * n * n)


/-- The aggregate budget has the required `n^2 log n (kappa+1)` shape with an
explicit constant, uniformly for every `n >= 4`. -/
theorem aggregateTwoPhaseHorizon_le_targetShape
    (hn : 4 <= n) :
    aggregateTwoPhaseHorizon n kappa <= targetShape n kappa := by
  have h6base : 6 <= 2 * n := by
    omega
  have h6 : 6 * n <= 2 * n * n := by
    exact Nat.mul_le_mul_right n h6base


  have hs : 1 <= carrierLog n := by
    unfold carrierLog
    omega
  have hk : 1 <= kappa + 1 := by
    omega
  have hsle :
      carrierLog n <= carrierLog n * (kappa + 1) := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (carrierLog n) hk
  have hone :
      1 <= carrierLog n * (kappa + 1) :=
    Nat.le_trans hs hsle


  have hentry :
      carrierTrials n kappa + 1 + 8 * carrierLog n <=
        265 * (carrierLog n * (kappa + 1)) := by
    unfold carrierTrials
    omega


  unfold aggregateTwoPhaseHorizon targetShape
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_left (carrierTrials n kappa) h6
  · apply Nat.mul_le_mul_right (16 * n * n)
    unfold aggregateReacquireBlocks
    exact Nat.mul_le_mul_left 16 hentry


/-! Small closed arithmetic checks. -/


theorem aggregate_small_4_0 :
    aggregateTwoPhaseHorizon 4 0 <= targetShape 4 0 := by
  decide


theorem aggregate_small_4_3 :
    aggregateTwoPhaseHorizon 4 3 <= targetShape 4 3 := by
  decide


theorem aggregate_small_5_2 :
    aggregateTwoPhaseHorizon 5 2 <= targetShape 5 2 := by
  decide


end BirthB4TwoPhaseComplexity


#print axioms BirthB4TwoPhaseComplexity.carrierTrials_eq_fallback
#print axioms BirthB4TwoPhaseComplexity.carrierBlock_eq_six_n
#print axioms BirthB4TwoPhaseComplexity.aggregateTwoPhaseHorizon_le_targetShape
#print axioms BirthB4TwoPhaseComplexity.aggregate_small_4_0
#print axioms BirthB4TwoPhaseComplexity.aggregate_small_4_3
#print axioms BirthB4TwoPhaseComplexity.aggregate_small_5_2
