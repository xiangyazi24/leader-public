import Leader.Wu.RaceEntrance.ModerateMass
import Leader.Wu.RaceEntrance.LongMass

set_option autoImplicit false

open FiniteUniformStoppingTree LDTwoGapFrame LDSinkTwoGapNoResetKernel
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapRaceEntranceModerateMass LDSinkTwoGapRaceEntranceLongMass
open LDSinkTwoGapRaceEntranceLocalizedFinish

namespace LDSinkTwoGapRaceEntranceUniformAll

variable {n psi : Nat}

/-- An absolute constant; it is independent of the ring and both gap lengths. -/
def deletionDenominator : Nat := 32 * 2 ^ moderateCollapseBudget

theorem deletion_denominator_pos : 0 < deletionDenominator :=
  Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

private theorem moderate_denominator_le :
    16 * 2 ^ moderateCollapseBudget ≤ deletionDenominator :=
  Nat.mul_le_mul_right (2 ^ moderateCollapseBudget) (by decide : 16 ≤ 32)

private theorem long_denominator_le : longDenominator ≤ deletionDenominator := by
  rw [long_denominator_eq]
  exact Nat.mul_le_mul_left 32 (Nat.pow_le_pow_right (by decide)
    (by decide : finishCollapseBudget ≤ moderateCollapseBudget))

/-- Unconditional physical pair-span progress: every actual legal gap pair
has constant deletion mass under the original uniform K2 scheduler by
`30*n*(a+b)`.  There is no ratio, initial shield, phase, entrance, Bellman,
transfer, or independently sampled recovery hypothesis. -/
theorem gapPair_uniform_deletion_mass (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) :
    n ^ (30 * n * (F.recovery.d + F.attack.d)) ≤ deletionDenominator *
      successCount (physicalBlockStep hpsi F) (.active b) (30 * n * (F.recovery.d + F.attack.d)) := by
  by_cases hm : F.attack.d ≤ 16 * F.recovery.d + 1
  · have h := gapPair_moderate_uniform_at_span hpsi F b hg hm
    exact Nat.le_trans h (Nat.mul_le_mul_right _ moderate_denominator_le)
  · have hl : 16 * F.recovery.d + 2 ≤ F.attack.d := by omega
    have h := gapPair_long_uniform_at_span hpsi F b hg hl
    exact Nat.le_trans h (Nat.mul_le_mul_right _ long_denominator_le)

end LDSinkTwoGapRaceEntranceUniformAll

#print axioms LDSinkTwoGapRaceEntranceUniformAll.deletion_denominator_pos
#print axioms LDSinkTwoGapRaceEntranceUniformAll.gapPair_uniform_deletion_mass
