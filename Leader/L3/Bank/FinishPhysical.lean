import Leader.L3.RenewalPreparationStage

/-!
BANK finish: one missing masked-reference repair
contract and the exact selected spatial coefficient gap.

No import from BankFinishStage, no changes to the leader repo.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The paper's prepared singleton repair bound, in a deliberately
rounded-up integer form, on the ORIGINAL valid, masked BANK chain.
This is a missing producer obligation, not a theorem.
In the installed BANK band q=ceilLogTwo n >=80 and s=ceilLogTwo q,
the repair ledger is STRICTLY smaller than (441*s+378)*n^2. -/
def BankFinishMaskedRepairBound {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ z : BankReferenceState ring hbank,
    BankPreparedAtSomeRoot ring hbank z →
    ∀ T : Nat,
      costNumerator
        (bankValidRootedReferenceData ring hbank).referenceNext
        (bankValidRootedReferenceData ring hbank).referenceStop z T ≤
      n ^ T *
        ((441 * ceilLogTwo (ceilLogTwo n) + 378) * n ^ 2)

/-- For every installed BANK advice q>=80, the reference finish
allowance exceeds the rounded paper repair bound by 113135*n^2.
This is arithmetic only; it does not prove the preceding Prop. -/
theorem bankFinishSpatialCoefficientGap (q : Nat) (hq : 80 ≤ q) :
    441 * ceilLogTwo q + 378 + 113135 =
      headlineReferenceFinishRate q := by
  have hnotSmall : ¬ q ≤ 32 := by omega
  have hspec : q ≤ 2 ^ ceilLogTwo q :=
    (ceilLogTwo_spec q (by omega : 2 ≤ q)).2
  have hs : 7 ≤ ceilLogTwo q := by
    by_cases hle : ceilLogTwo q ≤ 6
    · have hp : (2 : Nat) ^ ceilLogTwo q ≤ 2 ^ 6 :=
        Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) hle
      have h64 : (2 : Nat) ^ 6 = 64 := by decide
      rw [h64] at hp
      omega
    · omega
  have hnotSix : ¬ ceilLogTwo q = 6 := by omega
  unfold headlineReferenceFinishRate headlineReferenceRate
    headlineInheritedRate
  simp only [if_neg hnotSmall, if_neg hnotSix]
  omega

end L3.RenewalReferenceClock
