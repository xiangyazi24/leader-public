import Leader.L3.Bank.InheritedCensus

/-!
The BANK band forces q >= 80, so the headline inherited-authority
coefficient equals the spatial retirement coefficient 116 b + 232
(repair.tex 615, 701-705).
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal

set_option autoImplicit false

/-- The BANK branch forces q>=80, hence ceilLogTwo q>=7:
the headline inherited-authority coefficient is EXACTLY the
spatial retirement coefficient, not merely a larger allowance. -/
theorem bankInheritedHeadlineRateBankEq
    (q : Nat)
    (hbank : (compileAdvice q).useSmall = false) :
    headlineInheritedRate q =
      116 * (compileAdvice q).b + 232 := by
  have hdec : (decide (q ≤ 79) : Bool) = false := by
    change (decide (q ≤ 79) : Bool) = false at hbank
    exact hbank
  have hq : 80 ≤ q := by
    by_cases hh : q ≤ 79
    · simp [hh] at hdec
    · omega
  have hq32 : ¬ q ≤ 32 := by omega
  have hspec : q ≤ 2 ^ ceilLogTwo q :=
    (ceilLogTwo_spec q (by omega)).2
  have hlarge : 7 ≤ ceilLogTwo q := by
    by_cases hs : ceilLogTwo q ≤ 6
    · have hp : (2 : Nat) ^ ceilLogTwo q ≤ 2 ^ 6 :=
        Nat.pow_le_pow_right (by omega) hs
      have hsmallPower : (2 : Nat) ^ 6 = 64 := by decide
      omega
    · omega
  have hnotSix : ¬ ceilLogTwo q = 6 := by omega
  have hb : (compileAdvice q).b = ceilLogTwo q + 11 := by
    change max 2 (ceilLogTwo q) + 11 =
      ceilLogTwo q + 11
    omega
  unfold headlineInheritedRate
  rw [if_neg hq32, if_neg hnotSix, hb]

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInheritedHeadlineRateBankEq
