import Leader.L3.Grant.ShortCover

/-!
# G17: the expected success time on the finite advice branch (C.22--C.25)

From every purified, leaderless, grant-free configuration of the finite
branch, the expected number of physical interactions until
`headlineGrantReady ∨ headlineGeneratedTarget` is at most

`H(n) + (2 (2^K + 1) + n (K - 1) + 1) / 2`,

`H(n) = sum_{k<n} ceil(n/(k+1))` the coupon-collector term and
`2^K + 1 + n(K-1)/2` the finite counter bound (C.22).
-/

namespace L3

open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- **The physical cost bound on the finite branch.**

Consumer: `grantShortExpectedHitting`. -/
theorem grantShortCostBound {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (C : HeadlineConfiguration n) (hp : headlinePurified ring C) :
    ∀ T, costNumerator (headlinePhysicalNext ring)
        (fun D => headlineGrantReady ring D ∨
          headlineGeneratedTarget ring D) C T ≤
      n ^ T * (shortHarm n n +
        (2 * (2 ^ (compileAdvice (ceilLogTwo n)).K + 1) +
          n * ((compileAdvice (ceilLogTwo n)).K - 1) + 1) / 2) := by
  intro T
  have hq3 : 3 ≤ ceilLogTwo n := by
    by_cases h : 3 ≤ ceilLogTwo n
    · exact h
    · have hspec := (ceilLogTwo_spec n (by omega)).2
      have hle : ceilLogTwo n ≤ 2 := by omega
      have hp2 := Nat.pow_le_pow_right (by decide : 0 < 2) hle
      have h4 : (2 : Nat) ^ 2 = 4 := by decide
      omega
  have hk := compileAdvice_K_lt_kStar (ceilLogTwo n) hq3 hsmall
  have hK0 : 0 < (compileAdvice (ceilLogTwo n)).K := by
    change 0 < 2 * ceilLogTwo n + (compileAdvice (ceilLogTwo n)).kappa
    omega
  have h1 := grantShortPhysicalCostLe ring hn hsmall C hp T
  have h2 := shortAbsCost ring (by omega)
    (compileAdvice (ceilLogTwo n)).K hk hK0 (shortSmalls C) T
  exact Nat.le_trans h1 h2

/-- **The expected hitting time on the finite branch.**

Consumer: `grantLeaderlessShortClause` (GrantLeaderlessShort.lean). -/
theorem grantShortExpectedHitting {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (C : HeadlineConfiguration n) (hp : headlinePurified ring C) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (headlinePhysicalNext ring)
      (fun D => headlineGrantReady ring D ∨ headlineGeneratedTarget ring D)
      C ((shortHarm n n +
        (2 * (2 ^ (compileAdvice (ceilLogTwo n)).K + 1) +
          n * ((compileAdvice (ceilLogTwo n)).K - 1) + 1) / 2 : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (headlinePhysicalNext ring) _ (by omega : 0 < n) C _).2
  exact grantShortCostBound ring hn hsmall C hp

end L3

#print axioms L3.grantShortCostBound
#print axioms L3.grantShortExpectedHitting
