import Leader.Core.BellmanGeometricTail

namespace BellmanWhp

open FiniteUniformStoppingTree

set_option autoImplicit false

/-- If the geometric coefficient `2^k` dominates the scheduler degree `n`,
the active mass is at most a `1/n` fraction of the depth-`k*(2*B)` scheduler
space. -/
theorem whp_tail
    {S : Type} {n B : Nat}
    (step : S → Fin n → StopNode S)
    (potential : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step 1 potential)
    (hB : ∀ x, potential x ≤ B)
    (hn : 0 < n)
    (state : StopNode S) (k : Nat)
    (hk : n ≤ 2 ^ k) :
    n * activeCount step state (k * (2 * B)) ≤
      n ^ (k * (2 * B)) := by
  have hgeo :=
    BellmanGeometricTail.geometric_tail
      step potential hsuper hB hn state k
  exact Nat.le_trans
    (Nat.mul_le_mul_right
      (activeCount step state (k * (2 * B))) hk)
    hgeo

/-- Taking `k = floor(log₂ n) + 1` makes `2^k` strictly larger than every
positive `n`, hence gives the standard `1/n` active-tail bound. -/
theorem whp_log
    {S : Type} {n B : Nat}
    (step : S → Fin n → StopNode S)
    (potential : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step 1 potential)
    (hB : ∀ x, potential x ≤ B)
    (hn : 0 < n)
    (state : StopNode S) :
    n * activeCount step state
        ((Nat.log2 n + 1) * (2 * B)) ≤
      n ^ ((Nat.log2 n + 1) * (2 * B)) := by
  have hne : n ≠ 0 := Nat.ne_of_gt hn
  have hlt : n < 2 ^ (Nat.log2 n + 1) :=
    (Nat.log2_lt hne).1 (by omega)
  exact whp_tail step potential hsuper hB hn state
    (Nat.log2 n + 1) (Nat.le_of_lt hlt)

/-- For every factor at least two, the no-failure reciprocal tail gives a
positive success-mass lower bound without division. -/
theorem success_mass_ge_factor
    {S : Type} {n factor : Nat}
    (step : S → Fin n → StopNode S)
    (potential : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step 1 potential)
    (hnoFailure : ∀ state edge, step state edge ≠ .failure)
    (state : S) (hpositive : 0 < potential (.active state))
    (hfactor : 2 ≤ factor) :
    n ^ (factor * potential (.active state)) ≤
      factor * successCount step (.active state)
        (factor * potential (.active state)) := by
  have hsuccess :=
    BalancedFailureRestart.pred_mul_pow_le_factor_mul_successCount
      step potential hsuper hnoFailure state hpositive
      (factor := factor)
  have hcoeff : 1 ≤ factor - 1 := by omega
  have hscale :
      n ^ (factor * potential (.active state)) ≤
        (factor - 1) * n ^ (factor * potential (.active state)) := by
    have hmul := Nat.mul_le_mul_right
      (n ^ (factor * potential (.active state))) hcoeff
    simpa using hmul
  exact Nat.le_trans hscale hsuccess

/-- At horizon `2 * Φ`, at least half of all scheduler words have succeeded,
stated as the exact division-free mass inequality. -/
theorem success_mass_ge
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (potential : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step 1 potential)
    (hnoFailure : ∀ state edge, step state edge ≠ .failure)
    (state : S) (hpositive : 0 < potential (.active state)) :
    n ^ (2 * potential (.active state)) ≤
      2 * successCount step (.active state)
        (2 * potential (.active state)) := by
  simpa using
    (success_mass_ge_factor (factor := 2)
      step potential hsuper hnoFailure state hpositive (by omega))

end BellmanWhp

#print axioms BellmanWhp.whp_tail
#print axioms BellmanWhp.whp_log
#print axioms BellmanWhp.success_mass_ge_factor
#print axioms BellmanWhp.success_mass_ge
