import Leader.Wu.Elimination.ArbitraryInputGoal

/-!
# First two physical accounting intervals from arbitrary UCell input

Nearest support and separation are acquired using their independently proved
original-scheduler estimates. Extinction is retained at every handoff.
-/

namespace K2ArbitraryElimination

open StateBoundUnifiedCell LDSinkBoundedKernel LabelFreeElimination K2FiniteProgress
  FiniteUniformStoppingTree LeaderCountDyadicTail FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

variable {n ψ κ : Nat}

/-- Four logarithmic mark blocks pay the initial union over n old live marks. -/
def nearestTime (n : Nat) : Nat := (4 * (Nat.log2 n + 1)) * (2 * (n * n))

/-- Three logarithmic separation blocks give miss mass at most n⁻³. -/
def separationTime (n : Nat) : Nat := (3 * (Nat.log2 n + 1)) * (2 * n * n)

/-- Actual arbitrary-input nearest support or physical extinction. -/
theorem nearest_tail (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) :
    n ^ 3 * wordSum (AdjacentLeaderElimination.step hψ ring)
      (miss (K2NearestSupportEntry.Entry ring)) C (nearestTime n) ≤ n ^ nearestTime n :=
  K2NearestSupportEntry.arbitrary_entry_polynomial_tail hψ hn ring C 3

/-- Literal separation miss on every physical input, with its actual clock. -/
theorem separation_three_tail (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) :
    n ^ 3 * wordSum (AdjacentLeaderElimination.step hψ ring)
      (AdjacentSeparationEntry.miss ring) C (separationTime n) ≤ n ^ separationTime n := by
  have hlog : n ≤ 2 ^ (Nat.log2 n + 1) :=
    Nat.le_of_lt ((Nat.log2_lt (Nat.ne_of_gt ring.hn)).1 (by omega))
  have hpow : n ^ 3 ≤ 2 ^ (3 * (Nat.log2 n + 1)) := by
    calc
      n ^ 3 ≤ (2 ^ (Nat.log2 n + 1)) ^ 3 := Nat.pow_le_pow_left hlog _
      _ = _ := by rw [← Nat.pow_mul, Nat.mul_comm]
  exact Nat.le_trans (Nat.mul_le_mul_right _ hpow)
    (AdjacentSeparationEntry.separation_tail hψ ring C (3 * (Nat.log2 n + 1)))

/-- When nearest entry already holds, attaining separation produces the
actual Prepared predicate. Both facts are evaluated on the current endpoint. -/
theorem preparedMiss_le_separation (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hC : K2NearestSupportEntry.Entry ring C) :
    miss (Prepared ring) C ≤ AdjacentSeparationEntry.miss ring C := by
  classical
  by_cases hs : AdjacentSeparationEntry.Separated ring C
  · have hp := entry_separated_prepared ring C hC hs
    simp [miss, AdjacentSeparationEntry.miss, hp, hs]
  · simpa only [AdjacentSeparationEntry.miss, if_neg hs] using miss_le_one (Prepared ring) C

/-- Separation consumes the exact nearest-entry endpoint and every suffix. -/
theorem prepared_after_entry_tail (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : K2NearestSupportEntry.Entry ring C) :
    n ^ 3 * wordSum (AdjacentLeaderElimination.step hψ ring) (miss (Prepared ring)) C
        (separationTime n) ≤ n ^ separationTime n := by
  have hmono := wordSum_mono_on (AdjacentLeaderElimination.step hψ ring)
    (K2NearestSupportEntry.Entry ring) (K2NearestSupportEntry.entry_step hψ hn ring)
    (miss (Prepared ring)) (AdjacentSeparationEntry.miss ring)
    (preparedMiss_le_separation ring) (separationTime n) C hC
  exact Nat.le_trans (Nat.mul_le_mul_left _ hmono) (separation_three_tail hψ ring C)

/-- First two accounting intervals, without changing the physical row. -/
theorem arbitrary_prepared_tail (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) :
    n ^ 3 * wordSum (AdjacentLeaderElimination.step hψ ring) (miss (Prepared ring)) C
        (nearestTime n + separationTime n) ≤ 2 * n ^ (nearestTime n + separationTime n) := by
  exact compose_miss (AdjacentLeaderElimination.step hψ ring)
    (K2NearestSupportEntry.Entry ring) (Prepared ring) (nearestTime n) (separationTime n)
    (n ^ 3) 1 1 C (by simpa only [Nat.one_mul] using nearest_tail hψ hn ring C)
    (fun D hD => by simpa only [Nat.one_mul] using prepared_after_entry_tail hψ hn ring D hD)

end K2ArbitraryElimination

#print axioms K2ArbitraryElimination.nearest_tail
#print axioms K2ArbitraryElimination.prepared_after_entry_tail
#print axioms K2ArbitraryElimination.arbitrary_prepared_tail
