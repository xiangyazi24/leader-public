import Leader.Core.BalancedFailureRestart

/-!
# Geometric Bellman tail by exact restart blocks

This file upgrades the reciprocal finite-horizon Bellman tail to a geometric
tail when the Bellman potential is uniformly bounded.  The composition is an
exact scheduler-tree decomposition; no probabilistic independence premise is
used.
-/

namespace BellmanGeometricTail

open FiniteUniformStoppingTree

set_option autoImplicit false

/-- Exact semigroup law for finite uniform scheduler-tree sums. -/
theorem treeWeight_add_horizon
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (weight : StopNode S → Nat) :
    ∀ x T T',
      treeWeight step weight x (T + T') =
        treeWeight step
          (fun y => treeWeight step weight y T') x T := by
  intro x T T'
  induction T generalizing x with
  | zero => simp only [Nat.zero_add, treeWeight]
  | succ T ih =>
      rw [Nat.succ_add]
      simp only [treeWeight]
      exact ofFn_sum_eq _ _ (fun edge =>
        ih (stepNode step x edge))

/-- Split an active-leaf count at an arbitrary horizon boundary.  The right
side is the exact sum, over the depth-`T` frontier, of the active count of the
remaining suffix tree.  Terminal frontier nodes contribute zero. -/
theorem activeCount_add
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S) (T T' : Nat) :
    activeCount step x (T + T') =
      treeWeight step (fun y => activeCount step y T') x T := by
  simpa only [activeCount] using
    (treeWeight_add_horizon step activeWeight x T T')

/-- From any node, the active depth-`K` leaves are bounded by all `n^K`
scheduler words; at a terminal node both sides are zero. -/
theorem activeCount_le_pow_mul_activeWeight
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) :
    ∀ x K,
      activeCount step x K ≤ n ^ K * activeWeight x := by
  intro x K
  cases x with
  | active s =>
      have hpartition := node_count_partition step (.active s) K
      simp only [activeWeight, Nat.mul_one]
      omega
  | success =>
      simp [activeCount, treeWeight_success, activeWeight]
  | failure =>
      simp [activeCount, treeWeight_failure, activeWeight]

/-- Padding a horizon by `K` can create at most `n^K` continuations from each
currently active leaf. -/
theorem activeCount_add_le_pow_mul
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S) (T K : Nat) :
    activeCount step x (T + K) ≤
      n ^ K * activeCount step x T := by
  rw [activeCount_add step x T K]
  calc
    treeWeight step (fun y => activeCount step y K) x T ≤
        treeWeight step (fun y => n ^ K * activeWeight y) x T :=
      treeWeight_mono step
        (fun y => activeCount step y K)
        (fun y => n ^ K * activeWeight y)
        (fun y => activeCount_le_pow_mul_activeWeight step y K) x T
    _ = n ^ K * activeCount step x T := by
      simpa only [activeCount] using
        (treeWeight_mul_left step (n ^ K) activeWeight x T)

/-- Any reciprocal tail estimate remains true after padding to a larger
horizon, because the scheduler-space denominator grows by the same `n^K`
factor that can pad active leaves. -/
theorem factor_mul_activeCount_le_pow_of_horizon_le
    {S : Type} {n factor T U : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S)
    (hTU : T ≤ U)
    (hbase : factor * activeCount step x T ≤ n ^ T) :
    factor * activeCount step x U ≤ n ^ U := by
  obtain ⟨K, hU⟩ := Nat.exists_eq_add_of_le hTU
  subst U
  have hpad := activeCount_add_le_pow_mul step x T K
  calc
    factor * activeCount step x (T + K) ≤
        factor * (n ^ K * activeCount step x T) :=
      Nat.mul_le_mul_left factor hpad
    _ = n ^ K * (factor * activeCount step x T) := by
      ac_rfl
    _ ≤ n ^ K * n ^ T :=
      Nat.mul_le_mul_left (n ^ K) hbase
    _ = n ^ (T + K) := by
      rw [Nat.pow_add]
      ac_rfl

/-- Uniform one-block half-tail.  The reciprocal Bellman theorem is first
applied at horizon `2 * potential y`, then padded to `2 * B` using the uniform
bound on the potential. -/
theorem two_mul_activeCount_block_le
    {S : Type} {n B : Nat}
    (step : S → Fin n → StopNode S)
    (potential : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step 1 potential)
    (hB : ∀ x, potential x ≤ B)
    (hn : 0 < n) :
    ∀ y, 2 * activeCount step y (2 * B) ≤ n ^ (2 * B) := by
  intro y
  cases y with
  | success =>
      simp [activeCount, treeWeight_success, activeWeight]
  | failure =>
      simp [activeCount, treeWeight_failure, activeWeight]
  | active s =>
      have hpositive : 0 < potential (.active s) := by
        by_cases hz : potential (.active s) = 0
        · have hbellman := hsuper.2.2 s
          rw [hz] at hbellman
          simp only [Nat.one_mul, Nat.mul_zero] at hbellman
          omega
        · exact Nat.pos_of_ne_zero hz
      have hreciprocal :=
        BalancedFailureRestart.factor_mul_activeCount_le_pow_of_natSuperSolution
          step potential hsuper (.active s) hpositive (factor := 2)
      have hle :
          2 * potential (.active s) ≤ 2 * B :=
        Nat.mul_le_mul_left 2 (hB (.active s))
      exact factor_mul_activeCount_le_pow_of_horizon_le
        step (.active s) hle hreciprocal

/-- Exact one-block contraction from an arbitrary prefix horizon.  This is the
Markov/restart step on the finite scheduler tree. -/
theorem two_mul_activeCount_add_block_le
    {S : Type} {n L : Nat}
    (step : S → Fin n → StopNode S)
    (hblock : ∀ y, 2 * activeCount step y L ≤ n ^ L)
    (x : StopNode S) (T : Nat) :
    2 * activeCount step x (T + L) ≤
      n ^ L * activeCount step x T := by
  rw [activeCount_add step x T L]
  have hpoint :
      ∀ y : StopNode S,
        2 * activeCount step y L ≤ n ^ L * activeWeight y := by
    intro y
    cases y with
    | active s =>
        simpa [activeWeight] using hblock (.active s)
    | success =>
        simp [activeCount, treeWeight_success, activeWeight]
    | failure =>
        simp [activeCount, treeWeight_failure, activeWeight]
  calc
    2 * treeWeight step (fun y => activeCount step y L) x T =
        treeWeight step (fun y => 2 * activeCount step y L) x T := by
      symm
      exact treeWeight_mul_left step 2
        (fun y => activeCount step y L) x T
    _ ≤ treeWeight step (fun y => n ^ L * activeWeight y) x T :=
      treeWeight_mono step
        (fun y => 2 * activeCount step y L)
        (fun y => n ^ L * activeWeight y)
        hpoint x T
    _ = n ^ L * activeCount step x T := by
      simpa only [activeCount] using
        (treeWeight_mul_left step (n ^ L) activeWeight x T)

/-- Restart the reciprocal half-tail every `2*B` scheduler interactions.  After
`k` aligned blocks, at most a `2^-k` fraction of scheduler words remain
active, stated without division. -/
theorem geometric_tail
    {S : Type} {n B : Nat}
    (step : S → Fin n → StopNode S)
    (potential : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step 1 potential)
    (hB : ∀ x, potential x ≤ B)
    (hn : 0 < n)
    (state : StopNode S) (k : Nat) :
    2 ^ k * activeCount step state (k * (2 * B)) ≤
      n ^ (k * (2 * B)) := by
  have hblock :
      ∀ y : StopNode S,
        2 * activeCount step y (2 * B) ≤ n ^ (2 * B) :=
    two_mul_activeCount_block_le step potential hsuper hB hn
  induction k with
  | zero =>
      cases state <;>
        simp [activeCount, treeWeight, activeWeight]
  | succ k ih =>
      have hcontract :=
        two_mul_activeCount_add_block_le step hblock state
          (k * (2 * B))
      calc
        2 ^ Nat.succ k *
            activeCount step state (Nat.succ k * (2 * B)) =
          2 ^ k *
            (2 * activeCount step state
              (k * (2 * B) + 2 * B)) := by
                rw [Nat.pow_succ, Nat.succ_mul k (2 * B)]
                ac_rfl
        _ ≤ 2 ^ k *
            (n ^ (2 * B) *
              activeCount step state (k * (2 * B))) :=
          Nat.mul_le_mul_left (2 ^ k) hcontract
        _ = n ^ (2 * B) *
            (2 ^ k * activeCount step state (k * (2 * B))) := by
          ac_rfl
        _ ≤ n ^ (2 * B) * n ^ (k * (2 * B)) :=
          Nat.mul_le_mul_left (n ^ (2 * B)) ih
        _ = n ^ (Nat.succ k * (2 * B)) := by
          rw [Nat.succ_mul k (2 * B), Nat.pow_add]
          ac_rfl

end BellmanGeometricTail

#print axioms BellmanGeometricTail.treeWeight_add_horizon
#print axioms BellmanGeometricTail.activeCount_add
#print axioms BellmanGeometricTail.activeCount_le_pow_mul_activeWeight
#print axioms BellmanGeometricTail.activeCount_add_le_pow_mul
#print axioms BellmanGeometricTail.factor_mul_activeCount_le_pow_of_horizon_le
#print axioms BellmanGeometricTail.two_mul_activeCount_block_le
#print axioms BellmanGeometricTail.two_mul_activeCount_add_block_le
#print axioms BellmanGeometricTail.geometric_tail
