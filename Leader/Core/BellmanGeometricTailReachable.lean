import Leader.Core.BellmanGeometricTail

/-!
# Geometric Bellman tails with a reachable-state potential bound

The potential bound is required only on nodes reachable from the chosen
start. The tree-weight comparison below carries reachability through every
scheduler edge, so no bound on an unreachable frontier node is used.

All bounds are exact natural-number inequalities over finite scheduler
words. The final corollary uses the start's own potential as the bound when
the potential is nonincreasing on every active-state edge.
-/

namespace BellmanGeometricTailReachable

open FiniteUniformStoppingTree
open BellmanGeometricTail

set_option autoImplicit false

/-! ## Reachability for the absorbing stopped transition -/

/-- Reachability includes the empty scheduler word and is closed under
appending one raw scheduler edge. Terminal nodes remain absorbing because
the constructor uses `stepNode`. -/
inductive Reach {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) :
    StopNode S → StopNode S → Prop where
  | refl (x : StopNode S) : Reach step x x
  | next {x y : StopNode S} (hxy : Reach step x y) (edge : Fin n) :
      Reach step x (stepNode step y edge)

/-- Concatenating two finite executions preserves reachability. -/
theorem Reach.trans
    {S : Type} {n : Nat}
    {step : S → Fin n → StopNode S}
    {x y z : StopNode S}
    (hxy : Reach step x y) (hyz : Reach step y z) :
    Reach step x z := by
  revert hxy
  induction hyz with
  | refl =>
      intro hxy
      exact hxy
  | next hyz edge ih =>
      intro hxy
      exact Reach.next (ih hxy) edge

/-- Every child of a reachable node is reachable from the same start. -/
theorem reach_stepNode
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    {start x : StopNode S}
    (hx : Reach step start x) (edge : Fin n) :
    Reach step start (stepNode step x edge) :=
  Reach.next hx edge

/-! ## Comparison restricted to the reachable scheduler frontier -/

/-- Pointwise domination on the reachable set suffices to compare tree
weights from any reachable node, at every finite horizon. -/
theorem treeWeight_mono_reach
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (start : StopNode S)
    (w v : StopNode S → Nat)
    (hwv : ∀ y, Reach step start y → w y ≤ v y) :
    ∀ T x, Reach step start x →
      treeWeight step w x T ≤ treeWeight step v x T := by
  intro T
  induction T with
  | zero =>
      intro x hx
      exact hwv x hx
  | succ T ih =>
      intro x hx
      simp only [treeWeight]
      exact ofFn_sum_le _ _ (fun edge =>
        ih (stepNode step x edge) (Reach.next hx edge))

/-- The reciprocal Bellman tail at a reachable node can be padded to the
common block length `2 * B`. Only that node's reachable-state bound is
needed for this one-block estimate. -/
theorem two_mul_activeCount_block_le_reach
    {S : Type} {n B : Nat}
    (step : S → Fin n → StopNode S)
    (potential : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step 1 potential)
    (start : StopNode S)
    (hB : ∀ y, Reach step start y → potential y ≤ B)
    (hn : 0 < n) :
    ∀ y, Reach step start y →
      2 * activeCount step y (2 * B) ≤ n ^ (2 * B) := by
  intro y hy
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
      have hle : 2 * potential (.active s) ≤ 2 * B :=
        Nat.mul_le_mul_left 2 (hB (.active s) hy)
      exact factor_mul_activeCount_le_pow_of_horizon_le
        step (.active s) hle hreciprocal

/-- Split at horizon `T` and apply the one-block bound only at reachable
frontier nodes. Terminal frontier nodes contribute zero active leaves. -/
theorem two_mul_activeCount_add_block_le_reach
    {S : Type} {n L : Nat}
    (step : S → Fin n → StopNode S)
    (start : StopNode S)
    (hblock : ∀ y, Reach step start y →
      2 * activeCount step y L ≤ n ^ L)
    (x : StopNode S) (hx : Reach step start x) (T : Nat) :
    2 * activeCount step x (T + L) ≤
      n ^ L * activeCount step x T := by
  rw [activeCount_add step x T L]
  have hpoint :
      ∀ y : StopNode S, Reach step start y →
        2 * activeCount step y L ≤ n ^ L * activeWeight y := by
    intro y hy
    cases y with
    | active s =>
        simpa [activeWeight] using hblock (.active s) hy
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
      treeWeight_mono_reach step start
        (fun y => 2 * activeCount step y L)
        (fun y => n ^ L * activeWeight y)
        hpoint T x hx
    _ = n ^ L * activeCount step x T := by
      simpa only [activeCount] using
        (treeWeight_mul_left step (n ^ L) activeWeight x T)

/-! ## Geometric tails -/

/-- A Bellman potential bounded only on nodes reachable from `start`
gives the same division-free geometric tail as a globally bounded one. -/
theorem geometric_tail_reach
    {S : Type} {n B : Nat}
    (step : S → Fin n → StopNode S)
    (potential : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step 1 potential)
    (start : StopNode S)
    (hB : ∀ y, Reach step start y → potential y ≤ B)
    (hn : 0 < n)
    (k : Nat) :
    2 ^ k * activeCount step start (k * (2 * B)) ≤
      n ^ (k * (2 * B)) := by
  have hblock :
      ∀ y : StopNode S, Reach step start y →
        2 * activeCount step y (2 * B) ≤ n ^ (2 * B) :=
    two_mul_activeCount_block_le_reach
      step potential hsuper start hB hn
  have htail :
      ∀ j : Nat, ∀ x : StopNode S, Reach step start x →
        2 ^ j * activeCount step x (j * (2 * B)) ≤
          n ^ (j * (2 * B)) := by
    intro j
    induction j with
    | zero =>
        intro x hx
        cases x <;>
          simp [activeCount, treeWeight, activeWeight]
    | succ j ih =>
        intro x hx
        have hcontract :=
          two_mul_activeCount_add_block_le_reach
            step start hblock x hx (j * (2 * B))
        calc
          2 ^ Nat.succ j *
              activeCount step x (Nat.succ j * (2 * B)) =
            2 ^ j *
              (2 * activeCount step x
                (j * (2 * B) + 2 * B)) := by
                  rw [Nat.pow_succ, Nat.succ_mul j (2 * B)]
                  ac_rfl
          _ ≤ 2 ^ j *
              (n ^ (2 * B) *
                activeCount step x (j * (2 * B))) :=
            Nat.mul_le_mul_left (2 ^ j) hcontract
          _ = n ^ (2 * B) *
              (2 ^ j * activeCount step x (j * (2 * B))) := by
            ac_rfl
          _ ≤ n ^ (2 * B) * n ^ (j * (2 * B)) :=
            Nat.mul_le_mul_left (n ^ (2 * B)) (ih x hx)
          _ = n ^ (Nat.succ j * (2 * B)) := by
            rw [Nat.succ_mul j (2 * B), Nat.pow_add]
            ac_rfl
  exact htail k start (Reach.refl start)

/-- The same reachable-set bound may be reused after restarting at any
node reachable from the original start. -/
theorem geometric_tail_reach_from
    {S : Type} {n B : Nat}
    (step : S → Fin n → StopNode S)
    (potential : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step 1 potential)
    (start : StopNode S)
    (hB : ∀ y, Reach step start y → potential y ≤ B)
    (hn : 0 < n)
    (x : StopNode S) (hx : Reach step start x) (k : Nat) :
    2 ^ k * activeCount step x (k * (2 * B)) ≤
      n ^ (k * (2 * B)) := by
  exact geometric_tail_reach (B := B)
    step potential hsuper x
    (fun y hy => hB y (Reach.trans hx hy)) hn k

/-! ## A nonincreasing potential supplies its own reachable bound -/

/-- Edgewise monotonicity on active states extends to all stopped nodes;
terminal cases use only absorption and require no extra hypothesis. -/
theorem potential_stepNode_le
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (potential : StopNode S → Nat)
    (hmono : ∀ s e, potential (step s e) ≤ potential (.active s)) :
    ∀ x e, potential (stepNode step x e) ≤ potential x := by
  intro x e
  cases x with
  | active s => exact hmono s e
  | success => exact Nat.le_refl _
  | failure => exact Nat.le_refl _

/-- An edgewise nonincreasing potential is bounded by its initial value
at every reachable node. -/
theorem potential_le_of_reach
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (potential : StopNode S → Nat)
    (hmono : ∀ s e, potential (step s e) ≤ potential (.active s))
    {x y : StopNode S}
    (hxy : Reach step x y) :
    potential y ≤ potential x := by
  induction hxy with
  | refl =>
      exact Nat.le_refl _
  | next hxy edge ih =>
      exact Nat.le_trans
        (potential_stepNode_le step potential hmono _ edge) ih

/-- When the Bellman potential is nonincreasing on each active edge,
blocks of length twice the start's own potential give a geometric tail. -/
theorem geometric_tail_of_nonincreasing
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (potential : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step 1 potential)
    (hmono : ∀ s e, potential (step s e) ≤ potential (.active s))
    (hn : 0 < n)
    (start : StopNode S) (k : Nat) :
    2 ^ k * activeCount step start (k * (2 * potential start)) ≤
      n ^ (k * (2 * potential start)) := by
  exact geometric_tail_reach (B := potential start)
    step potential hsuper start
    (fun y hy => potential_le_of_reach step potential hmono hy)
    hn k

end BellmanGeometricTailReachable

#print axioms BellmanGeometricTailReachable.Reach.trans
#print axioms BellmanGeometricTailReachable.reach_stepNode
#print axioms BellmanGeometricTailReachable.treeWeight_mono_reach
#print axioms BellmanGeometricTailReachable.two_mul_activeCount_block_le_reach
#print axioms BellmanGeometricTailReachable.two_mul_activeCount_add_block_le_reach
#print axioms BellmanGeometricTailReachable.geometric_tail_reach
#print axioms BellmanGeometricTailReachable.geometric_tail_reach_from
#print axioms BellmanGeometricTailReachable.potential_stepNode_le
#print axioms BellmanGeometricTailReachable.potential_le_of_reach
#print axioms BellmanGeometricTailReachable.geometric_tail_of_nonincreasing
