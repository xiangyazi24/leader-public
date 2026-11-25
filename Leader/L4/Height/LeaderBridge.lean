import Leader.L4.Height.Window
import Leader.L3.ProbStages

/-!
The truncated IID hitting cost agrees with the uniform first-hit numerator.
This identifies natural expectation budgets and transports the stage and
one-step potential theorems to the height-process expectation predicate.
-/

namespace L4.Height

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting

variable {S : Type} {n : Nat} (next : S → Fin n → S)

/-- Both numerators obey the same zero, terminal, and first-letter equations.
Neither definition takes a decidability parameter: both fix classical
decidability internally, so no change of instance is needed. -/
theorem iidHitCost_eq_costNumerator (P : S → Prop) :
    ∀ (T : Nat) (x : S),
      iidHitCost next P T x = costNumerator next P x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x
      rfl
  | succ T ih =>
      intro x
      by_cases hx : P x
      · rw [iidHitCost_of_target next P x hx,
          costNumerator_terminal next P x hx]
      · rw [costNumerator_succ next P x hx T]
        simp only [iidHitCost, if_neg hx, ih]

/-- On a nonempty uniform alphabet, bounding every truncated cost by a
natural budget is equivalent to the rational first-hit expectation bound,
including its almost-sure hitting clause. -/
theorem iid_expected_iff_leader (P : S → Prop) (hn : 0 < n)
    (x : S) (B : Nat) :
    IIDExpectedHittingTimeAtMost next P x B ↔
      UniformFirstHit.ExpectedHittingTimeAtMost next P x (B : Rat) := by
  rw [UniformFirstHit.expectedHittingTimeAtMost_iff_cost next P hn x B]
  unfold IIDExpectedHittingTimeAtMost
  apply forall_congr'
  intro T
  rw [iidHitCost_eq_costNumerator, Nat.mul_comm B]

/-- Expected costs add across first entry into the intermediate or final
target. Neither target needs to be closed under the transition. -/
theorem iid_stage_le (hn : 0 < n) (x : S) (A P : S → Prop)
    (B₁ B₂ : Nat)
    (h₁ : IIDExpectedHittingTimeAtMost next (fun z => A z ∨ P z) x B₁)
    (h₂ : ∀ y, A y → IIDExpectedHittingTimeAtMost next P y B₂) :
    IIDExpectedHittingTimeAtMost next P x (B₁ + B₂) := by
  apply (iid_expected_iff_leader next P hn x (B₁ + B₂)).2
  apply L3.Prob.expectedHittingTimeAtMost_stage_le next hn x A P B₁ B₂
  · exact (iid_expected_iff_leader next (fun z => A z ∨ P z)
      hn x B₁).1 h₁
  · intro y hy
    exact (iid_expected_iff_leader next P hn y B₂).1 (h₂ y hy)

/-- A natural potential with one unit of expected drift bounds every
truncated IID hitting cost, even when the alphabet is empty. -/
theorem iid_potential_le (P : S → Prop) (Φ : S → Nat)
    (hdrift : ∀ x, ¬ P x →
      n + (List.ofFn (fun e : Fin n => Φ (next x e))).sum ≤ n * Φ x) :
    ∀ x, IIDExpectedHittingTimeAtMost next P x (Φ x) := by
  intro x T
  rw [iidHitCost_eq_costNumerator, Nat.mul_comm (Φ x)]
  exact L3.Prob.costNumerator_le_of_potential next P Φ hdrift x T

end L4.Height

