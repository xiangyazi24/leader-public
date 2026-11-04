import Leader.Wu.Scheduler.LeaderCountExpectedCost

/-!
The finite Nat harmonic argument used by the frozen higher-level cost
theorem, checked in a small leaf. Only its arithmetic is needed here; this
avoids importing the broad tactic umbrella in HarmonicEpisodeCharge into
the already large physical final-two cone under the local memory cap.
-/

set_option autoImplicit false

namespace K2FiniteSafeEliminationArithmetic

open LeaderCountExpectedCost

def divisionBudget (N : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => divisionBudget N k + N / (k + 1)

theorem budget_succ (N k : Nat) :
    divisionBudget N (k + 1) = divisionBudget N k + N / (k + 1) := rfl

theorem budget_mono (N : Nat) {a b : Nat} (hab : a ≤ b) :
    divisionBudget N a ≤ divisionBudget N b := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases he : a = b + 1
      · subst a; exact Nat.le_refl _
      · exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)

theorem dyadic_pair_le (N r : Nat) (hr : 0 < r) :
    N / (2 * r) + N / (2 * r + 1) ≤ N / r := by
  have hright : N / (2 * r + 1) ≤ N / (2 * r) :=
    Nat.div_le_div_left (by omega) (by omega)
  have hdouble : 2 * (N / (2 * r)) ≤ N / r := by
    apply (Nat.le_div_iff_mul_le hr).mpr
    calc
      2 * (N / (2 * r)) * r = (N / (2 * r)) * (2 * r) := by ac_rfl
      _ ≤ N := Nat.div_mul_le_self N (2 * r)
  omega

theorem budget_odd_le (N k : Nat) :
    divisionBudget N (2 * k + 1) ≤ N + divisionBudget N k := by
  induction k with
  | zero => simp [divisionBudget]
  | succ k ih =>
      have he : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by omega
      rw [he, budget_succ N (2 * k + 1 + 1), budget_succ N (2 * k + 1), budget_succ N k]
      have hd := dyadic_pair_le N (k + 1) (by omega)
      have he0 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [he0]
      omega

theorem budget_halve (N k : Nat) :
    divisionBudget N k ≤ N + divisionBudget N (k / 2) := by
  have he := Nat.mod_add_div k 2
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have hk : k = 2 * (k / 2) := by omega
    exact Nat.le_trans (budget_mono N (by omega : k ≤ 2 * (k / 2) + 1))
      (budget_odd_le N (k / 2))
  · have hk : k = 2 * (k / 2) + 1 := by omega
    exact Nat.le_trans (budget_mono N (by omega : k ≤ 2 * (k / 2) + 1))
      (budget_odd_le N (k / 2))

/-- One copy of N pays each binary layer of the exact floor-division sum. -/
theorem budget_log (N k : Nat) : divisionBudget N k ≤ N * (Nat.log2 k + 1) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      by_cases hk : 2 ≤ k
      · have hh := ih (k / 2) (Nat.div_lt_self (by omega) (by decide))
        calc
          divisionBudget N k ≤ N + divisionBudget N (k / 2) := budget_halve N k
          _ ≤ N + N * (Nat.log2 (k / 2) + 1) := Nat.add_le_add_left hh N
          _ = N * (Nat.log2 k + 1) := by
            rw [Nat.log2_def k, if_pos hk]
            simp only [Nat.mul_add, Nat.mul_one]
            omega
      · have he : k = 0 ∨ k = 1 := by omega
        have hz : Nat.log2 1 = 0 := by decide
        rcases he with rfl | rfl <;> simp [divisionBudget, hz]

theorem levelSum_le_budget (N k : Nat) :
    levelSum (fun j => N / j) k ≤ divisionBudget N k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      rw [levelSum, divisionBudget]
      by_cases hk : 3 ≤ k + 1
      · simp only [if_pos hk]
        exact Nat.add_le_add_right ih _
      · simp only [if_neg hk, Nat.add_zero]
        exact Nat.le_trans ih (Nat.le_add_right _ _)

/-- A weighted harmonic tariff, with no stochastic or episode premise. -/
theorem level_tariff_log (N n k Q : Nat) (hk : k ≤ n) :
    Q * levelSum (fun j => N / j) k ≤ Q * (N * (Nat.log2 n + 1)) :=
  Nat.mul_le_mul_left Q (Nat.le_trans (levelSum_le_budget N k)
    (Nat.le_trans (budget_mono N hk) (budget_log N n)))

end K2FiniteSafeEliminationArithmetic

#print axioms K2FiniteSafeEliminationArithmetic.budget_log
#print axioms K2FiniteSafeEliminationArithmetic.level_tariff_log
