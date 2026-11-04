import Leader.Core.ControlledSchedulerMass

set_option autoImplicit false

open FiniteUniformStoppingTree ControlledSchedulerMass

namespace LDSinkTwoGapRaceEntranceAuditCoverage

variable {S : Type} {n : Nat}

/-- Every successful controlled word is either retained by the collapse
audit or rejected by that audit.  The trees use exactly the same raw word;
the failure term pays for every branch censored before its later success. -/
theorem controlled_success_covered (step : S → Fin n → StopNode S)
    (r : Redirection S n) (x : StopNode S) (T M : Nat) :
    successCount (controlledStep step r) x T ≤
      successCount (auditStep step r) (withBudget M x) T +
        failureCount (auditStep step r) (withBudget M x) T := by
  have htree : ∀ (T : Nat) (x : StopNode S) (M : Nat),
      treeWeight (controlledStep step r) successWeight x T ≤
        treeWeight (auditStep step r)
          (fun y => successWeight y + failureWeight y) (withBudget M x) T := by
    intro T
    induction T with
    | zero => intro x M; cases x <;> simp [treeWeight, withBudget, successWeight, failureWeight]
    | succ T ih =>
        intro x M
        cases x with
        | success => simp [withBudget, treeWeight_success, successWeight, failureWeight]
        | failure => simp [withBudget, treeWeight_failure, successWeight, failureWeight]
        | active s =>
            simp only [treeWeight, withBudget, stepNode]
            apply ofFn_sum_le
            intro e
            by_cases hc : r.Collapses s e
            · cases M with
              | zero =>
                  simp only [auditStep, if_pos hc, treeWeight_failure,
                    successWeight, failureWeight, Nat.zero_add, Nat.mul_one]
                  have hp := node_count_partition (controlledStep step r)
                    (controlledStep step r s e) T
                  change successCount (controlledStep step r) (controlledStep step r s e) T ≤ n ^ T
                  omega
              | succ M =>
                  simp only [auditStep, if_pos hc]
                  exact ih (controlledStep step r s e) M
            · simp only [auditStep, if_neg hc]
              exact ih (controlledStep step r s e) M
  have h := htree T x M
  rw [treeWeight_add] at h
  exact h

#print axioms controlled_success_covered

end LDSinkTwoGapRaceEntranceAuditCoverage
