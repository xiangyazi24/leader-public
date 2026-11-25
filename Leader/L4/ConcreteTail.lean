import Leader.L4.WeightedTagTrace
import Leader.L4.PhysicalTailKernel
import Leader.L4.ConcreteDebt

namespace L4.TaggedTrace

/-- A physical per-tag tail in the same finite-word counting semantics,
conditional only on the concrete live debt bound. No Freedman theorem
or additional concentration premise is used. -/
theorem concreteTagTail_of_debt (h : ConcreteBarrierDebt) : ConcreteTagTail :=
  TailCutoff.concreteTagTail_of_horizon_weight
    (TailWeight.concrete_horizon_weight_of_kernel PhysicalTailKernel.drift_kernel h)

/-- Conditional extinction of the common-clock maximum of all cover tags:
only the two remaining physical ledger propositions are hypotheses. -/
theorem allTags_mean_of_barrierBudgets
    (hstock : ConcreteStockBudget) (htenure : ConcreteTenureBudget)
    {p c1 n : Nat} (x : Config p c1 n)
    (hp : 2 ≤ p) (hcal : 12 ≤ c1) (hn : 4 ≤ n) (hnd : ¬ p ∣ n)
    (hm : MCOV x) (hc : COV x) :
    IIDExpectedHittingTimeAtMost allAdvance allEnded (allInit x) (150*n^2) :=
  concreteAllTags_mean_of_tail
    (concreteTagTail_of_debt (concreteBarrierDebt_of_budgets hstock htenure))
    x hp hcal hn hnd hm hc

end L4.TaggedTrace

