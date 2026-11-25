import Leader.L4.TaggedQueueAccount
import Leader.L4.TaggedGeometry
import Leader.L4.TaggedEpisodes

namespace L4.TaggedTrace

/-- Exact live trace domain for the still-open parts of the debt proof. -/
def LiveCoveredTrace {p c1 n : Nat} (x : Config p c1 n) (i : Fin n)
    (w : List (Fin n)) : Prop :=
  2 ≤ p ∧ 12 ≤ c1 ∧ 4 ≤ n ∧ (∃ j : Fin n, (x j).mark = true) ∧ MCOV x ∧ COV x ∧
    ¬ ended (track (init x i) w)

/-- Outstanding stock provenance on the concrete counters. Initial/exposed
stock is not just stock present at the start of the tape. -/
def ConcreteStockBudget : Prop :=
  ∀ {p c1 n : Nat} (x : Config p c1 n) (i : Fin n) (w : List (Fin n)),
    LiveCoveredTrace x i w →
    BarrierLedger.PaymentProvenance n (totals (track (init x i) w))

/-- Outstanding classification of actual completed leader tenures, not
the already-proved counting of a supplied chronology. -/
def ConcreteTenureBudget : Prop :=
  ∀ {p c1 n : Nat} (x : Config p c1 n) (i : Fin n) (w : List (Fin n)),
    LiveCoveredTrace x i w → (track (init x i) w).tenureCount ≤ n + 1

/-- The paper's concrete debt endpoint, conditional on the advertised
trace-side obligations. The current bound is supplied by the proved
actual queue account, not a premise on the compensated sum. -/
theorem concreteBarrierDebt_of_budgets
    (hstock : ConcreteStockBudget)
    (htnr : ConcreteTenureBudget) :
    ConcreteBarrierDebt := by
  intro p c1 n x i w hp hc1 hn hnd hm hc hsurv
  have hdom : LiveCoveredTrace x i w := ⟨hp, hc1, hn, covered_mark_exists_of_not_dvd x i hm hnd, hm, hc, hsurv⟩
  let s := track (init x i) w
  have hmove := L4.tagged_moves_le_size_add_paid_of_mcov hn x i w hm hnd hsurv
  have heq := hits_eq_moves_on_survival (init x i) w rfl hsurv
  have hpay := BarrierLedger.payment_sum (hstock x i w hdom)
  have hten : BarrierLedger.TenureCount n (totals s) := htnr x i w hdom
  have hq := trace_queueCompensation x i w
  have hnum := trace_episodes_le_tenures hn x i w hm
  change 5 * (s.idealIngresses : Int) ≤ s.current5 + 5 * (s.episodes : Int) at hq
  change s.episodes ≤ s.tenureCount at hnum
  have hque : BarrierLedger.QueueCompensation (totals s) := by
    change 5 * (s.idealIngresses : Int) ≤ s.current5 + 5 * (s.tenureCount : Int)
    omega
  have hb := BarrierLedger.debt5_lt_of_raw_ledger hn hmove hpay hten hque
  change 5 * (s.moveCount : Int) - s.current5 < 120 * (n : Int) at hb
  change s.outHits = s.moveCount at heq
  change 5 * (s.outHits : Int) - s.current5 < 120 * (n : Int)
  rw [heq]
  exact hb

end L4.TaggedTrace

#print axioms L4.TaggedTrace.concreteBarrierDebt_of_budgets
