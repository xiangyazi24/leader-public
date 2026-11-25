import Lean.Elab.Tactic.Omega

namespace L4
namespace BarrierLedger

/-- Totals for one surviving tagged bullet, measured from one covered cut.
The compensated ideal current is scaled by five; it is a signed quantity.
These are bookkeeping data, not extra protocol fields. -/
structure Totals where
  moves : Nat
  paidAdvances : Nat
  tenures : Nat
  idealIngresses : Nat
  current5 : Int

/-- The actual lifted trace must justify that the initial/exposed geometry
costs at most one circumference, and that all excess progress is paid.
This predicate is an interface, not a result about the pair protocol. -/
def LiftedGeometry (n : Nat) (t : Totals) : Prop :=
  ∃ exposed paid : Nat,
    t.moves ≤ exposed + paid ∧ exposed ≤ n ∧ paid ≤ t.paidAdvances

/-- The actual trace must classify all paid advances without double-charging:
initial/exposed stock, short-window spending, short-window carried stock, and
useful long-window admissions. The final class is bounded by ideal ingress
using the appropriate stopped queue coupling. This is an interface. -/
def PaymentProvenance (n : Nat) (t : Totals) : Prop :=
  ∃ initial shortSpent shortCarried long : Nat,
    t.paidAdvances ≤ initial + shortSpent + shortCarried + long ∧
    initial ≤ n ∧ shortSpent ≤ 5 * t.tenures ∧ shortCarried ≤ 5 * t.tenures ∧
    long ≤ t.idealIngresses

/-- The chronology of maximal living first-barrier tenures must supply this
count. No such chronology is assumed by the arithmetic proofs themselves. -/
def TenureCount (n : Nat) (t : Totals) : Prop :=
  t.tenures ≤ n + 1

/-- The sum of scaled compensated currents includes no reset jump; over all
started long-queue episodes each endpoint costs at most five. -/
def QueueCompensation (t : Totals) : Prop :=
  5 * (t.idealIngresses : Int) ≤ t.current5 + 5 * (t.tenures : Int)

theorem exposed_then_paid {n : Nat} {t : Totals} (h : LiftedGeometry n t) :
    t.moves ≤ n + t.paidAdvances := by
  rcases h with ⟨exposed, paid, hmove, hexposed, hpaid⟩
  omega

theorem payment_sum {n : Nat} {t : Totals} (h : PaymentProvenance n t) :
    t.paidAdvances ≤ n + 10 * t.tenures + t.idealIngresses := by
  rcases h with ⟨initial, spent, carried, long, hpay, hi, hs, hc, hl⟩
  omega

/-- Exact compensated bound before using the tenure-count estimate. -/
theorem debt5_of_raw_ledger {n : Nat} {t : Totals}
    (hmove : t.moves ≤ n + t.paidAdvances)
    (hpay : t.paidAdvances ≤ n + 10 * t.tenures + t.idealIngresses)
    (hqueue : QueueCompensation t) :
    5 * (t.moves : Int) - t.current5 ≤ 10 * (n : Int) + 55 * (t.tenures : Int) := by
  unfold QueueCompensation at hqueue
  omega

/-- The four pathwise inequalities suffice for the paper's strict debt
bound on its physical domain (n ge 4). -/
theorem debt5_lt_of_raw_ledger {n : Nat} {t : Totals}
    (hn : 4 ≤ n)
    (hmove : t.moves ≤ n + t.paidAdvances)
    (hpay : t.paidAdvances ≤ n + 10 * t.tenures + t.idealIngresses)
    (htenure : TenureCount n t) (hqueue : QueueCompensation t) :
    5 * (t.moves : Int) - t.current5 < 120 * (n : Int) := by
  have h := debt5_of_raw_ledger hmove hpay hqueue
  unfold TenureCount at htenure
  omega

/-- The modular interface to a future tagged-bullet trace proof. No protocol
claim is made without all four trace-side inputs. -/
theorem debt5_lt_of_trace_interfaces {n : Nat} {t : Totals}
    (hn : 4 ≤ n) (hgeometry : LiftedGeometry n t)
    (hprovenance : PaymentProvenance n t)
    (htenure : TenureCount n t) (hqueue : QueueCompensation t) :
    5 * (t.moves : Int) - t.current5 < 120 * (n : Int) :=
  debt5_lt_of_raw_ledger hn (exposed_then_paid hgeometry)
    (payment_sum hprovenance) htenure hqueue

#print axioms exposed_then_paid
#print axioms payment_sum
#print axioms debt5_of_raw_ledger
#print axioms debt5_lt_of_raw_ledger
#print axioms debt5_lt_of_trace_interfaces

end BarrierLedger
end L4
