import Leader.L3.Bank.RepairDigitPacketTransport
import Leader.L3.Bank.RepairDigitCorrespondence

/-!
# Lemma e-packet: the fourth reached-state clause on the audit ghost (statement, start)

repair.tex 1306-1307: "The pending moving-packet queue is a consecutive suffix of the accepted
serial stream." Stated on the existing digit audit (no new ghost): the accepted stream is the
list of recorded exports on the delimiter edge `src + R - 1 → src + R` of this lane
(`DelExport`, from `DigitRecordedExport`), ordered by their frame times; a pending moving packet
is a target cell whose masked input is `P`; its atom is the lane input ghost of the cell
(`L3.Correspondence.laneCells`).

`QueueAt … χ` with a proof-only map `χ` from target cells to exports (as `chi` in
CohortWindow):
* every pending cell `q` holds the operand of the recorded delimiter export `χ q`;
* a pending cell further left was exported later (exclusion: packets do not pass);
* no gap: every recorded delimiter export at or after the export of some pending cell is the
  export of a pending cell.

`PacketQueue` adds the shape invariant `PacketOrder`. It holds at every mobile-free cut
(`queueMobileFree`, `packetQueueMobileFree`): no pending cell. Model check of the clause on the
literal replay ghost (research/lean-l3/wip/r10c-mc/queue_mc.py): no violation, R = 2, 3.
-/

namespace L3.DigitPacketQueue

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.Correspondence
open L3.CohortSites
open L3.DigitPacketOrder

variable {c : Compiled} {n : Nat}

/-- A recorded export of this lane on the delimiter edge of the pair. Consumer: `QueueAt`. -/
def DelExport (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (A : DigitAudit c n) (x : DigitExport c n) : Prop :=
  DigitRecordedExport A x ∧ x.lane = lane ∧ x.source = digitSite ring root (src + (R - 1)) ∧
    x.destination = digitSite ring root (src + R)

/-- A moving packet. Consumer: `QueueAt`. -/
def IsPkt (i : BankRepairDigitInSh) : Prop := ∃ T, i = .P T

/-- **The fourth clause with witness `χ`.** Consumer: `PacketQueue`, the settled-empty and
renewal-trial phases of Lemma e-packet. -/
def QueueAt (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (χ : Nat → DigitExport c n) : Prop :=
  (∀ q, R ≤ q → q < 2 * R → IsPkt ((cohortProj ring root lane src R S).inp q) →
      DelExport ring root lane src R A (χ q) ∧
        (laneCells ring root lane src A.current q).input = (χ q).operand) ∧
    (∀ q q', R ≤ q → q < q' → q' < 2 * R →
      IsPkt ((cohortProj ring root lane src R S).inp q) →
      IsPkt ((cohortProj ring root lane src R S).inp q') → (χ q').time < (χ q).time) ∧
    (∀ q y, R ≤ q → q < 2 * R → IsPkt ((cohortProj ring root lane src R S).inp q) →
      DelExport ring root lane src R A y → (χ q).time ≤ y.time →
      ∃ q', R ≤ q' ∧ q' < 2 * R ∧ IsPkt ((cohortProj ring root lane src R S).inp q') ∧
        y = χ q')

/-- **The reached-state invariant with its ghost clause.** Consumer: the settled-empty and
renewal-trial phases of Lemma e-packet. -/
def PacketQueue (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) : Prop :=
  PacketOrder R (cohortProj ring root lane src R S) ∧
    ∃ χ : Nat → DigitExport c n, QueueAt ring root lane src R S A χ

/-- With no pending cell the clause holds for every witness. Consumer: `queueMobileFree`. -/
theorem queueOfNoPkt (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (χ : Nat → DigitExport c n)
    (h : ∀ q, R ≤ q → q < 2 * R → ¬ IsPkt ((cohortProj ring root lane src R S).inp q)) :
    QueueAt ring root lane src R S A χ :=
  ⟨fun q h1 h2 hp => absurd hp (h q h1 h2),
   fun q _ h1 h2 h3 hp _ => absurd hp (h q h1 (by omega)),
   fun q _ h1 h2 hp => absurd hp (h q h1 h2)⟩

/-- **Start.** At a mobile-free cut (no carry, only empty or settled target inputs) the clause
holds. Consumer: `packetQueueMobileFree`. -/
theorem queueMobileFree (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (χ : Nat → DigitExport c n)
    (h : ∀ q, R ≤ q → q < 2 * R → (cohortProj ring root lane src R S).live q = false ∧
      ((cohortProj ring root lane src R S).inp q = .E ∨
        ∃ T, (cohortProj ring root lane src R S).inp q = .S T)) :
    QueueAt ring root lane src R S A χ := by
  apply queueOfNoPkt
  intro q h1 h2 ⟨T, hT⟩
  rcases (h q h1 h2).2 with hi | ⟨T', hi⟩ <;> rw [hi] at hT <;> cases hT

/-- **Start of the full invariant.** Consumer: the e-packet composition at the end of the
inherited mobile work. -/
theorem packetQueueMobileFree (ring : DirectedRing n) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (S : Fin n → ProjD c) (A : DigitAudit c n) (χ : Nat → DigitExport c n)
    (h : ∀ q, R ≤ q → q < 2 * R → (cohortProj ring root lane src R S).live q = false ∧
      ((cohortProj ring root lane src R S).inp q = .E ∨
        ∃ T, (cohortProj ring root lane src R S).inp q = .S T)) :
    PacketQueue ring root lane src R S A :=
  ⟨⟨R, orderMobileFree R _ h⟩, χ, queueMobileFree ring root lane src R S A χ h⟩

end L3.DigitPacketQueue

#print axioms L3.DigitPacketQueue.queueOfNoPkt
#print axioms L3.DigitPacketQueue.queueMobileFree
#print axioms L3.DigitPacketQueue.packetQueueMobileFree
