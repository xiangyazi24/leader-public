import Leader.L4.Barrier
import Leader.L4.BarrierIID
import Leader.L4.BarrierLedger

namespace L4

/-- The paper's three physical nominations in their clockwise order. -/
def barrierQueueBonds {n : Nat} (hn : 4 ≤ n) (z : Fin n) : BarrierIID.QueueBonds n :=
  let h := barrierBondsDistinct hn z
  ⟨z, rightNeighbor z, rightNeighbor (rightNeighbor z), h.1, h.2.1, h.2.2⟩

theorem barrierQueueBonds_bond {n : Nat} (hn : 4 ≤ n) (z e : Fin n) :
    (barrierQueueBonds hn z).bond e = barrierBond z e := rfl

/-- Exact active conditional-mean numerator for the physical edge labelling.
The one-mark mean of the *unscaled* compensated ideal current is 2/(5n). -/
theorem barrierMark_sum {n : Nat} (hn : 4 ≤ n) (z : Fin n) (q : OpenQueue.StockPair) :
    BarrierIID.edgeSum (fun e => OpenQueue.scaledIncrement q (barrierBond z e)) = 2 :=
  BarrierIID.queueMark_sum_active (barrierQueueBonds hn z) q

/-- The all-edge sum transforms the tagged outgoing hit and the three actual
queue labels into a scaled conditional drift of 3/n while active. -/
theorem barrierDrift_sum {n : Nat} (hn : 4 ≤ n) (z out : Fin n)
    (q : OpenQueue.StockPair) :
    BarrierIID.edgeSum
        (BarrierIID.driftMark out (some (barrierQueueBonds hn z, q))) = 3 :=
  BarrierIID.driftMark_sum out _

/-- Each queue contribution is 0, 1 or 2 after scaling by five. -/
theorem scaledQueueMark_range {n : Nat}
    (queue : Option (BarrierIID.QueueBonds n × OpenQueue.StockPair)) (e : Fin n) :
    0 ≤ BarrierIID.queueMark queue e ∧ BarrierIID.queueMark queue e ≤ 2 := by
  cases queue with
  | none => change (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 2; decide
  | some p =>
    rcases p with ⟨b, ⟨i, j⟩⟩
    change 0 ≤ OpenQueue.scaledIncrement ⟨i, j⟩ (b.bond e) ∧
      OpenQueue.scaledIncrement ⟨i, j⟩ (b.bond e) ≤ 2
    cases i <;> cases j <;> cases b.bond e <;> decide

/-- One physical mark adds at most five to the scaled drift (and may add
as little as negative two), so an extinction mark can overshoot a survival
prefix budget by at most five. -/
theorem taggedDriftMark_range {n : Nat} (out e : Fin n)
    (queue : Option (BarrierIID.QueueBonds n × OpenQueue.StockPair)) :
    -2 ≤ BarrierIID.driftMark out queue e ∧ BarrierIID.driftMark out queue e ≤ 5 := by
  obtain ⟨h₁, h₂⟩ := scaledQueueMark_range queue e
  unfold BarrierIID.driftMark
  by_cases h : e = out
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- Attach the exact episode telescoping result to the paper's path ledger.
The episode alignment and at-most-one episode per tenure still have to be
proved for any concrete tagged-front construction. -/
theorem episodeQueueCompensation (t : BarrierLedger.Totals)
    (ww : List (List OpenQueue.Mark))
    (hJ : OpenQueue.episodeScaledIngresses ww = 5 * (t.idealIngresses : Int))
    (hQ : OpenQueue.episodeCurrent ww = t.current5)
    (hN : ww.length ≤ t.tenures) :
    BarrierLedger.QueueCompensation t := by
  have hw := OpenQueue.reset_telescope_le ww
  rw [hJ, hQ] at hw
  unfold BarrierLedger.QueueCompensation
  have hN' : Int.ofNat ww.length ≤ (t.tenures : Int) := Int.ofNat_le.mpr hN
  omega

end L4

