import Leader.L3.Width.DigitCompareStage

/-!
# The restart of the comparison observer is not ahead of the audit clock

The comparison lane restarts its observer at the clock `restart` of the writer value receipts
(`L3.WriterValueCuts.WidthWriterValueReceipts`): the end of the value chain
(`DigitValueChain`), which is the base value cut or the time of the last terminal of a five-cohort
completion. Both are at most the audit clock (`DigitTwoBaseCovers`, `DigitCompletion`), so
`restart ≤ clock` on every values-stable state (`stableRunRestartLe`), for every
`WidthDigitReference` (BANK and SMALL).
-/

namespace L3.CompareRestart

set_option autoImplicit false

open L3
open L3.WidthDigit
open L3.WriterValueCuts
open L3.CompareStage

/-- **The end of the value chain is at most the clock.** Consumer: `receiptsRestartLe`. -/
theorem chainRestartLe {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (A : DigitAudit c n) (structural first baseCut : Nat) (hb : baseCut ≤ A.clock)
    {last restart : Nat} {cuts : List (Nat × Nat)}
    (h : DigitValueChain ring root A structural first baseCut last restart cuts) :
    restart ≤ A.clock := by
  induction h with
  | start => exact hb
  | next _ target terminal _ hc _ =>
    obtain ⟨_, _, _, _, _, _, _, -, -, -, -, h5, -⟩ := hc
    exact h5.1.2.2.2.2.2.1

/-- **The restart of the writer value receipts is at most the clock.** Consumer:
`stableRunRestartLe`. -/
theorem receiptsRestartLe {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (retired restart : Nat)
    (h : WidthWriterValueReceipts ring root audit retired restart) :
    restart ≤ audit.clock := by
  obtain ⟨first, _, baseCut, structural, _, _, _, hbase, _, _, hchain, _⟩ := h
  exact chainRestartLe ring root audit structural first baseCut hbase.1.2.2.1 hchain

/-- **On every values-stable state the restart is at most the clock** (any digit reference).
Consumer: the start of the labelled comparison phase after the restart
(`L3.PacketMomentCompareStart.cmpLabelStart`, `LabelCut restart` at the start of
`CmpPairStage`). -/
theorem stableRunRestartLe {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (root : Fin n) (restart : Nat) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthStableRun ref root restart x) : restart ≤ x.2.clock := by
  obtain ⟨_, _, retired, _, _, _, _, hrec, -⟩ := hx
  exact receiptsRestartLe ring root x.2 retired restart hrec

end L3.CompareRestart

#print axioms L3.CompareRestart.chainRestartLe
#print axioms L3.CompareRestart.receiptsRestartLe
#print axioms L3.CompareRestart.stableRunRestartLe
