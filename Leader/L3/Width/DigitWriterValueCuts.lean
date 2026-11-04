import Leader.L3.Width.DigitCuts
import Leader.L3.Width.DigitQuiet

/-!
# The successor-value and comparison cuts with the writer-lane structural cut

`BankRepairDigitValueReceipts` (BankRepairDigitValueWave) carries
`DigitFirstCut (DigitStructuralAt …)`, the first time at which every complete pair has a first
strict completion on BOTH lanes, and anchors the writer value chain after it.  Its consumers in
the clean chain use the values-stable and comparison cuts only as stage endpoints (the value-wave
target, the comparison start, the comparison-entry certificate's start class); no proof reads the
comparison-lane half of the structural conjunct.  The block receipts that `WidthReceiptsClose`
starts from are writer-lane facts (`BlockReceipt`: five writer completions), and the paper
orders the comparison lane after the digit-stability cut (repair.tex 1743-1749), so the
comparison-lane half is an event the premise cannot take from its start class.

This module restates the cut family with the writer lane alone in the structural conjunct:

* `DigitWriterStructuralAt`: `DigitStructuralAt` at the writer lane;
* `WidthWriterValueReceipts`: `BankRepairDigitValueReceipts` with `DigitWriterStructuralAt`
  (same first segment, base value cut, value chain anchored after the structural time, coverage);
* `WidthWriterValuesStableCut`, `WidthWriterComparisonCut`: the values-stable and comparison cuts
  on these receipts;
* the premises on them: `WidthWriterReceiptsClose` (receipts of all blocks on a first-zero
  continuation give the writer values-stable cut), the clocks `WidthWriterValueWaveClock`,
  `WidthWriterComparisonClock`, and `WidthWriterComparisonCertificate`.

The comparison lane enters only in the comparison cut, through
`DigitFirstCut (DigitComparisonReady … restart)`.
-/

namespace L3.WriterValueCuts

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.ValueWaveClose

set_option autoImplicit false

/-- The writer-lane structural predicate: every complete pair has a first strict writer
completion at or before `cut`.  Consumer: `WidthWriterValueReceipts`. -/
def DigitWriterStructuralAt {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (A : DigitAudit c n) (cut : Nat) : Prop :=
  cut ≤ A.clock ∧
  ∀ source target : Nat,
    DigitCompletePair ring root A.start source target →
    ∃ terminal : DigitTerminal c n,
      DigitFirstStrictCompletion ring A root source target .writer 0 terminal ∧
      terminal.time ≤ cut

/-- The value receipts with the writer-lane structural cut: first segment, base value cut after
the retirement, the first writer structural cut, the value chain of five writer cohorts after it
and coverage of every complete block.  Consumer: `WidthWriterValuesStableCut`,
`WidthWriterComparisonCut`, `L3.CompareStage.WidthStableRun`. -/
def WidthWriterValueReceipts {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (retired restart : Nat) : Prop :=
  ∃ (first stop baseCut structural last : Nat) (cuts : List (Nat × Nat)),
    DigitFirstSegment ring root audit.start first stop ∧
    DigitBaseValueCut ring root audit 0 retired baseCut ∧
    DigitBoundaryAt ring root audit retired ∧
    DigitFirstCut (DigitWriterStructuralAt ring root audit) structural ∧
    DigitValueChain ring root audit structural first baseCut last restart cuts ∧
    (∀ block : Nat, DigitCompleteBlock ring root audit.start block →
      ∃ stable : Nat, (block, stable) ∈ cuts)

section Cuts

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- The values-stable cut on the writer receipts, on the audit started at a clean start, keeping
the boundary leader receipt (DESIGN-MOTIVATIONS 2026-11-02 08:45).  Consumer: `WidthWriterReceiptsClose`, `WidthWriterValueWaveClock`,
`WidthWriterComparisonClock`, `L3.WriterCore.widthWriterCoreCuts`. -/
def WidthWriterValuesStableCut (z : ref.State) : Prop :=
  ∃ (start : ref.State) (word : List (Fin n)) (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (retired restart : Nat),
    ref.start start ∧
    word.foldl (widthDigitAuditNext ref)
      (start, digitAuditInitial (piD (ref.phys start))) = (z, audit) ∧
    WFixedRoot ring root (piW (ref.phys z)) ∧
    DigitAt ring audit audit.clock (piD (ref.phys z)) audit.current ∧
    WidthWriterValueReceipts ring root audit retired restart ∧
    WidthDigitLeaderReceipt ref z

/-- The comparison cut on the writer receipts: the first comparison-ready cut restarted at the
last value cut, keeping the boundary leader receipt (DESIGN-MOTIVATIONS 2026-11-02 08:45).
Consumer: `WidthWriterComparisonClock`, `WidthWriterComparisonCertificate`,
`L3.CompareStage.WidthComparisonClose`, `L3.WriterCore.WidthWriterPreDrain`. -/
def WidthWriterComparisonCut (z : ref.State) : Prop :=
  ∃ (start : ref.State) (word : List (Fin n)) (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (retired restart comparisonCut : Nat),
    ref.start start ∧
    word.foldl (widthDigitAuditNext ref)
      (start, digitAuditInitial (piD (ref.phys start))) = (z, audit) ∧
    WFixedRoot ring root (piW (ref.phys z)) ∧
    DigitAt ring audit audit.clock (piD (ref.phys z)) audit.current ∧
    WidthWriterValueReceipts ring root audit retired restart ∧
    DigitFirstCut (DigitComparisonReady ring root audit restart) comparisonCut ∧
    WidthDigitLeaderReceipt ref z

/-- R10c premise (receipt conversion, writer structural cut): the receipts of all blocks on a
first-zero continuation carrying the boundary leader receipt give the writer values-stable cut.
Consumer:
`L3.WriterStage.widthWaveClockOfWriter`, `L3.WriterCore.bankWriterValueWaveOfMoments` and the
receipt premise of `l3HeadlineOfCleanBranches`. -/
def WidthWriterReceiptsClose : Prop :=
  ∀ (root : Fin n) (z : ref.State) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
    WidthZeroRun ref root (z, audit) →
    (∀ i, i < valueBlocks n → BlockReceipt ring root audit i) →
    WidthDigitLeaderReceipt ref z →
    WidthWriterValuesStableCut ref z

/-- The value-wave clock into the writer values-stable cut.  Consumer:
`L3.WriterCore.widthWriterCausalCoreOfPremises`. -/
def WidthWriterValueWaveClock (charge : Nat) : Prop :=
  BankRepairDigitChargedStage ref.next (WidthDigitFirstZeroCut ref)
    (WidthWriterValuesStableCut ref) charge

/-- The restarted comparison clock between the writer cuts.  Consumer:
`L3.WriterCore.widthWriterCausalCoreOfPremises`, `L3.CompareStage.smallComparisonClockOfMoments`
and the BANK comparison premise of `l3HeadlineOfCleanBranches`. -/
def WidthWriterComparisonClock (charge : Nat) : Prop :=
  BankRepairDigitChargedStage ref.next (WidthWriterValuesStableCut ref)
    (WidthWriterComparisonCut ref) charge

/-- R10c premise (comparison-entry certificate) at the writer comparison cut: at a drained
comparison cut, a clean word root and the quiet class of the digit machine (the digit values are
its `values` field; dirty bits are free).  `AcceptedReceipts.QDigit` is false here: a dirty cell
interior to the final fragment is not served by the cut (DESIGN-MOTIVATIONS 2026-11-02 14:05).
Consumer: `L3.WriterCore.widthWriterCausalCoreOfPremises` and the certificate premise of
`l3HeadlineOfCleanBranches`. -/
def WidthWriterComparisonCertificate : Prop :=
  ∀ start : ref.State, ref.drained start → WidthWriterComparisonCut ref start →
    ∃ (root : Fin n) (first : Nat),
      CleanWordAtRoot ring root (piW (ref.phys start)) ∧
      L3.DigitQuiet.WidthDigitQuiet ring root first (piD (ref.phys start))

end Cuts

end L3.WriterValueCuts
