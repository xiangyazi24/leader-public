import Leader.L3.Width.WaveCore
import Leader.L3.Width.DigitWriterValueCuts
import Leader.L3.Width.DigitWriterStage
import Leader.L3.Width.DigitClosePersist
import Leader.L3.Bank.RepairDigitReceiptsTruth
import Leader.L3.StageM.Entry

/-!
# Ordered block receipts and the value wave that delivers them

`L3.WriterValueCuts.WidthWriterReceiptsClose` is false on reached states
(close-family-notes section 15, research/lean-l3/wip/r10c-receipts/cex_receipts.py): its
hypothesis `BlockReceipt` (five writer completions after an UNCONSTRAINED time, per block) drops
the time order that its target `DigitValueChain` needs (each pair's five completions after
`max structural previous`).  The block stages of the value wave do produce that order: block
`j`'s completions come after the clock at the start of stage `j`, which is after every earlier
block's receipt, and stage `0` starts at the entry cut, after the writer structural cut and
the base covers.  This module keeps the order:

* `FwdChainBy`: `K` completions after `a`, all recorded by time `b`;
* `OrdData`: every interior block has a strict writer completion by `aft 0`, the base covers
  hold by `aft 0`, and block `i < j` has five completions in `(aft i, aft (i + 1)]`;
* `WidthWriterOrderedReceiptsClose`: the restated receipt conversion (DESIGN-MOTIVATIONS
  2026-11-02, "ordered receipts");
* `WidthOrdEntryCut`, `widthOrdEntryBlockStage`, `widthOrdWaveAfterEntry`: the block stages
  of `L3.WidthWave.widthCleanEntryBlockStage` with the times carried, at the same charge;
* `writerCutOrdEntry`: the writer cut lies in the ordered entry cut `P'' 0`.
-/

namespace L3.WriterOrdered

set_option autoImplicit false

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.ValueWaveClose
open L3.FiveTransfer
open L3.Projection
open L3.Correspondence
open L3.DigitStructuralClean
open L3.DigitCohortScratch
open L3.WidthWave
open L3.WriterValueCuts
open L3.WriterStage

/-! ### Completions recorded in a window -/

section Window

variable {c : Compiled} {n : Nat}

/-- `K` completions with strictly increasing terminal times after `a`, all at most `b`.
Consumer: `OrderedReceipt`. -/
def FwdChainBy (ring : DirectedRing n) (A : DigitAudit c n) (root : Fin n) (source target : Nat)
    (lane : DigitLane) : Nat → Nat → Nat → Prop
  | 0, _, _ => True
  | K + 1, a, b => ∃ t : DigitTerminal c n, DigitCompletion ring A root source target lane 0 t ∧
      a < t.time ∧ t.time ≤ b ∧ FwdChainBy ring A root source target lane K t.time b

/-- Consumer: the lemmas below. -/
theorem fwdChainBySucc (ring : DirectedRing n) (A : DigitAudit c n) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (K a b : Nat) :
    FwdChainBy ring A root source target lane (K + 1) a b =
      ∃ t : DigitTerminal c n, DigitCompletion ring A root source target lane 0 t ∧
        a < t.time ∧ t.time ≤ b ∧ FwdChainBy ring A root source target lane K t.time b := rfl

variable {ring : DirectedRing n} {root : Fin n} {source target : Nat} {lane : DigitLane}

/-- The window chain survives every audit letter.  Consumer: `ordDataStep`. -/
theorem fwdChainByStep (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) :
    ∀ K a b, FwdChainBy ring A root source target lane K a b →
      FwdChainBy ring (digitAuditStep ring S A e) root source target lane K a b := by
  intro K
  induction K with
  | zero => intro _ _ _; exact trivial
  | succ K ih =>
    intro a b h
    rw [fwdChainBySucc] at h
    rw [fwdChainBySucc]
    obtain ⟨t, ht, h1, h2, hr⟩ := h
    exact ⟨t, completionStep ring S A e root source target lane 0 t ht, h1, h2, ih _ _ hr⟩

/-- A lower window end can be lowered.  Consumer: `ordDataSucc`. -/
theorem fwdChainByAnti {A : DigitAudit c n} :
    ∀ K a a' b, a' ≤ a → FwdChainBy ring A root source target lane K a b →
      FwdChainBy ring A root source target lane K a' b := by
  intro K
  induction K with
  | zero => intro _ _ _ _ _; exact trivial
  | succ K _ =>
    intro a a' b hle h
    rw [fwdChainBySucc] at h
    rw [fwdChainBySucc]
    obtain ⟨t, ht, h1, h2, hr⟩ := h
    exact ⟨t, ht, by omega, h2, hr⟩

/-- A chain of completions is recorded by the clock.  Consumer: `ordDataSucc`. -/
theorem fwdChainByOfFwd {A : DigitAudit c n} :
    ∀ K a, FwdChain ring A root source target lane K a →
      FwdChainBy ring A root source target lane K a A.clock := by
  intro K
  induction K with
  | zero => intro _ _; exact trivial
  | succ K ih =>
    intro a h
    rw [fwdChainSucc] at h
    rw [fwdChainBySucc]
    obtain ⟨t, ht, h1, hr⟩ := h
    exact ⟨t, ht, h1, ht.2.2.2.2.2.1, ih _ hr⟩

/-- A chain of at least one completion ends after its lower end and by the clock.  Consumer:
`ordDataSucc`. -/
theorem fwdChainLt {A : DigitAudit c n} (K a : Nat)
    (h : FwdChain ring A root source target lane (K + 1) a) : a < A.clock := by
  rw [fwdChainSucc] at h
  obtain ⟨t, ht, h1, -⟩ := h
  obtain ⟨-, -, -, -, -, hclk, -⟩ := ht
  omega

end Window

/-! ### Ordered receipts -/

section Ordered

variable {n : Nat} (ring : DirectedRing n)

/-- **The ordered receipt of block `i`**: if block `i` (from the first delimiter of the audit
start) is an interior pair, five writer completions of it lie in `(a, b]`.  Consumer:
`OrdData`. -/
def OrderedReceipt (root : Fin n) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (i a b : Nat) : Prop :=
  ∀ first : Nat, DigitFirstDelimiter ring root A.start first →
    2 ≤ first + i * valueSpan n → first + i * valueSpan n + 2 * valueSpan n < n →
    FwdChainBy ring A root (first + i * valueSpan n) (first + i * valueSpan n + valueSpan n)
      DigitLane.writer 5 a b

/-- **Block `i` has a strict writer completion by `b`.**  Consumer: `OrdData`. -/
def StrictBy (root : Fin n) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) (i b : Nat) :
    Prop :=
  ∀ first : Nat, DigitFirstDelimiter ring root A.start first →
    2 ≤ first + i * valueSpan n → first + i * valueSpan n + 2 * valueSpan n < n →
    ∃ tm : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      DigitCompletion ring A root (first + i * valueSpan n)
        (first + i * valueSpan n + valueSpan n) DigitLane.writer 0 tm ∧ tm.time ≤ b

/-- **The ordered receipt data up to block `j`**: every interior block has a strict writer
completion by `aft 0` (the writer structural cut), the two base covers hold by `aft 0`, block
`i < j` has five completions in `(aft i, aft (i + 1)]`, and `aft j` is at most the clock.
Consumer: `WidthOrdEntryCut`, `WidthWriterOrderedReceiptsClose`. -/
def OrdData (root : Fin n) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) (aft : Nat → Nat)
    (j : Nat) : Prop :=
  (∀ i, i < valueBlocks n → StrictBy ring root A i (aft 0)) ∧
  (∃ retired : Nat, DigitTwoBaseCovers ring root A 0 retired (aft 0) ∧
    DigitBoundaryAt ring root A retired) ∧
  (∀ i, i < j → aft i ≤ aft (i + 1) ∧ OrderedReceipt ring root A i (aft i) (aft (i + 1))) ∧
  aft j ≤ A.clock

/-- The times up to `j` kept, the later ones set to `c`.  Consumer: `ordDataSucc`,
`ordDataSkip`. -/
def aftExtend (aft : Nat → Nat) (j c : Nat) : Nat → Nat :=
  fun i => if i ≤ j then aft i else c

/-- **The ordered data survive every audit letter.**  Consumer: `widthOrdEntryBlockStage`. -/
theorem ordDataStep (root : Fin n) (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n) (aft : Nat → Nat) (j : Nat)
    (h : OrdData ring root A aft j) : OrdData ring root (digitAuditStep ring S A e) aft j := by
  obtain ⟨hs, ⟨retired, hc, hb⟩, hr, hj⟩ := h
  refine ⟨fun i hi first hf h1 h2 => ?_, ⟨retired, L3.ClosePersist.coversStep ring S A e root 0
    retired (aft 0) hc, L3.ClosePersist.boundaryAtStep ring S A e root retired hb⟩, fun i hi => ⟨(hr i hi).1, fun first hf h1 h2 =>
      fwdChainByStep S A e 5 _ _ ((hr i hi).2 first hf h1 h2)⟩,
    by show aft j ≤ A.clock + 1; omega⟩
  obtain ⟨tm, htm, hle⟩ := hs i hi first hf h1 h2
  exact ⟨tm, completionStep ring S A e root _ _ DigitLane.writer 0 tm htm, hle⟩

/-- **Block `j`'s receipt closes stage `j`**: five completions after `after ≥ aft j` give the
ordered data up to `j + 1`, with `aft (j + 1)` the clock.  Consumer:
`widthOrdEntryBlockStage`. -/
theorem ordDataSucc (root : Fin n) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (aft : Nat → Nat) (j first after : Nat) (h : OrdData ring root A aft j)
    (hf : DigitFirstDelimiter ring root A.start first) (hle : aft j ≤ after)
    (hc : FwdChain ring A root (first + j * valueSpan n) (first + j * valueSpan n + valueSpan n)
      DigitLane.writer 5 after) :
    OrdData ring root A (aftExtend aft j A.clock) (j + 1) := by
  obtain ⟨hs, hcov, hr, -⟩ := h
  have hlt := fwdChainLt 4 after hc
  have e0 : aftExtend aft j A.clock 0 = aft 0 := by unfold aftExtend; rw [if_pos (by omega)]
  refine ⟨?_, ?_, fun i hi => ?_, ?_⟩
  · rw [e0]; exact hs
  · rw [e0]; exact hcov
  · have ei : aftExtend aft j A.clock i = aft i := by unfold aftExtend; rw [if_pos (by omega)]
    rw [ei]
    by_cases hij : i < j
    · have ei1 : aftExtend aft j A.clock (i + 1) = aft (i + 1) := by
        unfold aftExtend; rw [if_pos (by omega)]
      rw [ei1]
      exact hr i hij
    · have hie : i = j := by omega
      subst hie
      have ei1 : aftExtend aft i A.clock (i + 1) = A.clock := by
        unfold aftExtend; rw [if_neg (by omega)]
      rw [ei1]
      refine ⟨by omega, fun first' hf' _ _ => ?_⟩
      have he := L3.ValueWaveClose.firstDelimUnique ring root _ hf hf'
      subst he
      exact fwdChainByAnti 5 after (aft i) A.clock hle (fwdChainByOfFwd 5 after hc)
  · unfold aftExtend
    rw [if_neg (by omega)]
    exact Nat.le_refl _

/-- **A block with no receipt obligation** passes its time on.  Consumer:
`widthOrdEntryBlockStage`. -/
theorem ordDataSkip (root : Fin n) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (aft : Nat → Nat) (j : Nat) (h : OrdData ring root A aft j)
    (hno : ∀ first, DigitFirstDelimiter ring root A.start first →
      ¬ (2 ≤ first + j * valueSpan n ∧ first + j * valueSpan n + 2 * valueSpan n < n)) :
    OrdData ring root A (aftExtend aft j (aft j)) (j + 1) := by
  obtain ⟨hs, hcov, hr, hj⟩ := h
  have e0 : aftExtend aft j (aft j) 0 = aft 0 := by unfold aftExtend; rw [if_pos (by omega)]
  refine ⟨?_, ?_, fun i hi => ?_, ?_⟩
  · rw [e0]; exact hs
  · rw [e0]; exact hcov
  · have ei : aftExtend aft j (aft j) i = aft i := by unfold aftExtend; rw [if_pos (by omega)]
    rw [ei]
    by_cases hij : i < j
    · have ei1 : aftExtend aft j (aft j) (i + 1) = aft (i + 1) := by
        unfold aftExtend; rw [if_pos (by omega)]
      rw [ei1]
      exact hr i hij
    · have hie : i = j := by omega
      subst hie
      have ei1 : aftExtend aft i (aft i) (i + 1) = aft i := by
        unfold aftExtend; rw [if_neg (by omega)]
      rw [ei1]
      exact ⟨Nat.le_refl _, fun first hf h1 h2 => absurd ⟨h1, h2⟩ (hno first hf)⟩
  · unfold aftExtend
    rw [if_neg (by omega)]
    exact hj

end Ordered

/-! ### The restated premise and the ordered block stages -/

section Stages

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- **The restated receipt conversion** (DESIGN-MOTIVATIONS 2026-11-02, "ordered receipts";
replaces `WidthWriterReceiptsClose`, false on reached states): a first-zero continuation of a
clean start whose audit carries the ordered receipt data of all `K = n / R` blocks and the
boundary leader receipt is in the writer values-stable cut.  Consumer: `widthOrdWaveAfterEntry`
through the ordered wave clocks (`L3.WriterOrderedWave`) and the headline. -/
def WidthWriterOrderedReceiptsClose : Prop :=
  ∀ (root : Fin n) (z : ref.State) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (aft : Nat → Nat),
    WidthZeroRun ref root (z, audit) → OrdData ring root audit aft (valueBlocks n) →
    WidthDigitLeaderReceipt ref z → WidthWriterValuesStableCut ref z

/-- **The ordered block cut `P'' j`**: a first-zero continuation whose audit carries the ordered
receipt data up to block `j` and the pins of the blocks from `j` on.  Consumer:
`widthOrdEntryBlockStage`, `widthOrdWaveAfterEntry`. -/
def WidthOrdEntryCut (j : Nat) (z : ref.State) : Prop :=
  ∃ (root : Fin n) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (aft : Nat → Nat),
    WidthZeroRun ref root (z, audit) ∧ OrdData ring root audit aft j ∧
    WidthPairsFrom ref j root (z, audit)

/-- The pieces of an ordered block cut, by leader and first delimiter.  Consumer:
`widthOrdEntryBlockStage`. -/
def WidthOrdEntryPiece (j : Nat) (root : Fin n) : Option Nat → ref.State → Prop
  | none, z => ∃ (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (aft : Nat → Nat),
      WidthZeroRun ref root (z, audit) ∧
      (∀ first, ¬ DigitFirstDelimiter ring root audit.start first) ∧
      OrdData ring root audit aft j ∧ WidthPairsFrom ref j root (z, audit)
  | some first, z => ∃ (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (aft : Nat → Nat),
      WidthZeroRun ref root (z, audit) ∧ DigitFirstDelimiter ring root audit.start first ∧
      OrdData ring root audit aft j ∧ WidthPairsFrom ref j root (z, audit)

variable (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)

include hfix hn

/-- **The ordered block stage `P'' j → P'' (j + 1)` at `200 n R`**:
`L3.WidthWave.widthCleanEntryBlockStage` with the ordered receipt data carried; the stage of an
interior block starts its window at the current clock, which bounds every earlier receipt.
Consumer: `widthOrdWaveAfterEntry`. -/
theorem widthOrdEntryBlockStage (j : Nat) :
    WidthCoupledBlock ref (WidthOrdEntryCut ref j) (WidthOrdEntryCut ref (j + 1))
      (200 * n * valueSpan n) := by
  have hR := valueSpanTwo hn
  refine widthCoupledBlockSigma ref _ _ _
    (fun p : Fin n × Option Nat => WidthOrdEntryPiece ref j p.1 p.2) ?_ ?_
  · rintro z ⟨root, audit, aft, hrun, hord, hpf⟩
    rcases Classical.em (∃ first, DigitFirstDelimiter ring root audit.start first) with
      ⟨first, hf⟩ | hno
    · exact ⟨(root, some first), audit, aft, hrun, hf, hord, hpf⟩
    · exact ⟨(root, none), audit, aft, hrun, fun f hf => hno ⟨f, hf⟩, hord, hpf⟩
  rintro ⟨root, o⟩
  cases o with
  | none =>
    refine widthCoupledBlockOfImp ref _ _ _ ?_
    rintro z ⟨audit, aft, hrun, hno, hord, hpf⟩
    exact ⟨root, audit, aftExtend aft j (aft j), hrun,
      ordDataSkip ring root audit aft j hord (fun first hf => absurd hf (hno first)),
      widthPairsFromSucc ref j root _ hpf⟩
  | some first =>
    rcases Classical.em (2 ≤ first + j * valueSpan n ∧
        first + j * valueSpan n + 2 * valueSpan n < n) with ⟨hsrc, hend⟩ | hg
    · refine widthCoupledBlockSigma ref _ _ _
        (fun after z => ∃ (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
          (aft : Nat → Nat),
          WidthZeroRun ref root (z, audit) ∧ DigitFirstDelimiter ring root audit.start first ∧
          OrdData ring root audit aft j ∧ WidthPairsFrom ref j root (z, audit) ∧
          audit.clock = after) ?_ ?_
      · rintro z ⟨audit, aft, hrun, hf, hord, hpf⟩
        exact ⟨audit.clock, audit, aft, hrun, hf, hord, hpf, rfl⟩
      intro after
      refine widthRunPairBlock ref hfix hn root DigitLane.writer (first + j * valueSpan n)
        (valueSpan n) hR hsrc (by omega) (InheritedOk DigitLane.writer) after _ _
        (fun w => WidthZeroRun ref root w.1 ∧
          DigitFirstDelimiter ring root w.1.2.start first ∧
          (∃ aft : Nat → Nat, OrdData ring root w.1.2 aft j ∧ aft j ≤ after) ∧
          WidthPairsFrom ref (j + 1) root w.1) ?_ ?_ ?_
      · intro w e _ hc
        obtain ⟨aft, hord, hle⟩ := hc.2.2.1
        exact ⟨widthZeroRunStep ref root w.1 hc.1 e, hc.2.1,
          ⟨aft, ordDataStep ring root _ w.1.2 e aft j hord, hle⟩,
          widthPairsFromStep ref hfix hn (j + 1) root w.1 e hc.2.2.2⟩
      · rintro z ⟨audit, aft, hrun, hf, hord, hpf, haft⟩
        obtain ⟨hp, g, hw, hu⟩ := hpf first hf j (Nat.le_refl j) hsrc hend
        have hle : aft j ≤ after := by rw [← haft]; exact hord.2.2.2
        exact ⟨((z, audit), (g.1, 0)), rfl,
          widthWinInvDReset ref root DigitLane.writer _ _ _ (z, audit) g hw 0,
          widthUseReachReset ref root DigitLane.writer _ _ (z, audit) g hu, rfl,
          by show after ≤ audit.clock; omega, hp, hrun, hf, ⟨aft, hord, hle⟩,
          widthPairsFromSucc ref j root _ hpf⟩
      · intro w hfw hc
        obtain ⟨aft, hord, hle⟩ := hc.2.2.1
        exact ⟨root, w.1.2, aftExtend aft j w.1.2.clock, hc.1,
          ordDataSucc ring root w.1.2 aft j first after hord hc.2.1 hle hfw, hc.2.2.2⟩
    · refine widthCoupledBlockOfImp ref _ _ _ ?_
      rintro z ⟨audit, aft, hrun, hf, hord, hpf⟩
      refine ⟨root, audit, aftExtend aft j (aft j), hrun,
        ordDataSkip ring root audit aft j hord (fun first' hf' => ?_),
        widthPairsFromSucc ref j root _ hpf⟩
      have he := L3.ValueWaveClose.firstDelimUnique ring root _ hf hf'
      subst he
      exact hg

/-- **The value wave after the ordered entry, to any target closed under the ordered
receipts**: `K = n / R` ordered block stages of `200 n R` from `P'' 0` to `P'' K`, then the
target `Q`, within `200 n^2`.  Consumer: the ordered wave clocks (`L3.WriterOrderedWave`). -/
theorem widthOrdWaveAfterEntry (Q : ref.State → Prop)
    (hclose : ∀ (root : Fin n) (z : ref.State)
      (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (aft : Nat → Nat),
      WidthZeroRun ref root (z, audit) → OrdData ring root audit aft (valueBlocks n) → Q z) :
    BankRepairDigitChargedStage ref.next (WidthOrdEntryCut ref 0) Q
      (bankRepairDigitValueWaveMicroCharge n) :=
  bankRepairDigitChargedMono _ _ _ (blockFit (valueBlocksFit n))
    (bankRepairDigitChargedWeaken _ (WidthOrdEntryCut ref 0) (WidthOrdEntryCut ref 0)
      (WidthOrdEntryCut ref (valueBlocks n)) _ _ (fun _ h => h)
      (fun z ⟨root, audit, aft, hrun, hord, _⟩ => hclose root z audit aft hrun hord)
      (bankRepairDigitChargedChain _ (WidthOrdEntryCut ref) _
        (fun j => widthChargedOfCoupledBlock ref _ _ _ (widthOrdEntryBlockStage ref hfix hn j))
        (valueBlocks n)))

end Stages

/-! ### Entry: the writer cut lies in `P'' 0` -/

section Entry

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- The base covers of a first-zero continuation hold at its clock.  Consumer:
`writerCutOrdEntry`, `L3.WriterOrderedWave.structuralCutOrdEntry`. -/
theorem zeroRunCovers (root : Fin n) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthZeroRun ref root x) :
    ∃ retired : Nat, DigitTwoBaseCovers ring root x.2 0 retired x.2.clock ∧
      DigitBoundaryAt ring root x.2 retired := by
  obtain ⟨start, word0, word, y, retired, -, -, -, -, hC, hBd, hx⟩ := h
  have keyB : ∀ (w : List (Fin n)) (v : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      DigitBoundaryAt ring root v.2 retired →
      DigitBoundaryAt ring root (w.foldl (widthDigitAuditNext ref) v).2 retired := by
    intro w
    induction w with
    | nil => intro v hv; exact hv
    | cons e rest ih =>
      intro v hv
      exact ih (widthDigitAuditNext ref v e)
        (L3.ClosePersist.boundaryAtStep ring (piD (ref.phys v.1)) v.2 e root retired hv)
  have hB2 := keyB word y hBd
  rw [hx] at hB2
  refine ⟨retired, ?_, hB2⟩
  have key : ∀ (w : List (Fin n)) (v : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      DigitTwoBaseCovers ring root v.2 0 retired y.2.clock →
      DigitTwoBaseCovers ring root (w.foldl (widthDigitAuditNext ref) v).2 0 retired y.2.clock := by
    intro w
    induction w with
    | nil => intro v hv; exact hv
    | cons e rest ih =>
      intro v hv
      exact ih (widthDigitAuditNext ref v e)
        (L3.ClosePersist.coversStep ring (piD (ref.phys v.1)) v.2 e root 0 retired y.2.clock hv)
  have h1 := key word y hC
  rw [hx] at h1
  exact L3.BlockEntry.bankRepairDigitTwoBaseCoversCutMono ring root x.2 0 retired y.2.clock h1

/-- **The writer cut lies in the ordered entry cut `P'' 0`** (same state, same audit, `aft` the
clock): the writer cut's first strict completions are recorded by the clock, the base covers of
the first-zero continuation hold at the clock, and the pins come from
`L3.StageMEntry.pairPinOfCompletion`.  Consumer: the SMALL ordered wave clock
(`L3.WriterOrderedWave`). -/
theorem writerCutOrdEntry (hpin : L3.StageMEntry.WidthPinAfterStrict ref) (z : ref.State)
    (h : WidthDigitWriterCut ref z) : WidthOrdEntryCut ref 0 z := by
  obtain ⟨root, audit, hrun, hdone⟩ := h
  refine ⟨root, audit, fun _ => audit.clock, hrun, ⟨fun i _ first hf _ hend => ?_,
    zeroRunCovers ref root (z, audit) hrun, fun i hi => absurd hi (Nat.not_lt_zero i),
    Nat.le_refl _⟩, ?_⟩
  · obtain ⟨tm, htm⟩ := hdone i first hf hend
    exact ⟨tm, htm, htm.2.2.2.2.2.1⟩
  · intro first hf i _ h2 hend
    obtain ⟨tm, htm⟩ := hdone i first hf hend
    exact L3.StageMEntry.pairPinOfCompletion ref hpin root (z, audit) hrun _ tm h2 hend htm

end Entry

end L3.WriterOrdered

#print axioms L3.WriterOrdered.fwdChainByStep
#print axioms L3.WriterOrdered.fwdChainByAnti
#print axioms L3.WriterOrdered.fwdChainByOfFwd
#print axioms L3.WriterOrdered.ordDataStep
#print axioms L3.WriterOrdered.ordDataSucc
#print axioms L3.WriterOrdered.ordDataSkip
#print axioms L3.WriterOrdered.widthOrdEntryBlockStage
#print axioms L3.WriterOrdered.widthOrdWaveAfterEntry
#print axioms L3.WriterOrdered.zeroRunCovers
#print axioms L3.WriterOrdered.writerCutOrdEntry
