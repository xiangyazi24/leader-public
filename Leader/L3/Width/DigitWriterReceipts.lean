import Leader.L3.Width.DigitWriterValueCuts
import Leader.L3.Width.WaveCore
import Leader.L3.Width.DigitBoundary

/-!
# The writer structural cut follows from the block receipts, on the reached start class

The receipt conversion `WidthWriterReceiptsClose` starts from the first-zero continuations
carrying the block receipts of all `K = n / R` blocks (`BlockReceipt`: five writer completions,
each a strict completion `DigitCompletion … .writer 0`).  Its target carries
`DigitFirstCut (DigitWriterStructuralAt …)`.  This module proves that this conjunct is no extra
event: at every state of the start class, on the clean start of a boundary reference, the first
writer structural cut exists.

* `writerStructuralOfReceipts`: with the delimiters of the audit start at `first + j R`
  (`2 ≤ first`), the receipts of all blocks give the first writer structural cut.
* `writerStructuralAtZeroRun`: at every first-zero continuation of the clean start of a boundary
  reference, the receipts of all blocks give the first writer structural cut; the
  delimiters come from `widthCleanBoundaryDelimiters` at the clean start.
* `chargedStageReach`: a charged first-hit stage reaches its target from every start state.
* `receiptStartReached`: from every pinned entry state `P' 0`, the proved block stages of the
  wave reach a state of the start class of `WidthWriterReceiptsClose`, at which the first writer
  structural cut exists.  So the start class is reached whenever the entry cut is, and on it the
  restated premise does not assert the structural event.

The both-lane conjunct of `BankRepairDigitValueReceipts` has no such derivation: the block
receipts record writer terminals only (`digitReceiptLane .writer`), and nothing in them constrains
the comparison receipts of the same frames.
-/

namespace L3.WriterReceipts

open L3
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.WidthDigit
open L3.ValueWaveClose
open L3.WriterValueCuts
open L3.DigitCohortScratch
open L3.DigitPairsClean
open L3.FiveTransfer
open L3.DigitStructuralClean

set_option autoImplicit false

/-- **Receipts give the first writer structural cut**: if the delimiters of the audit start are
the positions `first + j R` (`2 ≤ first`) and every block `i < K` has its receipt, every complete
pair has a strict writer completion recorded by the clock, so the first writer structural cut
exists.  Consumer: `writerStructuralAtZeroRun`. -/
theorem writerStructuralOfReceipts {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (root : Fin n) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (first : Nat)
    (h2 : 2 ≤ first)
    (hb : ∀ k, 0 < k → k < n →
      ((audit.start (digitSite ring root k)).word.beta = true ↔
        first ≤ k ∧ (k - first) % digitSpan (compileAdvice (ceilLogTwo n)) = 0))
    (hrec : ∀ i, i < valueBlocks n → BlockReceipt ring root audit i) :
    ∃ s, DigitFirstCut (DigitWriterStructuralAt ring root audit) s := by
  have hR := valueSpanTwo hn
  have hSA : DigitWriterStructuralAt ring root audit audit.clock := by
    refine ⟨Nat.le_refl _, fun source target hpair => ?_⟩
    obtain ⟨⟨⟨hs0, hsn, hsb⟩, -, -, -, -⟩, -⟩ := hpair.1
    obtain ⟨hfs, hmod⟩ := (hb source hs0 hsn).1 hsb
    have htg := hpair.2.1
    have hend2 := hpair.2.2.2
    have hfd : DigitFirstDelimiter ring root audit.start first :=
      firstDelimOf ring root audit.start first hb (by omega) (by omega)
    generalize hRv : valueSpan n = R at hR
    have hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R := hRv
    rw [hRd] at hmod htg hend2
    have hsrc : source = first + (source - first) / R * R := by
      have := Nat.div_add_mod (source - first) R
      rw [hmod, Nat.add_zero, Nat.mul_comm] at this
      omega
    generalize (source - first) / R = i at hsrc
    have hle : (i + 1) * R ≤ n := by
      rw [Nat.add_mul]
      omega
    have hi : i < valueBlocks n := by
      unfold valueBlocks
      rw [hRv]
      exact Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le (by omega)).2 hle)
    have hc : ∃ after, FwdChain ring audit root (first + i * R) (first + i * R + R)
        DigitLane.writer 5 after := by
      have h := hrec i hi first hfd
      rw [hRv] at h
      exact h (by omega) (by omega)
    obtain ⟨after, hch⟩ := hc
    have hch' : FwdChain ring audit root (first + i * R) (first + i * R + R)
        DigitLane.writer (4 + 1) after := hch
    rw [fwdChainSucc] at hch'
    obtain ⟨tm, htm, -⟩ := hch'
    rw [← hsrc] at htm
    rw [htg]
    obtain ⟨t1, ht1⟩ := firstStrictOfCompletion ring audit root source (source + R)
      DigitLane.writer 0 ⟨tm, htm⟩
    exact ⟨t1, ht1, ht1.1.2.2.2.2.2.1⟩
  obtain ⟨s, hs, hmin⟩ := existsFirst (DigitWriterStructuralAt ring root audit) ⟨_, hSA⟩
  exact ⟨s, hs, hmin⟩

/-- The audit start is carried by the coupled step.  Consumer: `writerStructuralAtZeroRun`. -/
theorem widthAuditStartFold {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) :
    ∀ (word : List (Fin n)) (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      (word.foldl (widthDigitAuditNext ref) q).2.start = q.2.start := by
  intro word
  induction word with
  | nil => intro q; rfl
  | cons e rest ih => intro q; exact ih _

/-- **The writer structural cut on the start class of the receipt conversion**: at every
first-zero continuation of the clean start of a boundary reference whose audit
carries the receipts of all blocks, the first writer structural cut exists.  Consumer:
`receiptStartReached` and the producer of `WidthWriterReceiptsClose` (its structural
conjunct). -/
theorem writerStructuralAtZeroRun {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (z : ref.State) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hrun : WidthZeroRun ref.toWidthDigitReference root (z, audit))
    (hrec : ∀ i, i < valueBlocks n → BlockReceipt ring root audit i) :
    ∃ s, DigitFirstCut (DigitWriterStructuralAt ring root audit) s := by
  obtain ⟨start, word0, word, y, retired, hst, hfold0, hW, -, -, -, hfold⟩ := hrun
  obtain ⟨root0, hs, hL⟩ := widthCleanBoundaryRoot ref start hst
  obtain ⟨first, ht, -, hb⟩ := widthCleanBoundaryDelimiters ref hn root0 start hL
  have hy1 : y.1 = word0.foldl ref.next start := by
    have := widthBoundaryDigitBoundaryAuditFirst ref start
      (digitAuditInitial (piD (ref.phys start))) word0
    rw [hfold0] at this
    exact this
  have hW0 : WFixedRoot ring root0 (piW (ref.phys y.1)) := by
    rw [hy1]
    exact widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root0 start hs word0
  have hr : root = root0 := hW0.2.1 root hW.1
  subst hr
  have hstart : audit.start = piD (ref.phys start) := by
    have h1 := widthAuditStartFold ref.toWidthDigitReference word y
    have h0 := widthAuditStartFold ref.toWidthDigitReference word0
      (start, digitAuditInitial (piD (ref.phys start)))
    rw [hfold] at h1
    rw [hfold0] at h0
    rw [h1, h0]
    rfl
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  refine writerStructuralOfReceipts ring hn root audit first (by omega) ?_ hrec
  rw [hstart]
  exact hb

/-- **A charged first-hit stage reaches its target**: from every start state some word hits the
target (otherwise every word pays its full length and the cost at horizon `c + 1` exceeds the
charge).  Consumer: `receiptStartReached`. -/
theorem chargedStageReach {S : Type} {n : Nat} (hn : 0 < n) (next : S → Fin n → S)
    (A Q : S → Prop) (c : Nat) (h : BankRepairDigitChargedStage next A Q c)
    (x : S) (hx : A x) : ∃ w : List (Fin n), Q (w.foldl next x) := by
  classical
  refine Classical.byContradiction fun hno => ?_
  have hnever : ∀ (w : List (Fin n)) (y : S), (∃ v : List (Fin n), y = v.foldl next x) → ¬ Q (w.foldl next y) := by
    rintro w y ⟨v, rfl⟩ hq
    exact hno ⟨v ++ w, by rw [List.foldl_append]; exact hq⟩
  have hfull : ∀ (T : Nat) (y : S), (∃ v : List (Fin n), y = v.foldl next x) →
      costNumerator next Q y T = n ^ T * T := by
    intro T
    induction T with
    | zero => intro y _; simp
    | succ T ih =>
        intro y hy
        have hqy : ¬ Q y := hnever [] y hy
        rw [costNumerator_succ next Q y hqy T]
        rw [ofFn_sum_eq _ (fun _ => n ^ T * T) (fun e => ih (next y e) (by
          obtain ⟨v, rfl⟩ := hy
          exact ⟨v ++ [e], by rw [List.foldl_append]; rfl⟩)), ofFn_sum_const]
        rw [Nat.pow_succ]
        grind
  have hc := h x hx (c + 1)
  rw [hfull (c + 1) x ⟨[], rfl⟩] at hc
  have hpos : 0 < n ^ (c + 1) := Nat.pow_pos hn
  rw [Nat.mul_succ] at hc
  omega

/-- **The start class of the receipt conversion is reached, with its structural conjunct**: from
every pinned entry state `P' 0` of a boundary reference, the proved block stages of the
wave (`L3.WidthWave.widthCleanWaveAfterEntry` with the start class itself as target) reach a
first-zero continuation carrying the receipts of all blocks, at which the first writer
structural cut exists (`writerStructuralAtZeroRun`).  Consumer: the non-vacuity check of
`WidthWriterReceiptsClose` (research/lean-l3/ledgers/SMALL-emax-notes.md section 10). -/
theorem receiptStartReached {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (z : ref.State) (hz : WidthEntryCut ref.toWidthDigitReference 0 z) :
    ∃ (w : List (Fin n)) (root : Fin n) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
      WidthZeroRun ref.toWidthDigitReference root (w.foldl ref.next z, audit) ∧
      (∀ i, i < valueBlocks n → BlockReceipt ring root audit i) ∧
      ∃ s, DigitFirstCut (DigitWriterStructuralAt ring root audit) s := by
  have hstage := L3.WidthWave.widthCleanWaveAfterEntry ref.toWidthDigitReference
    ref.singletonFixed hn
    (fun y => ∃ (root : Fin n) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
      WidthZeroRun ref.toWidthDigitReference root (y, audit) ∧
      (∀ i, i < valueBlocks n → BlockReceipt ring root audit i))
    (fun root y audit h1 h2 => ⟨root, audit, h1, h2⟩)
  obtain ⟨w, root, audit, hrun, hrec⟩ :=
    chargedStageReach (by omega) ref.next _ _ _ hstage z hz
  exact ⟨w, root, audit, hrun, hrec,
    writerStructuralAtZeroRun ref hn root _ audit hrun hrec⟩

end L3.WriterReceipts

#print axioms L3.WriterReceipts.writerStructuralOfReceipts
#print axioms L3.WriterReceipts.writerStructuralAtZeroRun
#print axioms L3.WriterReceipts.chargedStageReach
#print axioms L3.WriterReceipts.receiptStartReached
