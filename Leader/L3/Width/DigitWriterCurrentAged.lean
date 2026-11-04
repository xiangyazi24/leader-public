import Leader.L3.Width.DigitWriterCurrentOrderRun
import Leader.L3.Width.DigitWriterCurrentAge

/-!
# Writer currentness: the residual without the inheritance clause

`WriterAgedBody ref` is `WriterAgeBody ref` without the clause "every ghost carry of the target
window is non-inherited": that clause is a theorem on the clean run of a complete pair
(`windowNoInherited`, from `orderInvRun`), once one writer terminal with a non-inherited ledger on
the last target cell is recorded, which `DigitCompletion` provides.

What is left (`WriterAgedBody`) is the age of the content of the window at the terminal state of
the fifth next writer completion: every tracked atom was sampled after `after` (A1) and every use
of every target ledger reads an operand sampled after `after` (A2b).

Consumer: `writersCurrentOfAgedBank`.
-/

namespace L3.WriterCurrent

set_option autoImplicit false

open L3
open L3.WidthDigit
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CurrentWin
open L3.WidthWave
open L3.CloseEntry
open L3.ValueWaveClose

variable {n : Nat} {ring : DirectedRing n}

/-- **The order invariant holds at the start.**  Consumer: `windowNoInherited`. -/
theorem orderInvInitial (ref : WidthDigitReference ring) (root : Fin n) (src R : Nat)
    (start : ref.State) (hlay : WidthCohortLayout ref root src R start) :
    OrderInv ref root src R (start, digitAuditInitial (piD (ref.phys start))) := by
  refine ⟨hlay, carryAll_initial _, ?_, ?_⟩
  · intro q q' L L' h1 h2 h3 hq hq' hinh
    exfalso
    have hq'' : (digitGhostInitial (piD (ref.phys start))
        (digitSite ring root (src + q'))).writer.carry = some L' := hq'
    by_cases hw : ((piD (ref.phys start)) (digitSite ring root (src + q'))).top.wCarry.isW = true
    · simp [digitGhostInitial, DigitGhost.initial, DigitLaneGhost.initial, digitLaneView, hw]
        at hq''
      rw [← hq''] at hinh
      simp at hinh
    · simp [digitGhostInitial, DigitGhost.initial, DigitLaneGhost.initial, digitLaneView, hw]
        at hq''
  · intro T L hT
    obtain ⟨f, hf, -⟩ := hT
    simp [digitAuditInitial] at hf

/-- **After a recorded writer completion of a complete pair, no carry of the target window is
inherited** (boundary reference, clean run).

Consumer: `writerAgeBodyOfAged`. -/
theorem windowNoInherited (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (start : ref.State)
    (hL : WidthBoundaryDigitLayoutValues ref root start) (source : Nat)
    (hpair : DigitCompletePair ring root (piD (ref.phys start)) source
      (source + digitSpan (compileAdvice (ceilLogTwo n)))) (u : List (Fin n))
    (T : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (hT : DigitRecordedTerminal
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2 T)
    (hlane : T.lane = DigitLane.writer)
    (hsrcT : T.source = digitSite ring root
      (source + (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1)))
    (hled : T.ledger = some L) (hinh : L.inherited = none) :
    NoInhWin (digitSpan (compileAdvice (ceilLogTwo n)))
      (winCarry ring root source
        (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))).2.current) := by
  obtain ⟨hsrc, hend, hlay⟩ := pairLayoutStart ref hn root start hL source hpair
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  have hrun := orderInvRun ref.toWidthDigitReference ref.singletonFixed hn root source _ hR hsrc
    hend u _ (orderInvInitial ref.toWidthDigitReference root source _ start hlay)
  exact hrun.2.2.2 T L hT hlane hsrcT hled hinh

/-- **The residual of the writer entry content**: the aged tracked atoms (A1) and the aged uses
of every target ledger (A2b) at the terminal state of the fifth next writer completion.

Consumer: `writerAgeBodyOfAged`. -/
def WriterAgedBody (ref : WidthDigitReference ring) : Prop :=
  ∀ (root : Fin n) (start : ref.State) (u : List (Fin n)) (source after : Nat)
    (T : DigitTerminal (compileAdvice (ceilLogTwo n)) n),
    ref.start start → ref.singleton root start →
    DigitCompletePair ring root (piD (ref.phys start)) source
      (source + digitSpan (compileAdvice (ceilLogTwo n))) →
    DigitFiveCompletions ring
      (u.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2
      root source (source + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.writer after T →
    T.time =
      (u.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2.clock →
    (∀ q (x : DigitAtom n),
      trackedAt (digitSpan (compileAdvice (ceilLogTwo n)))
        (laneCells ring root DigitLane.writer source
          (u.foldl (widthDigitAuditNext ref)
            (start, digitAuditInitial (piD (ref.phys start)))).2.current) q = some x →
      AgedAtom after x) ∧
    (∀ q, digitSpan (compileAdvice (ceilLogTwo n)) ≤ q →
      q < 2 * digitSpan (compileAdvice (ceilLogTwo n)) →
      ∀ L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n,
      (laneCells ring root DigitLane.writer source
        (u.foldl (widthDigitAuditNext ref)
          (start, digitAuditInitial (piD (ref.phys start)))).2.current q).carry = some L →
      ∀ use, use ∈ L.uses → UseAged ring root DigitLane.writer source
        (digitSpan (compileAdvice (ceilLogTwo n))) after
        (u.foldl (widthDigitAuditNext ref)
          (start, digitAuditInitial (piD (ref.phys start)))).2.clock use)

/-- **`WriterAgeBody` from `WriterAgedBody`** (boundary reference): the inheritance clause is
derived from the first completion of the five.

Consumer: `writersCurrentOfAgedBank`. -/
theorem writerAgeBodyOfAged (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hbody : WriterAgedBody ref.toWidthDigitReference) :
    WriterAgeBody ref.toWidthDigitReference := by
  intro root start u source after T hst hs hpair hT hTc
  obtain ⟨hA1, hA2⟩ := hbody root start u source after T hst hs hpair hT hTc
  refine ⟨hA1, ?_⟩
  intro q h1 h2 L hL
  refine ⟨?_, hA2 q h1 h2 L hL⟩
  obtain ⟨root0, hs0, hL0⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root0 :=
    (ref.singletonFixed root0 start hs0).2.1 root (ref.singletonFixed root start hs).1
  subst hr
  obtain ⟨t1, -, -, -, h1', -, -, -, -⟩ := hT
  obtain ⟨-, hrec, hlane, hsrcT, -, -, hpos, ledger, samples, exports, uses, hled, hinh, -⟩ :=
    h1'.1
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  have hsrcT' : t1.source = digitSite ring root
      (source + (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1)) := by
    rw [hsrcT]
    congr 1
    omega
  have hnoinh := windowNoInherited ref hn root start hL0 source hpair u t1 ledger hrec hlane
    hsrcT' hled hinh
  exact hnoinh q L h1 h2 hL

open L3.WriterValueCuts in
/-- **`DigitWritersCurrent` at the BANK writer comparison cut from the aged atoms and the aged
uses alone** (the inheritance clause, `LiveE` and the non-empty ledgers are theorems).

Consumer: the BANK case of the writer comparison certificate (second conjunct). -/
theorem writersCurrentOfAgedBank (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hbody : WriterAgedBody (bankWidthDigitReference ring hn hbank))
    (start : BankReferenceState ring hbank) (word : List (Fin n)) (root : Fin n)
    (z : BankReferenceState ring hbank)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (retired restart : Nat)
    (hst : (bankWidthDigitReference ring hn hbank).start start)
    (hfold : word.foldl (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (start, digitAuditInitial (piD ((bankWidthDigitReference ring hn hbank).phys start))) =
      (z, audit))
    (hW : WFixedRoot ring root (piW ((bankWidthDigitReference ring hn hbank).phys z)))
    (hrec : WidthWriterValueReceipts ring root audit retired restart) :
    ∃ (structural first baseCut last : Nat) (cuts : List (Nat × Nat)),
      DigitValueChain ring root audit structural first baseCut last restart cuts ∧
      DigitWritersCurrent ring root audit
        (piD ((bankWidthDigitReference ring hn hbank).phys z)) audit.current structural
        audit.clock cuts :=
  writersCurrentOfBodyBank hn hbank
    (writerAgeBodyOfAged (bankWidthBoundaryReference ring hn hbank) hn hbody) start word
    root z audit retired restart hst hfold hW hrec

end L3.WriterCurrent

#print axioms L3.WriterCurrent.writersCurrentOfAgedBank
#print axioms L3.WriterCurrent.windowNoInherited
#print axioms L3.WriterCurrent.writerAgeBodyOfAged
