import Leader.L3.Width.DigitWriterCurrentUseStruct
import Leader.L3.Width.DigitWriterCurrentAged

/-!
# Writer currentness: the residual keeps only the age of the operands

`WriterAgedCore ref` is `WriterAgedBody ref` with the structural half of the aged uses removed: for
every use of every target ledger at the terminal state of the fifth next writer completion it asks
only that the operand is a sample stamped after `after`.  The rest of `UseAged` (the use is no later
than the clock, the sample is earlier than the use, of the writer lane, at a cell of the source
window) is `usesStructural`, a theorem on the clean run of a complete pair.

Consumer: `writersCurrentOfCoreBank`.
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

/-- **Every use of every target ledger is structurally sound on the clean run of a complete
pair** (boundary reference).

Consumer: `writerAgedBodyOfCore`. -/
theorem usesStructural (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (start : ref.State)
    (hL : WidthBoundaryDigitLayoutValues ref root start) (source : Nat)
    (hpair : DigitCompletePair ring root (piD (ref.phys start)) source
      (source + digitSpan (compileAdvice (ceilLogTwo n)))) (u : List (Fin n)) :
    UseStructInv ring root source (digitSpan (compileAdvice (ceilLogTwo n)))
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2 := by
  obtain ⟨hsrc, hend, hlay⟩ := pairLayoutStart ref hn root start hL source hpair
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  have h0 : StructBundle ref.toWidthDigitReference root source
      (digitSpan (compileAdvice (ceilLogTwo n))) (start, digitAuditInitial (piD (ref.phys start))) := by
    refine ⟨hlay, ghostCorrDistinctInitial ring root _ _ _ _, carryAll_initial _, ?_⟩
    intro q L h1 h2 hq u' hu'
    have hq'' : (digitGhostInitial (piD (ref.phys start))
        (digitSite ring root (source + q))).writer.carry = some L := hq
    by_cases hw : ((piD (ref.phys start)) (digitSite ring root (source + q))).top.wCarry.isW = true
    · simp [digitGhostInitial, DigitGhost.initial, DigitLaneGhost.initial, digitLaneView, hw]
        at hq''
      rw [← hq''] at hu'
      simp at hu'
    · simp [digitGhostInitial, DigitGhost.initial, DigitLaneGhost.initial, digitLaneView, hw]
        at hq''
  exact (useStructRun ref.toWidthDigitReference ref.singletonFixed hn root source _ hR hsrc hend u
    _ h0).2.2.2

/-- **The residual of the writer entry content, age only**: every tracked atom and the operand of
every use of every target ledger is a sample stamped after `after`, at the terminal state of the
fifth next writer completion.

Consumer: `writerAgedBodyOfCore`. -/
def WriterAgedCore (ref : WidthDigitReference ring) : Prop :=
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
      ∀ use, use ∈ L.uses → ∃ id : DigitStamp n, use.operand = some (.sampled id) ∧
        after < id.time)

/-- **`WriterAgedBody` from `WriterAgedCore`** (boundary reference).

Consumer: `writersCurrentOfCoreBank`. -/
theorem writerAgedBodyOfCore (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hcore : WriterAgedCore ref.toWidthDigitReference) :
    WriterAgedBody ref.toWidthDigitReference := by
  intro root start u source after T hst hs hpair hT hTc
  obtain ⟨hA1, hA2⟩ := hcore root start u source after T hst hs hpair hT hTc
  refine ⟨hA1, ?_⟩
  intro q h1 h2 L hL use hu
  obtain ⟨root0, hs0, hL0⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root0 :=
    (ref.singletonFixed root0 start hs0).2.1 root (ref.singletonFixed root start hs).1
  subst hr
  have hst' := usesStructural ref hn root start hL0 source hpair u q L h1 h2 hL use hu
  obtain ⟨id, hop, hage⟩ := hA2 q h1 h2 L hL use hu
  obtain ⟨ht, hid⟩ := hst'
  obtain ⟨hlt, hlane, hsite⟩ := hid id hop
  exact ⟨ht, id, hop, hage, hlt, hlane, hsite⟩

open L3.WriterValueCuts in
/-- **`DigitWritersCurrent` at the BANK writer comparison cut from the age of the tracked atoms
and of the operands of the target ledgers alone.**

Consumer: the BANK case of the writer comparison certificate (second conjunct). -/
theorem writersCurrentOfCoreBank (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcore : WriterAgedCore (bankWidthDigitReference ring hn hbank))
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
  writersCurrentOfAgedBank hn hbank
    (writerAgedBodyOfCore (bankWidthBoundaryReference ring hn hbank) hn hcore) start word
    root z audit retired restart hst hfold hW hrec

end L3.WriterCurrent

#print axioms L3.WriterCurrent.usesStructural
#print axioms L3.WriterCurrent.writersCurrentOfCoreBank
