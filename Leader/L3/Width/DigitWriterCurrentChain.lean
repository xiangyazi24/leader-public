import Leader.L3.Width.DigitWriterCurrentEntry
import Leader.L3.Width.DigitClosePersist

/-!
# Writer currentness at the writer comparison cut, from the entry content

`DigitWritersCurrent` (`Target.lean`) asks that every complete pair `(source, target)` has a stable
cut `(source, stable)` in the value chain's list of cuts at which the writer lane of the pair is
current at the clock.  The value chain gives, for every target block, the fifth next writer
completion `T` of the pair after `max structural stable`, with `T.time` the stable cut of the
target.  This module assembles:

* `chainPath`: every cut of a `DigitValueChain` other than the first comes from a chain step whose
  source is also a cut, with the `DigitFiveCohortCompletions` of the step;
* `fiveCompletionsFoldBack`: the five completions of an extended run hold at the prefix that ends
  at the fifth terminal;
* `writersCurrentOfCore`: from `WriterEntryCore`, the window class enters at the fifth terminal,
  is carried to the cut, and `DigitWritersCurrent` holds at the writer comparison cut.

`WriterEntryCore` is the only unproved input (see `WidthDigitWriterCurrentEntry`).

Consumer: the writer comparison certificate (second conjunct), via the physical value step.
-/

namespace L3.WriterCurrent

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WriterValueCuts
open L3.ClosePersist
open L3.CloseEntry
open L3.CloseCurrent
open L3.CloseBoundary
open L3.ValueWaveClose

section Chain

variable {c : Compiled} {n : Nat} {ring : DirectedRing n}

/-- **Every cut of a value chain is the first cut or comes from a chain step** from a cut of the
chain with its five cohort completions; the head of the cut list is `(source, previous)`.

Consumer: `writersCurrentOfCore`. -/
theorem chainPath {root : Fin n} {A : DigitAudit c n} {structural first baseCut : Nat}
    {source previous : Nat} {cuts : List (Nat × Nat)}
    (h : DigitValueChain ring root A structural first baseCut source previous cuts) :
    (source, previous) ∈ cuts ∧
      ∀ target st : Nat, (target, st) ∈ cuts →
        target = first ∨
        ∃ (src stable : Nat) (terminal : DigitTerminal c n),
          (src, stable) ∈ cuts ∧ DigitCompletePair ring root A.start src target ∧
          DigitFiveCohortCompletions ring A root src target .writer (max structural stable)
            terminal ∧ st = terminal.time := by
  induction h with
  | start =>
    refine ⟨List.mem_cons_self .., ?_⟩
    intro target st hm
    left
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    exact hm.1
  | @next source' previous' cuts' h target' terminal hp hc ih =>
    refine ⟨List.mem_cons_self .., ?_⟩
    intro target st hm
    rcases List.mem_cons.mp hm with hm | hm
    · right
      simp only [Prod.mk.injEq] at hm
      obtain ⟨hm1, hm2⟩ := hm
      subst hm1
      exact ⟨source', previous', terminal, List.mem_cons_of_mem _ ih.1, hp, hc, hm2⟩
    · rcases ih.2 target st hm with h1 | ⟨src, stable, term, h2, h3, h4, h5⟩
      · exact Or.inl h1
      · exact Or.inr ⟨src, stable, term, List.mem_cons_of_mem _ h2, h3, h4, h5⟩

/-- A next completion of the stepped audit with terminal no later than the old clock is one of the
old audit.  Consumer: `fiveCompletionsFoldBack`. -/
theorem nextCompletionBack (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (after : Nat) (tm : DigitTerminal c n)
    (h : DigitNextCompletion ring (digitAuditStep ring S A e) root source target lane after tm)
    (ht : tm.time ≤ A.clock) :
    DigitNextCompletion ring A root source target lane after tm :=
  ⟨completionBack ring S A e root source target lane 0 tm h.1 ht, h.2.1, fun other ho hlt =>
    h.2.2 other (L3.FiveTransfer.completionStep ring S A e root source target lane 0 other ho) hlt⟩

/-- Five completions of the stepped audit ending no later than the old clock are five completions
of the old audit.  Consumer: `fiveCompletionsFoldBack`. -/
theorem fiveCompletionsBack (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (after : Nat) (last : DigitTerminal c n)
    (h : DigitFiveCompletions ring (digitAuditStep ring S A e) root source target lane after last)
    (ht : last.time ≤ A.clock) :
    DigitFiveCompletions ring A root source target lane after last := by
  obtain ⟨t1, t2, t3, t4, h1, h2, h3, h4, h5⟩ := h
  have a2 := h2.2.1
  have a3 := h3.2.1
  have a4 := h4.2.1
  have a5 := h5.2.1
  exact ⟨t1, t2, t3, t4, nextCompletionBack S A e root source target lane _ t1 h1 (by omega),
    nextCompletionBack S A e root source target lane _ t2 h2 (by omega),
    nextCompletionBack S A e root source target lane _ t3 h3 (by omega),
    nextCompletionBack S A e root source target lane _ t4 h4 (by omega),
    nextCompletionBack S A e root source target lane _ last h5 ht⟩

/-- **The five completions of the end of a run hold at any earlier clock no earlier than the fifth
terminal.**

Consumer: `writersCurrentOfCore`. -/
theorem fiveCompletionsFoldBack (ref : WidthDigitReference ring) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (after : Nat)
    (T : DigitTerminal (compileAdvice (ceilLogTwo n)) n) :
    ∀ (word : List (Fin n)) (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      DigitFiveCompletions ring (word.foldl (widthDigitAuditNext ref) y).2 root source target
        lane after T →
      T.time ≤ y.2.clock →
      DigitFiveCompletions ring y.2 root source target lane after T := by
  intro word
  induction word with
  | nil => intro y h _; exact h
  | cons e rest ih =>
    intro y h ht
    have h1 := ih (widthDigitAuditNext ref y e) h (by show T.time ≤ y.2.clock + 1; omega)
    exact fiveCompletionsBack (piD (ref.phys y.1)) y.2 e root source target lane after T h1 ht

end Chain

section Assembly

variable {n : Nat} {ring : DirectedRing n}

/-- **`DigitWritersCurrent` at the writer comparison cut, from the entry content.**  On a clean run
from a start of a boundary reference ending at `(z, audit)` with the writer value receipts, there
are a structural cut and the chain's cut list for which the value chain holds and every complete
pair is writer-current at the clock.

Consumer: the physical value step and the assembly of `DigitValuesCorrect`
(`WidthWriterComparisonCertificate`, second conjunct). -/
theorem writersCurrentOfCore (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hcore : WriterEntryCore ref.toWidthDigitReference)
    (start : ref.State) (word : List (Fin n)) (root : Fin n) (z : ref.State)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (retired restart : Nat)
    (hst : ref.start start)
    (hfold : word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start))) = (z, audit))
    (hW : WFixedRoot ring root (piW (ref.phys z)))
    (hrec : WidthWriterValueReceipts ring root audit retired restart) :
    ∃ (structural first baseCut last : Nat) (cuts : List (Nat × Nat)),
      DigitValueChain ring root audit structural first baseCut last restart cuts ∧
      DigitWritersCurrent ring root audit (piD (ref.phys z)) audit.current structural audit.clock
        cuts := by
  obtain ⟨first, stop, baseCut, structural, last, cuts, hseg, -, -, -, hchain, hcover⟩ := hrec
  refine ⟨structural, first, baseCut, last, cuts, hchain, ?_⟩
  intro source target hpair
  -- the clean start and the root
  obtain ⟨root0, hs, hL⟩ := widthCleanBoundaryRoot ref start hst
  have hx1 : z = word.foldl ref.next start := by
    have := widthBoundaryDigitBoundaryAuditFirst ref start
      (digitAuditInitial (piD (ref.phys start))) word
    rw [hfold] at this
    exact this
  rw [hx1] at hW
  have hr : root = root0 :=
    (widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root0 start hs word).2.1 root hW.1
  subst hr
  have hstart : audit.start = piD (ref.phys start) := by
    have := L3.WriterReceipts.widthAuditStartFold ref.toWidthDigitReference word
      (start, digitAuditInitial (piD (ref.phys start)))
    rw [hfold] at this
    exact this
  have hclk : audit.clock = word.length := by
    have := clockFold ref.toWidthDigitReference word
      (start, digitAuditInitial (piD (ref.phys start)))
    rw [hfold] at this
    have h1 : audit.clock = 0 + word.length := this
    omega
  -- the predecessor cut of the target
  obtain ⟨hs0, hsn, hsb⟩ := hpair.1.1.1
  have hlt : source < target := by
    have hd := hpair.1.1.2.1
    have := hpair.2.1
    omega
  obtain ⟨hfd, hfmin⟩ := hseg.1
  have hfs : first ≤ source := by
    by_cases h : first ≤ source
    · exact h
    · have := hfmin source hs0 (by omega)
      rw [this] at hsb
      exact absurd hsb (by simp)
  obtain ⟨stable', hmem'⟩ := hcover target hpair.2.2
  rcases (chainPath hchain).2 target stable' hmem' with hfirst | ⟨src, stable, terminal, hsrc, hp, hc, hst'⟩
  · omega
  · have hsrcEq : src = source := by
      have h1 := hp.2.1
      have h2 := hpair.2.1
      omega
    subst hsrcEq
    refine ⟨stable, hsrc, ?_⟩
    -- the fifth completion and its terminal
    obtain ⟨t1, t2, t3, t4, -, -, -, h1, h2, h3, h4, h5, -⟩ := hc
    have hT5 : DigitFiveCompletions ring audit root src target DigitLane.writer
        (max structural stable) terminal := ⟨t1, t2, t3, t4, h1, h2, h3, h4, h5⟩
    have htg := hpair.2.1
    have hTle : terminal.time ≤ audit.clock := completionTimeLe ring audit h5.1
    have hpair' : DigitCompletePair ring root (piD (ref.phys start)) src
        (src + digitSpan (compileAdvice (ceilLogTwo n))) := by
      rw [← hstart, ← htg]; exact hpair
    rw [htg] at hT5
    obtain ⟨hsrc2, hend, -⟩ := pairLayoutStart ref hn root start hL src hpair'
    have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
    let init : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n :=
      (start, digitAuditInitial (piD (ref.phys start)))
    let y0 := (word.take terminal.time).foldl (widthDigitAuditNext ref.toWidthDigitReference) init
    have hy0 : (word.drop terminal.time).foldl (widthDigitAuditNext ref.toWidthDigitReference) y0 =
        (z, audit) := by
      show (word.drop terminal.time).foldl _ ((word.take terminal.time).foldl _ init) = _
      rw [← List.foldl_append, List.take_append_drop]
      exact hfold
    have hclk0 : y0.2.clock = terminal.time := by
      show ((word.take terminal.time).foldl _ init).2.clock = terminal.time
      rw [clockFold, List.length_take]
      show 0 + min terminal.time word.length = terminal.time
      omega
    have hT0 : DigitFiveCompletions ring y0.2 root src
        (src + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.writer (max structural stable)
        terminal := by
      have hT5' : DigitFiveCompletions ring
          ((word.drop terminal.time).foldl (widthDigitAuditNext ref.toWidthDigitReference) y0).2
          root src (src + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.writer
          (max structural stable) terminal := by
        rw [hy0]; exact hT5
      exact fiveCompletionsFoldBack ref.toWidthDigitReference root src _ DigitLane.writer _ terminal
        (word.drop terminal.time) y0 hT5' (Nat.le_of_eq hclk0.symm)
    have hpw0 := writerEntryOfCore ref hn hcore root start (word.take terminal.time) src
      (max structural stable) terminal hst hs hpair' hT0 hclk0.symm
    have hpw := writerPairWinRun ref.toWidthDigitReference ref.singletonFixed hn root src
      (digitSpan (compileAdvice (ceilLogTwo n))) hR hsrc2 hend (max structural stable)
      (word.drop terminal.time) y0 hpw0
    rw [hy0] at hpw
    have hcur := writerPairCurrentOfWin ref.toWidthDigitReference root src (max structural stable)
      (z, audit) hpw
    rw [htg]
    exact hcur

end Assembly

end L3.WriterCurrent

#print axioms L3.WriterCurrent.chainPath
#print axioms L3.WriterCurrent.writersCurrentOfCore
