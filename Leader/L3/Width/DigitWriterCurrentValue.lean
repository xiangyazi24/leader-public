import Leader.L3.Width.DigitComparisonValuesFold

/-!
# Writer currentness: the value step from the ledger to the block value

A genuine writer completion `T` of a complete pair `(source, target)` carries a ledger whose uses
are a carry chain (`writerTerminalChain`).  Its stored string is the successor of its sampled string
modulo `topA ^ digitSpan` (`carryChain_mod`).  This module states what turns that into a statement
about the *physical* digits, using only what the completion records:

* `ledgerIn_of_completion`: the string consumed by the ledger is, cell by cell, the digit that the
  source cell held in the frame that sampled it, and that frame is later than the completion's
  `cut`;
* `blockValue_succ_of_cells`: if the physical source cells hold the consumed string and the
  physical target cells hold the string the ledger asks to store, then
  `valueBlockID target = (valueBlockID source + 1) % topA ^ digitSpan`.

The two cell hypotheses of `blockValue_succ_of_cells` are exactly the facts that are not recorded:
that no later frame changed the source cell after the sample, and that the target cell was clean
when written and not overwritten since.  They are the stability (c) of the task; see the notes.

Consumer: the assembly of `DigitValuesCorrect` at the writer comparison cut.
-/

namespace L3.WriterCurrent

open L3.AcceptedReceipts

set_option autoImplicit false

section Value

variable {c : Compiled} {n : Nat}

/-- **The string a completion's ledger consumed is the string its samples read.**  For a
completion of a complete pair after `cut`, the ledger is genuine of length `digitSpan`, and for each
offset `j` there is a frame later than `cut` on the edge leaving the source cell `source + j` whose
old state held, at that cell, the digit the ledger consumed at use `j`.

Consumer: `writerBlockValue`. -/
theorem ledgerIn_of_completion (ring : DirectedRing n) (A : DigitAudit c n) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (cut : Nat) (terminal : DigitTerminal c n)
    (h : DigitCompletion ring A root source target lane cut terminal) :
    ∃ L : DigitCarryGhost c n, terminal.ledger = some L ∧ L.inherited = none ∧
      L.uses.length = digitSpan c ∧
      ∀ j : Nat, j < digitSpan c →
        ∃ f ∈ A.frames, f.edge = digitSite ring root (source + j) ∧ cut < f.time ∧
          ledgerIn L.uses j = ((f.old (digitSite ring root (source + j))).top.d).val := by
  obtain ⟨-, -, -, -, -, -, pos, ledger, samples, exports, uses, h1, h2, h3, hj, -, -⟩ := h
  refine ⟨ledger, h1, h2, h3, fun j hjlt => ?_⟩
  obtain ⟨⟨f, hf, hft, hfe, -, hfv⟩, -, s3, s4, -, -, -, -, -, -, -, -, u1, -, -, u4, -, -, -, -⟩ :=
    hj ⟨j, hjlt⟩
  refine ⟨f, hf, by rw [hfe]; exact s3, by rw [hft]; exact s4, ?_⟩
  have e1 : ledgerIn ledger.uses j = ((uses ⟨j, hjlt⟩).value).val := by
    unfold ledgerIn
    rw [u1]
    rfl
  rw [e1, u4, hfv, hfe, s3]

/-- **The block value step, given the two cell facts.**  If the physical source cells hold the
string consumed by a carry chain of length `digitSpan` and the physical target cells hold the string
the chain asks to store, the target block is the successor of the source block modulo
`topA ^ digitSpan`.

Consumer: `writerBlockValue`; the cell hypotheses are the stability facts (c). -/
theorem blockValue_succ_of_cells {ring : DirectedRing n} {root : Fin n}
    (v : Fin n → Bool × Fin c.topA) (source target : Nat)
    {cc : Bool} {us : List (DigitUse c n)} (hch : CarryChain c.topA cc us)
    (hlen : us.length = digitSpan c)
    (hin : ∀ j, j < digitSpan c →
      (v (digitSite ring root (source + j))).2.val = ledgerIn us j)
    (hout : ∀ j, j < digitSpan c →
      (v (digitSite ring root (target + j))).2.val = ledgerOut us j) :
    valueBlockID ring root v target =
      (valueBlockID ring root v source + 1) % c.topA ^ digitSpan c := by
  have hm := carryChain_mod hch
  rw [hlen] at hm
  have e1 : valueBlockID ring root v source = digitsVal c.topA (ledgerIn us) (digitSpan c) :=
    digitsVal_congr c.topA (fun h => (v (digitSite ring root (source + h))).2.val) _ _ hin
  have e2 : valueBlockID ring root v target = digitsVal c.topA (ledgerOut us) (digitSpan c) :=
    digitsVal_congr c.topA (fun h => (v (digitSite ring root (target + h))).2.val) _ _ hout
  rw [e1, e2]
  exact hm

end Value

section Fold

open L3.WidthDigit

variable {n : Nat} {ring : DirectedRing n}

/-- **The value step of a writer completion on the audit fold of a drained start**, given the two
cell facts: if the physical source cells hold the string the completion's ledger consumed and the
physical target cells hold the string it asks to store, then the target block is the successor of
the source block.  The ledger is a carry chain because it is a recorded writer terminal of the
fold (`writerTerminalChain`).

Consumer: the assembly of `DigitValuesCorrect` at the writer comparison cut; the hypotheses `hin`
and `hout` are the stability facts (c) that the cut does not supply. -/
theorem writerBlockValue (ref : WidthDigitReference ring) (start : ref.State)
    (hd : ref.drained start) (word : List (Fin n)) (root : Fin n) (source target cut : Nat)
    (T : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hcomp : DigitCompletion ring
      (word.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2
      root source target DigitLane.writer cut T)
    (v : Fin n → Bool × Fin (compileAdvice (ceilLogTwo n)).topA)
    (hin : ∀ L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n, T.ledger = some L →
      ∀ j, j < digitSpan (compileAdvice (ceilLogTwo n)) →
        (v (digitSite ring root (source + j))).2.val = ledgerIn L.uses j)
    (hout : ∀ L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n, T.ledger = some L →
      ∀ j, j < digitSpan (compileAdvice (ceilLogTwo n)) →
        (v (digitSite ring root (target + j))).2.val = ledgerOut L.uses j) :
    AcceptedReceipts.valueBlockID ring root v target =
      (AcceptedReceipts.valueBlockID ring root v source + 1) %
        (compileAdvice (ceilLogTwo n)).topA ^ digitSpan (compileAdvice (ceilLogTwo n)) := by
  obtain ⟨L, hL, hinh, hlen, -⟩ := ledgerIn_of_completion ring _ root source target
    DigitLane.writer cut T hcomp
  have hinv := (auditCarryInv_fold ref word (start, digitAuditInitial (piD (ref.phys start))) hd
    (auditCarryInv_initial ring _)).2
  have hch := writerTerminalChain hinv T hcomp.2.1 hcomp.2.2.1 L hL hinh
  exact blockValue_succ_of_cells v source target hch hlen (hin L hL) (hout L hL)

end Fold

end L3.WriterCurrent

#print axioms L3.WriterCurrent.writerBlockValue
#print axioms L3.WriterCurrent.ledgerIn_of_completion
