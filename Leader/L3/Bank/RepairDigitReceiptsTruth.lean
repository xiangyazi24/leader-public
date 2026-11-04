import Leader.L3.Bank.RepairDigitBlockEntry
import Leader.L3.Bank.RepairDigitValueWaveClose
import Leader.L3.Bank.RepairDigitLedger

/-!
R10c, receipt truth and the zero-cover rebase.

This module proves only the physical/recorded facts named below. In particular,
it does NOT prove ReceiptsClose or StructuralCut -> EntryCut 0.
A ranked two-lane scheduling requirement is stated as a definition, not
as a theorem or a new assumption about every reachable run.
-/

namespace L3.BlockEntry

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.ValueWaveClose

/-- Enlarging the cutoff of an already recorded pair of base covers to the
current audit clock preserves both rooted lineages and their proposals.
Consumer: bankRepairDigitStructuralZeroRun. -/
theorem bankRepairDigitTwoBaseCoversCutMono
    {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (audit : DigitAudit c n) (boundary retired cut : Nat)
    (h : DigitTwoBaseCovers ring root audit boundary retired cut) :
    DigitTwoBaseCovers ring root audit boundary retired audit.clock := by
  rcases h with ⟨hext, hret, hclock, hrest⟩
  refine ⟨hext, Nat.le_trans hret hclock, Nat.le_refl _, ?_⟩
  rcases hrest with hempty |
    ⟨bornFirst, bornSecond, lastFirst, lastSecond,
      chainFirst, chainSecond,
      hbornFirst, hbornSecond, hlineFirst, hlineSecond,
      hlastFirst, hlastSecond, hproposals⟩
  · exact Or.inl hempty
  · apply Or.inr
    refine ⟨bornFirst, bornSecond, lastFirst, lastSecond,
      chainFirst, chainSecond, hbornFirst, hbornSecond,
      hlineFirst, hlineSecond,
      Nat.le_trans hlastFirst hclock,
      Nat.le_trans hlastSecond hclock, ?_⟩
    intro site hwritable
    obtain ⟨first, second, hfirst, hsecond, htime⟩ :=
      hproposals site hwritable
    refine ⟨first, second, ?_, ?_, htime⟩
    · exact bankRepairDigitZeroCoverMono ring root audit audit
        (fun _ hf => hf) boundary retired cut audit.clock hclock
        chainFirst chainFirst (fun _ hf => hf) site first hfirst
    · exact bankRepairDigitZeroCoverMono ring root audit audit
        (fun _ hf => hf) boundary retired cut audit.clock hclock
        chainSecond chainSecond (fun _ hf => hf) site second hsecond

/-- The actual structural witness has a zero-run at its CURRENT audit with
the identity continuation word. Its original word is the RFold replay;
the post-cover continuation is [].
Consumer: the entry bridge before waveAfterEntry. -/
theorem bankRepairDigitStructuralZeroRun
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (h : BankRepairDigitStructuralCut ring hbank z) :
    ∃ (root : Fin n)
      (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
      (structural : Nat),
      ZeroRun ring hbank root (z, audit) ∧
      DigitFirstCut (DigitStructuralAt ring root audit) structural := by
  obtain ⟨start, word, root, audit, retired, zeroCut, structural,
    hR, hfold, hW, hD, hcover, hstrict⟩ := h
  refine ⟨root, audit, structural, ?_, hstrict⟩
  refine ⟨start, word, [], (z, audit), retired,
    hR, hfold, hW, hD, ?_, rfl⟩
  exact bankRepairDigitTwoBaseCoversCutMono
    ring root audit 0 retired zeroCut hcover

/-- The structural cut is, with the same witness and unchanged first-zero
projection, a valid first-zero cut. This does NOT provide a physical pair pin.
Consumer: ValueWaveClose.valueCutOfFirstZero. -/
theorem bankRepairDigitStructuralFirstZeroCut
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (h : BankRepairDigitStructuralCut ring hbank z) :
    BankRepairDigitFirstZeroCut ring hbank z := by
  obtain ⟨start, word, root, audit, retired, zeroCut, structural,
    hR, hfold, hW, hD, hcover, hstrict⟩ := h
  exact ⟨start, word, root, audit, retired,
    hR, hfold, hW, hD,
    bankRepairDigitTwoBaseCoversCutMono
      ring root audit 0 retired zeroCut hcover⟩

/-- At the current structural state, the WEAK value-block entrance P 0 is
available. It is not the stronger EntryCut 0, which still requires
PairsFrom 0. Consumer: the distinction in the R10c wave interface. -/
theorem bankRepairDigitStructuralValueBlockStart
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (h : BankRepairDigitStructuralCut ring hbank z) :
    ValueBlockCut ring hbank 0 z := by
  exact valueCutOfFirstZero ring hbank z
    (bankRepairDigitStructuralFirstZeroCut ring hbank z h)

/-- Five NEXT-completion receipts are strictly after their common cut.
This is not derivable from an unordered five-chain FwdChain witness alone.
Consumer: the chronological dependency of DigitValueChain.next. -/
theorem bankRepairDigitFiveCohortAfter
    {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (audit : DigitAudit c n)
    (root : Fin n) (source target : Nat)
    (lane : DigitLane) (after : Nat)
    (terminal : DigitTerminal c n)
    (h : DigitFiveCohortCompletions ring audit root source target
      lane after terminal) :
    after < terminal.time := by
  obtain ⟨first, second, third, fourth, anchor, anchorTail,
    firstRank, hfirst, hsecond, hthird, hfourth, hlast,
    hanchor, hanchorBefore, hrankPositive, hserial⟩ := h
  have ha : after < first.time := hfirst.2.1
  have hb : first.time < second.time := hsecond.2.1
  have hc : second.time < third.time := hthird.2.1
  have hd : third.time < fourth.time := hfourth.2.1
  have he : fourth.time < terminal.time := hlast.2.1
  omega

/-- The first value cut is retained in the receipt list after any number of
actual chronological successor-link extensions.
Consumer: the first-block coverage field of BankRepairDigitValueReceipts. -/
theorem bankRepairDigitValueChainRetainsFirst
    {c : Compiled} {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (audit : DigitAudit c n)
    (structural first baseCut last previous : Nat)
    (cuts : List (Nat × Nat))
    (h : DigitValueChain ring root audit structural first baseCut
      last previous cuts) :
    (first, baseCut) ∈ cuts := by
  induction h with
  | start =>
      simp
  | next h target terminal hp hc ih =>
      exact List.mem_cons_of_mem _ ih

/-- The stronger receipt information needed by the paper consumer:
one strict BOTH-lane structural cut and actual serial, ranked writer
completions, linked by recorded times rather than independently selected
unordered receipts. No existence or reachability claim is made here.
Consumer: the missing ReceiptsClose assembly, not waveAfterEntry directly. -/
def BankRepairDigitRankedBothLaneSchedule
    {n : Nat} (ring : DirectedRing n)
    (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (structural baseCut : Nat) : Prop :=
  DigitFirstCut (DigitStructuralAt ring root audit) structural ∧
  ∀ first : Nat, DigitFirstDelimiter ring root audit.start first →
    ∃ (times : Nat → Nat)
      (terminals : Nat →
        DigitTerminal (compileAdvice (ceilLogTwo n)) n),
      times 0 = baseCut ∧
      ∀ j : Nat,
        2 ≤ first + j * valueSpan n →
        first + j * valueSpan n + 2 * valueSpan n < n →
        DigitFiveCohortCompletions ring audit root
          (first + j * valueSpan n)
          (first + (j + 1) * valueSpan n)
          .writer (max structural (times j)) (terminals j) ∧
        times (j + 1) = (terminals j).time

end L3.BlockEntry

#print axioms L3.BlockEntry.bankRepairDigitTwoBaseCoversCutMono
#print axioms L3.BlockEntry.bankRepairDigitStructuralZeroRun
#print axioms L3.BlockEntry.bankRepairDigitStructuralFirstZeroCut
#print axioms L3.BlockEntry.bankRepairDigitStructuralValueBlockStart
#print axioms L3.BlockEntry.bankRepairDigitFiveCohortAfter
#print axioms L3.BlockEntry.bankRepairDigitValueChainRetainsFirst
