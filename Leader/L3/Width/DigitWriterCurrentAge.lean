import Leader.L3.Width.DigitWriterCurrentBank
import Leader.L3.Width.DigitWriterCurrentLiveInv
import Leader.L3.Width.DigitWriterCurrentLedgers

/-!
# Writer currentness: the `LiveE` clause of the aged window is not a separate fact

`WinAge … after` has three clauses: `LiveE` (a live target carry has an empty input), the aged
tracked atoms, and the ledger clause (every ghost carry of the target window is non-inherited,
non-empty with aged uses).  This module shows that, on the audit fold of a drained start, the first
clause follows from the third:

* `liveE_of_ledgers`: from `LiveInv` (`WidthDigitWriterCurrentLiveInv`), the carry correspondence
  (`CarryAll`) and the ledger clause, `LiveE R` of the masked writer lane;
* `WriterAgeBody`: the aged-atoms clause and the ledger clause alone;
* `writerAgeCoreOfBody`: `WriterAgeBody ref ⇒ WriterAgeCore ref` for every `WidthDigitReference`.

Consumer: `writersCurrentOfAgeBank` (WidthDigitWriterCurrentBank) through `WriterAgeCore`.
-/

namespace L3.WriterCurrent

set_option autoImplicit false

open L3
open L3.WidthDigit
open L3.CohortDomination
open L3.CohortSites
open L3.GhostBridge
open L3.Correspondence
open L3.CurrentWin
open L3.CohortIdentity
open L3.RenewalReferenceClock

variable {n : Nat} {ring : DirectedRing n}

/-- **`LiveE` of the masked writer lane from the ledger clause.**

Consumer: `writerAgeCoreOfBody`. -/
theorem liveE_of_ledgers {c : Compiled} (root : Fin n) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (hcar : CarryAll S A.current)
    (hlive : LiveInv S A.current)
    (hled : ∀ q, R ≤ q → q < 2 * R → ∀ L : DigitCarryGhost c n,
      (laneCells ring root DigitLane.writer src A.current q).carry = some L → L.inherited = none) :
    LiveE R (cohortProj ring root DigitLane.writer src R S) := by
  intro q h1 h2 hl
  have hl' : (S (digitSite ring root (src + q))).top.wCarry.isW = true := by
    have := projLive ring root DigitLane.writer src R S q h1 h2
    rw [hl] at this
    exact this.symm
  have hc := hcar (digitSite ring root (src + q))
  obtain ⟨cc, hcc⟩ : ∃ cc, (S (digitSite ring root (src + q))).top.wCarry = .W cc := by
    cases hh : (S (digitSite ring root (src + q))).top.wCarry with
    | OFF => rw [hh] at hl'; simp [WCarry.isW] at hl'
    | W cc => exact ⟨cc, rfl⟩
  rw [hcc] at hc
  obtain ⟨L, hL, -⟩ := hc
  have hinh := hled q h1 h2 L hL
  have hE := hlive (digitSite ring root (src + q)) L hl' hL hinh
  rw [projIn ring root DigitLane.writer src R S q h1 h2]
  show bankRepairDigitInShOf (S (digitSite ring root (src + q))).top.wIn = .E
  rw [hE]
  rfl

/-- **The residual of the writer entry content once `LiveE` is removed**: the aged tracked atoms
and the ledger clause at the terminal state of the fifth next writer completion.

Consumer: `writerAgeCoreOfBody`. -/
def WriterAgeBody (ref : WidthDigitReference ring) : Prop :=
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
      L.inherited = none ∧
        ∀ use, use ∈ L.uses → UseAged ring root DigitLane.writer source
          (digitSpan (compileAdvice (ceilLogTwo n))) after
          (u.foldl (widthDigitAuditNext ref)
            (start, digitAuditInitial (piD (ref.phys start)))).2.clock use)

/-- **`WriterAgeCore` from `WriterAgeBody`** (any `WidthDigitReference`): the `LiveE` clause is
derived.

Consumer: `writersCurrentOfAgeBank` with `WriterAgeBody` in place of `WriterAgeCore`. -/
theorem writerAgeCoreOfBody (ref : WidthDigitReference ring)
    (hbody : WriterAgeBody ref) : WriterAgeCore ref := by
  intro root start u source after T hst hs hpair hT hTc
  obtain ⟨hA1, hA2⟩ := hbody root start u source after T hst hs hpair hT hTc
  have hd : ref.drained start := ref.startDrained start hst
  have hinv := (auditCarryInv_fold ref u (start, digitAuditInitial (piD (ref.phys start))) hd
    (auditCarryInv_initial ring _)).2
  have hli := liveInv_fold ref u (start, digitAuditInitial (piD (ref.phys start))) hd
    (liveInv_initial _)
  have hne := ledgerNE_fold ref u (start, digitAuditInitial (piD (ref.phys start)))
    (ledgerNE_initial _)
  refine ⟨liveE_of_ledgers root source _ _ _ hinv.1 hli
    (fun q h1 h2 L hL => (hA2 q h1 h2 L hL).1), hA1, ?_⟩
  intro q h1 h2 L hL
  obtain ⟨hi, hu⟩ := hA2 q h1 h2 L hL
  exact ⟨hi, hne _ L hL hi, hu⟩

open L3.WriterValueCuts in
/-- **`DigitWritersCurrent` at the BANK writer comparison cut from the aged atoms and the ledger
clause alone.**

Consumer: the BANK case of the writer comparison certificate (second conjunct). -/
theorem writersCurrentOfBodyBank (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hbody : WriterAgeBody (bankWidthDigitReference ring hn hbank))
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
  writersCurrentOfAgeBank hn hbank (writerAgeCoreOfBody _ hbody) start word root z audit
    retired restart hst hfold hW hrec

end L3.WriterCurrent

#print axioms L3.WriterCurrent.writersCurrentOfBodyBank
#print axioms L3.WriterCurrent.liveE_of_ledgers
#print axioms L3.WriterCurrent.writerAgeCoreOfBody
