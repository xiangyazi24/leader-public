import Leader.L3.Bank.RepairDigitBlockCuts

/-!
# T34: the block cuts of the value wave and the value-wave clock

**Layout.** `R = valueSpan n = digitSpan c = 2^t - 1` (the delimiter spacing), `K = n / R`
(`valueBlocksFit : K * R ≤ n`). Block `j` of a run with leader `root` is the complete pair
`(src, src + R)`, with `src = first + j * R` and `first` the first delimiter of the audit start
(`DigitFirstDelimiter`, unique by `firstDelimUnique`), on the writer lane; this is the layout of
`CohortLayout` (delimiters at `src`, `src + R`, `src + 2R`) and of `FwdChain … src (src + R)`.
A block whose pair is not interior (`¬ (2 ≤ src ∧ src + 2R < n)`) is empty.

**Cuts.**
* `ZeroRun root x`: the coupled pair `x` (BANK × audit) continues, by a coupled word, a state of
  the first-zero cut at the same leader `root` (all fields of `BankRepairDigitFirstZeroCut`).
* `BlockReceipt root A j`: the five chained writer completions of block `j` after some time are
  recorded in `A` (vacuous if block `j` is empty).
* `ValueBlockCut j z` (the `P j` of `valueWaveOfCoupledBlocks`): `z` with its audit continues a
  first-zero cut and the audit carries the receipts of blocks `< j`.

**Proved.** `h0` (`valueCutOfFirstZero`), the block finish `hB` (inside `valueBlockStage`: the
run-carrying block `BlockCuts.runCoupledBlock` sees `FwdChain` and the run on the same coupled
state), every block stage from the entrance lift (`valueBlockStage`), and the assembly
(`bankRepairDigitValueWaveClockOfEntry`).

**The two missing facts, as named hypotheses** (both are structured statements about the run):

* `BlockEntryLift ring hbank`: for every block `j`, every leader `root`, first delimiter
  `first` of the audit start, and every coupled pair `(z, audit)` continuing a first-zero cut at
  `root` whose audit carries the receipts of blocks `< j`, if block `j` is interior then there
  are a cycle ghost `g` (for the lane of block `j`) and an anchor time `after` with
  `WinInvD … (InheritedOk writer) (z, audit) g`, `UseReach … ((z, audit), g)`,
  `after ≤ audit.clock` and `AnchorIn … after audit`, on the **same** BANK state and the
  **same** audit. (This is `pinCoupledBlockStart`'s `hStart` with `UseReach` at any chosen
  ghost in place of `PinReach` at `lam = 0`; the cycle numbering is reset by `useReachReset` and
  `winInvDReset`.)
* `ReceiptsClose ring hbank`: every coupled pair `(z, audit)` continuing a first-zero cut at
  `root` whose audit carries the receipts of all `K` blocks is a `BankRepairDigitValuesStableCut`
  state. (The conversion of five-completion receipts into `BankRepairDigitValueReceipts`: first
  segment, base value cut, first structural cut, `DigitValueChain` with
  `DigitFiveCohortCompletions`, which needs T30's open item 4: `DigitAnchor` and the serial tail
  ranks `DigitSerialTerminalRanks`, and coverage.)

`BlockEntryLift` is the clause that does not hold at a generic block cut: see the T34 notes. The
ghost clauses hold at the second closing letter after any chain start
(`BlockCuts.pinStartOfTwoCloses`), not at the state where the previous block finished.
-/

namespace L3.ValueWaveClose

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.RenewalReferenceClock
open L3.CohortStages
open L3.CohortTransfer
open L3.CohortLedger
open L3.FiveTransfer
open L3.Projection
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow
open L3.CohortClose
open L3.CohortOrder
open L3.BlockStart
open L3.FiveClose
open L3.HClose
open L3.CloseReceipt
open L3.FiveReach
open L3.ValueCorr
open L3.ValueLedger
open L3.SitePin
open L3.UseRows
open L3.UseCells
open L3.UseTrack
open L3.BlockCuts

/-! ### Layout -/

/-- The block length of the value wave: the delimiter spacing `2^t - 1`. -/
def valueSpan (n : Nat) : Nat := digitSpan (compileAdvice (ceilLogTwo n))

/-- The number of block stages of the value wave. -/
def valueBlocks (n : Nat) : Nat := n / valueSpan n

/-- `K R ≤ n`. Consumer: `bankRepairDigitValueWaveClockOfEntry` (`valueWaveOfCoupledBlocks`'s
`hK`). -/
theorem valueBlocksFit (n : Nat) : valueBlocks n * valueSpan n ≤ n :=
  Nat.div_mul_le_self n _

/-- `2 ≤ R` on the BANK band. Consumer: `valueBlockStage` (the section hypothesis `hR`). -/
theorem valueSpanTwo {n : Nat} (hn : 5 ≤ n) : 2 ≤ valueSpan n := by
  have ht := compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have h4 : 4 ≤ 2 ^ (compileAdvice (ceilLogTwo n)).t :=
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (compileAdvice (ceilLogTwo n)).t := Nat.pow_le_pow_right (by decide) ht
  unfold valueSpan digitSpan
  omega

/-- The first delimiter is unique. Consumer: `valueBlockStage` (the block finish names the
receipt of the same block). -/
theorem firstDelimUnique {n : Nat} {c : Compiled} (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) {a b : Nat} (ha : DigitFirstDelimiter ring root S a)
    (hb : DigitFirstDelimiter ring root S b) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exfalso
    have h1 := hb.2 a ha.1.1 h
    rw [ha.1.2.2] at h1
    cases h1
  · exact h
  · exfalso
    have h1 := ha.2 b hb.1.1 h
    rw [hb.1.2.2] at h1
    cases h1

/-! ### Cuts -/

section Cuts

variable {n : Nat} (ring : DirectedRing n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-- The coupled pair `x` continues, by a coupled word, a state of the first-zero cut at the
leader `root`. -/
def ZeroRun (root : Fin n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ (start : BankReferenceState ring hbank) (word0 word : List (Fin n))
    (y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (retired : Nat),
    BankRepairRFoldEstablished ring hbank start ∧
    word0.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = y ∧
    WFixedRoot ring root (piW y.1.val.1) ∧
    DigitAt ring y.2 y.2.clock (piD y.1.val.1) y.2.current ∧
    DigitTwoBaseCovers ring root y.2 0 retired y.2.clock ∧
    word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) y = x

/-- The receipt of block `j`: if block `j` (from the first delimiter of the audit start) is an
interior pair, five chained writer completions of it after some time are recorded. -/
def BlockReceipt (root : Fin n) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) (j : Nat) :
    Prop :=
  ∀ first : Nat, DigitFirstDelimiter ring root A.start first →
    2 ≤ first + j * valueSpan n → first + j * valueSpan n + 2 * valueSpan n < n →
    ∃ after : Nat, FwdChain ring A root (first + j * valueSpan n)
      (first + j * valueSpan n + valueSpan n) DigitLane.writer 5 after

/-- **The block cut `P j`**: a first-zero continuation whose audit carries the receipts of the
blocks before `j`. Consumer: `bankRepairDigitValueWaveClockOfEntry`. -/
def ValueBlockCut (j : Nat) (z : BankReferenceState ring hbank) : Prop :=
  ∃ (root : Fin n) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
    ZeroRun ring hbank root (z, audit) ∧ ∀ i, i < j → BlockReceipt ring root audit i

/-- **Missing fact 1 (the entrance lift)**: at every block cut of an interior block, a cycle
ghost of that block's lane with the strengthened window invariant and `UseReach`, and an anchor
recorded at or before the clock, on the same BANK state and audit. -/
def BlockEntryLift : Prop :=
  ∀ (j : Nat) (root : Fin n) (first : Nat) (z : BankReferenceState ring hbank)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
    ZeroRun ring hbank root (z, audit) → DigitFirstDelimiter ring root audit.start first →
    (∀ i, i < j → BlockReceipt ring root audit i) →
    2 ≤ first + j * valueSpan n → first + j * valueSpan n + 2 * valueSpan n < n →
    ∃ (g : (Nat → Nat) × Nat) (after : Nat),
      WinInvD ring hbank root DigitLane.writer (first + j * valueSpan n) (valueSpan n)
        (InheritedOk DigitLane.writer) (z, audit) g ∧
      UseReach ring hbank root DigitLane.writer (first + j * valueSpan n) (valueSpan n)
        ((z, audit), g) ∧
      after ≤ audit.clock ∧
      AnchorIn ring root DigitLane.writer (first + j * valueSpan n) (valueSpan n) after audit

/-- **Missing fact 2 (the receipt conversion)**: the receipts of all blocks on a first-zero
continuation give the value cut. -/
def ReceiptsClose : Prop :=
  ∀ (root : Fin n) (z : BankReferenceState ring hbank)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
    ZeroRun ring hbank root (z, audit) →
    (∀ i, i < valueBlocks n → BlockReceipt ring root audit i) →
    BankRepairDigitValuesStableCut ring hbank z

/-- First-zero continuations are carried by every coupled letter. Consumer: `valueBlockStage`. -/
theorem zeroRunStep (root : Fin n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : ZeroRun ring hbank root x) (e : Fin n) :
    ZeroRun ring hbank root (bankRepairDigitBoundaryAuditNext ring hbank x e) := by
  obtain ⟨start, word0, word, y, retired, hR, hy, hW, hD, hC, hx⟩ := h
  refine ⟨start, word0, word ++ [e], y, retired, hR, hy, hW, hD, hC, ?_⟩
  rw [List.foldl_append, hx]
  rfl

/-- Receipts persist along audit steps. Consumer: `valueBlockStage`. -/
theorem receiptStep (root : Fin n) (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n) (j : Nat)
    (h : BlockReceipt ring root A j) : BlockReceipt ring root (digitAuditStep ring S A e) j := by
  intro first hf h1 h2
  obtain ⟨after, hc⟩ := h first hf h1 h2
  exact ⟨after, fwdChainStep S A e 5 after hc⟩

/-- **`h0`**: the first-zero cut lies in the block cut `P 0`. Consumer:
`bankRepairDigitValueWaveClockOfEntry`. -/
theorem valueCutOfFirstZero (z : BankReferenceState ring hbank)
    (h : BankRepairDigitFirstZeroCut ring hbank z) : ValueBlockCut ring hbank 0 z := by
  obtain ⟨start, word, root, audit, retired, hR, hfold, hW, hD, hC⟩ := h
  exact ⟨root, audit, ⟨start, word, [], (z, audit), retired, hR, hfold, hW, hD, hC, rfl⟩,
    fun i hi => absurd hi (Nat.not_lt_zero i)⟩

/-- The pieces of a block cut: by leader, and by the first delimiter of the audit start (or its
absence). -/
def BlockPiece (j : Nat) (root : Fin n) : Option Nat → BankReferenceState ring hbank → Prop
  | none, z => ∃ audit : DigitAudit (compileAdvice (ceilLogTwo n)) n,
      ZeroRun ring hbank root (z, audit) ∧
      (∀ first, ¬ DigitFirstDelimiter ring root audit.start first) ∧
      ∀ i, i < j → BlockReceipt ring root audit i
  | some first, z => ∃ audit : DigitAudit (compileAdvice (ceilLogTwo n)) n,
      ZeroRun ring hbank root (z, audit) ∧ DigitFirstDelimiter ring root audit.start first ∧
      ∀ i, i < j → BlockReceipt ring root audit i

/-- **The block stage `P j → P (j + 1)`** from the entrance lift, at charge `200 n R`: empty
blocks are inclusions; an interior block is `runCoupledBlock` on the window chain of its pair,
split by leader, first delimiter and anchor time, whose finish (`hB`) records the receipt of
block `j` on the run. Consumer: `bankRepairDigitValueWaveClockOfEntry`. -/
theorem valueBlockStage (hn : 5 ≤ n) (hlift : BlockEntryLift ring hbank) (j : Nat) :
    CoupledBlock ring hbank (ValueBlockCut ring hbank j) (ValueBlockCut ring hbank (j + 1))
      (200 * n * valueSpan n) := by
  have hR := valueSpanTwo hn
  refine coupledBlockSigma ring hbank _ _ _
    (fun p : Fin n × Option Nat => BlockPiece ring hbank j p.1 p.2) ?_ ?_
  · rintro z ⟨root, audit, hrun, hrec⟩
    rcases Classical.em (∃ first, DigitFirstDelimiter ring root audit.start first) with
      ⟨first, hf⟩ | hno
    · exact ⟨(root, some first), audit, hrun, hf, hrec⟩
    · exact ⟨(root, none), audit, hrun, fun f hf => hno ⟨f, hf⟩, hrec⟩
  rintro ⟨root, o⟩
  cases o with
  | none =>
      refine coupledBlockOfImp ring hbank _ _ _ ?_
      rintro z ⟨audit, hrun, hno, -⟩
      exact ⟨root, audit, hrun, fun i _ first hf => absurd hf (hno first)⟩
  | some first =>
      rcases Classical.em (2 ≤ first + j * valueSpan n ∧
          first + j * valueSpan n + 2 * valueSpan n < n) with ⟨hsrc, hend⟩ | hg
      · refine coupledBlockSigma ring hbank _ _ _
          (fun after z => ∃ (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
            (g : (Nat → Nat) × Nat),
            ZeroRun ring hbank root (z, audit) ∧ DigitFirstDelimiter ring root audit.start first ∧
            (∀ i, i < j → BlockReceipt ring root audit i) ∧
            WinInvD ring hbank root DigitLane.writer (first + j * valueSpan n) (valueSpan n)
              (InheritedOk DigitLane.writer) (z, audit) g ∧
            UseReach ring hbank root DigitLane.writer (first + j * valueSpan n) (valueSpan n)
              ((z, audit), g) ∧
            after ≤ audit.clock ∧
            AnchorIn ring root DigitLane.writer (first + j * valueSpan n) (valueSpan n) after
              audit) ?_ ?_
        · rintro z ⟨audit, hrun, hf, hrec⟩
          obtain ⟨g, after, hw, hu, haft, hanc⟩ := hlift j root first z audit hrun hf hrec hsrc hend
          exact ⟨after, audit, g, hrun, hf, hrec, hw, hu, haft, hanc⟩
        intro after
        refine runCoupledBlock ring hn hbank root DigitLane.writer (first + j * valueSpan n)
          (valueSpan n) hR hsrc (by omega) (InheritedOk DigitLane.writer) after _ _
          (fun w => ZeroRun ring hbank root w.1 ∧ DigitFirstDelimiter ring root w.1.2.start first ∧
            ∀ i, i < j → BlockReceipt ring root w.1.2 i) ?_ ?_ ?_
        · intro w e _ hc
          exact ⟨zeroRunStep ring hbank root w.1 hc.1 e, hc.2.1,
            fun i hi => receiptStep ring root _ w.1.2 e i (hc.2.2 i hi)⟩
        · rintro z ⟨audit, g, hrun, hf, hrec, hw, hu, haft, hanc⟩
          exact ⟨((z, audit), (g.1, 0)), rfl,
            winInvDReset ring hbank root DigitLane.writer _ _ _ (z, audit) g hw 0,
            useReachReset ring hbank root DigitLane.writer _ _ (z, audit) g hu, rfl, haft, hanc,
            hrun, hf, hrec⟩
        · intro w hfw hc
          refine ⟨root, w.1.2, hc.1, fun i hi => ?_⟩
          rcases Nat.lt_or_ge i j with hij | hij
          · exact hc.2.2 i hij
          · have hie : i = j := by omega
            subst hie
            intro first' hf' _ _
            have he := firstDelimUnique ring root _ hc.2.1 hf'
            subst he
            exact ⟨after, hfw⟩
      · refine coupledBlockOfImp ring hbank _ _ _ ?_
        rintro z ⟨audit, hrun, hf, hrec⟩
        refine ⟨root, audit, hrun, fun i hi => ?_⟩
        rcases Nat.lt_or_ge i j with hij | hij
        · exact hrec i hij
        · have hie : i = j := by omega
          subst hie
          intro first' hf' h1 h2
          have he := firstDelimUnique ring root _ hf hf'
          subst he
          exact absurd ⟨h1, h2⟩ hg

/-- **The value-wave clock from the two missing facts** (`BlockEntryLift`, `ReceiptsClose`),
with no other premise beyond the BANK band and `5 ≤ n`: `valueWaveOfCoupledBlocks` with the
block cuts `ValueBlockCut`, `K = n / R` blocks of length `R = 2^t - 1`. Consumer: the third
conjunct of `BankRepairDigitFourMicroClocks` (`BankRepairDigitValueWaveClock`). -/
theorem bankRepairDigitValueWaveClockOfEntry (hn : 5 ≤ n) (hlift : BlockEntryLift ring hbank)
    (hclose : ReceiptsClose ring hbank) : BankRepairDigitValueWaveClock ring hbank :=
  valueWaveOfCoupledBlocks ring hbank (ValueBlockCut ring hbank) (valueBlocks n) (valueSpan n)
    (valueCutOfFirstZero ring hbank) (valueBlockStage ring hbank hn hlift)
    (fun z ⟨root, audit, hrun, hrec⟩ => hclose root z audit hrun hrec) (valueBlocksFit n)

end Cuts

end L3.ValueWaveClose

#print axioms L3.ValueWaveClose.valueBlocksFit
#print axioms L3.ValueWaveClose.valueSpanTwo
#print axioms L3.ValueWaveClose.firstDelimUnique
#print axioms L3.ValueWaveClose.valueCutOfFirstZero
#print axioms L3.ValueWaveClose.valueBlockStage
#print axioms L3.ValueWaveClose.bankRepairDigitValueWaveClockOfEntry
