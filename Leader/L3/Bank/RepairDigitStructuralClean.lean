import Leader.L3.Bank.RepairDigitPairsClean
import Leader.L3.Bank.RepairDigitReceiptsTruth

/-!
# R10c: the value wave restated at the clean structural cut

`WidthFirstZeroPairs` (the pins of every interior pair at the first-zero cut) is, at BANK, a claim
about the lanes at every clean gone cut (`firstZeroPairsForcesCyc`): every writer lane of a pair
`i ≥ 1` there would already be in a cycle class. The clean entrance does not read the writer-lane
registers, and the cycle class is thin among lane states (CLASS-COUNT 100 / 2304 at `R = 2`,
456 / 110592 at `R = 3`; the all-empty lane is outside it). This module therefore restates the
value-wave premise at the structural cut, where the group 6 bridge applies:

* `WidthDigitStructuralCut`, `WidthDigitStructuralClock`: the first strict completions of every
  complete pair in both lanes, on the audit restarted at the clean start, and the clock from the
  first-zero cut to it (the R10c premise replacing `WidthFirstZeroPairs`);
* `WidthEntryCut`, `WidthDigitEntryClock`: the strengthened block cut (pins of every interior
  pair) on the clean start, and the entry clock from the structural cut;
* `widthZeroRunStep`, `widthStructuralZeroRun`, `widthStructuralFirstZero`: the generic cut
  algebra;
* BANK: `cleanEntryBlockStage`, `cleanWaveAfterEntry` (the 200 n^2 value wave after the entry,
  from `WidthReceiptsClose` alone), `widthStructuralCyc` (every interior pair of both lanes in
  `CohortCyc` at the structural cut), and `widthDigitValueWaveOfStructural`: the R10c premise
  `WidthDigitValueWaveClock` on BANK from the structural clock, the entry clock and
  `WidthReceiptsClose`, at the structural plus entry plus wave charge.
-/

namespace L3.DigitStructuralClean

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
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
open L3.ValueWaveClose
open L3.PairBlock
open L3.BlockEntry
open L3.WidthDigit
open L3.DigitEntryPhase
open L3.DigitPairsClean

set_option autoImplicit false

/-! ### The generic structural and entry cuts -/

section Generic

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- The structural cut on the clean start: the first-zero data at some cut `zeroCut`, and a
first cut at which every complete pair has a first strict completion in both lanes, on the
audit started at a clean start. Consumer: `WidthDigitStructuralClock`, `WidthDigitEntryClock`,
`widthStructuralCyc`. -/
def WidthDigitStructuralCut (z : ref.State) : Prop :=
  ∃ (start : ref.State) (word : List (Fin n)) (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (retired zeroCut structural : Nat),
    ref.start start ∧
    word.foldl (widthDigitAuditNext ref)
      (start, digitAuditInitial (piD (ref.phys start))) = (z, audit) ∧
    WFixedRoot ring root (piW (ref.phys z)) ∧
    DigitAt ring audit audit.clock (piD (ref.phys z)) audit.current ∧
    DigitTwoBaseCovers ring root audit 0 retired zeroCut ∧
    DigitBoundaryAt ring root audit retired ∧
    DigitFirstCut (DigitStructuralAt ring root audit) structural

/-- R10c premise (structural clock, Lemma e-max for the first strict completions): from the
first-zero cut to the structural cut at charge `charge`. Replaces `WidthFirstZeroPairs` in the
value-wave producer. Consumer: `widthDigitValueWaveOfStructural`. -/
def WidthDigitStructuralClock (charge : Nat) : Prop :=
  BankRepairDigitChargedStage ref.next (WidthDigitFirstZeroCut ref)
    (WidthDigitStructuralCut ref) charge

/-- The strengthened block cut `P' j` on the clean start: a first-zero continuation, the
receipts of the blocks `< j`, and the pins of the interior blocks `≥ j`. Consumer:
`WidthDigitEntryClock`, `cleanEntryBlockStage`, `cleanWaveAfterEntry`. -/
def WidthEntryCut (j : Nat) (z : ref.State) : Prop :=
  ∃ (root : Fin n) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
    WidthZeroRun ref root (z, audit) ∧ (∀ i, i < j → BlockReceipt ring root audit i) ∧
    WidthPairsFrom ref j root (z, audit)

/-- R10c premise (entry clock): from the structural cut to the strengthened block cut `P' 0`
(the pinned window of every interior pair) at charge `charge`. Consumer:
`widthDigitValueWaveOfStructural`. -/
def WidthDigitEntryClock (charge : Nat) : Prop :=
  BankRepairDigitChargedStage ref.next (WidthDigitStructuralCut ref) (WidthEntryCut ref 0) charge

/-- First-zero continuations are carried by every coupled letter. Consumer:
`cleanEntryBlockStage`. -/
theorem widthZeroRunStep (root : Fin n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthZeroRun ref root x) (e : Fin n) :
    WidthZeroRun ref root (widthDigitAuditNext ref x e) := by
  obtain ⟨start, word0, word, y, retired, hR, hy, hW, hD, hC, hB, hx⟩ := h
  refine ⟨start, word0, word ++ [e], y, retired, hR, hy, hW, hD, hC, hB, ?_⟩
  rw [List.foldl_append, hx]
  rfl

/-- The structural cut is a first-zero continuation at its current audit, with its structural
cut. Consumer: `widthStructuralCyc`, the entry clock producer. -/
theorem widthStructuralZeroRun (z : ref.State) (h : WidthDigitStructuralCut ref z) :
    ∃ (start : ref.State) (word : List (Fin n)) (root : Fin n)
      (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (structural : Nat),
      ref.start start ∧
      word.foldl (widthDigitAuditNext ref)
        (start, digitAuditInitial (piD (ref.phys start))) = (z, audit) ∧
      WFixedRoot ring root (piW (ref.phys z)) ∧
      WidthZeroRun ref root (z, audit) ∧
      DigitFirstCut (DigitStructuralAt ring root audit) structural := by
  obtain ⟨start, word, root, audit, retired, zeroCut, structural, hR, hfold, hW, hD, hcov, hB,
    hstrict⟩ := h
  exact ⟨start, word, root, audit, structural, hR, hfold, hW,
    ⟨start, word, [], (z, audit), retired, hR, hfold, hW, hD,
      bankRepairDigitTwoBaseCoversCutMono ring root audit 0 retired zeroCut hcov, hB, rfl⟩, hstrict⟩

/-- The structural cut with the boundary leader receipt lies in the first-zero cut. Consumer:
the composition of the structural and value stages (the old
`bankRepairDigitStructuralFirstZeroCut` on the clean start). -/
theorem widthStructuralFirstZero (z : ref.State) (h : WidthDigitStructuralCut ref z)
    (hL : WidthDigitLeaderReceipt ref z) :
    WidthDigitFirstZeroCut ref z := by
  obtain ⟨start, word, root, audit, retired, zeroCut, structural, hR, hfold, hW, hD, hcov, hB, -⟩ := h
  exact ⟨start, word, root, audit, retired, hR, hfold, hW, hD,
    bankRepairDigitTwoBaseCoversCutMono ring root audit 0 retired zeroCut hcov, hB, hL⟩

end Generic

/-! ### BANK: the value wave after the entry, on the clean start -/

section Bank

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-- The pieces of a clean entry cut: by leader, and by the first delimiter (or its absence).
Consumer: `cleanEntryBlockStage`. -/
def CleanEntryPiece (j : Nat) (root : Fin n) : Option Nat → BankReferenceState ring hbank → Prop
  | none, z => ∃ audit : DigitAudit (compileAdvice (ceilLogTwo n)) n,
      WidthZeroRun (bankWidthDigitReference ring hn hbank) root (z, audit) ∧
      (∀ first, ¬ DigitFirstDelimiter ring root audit.start first) ∧
      (∀ i, i < j → BlockReceipt ring root audit i) ∧ PairsFrom ring hbank j root (z, audit)
  | some first, z => ∃ audit : DigitAudit (compileAdvice (ceilLogTwo n)) n,
      WidthZeroRun (bankWidthDigitReference ring hn hbank) root (z, audit) ∧
      DigitFirstDelimiter ring root audit.start first ∧
      (∀ i, i < j → BlockReceipt ring root audit i) ∧ PairsFrom ring hbank j root (z, audit)

/-- **The clean block stage `P' j → P' (j + 1)` at `200 n R`**: `entryBlockStage` with the
first-zero continuation on the clean start (the continuation is only carried). Consumer:
`cleanWaveAfterEntry`. -/
theorem cleanEntryBlockStage (j : Nat) :
    CoupledBlock ring hbank (WidthEntryCut (bankWidthDigitReference ring hn hbank) j)
      (WidthEntryCut (bankWidthDigitReference ring hn hbank) (j + 1)) (200 * n * valueSpan n) := by
  have hR := valueSpanTwo hn
  refine coupledBlockSigma ring hbank _ _ _
    (fun p : Fin n × Option Nat => CleanEntryPiece ring hn hbank j p.1 p.2) ?_ ?_
  · rintro z ⟨root, audit, hrun, hrec, hpf⟩
    rcases Classical.em (∃ first, DigitFirstDelimiter ring root audit.start first) with
      ⟨first, hf⟩ | hno
    · exact ⟨(root, some first), audit, hrun, hf, hrec, hpf⟩
    · exact ⟨(root, none), audit, hrun, fun f hf => hno ⟨f, hf⟩, hrec, hpf⟩
  rintro ⟨root, o⟩
  cases o with
  | none =>
      refine coupledBlockOfImp ring hbank _ _ _ ?_
      rintro z ⟨audit, hrun, hno, -, hpf⟩
      exact ⟨root, audit, hrun, fun i _ first hf => absurd hf (hno first),
        pairsFromSucc ring hbank j root _ hpf⟩
  | some first =>
      rcases Classical.em (2 ≤ first + j * valueSpan n ∧
          first + j * valueSpan n + 2 * valueSpan n < n) with ⟨hsrc, hend⟩ | hg
      · refine coupledBlockSigma ring hbank _ _ _
          (fun after z => ∃ audit : DigitAudit (compileAdvice (ceilLogTwo n)) n,
            WidthZeroRun (bankWidthDigitReference ring hn hbank) root (z, audit) ∧
            DigitFirstDelimiter ring root audit.start first ∧
            (∀ i, i < j → BlockReceipt ring root audit i) ∧
            PairsFrom ring hbank j root (z, audit) ∧ audit.clock = after) ?_ ?_
        · rintro z ⟨audit, hrun, hf, hrec, hpf⟩
          exact ⟨audit.clock, audit, hrun, hf, hrec, hpf, rfl⟩
        intro after
        refine runPairBlock ring hn hbank root DigitLane.writer (first + j * valueSpan n)
          (valueSpan n) hR hsrc (by omega) (InheritedOk DigitLane.writer) after _ _
          (fun w => WidthZeroRun (bankWidthDigitReference ring hn hbank) root w.1 ∧
            DigitFirstDelimiter ring root w.1.2.start first ∧
            (∀ i, i < j → BlockReceipt ring root w.1.2 i) ∧
            PairsFrom ring hbank (j + 1) root w.1) ?_ ?_ ?_
        · intro w e _ hc
          exact ⟨widthZeroRunStep (bankWidthDigitReference ring hn hbank) root w.1 hc.1 e, hc.2.1,
            fun i hi => receiptStep ring root _ w.1.2 e i (hc.2.2.1 i hi),
            pairsFromStep ring hbank hn (j + 1) root w.1 e hc.2.2.2⟩
        · rintro z ⟨audit, hrun, hf, hrec, hpf, haft⟩
          obtain ⟨hp, g, hw, hu⟩ := hpf first hf j (Nat.le_refl j) hsrc hend
          exact ⟨((z, audit), (g.1, 0)), rfl,
            winInvDReset ring hbank root DigitLane.writer _ _ _ (z, audit) g hw 0,
            useReachReset ring hbank root DigitLane.writer _ _ (z, audit) g hu, rfl,
            by show after ≤ audit.clock; omega, hp, hrun, hf, hrec,
            pairsFromSucc ring hbank j root _ hpf⟩
        · intro w hfw hc
          refine ⟨root, w.1.2, hc.1, fun i hi => ?_, hc.2.2.2⟩
          rcases Nat.lt_or_ge i j with hij | hij
          · exact hc.2.2.1 i hij
          · have hie : i = j := by omega
            subst hie
            intro first' hf' _ _
            have he := firstDelimUnique ring root _ hc.2.1 hf'
            subst he
            exact ⟨after, hfw⟩
      · refine coupledBlockOfImp ring hbank _ _ _ ?_
        rintro z ⟨audit, hrun, hf, hrec, hpf⟩
        refine ⟨root, audit, hrun, fun i hi => ?_, pairsFromSucc ring hbank j root _ hpf⟩
        rcases Nat.lt_or_ge i j with hij | hij
        · exact hrec i hij
        · have hie : i = j := by omega
          subst hie
          intro first' hf' h1 h2
          have he := firstDelimUnique ring root _ hf hf'
          subst he
          exact absurd ⟨h1, h2⟩ hg

/-- **The value wave after the clean entry, from `WidthReceiptsClose` alone**: `K = n / R`
clean block stages of `200 n R` from `P' 0` to `P' K`, then the value cut, within `200 n^2`.
Consumer: `widthDigitValueWaveOfStructural`. -/
theorem cleanWaveAfterEntry
    (hclose : WidthReceiptsClose (bankWidthDigitReference ring hn hbank)) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (WidthEntryCut (bankWidthDigitReference ring hn hbank) 0)
      (WidthDigitValuesStableCut (bankWidthDigitReference ring hn hbank))
      (bankRepairDigitValueWaveMicroCharge n) :=
  bankRepairDigitChargedMono _ _ _ (blockFit (valueBlocksFit n))
    (bankRepairDigitChargedWeaken _ (WidthEntryCut (bankWidthDigitReference ring hn hbank) 0)
      (WidthEntryCut (bankWidthDigitReference ring hn hbank) 0)
      (WidthEntryCut (bankWidthDigitReference ring hn hbank) (valueBlocks n)) _ _ (fun _ h => h)
      (fun z ⟨root, audit, hrun, hrec, _⟩ => hclose root z audit hrun hrec)
      (bankRepairDigitChargedChain _ (WidthEntryCut (bankWidthDigitReference ring hn hbank)) _
        (fun j => chargedOfCoupledBlock ring hbank _ _ _ (cleanEntryBlockStage ring hn hbank j))
        (valueBlocks n)))

/-- **The R10c value-wave premise on BANK from the restated premises**: the structural clock,
the entry clock and `WidthReceiptsClose` give `WidthDigitValueWaveClock` at the structural plus
entry plus wave charge. With the structural micro-charge and the entry charge
`6 n (5 R + 2 + ceilLogTwo n)` the total fits the 201 ledger (`entryLedgerFit`). Consumer:
`bankWidthDigitCausalCore` (WidthDigitCleanCore), in place of the value-wave premise built on
`WidthFirstZeroPairs`. -/
theorem widthDigitValueWaveOfStructural (cS cE : Nat)
    (hS : WidthDigitStructuralClock (bankWidthDigitReference ring hn hbank) cS)
    (hE : WidthDigitEntryClock (bankWidthDigitReference ring hn hbank) cE)
    (hclose : WidthReceiptsClose (bankWidthDigitReference ring hn hbank)) :
    WidthDigitValueWaveClock (bankWidthDigitReference ring hn hbank)
      (cS + cE + bankRepairDigitValueWaveMicroCharge n) :=
  bankRepairDigitZeroCompose (bankRepairNext ring hbank) _ _ _ _ _
    (bankRepairDigitZeroCompose (bankRepairNext ring hbank) _ _ _ _ _ hS hE)
    (cleanWaveAfterEntry ring hn hbank hclose)

include hn in
/-- **The group 6 class at the clean structural cut**: at every BANK structural cut on the
clean start, for every first delimiter of the audit start, every interior pair is complete and
both of its lanes are in `CohortCyc` (`cleanStructuralCyc`). Consumer: the entry clock producer
(`WidthDigitEntryClock`: the cohort move to the next cycle start, then `winInvDAtCycStart`). -/
theorem widthStructuralCyc
    (z : BankReferenceState ring hbank)
    (h : WidthDigitStructuralCut (bankWidthDigitReference ring hn hbank) z) :
    ∃ (root : Fin n) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
      WidthZeroRun (bankWidthDigitReference ring hn hbank) root (z, audit) ∧
      ∀ first, DigitFirstDelimiter ring root audit.start first → ∀ (i : Nat) (lane : DigitLane),
        2 ≤ first + i * valueSpan n → first + i * valueSpan n + 2 * valueSpan n < n →
        PairIn ring root (first + i * valueSpan n) (valueSpan n) audit ∧
        CohortCyc (valueSpan n) (cohortProj ring root lane (first + i * valueSpan n) (valueSpan n)
          (piD z.val.1)) := by
  obtain ⟨start, word, root, audit, structural, ⟨hD, hC⟩, hfold, hW, hrun, hS⟩ :=
    widthStructuralZeroRun (bankWidthDigitReference ring hn hbank) z h
  have hfold' : word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (z, audit) := hfold
  refine ⟨root, audit, hrun, fun first hf i lane h2 hend => ?_⟩
  have hc := cleanStructuralCyc ring hn hbank start hD hC word root
    (by rw [hfold']; exact hW) structural (by rw [hfold']; exact hS.1) first
    (by rw [hfold']; exact hf) i lane h2 hend
  rw [hfold'] at hc
  exact hc

end Bank

end L3.DigitStructuralClean

#print axioms L3.DigitStructuralClean.widthZeroRunStep
#print axioms L3.DigitStructuralClean.widthStructuralZeroRun
#print axioms L3.DigitStructuralClean.widthStructuralFirstZero
#print axioms L3.DigitStructuralClean.cleanEntryBlockStage
#print axioms L3.DigitStructuralClean.cleanWaveAfterEntry
#print axioms L3.DigitStructuralClean.widthDigitValueWaveOfStructural
#print axioms L3.DigitStructuralClean.widthStructuralCyc
