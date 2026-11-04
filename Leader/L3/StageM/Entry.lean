import Leader.L3.Width.DigitWriterStage
import Leader.L3.Bank.RepairDigitStructuralClean

/-!
# The entry clocks from the pin after a strict completion

The two entry clocks of `l3HeadlineOfCleanBranches`,

* `hentrySmall`: SMALL, from the writer cut `WidthDigitWriterCut` to the pinned block cut
  `WidthEntryCut _ 0`;
* `hentry`: BANK, `WidthDigitEntryClock` (from the structural cut `WidthDigitStructuralCut` to
  `WidthEntryCut _ 0`);

are inclusions of cuts, hence hold at every charge, once one per-pair fact holds on the writer
lane: `WidthPinAfterStrict`. On a first-zero run of the clean audit, a writer pair with a strict
completion (`DigitCompletion` at the cut `0`) has the pinned window and the use track
(`WidthWinInvD ∧ WidthUseReach` for some cycle ghost). Both cuts give a strict completion of
every interior writer pair (the writer cut by definition; the structural cut by
`DigitStructuralAt` and `cleanPairIn`), and `DigitCompletion` contains the complete pair
(`PairIn`), so every interior pair is pinned (`WidthPairPin`), which is `WidthEntryCut _ 0`.

Truth of `WidthPinAfterStrict` on the literal lane (research/lean-l3/wip/r10c-mc/entry_mc.py,
lane rows `cohortEdge`, audit ghost `digitLaneReplay`, exhaustive from every lane state with the
initial ghost): at every lane state after a strict completion and for every cycle witness
`(o, lam)` (`CohortCycIn`, counter `0`), `YInv`, `ChosenInv` and the window clauses (`CycWin`,
`ChiInv`, `ChiAtoms`, `CurIdA`, with `t0` just before the first crossing of the chosen cohort)
hold: 40/40 states at `R = 2`, 176/176 at `R = 3` (112 with crossed slots, 35 with younger
packets). Not modelled: the value clauses (`WidthValReach`) and the run invariants
(`GhostCorrDistinct`, layout, frame order), which are first-zero-run invariants.
-/

namespace L3.StageMEntry

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open L3.WidthDigit
open L3.DigitCohortScratch
open L3.DigitStructuralClean
open L3.WriterStage
open L3.DigitPairsClean
open L3.PairBlock
open L3.Correspondence
open L3.ValueWaveClose

section Generic

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- **The pin after a strict completion** (the single open per-pair fact of the entry stage):
on a first-zero run of the clean audit, an interior writer pair with a strict completion has a
cycle ghost with the pinned window (`WidthWinInvD`, base `InheritedOk`) and the use track
(`WidthUseReach`). Consumer: `pairPinOfCompletion`, hence `writerCutEntry`,
`smallEntryOfPin`, `bankEntryOfPin`. -/
def WidthPinAfterStrict : Prop :=
  ∀ (root : Fin n) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    WidthZeroRun ref root x →
    ∀ (src : Nat) (tm : DigitTerminal (compileAdvice (ceilLogTwo n)) n),
      2 ≤ src → src + 2 * valueSpan n < n →
      DigitCompletion ring x.2 root src (src + valueSpan n) DigitLane.writer 0 tm →
      ∃ g : (Nat → Nat) × Nat,
        WidthWinInvD ref root DigitLane.writer src (valueSpan n)
          (InheritedOk DigitLane.writer) x g ∧
        WidthUseReach ref root DigitLane.writer src (valueSpan n) (x, g)

/-- A strict completion gives the pair's pin, the complete pair being part of the completion.
Consumer: `writerCutEntry`, `structuralCutEntry`. -/
theorem pairPinOfCompletion (hpin : WidthPinAfterStrict ref) (root : Fin n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthZeroRun ref root x) (src : Nat)
    (tm : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (h2 : 2 ≤ src)
    (hend : src + 2 * valueSpan n < n)
    (hc : DigitCompletion ring x.2 root src (src + valueSpan n) DigitLane.writer 0 tm) :
    WidthPairPin ref root src x :=
  ⟨hc.1, hpin root x hx src tm h2 hend hc⟩

/-- The writer cut lies in the pinned block cut `P' 0`. Consumer: `smallEntryOfPin`. -/
theorem writerCutEntry (hpin : WidthPinAfterStrict ref) (z : ref.State)
    (h : WidthDigitWriterCut ref z) : WidthEntryCut ref 0 z := by
  obtain ⟨root, audit, hrun, hdone⟩ := h
  refine ⟨root, audit, hrun, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
  intro first hf i _ h2 hend
  obtain ⟨tm, htm⟩ := hdone i first hf hend
  exact pairPinOfCompletion ref hpin root (z, audit) hrun _ tm h2 hend htm

end Generic

/-- An inclusion of cuts is a charged stage at every charge (the cost from a goal state is `0`).
Consumer: `smallEntryOfPin`, `bankEntryOfPin`. -/
theorem chargedOfIncl {S : Type} {n : Nat} (next : S → Fin n → S) (A B : S → Prop)
    (h : ∀ x, A x → B x) (charge : Nat) : BankRepairDigitChargedStage next A B charge := by
  intro x hx T
  rw [costNumerator_terminal next B x (h x hx) T]
  exact Nat.zero_le _

/-- **The SMALL entry clock** (`hentrySmall`), at every charge, from the pin after a strict
completion at the band reference. Consumer: `hentrySmall` of `l3HeadlineOfCleanBranches`. -/
theorem smallEntryOfPin {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hpin : WidthPinAfterStrict (bandWidthDigitReference ring hn)) (charge : Nat) :
    BankRepairDigitChargedStage (bandWidthDigitReference ring hn).next
      (WidthDigitWriterCut (bandWidthDigitReference ring hn))
      (WidthEntryCut (bandWidthDigitReference ring hn) 0) charge :=
  chargedOfIncl _ _ _ (writerCutEntry _ hpin) charge

section Bank

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

include hn in
/-- The structural cut lies in the pinned block cut `P' 0` on BANK: every interior writer pair
is complete (`cleanPairIn`) and has its first strict completion (`DigitStructuralAt`).
Consumer: `bankEntryOfPin`. -/
theorem structuralCutEntry
    (hpin : WidthPinAfterStrict (bankWidthDigitReference ring hn hbank))
    (z : BankReferenceState ring hbank)
    (h : WidthDigitStructuralCut (bankWidthDigitReference ring hn hbank) z) :
    WidthEntryCut (bankWidthDigitReference ring hn hbank) 0 z := by
  obtain ⟨start, word, root, audit, structural, ⟨hD, hC⟩, hfold, hW, hrun, hS⟩ :=
    widthStructuralZeroRun (bankWidthDigitReference ring hn hbank) z h
  have hfold' : word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (z, audit) := hfold
  refine ⟨root, audit, hrun, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
  intro first hf i _ h2 hend
  have hpair := cleanPairIn ring hn hbank start hD hC word root
    (by rw [hfold']; exact hW) first (by rw [hfold']; exact hf) i h2 hend
  rw [hfold'] at hpair
  obtain ⟨tm, htm, -⟩ := hS.1.2 _ _ DigitLane.writer hpair
  exact pairPinOfCompletion (bankWidthDigitReference ring hn hbank) hpin root (z, audit) hrun _
    tm h2 hend htm.1

include hn in
/-- **The BANK entry clock** (`hentry`), at every charge, from the pin after a strict
completion at the BANK reference. Consumer: `hentry` of `l3HeadlineOfCleanBranches`. -/
theorem bankEntryOfPin
    (hpin : WidthPinAfterStrict (bankWidthDigitReference ring hn hbank)) (charge : Nat) :
    WidthDigitEntryClock (bankWidthDigitReference ring hn hbank) charge :=
  chargedOfIncl _ _ _ (structuralCutEntry ring hn hbank hpin) charge

end Bank

end L3.StageMEntry

#print axioms L3.StageMEntry.pairPinOfCompletion
#print axioms L3.StageMEntry.writerCutEntry
#print axioms L3.StageMEntry.chargedOfIncl
#print axioms L3.StageMEntry.smallEntryOfPin
#print axioms L3.StageMEntry.structuralCutEntry
#print axioms L3.StageMEntry.bankEntryOfPin
