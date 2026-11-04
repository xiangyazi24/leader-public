import Leader.L3.Width.DigitReference

/-!
# The R10c digit cut family on an abstract reference, with the clean start

Every BANK digit cut is restated over a `WidthDigitReference`: the coupled audit step
`widthDigitAuditNext` (first coordinate the reference successor, second the proof-only digit
audit of the OLD physical D projection), the boundary, gone, first-zero, successor-value and
comparison cuts with the audit started at `ref.start` (the clean start), the cohort window tree
behind `FirstZeroPairs` (`WidthCohortLayout` ... `WidthPairsFrom`), and the R10c premises:
the boundary stage, the first-zero, value-wave and comparison clocks (charges as parameters),
`WidthFirstZeroPairs`, `WidthReceiptsClose` and the comparison-entry certificate.

BANK identities (`bankWidthDigitReference`):

* start-free objects are the BANK objects by `rfl`: the audit step, `widthDigitAllBaseLabelsGone`,
  `WidthDigitLeaderReceipt`, `WidthDigitLayoutFixed`, `WidthCohortLayout`, `widthWindowNext`,
  `WidthValReach`, `WidthPinReach`, `WidthUseReach`, `WidthWinInvD`, `WidthPairPin`,
  `WidthPairsFrom`;
* start-dependent cuts are the CLEAN BANK cuts of BankRepairDigitBoundaryClean (the old cuts with
  `BankRepairRFoldEstablished` are unreachable from the clean entrance): boundary retired, gone
  cut and gone-reachable are equivalent to `BankCleanBoundaryRetiredCut`,
  `BankCleanBoundaryGoneCut`, `BankCleanBoundaryGoneReachable`;
* the boundary stage holds on BANK (`widthDigitBoundaryStageBank`, from
  `bankCleanBoundaryStage`).
-/

namespace L3.WidthDigit

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

set_option autoImplicit false

section Cuts

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-! ### The coupled audit step and the boundary cuts -/

/-- One reference step with the proof-only digit audit of the OLD physical D projection.
Consumer: every cut below. -/
def widthDigitAuditNext
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n) :
    ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n :=
  (ref.next z.1 e, digitAuditStep ring (piD (ref.phys z.1)) z.2 e)

/-- Every inherited base label of the audit is gone.  Consumer: `WidthDigitGoneCut`. -/
def widthDigitAllBaseLabelsGone
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ¬ ∃ site : Fin n, bankRepairDigitInheritedLabelAlive site z.2.current

/-- The boundary cut: leading and final packet authority retired and inherited base extinct,
on the audit started at a clean start.  Consumer: `widthCleanDigitCoreCuts`,
`WidthDigitBoundaryStage`, `WidthDigitFirstZeroClock`. -/
def WidthDigitBoundaryRetiredCut (z : ref.State) : Prop :=
  ∃ (start : ref.State) (word : List (Fin n)) (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
    ref.start start ∧
    word.foldl (widthDigitAuditNext ref)
      (start, digitAuditInitial (piD (ref.phys start))) = (z, audit) ∧
    WFixedRoot ring root (piW (ref.phys z)) ∧
    DigitAt ring audit audit.clock (piD (ref.phys z)) audit.current ∧
    DigitBoundaryReceipt ring root (piD (ref.phys z)) ∧
    DigitBaseExtinct ring root audit 0 audit.clock

/-- The gone cut: reached from a clean start by a word at which every inherited base label of
the audit restarted there is gone.  Consumer: `WidthDigitGoneReachable`. -/
def WidthDigitGoneCut (z : ref.State) : Prop :=
  ∃ (start : ref.State) (word : List (Fin n)),
    ref.start start ∧
    widthDigitAllBaseLabelsGone ref
      (word.foldl (widthDigitAuditNext ref)
        (start, digitAuditInitial (piD (ref.phys start)))) ∧
    z = word.foldl ref.next start

/-- States reachable from the gone cut.  Consumer: `widthCleanDigitCoreCuts`. -/
def WidthDigitGoneReachable (z : ref.State) : Prop :=
  ∃ (z₀ : ref.State) (word : List (Fin n)),
    WidthDigitGoneCut ref z₀ ∧ z = word.foldl ref.next z₀

/-- The boundary receipt at the W fixed leader.  Consumer: the first-zero clock producers
(the BANK keep stage carries it). -/
def WidthDigitLeaderReceipt (z : ref.State) : Prop :=
  ∃ root : Fin n, WFixedRoot ring root (piW (ref.phys z)) ∧
    DigitBoundaryReceipt ring root (piD (ref.phys z))

/-- The boundary receipt at a past time survives later frames.  Consumer: the producers of
`WidthDigitFirstZeroCut`, `WidthZeroRun`, `L3.WriterValueCuts.WidthWriterValueReceipts`. -/
theorem digitBoundaryAtMono {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (A A' : DigitAudit c n) (hstart : A'.start = A.start)
    (hsub : ∀ f, f ∈ A.frames → f ∈ A'.frames) (cut : Nat)
    (h : DigitBoundaryAt ring root A cut) : DigitBoundaryAt ring root A' cut := by
  obtain ⟨S, G, hat, hr⟩ := h
  exact ⟨S, G, bankRepairDigitZeroAtMono ring A A' hstart hsub cut S G hat, hr⟩

/-! ### The first-zero, successor-value and comparison cuts -/

/-- First zero: two witnessed root-origin base passes after retirement, on the audit started
at a clean start, at the W fixed root, keeping the boundary leader receipt of the
boundary-retired cut (DESIGN-MOTIVATIONS 2026-11-02 08:45: every width cut from the
boundary-retired cut on carries `WidthDigitLeaderReceipt`), with the boundary receipt at the
retirement itself: the covers are later than it, so no stale first-segment input outlasts them
(run: research/lean-l3/wip/r10c-qdigit/cex_first_block.py).  Consumer: `widthCleanDigitCoreCuts`,
`WidthDigitFirstZeroClock`, `WidthDigitValueWaveClock`. -/
def WidthDigitFirstZeroCut (z : ref.State) : Prop :=
  ∃ (start : ref.State) (word : List (Fin n)) (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (retired : Nat),
    ref.start start ∧
    word.foldl (widthDigitAuditNext ref)
      (start, digitAuditInitial (piD (ref.phys start))) = (z, audit) ∧
    WFixedRoot ring root (piW (ref.phys z)) ∧
    DigitAt ring audit audit.clock (piD (ref.phys z)) audit.current ∧
    DigitTwoBaseCovers ring root audit 0 retired audit.clock ∧
    DigitBoundaryAt ring root audit retired ∧
    WidthDigitLeaderReceipt ref z

/-- All successor-value dependencies current and stable, on the audit started at a clean
start.  Consumer: `widthCleanDigitCoreCuts`, `WidthDigitValueWaveClock`,
`WidthDigitComparisonClock`, `WidthReceiptsClose`. -/
def WidthDigitValuesStableCut (z : ref.State) : Prop :=
  ∃ (start : ref.State) (word : List (Fin n)) (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (retired restart : Nat),
    ref.start start ∧
    word.foldl (widthDigitAuditNext ref)
      (start, digitAuditInitial (piD (ref.phys start))) = (z, audit) ∧
    WFixedRoot ring root (piW (ref.phys z)) ∧
    DigitAt ring audit audit.clock (piD (ref.phys z)) audit.current ∧
    BankRepairDigitValueReceipts ring root audit retired restart

/-- The value receipts and the first comparison-ready cut restarted at the last value cut,
on the audit started at a clean start.  Consumer: `WidthDigitComparisonClock`,
`WidthCleanDigitCorePreDrain`, `WidthDigitComparisonCertificate`. -/
def WidthDigitComparisonCut (z : ref.State) : Prop :=
  ∃ (start : ref.State) (word : List (Fin n)) (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (retired restart comparisonCut : Nat),
    ref.start start ∧
    word.foldl (widthDigitAuditNext ref)
      (start, digitAuditInitial (piD (ref.phys start))) = (z, audit) ∧
    WFixedRoot ring root (piW (ref.phys z)) ∧
    DigitAt ring audit audit.clock (piD (ref.phys z)) audit.current ∧
    BankRepairDigitValueReceipts ring root audit retired restart ∧
    DigitFirstCut (DigitComparisonReady ring root audit restart) comparisonCut

/-! ### The cohort window tree behind `FirstZeroPairs` -/

/-- Fixed marker layout and fixed leader: the singleton class plus `Q_W`.  Consumer:
`WidthCohortLayout`. -/
def WidthDigitLayoutFixed (root : Fin n) (z : ref.State) : Prop :=
  ref.singleton root z ∧ AcceptedReceipts.QWord ring (piW (ref.phys z))

/-- The layout class of one interior pair.  Consumer: `WidthWinInvD`. -/
def WidthCohortLayout (root : Fin n) (src R : Nat) (z : ref.State) : Prop :=
  WidthDigitLayoutFixed ref root z ∧
    (piD (ref.phys z) (digitSite ring root src)).word.beta = true ∧
    (piD (ref.phys z) (digitSite ring root (src + R))).word.beta = true ∧
    (piD (ref.phys z) (digitSite ring root (src + 2 * R))).word.beta = true ∧
    ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (piD (ref.phys z) (digitSite ring root (src + k))).word.beta = false

/-- The cycle ghost of `cohortCycleNext`, read off the reference component.  Consumer:
`widthWindowNext`. -/
noncomputable def widthWindowGhost (root : Fin n) (lane : DigitLane) (src R : Nat)
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (e : Fin n) : (Nat → Nat) × Nat :=
  cohortCycleGhost R (cohortProj ring root lane src R (piD (ref.phys z.1))) g
    (cohortEdgeOf root src R e)

/-- The coupled chain with the cycle ghost.  Consumer: `WidthChiCore`. -/
noncomputable def widthWindowNext (root : Fin n) (lane : DigitLane) (src R : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (e : Fin n) :
    (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat) :=
  (widthDigitAuditNext ref w.1 e, widthWindowGhost ref root lane src R w.1 w.2 e)

/-- The value invariant of a coupled state.  Consumer: `WidthValReach`. -/
def WidthValInv (root : Fin n) (lane : DigitLane) (src R : Nat)
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ValCorr ring root lane src R (piD (ref.phys z.1)) z.2 ∧ ExportVal ring root lane src R z.2 ∧
    UseVal ring root lane src R z.2 ∧ LedgerOk ring root lane src R z.2

/-- Exact frames and the value invariant.  Consumer: `WidthPinReach`. -/
def WidthValReach (root : Fin n) (lane : DigitLane) (src R : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat)) :
    Prop :=
  FramesExact ring w.1.2 ∧ WidthValInv ref root lane src R w.1

/-- The younger cells of a coupled state are pinned.  Consumer: `WidthPinState`. -/
def WidthYInv (root : Fin n) (lane : DigitLane) (src R : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat)) :
    Prop :=
  YoungInv R (SPin ring root lane src w.1.2) (tracked ring root lane src R w.1.2) w.2.1

/-- The window clauses of a closing window, without destinations.  Consumer:
`WidthLastClose`. -/
def WidthChiCore (root : Fin n) (lane : DigitLane) (src R : Nat)
    (wc : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  (∀ i, i < R → DigitRecordedExport wc.1.2 (chi i) ∧ OnEdge ring root lane src R (chi i)) ∧
  (∀ a b, a < b → b < R → (chi a).time < (chi b).time) ∧
  ∀ (word : List (Fin n)) (x : DigitExport (compileAdvice (ceilLogTwo n)) n),
    DigitRecordedExport (word.foldl (widthWindowNext ref root lane src R) wc).1.2 x →
    OnEdge ring root lane src R x → (chi 0).time ≤ x.time → x.time ≤ (chi (R - 1)).time →
    ∃ i, i < R ∧ x = chi i

/-- The window closed last.  Consumer: `WidthPinState`, `WidthIdState`. -/
def WidthLastClose (root : Fin n) (lane : DigitLane) (src R : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat) : Prop :=
  WidthChiCore ref root lane src R w chi ∧ SitePin ring root lane src R w.1.2 chi ∧
  ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n, DigitRecordedExport w.1.2 x →
    OnEdge ring root lane src R x → x.time ≤ t0 → x.time ≤ (chi (R - 1)).time

/-- The pin invariant.  Consumer: `WidthPinReach`. -/
def WidthPinState (root : Fin n) (lane : DigitLane) (src R : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat)) :
    Prop :=
  ChosenInv R (SPin ring root lane src w.1.2) (tracked ring root lane src R w.1.2) w.2.1 ∧
  WidthYInv ref root lane src R w ∧
  ∃ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat),
    CycWin ring root lane src R w.1.2 w.2.1 chi t0 ∧
    ChiInv R (SPin ring root lane src w.1.2) chi w.2.1 ∧
    (1 ≤ w.2.2 → ∃ chiOld, WidthLastClose ref root lane src R w chiOld t0)

/-- Exact frames, the value invariant, the pin invariant.  Consumer: `WidthUseReach`. -/
def WidthPinReach (root : Fin n) (lane : DigitLane) (src R : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat)) :
    Prop :=
  WidthValReach ref root lane src R w ∧ WidthPinState ref root lane src R w

/-- The identity state.  Consumer: `WidthUseReach`. -/
def WidthIdState (root : Fin n) (lane : DigitLane) (src R : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat)) :
    Prop :=
  ∃ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat),
    CycWin ring root lane src R w.1.2 w.2.1 chi t0 ∧
    ChiInv R (SPin ring root lane src w.1.2) chi w.2.1 ∧
    CurIdA R w.2.1 (inA ring root lane src w.1.2) chi ∧
    (1 ≤ w.2.2 → ∃ chiOld, WidthLastClose ref root lane src R w chiOld t0 ∧
      OldIdA R w.2.1 (inA ring root lane src w.1.2) chiOld)

/-- The strengthened reach class.  Consumer: `WidthPairPin`. -/
def WidthUseReach (root : Fin n) (lane : DigitLane) (src R : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat)) :
    Prop :=
  WidthPinReach ref root lane src R w ∧ WidthIdState ref root lane src R w

/-- The strengthened window invariant.  Consumer: `WidthPairPin`. -/
def WidthWinInvD (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop)
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) : Prop :=
  WidthCohortLayout ref root src R z.1 ∧ AuditFrameOrder z.2 ∧
  GhostCorrDistinct ring root lane src R Base (piD (ref.phys z.1)) z.2 ∧
  (∃ o, CohortCycIn R g.2 (cohortProj ring root lane src R (piD (ref.phys z.1))) g o) ∧
  ∃ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat),
    CycWin ring root lane src R z.2 g.1 chi t0 ∧ ChiAtoms ring root lane src R Base z.2 g.1 chi

/-- The lift data of one pair.  Consumer: `WidthPairsFrom`. -/
def WidthPairPin (root : Fin n) (src : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  PairIn ring root src (valueSpan n) x.2 ∧
  ∃ g : (Nat → Nat) × Nat,
    WidthWinInvD ref root DigitLane.writer src (valueSpan n) (InheritedOk DigitLane.writer) x g ∧
    WidthUseReach ref root DigitLane.writer src (valueSpan n) (x, g)

/-- The lift data of every interior block `i ≥ j`.  Consumer: `WidthFirstZeroPairs`. -/
def WidthPairsFrom (j : Nat) (root : Fin n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∀ first : Nat, DigitFirstDelimiter ring root x.2.start first → ∀ i, j ≤ i →
    2 ≤ first + i * valueSpan n → first + i * valueSpan n + 2 * valueSpan n < n →
    WidthPairPin ref root (first + i * valueSpan n) x

/-- A coupled pair continuing a first-zero state of the audit started at a clean start.
Consumer: `WidthReceiptsClose`. -/
def WidthZeroRun (root : Fin n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ (start : ref.State) (word0 word : List (Fin n))
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (retired : Nat),
    ref.start start ∧
    word0.foldl (widthDigitAuditNext ref)
      (start, digitAuditInitial (piD (ref.phys start))) = y ∧
    WFixedRoot ring root (piW (ref.phys y.1)) ∧
    DigitAt ring y.2 y.2.clock (piD (ref.phys y.1)) y.2.current ∧
    DigitTwoBaseCovers ring root y.2 0 retired y.2.clock ∧
    DigitBoundaryAt ring root y.2 retired ∧
    word.foldl (widthDigitAuditNext ref) y = x

/-! ### The R10c premises, once for both bands -/

/-- R10c premise (first-zero pair pins): at every first-zero state of the clean audit, every
interior block of the first delimiter carries the lift data.  Consumer: the value-wave clock
producer (to be re-derived on the clean start; BANK old-start version
`bankRepairDigitValueWaveClockOfPairs`). -/
def WidthFirstZeroPairs : Prop :=
  ∀ (start : ref.State) (word : List (Fin n)) (root : Fin n) (z : ref.State)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (retired : Nat),
    ref.start start →
    word.foldl (widthDigitAuditNext ref)
      (start, digitAuditInitial (piD (ref.phys start))) = (z, audit) →
    WFixedRoot ring root (piW (ref.phys z)) →
    DigitAt ring audit audit.clock (piD (ref.phys z)) audit.current →
    DigitTwoBaseCovers ring root audit 0 retired audit.clock →
    WidthPairsFrom ref 0 root (z, audit)

/-- R10c premise (receipt conversion): the receipts of all blocks on a clean first-zero
continuation give the successor-value cut.  Consumer: the value-wave clock producer. -/
def WidthReceiptsClose : Prop :=
  ∀ (root : Fin n) (z : ref.State) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
    WidthZeroRun ref root (z, audit) →
    (∀ i, i < valueBlocks n → BlockReceipt ring root audit i) →
    WidthDigitValuesStableCut ref z

/-- R10c premise (boundary stage): from the clean start, the boundary cut with the drain
retained, at charge `charge`.  Consumer: `widthDigitCausalCoreOfPremises`. -/
def WidthDigitBoundaryStage (charge : Nat) : Prop :=
  BankRepairDigitChargedStage ref.next ref.start
    (fun z => ref.drained z ∧
      (WidthDigitBoundaryRetiredCut ref z ∧ WidthDigitGoneReachable ref z))
    charge

/-- R10c premise (T19 first-zero clock) at charge `charge`.  Consumer:
`widthDigitCausalCoreOfPremises`. -/
def WidthDigitFirstZeroClock (charge : Nat) : Prop :=
  BankRepairDigitChargedStage ref.next
    (fun z => WidthDigitBoundaryRetiredCut ref z ∧ WidthDigitGoneReachable ref z)
    (WidthDigitFirstZeroCut ref) charge

/-- R10c premise (successor-value wave clock) at charge `charge`.  Consumer:
`widthDigitCausalCoreOfPremises`. -/
def WidthDigitValueWaveClock (charge : Nat) : Prop :=
  BankRepairDigitChargedStage ref.next (WidthDigitFirstZeroCut ref)
    (WidthDigitValuesStableCut ref) charge

/-- R10c premise (restarted comparison clock) at charge `charge`.  Consumer:
`widthDigitCausalCoreOfPremises`. -/
def WidthDigitComparisonClock (charge : Nat) : Prop :=
  BankRepairDigitChargedStage ref.next (WidthDigitValuesStableCut ref)
    (WidthDigitComparisonCut ref) charge

/-- R10c premise (comparison-entry certificate): at a drained comparison cut, a clean word root
with correct digit values and QDigit.  Consumer: `widthDigitCausalCoreOfPremises`. -/
def WidthDigitComparisonCertificate : Prop :=
  ∀ start : ref.State, ref.drained start → WidthDigitComparisonCut ref start →
    ∃ root : Fin n,
      CleanWordAtRoot ring root (piW (ref.phys start)) ∧
      AcceptedReceipts.DigitValuesCorrect ring root
        (AcceptedReceipts.digitValueView (piD (ref.phys start))) ∧
      AcceptedReceipts.QDigit ring (piD (ref.phys start))

end Cuts

/-! ### BANK identities -/

section Bank

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-- The generic audit step at BANK is `bankRepairDigitBoundaryAuditNext`.  Consumer: the BANK
recovery of the old-start objects and `widthDigitBoundaryRetiredBank`. -/
theorem widthDigitAuditNextBank :
    widthDigitAuditNext (bankWidthDigitReference ring hn hbank) =
      bankRepairDigitBoundaryAuditNext ring hbank := rfl

/-- Consumer: `widthDigitGoneCutBank`. -/
theorem widthDigitAllBaseLabelsGoneBank :
    widthDigitAllBaseLabelsGone (bankWidthDigitReference ring hn hbank) =
      bankRepairDigitAllBaseLabelsGone ring hbank := rfl

/-- Consumer: the BANK first-zero clock producer (the keep stage lands in it). -/
theorem widthDigitLeaderReceiptBank :
    WidthDigitLeaderReceipt (bankWidthDigitReference ring hn hbank) =
      BankRepairDigitLeaderReceipt ring hbank := rfl

/-- Consumer: the BANK cohort bridge (`bankCleanBoundaryCohortLayout`) feeding
`WidthFirstZeroPairs`. -/
theorem widthCohortLayoutBank (root : Fin n) (src R : Nat) :
    WidthCohortLayout (bankWidthDigitReference ring hn hbank) root src R =
      CohortLayout ring hbank root src R := rfl

/-- Consumer: the BANK window-run lemmas (`winInvDStep`, `useReachStep`) read through the
generic tree. -/
theorem widthWindowNextBank (root : Fin n) (lane : DigitLane) (src R : Nat) :
    widthWindowNext (bankWidthDigitReference ring hn hbank) root lane src R =
      windowNext ring hbank root lane src R := rfl

/-- Consumer: as `widthWindowNextBank`. -/
theorem widthWinInvDBank (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop) :
    WidthWinInvD (bankWidthDigitReference ring hn hbank) root lane src R Base =
      WinInvD ring hbank root lane src R Base := rfl

/-- Consumer: as `widthWindowNextBank`. -/
theorem widthUseReachBank (root : Fin n) (lane : DigitLane) (src R : Nat) :
    WidthUseReach (bankWidthDigitReference ring hn hbank) root lane src R =
      UseReach ring hbank root lane src R := rfl

/-- Consumer: the BANK `WidthFirstZeroPairs` producer (`pairPinStep`, `pairsFromStep`). -/
theorem widthPairsFromBank (j : Nat) (root : Fin n) :
    WidthPairsFrom (bankWidthDigitReference ring hn hbank) j root =
      PairsFrom ring hbank j root := rfl

/-- The generic boundary cut at BANK is the clean BANK boundary cut.  Consumer:
`widthDigitBoundaryStageBank`. -/
theorem widthDigitBoundaryRetiredBank (z : BankReferenceState ring hbank) :
    WidthDigitBoundaryRetiredCut (bankWidthDigitReference ring hn hbank) z ↔
      BankCleanBoundaryRetiredCut ring hbank z := by
  constructor
  · rintro ⟨start, word, root, audit, ⟨hD, hC⟩, h⟩
    exact ⟨start, word, root, audit, hD, hC, h⟩
  · rintro ⟨start, word, root, audit, hD, hC, h⟩
    exact ⟨start, word, root, audit, ⟨hD, hC⟩, h⟩

/-- The generic gone cut at BANK is the clean BANK gone cut.  Consumer:
`widthDigitGoneReachableBank`. -/
theorem widthDigitGoneCutBank (z : BankReferenceState ring hbank) :
    WidthDigitGoneCut (bankWidthDigitReference ring hn hbank) z ↔
      BankCleanBoundaryGoneCut ring hbank z := by
  constructor
  · rintro ⟨start, word, ⟨hD, hC⟩, h⟩
    exact ⟨start, word, hD, hC, h⟩
  · rintro ⟨start, word, hD, hC, h⟩
    exact ⟨start, word, ⟨hD, hC⟩, h⟩

/-- Consumer: `widthDigitBoundaryStageBank`. -/
theorem widthDigitGoneReachableBank (z : BankReferenceState ring hbank) :
    WidthDigitGoneReachable (bankWidthDigitReference ring hn hbank) z ↔
      BankCleanBoundaryGoneReachable ring hbank z := by
  constructor
  · rintro ⟨z₀, word, h, rfl⟩
    exact ⟨z₀, word, (widthDigitGoneCutBank ring hn hbank z₀).1 h, rfl⟩
  · rintro ⟨z₀, word, h, rfl⟩
    exact ⟨z₀, word, (widthDigitGoneCutBank ring hn hbank z₀).2 h, rfl⟩

/-- The R10c boundary stage holds on BANK, at the boundary micro-charge, from
`bankCleanBoundaryStage`.  Consumer: `bankWidthDigitCausalCore` (WidthDigitCleanCore). -/
theorem widthDigitBoundaryStageBank :
    WidthDigitBoundaryStage (bankWidthDigitReference ring hn hbank)
      (bankRepairDigitBoundaryMicroCharge n) :=
  bankRepairDigitChargedWeaken (bankRepairNext ring hbank) _ _ _ _ _
    (fun _ h => h)
    (fun z ⟨hD, hR, hG⟩ => ⟨hD, (widthDigitBoundaryRetiredBank ring hn hbank z).2 hR,
      (widthDigitGoneReachableBank ring hn hbank z).2 hG⟩)
    (bankCleanBoundaryStage ring hbank hn)

end Bank

end L3.WidthDigit

#print axioms L3.WidthDigit.widthDigitAuditNextBank
#print axioms L3.WidthDigit.widthCohortLayoutBank
#print axioms L3.WidthDigit.widthPairsFromBank
#print axioms L3.WidthDigit.widthDigitBoundaryRetiredBank
#print axioms L3.WidthDigit.widthDigitGoneCutBank
#print axioms L3.WidthDigit.widthDigitGoneReachableBank
#print axioms L3.WidthDigit.widthDigitBoundaryStageBank
