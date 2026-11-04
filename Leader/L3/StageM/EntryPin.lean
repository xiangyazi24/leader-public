import Leader.L3.StageM.Entry
import Leader.L3.Width.PacketMomentCompare

/-!
# The pin at a cycle start, and its propagation to the strict cut

`WidthPinAfterStrict` (the premise `hpin` of the headline) asks, on a first-zero run with a strict
completion of an interior writer pair, for the pinned window and the use track of the pair. This
module reduces it to one state-level fact at one earlier state of the run:

* `widthWinInvDAtCycStart`, `widthUseReachOfStart`: the width ports of `winInvDAtCycStart` and
  `useReachOfStart` (ghost `lam = 0`, counter `0`).
* `WidthCycStartPinned`: `lam = 0` is a cycle witness with counter `0` (`CohortCycIn R 0`, any old
  phase) and every chosen (home) source cell carries a sample read at its own cell (`ChosenInv` at
  `lam = 0`).
* `pairPinOfCycStart`: the run invariant `WidthRunInv` and `WidthCycStartPinned` give
  `WidthPairPin`.
* `pairPinFold`: `WidthPairPin` is carried by every word (`widthPairPinStep`).
* `WidthCycStartAfterStrict` (the reduced premise) and `pinAfterStrictOfCycStart`: if every strict
  completion has, earlier on the same run, a state with the run invariant and
  `WidthCycStartPinned`, then `WidthPinAfterStrict` holds.

The state meant for `WidthCycStartAfterStrict` is the state right after the export of the strict
cohort's tail sample (research/lean-l3/wip/r10c-mc/tail_mc.py: 8/8 export transitions at `R = 2`,
24/24 at `R = 3`, with `lam = 0` a witness at old phase `o ≤ R` and every source packet read at its
own cell).
-/

namespace L3.StageMEntryPin

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WidthWave
open L3.StageMEntry
open L3.WidthPacketMomentCutEntry
open L3.WidthPacketMomentGroupCompletion
open L3.Rearm
open L3.CohortWindow
open L3.CohortClose
open L3.SitePin
open L3.UseCells
open L3.UseTrack
open L3.Correspondence
open L3.CohortSites
open L3.PacketClass
open L3.ValueWaveClose
open L3.PairBlock
open L3.CohortDomination
open L3.CohortIdentity
open L3.GhostBridge

section Generic

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- Port of `winInvDAtCycStart`: the window invariant at a cycle start (`lam = 0`) from the
layout, the frame order and `GhostCorrDistinct`. Consumer: `pairPinOfCycStart`. -/
theorem widthWinInvDAtCycStart (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop)
    (z : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : WidthCohortLayout ref root src R z.1) (hfo : AuditFrameOrder z.2)
    (hgd : GhostCorrDistinct ring root lane src R Base (piD (ref.phys z.1)) z.2) (j o : Nat)
    (hc : CohortCycIn R j (cohortProj ring root lane src R (piD (ref.phys z.1)))
      ((fun _ => 0), j) o)
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) :
    WidthWinInvD ref root lane src R Base z ((fun _ => 0), j) :=
  ⟨hz, hfo, hgd, ⟨o, hc⟩, chi, _, cycWinStart ring root lane src R z.2 hfo chi,
    chiAtomsStart ring root lane src R Base _ chi⟩

/-- Port of `useReachOfStart`: a `WidthPinReach` state at a cycle start with counter `0` has the
use track. Consumer: `pairPinOfCycStart`. -/
theorem widthUseReachOfStart (root : Fin n) (lane : DigitLane) (src R : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (h : WidthPinReach ref root lane src R w) (hfo : AuditFrameOrder w.1.2)
    (h0 : w.2.1 = fun _ => 0) (hc : w.2.2 = 0) :
    WidthUseReach ref root lane src R w := by
  refine ⟨h, ?_⟩
  obtain ⟨-, -, chi, -⟩ := h.2
  refine ⟨chi, w.1.2.clock, ?_, fun i hi hc' => ?_, fun i hi hc' => ?_, fun h1 => by omega⟩
  · rw [h0]
    exact cycWinStart ring root lane src R _ hfo chi
  · rw [h0] at hc'
    have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
    omega
  · rw [h0] at hc'
    have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
    omega

/-- A pinned cycle start of the writer pair at `src`: `lam = 0` with counter `0` is a cycle
witness (some old phase), and the chosen home cells carry samples read at their own cells.
Consumer: `pairPinOfCycStart`, `WidthCycStartAfterStrict`. -/
def WidthCycStartPinned (root : Fin n) (src : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  (∃ o, CohortCycIn (valueSpan n) 0
    (cohortProj ring root DigitLane.writer src (valueSpan n) (piD (ref.phys x.1)))
    ((fun _ => 0), 0) o) ∧
  ChosenInv (valueSpan n) (SPin ring root DigitLane.writer src x.2)
    (tracked ring root DigitLane.writer src (valueSpan n) x.2) (fun _ => 0)

end Generic

section Boundary

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)

/-- **The pin at a pinned cycle start**: with the run invariant of the pair, a pinned cycle start
carries `WidthPairPin` (ghost `(0, 0)`). Consumer: `pinAfterStrictOfCycStart`. -/
theorem pairPinOfCycStart (root : Fin n) (src : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hinv : WidthRunInv ring ref root DigitLane.writer src (valueSpan n) x)
    (hp : WidthCycStartPinned ref.toWidthDigitReference root src x)
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) :
    WidthPairPin ref.toWidthDigitReference root src x := by
  obtain ⟨⟨hlay, hfo, hfe, hval, hgd⟩, hpair⟩ := hinv
  obtain ⟨⟨o, hc⟩, hch⟩ := hp
  have hreach : WidthPinReach ref.toWidthDigitReference root DigitLane.writer src (valueSpan n)
      (x, ((fun _ => 0), 0)) := by
    refine ⟨⟨hfe, hval⟩, hch, fun q hq => absurd hq (Nat.not_lt_zero q), chi, x.2.clock,
      cycWinStart ring root DigitLane.writer src (valueSpan n) x.2 hfo chi,
      fun i hi hc' => ?_, fun h1 => ?_⟩
    · have hpos : cohortPos (valueSpan n) (fun _ => 0) i = valueSpan n - 1 - i := rfl
      dsimp only at hc'
      omega
    · dsimp only at h1
      omega
  exact ⟨hpair, ((fun _ => 0), 0),
    widthWinInvDAtCycStart ref.toWidthDigitReference root DigitLane.writer src (valueSpan n)
      (InheritedOk DigitLane.writer) x hlay hfo hgd 0 o hc chi,
    widthUseReachOfStart ref.toWidthDigitReference root DigitLane.writer src (valueSpan n) _
      hreach hfo rfl rfl⟩

include hn in
/-- `WidthPairPin` is carried by every word. Consumer: `pinAfterStrictOfCycStart`. -/
theorem pairPinFold (root : Fin n) (src : Nat) (hsrc : 2 ≤ src)
    (hend : src + 2 * valueSpan n < n) :
    ∀ (word : List (Fin n)) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      WidthPairPin ref.toWidthDigitReference root src x →
      WidthPairPin ref.toWidthDigitReference root src
        (word.foldl (widthDigitAuditNext ref.toWidthDigitReference) x) := by
  intro word
  induction word with
  | nil => intro x h; exact h
  | cons e rest ih =>
    intro x h
    exact ih _ (widthPairPinStep ref.toWidthDigitReference ref.singletonFixed hn root src hsrc
      hend x e h)

/-- **The reduced premise**: every strict completion of an interior writer pair on a first-zero
run is preceded, on the same run, by a state with the run invariant of the pair and a pinned
cycle start (the state right after the export of the strict cohort's tail sample). Consumer:
`pinAfterStrictOfCycStart`. -/
def WidthCycStartAfterStrict : Prop :=
  ∀ (root : Fin n) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    WidthZeroRun ref.toWidthDigitReference root x →
    ∀ (src : Nat) (tm : DigitTerminal (compileAdvice (ceilLogTwo n)) n),
      2 ≤ src → src + 2 * valueSpan n < n →
      DigitCompletion ring x.2 root src (src + valueSpan n) DigitLane.writer 0 tm →
      ∃ (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (word : List (Fin n)),
        word.foldl (widthDigitAuditNext ref.toWidthDigitReference) y = x ∧
        WidthRunInv ring ref root DigitLane.writer src (valueSpan n) y ∧
        WidthCycStartPinned ref.toWidthDigitReference root src y

include hn in
/-- **`WidthPinAfterStrict` from the reduced premise**: the pin at the earlier pinned cycle start
(`pairPinOfCycStart`), carried to the strict cut (`pairPinFold`). Consumer: `hpin` of
`l3HeadlineOfCleanBranches` (once `WidthCycStartAfterStrict` is proved). -/
theorem pinAfterStrictOfCycStart (h : WidthCycStartAfterStrict ref) :
    WidthPinAfterStrict ref.toWidthDigitReference := by
  intro root x hx src tm h2 hend hc
  obtain ⟨y, word, hyx, hinv, hp⟩ := h root x hx src tm h2 hend hc
  obtain ⟨-, -, -, -, -, -, hpos, -, -, exports, -⟩ := hc
  have hpin := pairPinFold ref hn root src h2 hend word y
    (pairPinOfCycStart ref root src y hinv hp (fun _ => exports ⟨0, hpos⟩))
  rw [hyx] at hpin
  exact hpin.2

end Boundary

end L3.StageMEntryPin

#print axioms L3.StageMEntryPin.widthWinInvDAtCycStart
#print axioms L3.StageMEntryPin.widthUseReachOfStart
#print axioms L3.StageMEntryPin.pairPinOfCycStart
#print axioms L3.StageMEntryPin.pairPinFold
#print axioms L3.StageMEntryPin.pinAfterStrictOfCycStart
