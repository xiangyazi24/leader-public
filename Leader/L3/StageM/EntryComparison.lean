import Leader.L3.StageM.EntryCyc
import Leader.L3.Width.DigitWriterValueCuts

/-!
# The pins of the comparison lane

`WidthPairPin` (WidthDigitCuts) is stated for `DigitLane.writer`, but every ingredient is
lane-parametric: `WidthWinInvD`, `WidthUseReach`, their steps `widthWinInvDStep`,
`widthUseReachStep`, the run invariant `WidthRunInv` from the clean start (`widthCleanRunStart`) and
the pinned cycle start after the tail export (`wCycStartOfCompletion`, any lane and any cut).  This
module instantiates the chain at an arbitrary lane:

* `WidthLanePairPin`: `WidthPairPin` at a lane (`widthLanePairPinWriter`: at `writer` it is
  `WidthPairPin`);
* `widthLanePairPinStep`, `lanePairPinFold`: carried by every word;
* `lanePairPinOfWord`: a recorded completion of a pair at any cut on a word from a clean start gives
  the pin at the end of the word;
* `comparisonPairPinOfCompletion`: the comparison-lane copy of `pairPinOfCompletion`, cut `restart`;
* `comparisonPinOfReady`: at a comparison-ready cut, every complete pair of the audit start has the
  comparison pin (from the first strict comparison completion after `restart`);
* `lanePinsOfCutData`: both lanes at the data of a writer comparison cut.
-/

namespace L3.StageMEntry

set_option autoImplicit false
set_option linter.unusedSectionVars false

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentCutEntry
open L3.WidthPacketMomentCompare
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
open L3.StageMEntryPin
open L3.StageMEntryRun
open L3.StageMEntryCyc

section Generic

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- `WidthPairPin` at a lane: the complete pair, a cycle ghost with the pinned window and the use
track.  Consumer: `comparisonPairPinOfCompletion`, `comparisonPinOfReady` and the translation of the
pin bundle to the `pairs` clause of the quiet class. -/
def WidthLanePairPin (root : Fin n) (lane : DigitLane) (src : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  PairIn ring root src (valueSpan n) x.2 ∧
  ∃ g : (Nat → Nat) × Nat,
    WidthWinInvD ref root lane src (valueSpan n) (InheritedOk lane) x g ∧
    WidthUseReach ref root lane src (valueSpan n) (x, g)

/-- At the writer lane `WidthLanePairPin` is `WidthPairPin`.  Consumer: the translation of the pin
bundle to the `pairs` clause, which treats both lanes alike. -/
theorem widthLanePairPinWriter (root : Fin n) (src : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    WidthLanePairPin ref root DigitLane.writer src x ↔ WidthPairPin ref root src x :=
  Iff.rfl

/-- Port of `widthPairPinStep` at a lane.  Consumer: `lanePairPinFold`. -/
theorem widthLanePairPinStep
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z)))
    (hn : 5 ≤ n) (root : Fin n) (lane : DigitLane) (src : Nat) (hsrc : 2 ≤ src)
    (hend : src + 2 * valueSpan n < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) (h : WidthLanePairPin ref root lane src x) :
    WidthLanePairPin ref root lane src (widthDigitAuditNext ref x e) := by
  have hR := valueSpanTwo hn
  obtain ⟨hp, g, hw, hu⟩ := h
  exact ⟨hp, widthWindowGhost ref root lane src (valueSpan n) x g e,
    (widthWinInvDStep ref hfix hn root lane src (valueSpan n) hR hsrc hend
      (InheritedOk lane) x g hw e).1,
    widthUseReachStep ref hfix hn root lane src (valueSpan n) hR hsrc hend
      (InheritedOk lane) (x, g) e hw hu⟩

end Generic

section Boundary

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)

/-- Port of `pairPinOfCycStart` at a lane: the run invariant of the pair and a pinned cycle start
carry the pin (ghost `(0, 0)`).  Consumer: `lanePairPinOfWord`. -/
theorem lanePairPinOfCycStart (root : Fin n) (lane : DigitLane) (src : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hinv : WidthRunInv ring ref root lane src (valueSpan n) x)
    (hc : ∃ o, CohortCycIn (valueSpan n) 0
      (cohortProj ring root lane src (valueSpan n) (piD (ref.phys x.1))) ((fun _ => 0), 0) o)
    (hch : ChosenInv (valueSpan n) (SPin ring root lane src x.2)
      (tracked ring root lane src (valueSpan n) x.2) (fun _ => 0))
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) :
    WidthLanePairPin ref.toWidthDigitReference root lane src x := by
  obtain ⟨⟨hlay, hfo, hfe, hval, hgd⟩, hpair⟩ := hinv
  obtain ⟨o, hc⟩ := hc
  have hreach : WidthPinReach ref.toWidthDigitReference root lane src (valueSpan n) (x, ((fun _ => 0), 0)) := by
    refine ⟨⟨hfe, hval⟩, hch, fun q hq => absurd hq (Nat.not_lt_zero q), chi, x.2.clock,
      cycWinStart ring root lane src (valueSpan n) x.2 hfo chi,
      fun i hi hc' => ?_, fun h1 => ?_⟩
    · have hpos : cohortPos (valueSpan n) (fun _ => 0) i = valueSpan n - 1 - i := rfl
      dsimp only at hc'
      omega
    · dsimp only at h1
      omega
  exact ⟨hpair, ((fun _ => 0), 0),
    widthWinInvDAtCycStart ref.toWidthDigitReference root lane src (valueSpan n) (InheritedOk lane) x hlay hfo hgd 0 o hc
      chi,
    widthUseReachOfStart ref.toWidthDigitReference root lane src (valueSpan n) _ hreach hfo rfl rfl⟩

include hn in
/-- **The pin of a lane is carried by every word.**  Consumer: `lanePairPinOfWord`; at the
comparison lane it transports the pin from the strict completion to later cuts. -/
theorem lanePairPinFold (root : Fin n) (lane : DigitLane) (src : Nat) (hsrc : 2 ≤ src)
    (hend : src + 2 * valueSpan n < n) :
    ∀ (word : List (Fin n)) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      WidthLanePairPin ref.toWidthDigitReference root lane src x →
      WidthLanePairPin ref.toWidthDigitReference root lane src
        (word.foldl (widthDigitAuditNext ref.toWidthDigitReference) x) := by
  intro word
  induction word with
  | nil => intro x h; exact h
  | cons e rest ih =>
    intro x h
    exact ih _ (widthLanePairPinStep ref.toWidthDigitReference ref.singletonFixed hn root lane src
      hsrc hend x e h)

include hn in
/-- **A recorded completion on a word from a clean start gives the pin at the end of the word**, at
any lane and any cut: `src` is aligned with the first delimiter of the start, so the start has the
run invariant (`widthCleanRunStart`); right after the tail export of the completion the state has a
pinned cycle start (`wCycStartOfCompletion`), and the pin is carried from there
(`lanePairPinFold`).  This is the proof of `cycStartAfterStrict` and `pinAfterStrictOfCycStart` at
a lane.  Consumer: `comparisonPairPinOfCompletion`. -/
theorem lanePairPinOfWord (root : Fin n)
    (lane : DigitLane) (start : ref.State) (hs : ref.start start) (word : List (Fin n))
    (hW : WFixedRoot ring root (piW (ref.phys (word.foldl ref.next start)))) (src cut : Nat)
    (tm : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hend : src + 2 * valueSpan n < n)
    (hcomp : DigitCompletion ring
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2 root src (src + valueSpan n) lane cut
      tm) :
    2 ≤ src ∧ WidthLanePairPin ref.toWidthDigitReference root lane src
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))) := by
  have hR := valueSpanTwo hn
  have hst : (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2.start = piD (ref.phys start) := by
    rw [widthFoldStart ring ref word]
    rfl
  obtain ⟨root0, hs0, hL⟩ := widthCleanBoundaryRoot ref start hs
  have hsw := widthSingletonFold ring ref root0 word start hs0
  have hfix := ref.singletonFixed root0 _ hsw
  have hr : root = root0 := hfix.2.1 root hW.1
  subst hr
  obtain ⟨first0, ht, -, hb⟩ := widthCleanBoundaryDelimiters ref hn root start hL
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  obtain ⟨⟨⟨⟨⟨h0, hlt, hbeta⟩, -⟩, -⟩, -⟩, -⟩ := id hcomp
  rw [hst] at hbeta
  obtain ⟨hfs, hmod⟩ := (hb src h0 hlt).1 hbeta
  have h2 : 2 ≤ src := by omega
  have hf : DigitFirstDelimiter ring root (piD (ref.phys start)) first0 := by
    refine ⟨⟨by omega, by omega, (hb first0 (by omega) (by omega)).2 ⟨Nat.le_refl _, by simp⟩⟩,
      fun k hk1 hk2 => ?_⟩
    cases hbk : (piD (ref.phys start) (digitSite ring root k)).word.beta with
    | false => rfl
    | true =>
      exfalso
      have := ((hb k hk1 (by omega)).1 hbk).1
      omega
  obtain ⟨i, hi⟩ : ∃ i, src = first0 + i * valueSpan n := by
    refine ⟨(src - first0) / valueSpan n, ?_⟩
    have h1 := Nat.div_add_mod (src - first0) (valueSpan n)
    rw [show (src - first0) % valueSpan n = 0 from hmod, Nat.add_zero, Nat.mul_comm] at h1
    rw [h1]
    omega
  have hend' : first0 + i * valueSpan n + 2 * valueSpan n < n := by
    rw [← hi]
    exact hend
  obtain ⟨-, hI⟩ := widthCleanRunStart ring ref hn root lane start hs word hW first0 hf i hend'
  have hq0 : WidthRunInv ring ref root lane src (valueSpan n)
      (start, digitAuditInitial (piD (ref.phys start))) := by
    rw [hi]
    exact hI
  have hxEnd : wRunAt ref.toWidthDigitReference (start, digitAuditInitial (piD (ref.phys start)))
      word word.length = word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start))) :=
    wRunAtLen ref.toWidthDigitReference _ _ _ (Nat.le_refl _)
  rw [← hxEnd] at hcomp
  obtain ⟨t, -, hcyc, hch⟩ := wCycStartOfCompletion ref hn root lane src (valueSpan n)
    hR h2 hend (start, digitAuditInitial (piD (ref.phys start))) hq0 rfl rfl word rfl cut
    tm hcomp
  obtain ⟨-, -, -, -, -, -, hpos, -, -, exports, -⟩ := hcomp
  have hpin := lanePairPinFold ref hn root lane src h2 hend (word.drop t) _
    (lanePairPinOfCycStart ref root lane src _
      (wInvAt ref hn root lane src (valueSpan n) hR h2 hend _ hq0 word t) ⟨0, hcyc⟩ hch
      (fun _ => exports ⟨0, hpos⟩))
  rw [wRunAtSplit ref.toWidthDigitReference word _ t] at hpin
  exact ⟨h2, hpin⟩

include hn in
/-- **The comparison-lane copy of `pairPinOfCompletion`**: a recorded comparison completion of an
interior pair after `restart`, on a word from a clean start ending at the root, gives the comparison
pin.  Consumer: `comparisonPinOfReady` and the comparison half of the `pairs` clause. -/
theorem comparisonPairPinOfCompletion (root : Fin n)
    (start : ref.State) (hs : ref.start start) (word : List (Fin n))
    (hW : WFixedRoot ring root (piW (ref.phys (word.foldl ref.next start)))) (src restart : Nat)
    (tm : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hend : src + 2 * valueSpan n < n)
    (hc : DigitCompletion ring
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2 root src (src + valueSpan n)
      DigitLane.comparison restart tm) :
    WidthLanePairPin ref.toWidthDigitReference root DigitLane.comparison src
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))) :=
  (lanePairPinOfWord ref hn root DigitLane.comparison start hs word hW src restart tm hend hc).2

include hn in
/-- **The comparison pins at a comparison-ready cut**: every complete pair of the audit start has
the comparison pin at the cut, from the first strict comparison completion after `restart` that
`DigitComparisonReady` carries.  Consumer: the comparison half of the `pairs` clause of
`WidthWriterQuietAtCut`. -/
theorem comparisonPinOfReady (root : Fin n)
    (start : ref.State) (hs : ref.start start) (word : List (Fin n))
    (hW : WFixedRoot ring root (piW (ref.phys (word.foldl ref.next start)))) (restart cut : Nat)
    (hready : DigitComparisonReady ring root
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2 restart cut)
    (source target : Nat)
    (hpair : DigitCompletePair ring root
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2.start source target) :
    2 ≤ source ∧ source + 2 * valueSpan n < n ∧
      WidthLanePairPin ref.toWidthDigitReference root DigitLane.comparison source
        (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))) := by
  obtain ⟨-, -, hall, -⟩ := hready
  obtain ⟨terminal, -, -, hfirst, -, -, -, -⟩ := hall source target hpair
  have htarget : target = source + valueSpan n := hpair.2.1
  subst htarget
  have hend : source + 2 * valueSpan n < n := by
    have h := hpair.2.2.2
    have hv : digitSpan (compileAdvice (ceilLogTwo n)) = valueSpan n := rfl
    rw [hv] at h
    omega
  obtain ⟨h2, hpin⟩ := lanePairPinOfWord ref hn root DigitLane.comparison start hs word hW
    source restart terminal hend hfirst.1
  exact ⟨h2, hend, hpin⟩

include hn in
/-- **The pins of both lanes at a writer comparison cut, from the data of the cut**: on a run from
a clean start ending at the fixed root, the first strict writer completion of the structural cut
(cut `0`) gives the writer pin and the first strict comparison completion of the comparison-ready
cut (after `restart`) gives the comparison pin, for every complete pair of the audit start.
Consumer: the `pairs` clause of `WidthWriterQuietAtCut`. -/
theorem lanePinsOfCutData (root : Fin n)
    (start : ref.State) (hs : ref.start start) (word : List (Fin n))
    (z : ref.State) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hrun : word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start))) = (z, audit))
    (hfixed : WFixedRoot ring root (piW (ref.phys z)))
    (structural restart cut : Nat)
    (hstruct : DigitFirstCut (L3.WriterValueCuts.DigitWriterStructuralAt ring root audit) structural)
    (hready : DigitComparisonReady ring root audit restart cut)
    (lane : DigitLane) (source target : Nat)
    (hpair : DigitCompletePair ring root audit.start source target) :
    2 ≤ source ∧ source + 2 * valueSpan n < n ∧
      WidthLanePairPin ref.toWidthDigitReference root lane source (z, audit) := by
  have hzw : word.foldl ref.next start = z := by
    have h1 := widthAuditFoldFst ref.toWidthDigitReference word
      (start, digitAuditInitial (piD (ref.phys start)))
    rw [hrun] at h1
    exact h1.symm
  have hW : WFixedRoot ring root (piW (ref.phys (word.foldl ref.next start))) := by
    rw [hzw]
    exact hfixed
  have htarget : target = source + valueSpan n := hpair.2.1
  subst htarget
  have hend : source + 2 * valueSpan n < n := by
    have h := hpair.2.2.2
    have hv : digitSpan (compileAdvice (ceilLogTwo n)) = valueSpan n := rfl
    rw [hv] at h
    omega
  obtain ⟨tm, cut', hcomp⟩ : ∃ (tm : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (cut' : Nat),
      DigitCompletion ring audit root source (source + valueSpan n) lane cut' tm := by
    cases lane with
    | writer =>
        obtain ⟨tm, hfirst, -⟩ := hstruct.1.2 source _ hpair
        exact ⟨tm, 0, hfirst.1⟩
    | comparison =>
        obtain ⟨-, -, hall, -⟩ := hready
        obtain ⟨tm, -, -, hfirst, -, -, -, -⟩ := hall source _ hpair
        exact ⟨tm, restart, hfirst.1⟩
  have := lanePairPinOfWord ref hn root lane start hs word hW source cut' tm hend
    (by rw [hrun]; exact hcomp)
  rw [hrun] at this
  exact ⟨this.1, hend, this.2⟩

end Boundary

end L3.StageMEntry

#print axioms L3.StageMEntry.lanePairPinOfCycStart
#print axioms L3.StageMEntry.widthLanePairPinStep
#print axioms L3.StageMEntry.lanePairPinFold
#print axioms L3.StageMEntry.lanePairPinOfWord
#print axioms L3.StageMEntry.comparisonPairPinOfCompletion
#print axioms L3.StageMEntry.comparisonPinOfReady
#print axioms L3.StageMEntry.lanePinsOfCutData
