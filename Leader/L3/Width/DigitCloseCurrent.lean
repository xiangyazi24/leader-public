import Leader.L3.Bank.RepairDigitCurrentWin
import Leader.L3.Width.DigitCloseBoundary

/-!
# Clause (C) of the comparison close on the clean run

`L3.CloseBoundary.widthComparisonCloseOfClauses` reduces `WidthComparisonClose` to clause (R)
and clause (C): comparison currentness of every complete pair at the clock of the continuation.
This module proves (C) from one entry fact per pair.

* `PairWin ref root src R cut y`: at the coupled state `y`, the pair's layout, the ghost
  correspondence with the inherited base, the value invariant, the cycle class `CohortCycIn` of
  the masked comparison lane, and the aged window `L3.CurrentWin.WinAge … cut`.
* `pairWinStep`, `pairWinRun`: `PairWin` is carried by every letter (the cycle class by
  `cohortCycStep`, the aged window by `L3.CurrentWin.winAgeStep`).
* `CurrentEntry ref` (the entry fact, a hypothesis here): on the clean run from a start, at the
  terminal letter of a pair's first strict comparison completion after `restart`, `PairWin` holds
  with cut `restart`.  Model check: research/lean-l3/ledgers/close-mc.py, clauses `cyc_entry` and
  `C_entry` (R ≤ 3, arbitrary scratch).
* `comparisonsCurrentOfEntry`: clause (C) at the clock of every continuation of a values-stable
  state at which every pair is done; `widthComparisonCloseOfEntry`: `WidthComparisonClose` from
  clause (R) and the entry fact.
-/

namespace L3.CloseCurrent

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.ValueWaveClose
open L3.WriterValueCuts
open L3.CompareStage
open L3.CohortDomination
open L3.CohortSites
open L3.Rearm
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CurrentWin
open L3.ClosePersist
open L3.CloseBoundary
open L3.WidthWave

variable {n : Nat} {ring : DirectedRing n}

/-- Inherited atoms are not samples.  Consumer: `pairWinStep`, `comparisonsCurrentOfEntry`. -/
theorem inheritedNoSample (lane : DigitLane) :
    ∀ T (id : DigitStamp n), ¬ InheritedOk lane T (DigitAtom.sampled id) := by
  rintro T id ⟨site, slot, h⟩
  cases h

/-- **The window class of one pair at `cut`** on the comparison lane: layout, correspondence
with the inherited base, value invariant, cycle class and aged window, with `cut` no later than
the clock.  Consumer: `pairWinStep`, `CurrentEntry`, `comparisonsCurrentOfEntry`. -/
def PairWin (ref : WidthDigitReference ring) (root : Fin n) (src R cut : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthCohortLayout ref root src R y.1 ∧
  GhostCorrDistinct ring root DigitLane.comparison src R (InheritedOk DigitLane.comparison)
    (piD (ref.phys y.1)) y.2 ∧
  WidthValInv ref root DigitLane.comparison src R y ∧
  (∃ (j : Nat) (g : (Nat → Nat) × Nat) (o : Nat),
    CohortCycIn R j (cohortProj ring root DigitLane.comparison src R (piD (ref.phys y.1))) g o) ∧
  WinAge ring root DigitLane.comparison src R cut
    (cohortProj ring root DigitLane.comparison src R (piD (ref.phys y.1))) y.2 ∧
  cut ≤ y.2.clock

/-- **`PairWin` is carried by every letter.**  Consumer: `pairWinRun`. -/
theorem pairWinStep (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
    (root : Fin n) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (cut : Nat) (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : PairWin ref root src R cut y) :
    PairWin ref root src R cut (widthDigitAuditNext ref y e) := by
  obtain ⟨hlay, hgc, hval, ⟨jj, g, o, hcyc⟩, hage, hcut⟩ := h
  obtain ⟨hlay', hgc'⟩ := widthGhostCorrDistinctStep ref hfix hn root DigitLane.comparison src R
    hR hsrc hend (InheritedOk DigitLane.comparison) y hlay hgc e
  have hval' := widthValInvStep ref hfix hn root DigitLane.comparison src R hR hsrc hend y hlay
    hval e
  have hproj := (widthCohortStep ref hfix hn root DigitLane.comparison src R hR hsrc hend y.1
    hlay e).2
  refine ⟨hlay', hgc', hval', ?_, ?_, ?_⟩
  · show ∃ (j : Nat) (g : (Nat → Nat) × Nat) (o : Nat), CohortCycIn R j
      (cohortProj ring root DigitLane.comparison src R (piD (ref.phys (ref.next y.1 e)))) g o
    rw [hproj]
    rcases cohortCycStep hcyc (cohortEdgeOf root src R e) with ⟨o', -, h', -⟩ | h'
    · exact ⟨jj, _, o', h'⟩
    · exact ⟨jj + 1, _, 0, h'⟩
  · obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay
    obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref hfix hn root y.1 hL e
    show WinAge ring root DigitLane.comparison src R cut
      (cohortProj ring root DigitLane.comparison src R (piD (ref.phys (ref.next y.1 e))))
      (digitAuditStep ring (piD (ref.phys y.1)) y.2 e)
    rw [heq]
    obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
    exact winAgeStep ring (by omega) root (piD (ref.phys y.1)) R src hR hsrc hend hroot hb0 hbR
      hb2R hbF DigitLane.comparison (InheritedOk DigitLane.comparison)
      (inheritedNoSample DigitLane.comparison) y.2 j hj hbX hbY cut hcut hgc hcyc hage
  · show cut ≤ y.2.clock + 1
    omega

/-- `PairWin` along every word.  Consumer: `comparisonsCurrentOfEntry`. -/
theorem pairWinRun (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
    (root : Fin n) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (cut : Nat) (word : List (Fin n)) :
    ∀ y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      PairWin ref root src R cut y →
      PairWin ref root src R cut (word.foldl (widthDigitAuditNext ref) y) := by
  induction word with
  | nil => intro y h; exact h
  | cons e rest ih =>
    intro y h
    exact ih _ (pairWinStep ref hfix hn root src R hR hsrc hend cut y e h)

/-- A first strict completion of the end of a run whose terminal is no later than an earlier
clock is a first strict completion there.  Consumer: `comparisonsCurrentOfEntry`. -/
theorem firstStrictFoldBack (ref : WidthDigitReference ring) (root : Fin n) (source target : Nat)
    (lane : DigitLane) (cut : Nat) (T : DigitTerminal (compileAdvice (ceilLogTwo n)) n) :
    ∀ (word : List (Fin n)) (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      DigitFirstStrictCompletion ring (word.foldl (widthDigitAuditNext ref) y).2 root source
        target lane cut T →
      T.time ≤ y.2.clock →
      DigitFirstStrictCompletion ring y.2 root source target lane cut T := by
  intro word
  induction word with
  | nil => intro y h _; exact h
  | cons e rest ih =>
    intro y h ht
    have h1 := ih (widthDigitAuditNext ref y e) h (by show T.time ≤ y.2.clock + 1; omega)
    exact firstStrictBack ring (piD (ref.phys y.1)) y.2 e root source target lane cut T h1 ht

/-- **The entry fact of clause (C)**: on the clean run from a start with singleton root `root`, at
the terminal letter of a complete pair's first strict comparison completion after `restart`, the
pair's window class holds with cut `restart`.  This is the first missing fact of clause (C)
(the earlier "generated-class entry at the actual terminal frame", here at the first strict
post-restart terminal).  Consumer: `comparisonsCurrentOfEntry`, `widthComparisonCloseOfEntry`. -/
def CurrentEntry (ref : WidthDigitReference ring) : Prop :=
  ∀ (root : Fin n) (restart : Nat) (start : ref.State) (u : List (Fin n)) (source : Nat)
    (T : DigitTerminal (compileAdvice (ceilLogTwo n)) n),
    ref.start start → ref.singleton root start →
    DigitCompletePair ring root (piD (ref.phys start)) source
      (source + digitSpan (compileAdvice (ceilLogTwo n))) →
    DigitFirstStrictCompletion ring
      (u.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2
      root source (source + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.comparison
      restart T →
    T.time =
      (u.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2.clock →
    PairWin ref root source (digitSpan (compileAdvice (ceilLogTwo n))) restart
      (u.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start))))

/-- **Clause (C) from the entry fact**: on every continuation of a values-stable state at which
every complete pair has its comparison completion after `restart`, every complete pair is
comparison-current at the clock.  Consumer: `widthComparisonCloseOfEntry`. -/
theorem comparisonsCurrentOfEntry (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hE : CurrentEntry ref.toWidthDigitReference) (root : Fin n) (restart : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (w : List (Fin n))
    (hx : WidthStableRun ref.toWidthDigitReference root restart x)
    (hdone : ∀ i, WidthComparePairDone ref.toWidthDigitReference root restart i
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x)) :
    DigitComparisonsCurrent ring root
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2
      (piD (ref.phys (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).1))
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2.current restart
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2.clock := by
  intro source target hpair
  obtain ⟨T, hT⟩ := pairsFirstStrictOfDone ref hn root restart x w hx hdone source target hpair
  obtain ⟨start, word, retired, hst, hfold, hW, -, -, -⟩ := hx
  obtain ⟨root0, hs, hL⟩ := widthCleanBoundaryRoot ref start hst
  have hx1 : x.1 = word.foldl ref.next start := by
    have := widthBoundaryDigitBoundaryAuditFirst ref start
      (digitAuditInitial (piD (ref.phys start))) word
    rw [hfold] at this
    exact this
  rw [hx1] at hW
  have hr : root = root0 :=
    (widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root0 start hs word).2.1 root hW.1
  subst hr
  let init : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n :=
    (start, digitAuditInitial (piD (ref.phys start)))
  have hy : (word ++ w).foldl (widthDigitAuditNext ref.toWidthDigitReference) init =
      w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x := by
    rw [List.foldl_append, hfold]
  generalize hyv : w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x = y at hT hpair hy ⊢
  have hstart : y.2.start = piD (ref.phys start) := by
    rw [← hy, L3.WriterReceipts.widthAuditStartFold]
    rfl
  have hclk : y.2.clock = (word ++ w).length := by
    rw [← hy, clockFold]
    show 0 + (word ++ w).length = _
    omega
  rw [hstart] at hpair
  have hR := valueSpanTwo hn
  have hRd : digitSpan (compileAdvice (ceilLogTwo n)) = valueSpan n := rfl
  obtain ⟨first, ht, -, hb⟩ := widthCleanBoundaryDelimiters ref hn root start hL
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  obtain ⟨⟨⟨hs0, hsn, hsb⟩, -, -, -, -⟩, -⟩ := hpair.1
  obtain ⟨hfs, -⟩ := (hb source hs0 hsn).1 hsb
  have htg := hpair.2.1
  have hend2 := hpair.2.2.2
  rw [htg] at hT hpair ⊢
  have hTle : T.time ≤ y.2.clock := completionTimeLe ring y.2 hT.1
  let u := word ++ w
  have hsplit : u = u.take T.time ++ u.drop T.time := (List.take_append_drop T.time u).symm
  let y0 := (u.take T.time).foldl (widthDigitAuditNext ref.toWidthDigitReference) init
  have hy0 : (u.drop T.time).foldl (widthDigitAuditNext ref.toWidthDigitReference) y0 = y := by
    show (u.drop T.time).foldl _ ((u.take T.time).foldl _ init) = y
    rw [← List.foldl_append, ← hsplit]
    exact hy
  have hclk0 : y0.2.clock = T.time := by
    show ((u.take T.time).foldl _ init).2.clock = T.time
    rw [clockFold, List.length_take]
    show 0 + min T.time u.length = T.time
    have : T.time ≤ u.length := by rw [← hclk]; exact hTle
    omega
  have hT0 : DigitFirstStrictCompletion ring y0.2 root source
      (source + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.comparison restart T := by
    rw [← hy0] at hT
    exact firstStrictFoldBack ref.toWidthDigitReference root source _ DigitLane.comparison
      restart T (u.drop T.time) y0 hT (Nat.le_of_eq hclk0.symm)
  have hpw0 := hE root restart start (u.take T.time) source T hst hs hpair hT0 hclk0.symm
  have hpw := pairWinRun ref.toWidthDigitReference ref.singletonFixed hn root source
    (digitSpan (compileAdvice (ceilLogTwo n))) (by rw [hRd]; exact hR) (by omega)
    (by rw [hRd] at hend2 ⊢; omega) restart (u.drop T.time) y0 hpw0
  rw [hy0] at hpw
  obtain ⟨-, hgc, hval, ⟨jj, g, o, hcyc⟩, hage, -⟩ := hpw
  exact pairCurrentOfAge ring root DigitLane.comparison source
    (digitSpan (compileAdvice (ceilLogTwo n))) rfl (InheritedOk DigitLane.comparison)
    (inheritedNoSample DigitLane.comparison) (piD (ref.phys y.1)) y.2 restart hgc hval.1
    hval.2.2.1 hcyc hage

/-- **`WidthComparisonClose` from clause (R) and the entry fact of clause (C)** (any boundary
reference).  Consumer: the BANK premise of
`L3.PacketMomentCompareBank.hcompareBankOfStage` and the SMALL premise `hcmpCloseSmall` of
`l3HeadlineOfCleanBranches`, once (R) and `CurrentEntry` are produced. -/
theorem widthComparisonCloseOfEntry (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hR : ∀ (root : Fin n) (restart : Nat)
      (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (w : List (Fin n)),
      WidthStableRun ref.toWidthDigitReference root restart x →
      (∀ i, WidthComparePairDone ref.toWidthDigitReference root restart i
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x)) →
      ∀ source target : Nat,
        DigitCompletePair ring root
          (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2.start source target →
        ∀ terminal, DigitFirstStrictCompletion ring
          (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2 root source target
          .comparison restart terminal →
        ∃ (anchor : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (anchorTail : DigitStamp n),
          DigitAnchor ring (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2 root
            source target .comparison anchor anchorTail ∧
          DigitTerminalRanked (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2
            .comparison (digitSite ring root source) anchor anchorTail terminal)
    (hE : CurrentEntry ref.toWidthDigitReference) :
    WidthComparisonClose ref.toWidthDigitReference :=
  widthComparisonCloseOfClauses ref hn hR
    (fun root restart x w hx hdone => comparisonsCurrentOfEntry ref hn hE root restart x w hx
      hdone)

end L3.CloseCurrent

#print axioms L3.CloseCurrent.pairWinStep
#print axioms L3.CloseCurrent.pairWinRun
#print axioms L3.CloseCurrent.firstStrictFoldBack
#print axioms L3.CloseCurrent.comparisonsCurrentOfEntry
#print axioms L3.CloseCurrent.widthComparisonCloseOfEntry
