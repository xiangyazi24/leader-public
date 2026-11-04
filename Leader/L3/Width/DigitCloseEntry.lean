import Leader.L3.Width.DigitCloseCurrent

/-!
# The entry fact of clause (C): routine parts

`L3.CloseCurrent.CurrentEntry` asks, at the terminal state of a pair's first strict comparison
completion after `restart` on the clean run, for the pair's window class `PairWin … restart`.
This module proves its routine parts on every clean-run state and reduces `CurrentEntry` to the
new content `EntryCore`:

* `pairLayoutStart`: a complete pair of the clean start has the cohort layout there;
* `pairBaseRun`: along every clean-run word, the layout, the ghost correspondence with the
  inherited base and the value invariant of the pair;
* `restartLtTerminal`: a completion after `restart` terminates after `restart`;
* `EntryCore` (the remaining hypothesis): at that terminal state the masked comparison lane is in
  the cycle class and the aged window `WinAge restart` holds (model check: close-mc.py
  `cyc_entry`, `C_entry`);
* `currentEntryOfCore`: `CurrentEntry` from `EntryCore`.
-/

namespace L3.CloseEntry

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.ValueWaveClose
open L3.CohortDomination
open L3.CohortSites
open L3.Rearm
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortLedger
open L3.ValueLedger
open L3.CurrentWin
open L3.CloseCurrent
open L3.WidthWave

variable {n : Nat} {ring : DirectedRing n}

/-- **The layout of a complete pair at the clean start** (delimiters `first + j R`).  Consumer:
`pairBaseRun`. -/
theorem pairLayoutStart (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (start : ref.State)
    (hL : WidthBoundaryDigitLayoutValues ref root start) (source : Nat)
    (hpair : DigitCompletePair ring root (piD (ref.phys start)) source
      (source + digitSpan (compileAdvice (ceilLogTwo n)))) :
    2 ≤ source ∧ source + 2 * digitSpan (compileAdvice (ceilLogTwo n)) < n ∧
      WidthCohortLayout ref.toWidthDigitReference root source
        (digitSpan (compileAdvice (ceilLogTwo n))) start := by
  obtain ⟨first, ht, -, hb⟩ := widthCleanBoundaryDelimiters ref hn root start hL
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hR := valueSpanTwo hn
  have hRd : digitSpan (compileAdvice (ceilLogTwo n)) = valueSpan n := rfl
  obtain ⟨⟨⟨hs0, hsn, hsb⟩, -, -, -, -⟩, -⟩ := hpair.1
  have hend2 := hpair.2.2.2
  obtain ⟨hfs, hmod⟩ := (hb source hs0 hsn).1 hsb
  rw [hRd] at hb hmod hend2 ⊢
  generalize valueSpan n = R at hR hb hmod hend2 ⊢
  generalize hm : source - first = m at hmod
  have hsrc : source = first + m := by omega
  subst hsrc
  have hm1 : (m + R) % R = 0 := by rw [Nat.add_mod_right]; exact hmod
  have hm2 : (m + 2 * R) % R = 0 := by
    rw [show m + 2 * R = m + R + R by omega, Nat.add_mod_right, Nat.add_mod_right]; exact hmod
  refine ⟨by omega, by omega, hL.1, ?_, ?_, ?_, fun k hk0 hk2 hkR => ?_⟩
  · exact (hb _ (by omega) (by omega)).2
      ⟨by omega, by rw [show first + m - first = m by omega]; exact hmod⟩
  · exact (hb _ (by omega) (by omega)).2
      ⟨by omega, by rw [show first + m + R - first = m + R by omega]; exact hm1⟩
  · exact (hb _ (by omega) (by omega)).2
      ⟨by omega, by rw [show first + m + 2 * R - first = m + 2 * R by omega]; exact hm2⟩
  · cases hbeta : (piD (ref.phys start) (digitSite ring root (first + m + k))).word.beta with
    | false => rfl
    | true =>
      exfalso
      have h := ((hb _ (by omega) (by omega)).1 hbeta).2
      rw [show first + m + k - first = m + k by omega, Nat.add_mod, hmod, Nat.zero_add,
        Nat.mod_mod] at h
      by_cases hk : k < R
      · rw [Nat.mod_eq_of_lt hk] at h
        omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
        omega

/-- The routine part of the window class: layout, correspondence with the inherited base, value
invariant.  Consumer: `pairBaseRun`, `currentEntryOfCore`. -/
def PairBase (ref : WidthDigitReference ring) (root : Fin n) (src R : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthCohortLayout ref root src R y.1 ∧
  GhostCorrDistinct ring root DigitLane.comparison src R (InheritedOk DigitLane.comparison)
    (piD (ref.phys y.1)) y.2 ∧
  WidthValInv ref root DigitLane.comparison src R y

/-- **The routine part on every clean-run state** of a complete pair of the start.  Consumer:
`currentEntryOfCore`. -/
theorem pairBaseRun (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (start : ref.State)
    (hL : WidthBoundaryDigitLayoutValues ref root start) (source : Nat)
    (hpair : DigitCompletePair ring root (piD (ref.phys start)) source
      (source + digitSpan (compileAdvice (ceilLogTwo n)))) (u : List (Fin n)) :
    PairBase ref.toWidthDigitReference root source (digitSpan (compileAdvice (ceilLogTwo n)))
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))) := by
  obtain ⟨hsrc, hend, hlay⟩ := pairLayoutStart ref hn root start hL source hpair
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  have h0 : PairBase ref.toWidthDigitReference root source
      (digitSpan (compileAdvice (ceilLogTwo n))) (start, digitAuditInitial (piD (ref.phys start))) :=
    ⟨hlay, ghostCorrDistinctInitial ring root _ _ _ _,
      ⟨valCorrInitial ring root _ _ _ _, exportValInitial ring root _ _ _ _,
        useValInitial ring root _ _ _ _, ledgerOkInitial ring root _ _ _ _⟩⟩
  generalize (start, digitAuditInitial (piD (ref.phys start))) = y at h0
  induction u generalizing y with
  | nil => exact h0
  | cons e rest ih =>
    apply ih
    obtain ⟨hl, hg, hv⟩ := h0
    obtain ⟨hl', hg'⟩ := widthGhostCorrDistinctStep ref.toWidthDigitReference ref.singletonFixed hn
      root DigitLane.comparison source _ hR hsrc hend (InheritedOk DigitLane.comparison) y hl hg e
    exact ⟨hl', hg', widthValInvStep ref.toWidthDigitReference ref.singletonFixed hn root
      DigitLane.comparison source _ hR hsrc hend y hl hv e⟩

/-- A completion after `cut` terminates after `cut`.  Consumer: `currentEntryOfCore`. -/
theorem restartLtTerminal {c : Compiled} (A : DigitAudit c n) (root : Fin n) (source target : Nat)
    (lane : DigitLane) (cut : Nat) (T : DigitTerminal c n)
    (h : DigitCompletion ring A root source target lane cut T) : cut < T.time := by
  obtain ⟨-, -, -, -, -, -, pos, ledger, samples, exports, uses, -, -, -, hj, -, -⟩ := h
  obtain ⟨-, -, -, hc, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, h3⟩ := hj ⟨0, pos⟩
  omega

/-- **The new content of the entry fact**: at the terminal state of a complete pair's first strict
comparison completion after `restart` on the clean run, the masked comparison lane is in the
cycle class and the aged window holds at `restart`.  Model check: close-mc.py `cyc_entry` and
`C_entry` (R ≤ 3, arbitrary scratch).  Consumer: `currentEntryOfCore`. -/
def EntryCore (ref : WidthDigitReference ring) : Prop :=
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
    (∃ (j : Nat) (g : (Nat → Nat) × Nat) (o : Nat),
      CohortCycIn (digitSpan (compileAdvice (ceilLogTwo n))) j
        (cohortProj ring root DigitLane.comparison source (digitSpan (compileAdvice (ceilLogTwo n)))
          (piD (ref.phys (u.foldl (widthDigitAuditNext ref)
            (start, digitAuditInitial (piD (ref.phys start)))).1))) g o) ∧
    WinAge ring root DigitLane.comparison source (digitSpan (compileAdvice (ceilLogTwo n))) restart
      (cohortProj ring root DigitLane.comparison source (digitSpan (compileAdvice (ceilLogTwo n)))
        (piD (ref.phys (u.foldl (widthDigitAuditNext ref)
          (start, digitAuditInitial (piD (ref.phys start)))).1)))
      (u.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2

/-- **`CurrentEntry` from its new content** (any boundary reference).  Consumer:
`L3.CloseCurrent.widthComparisonCloseOfEntry`. -/
theorem currentEntryOfCore (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hcore : EntryCore ref.toWidthDigitReference) :
    CurrentEntry ref.toWidthDigitReference := by
  intro root restart start u source T hst hs hpair hT hTc
  obtain ⟨root0, hs0, hL⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root0 :=
    (ref.singletonFixed root0 start hs0).2.1 root (ref.singletonFixed root start hs).1
  subst hr
  obtain ⟨hl, hg, hv⟩ := pairBaseRun ref hn root start hL source hpair u
  obtain ⟨hcyc, hage⟩ := hcore root restart start u source T hst hs hpair hT hTc
  have hlt := restartLtTerminal _ root source _ DigitLane.comparison restart T hT.1
  exact ⟨hl, hg, hv, hcyc, hage, by rw [← hTc]; exact Nat.le_of_lt hlt⟩

end L3.CloseEntry

#print axioms L3.CloseEntry.pairLayoutStart
#print axioms L3.CloseEntry.pairBaseRun
#print axioms L3.CloseEntry.restartLtTerminal
#print axioms L3.CloseEntry.currentEntryOfCore
