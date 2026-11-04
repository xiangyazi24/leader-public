import Leader.L3.Width.DigitClosePersist

/-!
# Clause (B) of the comparison close and the ready cut at the current clock

`DigitComparisonReady … restart cut` (Target.lean) asks, at one cut, for the boundary receipt of
the state at the cut (clause (B)), for every complete pair a first strict comparison completion
after `restart` with an anchor and a ranked terminal (clause (R)), and comparison currentness of
all complete pairs (clause (C)).  This module, for any `WidthBoundaryReference`:

* `stableRunFacts`: on every continuation of a values-stable state, the clean start, its layout,
  the audit start, the layout-fixed class, the audit at the current state and the clock;
* `pairsFirstStrictOfDone`: if every complete pair of the first delimiter has a comparison
  completion after `restart` (`WidthComparePairDone`), every complete pair of the audit start has a
  first strict comparison completion after `restart` (delimiters `first + j R`,
  `widthCleanBoundaryDelimiters`);
* `readyAtClock`: the ready cut at the current clock: (B) from the leader receipt that
  `WidthStableRun` carries (DESIGN-MOTIVATIONS 2026-11-02 08:45) and `L3.CloseKeep.boundaryWord`,
  (R) for the first strict comparison terminals, and (C) at the current state;
* `widthComparisonCloseOfClauses`: `WidthComparisonClose` from (R) and (C)
  (`L3.ClosePersist.comparisonCutOfReady` at the cut `clock`).
-/

namespace L3.CloseBoundary

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.ValueWaveClose
open L3.WriterValueCuts
open L3.CompareStage
open L3.DigitCohortScratch
open L3.DigitPairsClean
open L3.ClosePersist

variable {n : Nat} {ring : DirectedRing n}

/-- The audit clock grows by the word length.  Consumer: `stableRunFacts`. -/
theorem clockFold (ref : WidthDigitReference ring) :
    ∀ (w : List (Fin n)) (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      (w.foldl (widthDigitAuditNext ref) q).2.clock = q.2.clock + w.length := by
  intro w
  induction w with
  | nil => intro q; rfl
  | cons e rest ih =>
    intro q
    rw [List.foldl_cons, ih, List.length_cons]
    show q.2.clock + 1 + rest.length = q.2.clock + (rest.length + 1)
    omega

/-- **The clean run facts on every continuation of a values-stable state**: the clean start with
its layout at the root, the audit start, the layout-fixed class at the values-stable state and at
the continuation, the audit at the continuation's state and the clock.  Consumer:
`pairsFirstStrictOfDone`, `readyAtClock`. -/
theorem stableRunFacts (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n)
    (restart : Nat) (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthStableRun ref.toWidthDigitReference root restart x) (w : List (Fin n)) :
    ∃ start : ref.State,
      ref.start start ∧ WidthBoundaryDigitLayoutValues ref root start ∧
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2.start =
        piD (ref.phys start) ∧
      WidthDigitLayoutFixed ref.toWidthDigitReference root x.1 ∧
      DigitAt ring (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2.clock
        (piD (ref.phys (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).1))
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2.current ∧
      x.2.clock ≤ (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2.clock := by
  obtain ⟨start, word, retired, hst, hfold, hW, -, -⟩ := hx
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
  have hy : (word ++ w).foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start))) =
      w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x := by
    rw [List.foldl_append, hfold]
  have hinv := widthBoundaryDigitBoundaryAuditInvariantRun ref hn root start hs (word ++ w)
  rw [hy] at hinv
  have hs0 := L3.WriterReceipts.widthAuditStartFold ref.toWidthDigitReference word
    (start, digitAuditInitial (piD (ref.phys start)))
  rw [hfold] at hs0
  have hs1 := L3.WriterReceipts.widthAuditStartFold ref.toWidthDigitReference w x
  have hc := clockFold ref.toWidthDigitReference w x
  refine ⟨start, hst, hL, by rw [hs1, hs0]; rfl, ?_, hinv.2.1, by omega⟩
  rw [hx1]
  exact (widthBoundaryDigitLayoutValuesWord ref root word start hL).1

/-- **Every complete pair has a first strict comparison completion after the restart** once
every complete pair of the first delimiter has a comparison completion after it (the delimiters of
the clean start are `first + j R`).  Consumer: `readyAtClock`. -/
theorem pairsFirstStrictOfDone (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (restart : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (w : List (Fin n))
    (hx : WidthStableRun ref.toWidthDigitReference root restart x)
    (hdone : ∀ i, WidthComparePairDone ref.toWidthDigitReference root restart i
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x)) :
    ∀ source target : Nat,
      DigitCompletePair ring root
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2.start source target →
      ∃ terminal, DigitFirstStrictCompletion ring
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2 root source target
        .comparison restart terminal := by
  obtain ⟨start, -, hL, hstart, -⟩ := stableRunFacts ref hn root restart x hx w
  obtain ⟨first, ht, -, hb⟩ := widthCleanBoundaryDelimiters ref hn root start hL
  rw [← hstart] at hb
  generalize w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x = y at hdone hb ⊢
  intro source target hpair
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hR := valueSpanTwo hn
  obtain ⟨⟨⟨hs0, hsn, hsb⟩, -, -, -, -⟩, -⟩ := hpair.1
  obtain ⟨hfs, hmod⟩ := (hb source hs0 hsn).1 hsb
  have htg := hpair.2.1
  have hend2 := hpair.2.2.2
  have hfd : DigitFirstDelimiter ring root y.2.start first :=
    firstDelimOf ring root y.2.start first hb (by omega) (by omega)
  generalize hRv : valueSpan n = R at hR
  have hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R := hRv
  rw [hRd] at hmod htg hend2
  have hsrc : source = first + (source - first) / R * R := by
    have := Nat.div_add_mod (source - first) R
    rw [hmod, Nat.add_zero, Nat.mul_comm] at this
    omega
  generalize (source - first) / R = i at hsrc
  obtain ⟨tm, htm⟩ := hdone i first hfd (by rw [hRv]; omega)
  rw [hRv, ← hsrc] at htm
  rw [htg]
  exact firstStrictOfCompletion ring y.2 root source (source + R) .comparison restart ⟨tm, htm⟩

/-- **The comparison-ready cut at the current clock** of a continuation `y` of a values-stable
state `x` at which every complete pair has its comparison completion after `restart`, from
(B) the leader receipt carried by `x` (persisting along `y`), (R) an anchor and a ranked terminal for every first strict
comparison terminal after `restart`, and (C) comparison currentness of the state of `y` at the
clock.  Consumer: `widthComparisonCloseOfClauses`. -/
theorem readyAtClock (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (restart : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (w : List (Fin n))
    (hx : WidthStableRun ref.toWidthDigitReference root restart x)
    (hdone : ∀ i, WidthComparePairDone ref.toWidthDigitReference root restart i
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x))
    (hR : ∀ source target : Nat,
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
    (hC : DigitComparisonsCurrent ring root
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2
      (piD (ref.phys (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).1))
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2.current restart
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2.clock) :
    DigitComparisonReady ring root (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2
      restart (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2.clock := by
  obtain ⟨start, -, -, -, hfx, hat, hclk⟩ := stableRunFacts ref hn root restart x hx w
  have hB : DigitBoundaryReceipt ring root (piD (ref.phys x.1)) := by
    obtain ⟨_, _, _, _, _, hW, -, -, hL⟩ := hx
    exact L3.CloseKeep.leaderBoundaryAt ref.toWidthDigitReference root x.1 hW hL
  have hrs := L3.CompareRestart.stableRunRestartLe ref.toWidthDigitReference root restart x hx
  have hq := widthBoundaryDigitBoundaryAuditFirst ref x.1 x.2 w
  refine ⟨by omega, Nat.le_refl _, fun source target hp => ?_, _, _, hat, ?_, hC⟩
  · obtain ⟨terminal, ht⟩ :=
      pairsFirstStrictOfDone ref hn root restart x w hx hdone source target hp
    obtain ⟨anchor, anchorTail, ha, hr⟩ := hR source target hp terminal ht
    exact ⟨terminal, anchor, anchorTail, ht, completionTimeLe ring _ ht.1, ha,
      completionTimeLe ring _ ha.1.1, hr⟩
  · show DigitBoundaryReceipt ring root
      (piD (ref.phys (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) (x.1, x.2)).1))
    rw [hq]
    exact L3.CloseKeep.boundaryWord ref hn root w x.1 hfx hB

/-- **`WidthComparisonClose` from clauses (R) and (C)** (any boundary reference); (B)
comes from the leader receipt of `WidthStableRun`.  (R) anchors and ranked terminals for the first
strict comparison terminals after the restart, (C) comparison currentness at the clock, on every
continuation at which every complete pair has its comparison completion after the restart.  The
facts (P) are proved (`L3.ClosePersist.comparisonCutOfReady`).  Consumer: the BANK premise of
`L3.PacketMomentCompareBank.hcompareBankOfStage` (`bankWidthBoundaryReference`) and the SMALL
premise `hcmpCloseSmall` of `l3HeadlineOfCleanBranches` (`smallWidthBoundaryReference`). -/
theorem widthComparisonCloseOfClauses (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
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
    (hC : ∀ (root : Fin n) (restart : Nat)
      (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (w : List (Fin n)),
      WidthStableRun ref.toWidthDigitReference root restart x →
      (∀ i, WidthComparePairDone ref.toWidthDigitReference root restart i
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x)) →
      DigitComparisonsCurrent ring root
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2
        (piD (ref.phys (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).1))
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2.current restart
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2.clock) :
    WidthComparisonClose ref.toWidthDigitReference := by
  intro root restart x w hx hdone
  exact comparisonCutOfReady ref hn root restart x w hx
    ⟨_, readyAtClock ref hn root restart x w hx hdone
      (hR root restart x w hx hdone) (hC root restart x w hx hdone)⟩

end L3.CloseBoundary

#print axioms L3.CloseBoundary.stableRunFacts
#print axioms L3.CloseBoundary.pairsFirstStrictOfDone
#print axioms L3.CloseBoundary.readyAtClock
#print axioms L3.CloseBoundary.widthComparisonCloseOfClauses
