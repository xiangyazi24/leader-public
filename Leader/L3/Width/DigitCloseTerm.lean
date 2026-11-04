import Leader.L3.Bank.RepairDigitTermEntry
import Leader.L3.Width.DigitCloseEntry

/-!
# The entry fact of clause (C), proved: the barrier behind the completing tail

`L3.CloseEntry.EntryCore` asks, at the terminal state of a complete pair's first strict
comparison completion after `restart` on the clean run, for the cycle class of the masked
comparison lane and the aged window `WinAge restart`.  This module proves it from the barrier
invariant of `L3.TermEntry`:

* `barRunWidth`: along every clean-run word from a clean start, the routine part `PairBase`,
  the frame order of the audit, and the barrier run invariant `BarRun` of the pair;
* `entryCoreOfBarrier`: the terminal of the completion is recorded by the last letter of the
  word, on the pair's terminal edge, by a live last carry whose clean ledger starts with the
  completion's tail sample `sigma`; `termEntryRing` gives the cycle class and `WinAge sigma.time`
  after it, and `restart < sigma.time` gives `WinAge restart`;
* `widthComparisonCloseOfRanks`: `WidthComparisonClose` from clause (R) alone.

Model check: research/lean-l3/ledgers/close-mc.py, clauses `bar_*`, `term_cyc`, `term_age`
(close-family-notes section 12).
-/

namespace L3.CloseTerm

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.ValueWaveClose
open L3.CompareStage
open L3.CohortDomination
open L3.CohortSites
open L3.Rearm
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortLedger
open L3.ValueLedger
open L3.UseRows
open L3.UseTrack
open L3.CurrentWin
open L3.CloseCurrent
open L3.CloseEntry
open L3.WidthWave
open L3.TermEntry

variable {n : Nat} {ring : DirectedRing n}

/-- **The barrier run on the clean run**: along every word from a clean start, the routine part
of the window class, the frame order of the audit and the barrier run invariant of a complete
pair of the start.  Consumer: `entryCoreOfBarrier`. -/
theorem barRunWidth (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (start : ref.State)
    (hL : WidthBoundaryDigitLayoutValues ref root start) (source : Nat)
    (hpair : DigitCompletePair ring root (piD (ref.phys start)) source
      (source + digitSpan (compileAdvice (ceilLogTwo n)))) (u : List (Fin n)) :
    PairBase ref.toWidthDigitReference root source (digitSpan (compileAdvice (ceilLogTwo n)))
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))) ∧
    AuditFrameOrder (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2 ∧
    BarRun ring root DigitLane.comparison source (digitSpan (compileAdvice (ceilLogTwo n)))
      (piD (ref.phys (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).1))
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2 := by
  obtain ⟨hsrc, hend, hlay⟩ := pairLayoutStart ref hn root start hL source hpair
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  have h0 : PairBase ref.toWidthDigitReference root source
      (digitSpan (compileAdvice (ceilLogTwo n))) (start, digitAuditInitial (piD (ref.phys start))) ∧
      AuditFrameOrder (start, digitAuditInitial (piD (ref.phys start))).2 ∧
      BarRun ring root DigitLane.comparison source (digitSpan (compileAdvice (ceilLogTwo n)))
        (piD (ref.phys (start, digitAuditInitial (piD (ref.phys start))).1))
        (start, digitAuditInitial (piD (ref.phys start))).2 :=
    ⟨⟨hlay, ghostCorrDistinctInitial ring root _ _ _ _,
      ⟨valCorrInitial ring root _ _ _ _, exportValInitial ring root _ _ _ _,
        useValInitial ring root _ _ _ _, ledgerOkInitial ring root _ _ _ _⟩⟩,
      auditFrameOrderInitial _,
      barRunInitial ring root _ _ _ hR _ _ (inheritedNoSample DigitLane.comparison)
        (ghostCorrDistinctInitial ring root _ _ _ _).1⟩
  generalize (start, digitAuditInitial (piD (ref.phys start))) = y at h0
  induction u generalizing y with
  | nil => exact h0
  | cons e rest ih =>
    apply ih
    obtain ⟨⟨hl, hg, hv⟩, hfo, hbar⟩ := h0
    obtain ⟨hl', hg'⟩ := widthGhostCorrDistinctStep ref.toWidthDigitReference ref.singletonFixed hn
      root DigitLane.comparison source _ hR hsrc hend (InheritedOk DigitLane.comparison) y hl hg e
    refine ⟨⟨hl', hg', widthValInvStep ref.toWidthDigitReference ref.singletonFixed hn root
      DigitLane.comparison source _ hR hsrc hend y hl hv e⟩, auditFrameOrderStep ring _ y.2 e hfo,
      ?_⟩
    obtain ⟨hL0, hb0, hbR, hb2R, hbF⟩ := hl
    obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn
      root y.1 hL0 e
    obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
    have hg2 : GhostCorrDistinct ring root DigitLane.comparison source
        (digitSpan (compileAdvice (ceilLogTwo n))) (InheritedOk DigitLane.comparison)
        (phiD ring (piD (ref.phys y.1)) (digitSite ring root j))
        (digitAuditStep ring (piD (ref.phys y.1)) y.2 (digitSite ring root j)) := by
      have h' : GhostCorrDistinct ring root DigitLane.comparison source
          (digitSpan (compileAdvice (ceilLogTwo n))) (InheritedOk DigitLane.comparison)
          (piD (ref.phys (ref.next y.1 (digitSite ring root j))))
          (digitAuditStep ring (piD (ref.phys y.1)) y.2 (digitSite ring root j)) := hg'
      rw [heq] at h'
      exact h'
    show BarRun ring root DigitLane.comparison source (digitSpan (compileAdvice (ceilLogTwo n)))
      (piD (ref.phys (ref.next y.1 (digitSite ring root j))))
      (digitAuditStep ring (piD (ref.phys y.1)) y.2 (digitSite ring root j))
    rw [heq]
    exact barRunStep ring (by omega) root (piD (ref.phys y.1)) _ source hR hsrc hend hroot hb0
      hbR hb2R hbF DigitLane.comparison (InheritedOk DigitLane.comparison)
      (inheritedNoSample DigitLane.comparison) y.2 j hj hbX hbY hg hg2 hbar

/-- **The entry fact of clause (C)** (any boundary reference): at the terminal state
of a complete pair's first strict comparison completion after `restart` on the clean run, the
masked comparison lane is in the cycle class and `WinAge restart` holds.  Consumer:
`L3.CloseEntry.currentEntryOfCore` (in `widthComparisonCloseOfRanks`). -/
theorem entryCoreOfBarrier (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    : EntryCore ref.toWidthDigitReference := by
  intro root restart start u source T hst hs hpair hT hTc
  obtain ⟨root0, hs0, hL⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root0 :=
    (ref.singletonFixed root0 start hs0).2.1 root (ref.singletonFixed root start hs).1
  subst hr
  obtain ⟨hsrc, hend, -⟩ := pairLayoutStart ref hn root start hL source hpair
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  have hlt := restartLtTerminal _ root source _ DigitLane.comparison restart T hT.1
  rcases List.eq_nil_or_concat u with hnil | ⟨u', e, hcat⟩
  · subst hnil
    have h0 : T.time = 0 := hTc
    omega
  · subst hcat
    obtain ⟨⟨hl, hg, -⟩, hfo, hbar⟩ := barRunWidth ref hn root start hL source hpair u'
    simp only [List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      at hT hTc ⊢
    generalize u'.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start))) = y at hl hg hfo hbar hT hTc ⊢
    have hclk : (widthDigitAuditNext ref.toWidthDigitReference y e).2.clock = y.2.clock + 1 := rfl
    rw [hclk] at hTc
    obtain ⟨-, hrec, hlane, hsrcT, -, -, pos, ledger, samples, exports, uses, hTL, hinh, -, hj,
      -, -⟩ := hT.1
    obtain ⟨-, hsl, hsi, hcut, -, -, -, -, -, -, -, -, hget, -, hop, -, -, -, -, -⟩ := hj ⟨0, pos⟩
    rcases recordedTerminalStepCases ring (piD (ref.phys y.1)) y.2 e T hrec with hold |
        ⟨-, hsite, hterm⟩
    · obtain ⟨f, hf, hft, -⟩ := hold
      have := (hfo.2.1 f hf).2
      omega
    · have he : e = digitSite ring root (source + (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1)) := by
        rw [← hsite, hsrcT]
        congr 1
        omega
      subst he
      rw [hlane] at hterm
      unfold svcAt at hterm
      obtain ⟨hlive, hledger⟩ := termLiveD DigitLane.comparison _ _ _ _ _ _ _ T hterm
      obtain ⟨hL0, hb0, hbR, hb2R, hbF⟩ := hl
      obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed
        hn root y.1 hL0 (digitSite ring root
          (source + (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1)))
      obtain ⟨-, hg'⟩ := widthGhostCorrDistinctStep ref.toWidthDigitReference ref.singletonFixed
        hn root DigitLane.comparison source _ hR hsrc hend (InheritedOk DigitLane.comparison) y
        ⟨hL0, hb0, hbR, hb2R, hbF⟩ hg (digitSite ring root
          (source + (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1)))
      have hg2 : GhostCorrDistinct ring root DigitLane.comparison source
          (digitSpan (compileAdvice (ceilLogTwo n))) (InheritedOk DigitLane.comparison)
          (phiD ring (piD (ref.phys y.1)) (digitSite ring root
            (source + (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1))))
          (digitAuditStep ring (piD (ref.phys y.1)) y.2 (digitSite ring root
            (source + (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1)))) := by
        have h' : GhostCorrDistinct ring root DigitLane.comparison source
            (digitSpan (compileAdvice (ceilLogTwo n))) (InheritedOk DigitLane.comparison)
            (piD (ref.phys (ref.next y.1 (digitSite ring root
              (source + (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1))))))
            (digitAuditStep ring (piD (ref.phys y.1)) y.2 (digitSite ring root
              (source + (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1)))) := hg'
        rw [heq] at h'
        exact h'
      have hlive' : (cohortProj ring root DigitLane.comparison source
          (digitSpan (compileAdvice (ceilLogTwo n))) (piD (ref.phys y.1))).live
            (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1) = true := by
        rw [projLive ring root _ source _ _ _ (by omega) (by omega)]
        exact hlive
      have hLc : (laneCells ring root DigitLane.comparison source y.2.current
          (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1)).carry = some ledger :=
        hledger.symm.trans hTL
      have hu : ledger.uses.head? = some (uses ⟨0, pos⟩) := by
        cases hus : ledger.uses with
        | nil =>
          rw [hus] at hget
          simp at hget
        | cons a t =>
          rw [hus] at hget
          simp at hget ⊢
          exact hget
      obtain ⟨⟨lam, hcyc⟩, hage⟩ := termEntryRing ring (by omega) root (piD (ref.phys y.1)) _
        source hR hsrc hend hroot hb0 hbR hb2R hbF DigitLane.comparison
        (InheritedOk DigitLane.comparison) y.2 hbX hbY hg hg2 hbar (samples ⟨0, pos⟩).id
        (by simpa using hsi) hsl hlive' ledger (uses ⟨0, pos⟩) hLc hinh hu hop
      refine ⟨⟨0, (lam, 0), 2 * digitSpan (compileAdvice (ceilLogTwo n)) + 1, ?_⟩, ?_⟩
      · show CohortCycIn _ 0 (cohortProj ring root DigitLane.comparison source _
          (piD (ref.phys (ref.next y.1 (digitSite ring root
            (source + (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1))))))) _ _
        rw [heq]
        exact hcyc
      · show WinAge ring root DigitLane.comparison source _ restart
          (cohortProj ring root DigitLane.comparison source _
            (piD (ref.phys (ref.next y.1 (digitSite ring root
              (source + (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1)))))))
          (digitAuditStep ring (piD (ref.phys y.1)) y.2 (digitSite ring root
            (source + (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1))))
        rw [heq]
        exact winAgeMono (Nat.le_of_lt hcut) hage

/-- **`WidthComparisonClose` from clause (R) alone** (any boundary reference): clause
(C) is discharged by `entryCoreOfBarrier`.  Consumer: the BANK premise of
`L3.PacketMomentCompareBank.hcompareBankOfStage` and the SMALL premise `hcmpCloseSmall` of
`l3HeadlineOfCleanBranches`, once clause (R) is produced. -/
theorem widthComparisonCloseOfRanks (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
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
            .comparison (digitSite ring root source) anchor anchorTail terminal) :
    WidthComparisonClose ref.toWidthDigitReference :=
  widthComparisonCloseOfEntry ref hn hR
    (currentEntryOfCore ref hn (entryCoreOfBarrier ref hn))

end L3.CloseTerm

#print axioms L3.CloseTerm.barRunWidth
#print axioms L3.CloseTerm.entryCoreOfBarrier
#print axioms L3.CloseTerm.widthComparisonCloseOfRanks
