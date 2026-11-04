import Leader.L3.Bank.RepairDigitCleanCore
import Leader.L3.Bank.RepairDigitFirstZeroClock

/-!
# R10c: the boundary stage from the clean entrance

The boundary premise `hboundary` of `bankDigitCausalCoreOfBoundary` asks for a first hit, from
the clean entrance `BankPostInheritedGrantDrain ∧ BankCleanRFold`, of
`(bankCleanDigitCoreCuts ring hbank).boundaryRetired`, i.e. of
`BankRepairDigitBoundaryRetiredCut ∧ BankRepairDigitGoneReachable`. Both old cuts name an
audit start with `BankRepairRFoldEstablished` (the monitored `AcceptedWord` history and the old
reader), and the gone cut a prepared history; the clean entrance carries `CleanWord` and the
clean reader instead, and no producer of `AcceptedWord` from `CleanWord` exists.

What the old boundary proofs actually read from that history is state data: the singleton root,
`QWord` and the root word values (`BankRepairDigitLayoutValues`). The clean entrance gives these
directly (`bankCleanBoundaryRoot`). This module proves the boundary stage at the full boundary
micro-charge with the audit restarted at the clean entrance:

* `bankCleanBoundaryLabelTasks`, `bankCleanBoundaryExtinctionClock`: the label-extinction part,
  into the clean gone cut `BankCleanBoundaryGoneCut`;
* `bankCleanBoundaryLeadingTasks`, `bankCleanBoundaryFinalTasks`, `bankCleanBoundaryFlushClock`:
  the receipt flush (leading and final regions) on the layout-values class, into the clean
  retired cut `BankCleanBoundaryRetiredCut` (the old cut with the clean audit start);
* `bankCleanBoundaryStage`: the composition at `bankRepairDigitBoundaryMicroCharge n`, with the
  grant drain carried;
* `bankCleanBoundaryCohortLayout`: every interior pair of every continuation of a clean entrance
  is in `CohortLayout` (the start condition of the group 6 bridge `strictCompletionCyc`).
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false

section CleanBoundary

variable {n : Nat} (ring : DirectedRing n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-! ### The clean entrance carries the old state data -/

/-- The clean entrance has a singleton root with the layout values (`QWord` and the root word
values). Consumer: `bankCleanBoundaryRetiredOfReceipt`, `bankCleanBoundaryFlushClock`,
`bankCleanBoundaryCohortLayout`. -/
theorem bankCleanBoundaryRoot (z : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank z) (hC : BankCleanRFold ring hbank z) :
    ∃ root, BankPostInheritedSingleton ring hbank root z ∧
      BankRepairDigitLayoutValues ring hbank root z := by
  obtain ⟨root, hfixed, _, _⟩ := hC.1.2
  have hs : BankPostInheritedSingleton ring hbank root z := ⟨hD, hfixed⟩
  exact ⟨root, hs, bankCleanDigitLayoutValuesOfSingleton ring hbank root z hs hC.1.2⟩

/-- `bankRepairDigitProducedEntranceNoFireFrozen` with `QWord` given directly instead of read
off `AcceptedWord`. Consumer: `bankCleanBoundaryLabelTasks`. -/
theorem bankCleanBoundaryFrozen (hn : 5 ≤ n) (start : BankReferenceState ring hbank)
    (root : Fin n) (hs : BankPostInheritedSingleton ring hbank root start)
    (hq : AcceptedReceipts.QWord ring (piW start.val.1)) :
    ∀ z, BankRepairDigitOneLabelReachableFrom ring hbank start z →
      (∀ e : Fin n,
        oldFire (z.1.val.1 e) (z.1.val.1 (ring.rightNeighbor e)) = none) ∧
      (∀ i, (piD z.1.val.1 i).word.native.l = (piD start.val.1 i).word.native.l) ∧
      (∀ i, (piD z.1.val.1 i).word.beta = (piD start.val.1 i).word.beta) := by
  intro z hz
  obtain ⟨hzs, -, hzb⟩ :=
    bankRepairDigitProducedReachableInv hn ring hbank start root hs hq z hz
  have hg : ∀ i, (z.1.val.1 i).grant = false := hzs.1.1.2
  refine ⟨fun e => bankRepairDigitOldFireNoneOfGrantFree _ _ (hg e) (hg _), ?_, hzb⟩
  intro i
  show (z.1.val.1 i).l = (start.val.1 i).l
  rw [bankRepairDigitRootedLeader ring hbank root z.1 hzs i,
    bankRepairDigitRootedLeader ring hbank root start hs i]

/-- The single-inherited-label tasks at every site of a clean entrance. Consumer:
`bankCleanBoundaryExtinctionClock`. -/
theorem bankCleanBoundaryLabelTasks (hn : 5 ≤ n) (z : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank z) (hC : BankCleanRFold ring hbank z) :
    ∀ site, BankRepairDigitSingleInheritedLabelTasks ring hbank z site := by
  obtain ⟨root, hfixed, hvalues, hq⟩ := hC.1.2
  have hs : BankPostInheritedSingleton ring hbank root z := ⟨hD, hfixed⟩
  intro site
  exact bankRepairDigitSingleInheritedLabelTasksOfFrozenInit (by omega) ring hbank z site _ _
    (bankCleanBoundaryFrozen ring hbank hn z root hs hq)
    (bankRepairDigitLabelInitialInvExempt ring _ _ _ (bankRepairDigitLeadingLengthPos hbank)
      site _ (bankRepairDigitNonRootStopOfWordValues ring hbank z root hs.2.1 hvalues site))

/-! ### Label extinction -/

/-- The clean gone cut: a state reached from a clean entrance by a word at which every
inherited base label of the audit restarted at the entrance is gone. Consumer:
`bankCleanBoundaryExtinctionClock`, `bankCleanBoundaryFlushClock`. -/
def BankCleanBoundaryGoneCut (z : BankReferenceState ring hbank) : Prop :=
  ∃ (start : BankReferenceState ring hbank) (word : List (Fin n)),
    BankPostInheritedGrantDrain ring hbank start ∧ BankCleanRFold ring hbank start ∧
    bankRepairDigitAllBaseLabelsGone ring hbank
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))) ∧
    z = word.foldl (bankRepairNext ring hbank) start

/-- States reachable from the clean gone cut. Consumer: `bankCleanBoundaryStage` (the clean
analogue of `BankRepairDigitGoneReachable` in the boundary cut). -/
def BankCleanBoundaryGoneReachable (z : BankReferenceState ring hbank) : Prop :=
  ∃ (z₀ : BankReferenceState ring hbank) (word : List (Fin n)),
    BankCleanBoundaryGoneCut ring hbank z₀ ∧ z = word.foldl (bankRepairNext ring hbank) z₀

/-- The clean boundary cut: `BankRepairDigitBoundaryRetiredCut` with the audit restarted at a
clean entrance instead of an `R`-fold-established one. Consumer: `bankCleanBoundaryStage`. -/
def BankCleanBoundaryRetiredCut (z : BankReferenceState ring hbank) : Prop :=
  ∃ (start : BankReferenceState ring hbank) (word : List (Fin n)) (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
    BankPostInheritedGrantDrain ring hbank start ∧ BankCleanRFold ring hbank start ∧
    word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (z, audit) ∧
    WFixedRoot ring root (piW z.val.1) ∧
    DigitAt ring audit audit.clock (piD z.val.1) audit.current ∧
    DigitBoundaryReceipt ring root (piD z.val.1) ∧
    DigitBaseExtinct ring root audit 0 audit.clock

/-- **Label extinction from the clean entrance** at the extinction part of the boundary
charge. Consumer: `bankCleanBoundaryStage`. -/
theorem bankCleanBoundaryExtinctionClock (hn : 5 ≤ n) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧ BankCleanRFold ring hbank z)
      (BankCleanBoundaryGoneCut ring hbank) (bankRepairDigitExtinctionMicroCharge n) := by
  rintro z ⟨hD, hC⟩ T
  have hcost := bankRepairDigitAllBaseCostLogarithmicOfTasks (by omega : 2 ≤ n) ring hbank _
    (bankCleanBoundaryLabelTasks ring hbank hn z hD hC) T
  have htr := bankRepairDigitCostTransfer
      (bankRepairNext ring hbank) (bankRepairDigitBoundaryAuditNext ring hbank)
      (BankCleanBoundaryGoneCut ring hbank)
      (bankRepairDigitAllBaseLabelsGone ring hbank) T _ _
      (fun word hg => ⟨z, word, hD, hC, hg, rfl⟩)
  refine Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.le_trans htr hcost)) (Nat.le_of_eq ?_)
  unfold bankRepairDigitExtinctionMicroCharge
  ac_rfl

/-! ### The receipt flush on the layout-values class -/

/-- The layout-values class at some root. Consumer: the two flush regions. -/
def BankCleanBoundaryLayout (z : BankReferenceState ring hbank) : Prop :=
  ∃ root, BankRepairDigitLayoutValues ring hbank root z

/-- The layout-values class is closed under words. Consumer: the two flush regions. -/
theorem bankCleanBoundaryLayoutWord (hn : 5 ≤ n) (z : BankReferenceState ring hbank)
    (hz : BankCleanBoundaryLayout ring hbank z) (word : List (Fin n)) :
    BankCleanBoundaryLayout ring hbank (word.foldl (bankRepairNext ring hbank) z) := by
  obtain ⟨root, h⟩ := hz
  exact ⟨root, bankRepairDigitLayoutValuesWord ring hn hbank root word z h⟩

/-- The delimiters of a layout-values state. Consumer: `bankCleanBoundaryLeadData`,
`bankCleanBoundaryFinData`, `bankCleanBoundaryCohortLayout`. -/
theorem bankCleanBoundaryDelimiters (hn : 5 ≤ n)
    (root : Fin n) (z : BankReferenceState ring hbank)
    (hL : BankRepairDigitLayoutValues ring hbank root z) :
    ∃ first : Nat,
      (compileAdvice (ceilLogTwo n)).t ≤ first ∧
      first < (compileAdvice (ceilLogTwo n)).t + digitSpan (compileAdvice (ceilLogTwo n)) ∧
      ∀ k : Nat, 0 < k → k < n →
        ((piD z.val.1 (digitSite ring root k)).word.beta = true ↔
          first ≤ k ∧ (k - first) % digitSpan (compileAdvice (ceilLogTwo n)) = 0) := by
  have hq := ringQ_facts n hn
  have ht : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) hq.1
  have hprim := tapTablePrimitive (compileAdvice (ceilLogTwo n)).t ht
  obtain ⟨d, hd, hk⟩ := bankRepairDigitDelimiterLayout ring root _ hL.2 (by omega) hprim
  refine ⟨(compileAdvice (ceilLogTwo n)).t + d, by omega, ?_, fun k h0 hkn => ?_⟩
  · unfold digitSpan; omega
  · rw [bankRepairDigitSiteShift]
    exact hk k h0 hkn

/-- Lead data on the layout-values class. Consumer: `bankCleanBoundaryLeadingTasks`. -/
theorem bankCleanBoundaryLeadData (hn : 5 ≤ n)
    (z : BankReferenceState ring hbank) (hz : BankCleanBoundaryLayout ring hbank z) :
    ∃ (root : Fin n) (first : Nat), BankRepairDigitLeadData ring hbank root first z ∧
      first + 1 ≤ (compileAdvice (ceilLogTwo n)).t +
        digitSpan (compileAdvice (ceilLogTwo n)) := by
  obtain ⟨root, hL⟩ := hz
  obtain ⟨first, ht, hf, hb⟩ := bankCleanBoundaryDelimiters ring hbank hn root z hL
  have hw := bankRepairDigitLeadWidth hn hbank
  have ht2 := compileAdvice_t_ge_two (ceilLogTwo n)
    (by have := bankRepairBankBand hbank; omega)
  exact ⟨root, first, ⟨hL.1, by omega, by omega, hb⟩, by omega⟩

/-- Final-region data on the layout-values class. Consumer: `bankCleanBoundaryFinalTasks`. -/
theorem bankCleanBoundaryFinData (hn : 5 ≤ n)
    (z : BankReferenceState ring hbank) (hz : BankCleanBoundaryLayout ring hbank z) :
    ∃ (root : Fin n) (first : Nat), BankRepairDigitLeadData ring hbank root first z ∧
      2 ≤ first ∧ first + digitSpan (compileAdvice (ceilLogTwo n)) + 1 ≤ n := by
  obtain ⟨root, hL⟩ := hz
  obtain ⟨first, ht, hf, hb⟩ := bankCleanBoundaryDelimiters ring hbank hn root z hL
  have hw := bankRepairDigitFinWidth hn hbank
  have ht2 := compileAdvice_t_ge_two (ceilLogTwo n)
    (by have := bankRepairBankBand hbank; omega)
  exact ⟨root, first, ⟨hL.1, by omega, by omega, hb⟩, by omega, by omega⟩

/-- The leading half of the receipt is never lost on the layout-values class. Consumer:
`bankCleanBoundaryFinalTasks`. -/
theorem bankCleanBoundaryLeadingStable (hn : 5 ≤ n) (z : BankReferenceState ring hbank)
    (hz : BankCleanBoundaryLayout ring hbank z)
    (hrec : BankRepairDigitLeaderLeading ring hbank z) (word : List (Fin n)) :
    BankRepairDigitLeaderLeading ring hbank (word.foldl (bankRepairNext ring hbank) z) := by
  obtain ⟨root, hL⟩ := hz
  obtain ⟨r, hW, hr⟩ := hrec
  have hrr : r = root := hL.1.1.2.2.1 r hW.1
  subst hrr
  refine ⟨r, bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank r z hL.1.1 word, ?_⟩
  have key : ∀ (w : List (Fin n)) (y : BankReferenceState ring hbank),
      BankRepairDigitLayoutFixed ring hbank r y →
      DigitLeadingBoundary ring r (piD y.val.1) →
      DigitLeadingBoundary ring r (piD (w.foldl (bankRepairNext ring hbank) y).val.1) := by
    intro w
    induction w with
    | nil => intro y _ h; exact h
    | cons e rest ih =>
        intro y hy h
        exact ih _ (bankRepairDigitLayoutFixedStep ring hn hbank r y hy e)
          (bankRepairDigitBankStepOf ring hn hbank r (DigitLeadingBoundary ring r)
            (fun S e hroot hbX hbY h => bankRepairDigitLeadingStep ring (by omega) r S e
              (bankRepairDigitLaneRowFactsHold _) hroot hbX hbY h) y hy e h)
  exact key word z hL.1 hr

/-- **Leading region** on the layout-values class, at the paper's budget `2 J` (the rank and
nominated edge of `bankRepairDigitLeadingFlushTasksHold`). Consumer:
`bankCleanBoundaryFlushClock`. -/
theorem bankCleanBoundaryLeadingTasks (hn : 5 ≤ n)
    :
    BankRepairDigitRegionTasks ring hbank (BankCleanBoundaryLayout ring hbank)
      (fun z => BankCleanBoundaryLayout ring hbank z ∧ BankRepairDigitLeaderLeading ring hbank z)
      (2 * bankRepairDigitBoundaryServices (ceilLogTwo (ceilLogTwo n))) := by
  have hR := bankRepairDigitLeadSpanTwo hbank
  refine ⟨bankRepairDigitLeadRank ring hbank,
    bankRepairDigitLeadChosen ring hbank ⟨0, by omega⟩, ?_, ?_, ?_⟩
  · intro z₀ word hz₀ hnt
    have hz := bankCleanBoundaryLayoutWord ring hbank hn z₀ hz₀ word
    generalize word.foldl (bankRepairNext ring hbank) z₀ = z at hz hnt ⊢
    obtain ⟨root, first, hd, -⟩ := bankCleanBoundaryLeadData ring hbank hn z hz
    apply bankRepairDigitLeadChosenSpec
    have hnb : ¬ DigitLeadingBoundary ring root (piD z.val.1) := fun hb =>
      hnt ⟨hz, root,
        bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank root z hd.1.1 [], hb⟩
    have hedge := fun e => bankRepairDigitLeadBankEdge ring hn hbank root z hd.1 e
    obtain ⟨k, _, hdrop⟩ := bankRepairDigitLeadRankDrop ring (by omega) root (piD z.val.1)
      (digitSpan (compileAdvice (ceilLogTwo n))) first hR hd.2.1 hd.2.2.1 (hedge root).2.1
      hd.2.2.2
      (fun k _ => ⟨(hedge (digitSite ring root k)).2.2.1, (hedge (digitSite ring root k)).2.2.2⟩)
      hnb
    refine ⟨digitSite ring root k, ?_⟩
    rw [bankRepairDigitLeadRankEq ring hbank root first _
        (bankRepairDigitLeadDataStep ring hn hbank root first z hd _),
      bankRepairDigitLeadRankEq ring hbank root first z hd, (hedge _).1]
    exact hdrop
  · intro z₀ word hz₀ _ e
    have hz := bankCleanBoundaryLayoutWord ring hbank hn z₀ hz₀ word
    generalize word.foldl (bankRepairNext ring hbank) z₀ = z at hz ⊢
    obtain ⟨root, first, hd, -⟩ := bankCleanBoundaryLeadData ring hbank hn z hz
    obtain ⟨k, hk, rfl⟩ := bankRepairDigitSiteSurj ring root e
    have hedge := fun e => bankRepairDigitLeadBankEdge ring hn hbank root z hd.1 e
    rw [bankRepairDigitLeadRankEq ring hbank root first _
        (bankRepairDigitLeadDataStep ring hn hbank root first z hd _),
      bankRepairDigitLeadRankEq ring hbank root first z hd, (hedge _).1]
    exact bankRepairDigitLeadRankStep ring (by omega) root (piD z.val.1)
      (digitSpan (compileAdvice (ceilLogTwo n))) first hR hd.2.2.1 (hedge root).2.1 hd.2.2.2
      k hk (hedge _).2.2.1 (hedge _).2.2.2
  · intro z hz
    obtain ⟨root, first, hd, hfle⟩ := bankCleanBoundaryLeadData ring hbank hn z hz
    rw [bankRepairDigitLeadRankEq ring hbank root first z hd]
    have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
    have ht : (compileAdvice (ceilLogTwo n)).t = ceilLogTwo (ceilLogTwo n) :=
      compileAdvice_t_large _ (by omega)
    have hspan : digitSpan (compileAdvice (ceilLogTwo n)) =
        bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)) := by
      unfold digitSpan bankRepairDigitRadius
      rw [ht]
    have hb := bankRepairDigitLeadRankOfBound ring root (piD z.val.1)
      (digitSpan (compileAdvice (ceilLogTwo n))) first (by omega) hd.2.1
    rw [hspan] at hb hfle
    rw [ht] at hfle
    have hA : first - 1 ≤ bankRepairDigitLeadingRecords (ceilLogTwo (ceilLogTwo n)) := by
      unfold bankRepairDigitLeadingRecords
      omega
    rw [hspan]
    exact Nat.le_trans hb (bankRepairDigitLeadBudgetFits _ _ hA)

/-- **Final region** on the layout-values class, at the paper's budget `F + R + U + r` (the
rank and nominated edge of `bankRepairDigitFinalFlushTasksHold`). Consumer:
`bankCleanBoundaryFlushClock`. -/
theorem bankCleanBoundaryFinalTasks (hn : 5 ≤ n)
    :
    BankRepairDigitRegionTasks ring hbank
      (fun z => BankCleanBoundaryLayout ring hbank z ∧ BankRepairDigitLeaderLeading ring hbank z)
      (fun z => BankCleanBoundaryLayout ring hbank z ∧ BankRepairDigitLeaderReceipt ring hbank z)
      (bankRepairDigitForwardCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitReturnCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitSettledCount (bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) +
        bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n))) := by
  have hR := bankRepairDigitLeadSpanTwo hbank
  refine ⟨bankRepairDigitFinRank ring hbank,
    bankRepairDigitFinChosen ring hbank ⟨0, by omega⟩, ?_, ?_, ?_⟩
  · intro z₀ word hz₀ hnt
    have hz := bankCleanBoundaryLayoutWord ring hbank hn z₀ hz₀.1 word
    have hlead := bankCleanBoundaryLeadingStable ring hbank hn z₀ hz₀.1 hz₀.2 word
    generalize word.foldl (bankRepairNext ring hbank) z₀ = z at hz hlead hnt ⊢
    obtain ⟨root, first, hd, hf2, hw⟩ := bankCleanBoundaryFinData ring hbank hn z hz
    have hedge := fun e => bankRepairDigitLeadBankEdge ring hn hbank root z hd.1 e
    obtain ⟨hRL, hLn, _, hbS, hbL, hbF, hmax⟩ := bankRepairDigitFinLayout ring root
      (piD z.val.1) (digitSpan (compileAdvice (ceilLogTwo n))) first hR hf2 hw hd.2.2.2
    obtain ⟨r', hW, hlb⟩ := hlead
    have hr : r' = root := hd.1.1.2.2.1 r' hW.1
    subst hr
    have hnf : ¬ DigitFinalBoundary ring r' (piD z.val.1) := fun hf =>
      hnt ⟨hz, r', hW, hlb, hf⟩
    apply bankRepairDigitFinChosenSpec
    obtain ⟨lane0, j0, hj0, hbad⟩ := bankRepairDigitFinalFailing ring r' (piD z.val.1) _ hLn
      hbL hmax hnf
    obtain ⟨k, _, hdrop⟩ := bankRepairDigitFinalRankDrop ring (by omega) r' (piD z.val.1)
      (digitSpan (compileAdvice (ceilLogTwo n)))
      (bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n)
      hR hRL hLn (hedge r').2.1 hbS hbL hbF
      (fun k _ => ⟨(hedge (digitSite ring r' k)).2.2.1, (hedge (digitSite ring r' k)).2.2.2⟩)
      lane0 j0 hj0 hbad
    refine ⟨digitSite ring r' k, ?_⟩
    rw [bankRepairDigitFinRankEq ring hbank r' first _
        (bankRepairDigitLeadDataStep ring hn hbank r' first z hd _),
      bankRepairDigitFinRankEq ring hbank r' first z hd, (hedge _).1]
    exact hdrop
  · intro z₀ word hz₀ _ e
    have hz := bankCleanBoundaryLayoutWord ring hbank hn z₀ hz₀.1 word
    generalize word.foldl (bankRepairNext ring hbank) z₀ = z at hz ⊢
    obtain ⟨root, first, hd, hf2, hw⟩ := bankCleanBoundaryFinData ring hbank hn z hz
    obtain ⟨k, hk, rfl⟩ := bankRepairDigitSiteSurj ring root e
    have hedge := fun e => bankRepairDigitLeadBankEdge ring hn hbank root z hd.1 e
    obtain ⟨hRL, hLn, _, hbS, hbL, hbF, _⟩ := bankRepairDigitFinLayout ring root
      (piD z.val.1) (digitSpan (compileAdvice (ceilLogTwo n))) first hR hf2 hw hd.2.2.2
    rw [bankRepairDigitFinRankEq ring hbank root first _
        (bankRepairDigitLeadDataStep ring hn hbank root first z hd _),
      bankRepairDigitFinRankEq ring hbank root first z hd, (hedge _).1]
    exact bankRepairDigitFinalRankStep ring (by omega) root (piD z.val.1)
      (digitSpan (compileAdvice (ceilLogTwo n)))
      (bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n)
      hR hRL hLn (hedge root).2.1 hbS hbL hbF
      (fun k _ => ⟨(hedge (digitSite ring root k)).2.2.1, (hedge (digitSite ring root k)).2.2.2⟩)
      k hk
  · intro z hz
    obtain ⟨root, first, hd, hf2, hw⟩ := bankCleanBoundaryFinData ring hbank hn z hz.1
    obtain ⟨_, hLn, hnL, _⟩ := bankRepairDigitFinLayout ring root
      (piD z.val.1) (digitSpan (compileAdvice (ceilLogTwo n))) first hR hf2 hw hd.2.2.2
    rw [bankRepairDigitFinRankEq ring hbank root first z hd]
    have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
    have ht : (compileAdvice (ceilLogTwo n)).t = ceilLogTwo (ceilLogTwo n) :=
      compileAdvice_t_large _ (by omega)
    have hspan : digitSpan (compileAdvice (ceilLogTwo n)) =
        bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)) := by
      unfold digitSpan bankRepairDigitRadius
      rw [ht]
    rw [← hspan]
    have h1 := bankRepairDigitFinalRankLe ring root (digitSpan (compileAdvice (ceilLogTwo n)))
      (bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n) (piD z.val.1)
    have h2 := bankRepairDigitFinalBudget (digitSpan (compileAdvice (ceilLogTwo n)))
      (n - bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n)
      (by omega) (by omega)
    exact Nat.le_trans h1 h2

/-- A state reachable from the clean gone cut with the leader receipt is in the clean
boundary cut (the audit of the entrance keeps every label gone and its invariant). Consumer:
`bankCleanBoundaryFlushClock`. -/
theorem bankCleanBoundaryRetiredOfReceipt (hn : 5 ≤ n) (z : BankReferenceState ring hbank)
    (hz : BankCleanBoundaryGoneReachable ring hbank z)
    (hrec : BankRepairDigitLeaderReceipt ring hbank z) :
    BankCleanBoundaryRetiredCut ring hbank z := by
  obtain ⟨_, word', ⟨start, word, hD, hC, hg, rfl⟩, rfl⟩ := hz
  obtain ⟨root, hs, -⟩ := bankCleanBoundaryRoot ring hbank start hD hC
  rw [← List.foldl_append] at hrec ⊢
  have hg' : bankRepairDigitAllBaseLabelsGone ring hbank
      ((word ++ word').foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))) := by
    rw [List.foldl_append]
    exact bankRepairDigitAllGoneWord hn ring hbank word' _ hg
  generalize word ++ word' = w at hrec hg' ⊢
  obtain ⟨r, hW, hr⟩ := hrec
  have hr' : r = root :=
    (bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank root _ hs w).2.1 r hW.1
  subst hr'
  have hinv := bankRepairDigitBoundaryAuditInvariantRun ring hn hbank r start hs w
  have hfirst := bankRepairDigitBoundaryAuditFirst ring hbank start
    (digitAuditInitial (piD start.val.1)) w
  have hat := hinv.2.1
  rw [hfirst] at hat
  refine ⟨start, w, r,
    (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1))).2, hD, hC, ?_,
    bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank r start hs w,
    hat, hr,
    bankRepairDigitBoundaryBaseExtinctOfSingleton ring hn hbank r start hs w hg'⟩
  exact Prod.ext hfirst rfl

/-- **The receipt flush from the clean gone cut** at the remainder of the boundary charge,
landing in the clean boundary cut on a state still reachable from the clean gone cut.
Consumer: `bankCleanBoundaryStage`. -/
theorem bankCleanBoundaryFlushClock (hn : 5 ≤ n) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankCleanBoundaryGoneCut ring hbank)
      (fun z => BankCleanBoundaryRetiredCut ring hbank z ∧
        BankCleanBoundaryGoneReachable ring hbank z)
      (bankRepairDigitFlushMicroCharge n) := by
  have hlead := bankRepairDigitRegionClockOfTasks ring hbank _ _ _
    (bankCleanBoundaryLeadingTasks ring hbank hn)
  have hfin := bankRepairDigitRegionClockOfTasks ring hbank _ _ _
    (bankCleanBoundaryFinalTasks ring hbank hn)
  have h := bankRepairDigitZeroCompose (bankRepairNext ring hbank) _ _ _ _ _ hlead hfin
  intro z hz T
  have hzl : BankCleanBoundaryLayout ring hbank z := by
    obtain ⟨start, word, hD, hC, -, hzeq⟩ := id hz
    obtain ⟨root, -, hL⟩ := bankCleanBoundaryRoot ring hbank start hD hC
    rw [hzeq]
    exact bankCleanBoundaryLayoutWord ring hbank hn start ⟨root, hL⟩ word
  have htr := bankRepairDigitCostTransfer (bankRepairNext ring hbank)
    (bankRepairNext ring hbank)
    (fun y => BankCleanBoundaryRetiredCut ring hbank y ∧
      BankCleanBoundaryGoneReachable ring hbank y)
    (fun y => BankCleanBoundaryLayout ring hbank y ∧ BankRepairDigitLeaderReceipt ring hbank y)
    T z z
    (fun w hw => ⟨bankCleanBoundaryRetiredOfReceipt ring hbank hn _ ⟨z, w, hz, rfl⟩ hw.2,
      z, w, hz, rfl⟩)
  refine Nat.le_trans (Nat.mul_le_mul_left 2 htr) (Nat.le_trans (h z hzl T) ?_)
  apply Nat.mul_le_mul_left
  unfold bankRepairDigitFlushMicroCharge
  rw [← Nat.mul_add, ← Nat.mul_add]
  exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left n
    (by have h := (bankRepairDigitFlushBudgetPays hbank).2; omega))

/-! ### The boundary stage -/

/-- **The boundary stage at the clean entrance**: from `BankPostInheritedGrantDrain ∧
BankCleanRFold`, the first hit of the clean boundary cut (grant drain retained, receipt and
base extinction on the audit restarted at the entrance, reachable from the clean gone cut)
costs at most the boundary micro-charge. This is `hboundary` of
`bankDigitCausalCoreOfBoundary` with `bankCleanDigitCoreCuts.boundaryRetired` replaced by its
clean analogue. Consumer: the clean digit core (`bankDigitCausalCoreOfBoundary`, after its
boundary cut is re-targeted to the clean audit start). -/
theorem bankCleanBoundaryStage (hn : 5 ≤ n) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧ BankCleanRFold ring hbank z)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        (BankCleanBoundaryRetiredCut ring hbank z ∧ BankCleanBoundaryGoneReachable ring hbank z))
      (bankRepairDigitBoundaryMicroCharge n) := by
  have h := bankRepairDigitZeroCompose (bankRepairNext ring hbank) _ _ _ _ _
    (bankCleanBoundaryExtinctionClock ring hbank hn) (bankCleanBoundaryFlushClock ring hbank hn)
  rw [bankRepairDigitBoundaryChargeSplit hn hbank] at h
  exact bankCleanDigitChargedCarryDrain ring hn hbank _ _ _ (fun z hz => hz.1) h

/-! ### The pair layout at a clean entrance -/

/-- **Every interior pair is in `CohortLayout`** at every continuation of a clean entrance:
with the fixed root and the first delimiter `first`, the pair `(first + i R, first + (i+1) R)`
(`R = digitSpan`) has its delimiters at `src`, `src + R`, `src + 2R` and none in between.
Consumer: the group 6 bridge `L3.DigitEntryBridge.strictCompletionCyc`, whose start is a
layout state where the audit restarts. -/
theorem bankCleanBoundaryCohortLayout (hn : 5 ≤ n)
    (z : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank z) (hC : BankCleanRFold ring hbank z)
    (word : List (Fin n)) :
    ∃ (root : Fin n) (first : Nat), (compileAdvice (ceilLogTwo n)).t ≤ first ∧
      ∀ i, 2 ≤ first + i * digitSpan (compileAdvice (ceilLogTwo n)) →
        first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
          2 * digitSpan (compileAdvice (ceilLogTwo n)) < n →
        L3.CohortSites.CohortLayout ring hbank root
          (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
          (digitSpan (compileAdvice (ceilLogTwo n)))
          (word.foldl (bankRepairNext ring hbank) z) := by
  obtain ⟨root, hs, hL⟩ := bankCleanBoundaryRoot ring hbank z hD hC
  have hL' := bankRepairDigitLayoutValuesWord ring hn hbank root word z hL
  obtain ⟨first, ht, -, hb⟩ := bankCleanBoundaryDelimiters ring hbank hn root _ hL'
  refine ⟨root, first, ht, fun i h2 hend => ?_⟩
  generalize digitSpan (compileAdvice (ceilLogTwo n)) = R at h2 hend hb ⊢
  generalize hm : i * R = m at h2 hend
  have hmR : m % R = 0 := by rw [← hm]; exact Nat.mul_mod_left i R
  have hm1 : (m + R) % R = 0 := by
    rw [← hm, show i * R + R = (i + 1) * R by rw [Nat.succ_mul]]
    exact Nat.mul_mod_left _ R
  have hm2 : (m + 2 * R) % R = 0 := by
    rw [← hm, show i * R + 2 * R = (i + 2) * R by rw [Nat.add_mul]]
    exact Nat.mul_mod_left _ R
  refine ⟨hL'.1, ?_, ?_, ?_, fun k hk0 hk2 hkR => ?_⟩
  · exact (hb _ (by omega) (by omega)).2
      ⟨by omega, by rw [show first + m - first = m by omega]; exact hmR⟩
  · exact (hb _ (by omega) (by omega)).2
      ⟨by omega, by rw [show first + m + R - first = m + R by omega]; exact hm1⟩
  · exact (hb _ (by omega) (by omega)).2
      ⟨by omega, by rw [show first + m + 2 * R - first = m + 2 * R by omega]; exact hm2⟩
  · cases hbeta : (piD (word.foldl (bankRepairNext ring hbank) z).val.1
        (digitSite ring root (first + m + k))).word.beta with
    | false => rfl
    | true =>
      exfalso
      have h := ((hb _ (by omega) (by omega)).1 hbeta).2
      rw [show first + m + k - first = m + k by omega, ← hm, Nat.mul_add_mod' i R k] at h
      by_cases hk : k < R
      · rw [Nat.mod_eq_of_lt hk] at h
        omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
        omega

end CleanBoundary

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankCleanBoundaryRoot
#print axioms L3.RenewalReferenceClock.bankCleanBoundaryLabelTasks
#print axioms L3.RenewalReferenceClock.bankCleanBoundaryExtinctionClock
#print axioms L3.RenewalReferenceClock.bankCleanBoundaryLeadingTasks
#print axioms L3.RenewalReferenceClock.bankCleanBoundaryFinalTasks
#print axioms L3.RenewalReferenceClock.bankCleanBoundaryRetiredOfReceipt
#print axioms L3.RenewalReferenceClock.bankCleanBoundaryFlushClock
#print axioms L3.RenewalReferenceClock.bankCleanBoundaryStage
#print axioms L3.RenewalReferenceClock.bankCleanBoundaryCohortLayout
