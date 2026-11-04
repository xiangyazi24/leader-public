import Leader.L3.Width.DigitWriterStage

/-!
# The comparison-lane e-max stage after the digit-stability cut

repair.tex 1743-1749: "Restart the comparison observer at the actual digit-stability cut ...
Lemma e-max apply to its actual arbitrary scratch."  The restart is the clock `restart` of the
writer value receipts (`WidthWriterValueReceipts … retired restart`) on the audit started at the
clean start; a comparison completion after it is `DigitCompletion … .comparison restart`.

* `WidthStableRun ref root restart x`: the writer values-stable cut data at the coupled state `x`
  (`L3.WriterValueCuts.WidthWriterValuesStableCut`).
* `WidthComparePairDone ref root restart i x`: complete pair `i` has a comparison completion
  after `restart`.
* `WidthComparePairMoment ref N` (premise): from every values-stable state, the first such
  completion of pair `i` has `E[z^T] ≤ 40`, `z = N/(N-1)`.
* `WidthComparisonClose ref` (premise): on a continuation of a values-stable state at which every
  complete pair has its comparison completion after `restart`, the comparison cut holds (the
  anchor, rank, boundary-receipt and currentness facts of `DigitComparisonReady` at that clock).
  It plays for the comparison lane the part `WidthReceiptsClose` plays for the wave.
* `widthComparisonStageOfMoments` (both bands): the comparison clock at `2 t` from the
  moments and the certificate `⌊n/r⌋ · 40 · (N-1)^t ≤ N^t` (Lemma e-max, exact Jensen).
* `smallComparisonClockOfMoments` (SMALL): at the slot `smallDigitCompareTable q`, which is the
  certified writer coefficient (same `N`, same pair count, same certificate).
-/

namespace L3.CompareStage

open L3
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open L3.WidthDigit
open L3.DigitCohortScratch
open L3.DigitStructuralClean
open L3.PairMoment
open L3.PairMomentPremise
open L3.WriterStage
open L3.WriterValueCuts

set_option autoImplicit false

section Generic

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- The values-stable cut data at a coupled state, with the boundary leader receipt
(DESIGN-MOTIVATIONS 2026-11-02 08:45).  Consumer: `WidthComparePairMoment`,
`WidthComparisonClose`, `widthComparisonStageOfMoments`. -/
def WidthStableRun (root : Fin n) (restart : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ (start : ref.State) (word : List (Fin n)) (retired : Nat),
    ref.start start ∧
    word.foldl (widthDigitAuditNext ref)
      (start, digitAuditInitial (piD (ref.phys start))) = x ∧
    WFixedRoot ring root (piW (ref.phys x.1)) ∧
    DigitAt ring x.2 x.2.clock (piD (ref.phys x.1)) x.2.current ∧
    WidthWriterValueReceipts ring root x.2 retired restart ∧
    WidthDigitLeaderReceipt ref x.1

/-- Complete pair `i` (from the first delimiter of the audit start) has a comparison completion
after `restart`.  Consumer: `WidthComparePairMoment`, `widthComparisonStageOfMoments`. -/
def WidthComparePairDone (root : Fin n) (restart i : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∀ first, DigitFirstDelimiter ring root x.2.start first →
    first + i * L3.ValueWaveClose.valueSpan n + 2 * L3.ValueWaveClose.valueSpan n < n →
    ∃ tm, DigitCompletion ring x.2 root (first + i * L3.ValueWaveClose.valueSpan n)
      (first + i * L3.ValueWaveClose.valueSpan n + L3.ValueWaveClose.valueSpan n)
      DigitLane.comparison restart tm

/-- **Lemma e-max's per-pair input on the comparison lane, restarted at the digit-stability
cut**: from every values-stable state, the first comparison completion of pair `i` after
`restart` has `E[z^T] ≤ 40`, `z = N/(N-1)`.  Consumer: `widthComparisonStageOfMoments`,
`smallComparisonClockOfMoments` and the SMALL comparison premise of
`l3HeadlineOfCleanBranches`. -/
def WidthComparePairMoment (N : Nat) : Prop :=
  ∀ (root : Fin n) (restart i : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    WidthStableRun ref root restart x → ¬ WidthComparePairDone ref root restart i x →
      MomentBound (widthDigitAuditNext ref) (WidthComparePairDone ref root restart i) N 40 x

/-- **Comparison close**: on a continuation of a values-stable state at which every complete
pair has its comparison completion after `restart`, the comparison cut holds.  Consumer:
`widthComparisonStageOfMoments`, `smallComparisonClockOfMoments` and the SMALL comparison
premise of `l3HeadlineOfCleanBranches`. -/
def WidthComparisonClose : Prop :=
  ∀ (root : Fin n) (restart : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (w : List (Fin n)),
    WidthStableRun ref root restart x →
    (∀ i, WidthComparePairDone ref root restart i (w.foldl (widthDigitAuditNext ref) x)) →
    WidthWriterComparisonCut ref (w.foldl (widthDigitAuditNext ref) x).1

/-- The comparison obligation persists.  Consumer: `widthComparisonStageOfMoments`. -/
theorem widthComparePairDoneStep (root : Fin n) (restart i : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : WidthComparePairDone ref root restart i x) :
    WidthComparePairDone ref root restart i (widthDigitAuditNext ref x e) := by
  intro first hf hend
  obtain ⟨tm, htm⟩ := h first hf hend
  exact ⟨tm, L3.FiveTransfer.completionStep ring _ x.2 e root _ _ _ restart tm htm⟩

/-- Pairs `i ≥ ⌊n/r⌋` are not complete.  Consumer: `widthComparisonStageOfMoments`. -/
theorem comparePairVacuous (hn : 5 ≤ n) (root : Fin n) (restart i : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hi : n / L3.ValueWaveClose.valueSpan n ≤ i) :
    WidthComparePairDone ref root restart i x := by
  intro first _ hend
  exfalso
  have hR := L3.ValueWaveClose.valueSpanTwo hn
  generalize L3.ValueWaveClose.valueSpan n = R at hR hi hend
  have hdm := Nat.div_add_mod n R
  have hmod := Nat.mod_lt n (by omega : 0 < R)
  have hmul : n / R * R ≤ i * R := Nat.mul_le_mul_right R hi
  have hc : R * (n / R) = n / R * R := Nat.mul_comm _ _
  omega

/-- **The comparison-lane e-max stage, both bands**: per-pair comparison moments at `N`, the
comparison close and the certificate `⌊n/r⌋ · 40 · (N-1)^t ≤ N^t` give the comparison clock at
charge `2 t`.  Consumer: `smallComparisonClockOfMoments`. -/
theorem widthComparisonStageOfMoments (hn : 5 ≤ n) (N t : Nat) (hN : 2 ≤ N)
    (hmom : WidthComparePairMoment ref N) (hclose : WidthComparisonClose ref)
    (hcert : n / L3.ValueWaveClose.valueSpan n * 40 * (N - 1) ^ t ≤ N ^ t) :
    WidthWriterComparisonClock ref (2 * t) := by
  intro z hz T
  obtain ⟨start, word, root, audit, retired, restart, hst, hfold, hW, hDA, hrec⟩ := hz
  have hx : WidthStableRun ref root restart (z, audit) :=
    ⟨start, word, retired, hst, hfold, hW, hDA, hrec⟩
  have hsim := simultaneousOfMoments (widthDigitAuditNext ref)
    (fun (i : Fin (n / L3.ValueWaveClose.valueSpan n)) y =>
      WidthComparePairDone ref root restart i.val y) N 40 t hN
    (fun i y e h => widthComparePairDoneStep ref root restart _ y e h) (z, audit)
    (fun i hng => hmom root restart i.val (z, audit) hx hng) hcert T
  let I : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n → Prop :=
    fun y => ∃ w : List (Fin n), y = w.foldl (widthDigitAuditNext ref) (z, audit)
  have hI0 : I (z, audit) := ⟨[], rfl⟩
  have hIstep : ∀ y, I y → ∀ e, I (widthDigitAuditNext ref y e) := by
    rintro y ⟨w, rfl⟩ e
    exact ⟨w ++ [e], by rw [List.foldl_append]; rfl⟩
  have hB : ∀ y, (I y ∧ ∀ i : Fin (n / L3.ValueWaveClose.valueSpan n),
      WidthComparePairDone ref root restart i.val y) → WidthWriterComparisonCut ref y.1 := by
    rintro y ⟨⟨w, rfl⟩, hgood⟩
    refine hclose root restart (z, audit) w hx (fun i => ?_)
    by_cases hi : i < n / L3.ValueWaveClose.valueSpan n
    · exact hgood ⟨i, hi⟩
    · exact comparePairVacuous ref hn root restart i _ (by omega)
  have hstop := costNumeratorTargetOnClosed (widthDigitAuditNext ref) I
    (fun y => I y ∧ ∀ i : Fin (n / L3.ValueWaveClose.valueSpan n),
      WidthComparePairDone ref root restart i.val y)
    (fun y => ∀ i : Fin (n / L3.ValueWaveClose.valueSpan n),
      WidthComparePairDone ref root restart i.val y)
    (fun y hy e => hIstep y hy e) (fun y hy hq => ⟨hy, hq⟩) T (z, audit) hI0
  have hproj := L3.Projection.costProjectLe ref.next (widthDigitAuditNext ref) Prod.fst
    (fun _ _ => rfl) (WidthWriterComparisonCut ref)
    (fun y => I y ∧ ∀ i : Fin (n / L3.ValueWaveClose.valueSpan n),
      WidthComparePairDone ref root restart i.val y) hB (z, audit) T
  calc 2 * costNumerator ref.next (WidthWriterComparisonCut ref) z T
      ≤ 2 * (n ^ T * t) := Nat.mul_le_mul_left 2 (Nat.le_trans hproj (Nat.le_trans hstop hsim))
    _ = n ^ T * (2 * t) := Nat.mul_left_comm _ _ _

end Generic

/-- **The SMALL comparison clock from comparison-lane moments**: `widthComparisonStageOfMoments`
at `N = widthPairMomentWidth n`, `t = ⌊c n² / 2⌋`, `c = smallDigitWriterTable q` (certificate
`smallWriterCertificate`), within the slot `smallDigitCompareTable q`.  Consumer:
`L3.WriterCore.writerDigitHalfOfBand` (its SMALL comparison input). -/
theorem smallComparisonClockOfMoments {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hs : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hmom : WidthComparePairMoment (bandWidthDigitReference ring hn) (widthPairMomentWidth n))
    (hclose : WidthComparisonClose (bandWidthDigitReference ring hn)) :
    WidthWriterComparisonClock (bandWidthDigitReference ring hn)
      (widthDigitBandCharge n smallDigitCompareTable (bankRepairDigitComparisonMicroCharge n)) := by
  rw [widthDigitBandChargeSmall _ _ hs]
  have hstage := widthComparisonStageOfMoments (bandWidthDigitReference ring hn) hn
    (widthPairMomentWidth n) (smallDigitWriterTable (ceilLogTwo n) * n ^ 2 / 2)
    (widthPairMomentWidthTwo (by omega)) hmom hclose
    (L3.PairMomentCert.smallWriterCertificate hn hs)
  refine bankRepairDigitChargedMono _ _ _ ?_ hstage
  have h2 := Nat.mul_div_le (smallDigitWriterTable (ceilLogTwo n) * n ^ 2) 2
  unfold smallDigitCompareTable
  omega

end L3.CompareStage

#print axioms L3.CompareStage.widthComparisonStageOfMoments
#print axioms L3.CompareStage.smallComparisonClockOfMoments
