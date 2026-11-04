import Leader.L3.Bank.RepairDigitPacketMomentCutEntry
import Leader.L3.Width.DigitCompareStage
import Leader.L3.Width.DigitPairMomentBank

/-!
# The BANK comparison clock (`hcompareBank`) from the comparison-lane per-pair moments

repair.tex 1743-1749: the comparison observer restarts at the digit-stability cut, the clock
`restart` of the writer value receipts; Lemma e-max runs on the comparison lane with completions
after `restart` (`DigitCompletion … .comparison restart`). The BANK chain:

* `stableRunInv`: on a values-stable state (`WidthStableRun`, a continuation of a clean start),
  every interior pair of the first delimiter has the run invariant (`RunInv`) on the comparison
  lane.
* `CmpPairStage a b` (the pre-attempt stage obligation on the comparison lane, after the
  restart): from every values-stable state, for every interior pair not yet completed after
  `restart`, `E[z^τ] ≤ a/b` to its completion after `restart` or to the mobile-free cut with
  labels stamped after `restart` (`LaneCutC restart`). `CmpPairStageW`: at a factor `w^B`,
  `B ≤ 3 C_r`.
* `comparePairMoment`: `WidthComparePairMoment` at BANK, `N = widthPairMomentWidth n`, from
  `CmpPairStageW` (`pairMomentOfStageC` with the cut `restart`, `stagePow`).
* `cmpCert`: `⌊n/r⌋ · 40 · (N-1)^t ≤ N^t` at `t = N (L + 6)` (`momentBlocks`, `pairMomentCount`);
  `cmpChargeLe`: `2 N (L + 6) ≤ bankRepairDigitComparisonMicroCharge n`.
* `hcompareBankOfStage`: the headline premise `hcompareBank` from `CmpPairStageW` and
  `WidthComparisonClose` at BANK (`L3.CompareStage.widthComparisonStageOfMoments`).
-/

namespace L3.PacketMomentCompareBank

set_option autoImplicit false

open L3
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.PacketMomentPrep
open L3.PacketMomentCells
open L3.PacketMomentGroupLabels
open L3.PacketMomentAttempt
open L3.PacketMomentPairDone
open L3.PacketMomentPairEntry
open L3.PacketMomentCutAttempt
open L3.PacketMomentCutEntry
open L3.CompareStage
open L3.WriterValueCuts
open L3.PairMomentPremise

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

include hn in
/-- **The run invariant at a values-stable state** on the comparison lane. Consumer:
`comparePairMoment`. -/
theorem stableRunInv (root : Fin n) (restart : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthStableRun (bankWidthDigitReference ring hn hbank) root restart x) (first : Nat)
    (hf : DigitFirstDelimiter ring root x.2.start first) (i : Nat)
    (hend : first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
      2 * digitSpan (compileAdvice (ceilLogTwo n)) < n) :
    2 ≤ first + i * digitSpan (compileAdvice (ceilLogTwo n)) ∧
      RunInv ring hbank root DigitLane.comparison
        (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
        (digitSpan (compileAdvice (ceilLogTwo n))) x := by
  obtain ⟨start, word, _, hs, hfold, hW, -, -⟩ := hx
  have hfold' : word.foldl (nxt ring hn hbank) (start, digitAuditInitial (piD start.val.1)) = x :=
    hfold
  have hst : x.2.start = piD start.val.1 := by
    rw [← hfold', foldStart ring hn hbank word]
    rfl
  have hW' : WFixedRoot ring root (piW (word.foldl (bankRepairNext ring hbank) start).val.1) := by
    have h1 := foldFst ring hn hbank word (start, digitAuditInitial (piD start.val.1))
    rw [hfold'] at h1
    rw [← h1]
    exact hW
  rw [hst] at hf
  obtain ⟨h2, hI⟩ := cleanRunStart ring hn hbank root DigitLane.comparison start hs.1 hs.2
    word hW' first hf i hend
  refine ⟨h2, ?_⟩
  rw [← hfold']
  have hR := bankRepairDigitLeadSpanTwo hbank
  exact runInvFold ring hn hbank root _ _ _ (by omega) h2 hend word _ hI

/-- **The comparison-lane stage obligation after the restart.** Consumer: `CmpPairStageW`,
`comparePairMoment`. -/
def CmpPairStage (a b : Nat) : Prop :=
  ∀ (root : Fin n) (restart i first : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    WidthStableRun (bankWidthDigitReference ring hn hbank) root restart x →
    DigitFirstDelimiter ring root x.2.start first →
    first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
      2 * digitSpan (compileAdvice (ceilLogTwo n)) < n →
    ¬ PairDoneC ring hbank root DigitLane.comparison
      (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
      (digitSpan (compileAdvice (ceilLogTwo n))) restart x →
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => PairDoneC ring hbank root DigitLane.comparison
          (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
          (digitSpan (compileAdvice (ceilLogTwo n))) restart y ∨
        LaneCutC ring hbank root DigitLane.comparison
          (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
          (digitSpan (compileAdvice (ceilLogTwo n))) restart y)
      (n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1)) a b x

/-- **The comparison-lane stage obligation at a factor `w^B`, `B ≤ 3 C_r`.** Consumer:
`comparePairMoment`, `hcompareBankOfStage`. -/
def CmpPairStageW : Prop :=
  ∃ B, B ≤ 3 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) ∧
    CmpPairStage ring hn hbank
      ((n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1)) ^ B)
      ((n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1) - n) ^ B)

/-- A completion of the pair of the first delimiter after `restart` is `WidthComparePairDone`
(the first delimiter is unique). Consumer: `comparePairMoment`. -/
theorem compareDoneOf (root : Fin n) (restart i first : Nat)
    (x y : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hf : DigitFirstDelimiter ring root x.2.start first) (hy : y.2.start = x.2.start)
    (h : PairDoneC ring hbank root DigitLane.comparison
      (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
      (digitSpan (compileAdvice (ceilLogTwo n))) restart y) :
    WidthComparePairDone (bankWidthDigitReference ring hn hbank) root restart i y := by
  intro f hf' _
  have he := firstDelimUnique ring root _ f first hf' (by rw [hy]; exact hf)
  subst he
  exact h

include hn in
/-- **`WidthComparePairMoment` at BANK** (`N = widthPairMomentWidth n`) from the comparison-lane
stage obligation. Consumer: `hcompareBankOfStage`. -/
theorem comparePairMoment
    (hst : CmpPairStageW ring hn hbank) :
    WidthComparePairMoment (bankWidthDigitReference ring hn hbank) (widthPairMomentWidth n) := by
  obtain ⟨B, hB, hs⟩ := hst
  intro root restart i x hx hnd
  obtain ⟨first, hf, hend, hno⟩ : ∃ first, DigitFirstDelimiter ring root x.2.start first ∧
      first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
        2 * digitSpan (compileAdvice (ceilLogTwo n)) < n ∧
      ¬ PairDoneC ring hbank root DigitLane.comparison
        (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
        (digitSpan (compileAdvice (ceilLogTwo n))) restart x := by
    refine Classical.byContradiction fun hcon => hnd ?_
    intro first hf hend
    exact Classical.byContradiction fun hno => hcon ⟨first, hf, hend, hno⟩
  obtain ⟨h2, hI⟩ := stableRunInv ring hn hbank root restart x hx first hf i hend
  have h7 := spanSeven hbank
  have hq := pairMomentOfStageC ring hn hbank root DigitLane.comparison _ _ h7 h2 hend restart x hI
    _ _ (hs root restart i first x hx hf hend hno)
  have hk := momentKeep (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) _
    (fun y => y.2.start = x.2.start) _ _ _ (fun y e hy => hy) x rfl hq
  have hw := momentWeaken _ _ (WidthComparePairDone (bankWidthDigitReference ring hn hbank) root
    restart i) _ _ _ (fun y hy => compareDoneOf ring hn hbank root restart i first x y hf hy.2 hy.1)
    x hk
  have hC := L3.PacketMomentWide.pairClockLarge _ h7
  show L3.PairMoment.MomentBound _ _
    (n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) + 1)) 40 x
  have hab := stagePow (n * (2 * bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n)))
    + 1)) n _ B (by omega) hC (Nat.le_refl _) hB
  generalize bankRepairDigitPairClock (digitSpan (compileAdvice (ceilLogTwo n))) = C at hw hC hab ⊢
  have hNn : 0 < n * (2 * C + 1) - n := by
    have : n * 2 ≤ n * (2 * C + 1) := Nat.mul_le_mul_left n (by omega)
    omega
  refine momentBoundOfQ _ _ _ _ _ 40 x (Nat.mul_pos (Nat.pow_pos hNn) (Nat.pow_pos hNn)) ?_ hw
  generalize (n * (2 * C + 1)) ^ B = a at hab ⊢
  generalize (n * (2 * C + 1) - n) ^ B = b at hab ⊢
  generalize (n * (2 * C + 1) - n) ^ C = p
  have h6 : 6 * a ≤ 40 * b := by omega
  have e1 : a * (6 * p) = 6 * a * p := by ac_rfl
  have e2 : 40 * (b * p) = 40 * b * p := by ac_rfl
  rw [e1, e2]
  exact Nat.mul_le_mul_right p h6

include hn in
/-- **The e-max certificate on the comparison lane at BANK**: `⌊n/r⌋ · 40 · (N-1)^t ≤ N^t` at
`t = N (L + 6)`, `N = widthPairMomentWidth n`, `L = ceilLogTwo n`. Consumer:
`hcompareBankOfStage`. -/
theorem cmpCert :
    n / L3.ValueWaveClose.valueSpan n * 40 *
        (widthPairMomentWidth n - 1) ^ (widthPairMomentWidth n * (ceilLogTwo n + 6)) ≤
      widthPairMomentWidth n ^ (widthPairMomentWidth n * (ceilLogTwo n + 6)) := by
  have hN := widthPairMomentWidthTwo (n := n) (by omega)
  have hb := L3.PairMoment.momentBlocks (widthPairMomentWidth n) hN (ceilLogTwo n + 6)
  have hc := L3.PairMomentBank.pairMomentCount hn
  have hK : n / L3.ValueWaveClose.valueSpan n ≤ 2 * n := by
    have := Nat.div_le_self n (L3.ValueWaveClose.valueSpan n)
    omega
  generalize widthPairMomentWidth n = N at hN hb ⊢
  generalize ceilLogTwo n + 6 = j at hb hc ⊢
  generalize n / L3.ValueWaveClose.valueSpan n = K at hK ⊢
  have hj : K * 40 * 2 ^ j ≤ 5 ^ j :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right 40 hK)) hc
  have h1 : K * 40 * (N - 1) ^ (N * j) * 2 ^ j ≤ 5 ^ j * (N - 1) ^ (N * j) := by
    rw [Nat.mul_right_comm]
    exact Nat.mul_le_mul_right _ hj
  have h2 : 2 ^ j * (K * 40 * (N - 1) ^ (N * j)) ≤ 2 ^ j * N ^ (N * j) := by
    rw [Nat.mul_comm (2 ^ j)]
    exact Nat.le_trans h1 hb
  exact Nat.le_of_mul_le_mul_left h2 (Nat.pow_pos (by decide))

include hbank in
/-- **The comparison charge fits**: `2 N (L + 6) ≤ 2 · P(s) · n`
(`bankRepairDigitComparisonMicroCharge`), from `2 C_r + 1 ≤ h(r)` and `L ≤ 2^s`, `s = ⌈log₂ L⌉`.
Consumer: `hcompareBankOfStage`. -/
theorem cmpChargeLe :
    2 * (widthPairMomentWidth n * (ceilLogTwo n + 6)) ≤ bankRepairDigitComparisonMicroCharge n := by
  have hq : 80 ≤ ceilLogTwo n := bankRepairBankBand hbank
  have ht : (compileAdvice (ceilLogTwo n)).t = ceilLogTwo (ceilLogTwo n) :=
    compileAdvice_t_large _ (by omega)
  have hL := (ceilLogTwo_spec (ceilLogTwo n) (by omega)).2
  have hs1 : 1 ≤ ceilLogTwo (ceilLogTwo n) := by
    have := ceilLogTwo_ge_six (ceilLogTwo n) (by omega)
    omega
  unfold widthPairMomentWidth bankRepairDigitComparisonMicroCharge bankRepairDigitPairUpper
    bankRepairDigitExponent
  rw [ht]
  have hE : 2 ^ ceilLogTwo (ceilLogTwo n) = 2 * 2 ^ (ceilLogTwo (ceilLogTwo n) - 1) := by
    rw [← Nat.pow_succ', show (ceilLogTwo (ceilLogTwo n) - 1).succ = ceilLogTwo (ceilLogTwo n) by
      omega]
  rw [hE] at hL
  generalize bankRepairDigitRadius (ceilLogTwo (ceilLogTwo n)) = r
  generalize 2 ^ (ceilLogTwo (ceilLogTwo n) - 1) = E at hL ⊢
  generalize ceilLogTwo n = L at hL ⊢
  have hCh : 2 * bankRepairDigitPairClock r + 1 ≤ bankRepairDigitPairEnvelope r := by
    unfold bankRepairDigitPairClock bankRepairDigitPairEnvelope
    omega
  generalize bankRepairDigitPairClock r = C at hCh ⊢
  generalize bankRepairDigitPairEnvelope r = h at hCh ⊢
  have a1 : n * (2 * C + 1) ≤ n * h := Nat.mul_le_mul_left n hCh
  have a2 : n * (2 * C + 1) * (L + 6) ≤ n * h * (2 * E + 6) := Nat.mul_le_mul a1 (by omega)
  have e : 2 * (4 * h * (E + 3)) * n = 4 * (n * h * (2 * E + 6)) := by grind
  rw [e]
  omega

include hn in
/-- **The headline premise `hcompareBank`** from the comparison-lane stage obligation and the
comparison close at BANK. Consumer: `hcompareBank` of `l3HeadlineOfCleanBranches`
(HeadlineCleanAssembly). -/
theorem hcompareBankOfStage
    (hst : CmpPairStageW ring hn hbank)
    (hclose : WidthComparisonClose (bankWidthDigitReference ring hn hbank)) :
    WidthWriterComparisonClock (bankWidthDigitReference ring hn hbank)
      (bankRepairDigitComparisonMicroCharge n) :=
  bankRepairDigitChargedMono _ _ _ (cmpChargeLe hbank)
    (widthComparisonStageOfMoments (bankWidthDigitReference ring hn hbank) hn
      (widthPairMomentWidth n) (widthPairMomentWidth n * (ceilLogTwo n + 6))
      (widthPairMomentWidthTwo (by omega)) (comparePairMoment ring hn hbank hst) hclose
      (cmpCert hn))

end L3.PacketMomentCompareBank

#print axioms L3.PacketMomentCompareBank.stableRunInv
#print axioms L3.PacketMomentCompareBank.compareDoneOf
#print axioms L3.PacketMomentCompareBank.comparePairMoment
#print axioms L3.PacketMomentCompareBank.cmpCert
#print axioms L3.PacketMomentCompareBank.cmpChargeLe
#print axioms L3.PacketMomentCompareBank.hcompareBankOfStage
