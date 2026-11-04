import Leader.L3.Width.DigitBoundary

/-!
# The SMALL digit slice tables and their fit

The SMALL digit stages are charged per advice slice `q = ceilLogTwo n` in `n²` units
(derivation below): boundary `widthBoundarySlice q`
(WidthDigitBoundary, the Lean boundary charge over the least ring size `N_q = 2^(q-1) + 1`),
first zero `smallDigitZeroTable q`, value wave `smallDigitWaveTable q`, comparison
`smallDigitCompareTable q`.  With `r = 2^t - 1`, `t = (compileAdvice q).t`, and
`C_r = bankRepairDigitPairClock r`, the derivation sets

* `z_q = ⌈2 [g(N_q, r) - 100]⌉ = ⌈6 r (3 + ln (3 N_q r)) / N_q⌉` (repair.tex `g(n,r) - 100`),
* `p_q = ⌈2 P_pair(N_q, r)⌉ = ⌈4 (2 C_r + 1) ln (40 N_q / r) / N_q⌉` (repair.tex `P_pair`), the
  two lanes of Lemma e-max together.

The two lanes are separate stages (repair.tex 1712-1717 and 1743-1749, ledger note
research/lean-l3/ledgers/SMALL-emax-notes.md): the writer lane before the wave, the comparison
lane after the digit-stability cut.  So the wave slot is `200 + smallDigitWriterTable q` (writer
e-max, certified per slice in `L3.PairMomentCert`, the entry clock `smallDigitEntryTable q`, then
the `100 n²` wave doubled) and the comparison slot is the same certified writer coefficient
(the comparison lane has the writer lane's width, pair count and per-pair moment; it replaces
the paper's `⌈p_q / 2⌉`, which it equals except at `q = 4`, one more, and `q ≤ 9`, below).

On `3 ≤ q ≤ 32` the first-zero table is the exact ceiling `smallDigitZeroFinite` (evaluated at
60 digits, every fractional gap at least 0.015).  On `q ≥ 33` it is the same formula with
`ln x` replaced by the integer upper bound `log₂`-exponent (`3 N_q r < 2^(q+t+2)`), so it
dominates the paper charge (`smallDigitZeroFormula`).  The paper's `p_q` table is no
longer a slot: both e-max lanes use the certified writer coefficients.

`smallDigitTablesFit`: the four tables plus the two dirty-drain half-units fit
`smallRepairDigitHalf n` on every SMALL ring.  On `q ≤ 32` the budget is the literal finite
reference table `headlineFiniteReference`, so the check is a `decide` over those slices
(the pattern of `headlineReferencePrefix_le`); on `q ≥ 33` it is structural (`t ∈ {6, 7}`,
every table at most 5 against a budget above 2·10⁵).
-/

namespace L3.WidthDigit

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock

set_option autoImplicit false

/-- First-zero coefficient `z_q = ⌈6 r (3 + ln (3 N_q r)) / N_q⌉` on `3 ≤ q ≤ 32` (`z_q = ⌈2[g(N_q,r) - 100]⌉`, repair.tex `g(n,r) - 100 = 3r[3 + ln(3nr)]/n`, exact ceiling).
Consumer: `smallDigitZeroTable`. -/
def smallDigitZeroFinite : Nat → Nat
  | 3 => 25
  | 4 => 15
  | 5 => 22
  | 6 => 13
  | 7 => 7
  | 8 => 4
  | 9 => 2
  | 10 => 2
  | _ => 1

/-- First-zero coefficient on `q ≥ 33`: `⌈6 r (3 + ln (3 N_q r)) / N_q⌉` with
`ln (3 N_q r) ≤ q + t + 2` (`3 N_q r < 2^(q+t+2)`).  Consumer: `smallDigitZeroTable`. -/
def smallDigitZeroFormula (q : Nat) : Nat :=
  (6 * (2 ^ (compileAdvice q).t - 1) * (3 + (q + (compileAdvice q).t + 2)) + 2 ^ (q - 1)) /
    (2 ^ (q - 1) + 1)

/-- The SMALL first-zero table (`n²` units).  Consumer: `smallDigitTablesFit` and the SMALL
first-zero premise of `l3HeadlineOfCleanBranches`. -/
def smallDigitZeroTable (q : Nat) : Nat :=
  if q ≤ 32 then smallDigitZeroFinite q else smallDigitZeroFormula q

/-- Writer-lane e-max coefficient on `3 ≤ q ≤ 32` (`n²` units, doubled): the least value for
which the per-slice certificate `40 ⌊n/r⌋ (N-1)^t ≤ N^t`, `t = ⌊c n² / 2⌋`,
`N = n (2 C_r + 1)`, holds on the whole slice by the piece list of
`L3.PairMomentCert.smallWriterPieces` (computed exactly; equal to `⌈p_q / 2⌉` except
`q = 4`, one more, and `q ≤ 9`, where it is below).  Consumer: `smallDigitWriterTable`. -/
def smallDigitWriterFinite : Nat → Nat
  | 3 => 1475
  | 4 => 943
  | 5 => 8360
  | 6 => 4926
  | 7 => 2820
  | 8 => 1587
  | 9 => 881
  | 10 => 484
  | 11 => 264
  | 12 => 143
  | 13 => 77
  | 14 => 41
  | 15 => 22
  | 16 => 12
  | 17 => 1447
  | 18 => 768
  | 19 => 406
  | 20 => 214
  | 21 => 113
  | 22 => 60
  | 23 => 31
  | 24 => 17
  | 25 => 9
  | 26 => 5
  | 27 => 3
  | 28 => 2
  | _ => 1

/-- The SMALL writer-lane e-max table: the finite certified coefficients, and `3` on `q ≥ 33`
(where `2 (2 C_r + 1) (q + 6) ≤ 3 n`).  Consumer: `smallDigitWaveTable`, `smallDigitCompareTable`,
`L3.PairMomentCert.smallWriterCertificate`. -/
def smallDigitWriterTable (q : Nat) : Nat :=
  if q ≤ 32 then smallDigitWriterFinite q else 3

/-- The SMALL entry coefficient: the entry clock from the writer cut to the pinned block cut
`P' 0` is charged `6 n (5 R + 2 + q)` as on BANK, i.e. `⌈6 (5 r + 2 + q) / N_q⌉ n²` on the
slice (`r = 2^t - 1`, `N_q = 2^(q-1) + 1`).  Consumer: `smallDigitWaveTable`,
`L3.WriterStage.smallEntryChargeLe`. -/
def smallDigitEntryTable (q : Nat) : Nat :=
  (6 * (5 * digitSpan (compileAdvice q) + 2 + q) + 2 ^ (q - 1)) / (2 ^ (q - 1) + 1)

/-- The SMALL value-wave table: the writer-lane e-max stage (`smallDigitWriterTable q`), the
entry clock (`smallDigitEntryTable q`) and the `100 n²` current-value wave after it, doubled
(`200`), as in repair.tex 1712-1717.  Consumer: `smallDigitTablesFit` and the SMALL wave
composition `L3.WriterStage.smallWaveClockOfWriter` feeding `l3HeadlineOfCleanBranches`. -/
def smallDigitWaveTable (q : Nat) : Nat :=
  200 + smallDigitWriterTable q + smallDigitEntryTable q

/-- The SMALL comparison table: the comparison lane alone, restarted at the digit-stability cut
(repair.tex 1743-1749).  Its per-pair moment, pair count and width `N` are the writer lane's, so
the certified writer coefficient serves (`L3.CompareStage.smallComparisonClockOfMoments`).
Consumer: `smallDigitTablesFit` and the SMALL comparison input of `l3HeadlineOfCleanBranches`. -/
def smallDigitCompareTable (q : Nat) : Nat := smallDigitWriterTable q

/-- The fit on the finite slices `3 ≤ q ≤ 32`, where the budget is the literal reference table.
Consumer: `smallDigitTablesFit`. -/
theorem smallDigitTablesFitFinite :
    ∀ i : Fin 33, 3 ≤ i.val →
      widthBoundarySlice i.val + smallDigitZeroFinite i.val +
          (200 + smallDigitWriterFinite i.val + smallDigitEntryTable i.val) +
          smallDigitWriterFinite i.val + 2 ≤
        L3.SmallFinishClean.smallDigitHalfAt i.val := by
  decide

/-- The fit on `33 ≤ q ≤ 79` (`t ∈ {6, 7}`).  Consumer: `smallDigitTablesFit`. -/
theorem smallDigitTablesFitLarge (q : Nat) (h33 : 33 ≤ q) (h79 : q < 80) :
    widthBoundarySlice q + smallDigitZeroFormula q + (200 + 3 + smallDigitEntryTable q) +
        3 + 2 ≤
      L3.SmallFinishClean.smallDigitHalfAt q := by
  have ht : (compileAdvice q).t = ceilLogTwo q := compileAdvice_t_large q h33
  have hc := ceilLogTwo_spec q (by omega)
  have h32' : 2 ^ 32 ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have e32 : (2 : Nat) ^ 32 = 4294967296 := by decide
  have hN : 0 < 2 ^ (q - 1) + 1 := Nat.succ_pos _
  have hc67 : ceilLogTwo q = 6 ∨ ceilLogTwo q = 7 := by
    have hlo : 6 ≤ ceilLogTwo q := by
      by_cases h : 6 ≤ ceilLogTwo q
      · exact h
      · have : 2 ^ ceilLogTwo q ≤ 2 ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
        have e5 : (2 : Nat) ^ 5 = 32 := by decide
        omega
    have hhi : ceilLogTwo q ≤ 7 := by
      by_cases h : ceilLogTwo q ≤ 7
      · exact h
      · have : 2 ^ 7 ≤ 2 ^ (ceilLogTwo q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have e7 : (2 : Nat) ^ 7 = 128 := by decide
        omega
    omega
  have h32 : ¬ q ≤ 32 := by omega
  rcases hc67 with hc6 | hc7
  · have e6 : (2 : Nat) ^ 6 = 64 := by decide
    have hq64 : q ≤ 64 := by rw [hc6] at hc; omega
    have hb : widthBoundarySlice q < 2 := by
      unfold widthBoundarySlice widthBoundarySliceNumerator widthBoundarySliceWidth
      have eL : bankRepairDigitLeadingLength 6 = 130 := by decide
      have eJ : bankRepairDigitBoundaryServices 6 = 1223319 := by decide
      have eX : bankRepairDigitForwardCount (bankRepairDigitRadius 6) +
          bankRepairDigitReturnCount (bankRepairDigitRadius 6) +
          bankRepairDigitSettledCount (bankRepairDigitRadius 6) + bankRepairDigitRadius 6 =
            132073328 := by decide
      rw [ht, hc6, eL, eJ, eX]
      exact (Nat.div_lt_iff_lt_mul hN).2 (by omega)
    have hz : smallDigitZeroFormula q < 2 := by
      unfold smallDigitZeroFormula
      rw [ht, hc6, e6]
      exact (Nat.div_lt_iff_lt_mul hN).2 (by omega)
    have hE : smallDigitEntryTable q < 2 := by
      unfold smallDigitEntryTable digitSpan
      rw [ht, hc6, e6]
      exact (Nat.div_lt_iff_lt_mul hN).2 (by omega)
    have hH : 300 ≤ L3.SmallFinishClean.smallDigitHalfAt q := by
      unfold L3.SmallFinishClean.smallDigitHalfAt headlineReferenceFinishRate
        headlineReferenceRate headlineInheritedRate
      rw [if_neg h32, if_neg h32, ht, hc6, if_pos rfl, if_pos rfl]
      decide
    omega
  · have hne : ¬ (7 : Nat) = 6 := by decide
    have e7 : (2 : Nat) ^ 7 = 128 := by decide
    have hq65 : 65 ≤ q := by
      rw [hc7] at hc
      have e6 : (2 : Nat) ^ 6 = 64 := by decide
      omega
    have h64 : 2 ^ 64 ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have e64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
    have hb : widthBoundarySlice q < 2 := by
      unfold widthBoundarySlice widthBoundarySliceNumerator widthBoundarySliceWidth
      have eL : bankRepairDigitLeadingLength 7 = 259 := by decide
      have eJ : bankRepairDigitBoundaryServices 7 = 9228714 := by decide
      have eX : bankRepairDigitForwardCount (bankRepairDigitRadius 7) +
          bankRepairDigitReturnCount (bankRepairDigitRadius 7) +
          bankRepairDigitSettledCount (bankRepairDigitRadius 7) + bankRepairDigitRadius 7 =
            2130513648 := by decide
      rw [ht, hc7, eL, eJ, eX]
      exact (Nat.div_lt_iff_lt_mul hN).2 (by omega)
    have hz : smallDigitZeroFormula q < 2 := by
      unfold smallDigitZeroFormula
      rw [ht, hc7, e7]
      exact (Nat.div_lt_iff_lt_mul hN).2 (by omega)
    have hE : smallDigitEntryTable q < 2 := by
      unfold smallDigitEntryTable digitSpan
      rw [ht, hc7, e7]
      exact (Nat.div_lt_iff_lt_mul hN).2 (by omega)
    have hH : 300 ≤ L3.SmallFinishClean.smallDigitHalfAt q := by
      unfold L3.SmallFinishClean.smallDigitHalfAt headlineReferenceFinishRate
        headlineReferenceRate headlineInheritedRate
      rw [if_neg h32, if_neg h32, ht, hc7, if_neg hne, if_neg hne]
      decide
    omega

/-- **The SMALL slice tables fit the SMALL digit budget** on every SMALL ring: boundary
`widthBoundarySlice`, first zero, value wave and comparison tables plus the two dirty-drain
half-units are at most `smallRepairDigitHalf n`.  Consumer: `l3HeadlineOfCleanBranches`. -/
theorem smallDigitTablesFit {n : Nat} (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    widthBoundarySlice (ceilLogTwo n) + smallDigitZeroTable (ceilLogTwo n) +
        smallDigitWaveTable (ceilLogTwo n) + smallDigitCompareTable (ceilLogTwo n) + 2 ≤
      L3.SmallFinishRepair.smallRepairDigitHalf n := by
  obtain ⟨hlo, hhi⟩ := L3.SmallFinishClean.smallDigitSliceBounds hn hsmall
  rw [L3.SmallFinishClean.smallRepairDigitHalfAtSlice]
  generalize ceilLogTwo n = q at hlo hhi ⊢
  unfold smallDigitCompareTable smallDigitZeroTable smallDigitWaveTable smallDigitWriterTable
  by_cases h32 : q ≤ 32
  · simp only [if_pos h32]
    exact smallDigitTablesFitFinite ⟨q, by omega⟩ hlo
  · simp only [if_neg h32]
    exact smallDigitTablesFitLarge q (by omega) hhi

end L3.WidthDigit

#print axioms L3.WidthDigit.smallDigitTablesFitFinite
#print axioms L3.WidthDigit.smallDigitTablesFitLarge
#print axioms L3.WidthDigit.smallDigitTablesFit
