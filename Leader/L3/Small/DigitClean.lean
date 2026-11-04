import Leader.L3.Small.FinishClean
import Leader.L3.Width.DigitCore

/-!
# The SMALL clean digit half from a causal core

`SmallCleanDigitHalf ring` is the half-stage from `SmallCleanRFoldOnGuard`
to `SmallCleanDigit` at budget `smallRepairDigitHalf n`.  The composition
of the R10c digit wave (four charged stages, forward-closed pre-drain,
nominated-edge dirty rank) is band-free and lives in WidthDigitCore; here
it is instantiated on the SMALL successor `renewalSmallNext`.

Budget.  On every SMALL slice (3 ≤ q ≤ qStar = 79, q = ceilLogTwo n)
`203 ≤ smallRepairDigitHalf n` (minimum 221 at q = 29..32), so the SMALL
budget pays the BANK 201 + 2 split: any four charges with sum ≤ 201 n²
close the SMALL digit half (`smallCleanDigitHalfOfSplitCore`).

The BANK micro-charges themselves (ψ-envelopes, ψ = ceilLogTwo q, sum
2 ν(ψ) n + 200 n²) fit the BANK 201 n² only because 2 ν(ψ) < n on BANK.
On SMALL they fit the full SMALL budget (smallRepairDigitHalf n - 2) n²
iff 2 ν(ψ) ≤ (smallRepairDigitHalf n - 202) n
(`smallDigitBankChargesFitOfEnvelope`).  That holds on every slice
28 ≤ q ≤ 79 (`smallDigitBankChargesFit`, slice table by kernel decide), on
q = 27 only from n = 81972576 on, and fails for every n with q ≤ 26
(q = 3, n = 5: 495180 > 4129 · 25).
-/

namespace L3.SmallFinishClean

open L3
open L3.HeadlineRenewal
open L3.SmallRenewal
open L3.SmallFinishRepair
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The SMALL digit budget as a function of the advice slice q.
Consumer: `smallRepairDigitHalfAtSlice`. -/
def smallDigitHalfAt (q : Nat) : Nat :=
  2 * (headlineReferenceFinishRate q -
    (441 * (compileAdvice q).t + 275)) - 3

/-- `smallRepairDigitHalf n` is the slice budget at q = ceilLogTwo n.
Consumer: `smallRepairDigitHalfBankSplit`, `smallDigitBankChargesFit`. -/
theorem smallRepairDigitHalfAtSlice (n : Nat) :
    smallRepairDigitHalf n = smallDigitHalfAt (ceilLogTwo n) := rfl

/-- SMALL slices are 3 ≤ q ≤ 79.  Consumer: `smallRepairDigitHalfBankSplit`,
`smallDigitBankChargesFit`. -/
theorem smallDigitSliceBounds {n : Nat} (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    3 ≤ ceilLogTwo n ∧ ceilLogTwo n < 80 := by
  have hupper := (ceilLogTwo_spec n (by omega : 2 ≤ n)).2
  refine ⟨?_, ?_⟩
  · by_cases hlow : ceilLogTwo n ≤ 2
    · have hp : 2 ^ ceilLogTwo n ≤ 2 ^ 2 :=
        Nat.pow_le_pow_right (by omega) hlow
      have h4 : (2 : Nat) ^ 2 = 4 := by decide
      omega
    · omega
  · have he : (compileAdvice (ceilLogTwo n)).useSmall =
        decide (ceilLogTwo n ≤ qStar) := rfl
    rw [he] at hsmall
    have hq := of_decide_eq_true hsmall
    have hstar : qStar = 79 := rfl
    omega

/-- The SMALL digit budget pays the BANK 201 + 2 split on every SMALL
slice.  Consumer: `smallCleanDigitHalfOfSplitCore`. -/
theorem smallRepairDigitHalfBankSplit {n : Nat} (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    203 ≤ smallRepairDigitHalf n := by
  obtain ⟨hlo, hhi⟩ := smallDigitSliceBounds hn hsmall
  have hcheck : ∀ i : Fin 80, 3 ≤ i.val → 203 ≤ smallDigitHalfAt i.val := by
    decide +kernel
  rw [smallRepairDigitHalfAtSlice]
  exact hcheck ⟨ceilLogTwo n, hhi⟩ hlo

/-- The SMALL clean digit half from a causal core on the SMALL successor
whose four charges fit the full SMALL budget minus the two dirty-drain
half-units.  Consumer: `smallCleanDigitHalfOfSplitCore`,
`smallCleanDigitHalfOfBankChargedCore`, and the SMALL clean finish
(`SmallCleanDigitHalf` premise of smallCleanFinishReferenceOfStages). -/
theorem smallCleanDigitHalfOfCausalCore {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (preDrain : RenewalSmallReference n → Prop)
    (cuts : WidthDigitCuts (RenewalSmallReference n))
    (cb cz cw cc : Nat)
    (hfit : cb + cz + cw + cc ≤ (smallRepairDigitHalf n - 2) * n ^ 2)
    (hcore : WidthDigitCausalCore (renewalSmallNext ring)
      (SmallCleanRFoldOnGuard ring) preDrain (SmallCleanDigit ring) cuts
      cb cz cw cc) :
    SmallCleanDigitHalf ring := by
  have hbudget := smallRepairDigitHalfBankSplit hn hsmall
  have h := widthDigitHalfOfCausalCore (renewalSmallNext ring)
    (SmallCleanRFoldOnGuard ring) preDrain (SmallCleanDigit ring) cuts
    cb cz cw cc (smallRepairDigitHalf n - 2) hfit hcore
  have he : smallRepairDigitHalf n - 2 + 2 = smallRepairDigitHalf n := by
    omega
  unfold SmallCleanDigitHalf
  rw [he] at h
  exact h

/-- The SMALL clean digit half from a causal core whose charges fit the
BANK split 201 n², with the same 201 + 2 accounting as BANK, absorbed into
the larger SMALL budget.  Consumer: the SMALL clean finish, when the SMALL
digit clocks are charged inside 201 n². -/
theorem smallCleanDigitHalfOfSplitCore {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (preDrain : RenewalSmallReference n → Prop)
    (cuts : WidthDigitCuts (RenewalSmallReference n))
    (cb cz cw cc : Nat)
    (hfit : cb + cz + cw + cc ≤ 201 * n ^ 2)
    (hcore : WidthDigitCausalCore (renewalSmallNext ring)
      (SmallCleanRFoldOnGuard ring) preDrain (SmallCleanDigit ring) cuts
      cb cz cw cc) :
    SmallCleanDigitHalf ring :=
  widthDigitHalfBudgetMono (renewalSmallNext ring)
    (SmallCleanRFoldOnGuard ring) (SmallCleanDigit ring) 203
    (smallRepairDigitHalf n) (smallRepairDigitHalfBankSplit hn hsmall)
    (widthDigitHalfOfCausalCore (renewalSmallNext ring)
      (SmallCleanRFoldOnGuard ring) preDrain (SmallCleanDigit ring) cuts
      cb cz cw cc 201 hfit hcore)

/-- Slice table: from q = 28 on, twice the ψ-envelope sum is paid by the
SMALL budget beyond 202 half-units at the smallest population of the
slice.  Consumer: `smallDigitBankChargesFit`. -/
theorem smallDigitEnvelopeSliceFit :
    ∀ i : Fin 80, 28 ≤ i.val →
      202 ≤ smallDigitHalfAt i.val ∧
      2 * bankRepairDigitNu (ceilLogTwo i.val) ≤
        (smallDigitHalfAt i.val - 202) * (2 ^ (i.val - 1) + 1) := by
  decide +kernel

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 12000 in
/-- The BANK ψ-envelope micro-charges fit the SMALL digit budget minus the
dirty drain whenever twice the envelope sum is at most (budget - 202) n:
the SMALL analogue of BANK's 2 ν < n.  Consumer: `smallDigitBankChargesFit`
and SMALL slices checked by population (q = 27 holds from
n = 81972576 on). -/
theorem smallDigitBankChargesFitOfEnvelope {n : Nat}
    (hH : 202 ≤ smallRepairDigitHalf n)
    (hnu : 2 * bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) ≤
      (smallRepairDigitHalf n - 202) * n) :
    bankRepairDigitBoundaryMicroCharge n +
        bankRepairDigitFirstZeroMicroCharge n +
        bankRepairDigitValueWaveMicroCharge n +
        bankRepairDigitComparisonMicroCharge n ≤
      (smallRepairDigitHalf n - 2) * n ^ 2 := by
  generalize smallRepairDigitHalf n = H at hH hnu ⊢
  unfold bankRepairDigitBoundaryMicroCharge bankRepairDigitFirstZeroMicroCharge
    bankRepairDigitValueWaveMicroCharge bankRepairDigitComparisonMicroCharge
  unfold bankRepairDigitNu at hnu
  generalize bankRepairDigitBoundaryUpper (ceilLogTwo (ceilLogTwo n)) = b at hnu ⊢
  generalize bankRepairDigitValueUpper (ceilLogTwo (ceilLogTwo n)) = v at hnu ⊢
  generalize bankRepairDigitPairUpper (ceilLogTwo (ceilLogTwo n)) = p at hnu ⊢
  have hsum : 2 * b * n + 2 * v * n + 200 * n ^ 2 + 2 * p * n =
      (2 * (b + v + p)) * n + 200 * n ^ 2 := by
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have hmul : (2 * (b + v + p)) * n ≤ (H - 202) * n ^ 2 := by
    rw [Nat.pow_two, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right n hnu
  have hsplit : (H - 202) * n ^ 2 + 200 * n ^ 2 = (H - 2) * n ^ 2 := by
    rw [← Nat.add_mul]
    congr 1
    omega
  omega

/-- The BANK ψ-envelope micro-charges fit the SMALL digit budget minus the
dirty drain on the SMALL slices 28 ≤ q ≤ 79.  Consumer:
`smallCleanDigitHalfOfBankChargedCore`. -/
theorem smallDigitBankChargesFit {n : Nat} (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hq : 28 ≤ ceilLogTwo n) :
    bankRepairDigitBoundaryMicroCharge n +
        bankRepairDigitFirstZeroMicroCharge n +
        bankRepairDigitValueWaveMicroCharge n +
        bankRepairDigitComparisonMicroCharge n ≤
      (smallRepairDigitHalf n - 2) * n ^ 2 := by
  obtain ⟨_, hhi⟩ := smallDigitSliceBounds hn hsmall
  obtain ⟨hH, htab⟩ : 202 ≤ smallDigitHalfAt (ceilLogTwo n) ∧
      2 * bankRepairDigitNu (ceilLogTwo (ceilLogTwo n)) ≤
        (smallDigitHalfAt (ceilLogTwo n) - 202) *
          (2 ^ (ceilLogTwo n - 1) + 1) :=
    smallDigitEnvelopeSliceFit ⟨ceilLogTwo n, hhi⟩ hq
  have hpop := (ceilLogTwo_spec n (by omega : 2 ≤ n)).1
  rw [← smallRepairDigitHalfAtSlice] at hH htab
  exact smallDigitBankChargesFitOfEnvelope hH
    (Nat.le_trans htab (Nat.mul_le_mul_left _ (by omega)))

/-- The SMALL clean digit half from a causal core charged with the BANK
ψ-envelope micro-charges, on the slices 28 ≤ q.  Consumer: the SMALL
clean finish on those slices. -/
theorem smallCleanDigitHalfOfBankChargedCore {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hq : 28 ≤ ceilLogTwo n)
    (preDrain : RenewalSmallReference n → Prop)
    (cuts : WidthDigitCuts (RenewalSmallReference n))
    (hcore : WidthDigitCausalCore (renewalSmallNext ring)
      (SmallCleanRFoldOnGuard ring) preDrain (SmallCleanDigit ring) cuts
      (bankRepairDigitBoundaryMicroCharge n)
      (bankRepairDigitFirstZeroMicroCharge n)
      (bankRepairDigitValueWaveMicroCharge n)
      (bankRepairDigitComparisonMicroCharge n)) :
    SmallCleanDigitHalf ring :=
  smallCleanDigitHalfOfCausalCore ring hn hsmall preDrain cuts _ _ _ _
    (smallDigitBankChargesFit hn hsmall hq) hcore

end L3.SmallFinishClean

#print axioms L3.SmallFinishClean.smallRepairDigitHalfAtSlice
#print axioms L3.SmallFinishClean.smallDigitSliceBounds
#print axioms L3.SmallFinishClean.smallRepairDigitHalfBankSplit
#print axioms L3.SmallFinishClean.smallCleanDigitHalfOfCausalCore
#print axioms L3.SmallFinishClean.smallCleanDigitHalfOfSplitCore
#print axioms L3.SmallFinishClean.smallDigitEnvelopeSliceFit
#print axioms L3.SmallFinishClean.smallDigitBankChargesFitOfEnvelope
#print axioms L3.SmallFinishClean.smallDigitBankChargesFit
#print axioms L3.SmallFinishClean.smallCleanDigitHalfOfBankChargedCore
