import Leader.L3.Width.DigitCleanCore
import Leader.L3.Bank.RepairDigitStructuralClean
import Leader.L3.Bank.RepairDigitEntryClose
import Leader.L3.Bank.RepairDigitStructuralFit
import Leader.L3.Width.DigitPairMomentBank

/-!
# The R10c digit premises for the reference of the band

`bandWidthDigitReference ring hn` is the digit reference of the advice band of `n`: the SMALL
reference when `useSmall = true`, the masked BANK reference otherwise.  The stage charges of
the band are `widthDigitBandCharge`: on SMALL a per-slice coefficient table times `n²`
, on BANK the BANK micro-charge.

The band composition of both clean digit halves from one premise list is
`L3.WriterCore.writerDigitHalfOfBand` (on the writer-lane cut family of `L3.WriterValueCuts`).
-/

namespace L3.WidthDigit

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock

set_option autoImplicit false

/-- The digit reference of the advice band.  Consumer: `L3.WriterCore.writerDigitHalfOfBand` and the
digit premises of `l3HeadlineOfCleanBranches`. -/
def bandWidthDigitReference {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n) :
    WidthDigitReference ring :=
  if h : (compileAdvice (ceilLogTwo n)).useSmall = true then
    smallWidthDigitReference ring hn h
  else bankWidthDigitReference ring hn (by simpa using h)

/-- Consumer: `L3.WriterCore.writerDigitHalfOfBand`. -/
theorem bandWidthDigitReferenceSmall {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hs : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    bandWidthDigitReference ring hn = smallWidthDigitReference ring hn hs := by
  unfold bandWidthDigitReference
  rw [dif_pos hs]

/-- Consumer: `L3.WriterCore.writerDigitHalfOfBand`. -/
theorem bandWidthDigitReferenceBank {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hb : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    bandWidthDigitReference ring hn = bankWidthDigitReference ring hn hb := by
  unfold bandWidthDigitReference
  rw [dif_neg (by simp [hb])]

/-- The charge of one digit stage on the band: the SMALL slice coefficient `slice q` times
`n²`, or the BANK micro-charge `bank`.  Consumer: the digit premises of
`widthCleanDigitHalfOfBand`. -/
def widthDigitBandCharge (n : Nat) (slice : Nat → Nat) (bank : Nat) : Nat :=
  if (compileAdvice (ceilLogTwo n)).useSmall then slice (ceilLogTwo n) * n ^ 2 else bank

/-- Consumer: `L3.WriterCore.writerDigitHalfOfBand`. -/
theorem widthDigitBandChargeSmall {n : Nat} (slice : Nat → Nat) (bank : Nat)
    (hs : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    widthDigitBandCharge n slice bank = slice (ceilLogTwo n) * n ^ 2 := by
  simp [widthDigitBandCharge, hs]

/-- Consumer: `L3.WriterCore.writerDigitHalfOfBand`. -/
theorem widthDigitBandChargeBank {n : Nat} (slice : Nat → Nat) (bank : Nat)
    (hb : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    widthDigitBandCharge n slice bank = bank := by
  simp [widthDigitBandCharge, hb]

end L3.WidthDigit

#print axioms L3.WidthDigit.bandWidthDigitReferenceSmall
#print axioms L3.WidthDigit.bandWidthDigitReferenceBank
