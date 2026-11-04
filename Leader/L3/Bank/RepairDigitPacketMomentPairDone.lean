import Leader.L3.Bank.RepairDigitPacketMomentAttempt

/-!
# Lemma e-packet: the completion of one pair as `WidthPairDone`

`L3.PacketMomentAttempt.attemptMoment` bounds the first `DigitCompletion` of a pair
`(src, src + R)` (`PairDone`). The per-pair obligation `L3.DigitCohortScratch.WidthPairDone` asks
for the completion of pair `i` from the first delimiter of the audit start; `PairOfFirst` is its
body at the BANK reference, written with `digitSpan` for `valueSpan n` (both are
`digitSpan (compileAdvice (ceilLogTwo n))` by definition), so that this module does not import the
`WidthPairDone` module; the consumer reads
`PairOfFirst` as `WidthPairDone` by `show`/`exact`. The first delimiter
is unique (`firstDelimUnique`), so with `src = first + i * valueSpan n`, `R = valueSpan n` the two
agree (`widthPairDoneOf`), and the audit start is fixed along the chain, so every moment bound of
`PairDone` is one of `WidthPairDone` (`pairMomentWidth`).
-/

namespace L3.PacketMomentPairDone

set_option autoImplicit false

open L3
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.PacketMomentPrep
open L3.PacketMomentGroupLabels
open L3.PacketMomentAttempt

/-- The body of `L3.DigitCohortScratch.WidthPairDone` at pair index `i`. Consumer:
`widthPairDoneOf`, `pairMomentWidth`. -/
def PairOfFirst {n : Nat} {ring : DirectedRing n} {hbank : (compileAdvice (ceilLogTwo n)).useSmall = false}
    (root : Fin n) (i : Nat) (lane : DigitLane)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∀ first, DigitFirstDelimiter ring root x.2.start first →
    first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
      2 * digitSpan (compileAdvice (ceilLogTwo n)) < n →
    ∃ tm, DigitCompletion ring x.2 root (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
      (first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
        digitSpan (compileAdvice (ceilLogTwo n))) lane 0 tm

section Coupled

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat)

/-! ### The pair of `WidthPairDone` -/

/-- The first delimiter is unique. Consumer: `widthPairDoneOf`. -/
theorem firstDelimUnique {c : Compiled} (S : Fin n → ProjD c) (f f' : Nat)
    (hf : DigitFirstDelimiter ring root S f) (hf' : DigitFirstDelimiter ring root S f') :
    f = f' := by
  rcases Nat.lt_trichotomy f f' with h | h | h
  · have h1 := hf'.2 f hf.1.1 h
    rw [hf.1.2.2] at h1
    cases h1
  · exact h
  · have h1 := hf.2 f' hf'.1.1 h
    rw [hf'.1.2.2] at h1
    cases h1

/-- **The completion of the pair is `WidthPairDone`** (`PairOfFirst`) for the pair index `i` of the first
delimiter of the audit start. Consumer: `pairMomentWidth`. -/
theorem widthPairDoneOf (i first0 : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hf0 : DigitFirstDelimiter ring root x.2.start first0)
    (hsrc : src = first0 + i * digitSpan (compileAdvice (ceilLogTwo n)))
    (hRv : R = digitSpan (compileAdvice (ceilLogTwo n))) (h : PairDone ring hbank root lane src R x) :
    PairOfFirst (ring := ring) (hbank := hbank) root i lane x := by
  intro first hf _
  have he := firstDelimUnique ring root _ first first0 hf hf0
  subst he
  subst hsrc
  subst hRv
  exact h

/-- **The moment of the pair completion is a moment of `WidthPairDone`** (`PairOfFirst`): the audit start, hence
its first delimiter, is fixed along the chain. Consumer: the per-pair moment
(`WidthStrictPairMoment` at BANK). -/
theorem pairMomentWidth (i first0 : Nat) (N a b : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hf0 : DigitFirstDelimiter ring root x.2.start first0)
    (hsrc : src = first0 + i * digitSpan (compileAdvice (ceilLogTwo n)))
    (hRv : R = digitSpan (compileAdvice (ceilLogTwo n)))
    (h : MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (PairDone ring hbank root lane src R) N a b x) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (PairOfFirst (ring := ring) (hbank := hbank) root i lane)
      N a b x := by
  have hk := momentKeep (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) _
    (fun y => y.2.start = x.2.start) N a b (fun y e hy => hy) x rfl h
  exact momentWeaken _ _ _ N a b (fun y hy => widthPairDoneOf ring hbank root lane src R i
    first0 y (by rw [hy.2]; exact hf0) hsrc hRv hy.1) x hk

end Coupled

end L3.PacketMomentPairDone

#print axioms L3.PacketMomentPairDone.firstDelimUnique
#print axioms L3.PacketMomentPairDone.widthPairDoneOf
#print axioms L3.PacketMomentPairDone.pairMomentWidth
