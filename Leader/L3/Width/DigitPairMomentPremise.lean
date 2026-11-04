import Leader.L3.Bank.RepairDigitAllPairsClock
import Leader.L3.Width.DigitPairMoment

/-!
# The per-pair premise of Lemma e-max, as an exponential moment

Lemma e-max (repair.tex `lem:e-max`, lines 1421-1465) consumes, for each complete pair on a
lane, the exponential moment `E[z^{T_pair}] < 40` at `z = N / (N - 1)`, `N = n (2 C_r + 1)`,
uniformly over legal states (its proof steps 1-6: geometric nominated-edge waits, preparation
moment `< 8`, padded attempts, the fair-race failure factorization, `M_j < 5`).  The first
moment `WidthStrictPairClock` (`E[T_pair] ≤ n h(r)`) does not imply it, and with only first
moments the union bound pays a factor about `8.7` over `ln K` (`simultaneousOfUniform`).

* `widthPairMomentWidth n`: `N = n (2 C_r + 1)` with `r = 2^t - 1`, `t` the advice width of the
  band of `n` (`C_r = bankRepairDigitPairClock`).
* `WidthStrictPairMoment ref N`: from every first-zero continuation of the audit restarted at
  the clean start, the first strict completion of pair `i` on `lane` has
  `E[z^T] ≤ 40` (`L3.PairMoment.MomentBound … N 40`), uniformly over the state.  Stated once,
  for both bands.  It is NOT proved here; it is the first missing fact of the digit stage.

Design decision: DESIGN-MOTIVATIONS (per-pair premise becomes a moment, 2026-11-02).
-/

namespace L3.PairMomentPremise

open L3
open L3.WidthDigit
open L3.DigitCohortScratch
open L3.RenewalReferenceClock

set_option autoImplicit false

/-- `N = n (2 C_r + 1)`, `r = 2^t - 1`, `t` the advice width of the band of `n`: the moment
parameter of Lemma e-max (`z = N / (N - 1)`).  Consumer: `WidthStrictPairMoment` at its two
band instances (`L3.PairMomentBank.widthStructuralClockOfMoments`, the SMALL writer lane). -/
def widthPairMomentWidth (n : Nat) : Nat :=
  n * (2 * bankRepairDigitPairClock (bankRepairDigitRadius (compileAdvice (ceilLogTwo n)).t) + 1)

/-- `N ≥ 2` for `n ≥ 1`.  Consumer: `L3.PairMomentBank.widthStructuralClockOfMoments`. -/
theorem widthPairMomentWidthTwo {n : Nat} (hn : 1 ≤ n) : 2 ≤ widthPairMomentWidth n := by
  unfold widthPairMomentWidth bankRepairDigitPairClock
  generalize bankRepairDigitRadius (compileAdvice (ceilLogTwo n)).t = r
  have h : 2 * 1 ≤ n * 2 := by omega
  have h2 : n * 2 ≤ n * (2 * (2 * r ^ 4 + 8 * r ^ 3 + 3 * r ^ 2 + 11 * r + 4) + 1) :=
    Nat.mul_le_mul_left n (by omega)
  omega

section Generic

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- **Lemma e-max's per-pair input, stated for both bands**: from every first-zero
continuation of the audit restarted at the clean start, the first strict completion of pair
`i` on `lane` has exponential moment `E[z^T] ≤ 40`, `z = N / (N - 1)`, uniformly over the
state.  Consumer: `L3.PairMomentBank.widthStructuralClockOfMoments` (BANK, `N =
widthPairMomentWidth n`) and the `hpair` premise of `l3HeadlineOfCleanBranches`. -/
def WidthStrictPairMoment (N : Nat) : Prop :=
  ∀ (root : Fin n) (i : Nat) (lane : DigitLane)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    WidthZeroRun ref root x → ¬ WidthPairDone ref root i lane x →
      L3.PairMoment.MomentBound (widthDigitAuditNext ref) (WidthPairDone ref root i lane) N 40 x

end Generic

end L3.PairMomentPremise

#print axioms L3.PairMomentPremise.widthPairMomentWidthTwo
