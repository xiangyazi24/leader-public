import Leader.L3.Bank.WordCleanTransport

/-!
# Width W clean clock, part 1: the width leaves and the hard-epoch layer

One generic layer for the projected W chain, parameterized by the
compiled certificate width t = `(compileAdvice (ceilLogTwo n)).t` instead
of ψ = ceilLogTwo (ceilLogTwo n).  It is the SmallWordClean* port of the
BANK W cone with the width premise `t = ψ` removed: every renewal
constant is restated in t (lease 8t + 4 = the physical `siLeaseMax`,
worker quota 2t + 1, horizon 2(2t+1)n², block 11(8t+5)n², five blocks
(440t + 275)n²), and the moment rate is proved with C = 2t + 1.  The
only remaining band premise is `5 ≤ n`.  On BANK t = ψ, so these are
the BANK constants; on SMALL they are the physical ones.

The ψ-constants enter the cone through ten declarations, which are
restated here in t: `bankWordRenewalLease`, `bankWordRenewalWorkerQuota`,
`bankWordRenewalHorizon`, `bankWordRenewalBlock`,
`bankWordRenewalFiveCoefficient`, `bankWordRenewalWorkerNominationHalf`,
`BankWordRenewalFreshAttemptCost`, `BankWordEpochPostSOneWorkerClock`,
`BankWordEpochLapCount`, `BankWordRetryPrefixInvariant`.  Every other
reused declaration is generic in its constants.

This module: the start class, the width leaves, the ten restated
constants, and the ported BankRepairWord and BankWordRenewal*
declarations.
-/

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

/-! ## The start class and the width leaves -/

/-- The projected W start class of the width layer: the fixed physical
root (the band premise is carried only to keep the ported shapes).
Consumer: the `hs` premise of every ported epoch theorem,
`widthWordSerializerRootClassClosed`, `smallWordCleanWordClockOfSmall`. -/
def WidthWordSerializerRootClass {n : Nat}
    (ring : DirectedRing n)
    (_hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  WFixedRoot ring root s

/-- The start class is closed on every phiW edge and lies in the
fixed-root class (`bankRepairDigitWFixedRootPhiW`).  Consumer: the
ported S1 cost and fixed-root lemmas (`widthWordEpochSOneCost`,
`widthWordEpochFixedRoot`, the wave steps). -/
theorem widthWordSerializerRootClassClosed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n) :
    ClockSerializerNoRootLossFromG ring root
      (WidthWordSerializerRootClass ring hsmallFive root) := by
  refine ⟨fun _ hs => hs, fun s hs e => ?_⟩
  have h := bankRepairDigitWFixedRootPhiW (by omega : 3 ≤ n) ring root s e hs
  exact ⟨h, h⟩

/-- `3 ≤ ceilLogTwo n` for `5 ≤ n`.  Consumer: `widthWordPassWidth`. -/
theorem widthWordAdviceThree {n : Nat} (hsmallFive : 5 ≤ n) :
    3 ≤ ceilLogTwo n := by
  have hn := ceilLogTwo_spec n (by omega)
  rcases Nat.lt_or_ge (ceilLogTwo n) 3 with hc | hc
  · have hp : (2 : Nat) ^ ceilLogTwo n ≤ 2 ^ 2 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : (2 : Nat) ^ 2 = 4 := by decide
    omega
  · exact hc

/-- Pass width for every n ≥ 5: `2 ≤ t` and `t + 2 ≤ n`.  For
q = ceilLogTwo n ≤ 32 the compiled width is the finite certificate width
(2, 3 or 5) and t ≤ q - 1 by evaluation; for q ≥ 33, t = ceilLogTwo q < q.
In both cases q < n.  Consumer: `widthWordPassLaunchRankBound`, the
ported pass steps and `widthWordRowTransport`. -/
theorem widthWordPassWidth {n : Nat}
    (hsmallFive : 5 ≤ n) :
    2 ≤ (compileAdvice (ceilLogTwo n)).t ∧
    (compileAdvice (ceilLogTwo n)).t + 2 ≤ n := by
  have hq3 := widthWordAdviceThree hsmallFive
  have hn := ceilLogTwo_spec n (by omega)
  have ha : ceilLogTwo n - 1 < 2 ^ (ceilLogTwo n - 1) := Nat.lt_two_pow_self
  have hqn : ceilLogTwo n + 1 ≤ n := by omega
  rcases Nat.lt_or_ge (ceilLogTwo n) 33 with hlt | hge
  · have hcheck : ∀ i : Fin 33, 3 ≤ i.val →
        2 ≤ (compileAdvice i.val).t ∧ (compileAdvice i.val).t + 1 ≤ i.val := by
      decide +kernel
    have h : 2 ≤ (compileAdvice (ceilLogTwo n)).t ∧
        (compileAdvice (ceilLogTwo n)).t + 1 ≤ ceilLogTwo n :=
      hcheck ⟨ceilLogTwo n, hlt⟩ hq3
    exact ⟨h.1, by omega⟩
  · rw [compileAdvice_t_large _ hge]
    have hq := ceilLogTwo_spec (ceilLogTwo n) (by omega)
    have hsix := ceilLogTwo_ge_six (ceilLogTwo n) hge
    have hb : ceilLogTwo (ceilLogTwo n) - 1 <
        2 ^ (ceilLogTwo (ceilLogTwo n) - 1) := Nat.lt_two_pow_self
    omega

/-- The serializer lease maximum is the width lease 8t + 4 (by
definition).  Consumer: `widthWordHardEpochSelectedGenuineRootIdle`,
`widthWordRenewalFrontierFreshBankPrepared`,
`widthWordEpochLapCountOfLineageStep`. -/
theorem widthWordHardEpochBankLeaseMaximum {n : Nat}
    (_hsmallFive : 5 ≤ n) :
    (compileAdvice (ceilLogTwo n)).siLeaseMax =
      8 * (compileAdvice (ceilLogTwo n)).t + 4 := rfl

/-- Room for the whole prefix and its first follower target.
Consumer: `widthWordRenewalFrontierFreshShapeOnBank`,
`widthWordRenewalFrontierShapePrefixNoRoot`. -/
theorem widthWordRenewalFrontierBankRoom {n : Nat}
    (hsmallFive : 5 ≤ n) :
    (compileAdvice (ceilLogTwo n)).t + 2 ≤ n :=
  (widthWordPassWidth hsmallFive).2

set_option exponentiation.threshold 600 in
/-- The R10a exponential moment rate `4 (n+1)^H ≤ 2^Q n^H` with
H = 2Cn², Q = 4C(n-1), C = 2t+1, for every n ≥ 5: for n ≥ 8 by the
coarse rate `bankUpperThreeEpoch`, and for n = 5, 6, 7 (q = 3, t = 2)
by evaluation.  Consumer: `widthUpperBankBandInterruptionQuarter`. -/
theorem widthUpperBandMomentRate
    (n : Nat) (hsmallFive : 5 ≤ n) :
    4 * (n + 1) ^
        (2 * (2 * (compileAdvice (ceilLogTwo n)).t + 1) * n ^ 2) ≤
      2 ^ ((8 * (compileAdvice (ceilLogTwo n)).t + 4) * (n - 1)) *
        n ^ (2 * (2 * (compileAdvice (ceilLogTwo n)).t + 1) *
          n ^ 2) := by
  rcases Nat.lt_or_ge n 8 with hlt | hge
  · have hq : ceilLogTwo n = 3 :=
      ceilLogTwo_unique 3 n (by omega)
        (by change 4 < n; omega) (by change n ≤ 8; omega)
    have ht : (compileAdvice (ceilLogTwo n)).t = 2 := by
      rw [hq]; decide
    rw [ht]
    rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7) with h | h | h <;>
      subst h <;> decide
  · have hnpos : 0 < n := by omega
    have hC : 1 ≤ 2 * (compileAdvice (ceilLogTwo n)).t + 1 := by omega
    generalize hCdef : 2 * (compileAdvice (ceilLogTwo n)).t + 1 = C at hC
    have hcoef : 8 * (compileAdvice (ceilLogTwo n)).t + 4 = 4 * C := by omega
    rw [hcoef]
    have hcanonical :
        n * (2 * C * n) = 2 * C * n ^ 2 := by
      simp only [Nat.pow_two, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm]
    have hp := Nat.pow_le_pow_left
      (L3.BinomialUpperTail.bankUpperUnitPower n hnpos) (2 * C * n)
    have hpower :
        (n + 1) ^ (n * (2 * C * n)) ≤
          3 ^ (2 * C * n) * n ^ (n * (2 * C * n)) := by
      simpa only [Nat.mul_pow, ← Nat.pow_mul] using hp
    rw [hcanonical] at hpower
    have hcoarse := L3.BinomialUpperTail.bankUpperThreeEpoch n C hge hC
    calc
      4 * (n + 1) ^ (2 * C * n ^ 2) ≤
          4 * (3 ^ (2 * C * n) *
            n ^ (2 * C * n ^ 2)) :=
        Nat.mul_le_mul_left 4 hpower
      _ = (4 * 3 ^ (2 * C * n)) *
            n ^ (2 * C * n ^ 2) := (Nat.mul_assoc _ _ _).symm
      _ ≤ 2 ^ (4 * C * (n - 1)) *
            n ^ (2 * C * n ^ 2) :=
        Nat.mul_le_mul_right _ hcoarse

/-- The R10a 1/4 upper-tail numerator with C = 2t + 1 for every n ≥ 5.
Consumer: `widthWordRenewalFreshRetryEstimate`. -/
theorem widthUpperBankBandInterruptionQuarter
    (n : Nat) (hsmallFive : 5 ≤ n) :
    4 * (n ^
          (2 * (2 * (compileAdvice (ceilLogTwo n)).t + 1) * n ^ 2) -
        L3.GrantDrainEntrance.grantDrainLabelBinomialShort n
          (2 * (2 * (compileAdvice (ceilLogTwo n)).t + 1) * n ^ 2)
          ((8 * (compileAdvice (ceilLogTwo n)).t + 4) * (n - 1))) ≤
      n ^ (2 * (2 * (compileAdvice (ceilLogTwo n)).t + 1) *
        n ^ 2) :=
  L3.BinomialUpperTail.grantDrainLabelBinomialUpperQuarterOfMoment
    n (2 * (2 * (compileAdvice (ceilLogTwo n)).t + 1) * n ^ 2)
    ((8 * (compileAdvice (ceilLogTwo n)).t + 4) * (n - 1))
    (by omega : 0 < n)
    (widthUpperBandMomentRate n hsmallFive)

/-! ## The renewal constants in t -/

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open PPL.Convergence.LDLocal
open L3.Prob

/-- Width port of `bankWordRenewalLease`: the renewal constant is written in the compiled width t instead of ψ = ceilLogTwo (ceilLogTwo n). Consumer: `widthWordEpochCompletionFiveCostHolds`, `widthWordEpochGenuineCostOfLapCount`. -/
def widthWordRenewalLease (n : Nat) : Nat :=
  8 * (compileAdvice (ceilLogTwo n)).t + 4

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open PPL.Convergence.LDLocal
open L3.Prob

/-- Width port of `bankWordRenewalWorkerQuota`: the renewal constant is written in the compiled width t instead of ψ = ceilLogTwo (ceilLogTwo n). Consumer: `widthWordRenewalFreshRetryCover`. -/
def widthWordRenewalWorkerQuota (n : Nat) : Nat :=
  2 * (compileAdvice (ceilLogTwo n)).t + 1

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open PPL.Convergence.LDLocal
open L3.Prob

/-- Width port of `bankWordRenewalHorizon`: the renewal constant is written in the compiled width t instead of ψ = ceilLogTwo (ceilLogTwo n). Consumer: `widthWordRenewalFreshRetryEstimate`. -/
def widthWordRenewalHorizon (n : Nat) : Nat :=
  2 * widthWordRenewalWorkerQuota n * n ^ 2

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open PPL.Convergence.LDLocal
open L3.Prob

/-- Width port of `bankWordRenewalBlock`: the renewal constant is written in the compiled width t instead of ψ = ceilLogTwo (ceilLogTwo n). Consumer: `widthWordEpochCompletionFiveCostHolds`, `widthWordEpochFreshCutFourCostHolds`. -/
def widthWordRenewalBlock (n : Nat) : Nat :=
  11 * (widthWordRenewalLease n + 1) * n ^ 2

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open PPL.Convergence.LDLocal
open L3.Prob

/-- Width port of `bankWordRenewalFiveCoefficient`: the renewal constant is written in the compiled width t instead of ψ = ceilLogTwo (ceilLogTwo n). Consumer: `widthWordEpochCompletionFiveCostHolds`.
 5B=(440t+275)n², already present abstractly in BankRepairWord. -/
theorem widthWordRenewalFiveCoefficient (n : Nat) :
    5 * widthWordRenewalBlock n =
      (440 * (compileAdvice (ceilLogTwo n)).t + 275) * n ^ 2 := by
  change
    5 * (11 * ((8 * (compileAdvice (ceilLogTwo n)).t + 4) + 1) *
      n ^ 2) =
      (440 * (compileAdvice (ceilLogTwo n)).t + 275) * n ^ 2
  exact bankWordEpochFiveCoefficient ((compileAdvice (ceilLogTwo n)).t) n

end

section
open L3.GrantDrainEntrance
open L3.Prob
open PPL.Convergence.LDLocal
open Classical

/-- Copy of the private `bankWordRenewalBinomialHalf` (generic in T, Q). Consumer: `widthWordRenewalWorkerNominationHalf`.
Exact binomial lower-half bound from the installed
lower weighted estimate and its 2n-block decay. The opaque
T,Q lemma is instantiated only after the two source facts. -/
theorem widthWordRenewalBinomialHalf
    (n T Q : Nat) (hn : 0 < n)
    (hlength : 2 * n * Q ≤ T) :
    2 * grantDrainLabelBinomialShort n T Q ≤ n ^ T := by
  have hweighted :=
    grantDrainLabelBinomialWeighted n T Q hn
  have hdecay :=
    grantDrainLabelTailDecay n T Q hn hlength
  have htotal := Nat.le_trans hweighted hdecay
  have hscaled :
      2 ^ T * (2 * grantDrainLabelBinomialShort n T Q) ≤
        2 ^ T * n ^ T := by
    calc
      2 ^ T * (2 * grantDrainLabelBinomialShort n T Q) =
          2 ^ (T + 1) * grantDrainLabelBinomialShort n T Q := by
            rw [Nat.pow_succ]
            simp only [Nat.mul_assoc]
      _ ≤ (2 * n) ^ T := htotal
      _ = 2 ^ T * n ^ T := Nat.mul_pow 2 n T
  exact Nat.le_of_mul_le_mul_left hscaled
    (Nat.pow_pos (by decide : 0 < (2 : Nat)))

/-- Width port of `bankWordRenewalWorkerNominationHalf`: the renewal constant is written in the compiled width t instead of ψ = ceilLogTwo (ceilLogTwo n). Consumer: `widthWordRenewalFreshRetryEstimate`.
 Paper 1061--1074: on the ACTUAL epoch chain, for any
predictable worker nomination, the event 'fewer than Cn
nominated hits in H=2Cn² letters' has mass at most 1/2.
This does not assert that an actual worker exists or survives. -/
theorem widthWordRenewalWorkerNominationHalf {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (chosen : BankWordRenewalPostSOne ring root s → Fin n)
    (hn : 0 < n) :
    2 * L3.Prob.scheduleSum n (widthWordRenewalHorizon n)
      (fun word =>
        if grantDrainLabelHits (bankWordRenewalNext ring root s)
            chosen z word < widthWordRenewalWorkerQuota n * n
        then 1 else 0) ≤
      n ^ widthWordRenewalHorizon n := by
  have hlength :
      2 * n * (widthWordRenewalWorkerQuota n * n) ≤
        widthWordRenewalHorizon n := by
    have heq :
        2 * n * (widthWordRenewalWorkerQuota n * n) =
          2 * widthWordRenewalWorkerQuota n * n ^ 2 := by
      rw [Nat.pow_two]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [heq]
    exact Nat.le_refl _
  have hmass := widthWordRenewalBinomialHalf
    n (widthWordRenewalHorizon n)
    (widthWordRenewalWorkerQuota n * n) hn hlength
  rw [grantDrainLabelBinomialLaw
    (bankWordRenewalNext ring root s)
    chosen z (widthWordRenewalHorizon n)
    (widthWordRenewalWorkerQuota n * n) hn]
  exact hmass

end

section
open Classical
open L3.Prob
open L3.GrantDrainEntrance
open PPL.Convergence.LDLocal
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `BankWordRenewalFreshAttemptCost`: the renewal constant is written in the compiled width t instead of ψ = ceilLogTwo (ceilLogTwo n). Consumer: `widthWordRenewalFreshAttemptCostHolds`, `widthWordRenewalFreshAttemptCostOfLineageStep`.
 The attempt-cost input is now quantified only over genuinely
fresh hard-acceptance seeds, not arbitrary old hardValid states. -/
def WidthWordRenewalFreshAttemptCost {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ seed : BankWordRenewalFreshSeed ring root s, ∀ T,
    costNumerator
      (L3.Prob.attemptStepper
        (bankWordRenewalFreshKernel ring root s))
      (fun a => L3.Prob.attemptGood a ∨ L3.Prob.attemptFail a)
      (.active seed.1) T ≤ n ^ T * widthWordRenewalBlock n

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `BankWordEpochPostSOneWorkerClock`: the renewal constant is written in the compiled width t instead of ψ = ceilLogTwo (ceilLogTwo n). Consumer: `widthWordEpochPostSOneWorkerClockHolds`, `widthWordEpochPostSOneWorkerClockOfInternalRows`.
 EXACT missing worker/serializer component of the one-epoch
bound, isolated for subsequent row and clock proofs.

Source: repair.tex (main) lines 3000-3156 for hard validation,
worker rows and the C*n^2 nomination clock; lines 3178-3207 for
lease/soft-lap destruction; lines 3238-3295 for arbitrary initial
bytes and the first genuine hard acceptance.

From EVERY *actually reachable* S1-completed epoch state, under
the same projected W process and causal receipt observer, the
remaining first-hit cost to a genuinely launched hard worker
is bounded by 6*n^2+(L+1)*(5*n^2+2*n), L=8*s+4.

The initial 6*n^2 pays the extra fresh episode after an inherited
S1 (< 5*n^2+2*n), and the L+1 remaining episodes cover the
lease/soft-lap barrier. This is NOT currently an established producer. -/
def WidthWordEpochPostSOneWorkerClock {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z : BankWordEpochState n,
    BankWordEpochReachable ring root s z →
    BankWordEpochSOneReached z →
    ∀ T : Nat,
      costNumerator (bankWordEpochNext ring root)
        BankWordEpochWorkerLaunched z T ≤
      n ^ T *
        (6 * n ^ 2 +
          (8 * (compileAdvice (ceilLogTwo n)).t + 5) *
            (5 * n ^ 2 + 2 * n))

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `BankWordEpochLapCount`: the renewal constant is written in the compiled width t instead of ψ = ceilLogTwo (ceilLogTwo n). Consumer: `widthWordEpochGenuineCostOfLapCount`, `widthWordEpochLapCountOfLineageStep`.
 DET.  Along any run from a reachable post-S1 state `z₀`, the
genuine-acceptance counter increases before the (L+2)-nd root S1
service after `z₀`, `L = widthWordRenewalLease n`.
Consumer: `bankWordEpochPostSOneWorkerClockOfLapCount`. -/
def WidthWordEpochLapCount {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z₀ : BankWordEpochState n,
    BankWordEpochReachable ring root s z₀ →
    BankWordEpochSOneReached z₀ →
    ∀ z : BankWordEpochState n,
      BankWordEpochReachableFrom ring root z₀ z →
      bankWordRootStartCount root z₀ + (widthWordRenewalLease n + 2) ≤
        bankWordRootStartCount root z →
      (bankWordHardEpochLedger ring root z₀).hardEpochs <
        (bankWordHardEpochLedger ring root z).hardEpochs

end

section
open Classical
open L3.Prob
open L3.GrantDrainEntrance
open PPL.Convergence.LDLocal
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `BankWordRetryPrefixInvariant`: the renewal constant is written in the compiled width t instead of ψ = ceilLogTwo (ceilLogTwo n). Consumer: `widthWordRetryPrefixInvariantSeed`, `widthWordRetryPrefixStep`.
 The prefix invariant of the fresh attempt before its first hard S1:
the clean-worker pass, the rooted soft shape, a live epoch with no
recorded completion, the lease ledger `lease + softFinishes = L`, and
a spendable lease during a soft episode.
Consumer: `bankWordRetryPrefixWord`. -/
def WidthWordRetryPrefixInvariant {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s) : Prop :=
  BankWordPassShape ring root z.1 ∧
  BankWordRenewalSoftShape ring root z.1 ∧
  0 < (bankWordHardEpochLedger ring root z.1).hardEpochs ∧
  (bankWordHardEpochLedger ring root z.1).workerDone = false ∧
  (z.1.2.1 root).siLease.val +
      (bankWordHardEpochLedger ring root z.1).softFinishes =
    widthWordRenewalLease n ∧
  ((z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.wphase = .CURRENT →
    0 < (z.1.2.1 root).siLease.val)

end

/-! ## Ported hard-epoch layer (BankRepairWord, BankWordRenewal*) -/

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordEpochSOneCost`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordProjectedOneEpochCostOfWorkerClock`.
 The true S1 first-hit numerator is at most n(5n-4)
from ANY physical W configuration represented by a genuine
fixed-root post-inherited BANK reference. -/
theorem widthWordEpochSOneCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      BankWordEpochSOneReached (bankWordEpochStart s) T ≤
    n ^ T * (n * (5 * n - 4)) := by
  rw [bankWordEpochSOneCostEq]
  change costNumerator
      (clockSerializerSOneOnlyNext ring root)
      clockSerializerIsStopped
      (.active s : ClockSerializerStopNode n
        (compileAdvice (ceilLogTwo n))) T ≤
    n ^ T * (n * (5 * n - 4))
  exact clockSerializerSOneCostFromG ring root
    (WidthWordSerializerRootClass ring hsmallFive root)
    (widthWordSerializerRootClassClosed ring hn hsmallFive root)
    s hs (by omega : 4 ≤ n) T

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordProjectedOneEpochCostOfWorkerClock`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochCompletionFiveCostHolds`.
 First genuine hard worker launch of this actual projected
epoch, from arbitrary inherited W bytes with a rooted BANK
representation, within paper B=11*(L+1)*n^2, L=8*s+4.

Only the exact post-S1 worker/serializer clock above is an
unproved input; the entire first-S1 phase is already paid by
SerClockCost, with equality of stopped cost numerators. -/
theorem widthWordProjectedOneEpochCostOfWorkerClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hworker : WidthWordEpochPostSOneWorkerClock ring root s)
    (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      BankWordEpochWorkerLaunched
      (bankWordEpochStart s) T ≤
    n ^ T *
      (11 * (8 * (compileAdvice (ceilLogTwo n)).t + 5) * n ^ 2) := by
  have hinit : BankWordEpochReachable ring root s
      (bankWordEpochStart s) :=
    ⟨[], rfl⟩
  have hfirst : ∀ U : Nat,
      costNumerator (bankWordEpochNext ring root)
        (fun z =>
          (BankWordEpochSOneReached z ∧
            BankWordEpochReachable ring root s z) ∨
          BankWordEpochWorkerLaunched z)
        (bankWordEpochStart s) U ≤
      n ^ U * (n * (5 * n - 4)) := by
    intro U
    calc
      costNumerator (bankWordEpochNext ring root)
          (fun z =>
            (BankWordEpochSOneReached z ∧
              BankWordEpochReachable ring root s z) ∨
            BankWordEpochWorkerLaunched z)
          (bankWordEpochStart s) U ≤
        costNumerator (bankWordEpochNext ring root)
          (fun z => BankWordEpochSOneReached z ∧
            BankWordEpochReachable ring root s z)
          (bankWordEpochStart s) U :=
        L3.Prob.costNumerator_target_mono
          (bankWordEpochNext ring root)
          (fun z => BankWordEpochSOneReached z ∧
            BankWordEpochReachable ring root s z)
          (fun z =>
            (BankWordEpochSOneReached z ∧
              BankWordEpochReachable ring root s z) ∨
            BankWordEpochWorkerLaunched z)
          (by intro z h; exact Or.inl h)
          (bankWordEpochStart s) U
      _ = costNumerator (bankWordEpochNext ring root)
          BankWordEpochSOneReached
          (bankWordEpochStart s) U :=
        bankWordEpochReachableSOneCostEq ring root s U
          (bankWordEpochStart s) hinit
      _ ≤ n ^ U * (n * (5 * n - 4)) :=
        widthWordEpochSOneCost ring hn hsmallFive root s hs U
  have hsecond : ∀ z : BankWordEpochState n,
      (BankWordEpochSOneReached z ∧
        BankWordEpochReachable ring root s z) →
      ∀ U : Nat,
        costNumerator (bankWordEpochNext ring root)
          BankWordEpochWorkerLaunched z U ≤
        n ^ U * (6 * n ^ 2 +
          (8 * (compileAdvice (ceilLogTwo n)).t + 5) *
            (5 * n ^ 2 + 2 * n)) := by
    intro z hz U
    exact hworker z hz.2 hz.1 U
  have hstaged :=
    L3.Prob.costNumerator_stage_le
      (bankWordEpochNext ring root)
      (bankWordEpochStart s)
      (fun z => BankWordEpochSOneReached z ∧
        BankWordEpochReachable ring root s z)
      BankWordEpochWorkerLaunched
      (n * (5 * n - 4))
      (6 * n ^ 2 +
        (8 * (compileAdvice (ceilLogTwo n)).t + 5) *
          (5 * n ^ 2 + 2 * n))
      hfirst hsecond T
  exact Nat.le_trans hstaged
    (Nat.mul_le_mul_left (n ^ T)
      (bankWordEpochBudgetArithmetic n
        ((compileAdvice (ceilLogTwo n)).t) hn))

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordEpochRunPhysicalRootClass`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochReachablePhysicalRootClass`.
 A real epoch run preserves the same protected singleton
representation at every physical edge, even after the S1 latch
stops. This does not inspect or reset private serializer bytes. -/
theorem widthWordEpochRunPhysicalRootClass {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (word : List (Fin n)) :
    WidthWordSerializerRootClass ring hsmallFive root
      (bankWordEpochRun ring root (bankWordEpochStart s) word).2.1 := by
  have hrun :
      ∀ (w : List (Fin n)) (z : BankWordEpochState n),
        WidthWordSerializerRootClass ring hsmallFive root z.2.1 →
        WidthWordSerializerRootClass ring hsmallFive root
          (bankWordEpochRun ring root z w).2.1 := by
    intro w
    induction w with
    | nil =>
        intro z hz
        exact hz
    | cons e rest ih =>
        intro z hz
        change WidthWordSerializerRootClass ring hsmallFive root
          (bankWordEpochRun ring root
            (bankWordEpochNext ring root z e) rest).2.1
        apply ih
        have hstep :=
          (widthWordSerializerRootClassClosed
            ring hn hsmallFive root).2 z.2.1 hz e
        rw [bankWordEpochPhysicalNext]
        exact hstep.1
  exact hrun word (bankWordEpochStart s) hs

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordEpochReachablePhysicalRootClass`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochFixedRoot`, `widthWordEpochRestartSOneCost`, `widthWordHardEpochSelectedGenuineRootIdle`.
 Reachability in the causal W epoch implies that the true
projected physical configuration is still in the root class. -/
theorem widthWordEpochReachablePhysicalRootClass {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    WidthWordSerializerRootClass ring hsmallFive root z.2.1 := by
  obtain ⟨word, hword⟩ := hz
  have hrun := widthWordEpochRunPhysicalRootClass
    ring hn hsmallFive root s hs word
  rw [hword] at hrun
  exact hrun

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordEpochRestartSOneCost`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRootStartCountNextLapCost`.
 A fresh S1-only observer can be started from ANY reachable
post-S1 real W configuration. The old stopped latch is not used
as a clock for a later episode. This is SerClockCost's
n(5n-4) clock, transferred using physical root-class closure. -/
theorem widthWordEpochRestartSOneCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (T : Nat) :
    costNumerator (clockSerializerSOneOnlyNext ring root)
      clockSerializerIsStopped
      (.active z.2.1 : ClockSerializerStopNode n
        (compileAdvice (ceilLogTwo n))) T ≤
    n ^ T * (n * (5 * n - 4)) := by
  exact clockSerializerSOneCostFromG ring root
    (WidthWordSerializerRootClass ring hsmallFive root)
    (widthWordSerializerRootClassClosed ring hn hsmallFive root)
    z.2.1
    (widthWordEpochReachablePhysicalRootClass
      ring hn hsmallFive root s hs z hz)
    (by omega : 4 ≤ n) T

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordEpochSOneRunningBReachable`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochLapInvariantStep`, `widthWordEpochPostLatchRootFactsStep`, `widthWordEpochSOneReachedOfRootTicketOrigin`.
 The invariant is preserved by every finite physical word
in a class with fixed-root closure. This is a real-word induction,
not a Markov surrogate or an assumption on the stopped observer. -/
theorem widthWordEpochSOneRunningBReachable
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    BankWordEpochSOneRunningBInvariant root z := by
  obtain ⟨word, hword⟩ := hz
  have hrun :
      ∀ word : List (Fin n), ∀ q : BankWordEpochState n,
        WidthWordSerializerRootClass ring hsmallFive root q.2.1 →
        BankWordEpochSOneRunningBInvariant root q →
        BankWordEpochSOneRunningBInvariant root
          (bankWordEpochRun ring root q word) := by
    intro word
    induction word with
    | nil =>
        intro q _ hsafe
        exact hsafe
    | cons e rest ih =>
        intro q hclass hsafe
        have hnext :=
          (widthWordSerializerRootClassClosed
            ring hn hsmallFive root).2 q.2.1 hclass e
        apply ih (bankWordEpochNext ring root q e)
        · rw [bankWordEpochPhysicalNext]
          exact hnext.1
        · exact bankWordEpochSOneRunningBStep ring root
            (by omega : 2 ≤ n) q e hnext.2 hsafe
  have hinv := hrun word (bankWordEpochStart s) hs
    (bankWordEpochSOneRunningBInitial root s)
  rw [hword] at hinv
  exact hinv

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordHardEpochSelectedGenuineRootIdle`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFrontierFreshRootIdle`.
 The genuine ticket receipt in a represented fixed-root BANK
execution has an actual IDLE root in the physical successor.
This uses the existing all-word singleton/root-class closure,
not a fabricated source of physical leader information. -/
theorem widthWordHardEpochSelectedGenuineRootIdle
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n)
    (hgen : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true) :
    ((bankWordEpochNext ring root z e).2.1 root).ser.cert =
      .IDLE := by
  obtain ⟨he, _, hhard⟩ :=
    bankWordHardEpochSelectedGenuineOwnerFlags
      ring root z e hgen
  subst e
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed
      ring hn hsmallFive root).2 z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hlocal := bankWordHardEpochHardAcceptLocalIdle
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2 hhard
  change ((phiW ring z.2.1 root) root).ser.cert = .IDLE
  rw [phiW_ser_source]
  exact hlocal.1

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordTicketPhysicalHardStartHistory`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordTicketHardStartThroughWord`.
 Actual represented BANK closure supplies WFixedRoot on
the successor of the selected hard S1. EWord.start then
constructs a complete physical history, independent of
whether that S1 had an origin-observer requested ticket. -/
theorem widthWordTicketPhysicalHardStartHistory
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hreq : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0) :
    L3.EWord.WValidationHistory ring root
      (bankWordEpochNext ring root z root).2.1
      L3.EWord.freshGhost := by
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed :
      WFixedRoot ring root (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed
      ring hn hsmallFive root).2 z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  change L3.EWord.WValidationHistory ring root
    (phiW ring z.2.1 root) L3.EWord.freshGhost
  exact L3.EWord.WValidationHistory.start z.2.1
    (by omega : 3 ≤ n) hpost.1 hpost.2 hreq hzero
    hfixed

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordTicketPhysicalHistoryNext`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordTicketPhysicalHistoryRun`.
 EWord.next applies on each nonaccepting actual edge.
The fixed-root premise is supplied by the same represented
BANK class used by the projected one-epoch cost theorem. -/
theorem widthWordTicketPhysicalHistoryNext
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (g : L3.EWord.ValidationGhost)
    (history : L3.EWord.WValidationHistory ring root z.2.1 g)
    (e : Fin n)
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardAccept =
        false) :
    L3.EWord.WValidationHistory ring root
      (bankWordEpochNext ring root z e).2.1
      (L3.EWord.validationGhostStep ring root z.2.1 g e) := by
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed :
      WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed
      ring hn hsmallFive root).2 z.2.1 hclass e).2
  change (serW (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e))).hard.hardAccept = false
    at hno
  change L3.EWord.WValidationHistory ring root
    (phiW ring z.2.1 e)
    (L3.EWord.validationGhostStep ring root z.2.1 g e)
  exact L3.EWord.WValidationHistory.next history e hno
    hfixed

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordTicketPhysicalHistoryRun`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordTicketHardStartThroughWord`.
 A genuine finite-word induction: EWord's full physical
validation history survives every actual nonaccepting edge
in a represented BANK run. The proof does not assume anything
about the (possibly older) Target ticket values. -/
theorem widthWordTicketPhysicalHistoryRun
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (word : List (Fin n)) :
    ∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      ∀ g : L3.EWord.ValidationGhost,
        L3.EWord.WValidationHistory ring root z.2.1 g →
        bankWordTicketNoHardAcceptWord ring root z word →
        ∃ g' : L3.EWord.ValidationGhost,
          L3.EWord.WValidationHistory ring root
            (bankWordEpochRun ring root z word).2.1 g' := by
  induction word with
  | nil =>
      intro z hz g history hno
      exact ⟨g, history⟩
  | cons e rest ih =>
      intro z hz g history hno
      have hfirst :
          (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardAccept =
            false := hno.1
      have hstep := widthWordTicketPhysicalHistoryNext
        ring hn hsmallFive root s hs z hz g history e hfirst
      have hreach := bankWordEpochReachableNext
        ring root s z hz e
      exact ih (bankWordEpochNext ring root z e) hreach
        (L3.EWord.validationGhostStep ring root z.2.1 g e)
        hstep hno.2

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordTicketHardStartThroughWord`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassNonvalidatingAfterGenuine`, `widthWordTicketHardStartThroughAcceptClean`.
 A real zero-lease hard start followed by a finite
nonaccepting word therefore has the complete EWord history
immediately before its first physical accepting edge. -/
theorem widthWordTicketHardStartThroughWord
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hreq : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0)
    (word : List (Fin n))
    (hno : bankWordTicketNoHardAcceptWord ring root
      (bankWordEpochNext ring root z root) word) :
    ∃ g : L3.EWord.ValidationGhost,
      L3.EWord.WValidationHistory ring root
        (bankWordEpochRun ring root
          (bankWordEpochNext ring root z root) word).2.1 g := by
  have hstart := widthWordTicketPhysicalHardStartHistory
    ring hn hsmallFive root s hs z hz hreq hzero
  have hreach := bankWordEpochReachableNext
    ring root s z hz root
  exact widthWordTicketPhysicalHistoryRun
    ring hn hsmallFive root s hs word
    (bankWordEpochNext ring root z root) hreach
    L3.EWord.freshGhost hstart hno

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordTicketHardStartThroughAcceptClean`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRootTicketOriginGenuineClean`.
 Hence the entire hard-S1/word/S6 segment has the exact
post-I0 nonroot scrub certificate, using EWord's already
established validating traversal and the literal accepting edge.
There is NO new named premise: hno is a finite physical
receipt test on the displayed word. -/
theorem widthWordTicketHardStartThroughAcceptClean
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hreq : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0)
    (word : List (Fin n))
    (hno : bankWordTicketNoHardAcceptWord ring root
      (bankWordEpochNext ring root z root) word)
    (e : Fin n)
    (hgen : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring
        (bankWordEpochRun ring root
          (bankWordEpochNext ring root z root) word) e)
      (bankWordHardEpochLedger ring root
        (bankWordEpochRun ring root
          (bankWordEpochNext ring root z root) word)) = true) :
    ∀ i : Fin n, i ≠ root →
      freeSI
        ((bankWordEpochNext ring root
          (bankWordEpochRun ring root
            (bankWordEpochNext ring root z root) word) e).2.1 i).si =
        true := by
  obtain ⟨g, history⟩ :=
    widthWordTicketHardStartThroughWord
      ring hn hsmallFive root s hs z hz hreq hzero word hno
  exact bankWordHardEpochSelectedHistoryClean
    ring root
    (bankWordEpochRun ring root
      (bankWordEpochNext ring root z root) word)
    e g history hgen

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordRootTicketOriginGenuineClean`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRootDoneOriginGenuineClean`.
 Once the literal root origin decomposition has been proved,
    the installed EWord bridge gives post-acceptance nonroot SI
    cleanup on the original projected physical successor. -/
theorem widthWordRootTicketOriginGenuineClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (ticket : WValidationTicket)
    (horigin : BankWordRootTicketOrigin ring root s z ticket)
    (e : Fin n)
    (hgen : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true) :
    ∀ i : Fin n, i ≠ root →
      freeSI ((bankWordEpochNext ring root z e).2.1 i).si =
        true := by
  obtain ⟨pre, mid, request, hz, hreq, hzero,
    hrequested, hrequestStamp, hstartStamp, hhard, hmid⟩ := horigin
  have hprefix : BankWordEpochReachable ring root s
      (bankWordEpochRun ring root
        (bankWordEpochStart s) pre) :=
    ⟨pre, rfl⟩
  have hdecomp :
      bankWordEpochRun ring root (bankWordEpochStart s)
        (pre ++ [root] ++ mid) =
      bankWordEpochRun ring root
        (bankWordEpochNext ring root
          (bankWordEpochRun ring root
            (bankWordEpochStart s) pre) root) mid := by
    rw [bankWordRootRunAppend, bankWordEpochRunSnoc]
  rw [hz, hdecomp] at hgen ⊢
  exact widthWordTicketHardStartThroughAcceptClean
    ring hn hsmallFive root s hs
    (bankWordEpochRun ring root
      (bankWordEpochStart s) pre)
    hprefix hreq hzero mid hmid e hgen

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordRootDoneOriginGenuineClean`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFrontierFreshBankForeignFree`.
 The joined-stamps theorem now supplies the exact ticket to
    which the root .done-origin relation must be applied. The
    still-missing premise is *only* the global production of
    BankWordRootDoneOrigin on represented reachable runs. -/
theorem widthWordRootDoneOriginGenuineClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hinv : BankWordRootDoneOrigin ring root s z)
    (e : Fin n)
    (hgen : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true) :
    ∀ i : Fin n, i ≠ root →
      freeSI ((bankWordEpochNext ring root z e).2.1 i).si =
        true := by
  obtain ⟨p, q, hp, hq, hrequestStamp, hstartStamp⟩ :=
    bankWordHardEpochGenuineJoinedStamps ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) hgen
  have he := (bankWordHardEpochSelectedGenuineOwnerFlags
    ring root z e hgen).1
  subst e
  exact widthWordRootTicketOriginGenuineClean
    ring hn hsmallFive root s hs z p (hinv p hp) root hgen

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordRootNonrootHardAcceptFalse`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFrontierWaveUnvisitedNonrootStep`, `widthWordRenewalWaveInternalUnvisitedQuietStep`, `widthWordRenewalWaveSelectedRemoteQuietStep`.
 On a represented fixed-root epoch, every nonroot source
    is nonaccepting. This includes the incoming-root edge. -/
theorem widthWordRootNonrootHardAcceptFalse {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n) (he : e ≠ root) :
    (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardAccept =
      false := by
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed
      ring hn hsmallFive root).2 z.2.1 hclass e).2
  have hx := L3.EWord.validationPostSourceNonroot
    ring root z.2.1 e hfixed he
  change (serW (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e))).hard.hardAccept = false
  exact L3.EWord.nonrootNoAccept
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hx

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordRootTicketOriginAllIncomingNext`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRootTicketOriginAllWordOfOutgoing`.
 The incoming-root S0 branch creates .requested, and S5
    leaves the old root ticket untouched. Both are covered
    without a foreign-stamp exception. -/
theorem widthWordRootTicketOriginAllIncomingNext {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n) (hj : ring.rightNeighbor e = root)
    (hinv : BankWordRootTicketOriginAll ring root s z) :
    BankWordRootTicketOriginAll ring root s
      (bankWordEpochNext ring root z e) := by
  have he : e ≠ root := by
    intro h
    apply clockNeighborDifferent ring (by omega : 2 ≤ n) e
    calc
      ring.rightNeighbor e = root := hj
      _ = e := h.symm
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed
      ring hn hsmallFive root).2 z.2.1 hclass e).2
  have hframe := bankWordRootIncomingTicketExact
    ring root z e (by omega : 2 ≤ n) hfixed hj
  have hno := widthWordRootNonrootHardAcceptFalse
    ring hn hsmallFive root s hs z hz e he
  intro ticket ht
  rw [hframe] at ht
  by_cases hc : (z.2.1 root).ser.cert = .IDLE
  · rw [if_pos hc] at ht
    have heq : ticket =
        { requestedAt := z.2.2.clock + 1,
          startedAt := z.2.2.clock + 1,
          stage := .requested } := (Option.some.inj ht).symm
    left
    rw [heq]
  · rw [if_neg hc] at ht
    rcases hinv ticket ht with hrequest | horigin
    · exact Or.inl hrequest
    · exact Or.inr
        (bankWordRootTicketOriginNonacceptNext
          ring root s z ticket e horigin hno)

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordRootTicketOriginAllWordOfOutgoing`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRootDoneOriginReachableOfOutgoing`.
 A precise reduction of the global bridge to the remaining
    nonaccepting root-outgoing step. No new axiom is declared:
    the missing closure is an explicit theorem parameter. -/
theorem widthWordRootTicketOriginAllWordOfOutgoing {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hout :
      ∀ z : BankWordEpochState n,
        BankWordEpochReachable ring root s z →
        BankWordRootTicketOriginAll ring root s z →
        (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
          false →
        BankWordRootTicketOriginAll ring root s
          (bankWordEpochNext ring root z root))
    (word : List (Fin n)) :
    ∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      BankWordRootTicketOriginAll ring root s z →
      BankWordRootTicketOriginAll ring root s
        (bankWordEpochRun ring root z word) := by
  induction word with
  | nil =>
      intro z hz hinv
      exact hinv
  | cons e rest ih =>
      intro z hz hinv
      have hzstep := bankWordEpochReachableNext
        ring root s z hz e
      have hstep : BankWordRootTicketOriginAll ring root s
          (bankWordEpochNext ring root z e) := by
        by_cases he : e = root
        · subst e
          by_cases hhard :
              (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
                true
          · have hclass := widthWordEpochReachablePhysicalRootClass
              ring hn hsmallFive root s hs z hz
            have hfixed : WFixedRoot ring root
                (phiW ring z.2.1 root) :=
              ((widthWordSerializerRootClassClosed
                ring hn hsmallFive root).2 z.2.1 hclass root).2
            have hpost := clockPostOutgoing
              ring root z.2.1 root (by omega : 2 ≤ n) hfixed rfl
            exact bankWordRootTicketOriginAllHardAcceptNext
              ring root s z hpost.1 hpost.2 hhard
          · have hno :
                (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
                  false := by
              cases h :
                (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept
              · rfl
              · exact False.elim (hhard h)
            exact hout z hz hinv hno
        · by_cases hj : ring.rightNeighbor e = root
          · exact widthWordRootTicketOriginAllIncomingNext
              ring hn hsmallFive root s hs z hz e hj hinv
          · have hno := widthWordRootNonrootHardAcceptFalse
              ring hn hsmallFive root s hs z hz e he
            exact bankWordRootTicketOriginAllRemoteNext
              ring root s z e hinv (Ne.symm he) (Ne.symm hj) hno
      exact ih (bankWordEpochNext ring root z e) hzstep hstep

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordRootDoneOriginReachableOfOutgoing`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRootDoneOriginReachable`. -/
theorem widthWordRootDoneOriginReachableOfOutgoing {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hout :
      ∀ z : BankWordEpochState n,
        BankWordEpochReachable ring root s z →
        BankWordRootTicketOriginAll ring root s z →
        (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
          false →
        BankWordRootTicketOriginAll ring root s
          (bankWordEpochNext ring root z root))
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    BankWordRootDoneOrigin ring root s z := by
  obtain ⟨word, hword⟩ := hz
  subst z
  apply bankWordRootTicketOriginAllDone
  exact widthWordRootTicketOriginAllWordOfOutgoing
    ring hn hsmallFive root s hs hout word
    (bankWordEpochStart s) ⟨[], rfl⟩
    (bankWordRootTicketOriginAllInitial ring root s)

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordRootTicketOriginAllOutgoingNext`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRootDoneOriginReachable`.
 All ROOT_OUT rows, completing the earlier hout premise. -/
theorem widthWordRootTicketOriginAllOutgoingNext {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hinv : BankWordRootTicketOriginAll ring root s z)
    (hno : (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
      false) :
    BankWordRootTicketOriginAll ring root s
      (bankWordEpochNext ring root z root) := by
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing
    ring root z.2.1 root (by omega : 2 ≤ n) hfixed rfl
  have hrows := bankWordRootOutgoingRowClass
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2
  rcases hrows with hstart | hreset | haccept | hroute
  · exact bankWordRootTicketOriginAllSOneNext
      ring root s z hz hpost.1 hpost.2 hstart
  · intro ticket ht
    rw [bankWordRootOutgoingTicketExact ring root z] at ht
    simp [wValidationPair, hreset] at ht
  · intro ticket ht
    rw [bankWordRootOutgoingTicketExact ring root z] at ht
    simp [wValidationPair, haccept] at ht
  · exact bankWordRootTicketOriginAllS2RNext
      ring root s z hinv hroute hno

end

section
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Width port of `bankWordRootDoneOriginReachable`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochSOneReachedOfGenuine`, `widthWordPassNonvalidatingAfterGenuine`, `widthWordRenewalFrontierFreshBankForeignFree`.
 Final unconditional represented-epoch origin bridge. -/
theorem widthWordRootDoneOriginReachable {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    BankWordRootDoneOrigin ring root s z := by
  exact widthWordRootDoneOriginReachableOfOutgoing
    ring hn hsmallFive root s hs
    (widthWordRootTicketOriginAllOutgoingNext
      ring hn hsmallFive root s hs) z hz

end

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.widthWordSerializerRootClassClosed
#print axioms L3.RenewalReferenceClock.widthWordAdviceThree
#print axioms L3.RenewalReferenceClock.widthWordPassWidth
#print axioms L3.RenewalReferenceClock.widthWordHardEpochBankLeaseMaximum
#print axioms L3.RenewalReferenceClock.widthWordRenewalFrontierBankRoom
#print axioms L3.RenewalReferenceClock.widthUpperBandMomentRate
#print axioms L3.RenewalReferenceClock.widthUpperBankBandInterruptionQuarter
#print axioms L3.RenewalReferenceClock.widthWordRenewalFiveCoefficient
#print axioms L3.RenewalReferenceClock.widthWordRenewalBinomialHalf
#print axioms L3.RenewalReferenceClock.widthWordRenewalWorkerNominationHalf
#print axioms L3.RenewalReferenceClock.widthWordEpochSOneCost
#print axioms L3.RenewalReferenceClock.widthWordProjectedOneEpochCostOfWorkerClock
#print axioms L3.RenewalReferenceClock.widthWordEpochRunPhysicalRootClass
#print axioms L3.RenewalReferenceClock.widthWordEpochReachablePhysicalRootClass
#print axioms L3.RenewalReferenceClock.widthWordEpochRestartSOneCost
#print axioms L3.RenewalReferenceClock.widthWordEpochSOneRunningBReachable
#print axioms L3.RenewalReferenceClock.widthWordHardEpochSelectedGenuineRootIdle
#print axioms L3.RenewalReferenceClock.widthWordTicketPhysicalHardStartHistory
#print axioms L3.RenewalReferenceClock.widthWordTicketPhysicalHistoryNext
#print axioms L3.RenewalReferenceClock.widthWordTicketPhysicalHistoryRun
#print axioms L3.RenewalReferenceClock.widthWordTicketHardStartThroughWord
#print axioms L3.RenewalReferenceClock.widthWordTicketHardStartThroughAcceptClean
#print axioms L3.RenewalReferenceClock.widthWordRootTicketOriginGenuineClean
#print axioms L3.RenewalReferenceClock.widthWordRootDoneOriginGenuineClean
#print axioms L3.RenewalReferenceClock.widthWordRootNonrootHardAcceptFalse
#print axioms L3.RenewalReferenceClock.widthWordRootTicketOriginAllIncomingNext
#print axioms L3.RenewalReferenceClock.widthWordRootTicketOriginAllWordOfOutgoing
#print axioms L3.RenewalReferenceClock.widthWordRootDoneOriginReachableOfOutgoing
#print axioms L3.RenewalReferenceClock.widthWordRootTicketOriginAllOutgoingNext
#print axioms L3.RenewalReferenceClock.widthWordRootDoneOriginReachable
