import Leader.PPL.Modes.ConstructionModeSplit
import Leader.PPL.Modes.StoppedClockSuffixFreeze
import Leader.PPL.Modes.SignalLineageClosed
import Leader.PPL.Modes.SignalAbsorptionLottery
import Leader.PPL.Modes.EarlyLeaderStop
import Leader.PPL.Probability.FixedWord
import Leader.PPL.Probability.EncounterProjection
import Leader.PPL.Probability.MarkedWordTransfer
import Leader.PPL.Probability.LotteryMoment

/-!
# Lemma 5(i): sweep / C_mid counting leaf

Truth audit: Lemma5iSweepMidCount is TRUE as stated.

The scheduler-only traversal estimate closes on current main. The prescribed
clockwise word is the literal edge word 0,1,...,n-1; at K = 2n the accepted
fixed-word theorem has horizon

  2*n*(n + 2*n) = 6*n^2,

which is exactly lemma5PaperSweepHorizon. Thus its miss numerator has
dyadic scale 2^(2*n).

The remaining bounded-round seam is isolated below as exactly one named Prop,
Lemma5iSweepMidPhysicalCountSplice. Its first clause is only the concrete
protocol-to-fixed-word count projection (including the arm-prefix and frozen
2n^2 padding). Its second clause is the concrete random-reset-epoch bind for
the final C_mid clock/mode predicate. That second bind is where the accepted
StoppedClockSuffixBoundsCorrected, fixed-agent 24n bound, stopped marked-word
transfer, head-offset coupling, and L7 count must be joined to the actual
clockResetSeenAux witnesses.

No horizon-level probability assumption other than these two concrete
projection statements remains.
-/

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/-! ## The paper's fixed clockwise sweep word -/

def lemma5ClockwiseSweepWord (n : Nat) : DetSchedule n :=
  List.ofFn (fun i : Fin n => i)

@[simp] theorem lemma5ClockwiseSweepWord_length (n : Nat) :
    (lemma5ClockwiseSweepWord n).length = n := by
  simp [lemma5ClockwiseSweepWord]

private theorem lemma5Sweep_add_congr {a b c d : Nat}
    (h1 : a = b) (h2 : c = d) : a + c = b + d := by
  rw [h1, h2]

private theorem lemma5FixedWordHorizon_eq (n : Nat) :
    2 * n * (n + 2 * n) = 6 * n * n := by
  calc
    2 * n * (n + 2 * n) =
        (2 * n) * n + (2 * n) * (2 * n) := by
      rw [Nat.mul_add]
    _ = 2 * (n * n) + 4 * (n * n) := by
      exact lemma5Sweep_add_congr
        (Nat.mul_assoc 2 n n)
        (by
          calc
            (2 * n) * (2 * n) =
                (2 * 2) * (n * n) := by
              ac_rfl
            _ = 4 * (n * n) := by rfl)
    _ = (2 + 4) * (n * n) :=
      (Nat.add_mul 2 4 (n * n)).symm
    _ = 6 * (n * n) := by rfl
    _ = 6 * n * n :=
      (Nat.mul_assoc 6 n n).symm

/-- Pure scheduler count for the 6n² traversal subwindow. -/
theorem lemma5ClockwiseSweepWord_miss_scaled (n : Nat) :
    fixedWordMissCount
          (lemma5ClockwiseSweepWord n)
          (lemma5PaperSweepHorizon n) *
        2 ^ (2 * n) ≤
      n ^ lemma5PaperSweepHorizon n := by
  have h :=
    fixedWordMissCount_mul_twoPow_le_of_length
      (lemma5ClockwiseSweepWord n)
      n (2 * n)
      (lemma5ClockwiseSweepWord_length n)
  dsimp at h
  rw [lemma5FixedWordHorizon_eq n] at h
  simpa [lemma5PaperSweepHorizon] using h

/-! ## Small Nat scale conversions -/

private theorem nat_le_two_pow_self_sweepMid (n : Nat) :
    n ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.pow_succ]
      have hp : 0 < 2 ^ n :=
        Nat.pow_pos (by omega)
      omega

theorem nat_le_two_pow_two_mul_sweepMid (n : Nat) :
    n ≤ 2 ^ (2 * n) := by
  have hself :
      n ≤ 2 ^ n :=
    nat_le_two_pow_self_sweepMid n
  have hmono :
      2 ^ n ≤ 2 ^ (2 * n) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact Nat.le_trans hself hmono

private theorem lemma5SweepQuadratic_add (n : Nat) :
    2 * n * n + 6 * n * n = 8 * n * n := by
  calc
    2 * n * n + 6 * n * n =
        2 * (n * n) + 6 * (n * n) := by
      exact lemma5Sweep_add_congr
        (Nat.mul_assoc 2 n n)
        (Nat.mul_assoc 6 n n)
    _ = (2 + 6) * (n * n) :=
      (Nat.add_mul 2 6 (n * n)).symm
    _ = 8 * (n * n) := by rfl
    _ = 8 * n * n :=
      (Nat.mul_assoc 8 n n).symm

private theorem lemma5OuterSweep_eq_horizon (n : Nat) :
    (lemma5ArmHorizon n + 2 * n * n) +
        lemma5PaperSweepHorizon n =
      lemma5iHorizon n := by
  unfold lemma5PaperSweepHorizon
    lemma5iHorizon lemma5SweepHorizon
  rw [Nat.add_assoc, lemma5SweepQuadratic_add]

/-!
## Single remaining concrete splice

Clause 1 is deliberately a domination, not another probability theorem:
once a max reset arm has occurred, every concrete traversal-bad full word is
charged to a miss of the fixed clockwise word in the 6n² paper sweep. The
factor n^(arm + 2n²) is exactly the free arm prefix plus the frozen padding.

Clause 2 is the corresponding latest-reset bind for C_mid. Its intended
discharge on current main is:

* fixedAgent24nBound / stoppedPredictableHost24nBound for each fixed
  agent's post-reset incident load in the 6n² paper sweep;
* StoppedClockSuffixBoundsCorrected and clockSuffixTickLotteryBridge for
  the suffix starting at the actual reset;
* stoppedMarkedWordTransfer, wlgHeadOffsetBounds, and lotteryCountBounds for
  the clock-lottery upper tail;
* neverLeaderless to turn the clock/mode condition into midPhysicalB.

The Prop contains no new transition law and no asymptotic statement.
-/
def Lemma5iSweepMidPhysicalCountSplice : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (hkappa : 48 * psi ≤ kappa)
      (hnpow : n ≤ 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    neverLeaderless ring C →
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring →
    StoppedClockSuffixBoundsCorrected →
    ModeStoppedTreeTransfer →
    PredictableHostTails →
    WLGHeadOffsetBounds →
    LotteryCountBounds →
    And
      (lemma5iTraversalFailureCount ring C ≤
        n ^ (lemma5ArmHorizon n + 2 * n * n) *
          fixedWordMissCount
            (lemma5ClockwiseSweepWord n)
            (lemma5PaperSweepHorizon n))
      (lemma5iMidClockFailureCount ring C * 2 ^ psi ≤
        n ^ lemma5iHorizon n)

/-!
The requested frozen leaf follows from the single splice.

For traversal, the accepted fixed-word theorem supplies scale 2^(2n),
which dominates the required factor n. For C_mid, the splice supplies scale
2^psi, and the frozen hypothesis n ≤ 2^psi gives the same conversion.
Both estimates are actually one factor 2 stronger than the interface needs.
-/
theorem lemma5iSweepMidCount
    (hsplice : Lemma5iSweepMidPhysicalCountSplice) :
    Lemma5iSweepMidCount := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C
  intro hcnz hlineage hclock hmarked hpredict hhead hlottery

  have hs :=
    hsplice hn3 hpsi hkappa hnpow
      ring C hcnz hlineage hclock hmarked
      hpredict hhead hlottery

  constructor
  · have hdom := hs.1
    have hscaled :=
      Nat.mul_le_mul_right (2 ^ (2 * n)) hdom
    have hmiss :=
      lemma5ClockwiseSweepWord_miss_scaled n
    have hmissPad :=
      Nat.mul_le_mul_left
        (n ^ (lemma5ArmHorizon n + 2 * n * n))
        hmiss
    have hnscale :
        n ≤ 2 ^ (2 * n) :=
      nat_le_two_pow_two_mul_sweepMid n
    calc
      n * lemma5iTraversalFailureCount ring C =
          lemma5iTraversalFailureCount ring C * n := by
        ac_rfl
      _ ≤
          lemma5iTraversalFailureCount ring C *
            2 ^ (2 * n) :=
        Nat.mul_le_mul_left
          (lemma5iTraversalFailureCount ring C)
          hnscale
      _ ≤
          (n ^ (lemma5ArmHorizon n + 2 * n * n) *
              fixedWordMissCount
                (lemma5ClockwiseSweepWord n)
                (lemma5PaperSweepHorizon n)) *
            2 ^ (2 * n) :=
        hscaled
      _ =
          n ^ (lemma5ArmHorizon n + 2 * n * n) *
            (fixedWordMissCount
                (lemma5ClockwiseSweepWord n)
                (lemma5PaperSweepHorizon n) *
              2 ^ (2 * n)) := by
        ac_rfl
      _ ≤
          n ^ (lemma5ArmHorizon n + 2 * n * n) *
            n ^ lemma5PaperSweepHorizon n :=
        hmissPad
      _ =
          n ^
            ((lemma5ArmHorizon n + 2 * n * n) +
              lemma5PaperSweepHorizon n) := by
        rw [Nat.pow_add (m := lemma5ArmHorizon n + 2 * n * n)]
      _ = n ^ lemma5iHorizon n := by
        rw [lemma5OuterSweep_eq_horizon]
      _ ≤ 2 * n ^ lemma5iHorizon n := by
        omega

  · have hmid := hs.2
    calc
      n * lemma5iMidClockFailureCount ring C =
          lemma5iMidClockFailureCount ring C * n := by
        ac_rfl
      _ ≤
          lemma5iMidClockFailureCount ring C * 2 ^ psi :=
        Nat.mul_le_mul_left
          (lemma5iMidClockFailureCount ring C)
          hnpow
      _ ≤ n ^ lemma5iHorizon n :=
        hmid
      _ ≤ 2 * n ^ lemma5iHorizon n := by
        omega

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5ClockwiseSweepWord_length
#print axioms PPL.Modes.Lemma5.lemma5ClockwiseSweepWord_miss_scaled
#print axioms PPL.Modes.Lemma5.nat_le_two_pow_two_mul_sweepMid
#print axioms PPL.Modes.Lemma5.lemma5iSweepMidCount
