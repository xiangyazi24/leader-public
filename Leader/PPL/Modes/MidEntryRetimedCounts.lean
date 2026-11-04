import Leader.PPL.Modes.MidEntryRetimedSplit
import Leader.PPL.Modes.MidEntryLatestResetSuffixBound


namespace PPL.Modes.Lemma5


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9


/-!
The imported live traversal projection is a fixed-arm theorem:
its pre argument has length exactly lemma5ArmHorizon n.  A first-max
stopping prefix in the retimed definition has variable length j <= that
horizon, so the existing theorem cannot literally be instantiated with that
shorter prefix.  The recursive retimed Aux definitions are also private to
Lemma5iRetimedSplit, so an importing file has no public eliminator exposing
the first-hit decomposition.


This is therefore the exact public-boundary stopping splice needed for the
traversal half.  It contains no new tail estimate: the quantitative input is
still Lemma5iTraversalLiveSuffixPhysicalProjection.  The intended proof is
the finite first-hit/Kraft sum.  The no-max nodes are prefix-closed and the
terminal first-max prefixes are prefix-free; a stop at depth j carries
n^(lemma5ArmHorizon n - j) arm completions, so summing terminal cylinders
costs only n^lemma5ArmHorizon n, not an extra arm-length factor.
-/
def Lemma5iRetimedTraversalFirstMaxCountSplice : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    Lemma5iTraversalLiveSuffixPhysicalProjection ->
    lemma5iRetimedTraversalFailureCount ring C <=
      n ^ (lemma5ArmHorizon n + 2 * n * n) *
        fixedWordMissCount
          (lemma5ClockwiseSweepWord n)
          (lemma5PaperSweepHorizon n)


/-!
The analogous public-boundary splice for C_mid.  Its quantitative suffix
input is the already-proved fixed-arm theorem
lemma5iMidLatestResetSuffixBound_proved.  Again, only the variable first-max
boundary is new; the stopped-clock/encounter/lottery estimates are not.
-/
def Lemma5iRetimedMidFirstMaxCountSplice : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    neverLeaderless ring C ->
    StoppedClockSuffixBoundsCorrected ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    Lemma5iMidLatestResetSuffixBound ->
    lemma5iRetimedMidClockFailureCount ring C * 2 ^ psi <=
      n ^ lemma5iHorizon n


/--
Worst stopping time: the first max is reached only after the final arm
letter.  The entire frozen 8*n^2 suffix is still present, and after consuming
the paper 6*n^2 window exactly 2*n^2 letters remain as free padding.
-/
theorem lemma5iRetimedLastArmPadding (n : Nat) :
    lemma5PaperSweepHorizon n +
        2 * n * n =
      lemma5SweepHorizon n := by
  unfold lemma5PaperSweepHorizon
    lemma5SweepHorizon
  calc
    6 * n * n + 2 * n * n =
        6 * (n * n) + 2 * (n * n) := by
      rw [Nat.mul_assoc, Nat.mul_assoc]
    _ = (6 + 2) * (n * n) :=
      (Nat.add_mul 6 2 (n * n)).symm
    _ = 8 * n * n := by
      rw [Nat.mul_assoc]


private theorem lemma5iRetimedOuterSweep_eq_horizon (n : Nat) :
    (lemma5ArmHorizon n + 2 * n * n) +
        lemma5PaperSweepHorizon n =
      lemma5iHorizon n := by
  unfold lemma5iHorizon
  rw [Nat.add_assoc]
  rw [Nat.add_comm
        (2 * n * n)
        (lemma5PaperSweepHorizon n)]
  rw [lemma5iRetimedLastArmPadding]


/--
Once the two first-max count splices are supplied, the residual
Lemma5iSweepMidCountRetimed closes with exactly the existing frozen algebra.


The traversal branch reuses the 6*n^2 fixed-word miss theorem and
n <= 2^(2*n).  The mid branch reuses the latest-reset suffix theorem and
n <= 2^psi.
-/
theorem lemma5iSweepMidCountRetimed_closed
    (hTraversalProjection :
      Lemma5iTraversalLiveSuffixPhysicalProjection)
    (hMidProjection :
      Lemma5iMidLatestResetWordProjection)
    (hTraversalSplice :
      Lemma5iRetimedTraversalFirstMaxCountSplice)
    (hMidSplice :
      Lemma5iRetimedMidFirstMaxCountSplice) :
    Lemma5iSweepMidCountRetimed := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C
  intro hcnz hlineage hclock hmarked
  intro hpredict hhead hlottery


  have hTraversal :=
    hTraversalSplice
      hn3 hpsi hkappa
      ring C
      hlineage
      hTraversalProjection


  have hMidFixed :
      Lemma5iMidLatestResetSuffixBound :=
    lemma5iMidLatestResetSuffixBound_proved
      hMidProjection


  have hMid :=
    hMidSplice
      hn3 hpsi hkappa hnpow
      ring C
      hcnz hclock hmarked
      hpredict hhead hlottery
      hMidFixed


  constructor
  · have hscaled :=
      Nat.mul_le_mul_right
        (2 ^ (2 * n)) hTraversal
    have hmiss :=
      lemma5ClockwiseSweepWord_miss_scaled n
    have hmissPad :=
      Nat.mul_le_mul_left
        (n ^
          (lemma5ArmHorizon n +
            2 * n * n))
        hmiss
    have hnscale :
        n <= 2 ^ (2 * n) :=
      nat_le_two_pow_two_mul_sweepMid n
    calc
      n * lemma5iRetimedTraversalFailureCount ring C =
          lemma5iRetimedTraversalFailureCount ring C * n := by
        ac_rfl
      _ <=
          lemma5iRetimedTraversalFailureCount ring C *
            2 ^ (2 * n) :=
        Nat.mul_le_mul_left
          (lemma5iRetimedTraversalFailureCount ring C)
          hnscale
      _ <=
          (n ^
              (lemma5ArmHorizon n +
                2 * n * n) *
            fixedWordMissCount
              (lemma5ClockwiseSweepWord n)
              (lemma5PaperSweepHorizon n)) *
            2 ^ (2 * n) :=
        hscaled
      _ =
          n ^
              (lemma5ArmHorizon n +
                2 * n * n) *
            (fixedWordMissCount
                (lemma5ClockwiseSweepWord n)
                (lemma5PaperSweepHorizon n) *
              2 ^ (2 * n)) := by
        ac_rfl
      _ <=
          n ^
              (lemma5ArmHorizon n +
                2 * n * n) *
            n ^ lemma5PaperSweepHorizon n :=
        hmissPad
      _ =
          n ^
            ((lemma5ArmHorizon n +
                2 * n * n) +
              lemma5PaperSweepHorizon n) := by
        rw [Nat.pow_add
          (m :=
            lemma5ArmHorizon n +
              2 * n * n)]
      _ = n ^ lemma5iHorizon n := by
        rw [lemma5iRetimedOuterSweep_eq_horizon]
      _ <= 2 * n ^ lemma5iHorizon n := by
        omega


  · calc
      n * lemma5iRetimedMidClockFailureCount ring C =
          lemma5iRetimedMidClockFailureCount ring C * n := by
        ac_rfl
      _ <=
          lemma5iRetimedMidClockFailureCount ring C *
            2 ^ psi :=
        Nat.mul_le_mul_left
          (lemma5iRetimedMidClockFailureCount ring C)
          hnpow
      _ <= n ^ lemma5iHorizon n :=
        hMid
      _ <= 2 * n ^ lemma5iHorizon n := by
        omega


end PPL.Modes.Lemma5


#print axioms PPL.Modes.Lemma5.lemma5iRetimedLastArmPadding
#print axioms PPL.Modes.Lemma5.lemma5iSweepMidCountRetimed_closed
