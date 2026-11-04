import Leader.PPL.Modes.MidEntrySweepCount


namespace PPL.Modes.Lemma5


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9


/-!
# Lemma 5(i): sweep / C_mid outer splice


Bounded-round status.


The original combined residual
Lemma5iSweepMidPhysicalCountSplice is reduced here to two strictly smaller
per-arm-suffix physical facts, one for each conjunct.


The outer scheduler algebra is completely discharged:


* split a full Lemma-5(i) word into the arm prefix and the 8*n^2 suffix;
* sum the per-arm traversal projection over all arm prefixes;
* sum the per-arm latest-reset C_mid estimate after multiplying by 2^psi;
* use the exact allSchedules cardinalities and Nat.pow_add.


What remains is protocol-local rather than scheduler algebra:


* Lemma5iTraversalSuffixPhysicalProjection:
  after fixing the arm prefix, the 8*n^2 traversal-bad suffix mass is bounded
  by the 2*n^2 padding times the fixed clockwise-word miss mass;


* Lemma5iMidLatestResetSuffixBound:
  after fixing the arm prefix, the latest-reset bind bounds the 8*n^2
  C_mid-bad suffix mass at scale 2^psi.  This is the precise place to consume
  stoppedClockSuffixBoundsCorrected, neverLeaderless, the fixed-agent
  encounter bound, stopped marked-word transfer, head-offset coupling, and
  the lottery count.


Current main has the analogous post-reset counting layer, but its
wordwise latest-reset physical projection is still isolated there as
Lemma5iiPostResetClockProjection.  No theorem on main presently supplies
either of the two physical suffix facts below.
-/


private def allSchedules_add_splice (n a b : Nat) :
    allSchedules n (a + b) =
      (allSchedules n a).flatMap (fun pre =>
        (allSchedules n b).map (fun suf => pre ++ suf)) := by
  induction b with
  | zero =>
      simp [allSchedules]
  | succ b ih =>
      rw [Nat.add_succ, allSchedules, ih]
      simp only [allSchedules, List.flatMap_assoc, List.map_flatMap,
        List.flatMap_map]
      congr
      funext pre
      congr
      funext suf
      rw [List.map_ofFn]
      congr 1
      funext e
      simp [List.append_assoc]


private def sum_map_le_splice
    {A : Type}
    (xs : List A)
    (f g : A -> Nat)
    (hfg : forall x, x ∈ xs -> f x <= g x) :
    (xs.map f).sum <= (xs.map g).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (hfg x (by simp))
        (ih (fun y hy => hfg y (by simp [hy])))


private def sum_map_const_splice
    {A : Type}
    (xs : List A) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.succ_mul, Nat.add_comm]


private def sum_map_mul_right_splice
    {A : Type}
    (xs : List A) (f : A -> Nat) (c : Nat) :
    (xs.map f).sum * c =
      (xs.map (fun x => f x * c)).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.add_mul]


/-! ## Per-arm suffix counts -/


def lemma5iTraversalSuffixFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre : DetSchedule n) : Nat :=
  ((allSchedules n (lemma5SweepHorizon n)).map
      (fun suf => pre ++ suf)).countP
    (lemma5iTraversalBadB ring C)


def lemma5iMidSuffixFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (pre : DetSchedule n) : Nat :=
  ((allSchedules n (lemma5SweepHorizon n)).map
      (fun suf => pre ++ suf)).countP
    (lemma5iMidClockBadB ring C)


private def traversalFailureCount_eq_suffixSum
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    lemma5iTraversalFailureCount ring C =
      ((allSchedules n (lemma5ArmHorizon n)).map
        (lemma5iTraversalSuffixFailureCount ring C)).sum := by
  unfold lemma5iTraversalFailureCount
    lemma5iTraversalSuffixFailureCount
  rw [show
      lemma5iHorizon n =
        lemma5ArmHorizon n + lemma5SweepHorizon n by rfl]
  rw [allSchedules_add_splice, List.countP_flatMap]
  rfl


private def midFailureCount_eq_suffixSum
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    lemma5iMidClockFailureCount ring C =
      ((allSchedules n (lemma5ArmHorizon n)).map
        (lemma5iMidSuffixFailureCount ring C)).sum := by
  unfold lemma5iMidClockFailureCount
    lemma5iMidSuffixFailureCount
  rw [show
      lemma5iHorizon n =
        lemma5ArmHorizon n + lemma5SweepHorizon n by rfl]
  rw [allSchedules_add_splice, List.countP_flatMap]
  rfl


/-!
## Residual 1: concrete traversal suffix projection


The arm prefix is fixed.  Thus this residual contains no free-arm factor.
The right side is exactly the paper 6*n^2 fixed-word miss numerator padded
by the remaining 2*n^2 scheduler letters.


A proof may choose the actual reset-lineage host/root determined by the arm
prefix and transfer the corresponding rotated clockwise traversal to
lemma5ClockwiseSweepWord by the fixed-word symmetry/counting machinery.
-/
def Lemma5iTraversalSuffixPhysicalProjection : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    forall pre : DetSchedule n,
      pre ∈ allSchedules n (lemma5ArmHorizon n) ->
      lemma5iTraversalSuffixFailureCount ring C pre <=
        n ^ (2 * n * n) *
          fixedWordMissCount
            (lemma5ClockwiseSweepWord n)
            (lemma5PaperSweepHorizon n)


/-!
## Residual 2: latest-reset C_mid suffix bound


Again the arm prefix is fixed.  This is the exact local target for the
latest-reset selection.  Its intended proof uses the supplied corrected
stopped-clock theorem at each selected ClockEpochStart, neverLeaderless for
the leader conjunct of midPhysicalB, the fixed-agent encounter bound, and the
already-proved marked-word/head-offset/lottery estimates.


Compared with the original combined residual, this statement has no outer
arm summation and no horizon recombination.
-/
def Lemma5iMidLatestResetSuffixBound : Prop :=
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
    forall pre : DetSchedule n,
      pre ∈ allSchedules n (lemma5ArmHorizon n) ->
      lemma5iMidSuffixFailureCount ring C pre * 2 ^ psi <=
        n ^ lemma5SweepHorizon n


/-! ## Conjunct 1: outer traversal bind -/


theorem lemma5iTraversalCountSplice
    (hprojection : Lemma5iTraversalSuffixPhysicalProjection) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    lemma5iTraversalFailureCount ring C <=
      n ^ (lemma5ArmHorizon n + 2 * n * n) *
        fixedWordMissCount
          (lemma5ClockwiseSweepWord n)
          (lemma5PaperSweepHorizon n) := by
  intro n psi kappa
  intro hn3 hpsi hkappa ring C hlineage


  have hpoint :
      forall pre : DetSchedule n,
        pre ∈ allSchedules n (lemma5ArmHorizon n) ->
        lemma5iTraversalSuffixFailureCount ring C pre <=
          n ^ (2 * n * n) *
            fixedWordMissCount
              (lemma5ClockwiseSweepWord n)
              (lemma5PaperSweepHorizon n) := by
    intro pre hpre
    exact
      hprojection hn3 hpsi hkappa
        ring C hlineage pre hpre


  have hsum :
      ((allSchedules n (lemma5ArmHorizon n)).map
        (lemma5iTraversalSuffixFailureCount ring C)).sum <=
      ((allSchedules n (lemma5ArmHorizon n)).map
        (fun _ =>
          n ^ (2 * n * n) *
            fixedWordMissCount
              (lemma5ClockwiseSweepWord n)
              (lemma5PaperSweepHorizon n))).sum :=
    sum_map_le_splice
      (allSchedules n (lemma5ArmHorizon n))
      (lemma5iTraversalSuffixFailureCount ring C)
      (fun _ =>
        n ^ (2 * n * n) *
          fixedWordMissCount
            (lemma5ClockwiseSweepWord n)
            (lemma5PaperSweepHorizon n))
      hpoint


  calc
    lemma5iTraversalFailureCount ring C =
        ((allSchedules n (lemma5ArmHorizon n)).map
          (lemma5iTraversalSuffixFailureCount ring C)).sum :=
      traversalFailureCount_eq_suffixSum ring C
    _ <=
        ((allSchedules n (lemma5ArmHorizon n)).map
          (fun _ =>
            n ^ (2 * n * n) *
              fixedWordMissCount
                (lemma5ClockwiseSweepWord n)
                (lemma5PaperSweepHorizon n))).sum :=
      hsum
    _ =
        (allSchedules n (lemma5ArmHorizon n)).length *
          (n ^ (2 * n * n) *
            fixedWordMissCount
              (lemma5ClockwiseSweepWord n)
              (lemma5PaperSweepHorizon n)) :=
      sum_map_const_splice
        (allSchedules n (lemma5ArmHorizon n))
        (n ^ (2 * n * n) *
          fixedWordMissCount
            (lemma5ClockwiseSweepWord n)
            (lemma5PaperSweepHorizon n))
    _ =
        n ^ lemma5ArmHorizon n *
          (n ^ (2 * n * n) *
            fixedWordMissCount
              (lemma5ClockwiseSweepWord n)
              (lemma5PaperSweepHorizon n)) := by
      rw [allSchedules_length]
    _ =
        n ^ (lemma5ArmHorizon n + 2 * n * n) *
          fixedWordMissCount
            (lemma5ClockwiseSweepWord n)
            (lemma5PaperSweepHorizon n) := by
      rw [Nat.pow_add]
      ac_rfl


/-! ## Conjunct 2: outer latest-reset bind -/


theorem lemma5iMidClockCountSplice
    (hbind : Lemma5iMidLatestResetSuffixBound) :
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
    lemma5iMidClockFailureCount ring C * 2 ^ psi <=
      n ^ lemma5iHorizon n := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow ring C
  intro hcnz hclock hmarked hpredict hhead hlottery


  have hpoint :
      forall pre : DetSchedule n,
        pre ∈ allSchedules n (lemma5ArmHorizon n) ->
        lemma5iMidSuffixFailureCount ring C pre * 2 ^ psi <=
          n ^ lemma5SweepHorizon n := by
    intro pre hpre
    exact
      hbind hn3 hpsi hkappa hnpow
        ring C hcnz hclock hmarked
        hpredict hhead hlottery pre hpre


  have hsum :
      ((allSchedules n (lemma5ArmHorizon n)).map
        (fun pre =>
          lemma5iMidSuffixFailureCount ring C pre *
            2 ^ psi)).sum <=
      ((allSchedules n (lemma5ArmHorizon n)).map
        (fun _ => n ^ lemma5SweepHorizon n)).sum :=
    sum_map_le_splice
      (allSchedules n (lemma5ArmHorizon n))
      (fun pre =>
        lemma5iMidSuffixFailureCount ring C pre *
          2 ^ psi)
      (fun _ => n ^ lemma5SweepHorizon n)
      hpoint


  calc
    lemma5iMidClockFailureCount ring C * 2 ^ psi =
        ((allSchedules n (lemma5ArmHorizon n)).map
          (lemma5iMidSuffixFailureCount ring C)).sum *
            2 ^ psi := by
      rw [midFailureCount_eq_suffixSum ring C]
    _ =
        ((allSchedules n (lemma5ArmHorizon n)).map
          (fun pre =>
            lemma5iMidSuffixFailureCount ring C pre *
              2 ^ psi)).sum :=
      sum_map_mul_right_splice
        (allSchedules n (lemma5ArmHorizon n))
        (lemma5iMidSuffixFailureCount ring C)
        (2 ^ psi)
    _ <=
        ((allSchedules n (lemma5ArmHorizon n)).map
          (fun _ => n ^ lemma5SweepHorizon n)).sum :=
      hsum
    _ =
        (allSchedules n (lemma5ArmHorizon n)).length *
          n ^ lemma5SweepHorizon n :=
      sum_map_const_splice
        (allSchedules n (lemma5ArmHorizon n))
        (n ^ lemma5SweepHorizon n)
    _ =
        n ^ lemma5ArmHorizon n *
          n ^ lemma5SweepHorizon n := by
      rw [allSchedules_length]
    _ =
        n ^ (lemma5ArmHorizon n + lemma5SweepHorizon n) := by
      rw [Nat.pow_add]
    _ = n ^ lemma5iHorizon n := by
      rfl


/-!
## Requested combined splice, conditional on the two minimized physical leaves


This theorem removes all outer counting from the original residual.  A later
physical round only has to prove the two per-arm suffix declarations above.
-/
theorem lemma5iSweepMidPhysicalCountSplice
    (hTraversal : Lemma5iTraversalSuffixPhysicalProjection)
    (hMid : Lemma5iMidLatestResetSuffixBound) :
    Lemma5iSweepMidPhysicalCountSplice := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C
  intro hcnz hlineage hclock hmarked hpredict hhead hlottery


  exact And.intro
    (lemma5iTraversalCountSplice
      hTraversal
      hn3 hpsi hkappa
      ring C hlineage)
    (lemma5iMidClockCountSplice
      hMid
      hn3 hpsi hkappa hnpow
      ring C hcnz hclock hmarked
      hpredict hhead hlottery)


end PPL.Modes.Lemma5


#print axioms PPL.Modes.Lemma5.lemma5iTraversalCountSplice
#print axioms PPL.Modes.Lemma5.lemma5iMidClockCountSplice
#print axioms PPL.Modes.Lemma5.lemma5iSweepMidPhysicalCountSplice
