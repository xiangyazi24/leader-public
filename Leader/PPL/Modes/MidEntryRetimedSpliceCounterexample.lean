import Leader.PPL.Modes.MidEntryRetimedCounts


namespace PPL.Modes.Lemma5

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9


set_option autoImplicit false
set_option Elab.async false


/-!
# Lemma 5(i) retimed first-max splice audit


The finite first-terminal/Kraft algebra is not the missing fact in the two
public residuals from Lemma5iRetimedCounts.


At a retimed terminal, the paper window starts immediately after the first
letter whose successor has maxResetSignalB = true.  By contrast,
Lemma5iTraversalLiveSuffixPhysicalProjection and
Lemma5iMidLatestResetSuffixBound quantify over a physical prefix whose length
is exactly lemma5ArmHorizon n.  The unused arm letters therefore occur before
their continuation, while a first-terminal bind must put unused first-stage
letters after the endpoint-dependent continuation.


The one-symbol example below isolates that mismatch.  It has a first hit after
one letter, where the bad predicate is true, but one more physical letter
destroys the bad state.  Hence a state-uniform fixed-arm bound at depth two is
zero even though the immediate first-hit continuation count is one.


This is a counterexample to the advertised pure-counting inference used for
both residuals.  It is not a proof of the negation of either full PPL Prop:
those Props also quantify over protocol-specific global premises.  A proof of
either full Prop needs a current-max continuation theorem, two exact interfaces
for which are recorded at the end of this file.
-/


/-! ## A finite counterexample to fixed-arm -> first-hit continuation -/


inductive RetimedSpliceToyState where
  | cold
  | hit
  | sink
  deriving DecidableEq


private def retimedSpliceToyEdge : Fin 1 :=
  ⟨0, by decide⟩


private def retimedSpliceToyStep :
    RetimedSpliceToyState -> Fin 1 -> RetimedSpliceToyState
  | .cold, _ => .hit
  | .hit, _ => .sink
  | .sink, _ => .sink


private def retimedSpliceToyRun :
    RetimedSpliceToyState ->
      List (Fin 1) -> RetimedSpliceToyState
  | s, [] => s
  | s, e :: rest =>
      retimedSpliceToyRun
        (retimedSpliceToyStep s e) rest


private def retimedSpliceToyBadB :
    RetimedSpliceToyState -> Bool
  | .hit => true
  | .cold => false
  | .sink => false


private def retimedSpliceToyBoolCount
    (b : Bool) : Nat :=
  if b then 1 else 0


/-- The fixed-arm observer waits for two physical letters. -/
private def retimedSpliceToyFixedArmCount
    (s : RetimedSpliceToyState) : Nat :=
  retimedSpliceToyBoolCount
    (retimedSpliceToyBadB
      (retimedSpliceToyRun s
        [retimedSpliceToyEdge,
         retimedSpliceToyEdge]))


/-- The first-hit observer stops after the first physical letter. -/
private def retimedSpliceToyFirstHitCount : Nat :=
  retimedSpliceToyBoolCount
    (retimedSpliceToyBadB
      (retimedSpliceToyRun
        .cold [retimedSpliceToyEdge]))


private theorem retimedSpliceToyRun_two
    (s : RetimedSpliceToyState) :
    retimedSpliceToyRun s
        [retimedSpliceToyEdge,
         retimedSpliceToyEdge] =
      .sink := by
  cases s <;> rfl


def RetimedSpliceToyFixedArmProjection : Prop :=
  forall s : RetimedSpliceToyState,
    retimedSpliceToyFixedArmCount s <= 0


private theorem
    retimedSpliceToyFixedArmProjection_proved :
    RetimedSpliceToyFixedArmProjection := by
  intro s
  unfold retimedSpliceToyFixedArmCount
  rw [retimedSpliceToyRun_two]
  change 0 <= 0
  exact Nat.le_refl 0


private theorem
    retimedSpliceToyFirstHitCount_eq_one :
    retimedSpliceToyFirstHitCount = 1 := by
  rfl


/--
Abstract form of the inference required by the proposed traversal splice:
a fixed-arm continuation estimate is treated as though it were an estimate
from the variable first-hit endpoint.
-/
def RetimedSpliceToyTraversalClaim : Prop :=
  RetimedSpliceToyFixedArmProjection ->
    retimedSpliceToyFirstHitCount <= 0


/--
The mid-clock splice has the same timing mismatch, independently of the
different suffix bad predicate used in the real protocol.
-/
def RetimedSpliceToyMidClaim : Prop :=
  RetimedSpliceToyFixedArmProjection ->
    retimedSpliceToyFirstHitCount <= 0


theorem retimedSpliceToyTraversalClaim_false :
    Not RetimedSpliceToyTraversalClaim := by
  intro h
  have hle :=
    h retimedSpliceToyFixedArmProjection_proved
  rw [retimedSpliceToyFirstHitCount_eq_one] at hle
  have hnot : Not ((1 : Nat) <= 0) := by
    decide
  exact hnot hle


theorem retimedSpliceToyMidClaim_false :
    Not RetimedSpliceToyMidClaim := by
  intro h
  have hle :=
    h retimedSpliceToyFixedArmProjection_proved
  rw [retimedSpliceToyFirstHitCount_eq_one] at hle
  have hnot : Not ((1 : Nat) <= 0) := by
    decide
  exact hnot hle


/-! ## The missing current-max continuation interfaces


These are the forms that an endpoint-retaining first-terminal bind can
consume.  The remaining first-stage letters are then pure Kraft padding after
the continuation, rather than physical letters inserted before it.
-/


/--
Traversal continuation started at the actual first-max physical endpoint.
The paper window is the first lemma5PaperSweepHorizon n letters of the
lemma5SweepHorizon n continuation; the remaining 2*n*n letters are free
padding.
-/
def Lemma5iRetimedTraversalCurrentMaxSuffixProjection : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (ring : DirectedRing n)
      (D : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    maxResetSignalB D = true ->
    (allSchedules n (lemma5SweepHorizon n)).countP
        (fun suffix =>
          !(allClockResetsSeenB ring D
            (suffix.take
              (lemma5PaperSweepHorizon n)))) <=
      n ^ (2 * n * n) *
        fixedWordMissCount
          (lemma5ClockwiseSweepWord n)
          (lemma5PaperSweepHorizon n)


/--
C_mid continuation started at the actual first-max physical endpoint.
This is the state-uniform terminal continuation estimate needed by the
first-terminal bind.  The existing Lemma5iMidLatestResetSuffixBound instead
starts its paper window only after a complete fixed arm prefix.
-/
def Lemma5iRetimedMidCurrentMaxSuffixBound : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (D : Config n psi kappa),
    neverLeaderless ring D ->
    StoppedClockSuffixBoundsCorrected ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    maxResetSignalB D = true ->
    (allSchedules n (lemma5SweepHorizon n)).countP
        (fun suffix =>
          let sweep :=
            suffix.take
              (lemma5PaperSweepHorizon n)
          allClockResetsSeenB ring D sweep &&
            !(reachesAux ring midPhysicalB D sweep)) *
        2 ^ psi <=
      n ^ lemma5SweepHorizon n


end PPL.Modes.Lemma5


#print axioms PPL.Modes.Lemma5.retimedSpliceToyTraversalClaim_false
#print axioms PPL.Modes.Lemma5.retimedSpliceToyMidClaim_false


