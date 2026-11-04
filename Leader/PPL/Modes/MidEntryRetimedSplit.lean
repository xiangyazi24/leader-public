import Leader.PPL.Modes.MidEntryTraversalSuffixProjection
import Leader.PPL.Modes.MidEntryArmCount

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/-!
# Lemma 5(i): retime traversal/C_mid at the first max-reset state

A historical max reset in the arm does not imply that signalR = kappa is
still present at the fixed arm boundary: one completed local hit run can
decrement an old max signal before that boundary.  Rather than add a new
refresh-versus-first-decrement probability theorem, this file starts the
paper 6*n^2 traversal/C_mid window at the first configuration in the arm
prefix for which maxResetSignalB is true.

Phase A and the harmless phase-B reset-lineage summand are unchanged.
Only phases C and D are retimed.
-/

/-! ## Retimed Boolean events -/

private def lemma5iRetimedTraversalBadAux
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    Config n psi kappa -> Nat -> DetSchedule n -> Bool
  | C, 0, word =>
      if maxResetSignalB C then
        !allClockResetsSeenB ring C
          (word.take (lemma5PaperSweepHorizon n))
      else
        false
  | C, fuel + 1, [] =>
      if maxResetSignalB C then
        !allClockResetsSeenB ring C []
      else
        false
  | C, fuel + 1, e :: rest =>
      if maxResetSignalB C then
        !allClockResetsSeenB ring C
          ((e :: rest).take (lemma5PaperSweepHorizon n))
      else
        lemma5iRetimedTraversalBadAux
          ring (pplStep ring C e) fuel rest

private def lemma5iRetimedMidClockBadAux
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    Config n psi kappa -> Nat -> DetSchedule n -> Bool
  | C, 0, word =>
      if maxResetSignalB C then
        let sweep :=
          word.take (lemma5PaperSweepHorizon n)
        allClockResetsSeenB ring C sweep &&
          !(reachesAux ring midPhysicalB C sweep)
      else
        false
  | C, fuel + 1, [] =>
      if maxResetSignalB C then
        allClockResetsSeenB ring C [] &&
          !(reachesAux ring midPhysicalB C [])
      else
        false
  | C, fuel + 1, e :: rest =>
      if maxResetSignalB C then
        let sweep :=
          (e :: rest).take
            (lemma5PaperSweepHorizon n)
        allClockResetsSeenB ring C sweep &&
          !(reachesAux ring midPhysicalB C sweep)
      else
        lemma5iRetimedMidClockBadAux
          ring (pplStep ring C e) fuel rest

/-- Phase C, retimed to the first max-reset configuration reached no later
than the end of the arm window. -/
def lemma5iRetimedTraversalBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) : Bool :=
  lemma5iRetimedTraversalBadAux
    ring C (lemma5ArmHorizon n) word

/-- Phase D, using the same first-max stopping state and the same following
paper 6*n^2 window. -/
def lemma5iRetimedMidClockBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) : Bool :=
  lemma5iRetimedMidClockBadAux
    ring C (lemma5ArmHorizon n) word

def lemma5iRetimedTraversalFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Nat :=
  (allSchedules n (lemma5iHorizon n)).countP
    (lemma5iRetimedTraversalBadB ring C)

def lemma5iRetimedMidClockFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Nat :=
  (allSchedules n (lemma5iHorizon n)).countP
    (lemma5iRetimedMidClockBadB ring C)

/-! ## Prefix closure and wordwise retimed coverage -/

private theorem lemma5iRetimed_reachesAux_false_take
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa -> Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n) :
    reachesAux ring good C word = false ->
      forall k,
        reachesAux ring good C (word.take k) = false := by
  induction word generalizing C with
  | nil =>
      intro hfalse k
      simpa [reachesAux] using hfalse
  | cons e rest ih =>
      intro hfalse k
      have hgood : good C = false := by
        cases hg : good C with
        | false =>
            rfl
        | true =>
            simp [reachesAux, hg] at hfalse
      have htail :
          reachesAux ring good
              (pplStep ring C e) rest = false := by
        simpa [reachesAux, hgood] using hfalse
      cases k with
      | zero =>
          simpa [reachesAux, hgood]
      | succ k =>
          have htaken :=
            ih (C := pplStep ring C e) htail k
          simpa [reachesAux, hgood] using htaken

private theorem lemma5iRetimedCoverAux
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (fuel : Nat)
    (word : DetSchedule n)
    (hfull :
      reachesAux ring midPhysicalB C word = false) :
    ((!reachesAux ring maxResetSignalB C
        (word.take fuel)) ||
      (lemma5iRetimedTraversalBadAux
          ring C fuel word ||
        lemma5iRetimedMidClockBadAux
          ring C fuel word)) = true := by
  induction fuel generalizing C word with
  | zero =>
      cases hm : maxResetSignalB C with
      | false =>
          simp [reachesAux, hm,
            lemma5iRetimedTraversalBadAux,
            lemma5iRetimedMidClockBadAux]
      | true =>
          have hmid :=
            lemma5iRetimed_reachesAux_false_take
              ring midPhysicalB C word hfull
              (lemma5PaperSweepHorizon n)
          cases hs :
              allClockResetsSeenB ring C
                (word.take
                  (lemma5PaperSweepHorizon n)) with
          | false =>
              simp [reachesAux, hm, hs,
                lemma5iRetimedTraversalBadAux,
                lemma5iRetimedMidClockBadAux]
          | true =>
              simp [reachesAux, hm, hs, hmid,
                lemma5iRetimedTraversalBadAux,
                lemma5iRetimedMidClockBadAux]
  | succ fuel ih =>
      cases hm : maxResetSignalB C with
      | true =>
          have hmid :=
            lemma5iRetimed_reachesAux_false_take
              ring midPhysicalB C word hfull
              (lemma5PaperSweepHorizon n)
          cases hs :
              allClockResetsSeenB ring C
                (word.take
                  (lemma5PaperSweepHorizon n)) with
          | false =>
              cases word <;>
                (try simp only [List.take_nil, reachesAux] at hs hmid hfull) <;>
                simp [reachesAux, hm, hfull, hs,
                  lemma5iRetimedTraversalBadAux,
                  lemma5iRetimedMidClockBadAux]
          | true =>
              cases word <;>
                (try simp only [List.take_nil, reachesAux] at hs hmid hfull) <;>
                simp [reachesAux, hm, hfull, hs, hmid,
                  lemma5iRetimedTraversalBadAux,
                  lemma5iRetimedMidClockBadAux]
      | false =>
          cases word with
          | nil =>
              simp [reachesAux, hm,
                lemma5iRetimedTraversalBadAux,
                lemma5iRetimedMidClockBadAux]
          | cons e rest =>
              cases hcur : midPhysicalB C with
              | true =>
                  simp [reachesAux, hcur] at hfull
              | false =>
                  have htail :
                      reachesAux ring midPhysicalB
                          (pplStep ring C e) rest = false := by
                    simpa [reachesAux, hcur] using hfull
                  have ht :=
                    ih
                      (C := pplStep ring C e)
                      (word := rest)
                      htail
                  simpa [reachesAux, hm,
                    lemma5iRetimedTraversalBadAux,
                    lemma5iRetimedMidClockBadAux]
                    using ht

/-- Every full Lemma-5(i) failure is covered by the old arm miss or one of
the two first-max retimed C/D events.  No boundary-live assumption occurs. -/
theorem lemma5iRetimedFailureCover
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hbad :
      (!(reachesAux ring midPhysicalB C word)) = true) :
    (lemma5iLeaderArmBadB ring C word ||
      (lemma5iRetimedTraversalBadB ring C word ||
        lemma5iRetimedMidClockBadB ring C word)) = true := by
  have hfull :
      reachesAux ring midPhysicalB C word = false := by
    cases h :
        reachesAux ring midPhysicalB C word with
    | false =>
        rfl
    | true =>
        simp [h] at hbad
  have h :=
    lemma5iRetimedCoverAux
      ring C (lemma5ArmHorizon n) word hfull
  simpa [lemma5iLeaderArmBadB,
    lemma5iArmPrefix,
    lemma5iRetimedTraversalBadB,
    lemma5iRetimedMidClockBadB]
    using h

/-! ## Count lift -/

private theorem lemma5iRetimed_countP_mono
    {A : Type}
    (xs : List A)
    (p q : A -> Bool)
    (hpq :
      forall x,
        p x = true ->
          q x = true) :
    xs.countP p <= xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons,
        List.countP_cons]
      cases hp : p x with
      | false =>
          cases hq : q x <;>
            simp [hp, hq] <;>
            omega
      | true =>
          have hqx : q x = true :=
            hpq x hp
          simp [hp, hqx]
          omega

private theorem lemma5iRetimed_countP_or_le_add
    {A : Type}
    (xs : List A)
    (p q : A -> Bool) :
    xs.countP (fun x => p x || q x) <=
      xs.countP p + xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons,
        List.countP_cons,
        List.countP_cons]
      cases hp : p x <;>
        cases hq : q x <;>
        simp [hp, hq] <;>
        omega

theorem lemma5iFailureCount_le_retimed
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) :
    lemma5iFailureCount ring C <=
      lemma5iLeaderArmFailureCount ring C +
        lemma5iRetimedTraversalFailureCount ring C +
        lemma5iRetimedMidClockFailureCount ring C := by
  have hmono :
      (allSchedules n
          (lemma5iHorizon n)).countP
          (fun word =>
            !(reachesAux ring midPhysicalB C word)) <=
        (allSchedules n
          (lemma5iHorizon n)).countP
          (fun word =>
            lemma5iLeaderArmBadB ring C word ||
              (lemma5iRetimedTraversalBadB
                  ring C word ||
                lemma5iRetimedMidClockBadB
                  ring C word)) := by
    apply lemma5iRetimed_countP_mono
    intro word hbad
    exact
      lemma5iRetimedFailureCover
        ring C word hbad
  have houter :=
    lemma5iRetimed_countP_or_le_add
      (allSchedules n (lemma5iHorizon n))
      (lemma5iLeaderArmBadB ring C)
      (fun word =>
        lemma5iRetimedTraversalBadB ring C word ||
          lemma5iRetimedMidClockBadB ring C word)
  have hinner :=
    lemma5iRetimed_countP_or_le_add
      (allSchedules n (lemma5iHorizon n))
      (lemma5iRetimedTraversalBadB ring C)
      (lemma5iRetimedMidClockBadB ring C)
  unfold lemma5iFailureCount
    lemma5iLeaderArmFailureCount
    lemma5iRetimedTraversalFailureCount
    lemma5iRetimedMidClockFailureCount
  omega

/-! ## Replacement four-way split -/

/-- Same four-charge accounting shape as Lemma5iFailureSplit.  Phase B is
kept as a nonnegative summand so the downstream coefficient-8 bridge does not
change; phases C and D are the first-max retimed events above. -/
def Lemma5iFailureSplitRetimed : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    neverLeaderless ring C ->
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    lemma5iFailureCount ring C <=
      lemma5iLeaderArmFailureCount ring C +
        lemma5iResetLineageFailureCount ring C +
        lemma5iRetimedTraversalFailureCount ring C +
        lemma5iRetimedMidClockFailureCount ring C

theorem lemma5iFailureSplitRetimed :
    Lemma5iFailureSplitRetimed := by
  intro n psi kappa
  intro _hn3 _hpsi _hkappa _hnpow
  intro ring C
  intro _hcnz _hlineage
  have h :=
    lemma5iFailureCount_le_retimed
      ring C
  omega

/-!
The only remaining physical/counting leaf after the retiming.  It is the
same consumer shape as the old Lemma5iSweepMidCount, but its C/D windows are
rooted at the first max reset rather than the fixed arm boundary.
-/
def Lemma5iSweepMidCountRetimed : Prop :=
  forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    neverLeaderless ring C ->
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    StoppedClockSuffixBoundsCorrected ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    And
      (n * lemma5iRetimedTraversalFailureCount ring C <=
        2 * n ^ lemma5iHorizon n)
      (n * lemma5iRetimedMidClockFailureCount ring C <=
        2 * n ^ lemma5iHorizon n)

/-- Reduction to the unchanged final part-(i) target.  Thus the old
lemma5Bridge_of_split consumer only needs its part-(i) producer replaced by
this retimed version; Lemma5iWordBound itself and the coefficient 8 are
unchanged. -/
theorem lemma5iWordBound_of_retimedCounts
    (hiArmReset : Lemma5iArmResetCount)
    (hiSweepMid : Lemma5iSweepMidCountRetimed) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    neverLeaderless ring C ->
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    StoppedClockSuffixBoundsCorrected ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    Lemma5iWordBound ring C := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C
  intro hcnz hlineage hclock hmarked
  intro hpredict hhead hlottery

  have hsplit :=
    lemma5iFailureSplitRetimed
      hn3 hpsi hkappa hnpow
      ring C hcnz hlineage

  have harmReset :=
    hiArmReset
      hn3 hpsi hkappa hnpow
      ring C hcnz hlineage
      hmarked hpredict hhead hlottery

  have hsweepMid :=
    hiSweepMid
      hn3 hpsi hkappa hnpow
      ring C hcnz hlineage
      hclock hmarked hpredict hhead hlottery

  have hsplit' :=
    Nat.mul_le_mul_left n hsplit
  simp only [Nat.mul_add] at hsplit'

  have h01 :
      n * lemma5iLeaderArmFailureCount ring C +
          n * lemma5iResetLineageFailureCount ring C <=
        4 * n ^ lemma5iHorizon n := by
    have h :=
      Nat.add_le_add
        harmReset.1 harmReset.2
    omega

  have h23 :
      n * lemma5iRetimedTraversalFailureCount ring C +
          n * lemma5iRetimedMidClockFailureCount ring C <=
        4 * n ^ lemma5iHorizon n := by
    have h :=
      Nat.add_le_add
        hsweepMid.1 hsweepMid.2
    omega

  unfold Lemma5iWordBound
  calc
    n * lemma5iFailureCount ring C <=
        n * lemma5iLeaderArmFailureCount ring C +
          n * lemma5iResetLineageFailureCount ring C +
          n * lemma5iRetimedTraversalFailureCount ring C +
          n * lemma5iRetimedMidClockFailureCount ring C :=
      hsplit'
    _ <=
        4 * n ^ lemma5iHorizon n +
          4 * n ^ lemma5iHorizon n := by
      omega
    _ = 8 * n ^ lemma5iHorizon n := by
      omega


/-- Phase-B-free assembly.  The retimed cover never uses the reset-lineage
event, so only the (unconditional) leader-arm count and the two retimed
counts are needed.  This removes Lemma5iResetLineageWordCharge from the
Lemma 5(i) route. -/
theorem lemma5iWordBound_of_retimedCounts_noResetLineage
    (hiSweepMid : Lemma5iSweepMidCountRetimed) :
    forall {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    neverLeaderless ring C ->
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring ->
    StoppedClockSuffixBoundsCorrected ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    Lemma5iWordBound ring C := by
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring C
  intro hcnz hlineage hclock hmarked
  intro hpredict hhead hlottery
  have hsplit :=
    lemma5iFailureCount_le_retimed ring C
  have harm :=
    lemma5iLeaderArmCount hn3 hpsi hkappa hnpow ring C hcnz
  have hsweepMid :=
    hiSweepMid
      hn3 hpsi hkappa hnpow
      ring C hcnz hlineage
      hclock hmarked hpredict hhead hlottery
  have hsplit' :=
    Nat.mul_le_mul_left n hsplit
  simp only [Nat.mul_add] at hsplit'
  have h1 := hsweepMid.1
  have h2 := hsweepMid.2
  unfold Lemma5iWordBound
  omega

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5iRetimedFailureCover
#print axioms PPL.Modes.Lemma5.lemma5iFailureCount_le_retimed
#print axioms PPL.Modes.Lemma5.lemma5iFailureSplitRetimed
#print axioms PPL.Modes.Lemma5.lemma5iWordBound_of_retimedCounts

#print axioms PPL.Modes.Lemma5.lemma5iWordBound_of_retimedCounts_noResetLineage
