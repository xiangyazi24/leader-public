import Leader.PPL.Modes.ConstructionMode

/-!
# P_PL Lemma 5: deterministic split

This file only splits the two finite-word claims of paper Lemma 5 into
small deterministic and counting obligations.  The assembly theorem at the
end uses no protocol transition reasoning.

Part (i) is charged in four named phases:
leader arm, reset-lineage survival, clockwise reset traversal, and the final
C_mid clock/mode condition.

Part (ii) is charged in two named phases:
too many fixed-agent encounters, and the residual post-reset clock event.
-/

namespace PPL.Modes.Lemma5

set_option autoImplicit false
set_option Elab.async false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/-! ## Concrete phase predicates and numerators for Lemma 5(i) -/

/-- Some physical resetting signal is still present. -/
def signalPresentB
    {n psi kappa : Nat}
    (C : Config n psi kappa) : Bool :=
  (List.ofFn
    (fun i : Fin n =>
      decide (0 < (C i).signalR.val))).foldl
        (fun acc b => acc || b) false

/-- Some max-TTL reset signal is present.  This is the physical witness
created by a leader arm before the sweep phase. -/
def maxResetSignalB
    {n psi kappa : Nat}
    (C : Config n psi kappa) : Bool :=
  (List.ofFn
    (fun i : Fin n =>
      decide ((C i).signalR.val = kappa))).foldl
        (fun acc b => acc || b) false

/-- Whether x experiences at least one actual Algorithm-4 clock reset while
the supplied schedule is consumed. -/
def clockResetSeenAux
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (x : Fin n) :
    Config n psi kappa → DetSchedule n → Bool
  | _, [] => false
  | C, e :: rest =>
      clockResetAt ring C x e ||
        clockResetSeenAux ring x
          (pplStep ring C e) rest

def allClockResetsSeenB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) : Bool :=
  allAgentsB
    (fun x =>
      clockResetSeenAux ring x C word)

/-- The paper's active reset/traversal subwindow.  The frozen Lean horizon
keeps two extra n-squared units as padding, so no small-n logarithm fit is
needed. -/
def lemma5PaperSweepHorizon (n : Nat) : Nat :=
  6 * n * n

def lemma5iArmPrefix
    {n : Nat}
    (word : DetSchedule n) : DetSchedule n :=
  word.take (lemma5ArmHorizon n)

def lemma5iPaperSweepSuffix
    {n : Nat}
    (word : DetSchedule n) : DetSchedule n :=
  (word.drop (lemma5ArmHorizon n)).take
    (lemma5PaperSweepHorizon n)

def lemma5iPaperPrefix
    {n : Nat}
    (word : DetSchedule n) : DetSchedule n :=
  lemma5iArmPrefix word ++
    lemma5iPaperSweepSuffix word

/-- Phase A: no max-TTL reset signal has appeared by the end of the arm
block. -/
def lemma5iLeaderArmBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) : Bool :=
  !(reachesAux ring maxResetSignalB C
      (lemma5iArmPrefix word))

/-- Phase B: the arm phase succeeded, but by the end of the paper sweep
there is no reset signal left.  This deliberately overcounts: a word may
already have reached C_mid and still be charged here. -/
def lemma5iResetLineageBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) : Bool :=
  reachesAux ring maxResetSignalB C
      (lemma5iArmPrefix word) &&
    !signalPresentB
      (runPPL ring C (lemma5iPaperPrefix word))

/-- Phase C: after a successful arm, the 6n² sweep fails to give every
agent an actual reset. -/
def lemma5iTraversalBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) : Bool :=
  let arm := lemma5iArmPrefix word
  let D := runPPL ring C arm
  let sweep := lemma5iPaperSweepSuffix word
  reachesAux ring maxResetSignalB C arm &&
    !allClockResetsSeenB ring D sweep

/-- Phase D: the reset traversal succeeded, but the run has still not
entered the physical C_mid condition during the paper prefix. -/
def lemma5iMidClockBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) : Bool :=
  let arm := lemma5iArmPrefix word
  let D := runPPL ring C arm
  let sweep := lemma5iPaperSweepSuffix word
  reachesAux ring maxResetSignalB C arm &&
    allClockResetsSeenB ring D sweep &&
    !(reachesAux ring midPhysicalB C
        (lemma5iPaperPrefix word))

def lemma5iLeaderArmFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Nat :=
  (allSchedules n (lemma5iHorizon n)).countP
    (lemma5iLeaderArmBadB ring C)

def lemma5iResetLineageFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Nat :=
  (allSchedules n (lemma5iHorizon n)).countP
    (lemma5iResetLineageBadB ring C)

def lemma5iTraversalFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Nat :=
  (allSchedules n (lemma5iHorizon n)).countP
    (lemma5iTraversalBadB ring C)

def lemma5iMidClockFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Nat :=
  (allSchedules n (lemma5iHorizon n)).countP
    (lemma5iMidClockBadB ring C)

/-! ## Concrete phase predicates and numerators for Lemma 5(ii) -/

/-- The binary L7 budget after spending one c-unit on the arbitrary incoming
head-run offset.  At the consumer c is at least three. -/
def lemma5iiEncounterCap
    (psi c : Nat) : Nat :=
  lotteryL7Horizon psi (c - 1)

/-- A fixed agent sees more incident interactions than the L7 parser budget
inside the full construction window. -/
def lemma5iiEncounterBadB
    {n : Nat}
    (psi c : Nat)
    (ring : DirectedRing n)
    (word : DetSchedule n) : Bool :=
  (List.ofFn
    (fun x : Fin n =>
      decide
        (lemma5iiEncounterCap psi c <
          predictableHostHits
            ring (fun _ => x) word))).foldl
      (fun acc b => acc || b) false

/-- Residual part-(ii) failure after the fixed-agent encounter cap holds.
Its eventual proof is the reset-relative clock suffix argument: starting
from C_mid, any first Detect state needs enough post-reset clock wins. -/
def lemma5iiPostResetClockBadB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (c : Nat)
    (word : DetSchedule n) : Bool :=
  !lemma5iiEncounterBadB psi c ring word &&
    !(constructAlong ring C word)

def lemma5iiEncounterFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (c : Nat) : Nat :=
  (allSchedules n
      (lemma5iiHorizon n psi kappa)).countP
    (lemma5iiEncounterBadB psi c ring)

def lemma5iiPostResetClockFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (c : Nat) : Nat :=
  (allSchedules n
      (lemma5iiHorizon n psi kappa)).countP
    (lemma5iiPostResetClockBadB ring C c)

/-! ## Six independent proof obligations -/

/-- Deterministic part-(i) split.  Every full-horizon failure is charged to
one of the four named phases. -/
def Lemma5iFailureSplit : Prop :=
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
    lemma5iFailureCount ring C ≤
      lemma5iLeaderArmFailureCount ring C +
      lemma5iResetLineageFailureCount ring C +
      lemma5iTraversalFailureCount ring C +
      lemma5iMidClockFailureCount ring C

/-- Counting leaves for the leader-arm and reset-lineage phases.  Each gets
coefficient two in the final n-scaled union bound. -/
def Lemma5iArmResetCount : Prop :=
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
    ModeStoppedTreeTransfer →
    PredictableHostTails →
    WLGHeadOffsetBounds →
    LotteryCountBounds →
    (n * lemma5iLeaderArmFailureCount ring C ≤
        2 * n ^ lemma5iHorizon n) ∧
    (n * lemma5iResetLineageFailureCount ring C ≤
        2 * n ^ lemma5iHorizon n)

/-- Counting leaves for clockwise reset traversal and the final C_mid
clock/mode condition. -/
def Lemma5iSweepMidCount : Prop :=
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
    (n * lemma5iTraversalFailureCount ring C ≤
        2 * n ^ lemma5iHorizon n) ∧
    (n * lemma5iMidClockFailureCount ring C ≤
        2 * n ^ lemma5iHorizon n)

/-- Deterministic part-(ii) split.  A construction-window failure either
exceeds the fixed-agent encounter budget, or is a bounded-encounter
post-reset clock failure. -/
def Lemma5iiFailureSplit : Prop :=
  ∀ {n psi kappa c : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (hc : 3 ≤ c)
      (hkappa : kappa = 16 * c * psi)
      (hnpow : n ≤ 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    midPhysicalB C = true →
    lemma5iiFailureCount ring C ≤
      lemma5iiEncounterFailureCount
          (psi := psi) (kappa := kappa) ring c +
        lemma5iiPostResetClockFailureCount ring C c

/-- Raw-time upper-tail count for the fixed-agent encounter overload in
part (ii), after union over all agents. -/
def Lemma5iiEncounterCount : Prop :=
  ∀ {n psi kappa c : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (hc : 3 ≤ c)
      (hkappa : kappa = 16 * c * psi)
      (hnpow : n ≤ 2 ^ psi)
      (ring : DirectedRing n),
    PredictableHostTails →
    n *
        lemma5iiEncounterFailureCount
          (psi := psi) (kappa := kappa) ring c ≤
      2 * n ^ lemma5iiHorizon n psi kappa

/-- Reset-relative L7 count for the bounded-encounter residual in part (ii).
A later physical reset only gives a newer zero-clock epoch and therefore
helps the construction-mode claim. -/
def Lemma5iiPostResetClockCount : Prop :=
  ∀ {n psi kappa c : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (hc : 3 ≤ c)
      (hkappa : kappa = 16 * c * psi)
      (hnpow : n ≤ 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    midPhysicalB C = true →
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring →
    StoppedClockSuffixBoundsCorrected →
    ModeStoppedTreeTransfer →
    WLGHeadOffsetBounds →
    LotteryCountBounds →
    n * lemma5iiPostResetClockFailureCount ring C c ≤
      2 * n ^ lemma5iiHorizon n psi kappa

/-!
Assembly only.  The constants are exactly four phase charges of size two in
part (i), and two phase charges of size two in part (ii).
-/
theorem lemma5Bridge_of_split
    (hiSplit : Lemma5iFailureSplit)
    (hiArmReset : Lemma5iArmResetCount)
    (hiSweepMid : Lemma5iSweepMidCount)
    (hiiSplit : Lemma5iiFailureSplit)
    (hiiEncounter : Lemma5iiEncounterCount)
    (hiiClock : Lemma5iiPostResetClockCount) :
    Lemma5DeterministicBridge := by
  constructor
  · intro n psi kappa
    intro hn3 hpsi hkappa hnpow
    intro ring C
    intro hcnz hlineage hclock hmarked hpredict hhead hcount

    have hsplit :=
      hiSplit hn3 hpsi hkappa hnpow
        ring C hcnz hlineage
    rcases
        hiArmReset hn3 hpsi hkappa hnpow
          ring C hcnz hlineage
          hmarked hpredict hhead hcount with
      ⟨harm, hreset⟩
    rcases
        hiSweepMid hn3 hpsi hkappa hnpow
          ring C hcnz hlineage hclock
          hmarked hpredict hhead hcount with
      ⟨htrav, hmid⟩

    have hsplit' :=
      Nat.mul_le_mul_left n hsplit
    simp only [Nat.mul_add] at hsplit'
    have h01 :=
      Nat.add_le_add harm hreset
    have h012 :=
      Nat.add_le_add h01 htrav
    have h0123 :=
      Nat.add_le_add h012 hmid
    have htotal :=
      Nat.le_trans hsplit' h0123

    unfold Lemma5iWordBound
    calc
      n * lemma5iFailureCount ring C ≤
          ((2 * n ^ lemma5iHorizon n +
              2 * n ^ lemma5iHorizon n) +
            2 * n ^ lemma5iHorizon n) +
          2 * n ^ lemma5iHorizon n := htotal
      _ = 8 * n ^ lemma5iHorizon n := by
        omega

  · intro n psi kappa c
    intro hn3 hpsi hc hkappa hnpow
    intro ring C
    intro hmid hlineage hclock hmarked hpredict hhead hcount

    have hsplit :=
      hiiSplit hn3 hpsi hc hkappa hnpow
        ring C hmid
    have henc :=
      hiiEncounter hn3 hpsi hc hkappa hnpow
        ring hpredict
    have hclk :=
      hiiClock hn3 hpsi hc hkappa hnpow
        ring C hmid hlineage hclock
        hmarked hhead hcount

    have hsplit' :=
      Nat.mul_le_mul_left n hsplit
    simp only [Nat.mul_add] at hsplit'
    have hsum :=
      Nat.add_le_add henc hclk
    have htotal :=
      Nat.le_trans hsplit' hsum

    unfold Lemma5iiWordBound
    calc
      n * lemma5iiFailureCount ring C ≤
          2 * n ^ lemma5iiHorizon n psi kappa +
            2 * n ^ lemma5iiHorizon n psi kappa := htotal
      _ = 4 * n ^ lemma5iiHorizon n psi kappa := by
        omega

/-!
Truth audit of the six leaves.

* Lemma5iFailureSplit: TRUE.  A failing word either never arms a max reset
  signal, or is charged by the reset-lineage overcount, or misses some actual
  reset in the paper sweep, or reaches the final residual without C_mid.

* Lemma5iArmResetCount: TRUE.  The arm is a predictable one-edge forcing
  event; reset-lineage disappearance is bounded by the stopped 24n encounter
  cap plus Lemma 7 at c=6, with absorption and re-arm treated as stopping.

* Lemma5iSweepMidCount: TRUE.  The clockwise word is a fixed-word event in
  the 6n² subwindow; after actual resets, ERRATA S3.2's fixed-agent 24n cap
  and StoppedClockSuffixBoundsCorrected control clock regrowth.  The frozen extra 2n²
  padding avoids the n=3 logarithm-fit problem.

* Lemma5iiFailureSplit: TRUE.  It is the Boolean partition of a failed
  constructAlong word into encounter-overload and bounded-encounter residual.

* Lemma5iiEncounterCount: TRUE.  The cap is
  4(c-1)psi*2^psi against raw horizon n*c*psi*2^psi after rewriting kappa;
  PredictableHostTails plus the proved upper-tail arithmetic gives the stated
  coefficient after the n-agent union.

* Lemma5iiPostResetClockCount: TRUE.  From C_mid, first entry to Detect needs
  at least kappa/2 post-entry clock wins since the latest reset.  A later reset
  only helps.  One arbitrary head-run offset is paid by using c-1 in Lemma 7.

No sub-Prop is currently suspected false, so there is no candidate
counterexample to report.
-/

#print axioms PPL.Modes.Lemma5.lemma5Bridge_of_split

end PPL.Modes.Lemma5

