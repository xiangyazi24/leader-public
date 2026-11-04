import Leader.PPL.Modes.StoppedClockInterfaces
import Leader.PPL.Modes.SignalLineage
import Leader.PPL.Modes.SignalAbsorption
import Leader.PPL.Probability.LotteryMoment

namespace PPL.Modes.Lemma6

set_option autoImplicit false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

abbrev Config (n psi kappa : Nat) :=
  PPL.Probability.PPLConfig n psi kappa

def allAgentsB
    {n : Nat}
    (p : Fin n -> Bool) : Bool :=
  (List.ofFn p).foldl
    (fun acc b => acc && b) true

def signalFreeB
    {n psi kappa : Nat}
    (C : Config n psi kappa) : Bool :=
  allAgentsB
    (fun i => decide ((C i).signalR.val = 0))

def allDetectB
    {n psi kappa : Nat}
    (C : Config n psi kappa) : Bool :=
  allAgentsB
    (fun i => decide ((C i).mode = true))

/--
A stronger, structural entry predicate for paper C_det union L>=1.

If there is a leader we stop successfully.  Otherwise every signal is gone
and every agent is Detect.  The deterministic bridge proves that the latter
state is in C_det: without a signal no clock is reset, so all agents stay at
the cap/Detect until a leader is created.
-/
def lemma6GoodB
    {n psi kappa : Nat}
    (C : Config n psi kappa) : Bool :=
  leaderPresent C ||
    (signalFreeB C && allDetectB C)

def reachesAux
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    Config n psi kappa ->
      DetSchedule n ->
      Bool
  | C, [] =>
      lemma6GoodB C
  | C, e :: es =>
      lemma6GoodB C ||
        reachesAux ring
          (pplStep ring C e) es

def lemma6Horizon
    (n psi c : Nat) : Nat :=
  2 * lemma9T n psi c

def lemma6FailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (c : Nat) : Nat :=
  (allSchedules n
      (lemma6Horizon n psi c)).countP
    (fun word =>
      !(reachesAux ring C word))

/--
Exact denominator-cleared Lemma-6 statement.

Under kappa=8*c*psi,
  lemma6Horizon = 16*n*kappa*2^psi.
The constant 8 is union-bound slack, not a paper constant.
-/
def Lemma6WordBound
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (c : Nat) : Prop :=
  n * lemma6FailureCount ring C c <=
    8 * n ^ lemma6Horizon n psi c

/--
The ONE Lemma-6 deterministic bridge.

R10 correction is built into this interface:
- while every pre-step state is leaderless, line 35 cannot arm a new signal;
- LeaderlessCoveragePreserved keeps every live tag inside the interval-start
  tag set;
- when those start tags are gone, signal_free_of_start_tags_gone gives the
  physical signal-free state;
- a leader at any earlier prefix is success, never a failed coupling;
- after signal-free, EarlyLeaderStopBounds is applied independently to fixed
  agents; lower-tail head offsets are harmless by WLGHeadOffsetBounds;
- leaderless + signal-free + all Detect enters C_det.
-/
def Lemma6DeterministicBridge : Prop :=
  forall
    {n psi kappa c : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hc : 6 <= c)
    (hkappa : kappa = 8 * c * psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa),
    SignalLineageOwnership (psi := psi) (kappa := kappa) ring ->
    EarlyLeaderStopBounds ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    (forall i : Fin n,
      0 < (C i).signalR.val ->
      Lemma9WordBound ring C i c) ->
    Lemma6WordBound ring C c

theorem lemma6_wordBound
    (hearly : EarlyLeaderStopBounds)
    (hbridge : Lemma6DeterministicBridge)
    {n psi kappa c : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hc : 6 <= c)
    (hkappa : kappa = 8 * c * psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hlineage : SignalLineageOwnership (psi := psi) (kappa := kappa) ring)
    (h9 :
      forall i : Fin n,
        0 < (C i).signalR.val ->
        Lemma9WordBound ring C i c) :
    Lemma6WordBound ring C c := by
  exact
    hbridge hn3 hpsi hc hkappa hnpow
      ring C hlineage hearly
      wlgHeadOffsetBounds
      lotteryCountBounds
      h9

end PPL.Modes.Lemma6

#print axioms PPL.Modes.Lemma6.lemma6_wordBound
