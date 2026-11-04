import Leader.PPL.Modes.StoppedClockInterfacesCorrected
import Leader.PPL.Modes.StoppedClockInterfaces
import Leader.PPL.Modes.SignalLineage
import Leader.PPL.Modes.SignalAbsorption
import Leader.PPL.Probability.FixedWord
import Leader.PPL.Probability.LotteryMoment

namespace PPL.Modes.Lemma5

set_option autoImplicit false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

abbrev Config (n psi kappa : Nat) :=
  PPL.Probability.PPLConfig n psi kappa

def K (n : Nat) : Nat :=
  Nat.log2 n + 1

def allAgentsB
    {n : Nat}
    (p : Fin n -> Bool) : Bool :=
  (List.ofFn p).foldl
    (fun acc b => acc && b) true

def midPhysicalB
    {n psi kappa : Nat}
    (C : Config n psi kappa) : Bool :=
  leaderPresent C &&
    allAgentsB
      (fun i =>
        decide ((C i).clock.val <= kappa / 2) &&
          decide ((C i).mode = false))

def neverLeaderless
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  forall D : Config n psi kappa,
    PopulationProtocol.Reachable
        (PPL.protocol psi kappa)
        ring C D ->
      leaderPresent D = true

def reachesAux
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (good : Config n psi kappa -> Bool) :
    Config n psi kappa ->
      DetSchedule n ->
      Bool
  | C, [] =>
      good C
  | C, e :: es =>
      good C ||
        reachesAux ring good
          (pplStep ring C e) es

def constructAlong
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    Config n psi kappa ->
      DetSchedule n ->
      Bool
  | C, [] =>
      allAgentsB
        (fun i => decide ((C i).mode = false))
  | C, e :: es =>
      allAgentsB
          (fun i => decide ((C i).mode = false)) &&
        constructAlong ring
          (pplStep ring C e) es

def lemma5ArmHorizon
    (n : Nat) : Nat :=
  2 * n * (1 + 4 * K n)

def lemma5SweepHorizon
    (n : Nat) : Nat :=
  8 * n * n

def lemma5iHorizon
    (n : Nat) : Nat :=
  lemma5ArmHorizon n +
    lemma5SweepHorizon n

def lemma5iFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Nat :=
  (allSchedules n (lemma5iHorizon n)).countP
    (fun word =>
      !(reachesAux ring midPhysicalB C word))

/--
Exact frozen Lemma-5(i) count statement.

The premise neverLeaderless is the finite-proof consumer of paper CNZ:
once C is in CNZ, every reached configuration still has a leader, so reaching
the physical clock/mode condition is reaching C_mid.
-/
def Lemma5iWordBound
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Prop :=
  n * lemma5iFailureCount ring C <=
    8 * n ^ lemma5iHorizon n

def lemma5iiHorizon
    (n psi kappa : Nat) : Nat :=
  (n * kappa / 16) * 2 ^ psi

def lemma5iiFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Nat :=
  (allSchedules n
      (lemma5iiHorizon n psi kappa)).countP
    (fun word =>
      !(constructAlong ring C word))

/--
Exact Lemma-5(ii) construction-window statement.

For the clean Nat specialization kappa=16*c*psi, c>=3.  The binary L7
certificate used by the proof is c-1, not c: an arbitrary initial hits value
can contribute at most one head-run offset before a fresh parser.  Spending
one c-unit gives 8*(c-1)*psi <= kappa/2-1 with ample slack.
-/
def Lemma5iiWordBound
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (c : Nat) : Prop :=
  n * lemma5iiFailureCount ring C <=
    4 * n ^ lemma5iiHorizon n psi kappa

/--
The ONE Lemma-5 deterministic bridge, bundling parts (i) and (ii).

It may use the numerical inequalities supplied by the named interfaces, but
introduces no scheduler probability law of its own.  Its physical obligations
are exactly:
(i) leader arm -> one reset lineage -> clockwise traversal; every actual
    clock reset starts a suffix epoch; line 41 starts a moved host at hits=0;
(ii) from C_mid, reaching Detect requires enough post-reset clock wins;
     a later reset only helps; the arbitrary head offset costs one win.
-/
def Lemma5DeterministicBridge : Prop :=
  (forall
      {n psi kappa : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hkappa : 48 * psi <= kappa)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
      neverLeaderless ring C ->
      SignalLineageOwnership (psi := psi) (kappa := kappa) ring ->
      StoppedClockSuffixBoundsCorrected ->
      ModeStoppedTreeTransfer ->
      PredictableHostTails ->
      WLGHeadOffsetBounds ->
      LotteryCountBounds ->
      Lemma5iWordBound ring C) ∧
  (forall
      {n psi kappa c : Nat}
      (hn3 : 3 <= n)
      (hpsi : 2 <= psi)
      (hc : 3 <= c)
      (hkappa : kappa = 16 * c * psi)
      (hnpow : n <= 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
      midPhysicalB C = true ->
      SignalLineageOwnership (psi := psi) (kappa := kappa) ring ->
      StoppedClockSuffixBoundsCorrected ->
      ModeStoppedTreeTransfer ->
      PredictableHostTails ->
      WLGHeadOffsetBounds ->
      LotteryCountBounds ->
      Lemma5iiWordBound ring C c)

theorem lemma5i_wordBound
    (hclock : StoppedClockSuffixBoundsCorrected)
    (hmarked : ModeStoppedTreeTransfer)
    (hbridge : Lemma5DeterministicBridge)
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hkappa : 48 * psi <= kappa)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hcnz : neverLeaderless ring C)
    (hlineage : SignalLineageOwnership (psi := psi) (kappa := kappa) ring) :
    Lemma5iWordBound ring C := by
  exact
    hbridge.1 hn3 hpsi hkappa hnpow
      ring C hcnz hlineage hclock hmarked
      predictableHostTails
      wlgHeadOffsetBounds
      lotteryCountBounds

theorem lemma5ii_wordBound
    (hclock : StoppedClockSuffixBoundsCorrected)
    (hmarked : ModeStoppedTreeTransfer)
    (hbridge : Lemma5DeterministicBridge)
    {n psi kappa c : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hc : 3 <= c)
    (hkappa : kappa = 16 * c * psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hmid : midPhysicalB C = true)
    (hlineage : SignalLineageOwnership (psi := psi) (kappa := kappa) ring) :
    Lemma5iiWordBound ring C c := by
  exact
    hbridge.2 hn3 hpsi hc hkappa hnpow
      ring C hmid hlineage hclock hmarked
      predictableHostTails
      wlgHeadOffsetBounds
      lotteryCountBounds

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.lemma5i_wordBound
#print axioms PPL.Modes.Lemma5.lemma5ii_wordBound
