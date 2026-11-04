import Leader.PPL.Modes.StoppedClockInterfaces
import Leader.PPL.Modes.SignalLineage
import Leader.PPL.Probability.LotteryMoment

namespace PPL.Modes.Lemma9

set_option autoImplicit false

open PPL.Probability
open PPL.Modes.SignalLineage

abbrev Config (n psi kappa : Nat) :=
  PPL.Probability.PPLConfig n psi kappa

def ghostRun
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    GhostConfig n psi kappa ->
      DetSchedule n ->
      GhostConfig n psi kappa
  | g, [] =>
      g
  | g, e :: es =>
      ghostRun ring (ghostStep ring g e) es

def tagAliveB
    {n psi kappa : Nat}
    (g : GhostConfig n psi kappa)
    (tag : SignalTag n) : Bool :=
  (List.ofFn
    (fun i : Fin n =>
      decide (g.owner i = some tag))).foldl
        (fun acc b => acc || b) false

def lemma9E
    (psi c : Nat) : Nat :=
  lotteryL8Horizon psi c

def lemma9T
    (n psi c : Nat) : Nat :=
  n * lemma9E psi c

def lemma9FailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (c : Nat) : Nat :=
  let start := initialGhost C
  let tag : SignalTag n :=
    { origin := i, arm := 0 }
  (allSchedules n (lemma9T n psi c)).countP
    (fun word =>
      tagAliveB (ghostRun ring start word) tag)

/--
The generic stopped H/T transfer missing from current main.

The lower clause is the transfer needed by Lemmas 9 and 6.
The upper clause is the same prefix-tree identity for the Lemma-5 use.
This is a probability/counting interface, NOT the per-lemma deterministic
bridge.
-/
def stoppedLotteryUpperFailureCount
    {n : Nat}
    (k h : Nat)
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (T E M : Nat) : Nat :=
  (allSchedules n T).countP
    (fun word =>
      let bits :=
        stoppedEncounterBits ring host stop word
      decide
        (stopReached stop word = false ∧
          E <= bits.length ∧
          M <=
            (lotteryRun k
              (lotteryOffset h)
              (bits.take E)).wins))

def ModeStoppedTreeTransfer : Prop :=
  (forall {n k h T E M : Nat},
      3 <= n ->
      1 <= k ->
      h <= k ->
      forall
        (ring : DirectedRing n)
        (host : List (Fin n) -> Fin n)
        (stop : List (Fin n) -> Bool),
        stoppedLotteryUpperFailureCount
              k h ring host stop T E M *
            2 ^ E <=
          n ^ T *
            lotteryAtLeastWordCount
              k h E M) ∧
  (forall {n k h T E M : Nat},
      3 <= n ->
      1 <= k ->
      h <= k ->
      forall
        (ring : DirectedRing n)
        (host : List (Fin n) -> Fin n)
        (stop : List (Fin n) -> Bool),
        stoppedLotteryLowerFailureCount
              k h ring host stop T E M *
            2 ^ E <=
          n ^ T *
            lotteryAtMostWordCount
              k h E M)

/--
Exact denominator-cleared paper-Lemma-9 statement.

Under kappa = 8*c*psi, lemma9E = 8*kappa*2^psi and
lemma9T = 8*n*kappa*2^psi.  The right side is a concrete O(1/n^2)
envelope; the constant 4 is proof slack, not a paper constant.
-/
def Lemma9WordBound
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (c : Nat) : Prop :=
  n * n *
      lemma9FailureCount ring C i c <=
    4 * n ^ lemma9T n psi c

/--
The ONE Lemma-9 deterministic bridge.

All stochastic/counting laws are explicit premises.  The proof of this Prop
is only the literal DetermineMode/lineage statement:
- one tag has one predictable current host;
- max-TTL merger chooses its owner;
- move resets hits;
- TTL never increases on one lineage;
- absorption, disappearance, and line-35 re-arm terminate that lineage;
plus the Nat union/arithmetic that combines the supplied inequalities.
-/
def Lemma9DeterministicBridge : Prop :=
  forall
    {n psi kappa c : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hc : 6 <= c)
    (hkappa : kappa = 8 * c * psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n),
    0 < (C i).signalR.val ->
    SignalLineageOwnership (psi := psi) (kappa := kappa) ring ->
    ModeStoppedTreeTransfer ->
    PredictableHostTails ->
    WLGHeadOffsetBounds ->
    LotteryCountBounds ->
    Lemma9WordBound ring C i c

theorem lemma9_wordBound
    (hmarked : ModeStoppedTreeTransfer)
    (hbridge : Lemma9DeterministicBridge)
    {n psi kappa c : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hc : 6 <= c)
    (hkappa : kappa = 8 * c * psi)
    (hnpow : n <= 2 ^ psi)
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (i : Fin n)
    (hsignal : 0 < (C i).signalR.val)
    (hlineage : SignalLineageOwnership (psi := psi) (kappa := kappa) ring) :
    Lemma9WordBound ring C i c := by
  exact
    hbridge hn3 hpsi hc hkappa hnpow
      ring C i hsignal hlineage hmarked
      predictableHostTails
      wlgHeadOffsetBounds
      lotteryCountBounds

end PPL.Modes.Lemma9

#print axioms PPL.Modes.Lemma9.lemma9_wordBound
