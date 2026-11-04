-- Leader/PPL/Modes/StoppedClockInterfaces.lean
import Leader.PPL.Transition
import Leader.PPL.Probability.FixedWord
import Leader.PPL.Probability.EncounterProjection
import Leader.PPL.Probability.LotteryCounts

set_option autoImplicit false

namespace PPL.Probability

abbrev PPLConfig (n psi kappa : Nat) :=
  Fin n -> PPL.State psi kappa

def runPPL {n psi kappa : Nat}
    (ring : DirectedRing n) (C : PPLConfig n psi kappa)
    (word : DetSchedule n) : PPLConfig n psi kappa :=
  runPopulationSchedule (PPL.protocol psi kappa) ring C word

def pplStep {n psi kappa : Nat}
    (ring : DirectedRing n) (C : PPLConfig n psi kappa)
    (e : Fin n) : PPLConfig n psi kappa :=
  (PPL.protocol psi kappa).step ring C e

/-- Exact pre-letter test for whether Algorithm 4 line 39 resets x's clock.
The leader re-arm at line 35 is included in the effective left signal. -/
def clockResetAt {n psi kappa : Nat}
    (ring : DirectedRing n) (C : PPLConfig n psi kappa)
    (x e : Fin n) : Bool :=
  let r := ring.rightNeighbor e
  let leftSignal :=
    if (C e).leader = true then kappa else (C e).signalR.val
  decide
    ((x = e \/ x = r) /\
      (0 < leftSignal \/ 0 < (C r).signalR.val))

/-- H means x is the responder to its left edge; T means x initiates. -/
def incidentBit {n : Nat} (ring : DirectedRing n)
    (x e : Fin n) : Option Bool :=
  if e = ring.leftNeighbor x then some true
  else if e = x then some false
  else none

/-- H/T marks from the current state until, but not including, the next
interaction that actually resets x's clock. -/
def clockSuffixBitsAux {n psi kappa : Nat}
    (ring : DirectedRing n) (x : Fin n) :
    PPLConfig n psi kappa -> DetSchedule n -> List Bool
  | _, [] => []
  | C, e :: rest =>
      if clockResetAt ring C x e then
        []
      else
        let C' := pplStep ring C e
        match incidentBit ring x e with
        | none => clockSuffixBitsAux ring x C' rest
        | some b => b :: clockSuffixBitsAux ring x C' rest

def clockSuffixBits {n psi kappa : Nat}
    (ring : DirectedRing n) (C : PPLConfig n psi kappa)
    (x : Fin n) (word : DetSchedule n) : List Bool :=
  clockSuffixBitsAux ring x C word

/-- Number of strict physical clock increments before the next actual reset.
At the cap, no further tick is counted. -/
def clockSuffixTicksAux {n psi kappa : Nat}
    (ring : DirectedRing n) (x : Fin n) :
    PPLConfig n psi kappa -> DetSchedule n -> Nat
  | _, [] => 0
  | C, e :: rest =>
      if clockResetAt ring C x e then
        0
      else
        let C' := pplStep ring C e
        (if (C x).clock.val < (C' x).clock.val then 1 else 0) +
          clockSuffixTicksAux ring x C' rest

def clockSuffixTicks {n psi kappa : Nat}
    (ring : DirectedRing n) (C : PPLConfig n psi kappa)
    (x : Fin n) (word : DetSchedule n) : Nat :=
  clockSuffixTicksAux ring x C word

/-- An epoch begins either at the proof entry (empty prefix) or immediately
after a scheduler letter that really took Algorithm 4 line 39 for x. -/
def ClockEpochStart {n psi kappa : Nat}
    (ring : DirectedRing n) (C0 : PPLConfig n psi kappa)
    (x : Fin n) (pre : DetSchedule n) : Prop :=
  pre = [] \/
    exists pre0 e,
      pre = pre0 ++ [e] /\
      clockResetAt ring (runPPL ring C0 pre0) x e = true

/-- Raw-word numerator for a bad clock epoch: before the next reset there are
at most E incident marks but the physical clock gains at least M ticks. -/
def stoppedClockSuffixUpperFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n) (C : PPLConfig n psi kappa)
    (x : Fin n) (T E M : Nat) : Nat :=
  (allSchedules n T).countP (fun word =>
    let bits := clockSuffixBits ring C x word
    decide
      (bits.length <= E /\
        M <= clockSuffixTicks ring C x word))

/-- Headline reset-relative interface.  The first conjunct pins the physical
meaning of an actual reset.  The second is the finite-word Nat domination:
condition on any legal epoch start, retain the actual post-start hits as the
lottery head-run offset, and stop at the next physical reset. -/
def StoppedClockSuffixBounds : Prop :=
  (forall (n psi kappa : Nat)
      (ring : DirectedRing n) (C0 : PPLConfig n psi kappa)
      (x e : Fin n),
      clockResetAt ring C0 x e = true ->
        (pplStep ring C0 e x).clock.val = 0) /\
  (forall (n psi kappa T E M : Nat),
      2 <= n -> 2 <= psi ->
      forall (ring : DirectedRing n)
        (C0 : PPLConfig n psi kappa)
        (x : Fin n) (pre : DetSchedule n),
        ClockEpochStart ring C0 x pre ->
          let C := runPPL ring C0 pre
          stoppedClockSuffixUpperFailureCount ring C x T E M *
                2 ^ E <=
            n ^ T *
              lotteryAtLeastWordCount
                psi (C x).hits.val E M)

/-! Generic H/T-mark stopping object used by the leaderless lower tail. -/

def stoppedEncounterBitsAux {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool) :
    List (Fin n) -> DetSchedule n -> List Bool
  | _, [] => []
  | pre, e :: rest =>
      if stop pre then
        []
      else
        let x := host pre
        match incidentBit ring x e with
        | none =>
            stoppedEncounterBitsAux ring host stop
              (pre ++ [e]) rest
        | some b =>
            b :: stoppedEncounterBitsAux ring host stop
              (pre ++ [e]) rest

def stoppedEncounterBits {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (word : DetSchedule n) : List Bool :=
  stoppedEncounterBitsAux ring host stop [] word

/-- Binary lower-tail failure after E stopped encounters.  Reaching stop at
any prefix, including the full horizon prefix, is success and excluded. -/
def stoppedLotteryLowerFailureCount {n : Nat}
    (k h : Nat) (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool)
    (T E M : Nat) : Nat :=
  (allSchedules n T).countP (fun word =>
    let bits := stoppedEncounterBits ring host stop word
    decide
      (stopReached stop word = false /\
        E <= bits.length /\
        (lotteryRun k (lotteryOffset h) (bits.take E)).wins <= M))

def leaderPresent {n psi kappa : Nat}
    (C : PPLConfig n psi kappa) : Bool :=
  (List.ofFn (fun i : Fin n => (C i).leader)).foldl
    (fun acc b => acc || b) false

/-- Prefix-measurable success stop used in every leaderless lower-tail
consumer: once some prefix contains a leader, the stopped experiment is done. -/
def firstLeaderStop {n psi kappa : Nat}
    (ring : DirectedRing n) (C0 : PPLConfig n psi kappa)
    (pre : List (Fin n)) : Bool :=
  leaderPresent (runPPL ring C0 pre)

/-- Headline early-leader interface.  The first conjunct is the encounter
lower tail with the first-leader stop.  The second retains the first E
oriented H/T encounter marks and compares them with the exact offset lottery.
No leader-created word is charged as a failure. -/
def EarlyLeaderStopBounds : Prop :=
  forall (n psi kappa T E M h : Nat),
    2 <= n -> 2 <= psi -> h <= psi ->
    forall (ring : DirectedRing n)
      (C0 : PPLConfig n psi kappa)
      (host : List (Fin n) -> Fin n),
      leaderPresent C0 = false ->
        let stop := firstLeaderStop ring C0
        stoppedPredictableHostLowerFailureCount
              ring host stop T E <=
            twoEdgeLowerTailCount n T E /\
        stoppedLotteryLowerFailureCount
              psi h ring host stop T E M * 2 ^ E <=
            n ^ T * lotteryAtMostWordCount psi h E M

end PPL.Probability
