import Leader.PPL.Modes.MidEntryTraversalEncounterWin
import Leader.PPL.Modes.MidEntryTraversalPaperEvents


namespace PPL.Modes.Lemma5


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9


/-- Deterministically choose one initial max-TTL carrier.
This is the same tie-breaking fold used by the old current-max host,
but it is evaluated only once, at the traversal start. -/
def lemma5iLeaderWaveStart
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa) : Fin n :=
  (List.ofFn (fun i : Fin n => i)).foldl
    (fun best i =>
      if (C best).signalR.val < (C i).signalR.val then
        i
      else
        best)
    ⟨0, ring.hn⟩


/-- Prefix-predictable carrier location of the chosen reset wave.


If the current wave location initiates, the merged surviving signal is at its
right neighbor, regardless of which input identity wins the TTL comparison.
If the wave location is the responder (H) or is nonincident, its location
does not move. -/
def lemma5iLeaderWaveHost
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    Config n psi kappa → List (Fin n) → Fin n :=
  fun C0 pre =>
    pre.foldl
      (fun x e =>
        if e = x then
          ring.rightNeighbor x
        else
          x)
      (lemma5iLeaderWaveStart ring C0)


/-- Stop at the first prefix where the wave location carries no reset signal.
The stopped H/T parser freezes forever once this becomes true. -/
def lemma5iLeaderWaveStopB
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : List (Fin n)) : Bool :=
  let Cpre := runPPL ring C0 pre
  let x := lemma5iLeaderWaveHost ring C0 pre
  decide ((Cpre x).signalR.val = 0)


def lemma5iLeaderWaveRotatedMiss
    {n : Nat}
    (ring : DirectedRing n)
    (start : Fin n)
    (sweep : DetSchedule n) : Bool :=
  decide
    (Not ((PPL.seqR ring start n).Sublist sweep))


def lemma5iLeaderWaveEncounterBad
    {n : Nat}
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (sweep : DetSchedule n) : Bool :=
  decide
    (24 * n <
      stoppedPredictableHostHits
        ring host stop sweep)


def lemma5iLeaderWaveTTLBad
    {n : Nat}
    (psi h : Nat)
    (ring : DirectedRing n)
    (host : List (Fin n) → Fin n)
    (stop : List (Fin n) → Bool)
    (sweep : DetSchedule n) : Bool :=
  let bits :=
    stoppedEncounterBits ring host stop sweep
  decide
    (bits.length ≤ lotteryL7Horizon psi 5 ∧
      lotteryTarget psi 6 ≤
        (lotteryRun psi
          (lotteryOffset h) bits).wins)


/-- Paper A/B/C residual with a fixed chosen reset-wave carrier instead of a
dynamically rerooted global maximum. -/
def Lemma5iRetimedTraversalABCSweepResidualWave : Prop :=
  ∀ {n psi kappa : Nat},
    3 ≤ n →
    2 ≤ psi →
    48 * psi ≤ kappa →
    n ≤ 2 ^ psi →
    ∀ (ring : DirectedRing n)
      (D : Config n psi kappa),
      SignalLineageOwnership
        (psi := psi) (kappa := kappa) ring →
      maxResetSignalB D = true →
      let start :=
        lemma5iLeaderWaveStart ring D
      let host :=
        lemma5iLeaderWaveHost ring D
      let stop :=
        lemma5iLeaderWaveStopB ring D
      let h :=
        (D start).hits.val
      (D start).signalR.val = kappa ∧
        h ≤ psi ∧
        ∀ sweep : DetSchedule n,
          sweep ∈
              allSchedules n
                (lemma5PaperSweepHorizon n) →
          !allClockResetsSeenB
              ring D sweep = true →
          ((lemma5iLeaderWaveRotatedMiss
                ring start sweep ||
              lemma5iLeaderWaveEncounterBad
                ring host stop sweep) ||
            lemma5iLeaderWaveTTLBad
              psi h ring host stop sweep) = true


end PPL.Modes.Lemma5
