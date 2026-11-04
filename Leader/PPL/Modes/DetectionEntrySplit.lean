import Leader.PPL.Modes.DetectionEntry
import Leader.PPL.Modes.SignalAbsorptionSplit

namespace PPL.Modes.Lemma6

set_option autoImplicit false

open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

def lemma6SignalPhaseFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (c : Nat) : Nat :=
  (allSchedules n (lemma9T n psi c)).countP
    (fun word =>
      decide
        (reachesAux ring C word = false ∧
          signalFreeB (runPPL ring C word) = false))

def lemma6ClockPhaseFailureCount
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (c : Nat) : Nat :=
  (allSchedules n (lemma9T n psi c)).countP
    (fun word => !(reachesAux ring C word))

def Lemma6LeaderlessSignalCoverage : Prop :=
  ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa)
      (word : DetSchedule n),
    SignalLineageOwnership (psi := psi) (kappa := kappa) ring →
    reachesAux ring C word = false →
    StartTagsGone
        (initialGhost C)
        (ghostRun ring (initialGhost C) word) →
    signalFreeB (runPPL ring C word) = true

def Lemma6SignalClearanceCount : Prop :=
  ∀ {n psi kappa c : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (hc : 6 ≤ c)
      (hkappa : kappa = 8 * c * psi)
      (hnpow : n ≤ 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    Lemma6LeaderlessSignalCoverage →
    SignalLineageOwnership (psi := psi) (kappa := kappa) ring →
    (∀ i : Fin n,
      0 < (C i).signalR.val →
      Lemma9WordBound ring C i c) →
    n * lemma6SignalPhaseFailureCount ring C c ≤
      4 * n ^ lemma9T n psi c

def Lemma6ClockFailureSplit : Prop :=
  ∀ {n psi kappa c : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (hkappa : kappa = 8 * c * psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa)
      (word : DetSchedule n),
    leaderPresent C = false →
    signalFreeB C = true →
    reachesAux ring C word = false →
    ∃ x : Fin n,
      (runPPL ring C word x).mode = false ∧
        (let host : List (Fin n) → Fin n := fun _ => x
         let stop := firstLeaderStop ring C
         let bits := stoppedEncounterBits ring host stop word
         stoppedPredictableHostHits ring host stop word <
              lemma9E psi c ∨
           (lemma9E psi c ≤ bits.length ∧
             (lotteryRun psi
               (lotteryOffset (C x).hits.val)
               (bits.take (lemma9E psi c))).wins ≤
                 lotteryTarget psi c))

def Lemma6ClockRiseCount : Prop :=
  ∀ {n psi kappa c : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (hc : 6 ≤ c)
      (hkappa : kappa = 8 * c * psi)
      (hnpow : n ≤ 2 ^ psi)
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    Lemma6ClockFailureSplit →
    leaderPresent C = false →
    signalFreeB C = true →
    EarlyLeaderStopBounds →
    WLGHeadOffsetBounds →
    LotteryCountBounds →
    n * lemma6ClockPhaseFailureCount ring C c ≤
      4 * n ^ lemma9T n psi c

def Lemma6TwoBlockBind : Prop :=
  ∀ {n psi kappa c A B : Nat}
      (ring : DirectedRing n)
      (C : Config n psi kappa),
    n * lemma6SignalPhaseFailureCount ring C c ≤
        A * n ^ lemma9T n psi c →
    (∀ D : Config n psi kappa,
      leaderPresent D = false →
      signalFreeB D = true →
      n * lemma6ClockPhaseFailureCount ring D c ≤
        B * n ^ lemma9T n psi c) →
    n * lemma6FailureCount ring C c ≤
      (A + B) * n ^ lemma6Horizon n psi c

theorem lemma6Bridge_of_split
    (hcoverage : Lemma6LeaderlessSignalCoverage)
    (hclear : Lemma6SignalClearanceCount)
    (hclockSplit : Lemma6ClockFailureSplit)
    (hclock : Lemma6ClockRiseCount)
    (hbind : Lemma6TwoBlockBind) :
    Lemma6DeterministicBridge := by
  intro n psi kappa c
  intro hn3 hpsi hc hkappa hnpow
  intro ring C
  intro hlineage hearly hhead hcount h9

  have hclearBound :
      n * lemma6SignalPhaseFailureCount ring C c ≤
        4 * n ^ lemma9T n psi c :=
    hclear hn3 hpsi hc hkappa hnpow
      ring C hcoverage hlineage h9

  have hclockBound :
      ∀ D : Config n psi kappa,
        leaderPresent D = false →
        signalFreeB D = true →
        n * lemma6ClockPhaseFailureCount ring D c ≤
          4 * n ^ lemma9T n psi c := by
    intro D hleader hsignal
    exact
      hclock hn3 hpsi hc hkappa hnpow
        ring D hclockSplit hleader hsignal
        hearly hhead hcount

  unfold Lemma6WordBound
  have hfinal :=
    hbind
      (n := n) (psi := psi) (kappa := kappa) (c := c)
      (A := 4) (B := 4)
      ring C hclearBound hclockBound
  simpa using hfinal

#print axioms lemma6Bridge_of_split

end PPL.Modes.Lemma6
