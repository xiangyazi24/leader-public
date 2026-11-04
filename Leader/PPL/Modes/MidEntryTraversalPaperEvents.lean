-- Leader/PPL/Modes/MidEntryTraversalPaperEvents.lean
import Leader.PPL.Modes.MidEntryTraversalEncounterWin
import Leader.PPL.Modes.SignalLineageClosed
import Leader.PPL.TokenCorrectness.Ghost

namespace PPL.Modes.Lemma5
set_option autoImplicit false
set_option Elab.async false
open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9

/-!
1. Paper A/B/C.

In sources/ppl-podc2023/paper.txt, Proof of Lemma 5 (about lines 829--843),
the paper first renames the leader that generated the fresh reset signal to
u_0.  Its next sentence gives:
A: seq_R(0,n) occurs during the next 6*n^2 interactions;
B: that signal has at most 24*n encounters there;
C: its TTL does not reach zero during its first 24*n encounters.
Thus the paper's 0 is the fresh/current-max signal holder, not absolute site 0
after an arbitrary retiming.

A prefix-predictable formal host is the deterministic site carrying maximal
signalR in runPPL ring D pre; stop when that maximum is zero; h is the
holder's initial hits.  clockResetAt is the clock-event witness.
determineModeSignalProjection gives the signal/hits H/T cases, while
postDetermineModeSignalStable and
step_signal_projection_of_stable postDetermineModeSignalStable lift those
cases to pplStep.  The BC q19732 B/C predicates consume exactly host/stop/h.
-/

def q19765MaxSignalSite {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa) : Fin n :=
  (List.ofFn (fun i : Fin n => i)).foldl
    (fun best i =>
      if (C best).signalR.val < (C i).signalR.val then i else best)
    ⟨0, ring.hn⟩

def q19765TraversalHost {n psi kappa : Nat}
    (ring : DirectedRing n) (D : Config n psi kappa)
    (pre : List (Fin n)) : Fin n :=
  q19765MaxSignalSite ring (runPPL ring D pre)

def q19765TraversalStopB {n psi kappa : Nat}
    (ring : DirectedRing n) (D : Config n psi kappa)
    (pre : List (Fin n)) : Bool :=
  let C := runPPL ring D pre
  let x := q19765TraversalHost ring D pre
  decide ((C x).signalR.val = 0)

def q19765TraversalHostResetB {n psi kappa : Nat}
    (ring : DirectedRing n) (D : Config n psi kappa)
    (pre : List (Fin n)) (e : Fin n) : Bool :=
  clockResetAt ring (runPPL ring D pre)
    (q19765TraversalHost ring D pre) e

theorem q19765_lotteryOffset_top_head_win (psi : Nat) :
    (lotteryStep psi (lotteryOffset psi) true).wins = 1 := by
  simp [lotteryStep, lotteryOffset]

/- h = psi is therefore valid: the next H is an immediate win, matching the
physical capped-hits TTL-decrement branch. -/

def q19765CanonicalMiss {n : Nat} (sweep : DetSchedule n) : Bool :=
  decide (Not ((lemma5ClockwiseSweepWord n).Sublist sweep))

def q19765EncounterBad {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool) (sweep : DetSchedule n) : Bool :=
  decide (24 * n < stoppedPredictableHostHits ring host stop sweep)

def q19765TTLBad {n : Nat}
    (psi h : Nat) (ring : DirectedRing n)
    (host : List (Fin n) -> Fin n) (stop : List (Fin n) -> Bool)
    (sweep : DetSchedule n) : Bool :=
  let bits := stoppedEncounterBits ring host stop sweep
  decide
    (bits.length <= lotteryL7Horizon psi 5 /\
      ((fun u : List Bool =>
        decide (lotteryTarget psi 6 <=
          (lotteryRun psi (lotteryOffset h) u).wins)) bits = true))

/-!
2. The frozen residual is false.

Take n=3, psi=2, kappa=96.  Only site 2 has signalR=96.  Use 50 cold
0-letters followed by [0,2,1,2].  The absolute [0,1,2] word is a Sublist.
The skipped 2 is a live T interaction and moves the signal 2 -> 0; the later
1 is cold, so site 1 never has clockResetAt=true.  Yet any stopped host has at
most 54 encounters (<72), and any stopped H/T list has at most 54 bits, hence
at most 54 lottery wins (<96).  Thus A, B, C are all false for every
existential host/stop/h.
-/

private def q19765Ring : DirectedRing 3 := ⟨by omega⟩

private def q19765State (i : Fin 3) : PPL.State 2 96 :=
  { leader := false, id := false, dist := ⟨i.val, by omega⟩, last := true,
    tokenB := none, tokenW := none, mode := false, clock := 0,
    signalR := if i = (2 : Fin 3) then ⟨96, by omega⟩ else 0,
    hits := 0, bullet := 0, shield := false, signalB := false }

private def q19765D : Config 3 2 96 := q19765State

private def q19765Sweep : DetSchedule 3 :=
  List.replicate 50 (0 : Fin 3) ++
    [(0 : Fin 3), (2 : Fin 3), (1 : Fin 3), (2 : Fin 3)]

private theorem q19765Sweep_length :
    q19765Sweep.length = lemma5PaperSweepHorizon 3 := by decide

private theorem q19765Sweep_mem :
    q19765Sweep ∈ allSchedules 3 (lemma5PaperSweepHorizon 3) :=
  mem_allSchedules_of_length 3 (lemma5PaperSweepHorizon 3)
    q19765Sweep q19765Sweep_length

private theorem q19765CanonicalWord_occurs :
    (lemma5ClockwiseSweepWord 3).Sublist q19765Sweep := by decide

private theorem q19765RotatedWord_misses :
    Not ((PPL.seqR q19765Ring (2 : Fin 3) 3).Sublist q19765Sweep) := by decide

private theorem q19765Max_live :
    maxResetSignalB q19765D = true := by decide

private theorem q19765Sweep_bad :
    !allClockResetsSeenB q19765Ring q19765D q19765Sweep = true := by
  decide

private theorem q19765StoppedHitsAux_le_length {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool) (pre word : List (Fin n)) :
    stoppedPredictableHostHitsAux ring host stop pre word <= word.length := by
  induction word generalizing pre with
  | nil => simp [stoppedPredictableHostHitsAux]
  | cons e rest ih =>
      cases hs : stop pre with
      | false =>
          have ht := ih (pre := pre ++ [e])
          cases hi : incidentLetter ring (host pre) e <;>
            simp [stoppedPredictableHostHitsAux, hs, hi] at * <;> omega
      | true => simp [stoppedPredictableHostHitsAux, hs]

private theorem q19765StoppedHits_le_length {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool) (word : List (Fin n)) :
    stoppedPredictableHostHits ring host stop word <= word.length := by
  simpa [stoppedPredictableHostHits] using
    q19765StoppedHitsAux_le_length ring host stop [] word

private theorem q19765StoppedBitsAux_length_le {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool) (pre word : List (Fin n)) :
    (stoppedEncounterBitsAux ring host stop pre word).length <= word.length := by
  induction word generalizing pre with
  | nil => simp [stoppedEncounterBitsAux]
  | cons e rest ih =>
      cases hs : stop pre with
      | false =>
          have ht := ih (pre := pre ++ [e])
          cases hb : incidentBit ring (host pre) e with
          | none => simp [stoppedEncounterBitsAux, hs, hb] at * <;> omega
          | some b => simp [stoppedEncounterBitsAux, hs, hb] at * <;> omega
      | true => simp [stoppedEncounterBitsAux, hs]

private theorem q19765StoppedBits_length_le {n : Nat}
    (ring : DirectedRing n) (host : List (Fin n) -> Fin n)
    (stop : List (Fin n) -> Bool) (word : List (Fin n)) :
    (stoppedEncounterBits ring host stop word).length <= word.length := by
  simpa [stoppedEncounterBits] using
    q19765StoppedBitsAux_length_le ring host stop [] word

private theorem q19765LotteryStep_wins_le_succ
    (k : Nat) (s : LotteryState) (b : Bool) :
    (lotteryStep k s b).wins <= s.wins + 1 := by
  cases b with
  | false => simp [lotteryStep]
  | true =>
      by_cases hk : k <= s.headRun + 1
      · simp [lotteryStep, hk]
      · simp [lotteryStep, hk]

private theorem q19765LotteryRun_wins_le
    (k : Nat) (s : LotteryState) (bits : List Bool) :
    (lotteryRun k s bits).wins <= s.wins + bits.length := by
  induction bits generalizing s with
  | nil => simp [lotteryRun]
  | cons b rest ih =>
      have hs := q19765LotteryStep_wins_le_succ k s b
      have ht := ih (s := lotteryStep k s b)
      simp only [lotteryRun, List.length_cons]
      omega

theorem q19765TraversalABCSweepResidual_false :
    Not Lemma5iRetimedTraversalABCSweepResidual := by
  intro hABC
  obtain ⟨host, stop, h, hh, hcharge⟩ :=
    hABC (n := 3) (psi := 2) (kappa := 96)
      (by omega) (by omega) (by omega)
      q19765Ring q19765D
      (signalLineageOwnership q19765Ring) q19765Max_live
  have hc := hcharge q19765Sweep q19765Sweep_mem q19765Sweep_bad
  have hhits :
      stoppedPredictableHostHits q19765Ring host stop q19765Sweep <= 54 := by
    have hle := q19765StoppedHits_le_length q19765Ring host stop q19765Sweep
    have hlen : q19765Sweep.length = 54 := by decide
    omega
  have hnotB :
      Not (24 * 3 < stoppedPredictableHostHits
        q19765Ring host stop q19765Sweep) := by omega
  let bits := stoppedEncounterBits q19765Ring host stop q19765Sweep
  have hbits : bits.length <= 54 := by
    have hle := q19765StoppedBits_length_le q19765Ring host stop q19765Sweep
    have hlen : q19765Sweep.length = 54 := by decide
    dsimp only [bits]
    omega
  have hrun :
      (lotteryRun 2 (lotteryOffset h) bits).wins <= bits.length := by
    have hle := q19765LotteryRun_wins_le 2 (lotteryOffset h) bits
    simpa [lotteryOffset] using hle
  have hnotC :
      Not (lotteryTarget 2 6 <=
        (lotteryRun 2 (lotteryOffset h) bits).wins) := by
    unfold lotteryTarget
    omega
  change
    ((q19765CanonicalMiss q19765Sweep ||
        q19765EncounterBad q19765Ring host stop q19765Sweep) ||
      q19765TTLBad 2 h q19765Ring host stop q19765Sweep) = true at hc
  simp [q19765CanonicalMiss, q19765CanonicalWord_occurs,
    q19765EncounterBad, hnotB, q19765TTLBad, bits, hnotC] at hc

/-!
Corrected residual: rotate A to the actual max-signal root and restore
n <= 2^psi.  The latter is needed because B=false gives only bits.length
<=24*n, while q19732 C is gated by lotteryL7Horizon psi 5.
A skipped holder interaction is not a failure after re-rooting: clockResetAt
makes it an actual reset, and the signal projection makes it monotone carrier
progress.  Keep h <= psi; equality is handled above.
-/

def q19765RotatedMiss {n : Nat}
    (ring : DirectedRing n) (start : Fin n) (sweep : DetSchedule n) : Bool :=
  decide (Not ((PPL.seqR ring start n).Sublist sweep))

def Lemma5iRetimedTraversalABCSweepResidualCorrected : Prop :=
  forall {n psi kappa : Nat},
    3 <= n -> 2 <= psi -> 48 * psi <= kappa -> n <= 2 ^ psi ->
    forall (ring : DirectedRing n) (D : Config n psi kappa),
      SignalLineageOwnership (psi := psi) (kappa := kappa) ring ->
      maxResetSignalB D = true ->
      let start := q19765MaxSignalSite ring D
      let host := q19765TraversalHost ring D
      let stop := q19765TraversalStopB ring D
      let h := (D start).hits.val
      (D start).signalR.val = kappa /\ h <= psi /\
      forall sweep : DetSchedule n,
        sweep ∈ allSchedules n (lemma5PaperSweepHorizon n) ->
        !allClockResetsSeenB ring D sweep = true ->
        ((q19765RotatedMiss ring start sweep ||
            q19765EncounterBad ring host stop sweep) ||
          q19765TTLBad psi h ring host stop sweep) = true

/-!
3. The requested I(prefix) branch was conditional on the frozen residual being
true, so no invariant theorem is asserted.

For the corrected residual the induction state should use
Cpre=runPPL ring D pre and x=host pre.  Before stop: signalR(x)>0; every
incident host letter contributes one stopped H/T bit and is a clockResetAt
event; the rotated reset frontier only advances (extra holder interactions
count as progress); and a lottery/TTL potential pays for every physical TTL
decrement.  Do NOT assert parser headRun = physical hits across an arbitrary
max-holder switch/re-arm.  Empty prefix follows from maxResetSignalB and
hits:Fin(psi+1); the cold/H/T step is exactly the public signal projection
plus step_signal_projection_of_stable postDetermineModeSignalStable.
-/

end PPL.Modes.Lemma5

#print axioms PPL.Modes.Lemma5.q19765_lotteryOffset_top_head_win
#print axioms PPL.Modes.Lemma5.q19765TraversalABCSweepResidual_false
