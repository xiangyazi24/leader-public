import Leader.PPL.MainTheorem.Whp
import Leader.PPL.MainTheorem.SpliceCounting
import Leader.PPL.MainTheorem.Kappa
import Leader.PPL.LogWindow.Whp

/-!
# Superseded: the first two generations of the P_PL Theorem 1 statement

Nothing in this file is imported by the proved headline
`PPL.theorem1Statement_proved` (`Leader/PPL/Theorem1Proved.lean`).  The file
keeps, under the namespace `PPL.Superseded`, the two statement generations
that the current `PPL.Theorem1Statement` (`Leader/PPL/MainTheorem/Statement.lean`)
replaced, together with the witnesses that killed them.  They are kept so the
recorded history stays checkable; do not build on them.

## Generation 1: the four-phase splice

`Superseded.Theorem1FourPhaseBounds`, `Superseded.Theorem1FourPhaseSplice` and
`Superseded.theorem1_whp_of_phase_bounds` compose Lemma 16, Lemma 5(i),
Lemma 17 and Lemma 18 only.  They omit the Lemma-5(ii) Construct-only quiet
window, which the paper needs to couple the full run to the prime/literal
L17 and L18 runs (see the docstring of `Superseded.Theorem1FourPhaseSplice`).
Replaced by the five-event splice below.

## Generation 2: the sequential five-event horizon

`Superseded.Theorem1Statement` uses `kappa = Superseded.theorem1C1 * psi`
with `Superseded.theorem1C1 = 32 * C17 + 352` and the sequential horizon
`Superseded.theorem1Horizon = H16 + H5(i) + H17 + H18`.  This horizon cannot
host the Lemma-5(ii) quiet window: `Superseded.theorem1_quietWindow_too_long_at_3_2`
shows the window is longer than H5(i)+H17+H18 at (n, psi) = (3, 2), and
`Superseded.theorem1_quietWindow_too_short_at_4_2` shows it is shorter than
H17+H18 at (4, 2).

Replaced on 2026-09-24 (RESEARCH_AGENDA.md, follow-up "03:5x Sep 24, P_PL
Theorem 1") by the current statement:
`PPL.theorem1Kappa psi = PPL.theorem1C1 * psi` with
`PPL.theorem1C1 = 16 * (4 * C17 + 24)` and horizon
`PPL.theorem1Horizon = H16 + H5(i) + H5(ii)`, so that L17 and L18 run inside the
fixed Lemma-5(ii) window (`PPL.Superseded.LogWindow.theorem1_quietWindow_covers_run`).  The
current generation was named with a `V2` suffix until the 2026-09-25 cleanup
(`research-map/RENAME_MAP_PPL.md`); the matching cost chain of this
generation is in `Leader/Superseded/Theorem1SequentialCost*.lean`.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## Generation 2 constants and statement (formerly in `Theorem1Skeleton.lean`) -/

def Superseded.theorem1C1 : Nat :=
  32 * theorem1C17 + 352

def Superseded.theorem1Kappa (psi : Nat) : Nat :=
  Superseded.theorem1C1 * psi

def Superseded.theorem1Horizon (n psi : Nat) : Nat :=
  PPL.Convergence.ReachCPB.lemma16Horizon
      n psi (Superseded.theorem1Kappa psi) +
    PPL.Modes.Lemma5.lemma5iHorizon n +
    PPL.Convergence.L17.H17 theorem1C17 n +
    PPL.Convergence.L18.l18Horizon n psi

/--
Finite-word form of the P_PL Theorem-1 target.


* psi is in the frozen logarithmic window n <= 2^psi and psi <= log2 n + 1;
* kappa is the fixed absolute multiple Superseded.theorem1C1 * psi;
* every S_PL target is Definition-1 safe;
* at Hmain, the exact failure numerator is at most 64/n of all schedules;
* the exact truncated first-hit cost numerator is O(Hmain), uniformly in T,
  with one absolute constant cExpected quantified before n.


The expected-cost conjunct is deliberately numerator-valued, matching the
finite first-hit accounting rather than introducing a probability
or measure-theory API.
-/
def Superseded.Theorem1Statement : Prop :=
  ∃ cExpected : Nat,
    0 < cExpected ∧
      32 * theorem1C17 + 352 ≤ Superseded.theorem1C1 ∧
      Superseded.theorem1C1 % 16 = 0 ∧
      ∀ {n psi : Nat},
        3 ≤ n →
        2 ≤ psi →
        n ≤ 2 ^ psi →
        psi ≤ theorem1K n →
        ∀ (ring : DirectedRing n)
          (C0 : Config n psi (Superseded.theorem1Kappa psi)),
          let H := Superseded.theorem1Horizon n psi
          (∀ C : Config n psi (Superseded.theorem1Kappa psi),
              SPL ring C →
                PopulationProtocol.IsSafe
                  (protocol psi (Superseded.theorem1Kappa psi))
                  ring C PPL.Safety.SPL.output) ∧
            n * theorem1FailureNumerator ring C0 H ≤
              64 * n ^ H ∧
            ∀ T : Nat,
              theorem1CostNumerator ring C0 T ≤
                n ^ T * (cExpected * H)


/-- The current constant `PPL.theorem1C1` is at least the superseded one. -/
theorem Superseded.theorem1C1_le_current :
    Superseded.theorem1C1 ≤ PPL.theorem1C1 := by
  unfold Superseded.theorem1C1 PPL.theorem1C1 theorem1C17
  omega


/-! ## Generation 1: the four-phase splice (formerly in `Theorem1Whp.lean`) -/

/-! ## 4. Exact current forms of the four requested uniform phase bounds -/


/--
The four fields record exactly the uniformity needed by a dynamic phase splice.

* L16 is uniform over every full P_PL start.
* L5(i) is uniform over every full P_PL start satisfying neverLeaderless.
* L17 is uniform over every literal start satisfying PB.
* L18 is uniform over every full start satisfying CPB plus a chosen unique root.

The existing named count theorems produce these fields once their own current
global/leaf hypotheses are supplied.
-/
structure Superseded.Theorem1FourPhaseBounds
    {n psi : Nat}
    (ring : DirectedRing n) : Prop where
  l16 :
    ∀ C : Config n psi (Superseded.theorem1Kappa psi),
      PPL.Convergence.ReachCPB.Lemma16WordBound
        ring C
  l5i :
    ∀ C : Config n psi (Superseded.theorem1Kappa psi),
      PPL.Modes.Lemma5.neverLeaderless ring C →
      PPL.Modes.Lemma5.Lemma5iWordBound
        ring C
  l17 :
    ∀ C : PPL.LiteralElimConfig n,
      PPL.Elim.PB ring C →
      PPL.Convergence.L17.Lemma17WordBound
        theorem1C17 ring C
  l18 :
    ∀ (root : Fin n)
      (C : Config n psi (Superseded.theorem1Kappa psi)),
      CPB ring C →
      PPL.Convergence.L18.L18UniqueLeaderAt
        C root →
      n *
          PPL.Convergence.L18.l18FailureCount
            ring root C ≤
        n ^
          PPL.Convergence.L18.l18Horizon
            n psi


/-! ## 5. The exact missing protocol-specific splice -/


/--
Missing bridge for the four-count version.

This is deliberately an event-splice statement, not the final WHP inequality.
It must:

1. cut a full scheduler word at the dynamically reached phase boundaries;
2. use the uniform bounds above at the resulting start configurations;
3. transport CPB to neverLeaderless at the L16/L5 seam;
4. couple the full P_PL run to the P_PL-prime/literal L17 and L18 runs;
5. pad each phase failure to the common Superseded.theorem1Horizon; and
6. cover every global no-SPL word by one of the four padded bad events.

Current main has no producer for this Prop from only the four requested bounds.
The missing probabilistic event is Lemma 5(ii)'s Construct-only quiet window,
whose own current bound has coefficient 4.
-/
def Superseded.Theorem1FourPhaseSplice : Prop :=
  ∀ {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ theorem1K n)
    (ring : DirectedRing n)
    (C0 : Config n psi (Superseded.theorem1Kappa psi))
    (hphase :
      Superseded.Theorem1FourPhaseBounds
        (psi := psi) ring),
    ∃ bad16 bad5 bad17 bad18 :
        DetSchedule n → Bool,
      (∀ word : DetSchedule n,
        word ∈
            allSchedules n
              (Superseded.theorem1Horizon n psi) →
        !(theorem1ReachesSPL
            ring C0 word) = true →
        bad16 word = true ∨
          bad5 word = true ∨
          bad17 word = true ∨
          bad18 word = true) ∧
      n *
          (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
            bad16 ≤
        12 *
          n ^ Superseded.theorem1Horizon n psi ∧
      n *
          (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
            bad5 ≤
        8 *
          n ^ Superseded.theorem1Horizon n psi ∧
      n *
          (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
            bad17 ≤
        n ^ Superseded.theorem1Horizon n psi ∧
      n *
          (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
            bad18 ≤
        n ^ Superseded.theorem1Horizon n psi


/-! ## 6. Constants -/


theorem Superseded.theorem1_four_phase_constants
    (n H : Nat) :
    12 * n ^ H +
        8 * n ^ H +
        n ^ H +
        n ^ H ≤
      64 * n ^ H := by
  omega

/-! ## 7. WHP assembly from the explicit splice -/


theorem Superseded.theorem1_whp_of_phase_bounds
    (hsplice : Superseded.Theorem1FourPhaseSplice)
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ theorem1K n)
    (ring : DirectedRing n)
    (C0 : Config n psi (Superseded.theorem1Kappa psi))
    (hphase :
      Superseded.Theorem1FourPhaseBounds
        (psi := psi) ring) :
    let H := Superseded.theorem1Horizon n psi
    n * theorem1FailureNumerator
        ring C0 H ≤
      64 * n ^ H := by
  dsimp only
  obtain
      ⟨bad16, bad5, bad17, bad18,
        hcover, hb16, hb5, hb17, hb18⟩ :=
    hsplice
      hn3 hpsi hnpow hpsiK
      ring C0 hphase
  have hfailure :
      theorem1FailureNumerator
          ring C0
          (Superseded.theorem1Horizon n psi) ≤
        (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              bad16 +
        (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              bad5 +
        (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              bad17 +
        (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              bad18 := by
    unfold theorem1FailureNumerator
    exact
      Superseded.LogWindow.theorem1_countP_four_union_le
        (allSchedules n
          (Superseded.theorem1Horizon n psi))
        (fun word =>
          !(theorem1ReachesSPL
            ring C0 word))
        bad16 bad5 bad17 bad18
        (fun word hword hnot =>
          hcover word hword (by simpa using hnot))
  have hscaled :=
    Nat.mul_le_mul_left n hfailure
  have hphaseSum :
      n *
          (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              bad16 +
        n *
          (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              bad5 +
        n *
          (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              bad17 +
        n *
          (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              bad18 ≤
      12 * n ^ Superseded.theorem1Horizon n psi +
        8 * n ^ Superseded.theorem1Horizon n psi +
        n ^ Superseded.theorem1Horizon n psi +
        n ^ Superseded.theorem1Horizon n psi := by
    exact
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add hb16 hb5)
          hb17)
        hb18
  calc
    n *
          theorem1FailureNumerator
            ring C0
            (Superseded.theorem1Horizon n psi) ≤
        n *
          ((allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                bad16 +
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                bad5 +
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                bad17 +
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                bad18) :=
      hscaled
    _ =
        n *
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                bad16 +
          n *
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                bad5 +
          n *
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                bad17 +
          n *
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                bad18 := by
      simp only [Nat.mul_add]
    _ ≤
        12 * n ^ Superseded.theorem1Horizon n psi +
          8 * n ^ Superseded.theorem1Horizon n psi +
          n ^ Superseded.theorem1Horizon n psi +
          n ^ Superseded.theorem1Horizon n psi :=
      hphaseSum
    _ ≤
        64 * n ^ Superseded.theorem1Horizon n psi :=
      Superseded.theorem1_four_phase_constants
        n (Superseded.theorem1Horizon n psi)


/-! ## Generation 2: the sequential five-event splice (formerly in `Theorem1FiveEventSplice.lean`) -/

def Superseded.theorem1H16 (n psi : Nat) : Nat :=
  PPL.Convergence.ReachCPB.lemma16Horizon
    n psi (Superseded.theorem1Kappa psi)

def Superseded.theorem1H5i (n : Nat) : Nat :=
  PPL.Modes.Lemma5.lemma5iHorizon n

def Superseded.theorem1H5ii (n psi : Nat) : Nat :=
  PPL.Modes.Lemma5.lemma5iiHorizon
    n psi (Superseded.theorem1Kappa psi)

def Superseded.theorem1H17 (n : Nat) : Nat :=
  PPL.Convergence.L17.H17 theorem1C17 n

def Superseded.theorem1H18 (n psi : Nat) : Nat :=
  PPL.Convergence.L18.l18Horizon n psi

theorem Superseded.theorem1Horizon_eq_phase_sum
    (n psi : Nat) :
    Superseded.theorem1Horizon n psi =
      Superseded.theorem1H16 n psi +
        Superseded.theorem1H5i n +
        Superseded.theorem1H17 n +
        Superseded.theorem1H18 n psi := by
  rfl

/-
The frozen Lemma-5(ii) horizon is not the H17+H18 tail.

At n=3, psi=2:
  T5ii = 41404944
  H5i+H17+H18 = 31053546.
Thus even if C_mid is hit immediately at the L16 endpoint, the full
Lemma-5(ii) window does not fit in the remaining frozen horizon.

At n=4, psi=2:
  T5ii = 55206592
  H17+H18 = 82809024.
Thus the Lemma-5(ii) window can also be strictly shorter than the prime
L17+L18 run that it is supposed to couple.

Both pairs satisfy the theorem-1 parameter window.
-/
theorem Superseded.theorem1_quietWindow_too_long_at_3_2 :
    3 ≤ 3 ∧
      2 ≤ 2 ∧
      3 ≤ 2 ^ 2 ∧
      2 ≤ theorem1K 3 ∧
      Superseded.theorem1H5ii 3 2 >
        Superseded.theorem1H5i 3 +
          Superseded.theorem1H17 3 +
          Superseded.theorem1H18 3 2 := by
  decide

theorem Superseded.theorem1_quietWindow_too_short_at_4_2 :
    3 ≤ 4 ∧
      2 ≤ 2 ∧
      4 ≤ 2 ^ 2 ∧
      2 ≤ theorem1K 4 ∧
      Superseded.theorem1H5ii 4 2 <
        Superseded.theorem1H17 4 +
          Superseded.theorem1H18 4 2 := by
  decide

def Superseded.theorem1Block16
    {n : Nat}
    (psi : Nat)
    (word : DetSchedule n) :
    DetSchedule n :=
  word.take (Superseded.theorem1H16 n psi)

def Superseded.theorem1Block5i
    {n : Nat}
    (psi : Nat)
    (word : DetSchedule n) :
    DetSchedule n :=
  (word.drop (Superseded.theorem1H16 n psi)).take
    (Superseded.theorem1H5i n)

def Superseded.theorem1State16
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (Superseded.theorem1Kappa psi))
    (word : DetSchedule n) :
    Config n psi (Superseded.theorem1Kappa psi) :=
  PPL.Probability.runPPL
    ring C0 (Superseded.theorem1Block16 psi word)

def Superseded.theorem1MidCut
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (Superseded.theorem1Kappa psi))
    (word : DetSchedule n) :
    Option Nat :=
  theorem1FirstHitCut
    ring
    PPL.Modes.Lemma5.midPhysicalB
    (Superseded.theorem1State16 ring C0 word)
    (Superseded.theorem1Block5i psi word)

def Superseded.theorem1MidState
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (Superseded.theorem1Kappa psi))
    (word : DetSchedule n) :
    Option (Config n psi (Superseded.theorem1Kappa psi)) :=
  match Superseded.theorem1MidCut ring C0 word with
  | none => none
  | some t =>
      some
        (PPL.Probability.runPPL
          ring
          (Superseded.theorem1State16 ring C0 word)
          ((Superseded.theorem1Block5i psi word).take t))

def Superseded.theorem1QuietWord
    {n : Nat}
    (psi t : Nat)
    (word : DetSchedule n) :
    DetSchedule n :=
  (word.drop (Superseded.theorem1H16 n psi + t)).take
    (Superseded.theorem1H17 n + Superseded.theorem1H18 n psi)

def Superseded.theorem1L17Word
    {n : Nat}
    (psi t : Nat)
    (word : DetSchedule n) :
    DetSchedule n :=
  (Superseded.theorem1QuietWord psi t word).take
    (Superseded.theorem1H17 n)

def Superseded.theorem1L18Word
    {n : Nat}
    (psi t : Nat)
    (word : DetSchedule n) :
    DetSchedule n :=
  ((Superseded.theorem1QuietWord psi t word).drop
      (Superseded.theorem1H17 n)).take
    (Superseded.theorem1H18 n psi)

def Superseded.theorem1Literal17End
    {n psi : Nat}
    (ring : DirectedRing n)
    (Cmid : Config n psi (Superseded.theorem1Kappa psi))
    (t : Nat)
    (word : DetSchedule n) :
    PPL.LiteralElimConfig n :=
  PPL.Probability.runPopulationSchedule
    PPL.Elim.protocolE ring
    (PPL.Elim.viewConfig Cmid)
    (Superseded.theorem1L17Word psi t word)

def Superseded.theorem1Prime17End
    {n psi : Nat}
    (ring : DirectedRing n)
    (Cmid : Config n psi (Superseded.theorem1Kappa psi))
    (t : Nat)
    (word : DetSchedule n) :
    Config n psi (Superseded.theorem1Kappa psi) :=
  PPL.Convergence.ConstructCoupling.runPrime
    ring Cmid
    (Superseded.theorem1L17Word psi t word)

def Superseded.theorem1AllLeaderRootsMissB
    {n psi : Nat}
    (ring : DirectedRing n)
    (C : Config n psi (Superseded.theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  (List.ofFn
      (fun root : Fin n =>
        (!(C root).leader) ||
          !(PPL.Convergence.L18.l18HitsSPL
            ring root C word))).foldl
    (fun a b => a && b) true

/-
Five padded bad predicates on full H-words.

L16 uses the fixed H16 prefix.
L5(i) starts at the fixed L16 endpoint.
The remaining three events start at the dynamic first C_mid cut inside the
H5(i) block. The quiet predicate deliberately covers H17+H18, because that
is exactly the interval on which the full run must agree with P_PL prime for
the L17 and L18 phases.

This is the semantically correct event. Current Lemma5iiWordBound controls
a different length, Superseded.theorem1H5ii, and the two counterexamples above show that
the lengths cannot be identified uniformly.
-/
def Superseded.theorem1Bad16B
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (Superseded.theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  !(PPL.Convergence.ReachCPB.reachesCPB
    ring C0 (Superseded.theorem1Block16 psi word))

def Superseded.theorem1Bad5iB
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (Superseded.theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  PPL.Convergence.ReachCPB.reachesCPB
      ring C0 (Superseded.theorem1Block16 psi word) &&
    !(PPL.Modes.Lemma5.reachesAux
      ring
      PPL.Modes.Lemma5.midPhysicalB
      (Superseded.theorem1State16 ring C0 word)
      (Superseded.theorem1Block5i psi word))

def Superseded.theorem1Bad5iiB
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (Superseded.theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  match Superseded.theorem1MidCut ring C0 word,
      Superseded.theorem1MidState ring C0 word with
  | some t, some Cmid =>
      PPL.Convergence.ReachCPB.reachesCPB
          ring C0 (Superseded.theorem1Block16 psi word) &&
        !(PPL.Modes.Lemma5.constructAlong
          ring Cmid
          (Superseded.theorem1QuietWord psi t word))
  | _, _ => false

def Superseded.theorem1Bad17B
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (Superseded.theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  match Superseded.theorem1MidCut ring C0 word,
      Superseded.theorem1MidState ring C0 word with
  | some t, some Cmid =>
      PPL.Convergence.ReachCPB.reachesCPB
          ring C0 (Superseded.theorem1Block16 psi word) &&
        PPL.Modes.Lemma5.constructAlong
          ring Cmid
          (Superseded.theorem1QuietWord psi t word) &&
        !(decide
          (PPL.LiteralL1
            (Superseded.theorem1Literal17End
              ring Cmid t word)))
  | _, _ => false

def Superseded.theorem1Bad18B
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (Superseded.theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  match Superseded.theorem1MidCut ring C0 word,
      Superseded.theorem1MidState ring C0 word with
  | some t, some Cmid =>
      let C17 :=
        Superseded.theorem1Prime17End ring Cmid t word
      PPL.Convergence.ReachCPB.reachesCPB
          ring C0 (Superseded.theorem1Block16 psi word) &&
        PPL.Modes.Lemma5.constructAlong
          ring Cmid
          (Superseded.theorem1QuietWord psi t word) &&
        decide
          (PPL.LiteralL1
            (Superseded.theorem1Literal17End
              ring Cmid t word)) &&
        Superseded.theorem1AllLeaderRootsMissB
          ring C17
          (Superseded.theorem1L18Word psi t word)
  | _, _ => false

/-
Exact semantic splice row.

A proof should use:
* ReachCPB.reachesCPB_eq_endpoint and the CPB closure used by
  ReachCPB.lemma16_wordBound_of_steps;
* Lemma5iRetimedSplit.lemma5iWordBound_of_retimedCounts_noResetLineage
  for the H5(i) phase, after transporting CPB to neverLeaderless;
* QuietWindow.lemma5iiQuietWindowCoupling together with
  ConstructCoupling.runCoupling for the full-to-prime trace;
* LiteralEliminationBridges.primeStep_projects and runPrime_projects for the
  P_PL-prime to literal Algorithm-5 projection;
* L17.lemma17_wordBound_of_leaves for the literal one-leader phase;
* L18.n_mul_l18FailureCount_le_pow for the final phase, conditional on its
  current L18ForcingWordReachesSPL and lemma4_deterministic_core inputs.

The missing row is not deterministic coupling. It is the padded probability
row for Superseded.theorem1Bad5iiB: Lemma5.lemma5ii_wordBound controls exactly H5ii,
while Superseded.theorem1Bad5iiB must control H17+H18. The two horizon counterexamples
above rule out replacing one length by the other.
-/
def Superseded.Theorem1FiveEventSplice : Prop :=
  ∀ {n psi : Nat},
    3 ≤ n →
    2 ≤ psi →
    n ≤ 2 ^ psi →
    psi ≤ theorem1K n →
    ∀ (ring : DirectedRing n)
      (C0 : Config n psi (Superseded.theorem1Kappa psi))
      (word : DetSchedule n),
      word ∈ allSchedules n (Superseded.theorem1Horizon n psi) →
      !(theorem1ReachesSPL ring C0 word) = true →
      Superseded.theorem1Bad16B ring C0 word = true ∨
        Superseded.theorem1Bad5iB ring C0 word = true ∨
        Superseded.theorem1Bad5iiB ring C0 word = true ∨
        Superseded.theorem1Bad17B ring C0 word = true ∨
        Superseded.theorem1Bad18B ring C0 word = true

/-
The five per-cut padding rows below are the exact counting interfaces needed
to turn the uniform phase bounds into full-H padded events.

Rows 16, 5(i), 17 and 18 are the ordinary dynamic-cut/padding uses of the
existing uniform bounds named above. The 5(ii) row is the obstruction:
current main only has the H5ii bound, not an H17+H18 Construct-window bound.
-/
def Superseded.Theorem1L16PaddedBound : Prop :=
  ∀ {n psi : Nat},
    3 ≤ n →
    2 ≤ psi →
    n ≤ 2 ^ psi →
    psi ≤ theorem1K n →
    ∀ (ring : DirectedRing n)
      (C0 : Config n psi (Superseded.theorem1Kappa psi)),
      n *
          (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad16B ring C0) ≤
        12 * n ^ Superseded.theorem1Horizon n psi

def Superseded.Theorem1L5iPaddedBound : Prop :=
  ∀ {n psi : Nat},
    3 ≤ n →
    2 ≤ psi →
    n ≤ 2 ^ psi →
    psi ≤ theorem1K n →
    ∀ (ring : DirectedRing n)
      (C0 : Config n psi (Superseded.theorem1Kappa psi)),
      n *
          (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad5iB ring C0) ≤
        8 * n ^ Superseded.theorem1Horizon n psi

def Superseded.Theorem1L5iiDynamicPaddedBound : Prop :=
  ∀ {n psi : Nat},
    3 ≤ n →
    2 ≤ psi →
    n ≤ 2 ^ psi →
    psi ≤ theorem1K n →
    ∀ (ring : DirectedRing n)
      (C0 : Config n psi (Superseded.theorem1Kappa psi)),
      n *
          (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad5iiB ring C0) ≤
        4 * n ^ Superseded.theorem1Horizon n psi

def Superseded.Theorem1L17DynamicPaddedBound : Prop :=
  ∀ {n psi : Nat},
    3 ≤ n →
    2 ≤ psi →
    n ≤ 2 ^ psi →
    psi ≤ theorem1K n →
    ∀ (ring : DirectedRing n)
      (C0 : Config n psi (Superseded.theorem1Kappa psi)),
      n *
          (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad17B ring C0) ≤
        n ^ Superseded.theorem1Horizon n psi

def Superseded.Theorem1L18DynamicPaddedBound : Prop :=
  ∀ {n psi : Nat},
    3 ≤ n →
    2 ≤ psi →
    n ≤ 2 ^ psi →
    psi ≤ theorem1K n →
    ∀ (ring : DirectedRing n)
      (C0 : Config n psi (Superseded.theorem1Kappa psi)),
      n *
          (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad18B ring C0) ≤
        n ^ Superseded.theorem1Horizon n psi

theorem Superseded.theorem1_whp_of_fiveEventSplice
    (hsplice : Superseded.Theorem1FiveEventSplice)
    (h16 : Superseded.Theorem1L16PaddedBound)
    (h5i : Superseded.Theorem1L5iPaddedBound)
    (h5ii : Superseded.Theorem1L5iiDynamicPaddedBound)
    (h17 : Superseded.Theorem1L17DynamicPaddedBound)
    (h18 : Superseded.Theorem1L18DynamicPaddedBound)
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ theorem1K n)
    (ring : DirectedRing n)
    (C0 : Config n psi (Superseded.theorem1Kappa psi)) :
    let H := Superseded.theorem1Horizon n psi
    n * theorem1FailureNumerator ring C0 H ≤
      64 * n ^ H := by
  dsimp only
  have hb16 :=
    h16 hn3 hpsi hnpow hpsiK ring C0
  have hb5i :=
    h5i hn3 hpsi hnpow hpsiK ring C0
  have hb5ii :=
    h5ii hn3 hpsi hnpow hpsiK ring C0
  have hb17 :=
    h17 hn3 hpsi hnpow hpsiK ring C0
  have hb18 :=
    h18 hn3 hpsi hnpow hpsiK ring C0

  have hfailure :
      theorem1FailureNumerator
          ring C0
          (Superseded.theorem1Horizon n psi) ≤
        (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad16B ring C0) +
        (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad5iB ring C0) +
        (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad5iiB ring C0) +
        (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad17B ring C0) +
        (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad18B ring C0) := by
    unfold theorem1FailureNumerator
    exact
      theorem1_countP_five_union_le
        (allSchedules n
          (Superseded.theorem1Horizon n psi))
        (fun word =>
          !(theorem1ReachesSPL
            ring C0 word))
        (Superseded.theorem1Bad16B ring C0)
        (Superseded.theorem1Bad5iB ring C0)
        (Superseded.theorem1Bad5iiB ring C0)
        (Superseded.theorem1Bad17B ring C0)
        (Superseded.theorem1Bad18B ring C0)
        (fun word hmem hbad =>
          hsplice
            hn3 hpsi hnpow hpsiK
            ring C0 word hmem (by simpa using hbad))

  have hscaled :=
    Nat.mul_le_mul_left n hfailure

  have hphase :
      n *
          (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad16B ring C0) +
        n *
          (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad5iB ring C0) +
        n *
          (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad5iiB ring C0) +
        n *
          (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad17B ring C0) +
        n *
          (allSchedules n
            (Superseded.theorem1Horizon n psi)).countP
              (Superseded.theorem1Bad18B ring C0) ≤
      12 * n ^ Superseded.theorem1Horizon n psi +
        8 * n ^ Superseded.theorem1Horizon n psi +
        4 * n ^ Superseded.theorem1Horizon n psi +
        n ^ Superseded.theorem1Horizon n psi +
        n ^ Superseded.theorem1Horizon n psi := by
    exact
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add hb16 hb5i)
            hb5ii)
          hb17)
        hb18

  calc
    n *
          theorem1FailureNumerator
            ring C0
            (Superseded.theorem1Horizon n psi) ≤
        n *
          ((allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                (Superseded.theorem1Bad16B ring C0) +
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                (Superseded.theorem1Bad5iB ring C0) +
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                (Superseded.theorem1Bad5iiB ring C0) +
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                (Superseded.theorem1Bad17B ring C0) +
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                (Superseded.theorem1Bad18B ring C0)) :=
      hscaled
    _ =
        n *
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                (Superseded.theorem1Bad16B ring C0) +
          n *
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                (Superseded.theorem1Bad5iB ring C0) +
          n *
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                (Superseded.theorem1Bad5iiB ring C0) +
          n *
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                (Superseded.theorem1Bad17B ring C0) +
          n *
            (allSchedules n
              (Superseded.theorem1Horizon n psi)).countP
                (Superseded.theorem1Bad18B ring C0) := by
      simp only [Nat.mul_add]
    _ ≤
        12 * n ^ Superseded.theorem1Horizon n psi +
          8 * n ^ Superseded.theorem1Horizon n psi +
          4 * n ^ Superseded.theorem1Horizon n psi +
          n ^ Superseded.theorem1Horizon n psi +
          n ^ Superseded.theorem1Horizon n psi :=
      hphase
    _ ≤
        64 * n ^ Superseded.theorem1Horizon n psi :=
      theorem1_five_event_constants
        n (Superseded.theorem1Horizon n psi)


end PPL


#print axioms PPL.Superseded.theorem1C1_le_current
#print axioms PPL.Superseded.theorem1_four_phase_constants
#print axioms PPL.Superseded.theorem1_whp_of_phase_bounds
#print axioms PPL.Superseded.theorem1Horizon_eq_phase_sum
#print axioms PPL.Superseded.theorem1_quietWindow_too_long_at_3_2
#print axioms PPL.Superseded.theorem1_quietWindow_too_short_at_4_2
#print axioms PPL.Superseded.theorem1_whp_of_fiveEventSplice
