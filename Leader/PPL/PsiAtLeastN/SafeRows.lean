import Leader.PPL.PsiAtLeastN.Statement
import Leader.PPL.PsiAtLeastN.SafeEntryForcing
import Leader.PPL.MainTheorem.GeneralQuietWindowFit
import Leader.PPL.MainTheorem.GeneralWhp
import Leader.PPL.MainTheorem.GeneralTargets

/-!
# P_PL Theorem 1 on `n ≤ psi`: shared statements of the safe whp chain

The whp proof of Theorem 1 (`PPL.theorem1_whp_of_splice`) splits a failing
word into five bad events (L16, L5(i), L5(ii), L17, L18) and bounds each by
a padded count.  On `psi < n` this is `PPL.PsiBelowN`.  On `n ≤ psi` only
the last event changes: the L18 phase now has to reach the rooted safe
predicate `SPLAt root ∨ CDLAt root` (`L18SafeForcing.lean`), and the target
of the splice is `Theorem1SafeTarget`, which with one segment contains
rooted `C_DL`.

This file restates, on the domain `n ≤ psi`:

* the arithmetic seams `theorem1_quietWindow_covers_run` and
  `theorem1H17_add_H18_le_H5ii` (their original proofs use only `3 ≤ n`,
  `2 ≤ psi`, `n ≤ 2 ^ psi`; the domain premise is carried for interface
  shape only);
* the L16, L5(i), L5(ii), L17 padded interfaces, unchanged except for the
  domain premise;
* the safe L18 bad event `theorem1Bad18SafeB` (the rooted `P_PL'` run of the
  L18 slice misses the rooted safe predicate for every leader root) and its
  padded interface;
* the safe five-event splice `Theorem1SafeFiveEventSplice` (a word that
  never visits `Theorem1SafeTarget` is bad for one of the five events), and
  the whp assembly `theorem1SafeWhp_of_splice` (constant 64, the same union
  and coefficient arithmetic as `PPL.theorem1_whp_of_splice`).

Inside this namespace the seam and interface names deliberately shadow
their `PPL` namesakes, so copied proof text elaborates unchanged.  No
accepted upstream module is edited.
-/

namespace PPL.PsiAtLeastN

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## Shadowed arithmetic seams -/

/-- The quiet-window fit (`PPL.theorem1_quietWindow_covers_run`) on the
domain `n ≤ psi`.  The original proof uses only `3 ≤ n`, `2 ≤ psi` and
`n ≤ 2 ^ psi`; it is the special case of
`PPL.Theorem1General.theorem1_quietWindow_covers_run`. -/
theorem theorem1_quietWindow_covers_run
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (_hge : n ≤ psi) :
    PPL.Convergence.L17.H17 theorem1C17 n +
        PPL.Convergence.L18.l18Horizon n psi ≤
      PPL.Modes.Lemma5.lemma5iiHorizon
        n psi (theorem1Kappa psi) :=
  PPL.Theorem1General.theorem1_quietWindow_covers_run hn3 hpsi hnpow

/-- `PPL.theorem1H17_add_H18_le_H5ii` on the domain `n ≤ psi`. -/
theorem theorem1H17_add_H18_le_H5ii
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (hge : n ≤ psi) :
    theorem1H17 n + theorem1H18 n psi <=
      theorem1H5ii n psi :=
  PPL.Theorem1General.theorem1H17_add_H18_le_H5ii hn3 hpsi hnpow

/-! ## The safe L18 bad event -/

/-- Every leader root misses the rooted safe predicate along the `P_PL'`
run of `word` (safe counterpart of `PPL.theorem1AllLeaderRootsMissB`). -/
def theorem1AllLeaderRootsMissSafeB
    {n psi : Nat}
    (ring : DirectedRing n)
    (C : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  (List.ofFn
      (fun root : Fin n =>
        (!(C root).leader) ||
          !(l18HitsSafe ring root C word))).foldl
    (fun a b => a && b) true

/-- Safe L18 bad event: `PPL.theorem1Bad18B` with the rooted safe predicate
in place of rooted `S_PL`. -/
def theorem1Bad18SafeB
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) : Bool :=
  match theorem1MidCut ring C0 word,
      theorem1MidState ring C0 word with
  | some t, some Cmid =>
      let C17 :=
        theorem1Prime17End ring Cmid t word
      PPL.Convergence.ReachCPB.reachesCPB
          ring C0 (theorem1Block16 psi word) &&
        PPL.Modes.Lemma5.constructAlong
          ring Cmid
          (theorem1QuietWord psi t word) &&
        decide
          (PPL.LiteralL1
            (theorem1Literal17End
              ring Cmid t word)) &&
        theorem1AllLeaderRootsMissSafeB
          ring C17
          (theorem1L18Word psi t word)
  | _, _ => false

/-- Safe L18 phase event at a dynamic first-hit cut
(`PPL.theorem1L18FirstHitPhaseBad` with the safe miss). -/
def theorem1L18SafeFirstHitPhaseBad
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p phase : DetSchedule n) : Bool :=
  let Cmid :=
    PPL.Probability.runPPL ring C0 p
  let w17 :=
    phase.take (theorem1H17 n)
  let C17 :=
    PPL.Convergence.ConstructCoupling.runPrime
      ring Cmid w17
  (PPL.Modes.Lemma5.constructAlong
      ring Cmid phase &&
    @decide
      (PPL.LiteralL1
        (PPL.Probability.runPopulationSchedule
          PPL.Elim.protocolE ring
          (PPL.Elim.viewConfig Cmid)
          w17))
      (theorem1LiteralL1Decidable _)) &&
    theorem1AllLeaderRootsMissSafeB
      ring C17
      ((phase.drop (theorem1H17 n)).take
        (theorem1H18 n psi))

/-! ## The safe events as instances of the general ones -/

/-- `theorem1ReachesSafeTarget` is the prefix-hitting test for the safe
target. -/
theorem theorem1ReachesSafeTarget_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    ∀ (C : Config n psi kappa) (word : DetSchedule n),
      theorem1ReachesSafeTarget ring C word =
        PPL.Theorem1General.theorem1ReachesB ring
          (fun C => decide (Theorem1SafeTarget ring C)) C word := by
  intro C word
  induction word generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only
        [theorem1ReachesSafeTarget, PPL.Theorem1General.theorem1ReachesB, ih]

/-- `l18HitsSafe` is the `P_PL'` prefix-hitting test for `L18SafeAt`. -/
theorem l18HitsSafe_eq
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n) :
    ∀ (C : Config n psi kappa) (word : DetSchedule n),
      l18HitsSafe ring root C word =
        PPL.Theorem1General.theorem1L18HitsB ring
          (fun C => decide (L18SafeAt ring root C)) C word := by
  intro C word
  induction word generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [l18HitsSafe, PPL.Theorem1General.theorem1L18HitsB, ih]

/-- `theorem1AllLeaderRootsMissSafeB` is the miss event for `L18SafeAt`. -/
theorem theorem1AllLeaderRootsMissSafeB_eq
    {n psi : Nat}
    (ring : DirectedRing n)
    (C : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) :
    theorem1AllLeaderRootsMissSafeB ring C word =
      PPL.Theorem1General.theorem1AllLeaderRootsMissGen ring
        (fun root C => decide (L18SafeAt ring root C)) C word := by
  unfold theorem1AllLeaderRootsMissSafeB
    PPL.Theorem1General.theorem1AllLeaderRootsMissGen
  simp only [l18HitsSafe_eq]

/-- `theorem1Bad18SafeB` is the L18 bad event for `L18SafeAt`. -/
theorem theorem1Bad18SafeB_eq
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (word : DetSchedule n) :
    theorem1Bad18SafeB ring C0 word =
      PPL.Theorem1General.theorem1Bad18Gen ring
        (fun root C => decide (L18SafeAt ring root C)) C0 word := by
  unfold theorem1Bad18SafeB PPL.Theorem1General.theorem1Bad18Gen
  cases theorem1MidCut ring C0 word <;>
    cases theorem1MidState ring C0 word <;>
    simp only [theorem1AllLeaderRootsMissSafeB_eq]

/-- `theorem1L18SafeFirstHitPhaseBad` is the L18 phase event for
`L18SafeAt`. -/
theorem theorem1L18SafeFirstHitPhaseBad_eq
    {n psi : Nat}
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (p phase : DetSchedule n) :
    theorem1L18SafeFirstHitPhaseBad ring C0 p phase =
      PPL.Theorem1General.theorem1L18FirstHitPhaseBadGen ring
        (fun root C => decide (L18SafeAt ring root C)) C0 p phase := by
  unfold theorem1L18SafeFirstHitPhaseBad
    PPL.Theorem1General.theorem1L18FirstHitPhaseBadGen
  dsimp only
  exact congrArg (and _) (theorem1AllLeaderRootsMissSafeB_eq ring _ _)

/-! ## The safe splice and the five padded interfaces on `n ≤ psi` -/

/-- Safe five-event splice: on `n ≤ psi`, a Theorem-1 word that never visits
`Theorem1SafeTarget` is bad for L16, L5(i), L5(ii), L17 or the safe L18
event. -/
def Theorem1SafeFiveEventSplice : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    n <= psi ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi))
      (word : DetSchedule n),
      word ∈ allSchedules n
        (theorem1Horizon n psi) ->
      !(theorem1ReachesSafeTarget ring C0 word) = true ->
      Or
        (theorem1Bad16B ring C0 word = true)
        (Or
          (theorem1Bad5iB ring C0 word = true)
          (Or
            (theorem1Bad5iiB ring C0 word = true)
            (Or
              (theorem1Bad17B ring C0 word = true)
              (theorem1Bad18SafeB ring C0 word = true))))

-- [copied from Leader/PPL/MainTheorem/Statement.lean:321-335]
def Theorem1L16PaddedBound : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    n <= psi ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi)),
      n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad16B ring C0) <=
        12 * n ^ theorem1Horizon n psi

-- [copied from Leader/PPL/MainTheorem/Statement.lean:336-350]
def Theorem1L5iPaddedBound : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    n <= psi ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi)),
      n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad5iB ring C0) <=
        8 * n ^ theorem1Horizon n psi

-- [copied from Leader/PPL/MainTheorem/Statement.lean:351-365]
def Theorem1L5iiDynamicPaddedBound : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    n <= psi ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi)),
      n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad5iiB ring C0) <=
        4 * n ^ theorem1Horizon n psi

-- [copied from Leader/PPL/MainTheorem/Statement.lean:366-380]
def Theorem1L17DynamicPaddedBound : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    n <= psi ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi)),
      n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad17B ring C0) <=
        n ^ theorem1Horizon n psi

/-- Padded safe L18 bound (`PPL.Theorem1L18DynamicPaddedBound` with
`theorem1Bad18SafeB`). -/
def Theorem1L18SafeDynamicPaddedBound : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    n <= psi ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi)),
      n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad18SafeB ring C0) <=
        n ^ theorem1Horizon n psi

/-- The safe whp bound follows from the safe splice and the five padded
phase bounds (`PPL.Theorem1General.theorem1_whp_of_splice_at` with the
global test `theorem1ReachesSafeTarget` and the L18 event
`theorem1Bad18SafeB`). -/
theorem theorem1SafeWhp_of_splice
    (hsplice : Theorem1SafeFiveEventSplice)
    (h16 : Theorem1L16PaddedBound)
    (h5i : Theorem1L5iPaddedBound)
    (h5ii : Theorem1L5iiDynamicPaddedBound)
    (h17 : Theorem1L17DynamicPaddedBound)
    (h18 : Theorem1L18SafeDynamicPaddedBound)
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (hge : n <= psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    let H := theorem1Horizon n psi
    n * theorem1SafeFailureNumerator ring C0 H <=
      64 * n ^ H :=
  PPL.Theorem1General.theorem1_whp_of_splice_at ring C0
    (theorem1ReachesSafeTarget ring C0) (theorem1Bad18SafeB ring C0)
    (fun word hmem hfail =>
      hsplice hn3 hpsi hnpow hge ring C0 word hmem hfail)
    (h16 hn3 hpsi hnpow hge ring C0)
    (h5i hn3 hpsi hnpow hge ring C0)
    (h5ii hn3 hpsi hnpow hge ring C0)
    (h17 hn3 hpsi hnpow hge ring C0)
    (h18 hn3 hpsi hnpow hge ring C0)

end PPL.PsiAtLeastN

#print axioms PPL.PsiAtLeastN.theorem1_quietWindow_covers_run
#print axioms PPL.PsiAtLeastN.theorem1SafeWhp_of_splice
