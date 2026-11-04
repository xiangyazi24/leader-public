import Leader.PPL.MainTheorem.Statement
import Leader.PPL.SPLEntry.CountScoped
import Leader.PPL.MainTheorem.GeneralQuietWindowFit
import Leader.PPL.MainTheorem.GeneralWhp

/-!
# P_PL Theorem 1 on the domain `psi < n`: shared statements

The proved Theorem 1 (`PPL.Theorem1Statement`) assumes the psi window
`psi ≤ theorem1K n = log2 n + 1`.  Reading the proofs, that window is used
for three things only:

* the L16 fixed-word scale `n ≤ 2 ^ (4 * lemma16K n)`, which holds for every
  `n` (`lemma16_wordBound_capped_noUpper`);
* `psi < n`, the scope of the Lemma-18 forcing word
  (`theorem1_psi_lt_n`, consumed by `L18ForcingWordReachesSPLScoped`);
* finiteness of the admissible `psi` at a fixed tiny `n` in the expected-cost
  proof, which `psi < n` also gives.

Every other occurrence is a threaded hypothesis that is never consumed (the
quiet-window fit `theorem1_quietWindow_covers_run` takes it and ignores it).

The namespace `PPL.PsiBelowN` restates the interfaces of the Theorem-1 chain
with `psi ≤ theorem1K n` replaced by `psi < n`, and re-proves them by copies
of the original proofs.  Inside this namespace the three declarations below
deliberately shadow their `PPL` namesakes, so the copied proof text that
calls them elaborates unchanged against the new hypothesis:

* `theorem1_quietWindow_covers_run` and `theorem1H17_add_H18_le_H5ii`, whose
  upper-window argument was unused;
* `theorem1_psi_lt_n`, which is the identity on the new hypothesis.

No accepted upstream module is edited.
-/

namespace PPL.PsiBelowN

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## Shadowed arithmetic seams -/

/-- The quiet-window fit (`PPL.theorem1_quietWindow_covers_run`) on the
domain `psi < n`.  The original proof uses only `3 ≤ n`, `2 ≤ psi` and
`n ≤ 2 ^ psi`; the window premise is carried for interface shape only.
Special case of `PPL.Theorem1General.theorem1_quietWindow_covers_run`. -/
theorem theorem1_quietWindow_covers_run
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (_hlt : psi < n) :
    PPL.Convergence.L17.H17 theorem1C17 n +
        PPL.Convergence.L18.l18Horizon n psi ≤
      PPL.Modes.Lemma5.lemma5iiHorizon
        n psi (theorem1Kappa psi) :=
  PPL.Theorem1General.theorem1_quietWindow_covers_run hn3 hpsi hnpow

/-- `PPL.theorem1H17_add_H18_le_H5ii` on the domain `psi < n`. -/
theorem theorem1H17_add_H18_le_H5ii
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (hlt : psi < n) :
    theorem1H17 n + theorem1H18 n psi <=
      theorem1H5ii n psi :=
  PPL.Theorem1General.theorem1H17_add_H18_le_H5ii hn3 hpsi hnpow

/-- On the domain `psi < n` the Lemma-18 scope premise is the hypothesis
itself (`PPL.theorem1_psi_lt_n` derives it from the log window). -/
theorem theorem1_psi_lt_n
    {n psi : Nat}
    (_hn3 : 3 ≤ n)
    (hlt : psi < n) :
    psi < n :=
  hlt

/-- The log window of `PPL.Theorem1Statement` lies inside `psi < n`. -/
theorem psi_lt_n_of_theorem1K
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsiK : psi ≤ theorem1K n) :
    psi < n :=
  PPL.theorem1_psi_lt_n hn3 hpsiK

/-! ## The splice and the five padded interfaces on `psi < n` -/

-- [copied from Leader/PPL/MainTheorem/Statement.lean:289-318]
/--
the earlier five-event semantic splice, retargeted to theorem1Kappa and theorem1Horizon.

The third event is now failure of the full fixed H5ii(theorem1Kappa) Construct
window beginning at the dynamic first C_mid cut.  The L17 and L18 words are
slices of that same quiet word.
-/
def Theorem1FiveEventSplice : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    psi < n ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi))
      (word : DetSchedule n),
      word ∈ allSchedules n
        (theorem1Horizon n psi) ->
      !(theorem1ReachesSPL ring C0 word) = true ->
      Or
        (theorem1Bad16B ring C0 word = true)
        (Or
          (theorem1Bad5iB ring C0 word = true)
          (Or
            (theorem1Bad5iiB ring C0 word = true)
            (Or
              (theorem1Bad17B ring C0 word = true)
              (theorem1Bad18B ring C0 word = true))))

-- [copied from Leader/PPL/MainTheorem/Statement.lean:321-335]
def Theorem1L16PaddedBound : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    psi < n ->
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
    psi < n ->
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
    psi < n ->
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
    psi < n ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi)),
      n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad17B ring C0) <=
        n ^ theorem1Horizon n psi

-- [copied from Leader/PPL/MainTheorem/Statement.lean:381-395]
def Theorem1L18DynamicPaddedBound : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    psi < n ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi)),
      n *
          (allSchedules n
            (theorem1Horizon n psi)).countP
              (theorem1Bad18B ring C0) <=
        n ^ theorem1Horizon n psi

/--
The WHP conjunct follows from the semantic splice and the five padded
phase bounds (`PPL.Theorem1General.theorem1_whp_of_splice_at` with the
global test `theorem1ReachesSPL` and the L18 event `theorem1Bad18B`).
-/
theorem theorem1_whp_of_splice
    (hsplice : Theorem1FiveEventSplice)
    (h16 : Theorem1L16PaddedBound)
    (h5i : Theorem1L5iPaddedBound)
    (h5ii : Theorem1L5iiDynamicPaddedBound)
    (h17 : Theorem1L17DynamicPaddedBound)
    (h18 : Theorem1L18DynamicPaddedBound)
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (hpsiK : psi < n)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    let H := theorem1Horizon n psi
    n * theorem1FailureNumerator ring C0 H <=
      64 * n ^ H :=
  PPL.Theorem1General.theorem1_whp_of_splice_at ring C0
    (theorem1ReachesSPL ring C0) (theorem1Bad18B ring C0)
    (fun word hmem hfail =>
      hsplice hn3 hpsi hnpow hpsiK ring C0 word hmem hfail)
    (h16 hn3 hpsi hnpow hpsiK ring C0)
    (h5i hn3 hpsi hnpow hpsiK ring C0)
    (h5ii hn3 hpsi hnpow hpsiK ring C0)
    (h17 hn3 hpsi hnpow hpsiK ring C0)
    (h18 hn3 hpsi hnpow hpsiK ring C0)

end PPL.PsiBelowN

#print axioms PPL.PsiBelowN.theorem1_quietWindow_covers_run
#print axioms PPL.PsiBelowN.theorem1_whp_of_splice
