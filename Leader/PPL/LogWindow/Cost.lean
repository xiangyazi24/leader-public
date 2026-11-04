import Leader.PPL.MainTheorem.SPLClosureCost
import Leader.PPL.MainTheorem.Statement
import Leader.PPL.MainTheorem.OneLeaderDynamicPadding
import Init.Omega

/-!
# Superseded (log-window route): dead declarations of `Leader/PPL/MainTheorem/SPLClosureCost.lean`

Moved out of `Leader/PPL/MainTheorem/SPLClosureCost.lean` by the P_PL Theorem 1 cleanup, phase 2.
These declarations served only the original psi <= log2 n + 1 route to
`PPL.theorem1Statement_proved`, which now goes through
`PPL.theorem1Statement_proved_via_slack` (`Leader/PPL/MainTheorem/PsiWindowSlack.lean`).
Nothing in the live Theorem 1 closure uses them; they are kept, and still build,
as the record of that route.  Every name `PPL.X` became `PPL.Superseded.LogWindow.X`;
see `research-map/RENAME_MAP_PPL.md` (phase 2).
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail
namespace PPL.Superseded.LogWindow

/--
Exactly the WHP body from the second probabilistic conjunct of
Theorem1Statement, but made uniform over the restart state C0.
Source statement: Leader/PPL/MainTheorem/Statement.lean, Theorem1Statement.
-/
def Theorem1WhpUniform : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    psi <= theorem1K n ->
    forall
      (ring : DirectedRing n)
      (C0 : Config n psi (theorem1Kappa psi)),
      let H := theorem1Horizon n psi
      n * theorem1FailureNumerator ring C0 H <=
        64 * n ^ H

/--
The direct analogue of the superseded Superseded.Theorem1UniformHalfFailure from
Leader/Superseded/Theorem1SequentialCost.lean.
-/
def Theorem1UniformHalfFailure : Prop :=
  forall {n psi : Nat},
    3 <= n ->
    2 <= psi ->
    n <= 2 ^ psi ->
    psi <= theorem1K n ->
    forall
      (ring : DirectedRing n)
      (C : Config n psi (theorem1Kappa psi)),
      2 *
          wordSum
            (fun D e =>
              PopulationProtocol.step
                (protocol psi (theorem1Kappa psi))
                ring D e)
            (miss (SPL ring))
            C
            (theorem1Horizon n psi) <=
        n ^ theorem1Horizon n psi

/--
Global-contract wrapper, exactly analogous to
Superseded.theorem1_cost_of_uniformFailure in Leader/Superseded/Theorem1SequentialCost.lean.
-/
theorem theorem1_cost_of_uniformFailure
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    (huniform : Theorem1UniformHalfFailure)
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (hpsiK : psi <= theorem1K n)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    forall T : Nat,
      theorem1CostNumerator ring C0 T <=
        n ^ T * (2 * theorem1Horizon n psi) := by
  exact
    theorem1_cost_of_halfFailure
      hlocal hn3 hpsi ring C0
      (by
        intro D
        exact
          huniform
            hn3 hpsi hnpow hpsiK
            ring D)

/--
For n >= 128, the uniform WHP bound is already a uniform half-failure
block bound.  The factor 128 is exactly 2*64.
-/
theorem Theorem1UniformHalfFailureLarge
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    (hwhp : Theorem1WhpUniform)
    {n psi : Nat}
    (hn128 : 128 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi)
    (hpsiK : psi <= theorem1K n)
    (ring : DirectedRing n)
    (C : Config n psi (theorem1Kappa psi)) :
    2 *
        wordSum
          (fun D e =>
            PopulationProtocol.step
              (protocol psi (theorem1Kappa psi))
              ring D e)
          (miss (SPL ring))
          C
          (theorem1Horizon n psi) <=
      n ^ theorem1Horizon n psi := by
  have hn3 : 3 <= n := by
    omega


  have hclosed :=
    theorem1SPL_closed_of_local
      hlocal hn3 hpsi ring


  have h64 :=
    hwhp
      (n := n)
      (psi := psi)
      hn3 hpsi hnpow hpsiK
      ring C
  dsimp only at h64


  rw [
    theorem1FailureNumerator_eq_wordSum_miss
      ring hclosed C (theorem1Horizon n psi)
  ] at h64


  have hscaled :
      64 *
          (2 *
            wordSum
              (fun D e =>
                PopulationProtocol.step
                  (protocol psi (theorem1Kappa psi))
                  ring D e)
              (miss (SPL ring))
              C
              (theorem1Horizon n psi)) <=
        64 * n ^ theorem1Horizon n psi := by
    calc
      64 *
          (2 *
            wordSum
              (fun D e =>
                PopulationProtocol.step
                  (protocol psi (theorem1Kappa psi))
                  ring D e)
              (miss (SPL ring))
              C
              (theorem1Horizon n psi)) =
          128 *
            wordSum
              (fun D e =>
                PopulationProtocol.step
                  (protocol psi (theorem1Kappa psi))
                  ring D e)
              (miss (SPL ring))
              C
              (theorem1Horizon n psi) := by
        omega
      _ <=
          n *
            wordSum
              (fun D e =>
                PopulationProtocol.step
                  (protocol psi (theorem1Kappa psi))
                  ring D e)
              (miss (SPL ring))
              C
              (theorem1Horizon n psi) :=
        Nat.mul_le_mul_right _ hn128
      _ <=
          64 * n ^ theorem1Horizon n psi :=
        h64


  exact
    Nat.le_of_mul_le_mul_left
      hscaled
      (by omega)

/--
Weak small-n leaf: this asks only for the final cost estimate needed by the
top-level reducer, with one absolute coefficient cSmall that also dominates
the large-n coefficient 2.
-/
def Theorem1SmallNCost : Prop :=
  exists cSmall : Nat,
    2 <= cSmall /\
    forall {n psi : Nat},
      3 <= n ->
      n < 128 ->
      2 <= psi ->
      n <= 2 ^ psi ->
      psi <= theorem1K n ->
      forall
        (ring : DirectedRing n)
        (C0 : Config n psi (theorem1Kappa psi))
        (T : Nat),
        theorem1CostNumerator ring C0 T <=
          n ^ T *
            (cSmall * theorem1Horizon n psi)

/--
The cost conjunct from uniform WHP plus the finite small-n leaf.


Large n uses Theorem1UniformHalfFailureLarge and
theorem1_cost_of_halfFailure.  Small n is exactly Theorem1SmallNCost.
The same cSmall is used globally; 2 <= cSmall absorbs the large-n coefficient.
-/
theorem theorem1Cost_of_whp_and_smallN
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    (hwhp : Theorem1WhpUniform)
    (hsmall : Theorem1SmallNCost) :
    exists cExpected : Nat,
      0 < cExpected /\
      forall {n psi : Nat},
        3 <= n ->
        2 <= psi ->
        n <= 2 ^ psi ->
        psi <= theorem1K n ->
        forall
          (ring : DirectedRing n)
          (C0 : Config n psi (theorem1Kappa psi))
          (T : Nat),
          theorem1CostNumerator ring C0 T <=
            n ^ T *
              (cExpected * theorem1Horizon n psi) := by
  rcases hsmall with
    ⟨cSmall, hcSmall, hsmallBound⟩


  refine
    ⟨cSmall, by omega, ?_⟩


  intro n psi hn3 hpsi hnpow hpsiK ring C0 T


  by_cases hnLarge : 128 <= n
  · have hblock :
        forall D : Config n psi (theorem1Kappa psi),
          2 *
              wordSum
                (fun E e =>
                  PopulationProtocol.step
                    (protocol psi (theorem1Kappa psi))
                    ring E e)
                (miss (SPL ring))
                D
                (theorem1Horizon n psi) <=
            n ^ theorem1Horizon n psi := by
      intro D
      exact
        Theorem1UniformHalfFailureLarge
          hlocal hwhp
          hnLarge hpsi hnpow hpsiK
          ring D


    have hcost :
        theorem1CostNumerator ring C0 T <=
          n ^ T *
            (2 * theorem1Horizon n psi) :=
      theorem1_cost_of_halfFailure
        hlocal hn3 hpsi ring C0 hblock T


    have hcoef :
        2 * theorem1Horizon n psi <=
          cSmall * theorem1Horizon n psi :=
      Nat.mul_le_mul_right
        (theorem1Horizon n psi)
        hcSmall


    exact
      Nat.le_trans
        hcost
        (Nat.mul_le_mul_left
          (n ^ T)
          hcoef)


  · have hnSmall : n < 128 := by
      omega
    exact
      hsmallBound
        (n := n)
        (psi := psi)
        hn3 hnSmall hpsi hnpow hpsiK
        ring C0 T

end PPL.Superseded.LogWindow
end
