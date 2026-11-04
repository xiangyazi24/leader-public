import Leader.PPL.SequentialClock.Statement

/-!
# Superseded: the small-n cost split

Part of the second (sequential five-event) generation of the P_PL Theorem 1
statement, stated at the superseded clock `Superseded.theorem1Kappa` and
horizon `Superseded.theorem1Horizon`.  Not imported by the proved headline
`PPL.theorem1Statement_proved`.  Replaced by `Leader/PPL/MainTheorem/MissAmplification.lean` and `Leader/PPL/MainTheorem/LocalStepProtocolStep.lean`; the reason for the
replacement is recorded in `Leader/PPL/SequentialClock/Statement.lean`.
Kept, under `PPL.Superseded`, so the recorded history stays checkable.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail

/--
Uniform endpoint-miss form of the corrected five-event 26/n bound.

This is intentionally a contract: the arithmetic five-event union has been
audited, but the protocol-specific dynamic splice producing this uniform
restart statement is not yet on main.
-/
def Superseded.Theorem1UniformTwentySixFailure : Prop :=
  ∀ {n psi : Nat},
    3 ≤ n →
    2 ≤ psi →
    n ≤ 2 ^ psi →
    psi ≤ theorem1K n →
    ∀ (ring : DirectedRing n)
      (C : Config n psi (Superseded.theorem1Kappa psi)),
      n *
          wordSum
            (fun D e =>
              PopulationProtocol.step
                (protocol psi (Superseded.theorem1Kappa psi))
                ring D e)
            (miss (SPL ring))
            C
            (Superseded.theorem1Horizon n psi) ≤
        26 * n ^ Superseded.theorem1Horizon n psi

/--
For n ≥ 52, the uniform 26/n block estimate is a uniform half-failure
estimate in exactly the endpoint-miss currency consumed by
FiniteAccounting.cost_le_two_blocks.
-/
theorem Superseded.Theorem1UniformHalfFailureLarge
    (h26 : Superseded.Theorem1UniformTwentySixFailure)
    {n psi : Nat}
    (hn52 : 52 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ theorem1K n)
    (ring : DirectedRing n)
    (C : Config n psi (Superseded.theorem1Kappa psi)) :
    2 *
        wordSum
          (fun D e =>
            PopulationProtocol.step
              (protocol psi (Superseded.theorem1Kappa psi))
              ring D e)
          (miss (SPL ring))
          C
          (Superseded.theorem1Horizon n psi) ≤
      n ^ Superseded.theorem1Horizon n psi := by
  have h26C :=
    h26
      (n := n)
      (psi := psi)
      (by omega)
      hpsi
      hnpow
      hpsiK
      ring
      C
  have hscaled :
      26 *
          (2 *
            wordSum
              (fun D e =>
                PopulationProtocol.step
                  (protocol psi (Superseded.theorem1Kappa psi))
                  ring D e)
              (miss (SPL ring))
              C
              (Superseded.theorem1Horizon n psi)) ≤
        26 * n ^ Superseded.theorem1Horizon n psi := by
    calc
      26 *
          (2 *
            wordSum
              (fun D e =>
                PopulationProtocol.step
                  (protocol psi (Superseded.theorem1Kappa psi))
                  ring D e)
              (miss (SPL ring))
              C
              (Superseded.theorem1Horizon n psi)) =
          52 *
            wordSum
              (fun D e =>
                PopulationProtocol.step
                  (protocol psi (Superseded.theorem1Kappa psi))
                  ring D e)
              (miss (SPL ring))
              C
              (Superseded.theorem1Horizon n psi) := by
        omega
      _ ≤
          n *
            wordSum
              (fun D e =>
                PopulationProtocol.step
                  (protocol psi (Superseded.theorem1Kappa psi))
                  ring D e)
              (miss (SPL ring))
              C
              (Superseded.theorem1Horizon n psi) :=
        Nat.mul_le_mul_right _ hn52
      _ ≤ 26 * n ^ Superseded.theorem1Horizon n psi :=
        h26C
  exact
    Nat.le_of_mul_le_mul_left
      hscaled
      (by omega)

/--
Small-n amplification packaged in the exact strength needed by the expected
cost proof.

The single cSmall is already the finite maximum over all admissible
3 ≤ n < 52 parameter pairs.  The block B may depend on n and psi, but its
half-failure estimate is uniform over every physical configuration.

A bounded forcing-word producer can feed this contract via the generic
ClosedDomainSchedulerAmplificationSol machinery.  Requiring 2 ≤ cSmall
also makes the same constant dominate the large-n two-block coefficient.
-/
def Superseded.Theorem1SmallNAmplification : Prop :=
  ∃ cSmall : Nat,
    2 ≤ cSmall ∧
    ∀ {n psi : Nat},
      3 ≤ n →
      n < 52 →
      2 ≤ psi →
      n ≤ 2 ^ psi →
      psi ≤ theorem1K n →
      ∃ B : Nat,
        0 < B ∧
        2 * B ≤ cSmall * Superseded.theorem1Horizon n psi ∧
        ∀ (ring : DirectedRing n)
          (C : Config n psi (Superseded.theorem1Kappa psi)),
          2 *
              wordSum
                (fun D e =>
                  PopulationProtocol.step
                    (protocol psi (Superseded.theorem1Kappa psi))
                    ring D e)
                (miss (SPL ring))
                C
                B ≤
            n ^ B

/--
Large n uses the 26/n -> 1/2 conversion at one Theorem-1 horizon.
Small n uses its amplified pair-specific half block B.

FiniteAccounting.cost_le_two_blocks then gives the first-hit cost bound.
The one absolute constant is exactly the cSmall supplied by the finite
small-pair maximum; its assumption 2 ≤ cSmall also covers the large branch.
-/
theorem Superseded.theorem1_cost_conjunct_of_large_and_small
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    (h26 : Superseded.Theorem1UniformTwentySixFailure)
    (hsmall : Superseded.Theorem1SmallNAmplification) :
    ∃ cExpected : Nat,
      0 < cExpected ∧
      ∀ {n psi : Nat},
        3 ≤ n →
        2 ≤ psi →
        n ≤ 2 ^ psi →
        psi ≤ theorem1K n →
        ∀ (ring : DirectedRing n)
          (C0 : Config n psi (Superseded.theorem1Kappa psi))
          (T : Nat),
          theorem1CostNumerator ring C0 T ≤
            n ^ T *
              (cExpected * Superseded.theorem1Horizon n psi) := by
  rcases hsmall with
    ⟨cSmall, hcSmall, hsmallBound⟩
  refine ⟨cSmall, by omega, ?_⟩
  intro n psi hn3 hpsi hnpow hpsiK ring C0 T

  have hclosed :
      ∀ (D : Config n psi (Superseded.theorem1Kappa psi))
        (e : Fin n),
        SPL ring D →
          SPL ring
            (PopulationProtocol.step
              (protocol psi (Superseded.theorem1Kappa psi))
              ring D e) := by
    intro D e hD
    unfold SPL at hD ⊢
    rcases hD with ⟨root, hroot⟩
    exact
      ⟨root,
        PPL.Safety.SPL.splAt_closed
          hlocal hn3 hpsi ring root D e hroot⟩

  have hnpos : 0 < n := by
    omega

  have h15 :
      0 <
        PPL.Convergence.ReachCPB.lemma16H15 n := by
    unfold PPL.Convergence.ReachCPB.lemma16H15
    exact
      Nat.mul_pos
        (Nat.mul_pos (by omega) hnpos)
        (by omega)

  have h16 :
      0 <
        PPL.Convergence.ReachCPB.lemma16Horizon
          n psi (Superseded.theorem1Kappa psi) := by
    unfold PPL.Convergence.ReachCPB.lemma16Horizon
    omega

  have hH :
      0 < Superseded.theorem1Horizon n psi := by
    unfold Superseded.theorem1Horizon
    omega

  by_cases hnLarge : 52 ≤ n
  · have hblock :
        ∀ D : Config n psi (Superseded.theorem1Kappa psi),
          2 *
              wordSum
                (fun E e =>
                  PopulationProtocol.step
                    (protocol psi (Superseded.theorem1Kappa psi))
                    ring E e)
                (miss (SPL ring))
                D
                (Superseded.theorem1Horizon n psi) ≤
            n ^ Superseded.theorem1Horizon n psi := by
      intro D
      exact
        Superseded.Theorem1UniformHalfFailureLarge
          h26
          hnLarge
          hpsi
          hnpow
          hpsiK
          ring
          D

    have hcost :=
      cost_le_two_blocks
        (fun D e =>
          PopulationProtocol.step
            (protocol psi (Superseded.theorem1Kappa psi))
            ring D e)
        (SPL ring)
        hclosed
        (Superseded.theorem1Horizon n psi)
        hH
        hblock

    have hcoef :
        2 * Superseded.theorem1Horizon n psi ≤
          cSmall * Superseded.theorem1Horizon n psi :=
      Nat.mul_le_mul_right
        (Superseded.theorem1Horizon n psi)
        hcSmall

    exact
      Nat.le_trans
        (by
          simpa [theorem1CostNumerator]
            using hcost T C0)
        (Nat.mul_le_mul_left (n ^ T) hcoef)

  · have hnSmall : n < 52 := by
      omega
    rcases
        hsmallBound
          (n := n)
          (psi := psi)
          hn3
          hnSmall
          hpsi
          hnpow
          hpsiK with
      ⟨B, hBpos, hBscale, hBhalf⟩

    have hblock :
        ∀ D : Config n psi (Superseded.theorem1Kappa psi),
          2 *
              wordSum
                (fun E e =>
                  PopulationProtocol.step
                    (protocol psi (Superseded.theorem1Kappa psi))
                    ring E e)
                (miss (SPL ring))
                D
                B ≤
            n ^ B := by
      intro D
      exact hBhalf ring D

    have hcost :=
      cost_le_two_blocks
        (fun D e =>
          PopulationProtocol.step
            (protocol psi (Superseded.theorem1Kappa psi))
            ring D e)
        (SPL ring)
        hclosed
        B
        hBpos
        hblock

    exact
      Nat.le_trans
        (by
          simpa [theorem1CostNumerator]
            using hcost T C0)
        (Nat.mul_le_mul_left (n ^ T) hBscale)

end PPL

#print axioms PPL.Superseded.Theorem1UniformHalfFailureLarge
#print axioms PPL.Superseded.theorem1_cost_conjunct_of_large_and_small
