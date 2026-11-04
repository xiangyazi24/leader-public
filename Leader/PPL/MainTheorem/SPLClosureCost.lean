import Leader.PPL.MainTheorem.Statement
import Leader.PPL.MainTheorem.OneLeaderDynamicPadding
import Init.Omega

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/PPL/LogWindow/Cost.lean`, namespace `PPL.Superseded.LogWindow`: `Theorem1WhpUniform`, `Theorem1UniformHalfFailure`, `theorem1_cost_of_uniformFailure`, `Theorem1UniformHalfFailureLarge`, `Theorem1SmallNCost`, `theorem1Cost_of_whp_and_smallN`.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail

/--
Specialization of one-step SPL closure.
Uses PPL.Safety.SPL.splAt_closed from Leader/PPL/Safety/SPL.lean,
in the same way as Superseded.theorem1_cost_of_uniformFailure in
Leader/Superseded/Theorem1SequentialCost.lean.
-/
theorem theorem1SPL_closed_of_local
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n) :
    forall
      (D : Config n psi (theorem1Kappa psi))
      (e : Fin n),
      SPL ring D ->
        SPL ring
          (PopulationProtocol.step
            (protocol psi (theorem1Kappa psi))
            ring D e) := by
  intro D e hD
  unfold SPL at hD ⊢
  rcases hD with ⟨root, hroot⟩
  exact
    ⟨root,
      PPL.Safety.SPL.splAt_closed
        hlocal hn3 hpsi ring root D e hroot⟩

/--
If SPL already holds at the current state, theorem1ReachesSPL is true for
every suffix.  This just unfolds theorem1ReachesSPL from
Leader/PPL/MainTheorem/Skeleton.lean.
-/
theorem theorem1ReachesSPL_true_of_current
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hC : SPL ring C) :
    theorem1ReachesSPL ring C word = true := by
  cases word with
  | nil =>
      simp [theorem1ReachesSPL, hC]
  | cons e rest =>
      simp [theorem1ReachesSPL, hC]

/--
For a closed target, prefix miss and endpoint miss are the same event.

This is the semantic bridge that is absent from the old cost file:
theorem1ReachesSPL is a prefix-hitting Boolean, whereas miss (SPL ring)
in Leader/Wu/Elimination/ArbitraryInputMissAccounting.lean is an endpoint indicator.
-/
theorem theorem1ReachesSPL_eq_endpoint_of_closed
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (hclosed :
      forall (D : Config n psi kappa) (e : Fin n),
        SPL ring D ->
          SPL ring
            (PopulationProtocol.step
              (protocol psi kappa) ring D e))
    (C : Config n psi kappa)
    (word : DetSchedule n) :
    theorem1ReachesSPL ring C word =
      decide
        (SPL ring
          (LDSinkBoundedKernel.run
            (fun D e =>
              PopulationProtocol.step
                (protocol psi kappa) ring D e)
            C word)) := by
  induction word generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only
        [theorem1ReachesSPL,
          LDSinkBoundedKernel.run]
      by_cases hC : SPL ring C
      · have hnext :
            SPL ring
              (PopulationProtocol.step
                (protocol psi kappa) ring C e) :=
          hclosed C e hC
        have hrec :
            theorem1ReachesSPL
                ring
                (PopulationProtocol.step
                  (protocol psi kappa) ring C e)
                rest =
              true :=
          theorem1ReachesSPL_true_of_current
            ring
            (PopulationProtocol.step
              (protocol psi kappa) ring C e)
            rest
            hnext
        rw [show decide (SPL ring C) = true by simp [hC],
          Bool.true_or]
        have hi :=
          ih
            (C :=
              PopulationProtocol.step
                (protocol psi kappa) ring C e)
        exact hrec.symm.trans hi
      · rw [show decide (SPL ring C) = false by simp [hC],
          Bool.false_or]
        exact
          ih
            (C :=
              PopulationProtocol.step
                (protocol psi kappa) ring C e)

/--
Exact bridge from the Theorem-1 prefix-failure numerator to the endpoint-miss
wordSum consumed by FiniteAccounting.cost_le_two_blocks.

The list-count conversion is theorem1L17CountP_eq_fixedWordSum from
Leader/PPL/MainTheorem/OneLeaderDynamicPadding.lean.  The raw endpoint-sum conversion is
K2FiniteSafeEliminationExpected.wordSum_run from
Leader/Wu/Elimination/SafeEliminationWordCost.lean.
-/
theorem theorem1FailureNumerator_eq_wordSum_miss
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (hclosed :
      forall (D : Config n psi kappa) (e : Fin n),
        SPL ring D ->
          SPL ring
            (PopulationProtocol.step
              (protocol psi kappa) ring D e))
    (C : Config n psi kappa)
    (T : Nat) :
    theorem1FailureNumerator ring C T =
      wordSum
        (fun D e =>
          PopulationProtocol.step
            (protocol psi kappa) ring D e)
        (miss (SPL ring))
        C T := by
  classical
  unfold theorem1FailureNumerator
  rw [theorem1L17CountP_eq_fixedWordSum]
  rw [← K2FiniteSafeEliminationExpected.wordSum_run]
  apply
    congrArg
      (fun f : DetSchedule n -> Nat =>
        FixedSpanRenewalPayload.wordSum n T f)
  funext word
  rw [
    theorem1ReachesSPL_eq_endpoint_of_closed
      ring hclosed C word
  ]
  unfold miss
  by_cases h :
      SPL ring
        (LDSinkBoundedKernel.run
          (fun D e =>
            PopulationProtocol.step
              (protocol psi kappa) ring D e)
          C word)
  · simp [h]
  · simp [h]

/--
Per-parameter restart reducer.  This is the old
Superseded.theorem1_cost_of_uniformFailure proof shape with theorem1Kappa and
theorem1Horizon, delegating the geometric restart to
K2ArbitraryElimination.FiniteAccounting.cost_le_two_blocks from
Leader/Wu/Elimination/ArbitraryInputExpectedCost.lean.
-/
theorem theorem1_cost_of_halfFailure
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi))
    (hblock :
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
          n ^ theorem1Horizon n psi) :
    forall T : Nat,
      theorem1CostNumerator ring C0 T <=
        n ^ T * (2 * theorem1Horizon n psi) := by
  have hclosed :=
    theorem1SPL_closed_of_local
      hlocal hn3 hpsi ring

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
          n psi (theorem1Kappa psi) := by
    unfold PPL.Convergence.ReachCPB.lemma16Horizon
    omega

  have hH :
      0 < theorem1Horizon n psi := by
    unfold theorem1Horizon
    omega

  have hcost :=
    cost_le_two_blocks
      (fun D e =>
        PopulationProtocol.step
          (protocol psi (theorem1Kappa psi))
          ring D e)
      (SPL ring)
      hclosed
      (theorem1Horizon n psi)
      hH
      hblock

  intro T
  simpa [theorem1CostNumerator]
    using hcost T C0

end PPL

#print axioms PPL.theorem1FailureNumerator_eq_wordSum_miss
#print axioms PPL.theorem1_cost_of_halfFailure
