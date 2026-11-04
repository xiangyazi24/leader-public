import Leader.PPL.MainTheorem.CostFromThirteenTail
import Leader.PPL.SPLEntry.ForcingWordClosed
import Leader.PPL.MainTheorem.PossibleUniformBound
import Init.Omega

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/Superseded/Theorem1LogWindow/Theorem1PossibleFromCPB.lean`, namespace `PPL.Superseded.LogWindow`: `q20313cpb_sum_if_count`, `q20313cpb_countP_take_pad`, `theorem1FromCPB_tailJointSelection_of_coeff`, `q20313cpb_firstHitCut_some_of_reachesAux`, `theorem1FromCPB_firstTwoStages`, `theorem1PossibleFromCPB_of_eight_lt`, `Theorem1PossibleConvergenceFrom9To12`, `theorem1PossibleConvergenceFrom9To12_of_reachCPB`.
-/

/-!
# Pointwise possible convergence of P_PL from a C_PB configuration (n > 8)

This file proves the post-CPB half of pointwise possible convergence: for the
Theorem-1 parameter window with `8 < n`, every configuration satisfying
`PPL.CPB` has a scheduler word whose prefix hits `SPL`
(`theorem1ReachesSPL ring C w = true`).

Architecture:

* **Restarted frame.**  The From13 chain charges L16 through a combined
  selector of coefficient 12, which is the only reason it needs `13 ≤ n`.
  Starting from a CPB configuration we skip L16 entirely: the H16 slot of the
  accounting frame is filled with an arbitrary edge repeated H16 times, and
  CPB survives this padding because CPB is closed under every run
  (`PPL.Convergence.ReachCPB.cpb_run_closed`).
* **L5(i).**  The landed Stage-2 body of `theorem1From13_firstTwoStages`
  (`Theorem1CostFrom13Bind.lean`) is reused verbatim at the padded endpoint,
  with selector coefficient 8, which needs only `8 < n`.
* **Joint tail.**  `theorem1From13_tailJointSelection_of_l18FirstHit` uses its
  hypothesis `13 ≤ n` only to get `4 + 1 + 1 < n`; it is copied here as
  `theorem1FromCPB_tailJointSelection_of_coeff` with that true premise, and fed
  the proved L18 first-hit bound `theorem1L18FirstHitPhaseBound_proved`.
* **Semantic prefix.**  `theorem1From13_tailSemanticPrefix_of_jointGood` turns
  the jointly good suffix into an `SPL` endpoint of a prefix, which is then
  converted into a prefix hit of `theorem1ReachesSPL`.

The corollary combines the result with an arbitrary-start → CPB reachability
hypothesis to obtain pointwise possible convergence for `9 ≤ n ≤ 12`, the
cases left open by the From13 producer.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail
open PPLLResearchFormulation
open PPLLTraceConvergence
open PPLLSchedulerBlocks
open PPLLClosedDomainSchedulerAmplificationSol

/-! ## From an SPL endpoint to a prefix hit -/

/-- An `SPL` endpoint of the explicit local run is a prefix hit of
`theorem1ReachesSPL` (the run's last configuration is one of the tested
prefixes). -/
theorem theorem1ReachesSPL_of_runLocalEndpoint
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hend :
      SPL ring
        (runLocalSchedule
          ring
          (PPL.protocol psi kappa).transition
          C word)) :
    theorem1ReachesSPL ring C word = true := by
  induction word generalizing C with
  | nil =>
      simpa [theorem1ReachesSPL, runLocalSchedule] using hend
  | cons e rest ih =>
      have htail :=
        ih
          (C :=
            PopulationProtocol.step
              (PPL.protocol psi kappa) ring C e)
          (by
            simpa
              [runLocalSchedule,
                localStep_eq_protocol_step]
              using hend)
      simp [theorem1ReachesSPL, htail]

/-- Prefix hits compose with a leading run: if some prefix of `b` hits `SPL`
from `runPPL ring C a`, then some prefix of `a ++ b` hits `SPL` from `C`. -/
theorem theorem1ReachesSPL_append_of_run
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (a b : DetSchedule n)
    (hb :
      theorem1ReachesSPL ring
        (PPL.Probability.runPPL ring C a) b = true) :
    theorem1ReachesSPL ring C (a ++ b) = true := by
  induction a generalizing C with
  | nil =>
      simpa
        [PPL.Probability.runPPL,
          PPL.Probability.runPopulationSchedule]
        using hb
  | cons e rest ih =>
      have htail :=
        ih
          (C :=
            PopulationProtocol.step
              (PPL.protocol psi kappa) ring C e)
          (by
            simpa
              [PPL.Probability.runPPL,
                PPL.Probability.runPopulationSchedule]
              using hb)
      simp [theorem1ReachesSPL, htail]

end PPL

#print axioms PPL.theorem1ReachesSPL_of_runLocalEndpoint
#print axioms PPL.theorem1ReachesSPL_append_of_run
