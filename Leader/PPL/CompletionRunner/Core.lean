import Leader.PPL.CompletionRunner.Backstep
import Leader.PPL.CompletionRunner.SecondPowerStart

/-!
# Step-parametric Lemma 4: deterministic core

Generic version of `TokenCorrectnessLemma4CoreRoute.lean` together with the
closed power inductions.  The headline `deterministicCore_of_steps` derives
the Lemma-4 deterministic core for an arbitrary runner from exactly:

* `RunSound R` and `IdsUniqueStep R` (run facts about the ghost refinement);
* the five named one-interaction properties `CoverageStep R`,
  `SweepMissingRows R`, `RightmostProgressStep R`, `OldOwnerProgressStep R`,
  `FreshLineagePersistenceStep R`;
* the one-block service geometry `ServiceGeometry R`.

No protocol branch is inspected: all Algorithm-2/3 semantics enters through
these hypotheses.  For the ordinary runner every hypothesis has an existing
producer (see `OrdinaryInstance.lean`); for the P_PL-prime runner they are the
remaining obligations of board row 18.3.
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Generic `lemma4HalfPowerDynamicsCovered_of_oldRows_service_firstPower_secondPower`:
the covered half-power dynamics from the step properties, the service
geometry and the two block-power inductions.
-/
theorem halfPowerDynamicsCovered_of_service_firstPower_secondPower
    (R : Lemma4Runner)
    (hcov : CoverageStep R)
    (hrows : SweepMissingRows R)
    (hright : RightmostProgressStep R)
    (hold : OldOwnerProgressStep R)
    (hpersist : FreshLineagePersistenceStep R)
    (hservice : ServiceGeometry R)
    (hfirst : HalfPowerFirstPowerInduction R)
    (hsecond : HalfPowerSecondPowerInduction R) :
    HalfPowerDynamicsCovered R := by
  have hgeom : RankGeometryCorrected R :=
    rankGeometryCorrected_of_serviceGeometry R hservice
  intro n psi kappa hpsi ring k kind
  constructor
  · intro C schedule hCd hsub
    exact
      hfirst
        hgeom hcov hrows hright hold hpersist
        (n := n) (psi := psi) (kappa := kappa)
        hpsi ring k kind C schedule
        hCd hsub
  · intro C0 pre G schedule
    intro hrun hcovered hCd hsub
    exact
      hsecond
        hgeom hcov hrows hright hold hpersist
        (n := n) (psi := psi) (kappa := kappa)
        hpsi ring k kind
        C0 pre G schedule
        hrun hcovered hCd hsub

/--
**Step-parametric Lemma 4 (deterministic core).**

For any runner, if its ghost runs are sound and keep lineage IDs unique, and
it satisfies the five one-interaction properties and the one-block service
geometry, then along every `C_d` trace of its physical step whose schedule
contains `H^(2 psi)` as a subsequence the ghost run logs a fresh completion
born at `k`.

Proof: the first- and second-power block inductions are closed for every
runner (`halfPowerFirstPowerInduction_proved`,
`halfPowerSecondPowerInduction_proved`), giving the covered half-power
dynamics, and the two-half assembly gives the core.
-/
theorem deterministicCore_of_steps
    (R : Lemma4Runner)
    (hsound : RunSound R)
    (huniq : IdsUniqueStep R)
    (hcov : CoverageStep R)
    (hrows : SweepMissingRows R)
    (hright : RightmostProgressStep R)
    (hold : OldOwnerProgressStep R)
    (hpersist : FreshLineagePersistenceStep R)
    (hservice : ServiceGeometry R) :
    DeterministicCore R :=
  deterministicCore_of_coveredHalfPowerDynamics R
    (halfPowerDynamicsCovered_of_service_firstPower_secondPower R
      hcov hrows hright hold hpersist hservice
      (halfPowerFirstPowerInduction_proved R hsound huniq)
      (halfPowerSecondPowerInduction_proved R hsound))

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.halfPowerDynamicsCovered_of_service_firstPower_secondPower
#print axioms PPL.Lemma4Generic.deterministicCore_of_steps
