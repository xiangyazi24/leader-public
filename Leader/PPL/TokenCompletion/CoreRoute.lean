import Leader.PPL.TokenCompletion.StepPropsClosed
import Leader.PPL.TokenCompletion.SweepOldOwnerRows
import Leader.PPL.TokenCompletion.TwoSweep

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
The only still-open one-interaction part of the unmasked old-owner step.

Truth argument: the off-pair/frame case is already proved.  On the selected
pair, collision/deletion gives the disappearance arm; otherwise the literal
c = 1, c >= 2, c = -1 and c <= -2 moves preserve the lineage ID, validity and
nonfreshness, never decrease canonical progress, and add exactly one on the
unique service edge.  These are precisely the initiator/responder rows below.
-/
def Lemma4CoreRouteOldOwnerInteractedRows : Prop :=
  Lemma4SweepOldOwnerInitiatorRow ∧
    Lemma4SweepOldOwnerResponderRow

/--
One complete H = seqR ++ seqL services a surviving relevant owner through
one macro-stage, with the fresh-frontier and empty-window variants.

Truth argument: all protocol semantics needed per service letter are already
provided by CoverageStep, SweepMissingRows, RightmostProgressStep,
OldOwnerProgressStep and FreshLineagePersistenceStep.  What remains is the
deterministic order of service edges: positive legs occur in the clockwise
sweep; after the turn, negative legs occur later in the counterclockwise sweep
in reverse spatial order.  The stage-bound defect is irrelevant here because this
Prop is the service-order clause, not the false arbitrary-G stage bound.
-/
def Lemma4CoreRouteServiceGeometry : Prop :=
  Lemma4TwoSweepServiceGeometry

/--
Pure first-half block-power induction.

Truth argument: on actual ghostRun states GhostSound gives
  psi <= stage < 2*psi.
For every nonfresh inherited owner, one complete block deletes it or strictly
raises stage.  Thus an owner surviving psi complete blocks would have stage at
least 2*psi, impossible.  Fresh owners are not part of the purge: the proved
unmasked persistence row keeps their FreshAt provenance through skipped and
selected letters, while CoverageStep preserves physical/ghost coverage.
Therefore the half word ends in CoveredFreshWindow.

No literal ghostStep branch fact belongs in this Prop; hgeom is the complete
one-block endpoint package.
-/
def Lemma4HalfPowerFirstPowerInduction : Prop :=
  ∀
    (hgeom : Lemma4TwoSweepRankGeometryCorrected)
    (hcov : Lemma4CoverageStep)
    (hrows : Lemma4SweepMissingRows)
    (hright : Lemma4RightmostProgressStep)
    (hold : Lemma4SweepOldOwnerProgressStep)
    (hpersist : Lemma4SweepFreshLineagePersistenceStep),
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (schedule : DetSchedule n),
    CdTrace hpsi ring k kind C schedule →
    (lemma4HalfWord ring k psi).Sublist schedule →
    Lemma4CoveredFreshWindow ring k kind
      (ghostRun hpsi ring 0
        (initialGhost C) schedule)

/--
Pure second-half block-power induction.

Truth argument: CoveredFreshWindow makes every live in-window owner fresh and
CoverageStep excludes valid unowned blockers.  If the window is empty, the
empty-window block clause creates a fresh rightmost frontier past the first
stage (or already completes).  Otherwise choose the finite rightmost fresh
owner.  Every subsequent no-completion block preserves coveredness and strictly
raises its stage.  The sound bound stage < 2*psi makes psi such blocks
impossible without a completion.  If completion happens early, completed is
So later skipped letters cannot erase the witness.

Again this is list/wordPower induction only, with no new protocol branch row.
-/
def Lemma4HalfPowerSecondPowerInduction : Prop :=
  ∀
    (hgeom : Lemma4TwoSweepRankGeometryCorrected)
    (hcov : Lemma4CoverageStep)
    (hrows : Lemma4SweepMissingRows)
    (hright : Lemma4RightmostProgressStep)
    (hold : Lemma4SweepOldOwnerProgressStep)
    (hpersist : Lemma4SweepFreshLineagePersistenceStep),
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (schedule : DetSchedule n),
    G =
        ghostRun hpsi ring 0
          (initialGhost C0) pre →
    Lemma4CoveredFreshWindow ring k kind G →
    CdTrace hpsi ring k kind G.phys schedule →
    (lemma4HalfWord ring k psi).Sublist schedule →
    HasFreshCompletion kind k
      (ghostRun hpsi ring pre.length G schedule)

/--
Current deterministic-core route with every already-proved asset discharged.

The only hypotheses are the two interacted old-owner rows (bundled as one
named Prop), one-block service geometry, and the two pure block-power
inductions.
-/
theorem
    lemma4HalfPowerDynamicsCovered_of_oldRows_service_firstPower_secondPower
    (holdRows : Lemma4CoreRouteOldOwnerInteractedRows)
    (hservice : Lemma4CoreRouteServiceGeometry)
    (hfirst : Lemma4HalfPowerFirstPowerInduction)
    (hsecond : Lemma4HalfPowerSecondPowerInduction) :
    Lemma4HalfPowerDynamicsCovered := by
  unfold Lemma4CoreRouteOldOwnerInteractedRows at holdRows
  unfold Lemma4CoreRouteServiceGeometry at hservice
  unfold Lemma4HalfPowerFirstPowerInduction at hfirst
  unfold Lemma4HalfPowerSecondPowerInduction at hsecond

  have hcov : Lemma4CoverageStep :=
    lemma4StepProps_proved.1

  have hright : Lemma4RightmostProgressStep :=
    lemma4StepProps_proved.2.1

  have hrows : Lemma4SweepMissingRows :=
    lemma4StepProps_proved.2.2

  have hpersist :
      Lemma4SweepFreshLineagePersistenceStep :=
    lemma4SweepFreshLineagePersistenceStep_proved

  have hold :
      Lemma4SweepOldOwnerProgressStep :=
    lemma4SweepOldOwnerProgressStep_of_interacted_rows
      holdRows.1 holdRows.2

  have hgeom :
      Lemma4TwoSweepRankGeometryCorrected :=
    lemma4TwoSweepRankGeometryCorrected_of_serviceGeometry
      hservice

  unfold Lemma4HalfPowerDynamicsCovered
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
Immediate deterministic-core corollary through the sole existing producer.
-/
theorem
    lemma4_deterministic_core_of_oldRows_service_firstPower_secondPower
    (holdRows : Lemma4CoreRouteOldOwnerInteractedRows)
    (hservice : Lemma4CoreRouteServiceGeometry)
    (hfirst : Lemma4HalfPowerFirstPowerInduction)
    (hsecond : Lemma4HalfPowerSecondPowerInduction) :
    lemma4_deterministic_core := by
  exact
    lemma4_deterministic_core_of_coveredHalfPowerDynamics
      (lemma4HalfPowerDynamicsCovered_of_oldRows_service_firstPower_secondPower
        holdRows hservice hfirst hsecond)

end PPL

#print axioms PPL.lemma4HalfPowerDynamicsCovered_of_oldRows_service_firstPower_secondPower
#print axioms PPL.lemma4_deterministic_core_of_oldRows_service_firstPower_secondPower
