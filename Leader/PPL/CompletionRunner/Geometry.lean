import Leader.PPL.CompletionRunner.Interface
import Init.Omega

/-!
# Step-parametric Lemma 4: block geometry and the power-layer targets

Generic restatements, over a `Lemma4Runner`, of

* the one-block two-sweep service geometry (`Lemma4TwoSweepServiceGeometry`)
  and its corrected rank-geometry package
  (`Lemma4TwoSweepRankGeometryCorrected`), with the stage-bound clause
  discharged by the runner-independent `lemma4TwoSweepStageBounds_sound`;
* the two block-power induction targets and the covered half-power dynamics
  of `TokenCorrectnessLemma4CoreRoute` / `TokenCorrectnessLemma4Dynamics`;
* the deterministic core `lemma4_deterministic_core`, and its reduction to
  the covered half-power dynamics.

As in `Runner.lean`, every statement is the ordinary one with `ghostRun`,
`ghostStep`, `CdTrace` replaced by `R.run`, `R.gstep`, `R.cdTrace`, and the
ordinary step-property Props replaced by their generic versions.  The service
geometry is kept curried over the five step properties exactly as in the
ordinary development.  Nothing in this file is protocol-specific.
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## 1. One-block service geometry -/

/--
Generic `Lemma4TwoSweepServiceGeometry`: one complete block
`H = seqR ++ seqL`, occurring as a sublist of an arbitrary schedule along a
`C_d` trace of the runner, services every surviving relevant owner through one
macro-stage:

* a nonfresh in-window owner is deleted or has a same-ID nonfresh valid
  in-window survivor with strictly larger stage;
* a fresh rightmost owner completes, or survives as fresh rightmost owner with
  strictly larger stage while the window stays covered-fresh;
* an empty covered-fresh window yields a completion or a fresh rightmost
  frontier past the first stage.

This is the only block-level hypothesis of the generic power layer; it is not
proved here.
-/
def ServiceGeometry (R : Lemma4Runner) : Prop :=
  forall
    (hcov : CoverageStep R)
    (hrows : SweepMissingRows R)
    (hright : RightmostProgressStep R)
    (hold : OldOwnerProgressStep R)
    (hpersist : FreshLineagePersistenceStep R),
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind),
    And
      (forall
          (C0 : Config n psi kappa)
          (pre : DetSchedule n)
          (G : GhostConfig n psi kappa)
          (schedule : DetSchedule n)
          (i : Fin n)
          (z : GhostToken n psi),
        G =
            R.run hpsi ring 0
              (initialGhost C0) pre ->
        R.cdTrace hpsi ring k kind G.phys schedule ->
        (lemma4Block ring k psi).Sublist schedule ->
        Lemma4GhostCoveredWindow ring k kind G ->
        Lemma4InWindow ring k psi i ->
        ghostTokenAt kind G i = some z ->
        ValidToken kind G.phys i ->
        Not (FreshAt kind k z.lmeta) ->
        let G' :=
          R.run hpsi ring pre.length G schedule
        Or
          (forall
              (j : Fin n)
              (z' : GhostToken n psi),
            ghostTokenAt kind G' j = some z' ->
            z'.lmeta.id ≠ z.lmeta.id)
          (exists j : Fin n,
            exists z' : GhostToken n psi,
              And
                (Lemma4InWindow ring k psi j)
                (And
                  (ghostTokenAt kind G' j = some z')
                  (And
                    (z'.lmeta.id = z.lmeta.id)
                    (And
                      (Not (FreshAt kind k z'.lmeta))
                      (And
                        (ValidToken kind G'.phys j)
                        (lemma4TokenStage
                            kind (G.phys i) z.value <
                          lemma4TokenStage
                            kind (G'.phys j) z'.value)))))))
      (And
        (forall
            (C0 : Config n psi kappa)
            (pre : DetSchedule n)
            (G : GhostConfig n psi kappa)
            (schedule : DetSchedule n)
            (x : Fin (2 * psi))
            (z : GhostToken n psi),
          G =
              R.run hpsi ring 0
                (initialGhost C0) pre ->
          Lemma4CoveredFreshWindow ring k kind G ->
          R.cdTrace hpsi ring k kind G.phys schedule ->
          (lemma4Block ring k psi).Sublist schedule ->
          Lemma4RightmostAt ring k kind G x z ->
          FreshAt kind k z.lmeta ->
          let i := shiftRight ring k x.val
          let G' :=
            R.run hpsi ring pre.length G schedule
          Or
            (HasFreshCompletion kind k G')
            (And
              (Lemma4CoveredFreshWindow
                ring k kind G')
              (exists y : Fin (2 * psi),
                exists z' : GhostToken n psi,
                  And
                    (Lemma4RightmostAt
                      ring k kind G' y z')
                    (And
                      (z'.lmeta.id = z.lmeta.id)
                      (And
                        (FreshAt kind k z'.lmeta)
                        (lemma4TokenStage
                            kind (G.phys i) z.value <
                          lemma4TokenStage
                            kind
                            (G'.phys
                              (shiftRight ring k y.val))
                            z'.value))))))
        (forall
            (C0 : Config n psi kappa)
            (pre : DetSchedule n)
            (G : GhostConfig n psi kappa)
            (schedule : DetSchedule n),
          G =
              R.run hpsi ring 0
                (initialGhost C0) pre ->
          Lemma4CoveredFreshWindow ring k kind G ->
          Lemma4WindowEmpty ring k kind G ->
          R.cdTrace hpsi ring k kind G.phys schedule ->
          (lemma4Block ring k psi).Sublist schedule ->
          let G' :=
            R.run hpsi ring pre.length G schedule
          Or
            (HasFreshCompletion kind k G')
            (And
              (Lemma4CoveredFreshWindow
                ring k kind G')
              (exists y : Fin (2 * psi),
                exists z' : GhostToken n psi,
                  And
                    (Lemma4RightmostAt
                      ring k kind G' y z')
                    (And
                      (FreshAt kind k z'.lmeta)
                      (psi <
                        lemma4TokenStage
                          kind
                          (G'.phys
                            (shiftRight ring k y.val))
                          z'.value))))))

/-! ## 2. Corrected rank geometry -/

/--
Generic `Lemma4TwoSweepRankGeometryCorrected`: the stage bound
`psi ≤ stage < 2*psi` for sound owners under `C_d`, followed by the three
service-geometry clauses.
-/
def RankGeometryCorrected (R : Lemma4Runner) : Prop :=
  forall
    (hcov : CoverageStep R)
    (hrows : SweepMissingRows R)
    (hright : RightmostProgressStep R)
    (hold : OldOwnerProgressStep R)
    (hpersist : FreshLineagePersistenceStep R),
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind),
    And
      (forall
          (G : GhostConfig n psi kappa)
          (i : Fin n)
          (z : GhostToken n psi),
        GhostSound G ->
        Cd ring k kind G.phys ->
        Lemma4InWindow ring k psi i ->
        ghostTokenAt kind G i = some z ->
        ValidToken kind G.phys i ->
        And
          (psi <=
            lemma4TokenStage
              kind (G.phys i) z.value)
          (lemma4TokenStage
              kind (G.phys i) z.value <
            2 * psi))
      (And
        (forall
            (C0 : Config n psi kappa)
            (pre : DetSchedule n)
            (G : GhostConfig n psi kappa)
            (schedule : DetSchedule n)
            (i : Fin n)
            (z : GhostToken n psi),
          G =
              R.run hpsi ring 0
                (initialGhost C0) pre ->
          R.cdTrace hpsi ring k kind G.phys schedule ->
          (lemma4Block ring k psi).Sublist schedule ->
          Lemma4GhostCoveredWindow ring k kind G ->
          Lemma4InWindow ring k psi i ->
          ghostTokenAt kind G i = some z ->
          ValidToken kind G.phys i ->
          Not (FreshAt kind k z.lmeta) ->
          let G' :=
            R.run hpsi ring pre.length G schedule
          Or
            (forall
                (j : Fin n)
                (z' : GhostToken n psi),
              ghostTokenAt kind G' j = some z' ->
              z'.lmeta.id ≠ z.lmeta.id)
            (exists j : Fin n,
              exists z' : GhostToken n psi,
                And
                  (Lemma4InWindow ring k psi j)
                  (And
                    (ghostTokenAt kind G' j = some z')
                    (And
                      (z'.lmeta.id = z.lmeta.id)
                      (And
                        (Not (FreshAt kind k z'.lmeta))
                        (And
                          (ValidToken kind G'.phys j)
                          (lemma4TokenStage
                              kind (G.phys i) z.value <
                            lemma4TokenStage
                              kind (G'.phys j) z'.value)))))))
        (And
          (forall
              (C0 : Config n psi kappa)
              (pre : DetSchedule n)
              (G : GhostConfig n psi kappa)
              (schedule : DetSchedule n)
              (x : Fin (2 * psi))
              (z : GhostToken n psi),
            G =
                R.run hpsi ring 0
                  (initialGhost C0) pre ->
            Lemma4CoveredFreshWindow ring k kind G ->
            R.cdTrace hpsi ring k kind G.phys schedule ->
            (lemma4Block ring k psi).Sublist schedule ->
            Lemma4RightmostAt ring k kind G x z ->
            FreshAt kind k z.lmeta ->
            let i := shiftRight ring k x.val
            let G' :=
              R.run hpsi ring pre.length G schedule
            Or
              (HasFreshCompletion kind k G')
              (And
                (Lemma4CoveredFreshWindow
                  ring k kind G')
                (exists y : Fin (2 * psi),
                  exists z' : GhostToken n psi,
                    And
                      (Lemma4RightmostAt
                        ring k kind G' y z')
                      (And
                        (z'.lmeta.id = z.lmeta.id)
                        (And
                          (FreshAt kind k z'.lmeta)
                          (lemma4TokenStage
                              kind
                              (G.phys
                                (shiftRight ring k x.val))
                              z.value <
                            lemma4TokenStage
                              kind
                              (G'.phys
                                (shiftRight ring k y.val))
                              z'.value))))))
          (forall
              (C0 : Config n psi kappa)
              (pre : DetSchedule n)
              (G : GhostConfig n psi kappa)
              (schedule : DetSchedule n),
            G =
                R.run hpsi ring 0
                  (initialGhost C0) pre ->
            Lemma4CoveredFreshWindow ring k kind G ->
            Lemma4WindowEmpty ring k kind G ->
            R.cdTrace hpsi ring k kind G.phys schedule ->
            (lemma4Block ring k psi).Sublist schedule ->
            let G' :=
              R.run hpsi ring pre.length G schedule
            Or
              (HasFreshCompletion kind k G')
              (And
                (Lemma4CoveredFreshWindow
                  ring k kind G')
                (exists y : Fin (2 * psi),
                  exists z' : GhostToken n psi,
                    And
                      (Lemma4RightmostAt
                        ring k kind G' y z')
                      (And
                        (FreshAt kind k z'.lmeta)
                        (psi <
                          lemma4TokenStage
                            kind
                            (G'.phys
                              (shiftRight ring k y.val))
                            z'.value)))))))

/--
The stage-bound clause is runner-independent (`lemma4TwoSweepStageBounds_sound`
reads only the ghost state), so the corrected rank geometry follows from the
service geometry for every runner.
-/
theorem rankGeometryCorrected_of_serviceGeometry
    (R : Lemma4Runner)
    (hservice : ServiceGeometry R) :
    RankGeometryCorrected R := by
  unfold RankGeometryCorrected
  intro hcov hrows hright hold hpersist
  intro n psi kappa hpsi ring k kind
  have hgeom :=
    hservice
      hcov hrows hright hold hpersist
      (n := n) (psi := psi) (kappa := kappa)
      hpsi ring k kind
  refine And.intro ?_ hgeom
  intro G i z
  intro hsound hCd hwin howner hvalid
  exact
    lemma4TwoSweepStageBounds_sound
      hpsi ring k kind G i z
      hsound hCd hwin howner hvalid

/-! ## 3. The two block-power targets -/

/--
Generic `Lemma4HalfPowerFirstPowerInduction` (first-half purge): along a `C_d`
trace containing `H^psi` as a sublist, the runner ends in a covered-fresh
window, i.e. every live in-window owner is a birth at `k` and every valid
in-window token is owned.
-/
def HalfPowerFirstPowerInduction (R : Lemma4Runner) : Prop :=
  ∀
    (hgeom : RankGeometryCorrected R)
    (hcov : CoverageStep R)
    (hrows : SweepMissingRows R)
    (hright : RightmostProgressStep R)
    (hold : OldOwnerProgressStep R)
    (hpersist : FreshLineagePersistenceStep R),
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (schedule : DetSchedule n),
    R.cdTrace hpsi ring k kind C schedule →
    (lemma4HalfWord ring k psi).Sublist schedule →
    Lemma4CoveredFreshWindow ring k kind
      (R.run hpsi ring 0
        (initialGhost C) schedule)

/--
Generic `Lemma4HalfPowerSecondPowerInduction` (protected frontier): from an
actual run state with a covered-fresh window, another `H^psi` along a `C_d`
trace logs a fresh completion born at `k`.
-/
def HalfPowerSecondPowerInduction (R : Lemma4Runner) : Prop :=
  ∀
    (hgeom : RankGeometryCorrected R)
    (hcov : CoverageStep R)
    (hrows : SweepMissingRows R)
    (hright : RightmostProgressStep R)
    (hold : OldOwnerProgressStep R)
    (hpersist : FreshLineagePersistenceStep R),
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
        R.run hpsi ring 0
          (initialGhost C0) pre →
    Lemma4CoveredFreshWindow ring k kind G →
    R.cdTrace hpsi ring k kind G.phys schedule →
    (lemma4HalfWord ring k psi).Sublist schedule →
    HasFreshCompletion kind k
      (R.run hpsi ring pre.length G schedule)

/-! ## 4. Half-power dynamics and the deterministic core -/

/-- Generic `Lemma4HalfPowerDynamicsCovered`: both half-word clauses. -/
def HalfPowerDynamicsCovered (R : Lemma4Runner) : Prop :=
  ∀ {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind),
    (∀ (C : Config n psi kappa)
       (schedule : DetSchedule n),
      R.cdTrace hpsi ring k kind C schedule ->
      (lemma4HalfWord ring k psi).Sublist schedule ->
      Lemma4CoveredFreshWindow ring k kind
        (R.run hpsi ring 0 (initialGhost C) schedule)) ∧
    (∀ (C0 : Config n psi kappa)
       (pre : DetSchedule n)
       (G : GhostConfig n psi kappa)
       (schedule : DetSchedule n),
      G = R.run hpsi ring 0 (initialGhost C0) pre ->
      Lemma4CoveredFreshWindow ring k kind G ->
      R.cdTrace hpsi ring k kind G.phys schedule ->
      (lemma4HalfWord ring k psi).Sublist schedule ->
      HasFreshCompletion kind k
        (R.run hpsi ring pre.length G schedule))

/--
Generic Lemma-4 deterministic core (source Lemma 4, deterministic part): if
`C_d` holds along the runner's physical trajectory and the schedule contains
the word `H^(2 psi)` as a subsequence, then the ghost run logs a fresh
completion of a lineage born at `k`.  For the ordinary runner this is
definitionally `lemma4_deterministic_core`.
-/
def DeterministicCore (R : Lemma4Runner) : Prop :=
  ∀ {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C : Config n psi kappa) (schedule : DetSchedule n)
    (_hCd : R.cdTrace hpsi ring k kind C schedule)
    (_hsub : (lemma4Word ring k psi).Sublist schedule),
    HasFreshCompletion kind k
      (R.run hpsi ring 0 (initialGhost C) schedule)

/--
Two-half assembly (generic `lemma4_deterministic_core_of_coveredHalfPowerDynamics`):
split `H^(2 psi) = H^psi ++ H^psi` inside the schedule, split the `C_d`
trace accordingly, apply the first clause to the prefix and the second clause
from the midpoint, and rejoin the runs.
-/
theorem deterministicCore_of_coveredHalfPowerDynamics
    (R : Lemma4Runner)
    (hdyn : HalfPowerDynamicsCovered R) :
    DeterministicCore R := by
  intro n psi kappa hpsi ring k kind C schedule hCd hsub
  have hword :
      lemma4Word ring k psi =
        lemma4HalfWord ring k psi ++
          lemma4HalfWord ring k psi :=
    lemma4Word_eq_two_halves ring k
  rw [hword] at hsub
  rcases List.append_sublist_iff.mp hsub with
    ⟨pre, post, hschedule, hpre, hpost⟩
  subst schedule
  rcases
    R.cdTrace_append hpsi ring k kind C pre post hCd
    with ⟨hCdPre, hCdPost⟩
  let Gmid : GhostConfig n psi kappa :=
    R.run hpsi ring 0 (initialGhost C) pre
  have hFreshCovered :
      Lemma4CoveredFreshWindow ring k kind Gmid :=
    (hdyn hpsi ring k kind).1 C pre hCdPre hpre
  have hmidPhys :
      Gmid.phys = R.physRun hpsi ring C pre :=
    R.run_phys hpsi ring 0 (initialGhost C) pre
  have hCdPost' :
      R.cdTrace hpsi ring k kind Gmid.phys post := by
    rw [hmidPhys]
    exact hCdPost
  have hfinish :
      HasFreshCompletion kind k
        (R.run hpsi ring pre.length Gmid post) :=
    (hdyn hpsi ring k kind).2
      C pre Gmid post rfl
      hFreshCovered hCdPost' hpost
  rw [R.run_append hpsi ring 0 (initialGhost C) pre post]
  simpa [Gmid] using hfinish

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.rankGeometryCorrected_of_serviceGeometry
#print axioms PPL.Lemma4Generic.deterministicCore_of_coveredHalfPowerDynamics
