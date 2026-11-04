import Leader.PPL.TokenCompletion.CoreRoute
import Leader.PPL.TokenCompletion.CoverageLeaves
import Init.Omega

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
One-block bootstrap for the second half.

Truth argument.

If the covered-fresh input window is empty, the empty-window field of
`Lemma4TwoSweepRankGeometryCorrected` gives exactly this conclusion.

If it is nonempty, choose the greatest occupied coordinate
`x : Fin (2 * psi)`.  Because the state is a canonical ghostRun prefix,
`lemma4CoverageGhostRunSound_proved` gives GhostSound, so the owner is a
valid physical token.  Covered freshness makes it FreshAt kind k, and
greatest-coordinate selection makes it Lemma4RightmostAt.  The corrected
stage bound gives `psi <= stage`.  Applying the fresh-rightmost block field
then gives either a fresh completion or a same-lineage rightmost fresh
survivor with strictly larger stage, hence `psi < stage'`.

The block field already quantifies an arbitrary schedule containing
`lemma4Block` only as a Sublist, so all interleaved extra scheduler letters
are included.
-/
def Lemma4SecondPowerCoveredBlockStart : Prop :=
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
    (lemma4Block ring k psi).Sublist schedule →
    let G' :=
      ghostRun hpsi ring pre.length G schedule
    HasFreshCompletion kind k G' ∨
      (Lemma4CoveredFreshWindow ring k kind G' ∧
        ∃ (y : Fin (2 * psi))
          (z' : GhostToken n psi),
          Lemma4RightmostAt
              ring k kind G' y z' ∧
            FreshAt kind k z'.lmeta ∧
            psi <
              lemma4TokenStage
                kind
                (G'.phys
                  (shiftRight ring k y.val))
                z'.value)

private def secondPowerFrontierAt
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (lower : Nat)
    (G : GhostConfig n psi kappa) : Prop :=
  Lemma4CoveredFreshWindow ring k kind G ∧
    ∃ (x : Fin (2 * psi))
      (z : GhostToken n psi),
      Lemma4RightmostAt ring k kind G x z ∧
        FreshAt kind k z.lmeta ∧
        lower ≤
          lemma4TokenStage
            kind
            (G.phys
              (shiftRight ring k x.val))
            z.value

/--
Completion log for one literal ghost step.
-/
private theorem secondPowerHasFreshCompletion_step
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (k : Fin n)
    (h : HasFreshCompletion kind k G) :
    HasFreshCompletion kind k
      (ghostStep hpsi ring step G e) := by
  unfold HasFreshCompletion at h ⊢
  rcases h with ⟨m, hm, hfresh⟩
  refine ⟨m, ?_, hfresh⟩
  simp only [ghostStep, List.mem_append]
  exact Or.inl (Or.inl hm)

/--
Completion log through an arbitrary suffix.
-/
private theorem secondPowerHasFreshCompletion_run
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (kind : TokenKind)
    (k : Fin n) :
    ∀ (t : Nat)
      (G : GhostConfig n psi kappa)
      (schedule : DetSchedule n),
      HasFreshCompletion kind k G →
      HasFreshCompletion kind k
        (ghostRun hpsi ring t G schedule) := by
  intro t G schedule hdone
  induction schedule generalizing t G with
  | nil =>
      exact hdone
  | cons e es ih =>
      simp only [ghostRun]
      exact
        ih
          (t := t + 1)
          (G := ghostStep hpsi ring t G e)
          (secondPowerHasFreshCompletion_step
            hpsi ring t G e kind k hdone)

/--
Endpoint C_d extracted from CdTrace.
-/
private theorem secondPowerCdTraceEnd
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind) :
    ∀ (C : Config n psi kappa)
      (schedule : DetSchedule n),
      CdTrace hpsi ring k kind C schedule →
      Cd ring k kind
        (PPL.Probability.runPopulationSchedule
          (protocol psi kappa) ring C schedule) := by
  intro C schedule
  induction schedule generalizing C with
  | nil =>
      intro hCd
      simpa
        [CdTrace,
          PPL.Probability.runPopulationSchedule]
        using hCd
  | cons e es ih =>
      intro hCd
      change
        Cd ring k kind C ∧
          CdTrace hpsi ring k kind
            (PopulationProtocol.step
              (protocol psi kappa) ring C e) es
        at hCd
      simpa [PPL.Probability.runPopulationSchedule]
        using
          ih
            (PopulationProtocol.step
              (protocol psi kappa) ring C e)
            hCd.2

/--
One further complete block strictly raises the tracked rightmost frontier,
unless a fresh completion has already been logged.

No reverse ancestry is needed: the fresh-frontier component of corrected
rank geometry returns a same-lineage rightmost fresh endpoint owner directly.
-/
private theorem secondPowerFrontierOneBlock
    (hgeom : Lemma4TwoSweepRankGeometryCorrected)
    (hcov : Lemma4CoverageStep)
    (hrows : Lemma4SweepMissingRows)
    (hright : Lemma4RightmostProgressStep)
    (hold : Lemma4SweepOldOwnerProgressStep)
    (hpersist : Lemma4SweepFreshLineagePersistenceStep)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (schedule : DetSchedule n)
    (lower : Nat)
    (hrun :
      G =
        ghostRun hpsi ring 0
          (initialGhost C0) pre)
    (hCd :
      CdTrace hpsi ring k kind
        G.phys schedule)
    (hsub :
      (lemma4Block ring k psi).Sublist
        schedule)
    (hfront :
      secondPowerFrontierAt
        ring k kind lower G) :
    let G' :=
      ghostRun hpsi ring pre.length G schedule
    HasFreshCompletion kind k G' ∨
      secondPowerFrontierAt
        ring k kind (lower + 1) G' := by
  have hgeom' : Lemma4TwoSweepRankGeometryCorrected :=
    hgeom
  unfold Lemma4TwoSweepRankGeometryCorrected at hgeom'

  have hg :=
    hgeom'
      hcov hrows hright hold hpersist
      (n := n) (psi := psi) (kappa := kappa)
      hpsi ring k kind

  rcases hfront with
    ⟨hcovered, x, z,
      hright0, hfresh0, hlo⟩

  have hs :=
    hg.2.2.1
      C0 pre G schedule x z
      hrun hcovered hCd hsub
      hright0 hfresh0
  dsimp only at hs

  rcases hs with hdone | hkeep
  · exact Or.inl hdone

  · rcases hkeep with
      ⟨hcovered', y, z',
        hright', _hid, hfresh', hlt⟩
    exact
      Or.inr
        ⟨hcovered', y, z',
          hright', hfresh', by omega⟩

/--
Power induction after the bootstrap block.

For r=1 the bootstrap row creates stage > psi, i.e. stage >= psi+1.
For the inductive step, split off the final required block.  The induction
hypothesis handles every earlier required block and all extra letters assigned
to that prefix; the final block theorem absorbs the remaining block together
with all trailing extra letters.

If a completion appears in the prefix, append-only completed history carries
it through the final suffix.
-/
private theorem secondPowerFrontierWordPower
    (hstart : Lemma4SecondPowerCoveredBlockStart)
    (hgeom : Lemma4TwoSweepRankGeometryCorrected)
    (hcov : Lemma4CoverageStep)
    (hrows : Lemma4SweepMissingRows)
    (hright : Lemma4RightmostProgressStep)
    (hold : Lemma4SweepOldOwnerProgressStep)
    (hpersist : Lemma4SweepFreshLineagePersistenceStep)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa) :
    ∀ (r : Nat)
      (pre : DetSchedule n)
      (G : GhostConfig n psi kappa)
      (schedule : DetSchedule n),
      0 < r →
      G =
          ghostRun hpsi ring 0
            (initialGhost C0) pre →
      Lemma4CoveredFreshWindow ring k kind G →
      CdTrace hpsi ring k kind G.phys schedule →
      (wordPower r
        (lemma4Block ring k psi)).Sublist schedule →
      let G' :=
        ghostRun hpsi ring pre.length G schedule
      HasFreshCompletion kind k G' ∨
        secondPowerFrontierAt
          ring k kind (psi + r) G' := by
  have hstart' : Lemma4SecondPowerCoveredBlockStart :=
    hstart
  unfold Lemma4SecondPowerCoveredBlockStart at hstart'

  intro r
  induction r with
  | zero =>
      intro pre G schedule hr
      omega

  | succ r ih =>
      intro pre G schedule _hr
      intro hrun hcovered hCd hsub

      by_cases hr0 : r = 0
      · subst r

        have hblockSub :
            (lemma4Block ring k psi).Sublist
              schedule := by
          simpa [wordPower] using hsub

        have hs :=
          hstart'
            hgeom hcov hrows hright hold hpersist
            (n := n) (psi := psi) (kappa := kappa)
            hpsi ring k kind
            C0 pre G schedule
            hrun hcovered hCd hblockSub
        dsimp only at hs

        rcases hs with hdone | hfront
        · exact Or.inl hdone

        · rcases hfront with
            ⟨hcovered', y, z',
              hright', hfresh', hstage⟩
          exact
            Or.inr
              ⟨hcovered', y, z',
                hright', hfresh', by omega⟩

      · have hrPos : 0 < r := by
          omega

        have hpow :
            wordPower (Nat.succ r)
                (lemma4Block ring k psi) =
              wordPower r
                  (lemma4Block ring k psi) ++
                lemma4Block ring k psi := by
          calc
            wordPower (Nat.succ r)
                (lemma4Block ring k psi) =
              wordPower (r + 1)
                (lemma4Block ring k psi) := by
                  rfl
            _ =
              wordPower r
                  (lemma4Block ring k psi) ++
                wordPower 1
                  (lemma4Block ring k psi) :=
              lemma4_wordPower_add
                r 1 (lemma4Block ring k psi)
            _ =
              wordPower r
                  (lemma4Block ring k psi) ++
                lemma4Block ring k psi := by
              simp [wordPower]

        rw [hpow] at hsub
        rcases List.append_sublist_iff.mp hsub with
          ⟨a, b, hschedule, ha, hb⟩
        subst schedule

        rcases
            lemma4_cdTrace_append
              hpsi ring k kind
              G.phys a b hCd with
          ⟨hCdA, hCdB0⟩

        let G1 :=
          ghostRun hpsi ring pre.length G a

        have hphysA :
            G1.phys =
              PPL.Probability.runPopulationSchedule
                (protocol psi kappa) ring G.phys a := by
          have he :=
            ghostRun_erases
              hpsi ring pre.length G a
          simpa [G1, eraseGhost] using he

        have hCdB :
            CdTrace hpsi ring k kind
              G1.phys b := by
          rw [hphysA]
          exact hCdB0

        have hfirst :=
          ih
            (pre := pre)
            (G := G)
            (schedule := a)
            hrPos
            hrun hcovered hCdA ha

        have hrun1 :
            G1 =
              ghostRun hpsi ring 0
                (initialGhost C0) (pre ++ a) := by
          have happ :=
            lemma4_ghostRun_append
              hpsi ring 0
              (initialGhost C0) pre a
          dsimp only [G1]
          rw [hrun]
          simpa using happ.symm

        have hwhole :
            ghostRun hpsi ring pre.length
                G (a ++ b) =
              ghostRun hpsi ring
                (pre ++ a).length G1 b := by
          have happ :=
            lemma4_ghostRun_append
              hpsi ring pre.length G a b
          dsimp only [G1]
          simpa [List.length_append] using happ

        rcases hfirst with hdone1 | hfront1
        · have hdone2 :=
            secondPowerHasFreshCompletion_run
              hpsi ring kind k
              (pre ++ a).length G1 b
              hdone1
          rw [hwhole]
          exact Or.inl hdone2

        · have hlast :=
            secondPowerFrontierOneBlock
              hgeom hcov hrows hright hold hpersist
              hpsi ring k kind
              C0 (pre ++ a) G1 b
              (psi + r)
              hrun1 hCdB hb hfront1
          dsimp only at hlast

          rw [hwhole]

          rcases hlast with hdone2 | hfront2
          · exact Or.inl hdone2

          · apply Or.inr
            have harith :
                (psi + r) + 1 =
                  psi + Nat.succ r := by
              omega
            rw [← harith]
            exact hfront2

/--
reduction.

Everything after the one-block bootstrap is discharged here:
* Completion through arbitrary suffixes;
* splitting a Sublist occurrence of wordPower psi into block-containing
  schedule pieces;
* strict rightmost-frontier stage accumulation across no-completion blocks;
* the final contradiction between stage >= 2*psi and the corrected sound
  stage bound stage < 2*psi.
-/
theorem lemma4HalfPowerSecondPowerInduction_of_blockStart
    (hstart : Lemma4SecondPowerCoveredBlockStart) :
    Lemma4HalfPowerSecondPowerInduction := by
  unfold Lemma4HalfPowerSecondPowerInduction

  intro hgeom hcov hrows hright hold hpersist
  intro n psi kappa hpsi ring k kind
  intro C0 pre G schedule
  intro hrun hcovered hCd hsub

  have hsubPower :
      (wordPower psi
        (lemma4Block ring k psi)).Sublist
          schedule := by
    simpa [lemma4HalfWord] using hsub

  have hiter :=
    secondPowerFrontierWordPower
      hstart hgeom hcov hrows
      hright hold hpersist
      hpsi ring k kind C0
      psi pre G schedule
      (by omega)
      hrun hcovered hCd hsubPower
  dsimp only at hiter

  rcases hiter with hdone | hfront
  · exact hdone

  · let Gend :=
      ghostRun hpsi ring pre.length G schedule

    rcases hfront with
      ⟨_hcoveredEnd, x, z,
        hrightEnd, _hfreshEnd, hlo⟩

    have hcanonEnd :
        Gend =
          ghostRun hpsi ring 0
            (initialGhost C0)
            (pre ++ schedule) := by
      have happ :=
        lemma4_ghostRun_append
          hpsi ring 0
          (initialGhost C0)
          pre schedule
      dsimp only [Gend]
      rw [hrun]
      simpa using happ.symm

    have hsoundEnd :
        GhostSound Gend := by
      rw [hcanonEnd]
      exact
        lemma4CoverageGhostRunSound_proved
          hpsi ring C0 (pre ++ schedule)

    have hphysEnd :
        Gend.phys =
          PPL.Probability.runPopulationSchedule
            (protocol psi kappa)
            ring G.phys schedule := by
      have he :=
        ghostRun_erases
          hpsi ring pre.length
          G schedule
      simpa [Gend, eraseGhost] using he

    have hCdEnd :
        Cd ring k kind Gend.phys := by
      rw [hphysEnd]
      exact
        secondPowerCdTraceEnd
          hpsi ring k kind
          G.phys schedule hCd

    have hgeom' : Lemma4TwoSweepRankGeometryCorrected :=
      hgeom
    unfold Lemma4TwoSweepRankGeometryCorrected at hgeom'

    have hg :=
      hgeom'
        hcov hrows hright hold hpersist
        (n := n) (psi := psi) (kappa := kappa)
        hpsi ring k kind

    have hrightData := hrightEnd
    unfold Lemma4RightmostAt at hrightData
    dsimp only at hrightData

    have hwin :
        Lemma4InWindow ring k psi
          (shiftRight ring k x.val) :=
      ⟨x, rfl⟩

    have hbound :=
      hg.1
        Gend
        (shiftRight ring k x.val)
        z
        hsoundEnd hCdEnd hwin
        hrightData.1 hrightData.2.1

    have hfalse : False := by
      have hbound' := hbound
      have hlo' := hlo
      dsimp only [Gend] at hbound' hlo'
      omega

    exact False.elim hfalse

end PPL

#print axioms PPL.lemma4HalfPowerSecondPowerInduction_of_blockStart
