import Leader.PPL.TokenCompletion.CoreRoute
import Leader.PPL.TokenCompletion.CoverageLeaves
import Init.Omega

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Exact one-block reverse interface missing from the current forward geometry.

Truth argument.

* `Lemma4CoverageStep`, iterated through the whole block-containing schedule,
  traces every nonfresh endpoint owner backward to an in-window pre-owner
  with the same lineage ID.  The fresh alternative is impossible by the
  endpoint nonfresh hypothesis.
* If that recovered pre-owner were fresh, the proved unmasked
  `Lemma4SweepFreshLineagePersistenceStep` would make every same-ID
  in-window survivor fresh, again contradicting the endpoint.
* The old-owner field of `Lemma4TwoSweepRankGeometryCorrected` then applies
  to that pre-owner over the *whole* arbitrary schedule containing one
  `lemma4Block` as a Sublist.  Hence interleaved extra letters are already
  accounted for.
* The deletion arm is contradicted by the given endpoint owner.  In the
  survivor arm, canonical `ghostIdsUnique_run` identifies the geometry's
  same-ID survivor with the given endpoint owner.  (The required `2 <= n`
  follows from `C_d` and `2 <= psi`, exactly as in
  TokenCorrectnessLemma4SweepOldOwnerRows.)
-/
def Lemma4FirstPowerNonfreshBlockBackstep : Prop :=
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
    (schedule : DetSchedule n)
    (j : Fin n)
    (z' : GhostToken n psi),
    G =
        ghostRun hpsi ring 0
          (initialGhost C0) pre →
    CdTrace hpsi ring k kind G.phys schedule →
    (lemma4Block ring k psi).Sublist schedule →
    Lemma4GhostCoveredWindow ring k kind G →
    Lemma4InWindow ring k psi j →
    ghostTokenAt kind
        (ghostRun hpsi ring pre.length G schedule) j =
      some z' →
    ValidToken kind
      (ghostRun hpsi ring pre.length G schedule).phys j →
    ¬ FreshAt kind k z'.lmeta →
    ∃ (i : Fin n) (z : GhostToken n psi),
      Lemma4InWindow ring k psi i ∧
        ghostTokenAt kind G i = some z ∧
        ValidToken kind G.phys i ∧
        ¬ FreshAt kind k z.lmeta ∧
        z'.lmeta.id = z.lmeta.id ∧
        lemma4TokenStage
            kind (G.phys i) z.value <
          lemma4TokenStage
            kind
            ((ghostRun hpsi ring pre.length G schedule).phys j)
            z'.value

private def firstPowerRankAt
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (lower : Nat)
    (G : GhostConfig n psi kappa) : Prop :=
  ∀ (i : Fin n) (z : GhostToken n psi),
    Lemma4InWindow ring k psi i →
    ghostTokenAt kind G i = some z →
    ValidToken kind G.phys i →
    ¬ FreshAt kind k z.lmeta →
    lower ≤
      lemma4TokenStage
        kind (G.phys i) z.value

private theorem firstPowerOwnerValid
    {n psi kappa : Nat}
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner : ghostTokenAt kind G i = some z) :
    ValidToken kind G.phys i := by
  cases kind with
  | black =>
      have hs := hsound.1 i z howner
      unfold ValidToken
      rw [hs.1]
      exact hs.2
  | white =>
      have hs := hsound.2 i z howner
      unfold ValidToken
      rw [hs.1]
      exact hs.2

/--
Coverage is the easy half of the first-power induction: the proved
`Lemma4CoverageStep` iterates along an arbitrary C_d trace.  This helper
keeps the canonical prefix equation explicit because CoverageStep requires it.
-/
private theorem firstPowerCoverageRun
    (hcov : Lemma4CoverageStep)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa) :
    ∀ (pre : DetSchedule n)
      (G : GhostConfig n psi kappa)
      (schedule : DetSchedule n),
      G =
          ghostRun hpsi ring 0
            (initialGhost C0) pre →
      CdTrace hpsi ring k kind G.phys schedule →
      Lemma4GhostCoveredWindow ring k kind G →
      Lemma4GhostCoveredWindow ring k kind
        (ghostRun hpsi ring pre.length G schedule) := by
  have hcov' : Lemma4CoverageStep := hcov
  unfold Lemma4CoverageStep at hcov'

  intro pre G schedule
  induction schedule generalizing pre G with
  | nil =>
      intro _hrun _hCd hcovered
      simpa [ghostRun] using hcovered

  | cons e es ih =>
      intro hrun hCd hcovered

      change
        Cd ring k kind G.phys ∧
          CdTrace hpsi ring k kind
            (PopulationProtocol.step
              (protocol psi kappa) ring G.phys e) es
        at hCd

      let G1 :=
        ghostStep hpsi ring pre.length G e

      have hCd1 :
          Cd ring k kind G1.phys := by
        change
          Cd ring k kind
            (PopulationProtocol.step
              (protocol psi kappa) ring G.phys e)
        exact
          lemma4_cdTrace_start
            hpsi ring k kind
            (PopulationProtocol.step
              (protocol psi kappa) ring G.phys e)
            es hCd.2

      have hstep :=
        (hcov' hpsi ring k kind).2
          C0 pre G e
          hrun hCd.1 hCd1 hcovered
      dsimp only at hstep

      have hrun1 :
          G1 =
            ghostRun hpsi ring 0
              (initialGhost C0) (pre ++ [e]) := by
        have happ :=
          lemma4_ghostRun_append
            hpsi ring 0
            (initialGhost C0) pre [e]
        dsimp only [G1]
        rw [hrun]
        simpa [ghostRun] using happ.symm

      have htail :
          CdTrace hpsi ring k kind G1.phys es := by
        change
          CdTrace hpsi ring k kind
            (PopulationProtocol.step
              (protocol psi kappa) ring G.phys e) es
        exact hCd.2

      have ht :=
        ih
          (pre := pre ++ [e])
          (G := G1)
          hrun1 htail hstep.1

      simpa [G1, ghostRun,
        List.length_append] using ht

private theorem firstPowerCdTraceEnd
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
      simpa [CdTrace,
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

private theorem firstPowerRankOneBlock
    (hback : Lemma4FirstPowerNonfreshBlockBackstep)
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
    (hcovered :
      Lemma4GhostCoveredWindow
        ring k kind G)
    (hrank :
      firstPowerRankAt
        ring k kind lower G) :
    firstPowerRankAt
      ring k kind (lower + 1)
      (ghostRun hpsi ring pre.length G schedule) := by
  have hback' := hback
  unfold Lemma4FirstPowerNonfreshBlockBackstep at hback'

  intro j z' hwin howner hvalid hnonfresh

  rcases
      hback'
        hgeom hcov hrows hright hold hpersist
        (n := n) (psi := psi) (kappa := kappa)
        hpsi ring k kind
        C0 pre G schedule j z'
        hrun hCd hsub hcovered
        hwin howner hvalid hnonfresh with
    ⟨i, z, hwin0, howner0,
      hvalid0, hnonfresh0, _hid, hlt⟩

  have hlo :=
    hrank
      i z hwin0 howner0
      hvalid0 hnonfresh0
  omega

/--
The actual `wordPower` induction.  It splits off the *last* required block.
That choice is important: the suffix containing the last block also contains
all trailing extra scheduler letters, so the one-block endpoint theorem
absorbs them.  There is therefore no problematic zero-block trailing suffix.
-/
private theorem firstPowerRankWordPower
    (hback : Lemma4FirstPowerNonfreshBlockBackstep)
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
    ∀ (r lower : Nat)
      (pre : DetSchedule n)
      (G : GhostConfig n psi kappa)
      (schedule : DetSchedule n),
      0 < r →
      G =
          ghostRun hpsi ring 0
            (initialGhost C0) pre →
      CdTrace hpsi ring k kind G.phys schedule →
      (wordPower r
        (lemma4Block ring k psi)).Sublist schedule →
      Lemma4GhostCoveredWindow ring k kind G →
      firstPowerRankAt ring k kind lower G →
      Lemma4GhostCoveredWindow ring k kind
          (ghostRun hpsi ring pre.length G schedule) ∧
        firstPowerRankAt
          ring k kind (lower + r)
          (ghostRun hpsi ring pre.length G schedule) := by
  intro r
  induction r with
  | zero =>
      intro lower pre G schedule hr
      omega

  | succ r ih =>
      intro lower pre G schedule _hr
      intro hrun hCd hsub hcovered hrank

      by_cases hr0 : r = 0
      · subst r
        have hblockSub :
            (lemma4Block ring k psi).Sublist
              schedule := by
          simpa [wordPower] using hsub

        have hcoveredEnd :=
          firstPowerCoverageRun
            hcov hpsi ring k kind C0
            pre G schedule
            hrun hCd hcovered

        have hrankEnd :=
          firstPowerRankOneBlock
            hback hgeom hcov hrows
            hright hold hpersist
            hpsi ring k kind
            C0 pre G schedule lower
            hrun hCd hblockSub
            hcovered hrank

        exact ⟨hcoveredEnd, by simpa using hrankEnd⟩

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
            (lower := lower)
            (pre := pre)
            (G := G)
            (schedule := a)
            hrPos
            hrun hCdA ha hcovered hrank

        rcases hfirst with
          ⟨hcovered1, hrank1⟩

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

        have hcovered2 :=
          firstPowerCoverageRun
            hcov hpsi ring k kind C0
            (pre ++ a) G1 b
            hrun1 hCdB hcovered1

        have hrank2 :=
          firstPowerRankOneBlock
            hback hgeom hcov hrows
            hright hold hpersist
            hpsi ring k kind
            C0 (pre ++ a) G1 b
            (lower + r)
            hrun1 hCdB hb
            hcovered1 hrank1

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

        rw [hwhole]

        refine ⟨hcovered2, ?_⟩
        have harith :
            (lower + r) + 1 =
              lower + Nat.succ r := by
          omega
        rw [← harith]
        exact hrank2

/--
reduction.

Everything after the one-block reverse-ancestry interface is discharged:
coverage along arbitrary extra letters, splitting the repeated Sublist into
block-containing schedule pieces, rank accumulation through `wordPower`, and
the final contradiction with the sound stage upper bound.
-/
theorem lemma4HalfPowerFirstPowerInduction_of_blockBackstep
    (hback : Lemma4FirstPowerNonfreshBlockBackstep) :
    Lemma4HalfPowerFirstPowerInduction := by
  unfold Lemma4HalfPowerFirstPowerInduction

  intro hgeom hcov hrows hright hold hpersist
  intro n psi kappa hpsi ring k kind
  intro C schedule hCd hsub

  have hCd0 :
      Cd ring k kind C :=
    lemma4_cdTrace_start
      hpsi ring k kind C schedule hCd

  have hcov' : Lemma4CoverageStep := hcov
  unfold Lemma4CoverageStep at hcov'

  have hcovered0 :
      Lemma4GhostCoveredWindow
        ring k kind (initialGhost C) :=
    (hcov' hpsi ring k kind).1 C hCd0

  have hsound0 :
      GhostSound (initialGhost C) := by
    have hs :=
      lemma4CoverageGhostRunSound_proved
        hpsi ring C []
    simpa [ghostRun] using hs

  have hgeom' := hgeom
  unfold Lemma4TwoSweepRankGeometryCorrected at hgeom'

  have hg :=
    hgeom'
      hcov hrows hright hold hpersist
      (n := n) (psi := psi) (kappa := kappa)
      hpsi ring k kind

  have hrank0 :
      firstPowerRankAt
        ring k kind psi (initialGhost C) := by
    intro i z hwin howner hvalid _hnonfresh
    exact
      (hg.1
        (initialGhost C) i z
        hsound0 hCd0 hwin
        howner hvalid).1

  have hsubPower :
      (wordPower psi
        (lemma4Block ring k psi)).Sublist
          schedule := by
    simpa [lemma4HalfWord] using hsub

  have hiter :=
    firstPowerRankWordPower
      hback hgeom hcov hrows
      hright hold hpersist
      hpsi ring k kind C
      psi psi
      [] (initialGhost C) schedule
      (by omega)
      (by rfl)
      hCd hsubPower
      hcovered0 hrank0

  let Gend :=
    ghostRun hpsi ring 0
      (initialGhost C) schedule

  have hcoveredEnd :
      Lemma4GhostCoveredWindow
        ring k kind Gend := by
    simpa [Gend] using hiter.1

  have hrankEnd :
      firstPowerRankAt
        ring k kind (psi + psi) Gend := by
    simpa [Gend] using hiter.2

  have hsoundEnd :
      GhostSound Gend := by
    simpa [Gend] using
      lemma4CoverageGhostRunSound_proved
        hpsi ring C schedule

  have hphysEnd :
      Gend.phys =
        PPL.Probability.runPopulationSchedule
          (protocol psi kappa) ring C schedule := by
    have he :=
      ghostRun_erases
        hpsi ring 0
        (initialGhost C) schedule
    rw [lemma4_erase_initialGhost C] at he
    simpa [Gend, eraseGhost] using he

  have hCdEnd :
      Cd ring k kind Gend.phys := by
    rw [hphysEnd]
    exact
      firstPowerCdTraceEnd
        hpsi ring k kind
        C schedule hCd

  refine ⟨?_, hcoveredEnd⟩
  unfold Lemma4FreshWindow
  intro i z hwin howner

  by_cases hfresh :
      FreshAt kind k z.lmeta
  · exact hfresh

  · have hvalid :
        ValidToken kind Gend.phys i :=
      firstPowerOwnerValid
        kind Gend i z hsoundEnd howner

    have hlo :=
      hrankEnd
        i z hwin howner hvalid hfresh

    have hb :=
      hg.1
        Gend i z
        hsoundEnd hCdEnd
        hwin howner hvalid

    have hfalse : False := by
      omega
    exact False.elim hfalse

end PPL

#print axioms PPL.lemma4HalfPowerFirstPowerInduction_of_blockBackstep
