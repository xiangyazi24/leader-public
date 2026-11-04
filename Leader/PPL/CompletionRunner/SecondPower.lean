import Leader.PPL.CompletionRunner.FirstPower
import Init.Omega

/-!
# Step-parametric Lemma 4: second-power block induction

Generic version of `TokenCorrectnessLemma4SecondPower.lean`.  The ordinary
one-step append-only lemma for `completed` (which unfolded `ghostStep`) is
replaced by the runner law `gstep_completed`, through
`Lemma4Runner.hasFreshCompletion_run`; run soundness is the hypothesis
`RunSound R`.
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Generic `Lemma4SecondPowerCoveredBlockStart`: one block from an actual run
state with a covered-fresh window either logs a fresh completion or leaves a
covered-fresh window with a fresh rightmost owner past the first stage.
-/
def SecondPowerCoveredBlockStart (R : Lemma4Runner) : Prop :=
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
    (lemma4Block ring k psi).Sublist schedule →
    let G' :=
      R.run hpsi ring pre.length G schedule
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

/-- Covered-fresh window with a fresh rightmost owner at stage `≥ lower`. -/
def secondPowerFrontierAt
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
One further block strictly raises the tracked fresh rightmost frontier unless
a fresh completion is logged (fresh-rightmost clause of the rank geometry).
-/
theorem secondPowerFrontierOneBlock
    (R : Lemma4Runner)
    (hgeom : RankGeometryCorrected R)
    (hcov : CoverageStep R)
    (hrows : SweepMissingRows R)
    (hright : RightmostProgressStep R)
    (hold : OldOwnerProgressStep R)
    (hpersist : FreshLineagePersistenceStep R)
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
        R.run hpsi ring 0
          (initialGhost C0) pre)
    (hCd :
      R.cdTrace hpsi ring k kind
        G.phys schedule)
    (hsub :
      (lemma4Block ring k psi).Sublist
        schedule)
    (hfront :
      secondPowerFrontierAt
        ring k kind lower G) :
    let G' :=
      R.run hpsi ring pre.length G schedule
    HasFreshCompletion kind k G' ∨
      secondPowerFrontierAt
        ring k kind (lower + 1) G' := by
  have hg :=
    hgeom
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
Power induction after the bootstrap block; a completion in a prefix is carried
through the suffix by the append-only log.
-/
theorem secondPowerFrontierWordPower
    (R : Lemma4Runner)
    (hstart : SecondPowerCoveredBlockStart R)
    (hgeom : RankGeometryCorrected R)
    (hcov : CoverageStep R)
    (hrows : SweepMissingRows R)
    (hright : RightmostProgressStep R)
    (hold : OldOwnerProgressStep R)
    (hpersist : FreshLineagePersistenceStep R)
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
          R.run hpsi ring 0
            (initialGhost C0) pre →
      Lemma4CoveredFreshWindow ring k kind G →
      R.cdTrace hpsi ring k kind G.phys schedule →
      (wordPower r
        (lemma4Block ring k psi)).Sublist schedule →
      let G' :=
        R.run hpsi ring pre.length G schedule
      HasFreshCompletion kind k G' ∨
        secondPowerFrontierAt
          ring k kind (psi + r) G' := by
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
          hstart
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
            R.cdTrace_append
              hpsi ring k kind
              G.phys a b hCd with
          ⟨hCdA, hCdB0⟩
        let G1 :=
          R.run hpsi ring pre.length G a
        have hphysA :
            G1.phys = R.physRun hpsi ring G.phys a :=
          R.run_phys hpsi ring pre.length G a
        have hCdB :
            R.cdTrace hpsi ring k kind
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
              R.run hpsi ring 0
                (initialGhost C0) (pre ++ a) :=
          run_prefix_eq R hpsi ring C0 pre G a hrun
        have hwhole :
            R.run hpsi ring pre.length
                G (a ++ b) =
              R.run hpsi ring
                (pre ++ a).length G1 b :=
          run_split_length R hpsi ring pre G a b
        rcases hfirst with hdone1 | hfront1
        · have hdone2 :=
            R.hasFreshCompletion_run
              hpsi ring kind k
              (pre ++ a).length G1 b
              hdone1
          try dsimp only
          rw [hwhole]
          exact Or.inl hdone2
        · have hlast :=
            secondPowerFrontierOneBlock R
              hgeom hcov hrows hright hold hpersist
              hpsi ring k kind
              C0 (pre ++ a) G1 b
              (psi + r)
              hrun1 hCdB hb hfront1
          dsimp only at hlast
          try dsimp only
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
Generic reduction: the second-power induction from the one-block
bootstrap and run soundness.  Append-only completion, sublist splitting,
strict frontier-stage accumulation across `psi` no-completion blocks and the
final contradiction with `stage < 2 psi` are discharged here.
-/
theorem halfPowerSecondPowerInduction_of_blockStart
    (R : Lemma4Runner)
    (hsound : RunSound R)
    (hstart : SecondPowerCoveredBlockStart R) :
    HalfPowerSecondPowerInduction R := by
  unfold HalfPowerSecondPowerInduction
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
    secondPowerFrontierWordPower R
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
      R.run hpsi ring pre.length G schedule
    rcases hfront with
      ⟨_hcoveredEnd, x, z,
        hrightEnd, _hfreshEnd, hlo⟩
    have hcanonEnd :
        Gend =
          R.run hpsi ring 0
            (initialGhost C0)
            (pre ++ schedule) :=
      run_prefix_eq R hpsi ring C0 pre G schedule hrun
    have hsoundEnd :
        GhostSound Gend := by
      rw [hcanonEnd]
      exact hsound hpsi ring C0 (pre ++ schedule)
    have hphysEnd :
        Gend.phys = R.physRun hpsi ring G.phys schedule :=
      R.run_phys hpsi ring pre.length G schedule
    have hCdEnd :
        Cd ring k kind Gend.phys := by
      rw [hphysEnd]
      exact R.cdTrace_end hpsi ring k kind G.phys schedule hCd
    have hg :=
      hgeom
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

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.halfPowerSecondPowerInduction_of_blockStart
