import Leader.PPL.TokenCompletion.FirstPower
import Init.Omega

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-!
Proof of `Lemma4FirstPowerNonfreshBlockBackstep`.

* `backstepAncestry`: iterating `Lemma4CoverageStep` backward along the C_d
  trace, every nonfresh in-window endpoint owner has an in-window nonfresh
  pre-owner with the same lineage ID at the start.  A fresh pre-owner at an
  intermediate step is excluded by `Lemma4SweepFreshLineagePersistenceStep`.
* The old-owner field of `Lemma4TwoSweepRankGeometryCorrected` applied to
  that pre-owner gives deletion (contradicted by the endpoint owner) or a
  same-ID survivor with strictly larger stage; `ghostIdsUnique_run`
  identifies the survivor with the endpoint owner.
-/

private theorem backstepCd_two_le_n
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (hCd : Cd ring k kind C) :
    2 ≤ n := by
  by_cases hn2 : 2 ≤ n
  · exact hn2
  · have hn0 : 0 < n := ring.hn
    have hn1 : n = 1 := by
      omega
    subst n

    let x0 : Fin (2 * psi) := ⟨0, by omega⟩
    let x1 : Fin (2 * psi) := ⟨1, by omega⟩

    have h0 := (hCd x0).1
    have h1 := (hCd x1).1
    dsimp only [x0, x1] at h0 h1

    have hs :
        shiftRight ring k 0 =
          shiftRight ring k 1 := by
      apply Fin.ext
      simp [shiftRight]
    rw [hs] at h0

    cases kind with
    | black =>
        have hm1 :
            1 % (2 * psi) = 1 :=
          Nat.mod_eq_of_lt (by omega)
        simp [tokenD', hm1] at h0 h1
        omega
    | white =>
        have hm0 :
            psi % (2 * psi) = psi :=
          Nat.mod_eq_of_lt (by omega)
        have hm1 :
            (1 + psi) % (2 * psi) =
              1 + psi :=
          Nat.mod_eq_of_lt (by omega)
        simp [tokenD', hm0, hm1] at h0 h1
        omega

private theorem backstepOwnerValid
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

/-- Backward nonfresh ancestry along a C_d trace. -/
private theorem backstepAncestry
    (hcov : Lemma4CoverageStep)
    (hpersist : Lemma4SweepFreshLineagePersistenceStep)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn2 : 2 ≤ n)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa) :
    ∀ (schedule : DetSchedule n)
      (pre : DetSchedule n)
      (G : GhostConfig n psi kappa),
      G =
          ghostRun hpsi ring 0
            (initialGhost C0) pre →
      CdTrace hpsi ring k kind G.phys schedule →
      Lemma4GhostCoveredWindow ring k kind G →
      ∀ (j : Fin n) (z' : GhostToken n psi),
        Lemma4InWindow ring k psi j →
        ghostTokenAt kind
            (ghostRun hpsi ring pre.length G schedule) j =
          some z' →
        ¬ FreshAt kind k z'.lmeta →
        ∃ (i : Fin n) (z : GhostToken n psi),
          Lemma4InWindow ring k psi i ∧
            ghostTokenAt kind G i = some z ∧
            ¬ FreshAt kind k z.lmeta ∧
            z'.lmeta.id = z.lmeta.id := by
  have hcov' : Lemma4CoverageStep := hcov
  unfold Lemma4CoverageStep at hcov'
  have hpersist' : Lemma4SweepFreshLineagePersistenceStep := hpersist
  unfold Lemma4SweepFreshLineagePersistenceStep at hpersist'

  intro schedule
  induction schedule with
  | nil =>
      intro pre G _hrun _hCd _hcovered j z' hwin howner hnf
      have howner' : ghostTokenAt kind G j = some z' := howner
      exact ⟨j, z', hwin, howner', hnf, rfl⟩

  | cons e es ih =>
      intro pre G hrun hCd hcovered j z' hwin howner hnf

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

      have hend :
          ghostRun hpsi ring pre.length G (e :: es) =
            ghostRun hpsi ring (pre ++ [e]).length G1 es := by
        rw [List.length_append]
        rfl

      rw [hend] at howner

      rcases
          ih (pre ++ [e]) G1 hrun1 htail hstep.1
            j z' hwin howner hnf with
        ⟨i1, z1, hwin1, howner1, hnf1, hid1⟩

      rcases hstep.2 i1 z1 hwin1 howner1 with
        hfresh1 | ⟨i0, z0, hwin0, howner0, hid0⟩
      · exact False.elim (hnf1 hfresh1)
      · have hn0 : ¬ FreshAt kind k z0.lmeta := by
          intro hfresh0
          have huniq :
              GhostIdsUniqueAt pre.length G := by
            rw [hrun]
            exact
              ghostIdsUnique_run
                hpsi hn2 ring C0 pre
          exact
            hnf1
              (hpersist' hpsi ring k kind
                pre.length G e i0 i1 z0 z1
                huniq hwin0 howner0 hfresh0
                hwin1 howner1 hid0)
        exact
          ⟨i0, z0, hwin0, howner0, hn0,
            hid1.trans hid0⟩

theorem lemma4FirstPowerNonfreshBlockBackstep_proved :
    Lemma4FirstPowerNonfreshBlockBackstep := by
  unfold Lemma4FirstPowerNonfreshBlockBackstep
  intro hgeom hcov hrows hright hold hpersist
  intro n psi kappa hpsi ring k kind C0 pre G schedule j z'
  intro hrun hCd hsub hcovered hwin howner _hvalid hnf

  have hCd0 :
      Cd ring k kind G.phys :=
    lemma4_cdTrace_start
      hpsi ring k kind G.phys schedule hCd

  have hn2 : 2 ≤ n :=
    backstepCd_two_le_n
      hpsi ring k kind G.phys hCd0

  rcases
      backstepAncestry
        hcov hpersist hpsi hn2 ring k kind C0
        schedule pre G hrun hCd hcovered
        j z' hwin howner hnf with
    ⟨i, z, hwin0, howner0, hnf0, hid⟩

  have hsound :
      GhostSound G := by
    rw [hrun]
    exact
      lemma4CoverageGhostRunSound_proved
        hpsi ring C0 pre

  have hvalid0 :
      ValidToken kind G.phys i :=
    backstepOwnerValid
      kind G i z hsound howner0

  have hgeom' : Lemma4TwoSweepRankGeometryCorrected := hgeom
  unfold Lemma4TwoSweepRankGeometryCorrected at hgeom'

  have hg :=
    hgeom'
      hcov hrows hright hold hpersist
      (n := n) (psi := psi) (kappa := kappa)
      hpsi ring k kind

  have hout :=
    hg.2.1
      C0 pre G schedule i z
      hrun hCd hsub hcovered
      hwin0 howner0 hvalid0 hnf0
  dsimp only at hout

  rcases hout with hdel | ⟨j2, z2, _hwin2, howner2, hid2, _hnf2, _hvalid2, hlt⟩
  · exact False.elim (hdel j z' howner hid)
  · have hGend :
        ghostRun hpsi ring pre.length G schedule =
          ghostRun hpsi ring 0
            (initialGhost C0) (pre ++ schedule) := by
      have happ :=
        lemma4_ghostRun_append
          hpsi ring 0
          (initialGhost C0) pre schedule
      rw [hrun]
      simpa using happ.symm

    have huniqEnd :
        GhostIdsUniqueAt (pre ++ schedule).length
          (ghostRun hpsi ring pre.length G schedule) := by
      rw [hGend]
      exact
        ghostIdsUnique_run
          hpsi hn2 ring C0 (pre ++ schedule)

    have hj : j = j2 :=
      huniqEnd.1 kind j j2 z' z2
        howner howner2 (hid.trans hid2.symm)
    subst hj

    have hz : z' = z2 := by
      rw [howner] at howner2
      exact Option.some.inj howner2
    subst hz

    exact ⟨i, z, hwin0, howner0, hvalid0, hnf0, hid, hlt⟩

theorem lemma4HalfPowerFirstPowerInduction_proved :
    Lemma4HalfPowerFirstPowerInduction :=
  lemma4HalfPowerFirstPowerInduction_of_blockBackstep
    lemma4FirstPowerNonfreshBlockBackstep_proved

end PPL

#print axioms PPL.lemma4FirstPowerNonfreshBlockBackstep_proved
#print axioms PPL.lemma4HalfPowerFirstPowerInduction_proved
