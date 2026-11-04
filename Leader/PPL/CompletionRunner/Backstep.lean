import Leader.PPL.CompletionRunner.FirstPower
import Init.Omega

/-!
# Step-parametric Lemma 4: first-power reverse ancestry

Generic version of `TokenCorrectnessLemma4FirstPowerBackstep.lean`.

* `backstepAncestry`: iterating the step clause of `CoverageStep R` backward
  along the `C_d` trace, every nonfresh in-window endpoint owner has an
  in-window nonfresh pre-owner with the same lineage ID at the start.  A fresh
  pre-owner at an intermediate step is excluded by
  `FreshLineagePersistenceStep R` together with run ID uniqueness.
* The old-owner field of `RankGeometryCorrected R` applied to that pre-owner
  gives deletion (contradicted by the endpoint owner) or a same-ID survivor
  with strictly larger stage; run ID uniqueness identifies the survivor with
  the endpoint owner.

The ordinary theorems `lemma4CoverageGhostRunSound_proved` and
`ghostIdsUnique_run` become the hypotheses `RunSound R` and
`IdsUniqueStep R`.
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-- `C_d` with `2 ≤ psi` forces a ring with at least two sites. -/
theorem cd_two_le_n
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

/-- Backward nonfresh ancestry along a `C_d` trace of the runner. -/
theorem backstepAncestry
    (R : Lemma4Runner)
    (huniq : IdsUniqueStep R)
    (hcov : CoverageStep R)
    (hpersist : FreshLineagePersistenceStep R)
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
          R.run hpsi ring 0
            (initialGhost C0) pre →
      R.cdTrace hpsi ring k kind G.phys schedule →
      Lemma4GhostCoveredWindow ring k kind G →
      ∀ (j : Fin n) (z' : GhostToken n psi),
        Lemma4InWindow ring k psi j →
        ghostTokenAt kind
            (R.run hpsi ring pre.length G schedule) j =
          some z' →
        ¬ FreshAt kind k z'.lmeta →
        ∃ (i : Fin n) (z : GhostToken n psi),
          Lemma4InWindow ring k psi i ∧
            ghostTokenAt kind G i = some z ∧
            ¬ FreshAt kind k z.lmeta ∧
            z'.lmeta.id = z.lmeta.id := by
  intro schedule
  induction schedule with
  | nil =>
      intro pre G _hrun _hCd _hcovered j z' hwin howner hnf
      rw [R.run_nil] at howner
      exact ⟨j, z', hwin, howner, hnf, rfl⟩
  | cons e es ih =>
      intro pre G hrun hCd hcovered j z' hwin howner hnf
      rcases cdTrace_step R hpsi ring k kind pre.length G e es hCd with
        ⟨hCd0, hCd1, htail⟩
      let G1 :=
        R.gstep hpsi ring pre.length G e
      have hstep :=
        (hcov hpsi ring k kind).2
          C0 pre G e
          hrun hCd0 hCd1 hcovered
      dsimp only at hstep
      have hrun1 :
          G1 =
            R.run hpsi ring 0
              (initialGhost C0) (pre ++ [e]) :=
        run_snoc_eq R hpsi ring C0 pre G e hrun
      rw [run_cons_length R hpsi ring pre G e es] at howner
      rcases
          ih (pre ++ [e]) G1 hrun1 htail hstep.1
            j z' hwin howner hnf with
        ⟨i1, z1, hwin1, howner1, hnf1, hid1⟩
      rcases hstep.2 i1 z1 hwin1 howner1 with
        hfresh1 | ⟨i0, z0, hwin0, howner0, hid0⟩
      · exact False.elim (hnf1 hfresh1)
      · have hn0 : ¬ FreshAt kind k z0.lmeta := by
          intro hfresh0
          have hU :
              GhostIdsUniqueAt pre.length G := by
            rw [hrun]
            exact
              idsUnique_run R huniq
                hpsi hn2 ring C0 pre
          exact
            hnf1
              (hpersist hpsi ring k kind
                pre.length G e i0 i1 z0 z1
                hU hwin0 howner0 hfresh0
                hwin1 howner1 hid0)
        exact
          ⟨i0, z0, hwin0, howner0, hn0,
            hid1.trans hid0⟩

/--
Generic `lemma4FirstPowerNonfreshBlockBackstep_proved`, from run soundness
and one-step lineage-ID uniqueness of the runner.
-/
theorem firstPowerNonfreshBlockBackstep_proved
    (R : Lemma4Runner)
    (hsound : RunSound R)
    (huniq : IdsUniqueStep R) :
    FirstPowerNonfreshBlockBackstep R := by
  unfold FirstPowerNonfreshBlockBackstep
  intro hgeom hcov hrows hright hold hpersist
  intro n psi kappa hpsi ring k kind C0 pre G schedule j z'
  intro hrun hCd hsub hcovered hwin howner _hvalid hnf
  have hCd0 :
      Cd ring k kind G.phys :=
    R.cdTrace_start hpsi ring k kind G.phys schedule hCd
  have hn2 : 2 ≤ n :=
    cd_two_le_n hpsi ring k kind G.phys hCd0
  rcases
      backstepAncestry R huniq
        hcov hpersist hpsi hn2 ring k kind C0
        schedule pre G hrun hCd hcovered
        j z' hwin howner hnf with
    ⟨i, z, hwin0, howner0, hnf0, hid⟩
  have hsoundG :
      GhostSound G := by
    rw [hrun]
    exact hsound hpsi ring C0 pre
  have hvalid0 :
      ValidToken kind G.phys i :=
    ownerValid_of_sound
      kind G i z hsoundG howner0
  have hg :=
    hgeom
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
        R.run hpsi ring pre.length G schedule =
          R.run hpsi ring 0
            (initialGhost C0) (pre ++ schedule) :=
      run_prefix_eq R hpsi ring C0 pre G schedule hrun
    have huniqEnd :
        GhostIdsUniqueAt (pre ++ schedule).length
          (R.run hpsi ring pre.length G schedule) := by
      rw [hGend]
      exact
        idsUnique_run R huniq
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

/-- Generic first-power induction, from run soundness and ID uniqueness. -/
theorem halfPowerFirstPowerInduction_proved
    (R : Lemma4Runner)
    (hsound : RunSound R)
    (huniq : IdsUniqueStep R) :
    HalfPowerFirstPowerInduction R :=
  halfPowerFirstPowerInduction_of_blockBackstep R hsound
    (firstPowerNonfreshBlockBackstep_proved R hsound huniq)

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.firstPowerNonfreshBlockBackstep_proved
#print axioms PPL.Lemma4Generic.halfPowerFirstPowerInduction_proved
