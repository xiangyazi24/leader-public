import Leader.PPL.TokenCompletion.SecondPower
import Init.Omega

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Finite greatest-element selection on `Fin N` without Mathlib: if some
coordinate satisfies `P`, some satisfying coordinate has no satisfying
coordinate strictly above it.
-/
private theorem secondStartExistsGreatest
    {N : Nat}
    (P : Fin N → Prop)
    (x0 : Fin N)
    (h0 : P x0) :
    ∃ x : Fin N, P x ∧
      ∀ y : Fin N, x.val < y.val → ¬ P y := by
  apply Classical.byContradiction
  intro hno
  have hstep :
      ∀ x : Fin N, P x →
        ∃ y : Fin N, x.val < y.val ∧ P y := by
    intro x hx
    apply Classical.byContradiction
    intro hne
    apply hno
    exact ⟨x, hx, fun y hy hPy => hne ⟨y, hy, hPy⟩⟩
  have hclimb :
      ∀ m : Nat, ∃ x : Fin N, m ≤ x.val ∧ P x := by
    intro m
    induction m with
    | zero =>
        exact ⟨x0, Nat.zero_le _, h0⟩
    | succ m ih =>
        obtain ⟨x, hx, hPx⟩ := ih
        obtain ⟨y, hy, hPy⟩ := hstep x hPx
        exact ⟨y, by omega, hPy⟩
  obtain ⟨x, hx, _⟩ := hclimb N
  have hlt := x.isLt
  omega

private theorem secondStartOwnerValid
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

private theorem secondStartCdHead
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (schedule : DetSchedule n)
    (hCd : CdTrace hpsi ring k kind C schedule) :
    Cd ring k kind C := by
  cases schedule with
  | nil => exact hCd
  | cons e es => exact hCd.1

theorem lemma4SecondPowerCoveredBlockStart_proved :
    Lemma4SecondPowerCoveredBlockStart := by
  unfold Lemma4SecondPowerCoveredBlockStart
  intro hgeom hcov hrows hright hold hpersist
  intro n psi kappa hpsi ring k kind
  intro C0 pre G schedule
  intro hrun hcovered hCd hsub

  have hgeom' : Lemma4TwoSweepRankGeometryCorrected :=
    hgeom
  unfold Lemma4TwoSweepRankGeometryCorrected at hgeom'
  have hg :=
    hgeom'
      hcov hrows hright hold hpersist
      (n := n) (psi := psi) (kappa := kappa)
      hpsi ring k kind

  by_cases hocc :
      ∃ x : Fin (2 * psi),
        ∃ z : GhostToken n psi,
          ghostTokenAt kind G
            (shiftRight ring k x.val) = some z
  · obtain ⟨x0, hx0⟩ := hocc
    obtain ⟨x, ⟨z, hz⟩, hmax⟩ :=
      secondStartExistsGreatest
        (fun y : Fin (2 * psi) =>
          ∃ z : GhostToken n psi,
            ghostTokenAt kind G
              (shiftRight ring k y.val) = some z)
        x0 hx0

    have hsound : GhostSound G := by
      rw [hrun]
      exact lemma4CoverageGhostRunSound_proved hpsi ring C0 pre

    have hvalid :
        ValidToken kind G.phys (shiftRight ring k x.val) :=
      secondStartOwnerValid kind G _ z hsound hz

    have hCd0 : Cd ring k kind G.phys :=
      secondStartCdHead hpsi ring k kind G.phys schedule hCd

    have hwin :
        Lemma4InWindow ring k psi (shiftRight ring k x.val) :=
      ⟨x, rfl⟩

    have hfresh : FreshAt kind k z.lmeta :=
      hcovered.1 _ z hwin hz

    have hlow :=
      (hg.1 G (shiftRight ring k x.val) z
        hsound hCd0 hwin hz hvalid).1

    have hrightAt : Lemma4RightmostAt ring k kind G x z := by
      unfold Lemma4RightmostAt
      dsimp only
      refine ⟨hz, hvalid, ?_⟩
      intro y hy
      have hnot := hmax y hy
      cases hyo : ghostTokenAt kind G (shiftRight ring k y.val) with
      | none => rfl
      | some w => exact False.elim (hnot ⟨w, hyo⟩)

    have hs :=
      hg.2.2.1
        C0 pre G schedule x z
        hrun hcovered hCd hsub
        hrightAt hfresh
    dsimp only at hs
    dsimp only
    rcases hs with hdone | hkeep
    · exact Or.inl hdone
    · rcases hkeep with
        ⟨hcovered', y, z', hright', _hid, hfresh', hlt⟩
      exact
        Or.inr
          ⟨hcovered', y, z', hright', hfresh', by omega⟩

  · have hempty : Lemma4WindowEmpty ring k kind G := by
      intro i z hwin hz
      obtain ⟨x, hx⟩ := hwin
      subst hx
      exact hocc ⟨x, z, hz⟩
    have hs :=
      hg.2.2.2
        C0 pre G schedule
        hrun hcovered hempty hCd hsub
    dsimp only at hs
    dsimp only
    exact hs

theorem lemma4HalfPowerSecondPowerInduction_proved :
    Lemma4HalfPowerSecondPowerInduction :=
  lemma4HalfPowerSecondPowerInduction_of_blockStart
    lemma4SecondPowerCoveredBlockStart_proved

end PPL

#print axioms PPL.lemma4SecondPowerCoveredBlockStart_proved
#print axioms PPL.lemma4HalfPowerSecondPowerInduction_proved
