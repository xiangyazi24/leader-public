import Leader.PPL.TokenCompletion.RightmostInitiator
import Leader.PPL.TokenCompletion.GhostStepMirror

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Run-level terminal provenance missing from the current main branch.

This is exactly the invariant: if no selected fresh completion has
already been logged, every live fresh owner born at k is still strictly below
the terminal move count.
-/
def Lemma4FreshTerminalProvenance
    {n psi kappa : Nat}
    (k : Fin n)
    (G : GhostConfig n psi kappa) : Prop :=
  ∀ (kind : TokenKind) (i : Fin n)
      (z : GhostToken n psi),
    ghostTokenAt kind G i = some z →
    ¬ HasFreshCompletion kind k G →
    FreshAt kind k z.lmeta →
    z.lmeta.moves < tokenTrajectoryMoves psi

/--
Corrected literal initiator leaf.

The only change from Lemma4RightmostInitiatorLiteralCases is the conditional
terminal-age premise immediately after fresh-lineage kinematics.
-/
def Lemma4RightmostInitiatorLiteralCasesAged : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    GhostSound G →
    GhostIdsUniqueAt step G →
    Lemma4FreshKinematics ring k G →
    (¬ HasFreshCompletion kind k G →
      FreshAt kind k z.lmeta →
      z.lmeta.moves < tokenTrajectoryMoves psi) →
    Lemma4RightmostAt ring k kind G x z →
    e = shiftRight ring k x.val →
    let i := shiftRight ring k x.val
    let G' := ghostStep hpsi ring step G e
    (¬ FreshAt kind k z.lmeta ∧
      ∀ j : Fin n, ∀ z' : GhostToken n psi,
        ghostTokenAt kind G' j = some z' →
        z'.lmeta.id ≠ z.lmeta.id) ∨
    HasFreshCompletion kind k G' ∨
    ∃ y : Fin (2 * psi), ∃ z' : GhostToken n psi,
      Lemma4RightmostAt ring k kind G' y z' ∧
      z'.lmeta.id = z.lmeta.id ∧
      (FreshAt kind k z.lmeta →
        FreshAt kind k z'.lmeta) ∧
      lemma4TokenProgress kind
          (G.phys i) z.value ≤
        lemma4TokenProgress kind
          (G'.phys (shiftRight ring k y.val))
          z'.value ∧
      (e = lemma4ServiceEdge ring kind G i z →
        lemma4TokenProgress kind
            (G'.phys (shiftRight ring k y.val))
            z'.value =
          lemma4TokenProgress kind
              (G.phys i) z.value +
            1)

/--
The single remaining state-local row after the append-only completion arm is
removed.

Case covered: G has no prior selected fresh completion.  Therefore the aged
premise specializes to the unconditional bound on the tracked owner's age.
This is the only residual left for part 2 in this bounded round.
-/
def Lemma4RightmostInitiatorAgedNoPriorCompletionRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    GhostSound G →
    GhostIdsUniqueAt step G →
    Lemma4FreshKinematics ring k G →
    ¬ HasFreshCompletion kind k G →
    (FreshAt kind k z.lmeta →
      z.lmeta.moves < tokenTrajectoryMoves psi) →
    Lemma4RightmostAt ring k kind G x z →
    e = shiftRight ring k x.val →
    let i := shiftRight ring k x.val
    let G' := ghostStep hpsi ring step G e
    (¬ FreshAt kind k z.lmeta ∧
      ∀ j : Fin n, ∀ z' : GhostToken n psi,
        ghostTokenAt kind G' j = some z' →
        z'.lmeta.id ≠ z.lmeta.id) ∨
    HasFreshCompletion kind k G' ∨
    ∃ y : Fin (2 * psi), ∃ z' : GhostToken n psi,
      Lemma4RightmostAt ring k kind G' y z' ∧
      z'.lmeta.id = z.lmeta.id ∧
      (FreshAt kind k z.lmeta →
        FreshAt kind k z'.lmeta) ∧
      lemma4TokenProgress kind
          (G.phys i) z.value ≤
        lemma4TokenProgress kind
          (G'.phys (shiftRight ring k y.val))
          z'.value ∧
      (e = lemma4ServiceEdge ring kind G i z →
        lemma4TokenProgress kind
            (G'.phys (shiftRight ring k y.val))
            z'.value =
          lemma4TokenProgress kind
              (G.phys i) z.value +
            1)

/--
completed is append-only in one ghostStep, so an already present selected
fresh completion remains present after the step.
-/
private theorem agedHasFreshCompletion_step
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
Allowed bounded-round reduction of part 2.

The already-completed branch is fully closed above.  Supplying the one named
no-prior-completion row closes the corrected aged leaf.
-/
theorem lemma4RightmostInitiatorLiteralCasesAged_of_noPriorRow
    (hNoPrior :
      Lemma4RightmostInitiatorAgedNoPriorCompletionRow) :
    Lemma4RightmostInitiatorLiteralCasesAged := by
  unfold Lemma4RightmostInitiatorLiteralCasesAged
  intro n psi kappa hpsi
  intro ring k kind step G e x z
  intro hCd hCd' hcovered hsound huniq hkin
  intro hage hright htrack
  by_cases hdone : HasFreshCompletion kind k G
  · dsimp only
    exact
      Or.inr
        (Or.inl
          (agedHasFreshCompletion_step
            hpsi ring step G e kind k hdone))
  · exact
      hNoPrior
        hpsi ring k kind step G e x z
        hCd hCd' hcovered hsound huniq hkin
        hdone (hage hdone) hright htrack

/--
Local copy of the small ring fact used by the original adapter.

The original lemma4Cd_two_le_n is private to
TokenCorrectnessLemma4RightmostInitiator.lean, so the corrected adapter cannot
name it.
-/
private theorem agedCd_two_le_n
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

/--
Corrected run-history adapter.

hage has the intended statement of the parallel
lemma4FreshTerminalProvenance_run producer.  Once that theorem lands, it can
be supplied directly here.
-/
theorem lemma4RightmostInitiatorBranch_of_literalCasesAged
    (hsound : Lemma4CoverageGhostRunSound)
    (hage :
      ∀ {n psi kappa : Nat}
        (hpsi : 2 ≤ psi)
        (ring : DirectedRing n)
        (k : Fin n)
        (C0 : Config n psi kappa)
        (pre : DetSchedule n),
        Lemma4FreshTerminalProvenance k
          (ghostRun hpsi ring 0
            (initialGhost C0) pre))
    (hliteral : Lemma4RightmostInitiatorLiteralCasesAged) :
    Lemma4RightmostInitiatorBranch := by
  unfold Lemma4RightmostInitiatorBranch
  intro n psi kappa hpsi
  intro ring k kind C0 pre G e x z
  intro hG hCd hCd' hcovered hright htrack

  have hsoundG : GhostSound G := by
    rw [hG]
    exact hsound hpsi ring C0 pre

  have hn2 : 2 ≤ n :=
    agedCd_two_le_n
      hpsi ring k kind G.phys hCd

  have huniq :
      GhostIdsUniqueAt pre.length G := by
    rw [hG]
    exact
      ghostIdsUnique_run
        hpsi hn2 ring C0 pre

  have hkin :
      Lemma4FreshKinematics ring k G := by
    rw [hG]
    exact
      lemma4FreshKinematics_run
        hpsi ring k C0 pre

  have hageG :
      Lemma4FreshTerminalProvenance k G := by
    rw [hG]
    exact hage hpsi ring k C0 pre

  have hrightData := hright
  unfold Lemma4RightmostAt at hrightData
  dsimp only at hrightData

  have howner :
      ghostTokenAt kind G
          (shiftRight ring k x.val) =
        some z :=
    hrightData.1

  have hageZ :
      ¬ HasFreshCompletion kind k G →
      FreshAt kind k z.lmeta →
      z.lmeta.moves < tokenTrajectoryMoves psi :=
    hageG kind
      (shiftRight ring k x.val) z howner

  change
    let i := shiftRight ring k x.val
    let G' :=
      ghostStep hpsi ring pre.length G e
    (¬ FreshAt kind k z.lmeta ∧
      ∀ j : Fin n, ∀ z' : GhostToken n psi,
        ghostTokenAt kind G' j = some z' →
        z'.lmeta.id ≠ z.lmeta.id) ∨
    HasFreshCompletion kind k G' ∨
    ∃ y : Fin (2 * psi), ∃ z' : GhostToken n psi,
      Lemma4RightmostAt ring k kind G' y z' ∧
      z'.lmeta.id = z.lmeta.id ∧
      (FreshAt kind k z.lmeta →
        FreshAt kind k z'.lmeta) ∧
      lemma4TokenProgress kind
          (G.phys i) z.value ≤
        lemma4TokenProgress kind
          (G'.phys (shiftRight ring k y.val))
          z'.value ∧
      (e = lemma4ServiceEdge ring kind G i z →
        lemma4TokenProgress kind
            (G'.phys (shiftRight ring k y.val))
            z'.value =
          lemma4TokenProgress kind
              (G.phys i) z.value +
            1)

  exact
    hliteral
      hpsi ring k kind pre.length
      G e x z
      hCd hCd' hcovered
      hsoundG huniq hkin hageZ
      hright htrack

end PPL

#print axioms PPL.lemma4RightmostInitiatorLiteralCasesAged_of_noPriorRow
#print axioms PPL.lemma4RightmostInitiatorBranch_of_literalCasesAged
