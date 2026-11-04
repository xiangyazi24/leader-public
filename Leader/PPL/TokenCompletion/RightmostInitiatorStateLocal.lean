import Leader.PPL.TokenCompletion.RightmostInitiatorNoPrior

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Pure one-step terminal residual.

Compared with Lemma4RightmostInitiatorAgedTerminalRow, this drops the
run-history hypothesis `¬ HasFreshCompletion kind k G` and ID uniqueness.
The remaining hypotheses are exactly the state-local ingredients needed to
exclude collision/nonterminal survival and identify the final fresh service.
-/
def Lemma4RightmostInitiatorTerminalStateLocalResidual : Prop :=
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
    Lemma4FreshKinematics ring k G →
    (FreshAt kind k z.lmeta →
      z.lmeta.moves < tokenTrajectoryMoves psi) →
    Lemma4RightmostAt ring k kind G x z →
    e = shiftRight ring k x.val →
    (∀ zL : GhostToken n psi,
      (ghostStepSelectedPair
          hpsi ring step G e kind).left =
        some zL →
      zL.lmeta.id ≠ z.lmeta.id) →
    (∀ zR : GhostToken n psi,
      (ghostStepSelectedPair
          hpsi ring step G e kind).right =
        some zR →
      zR.lmeta.id ≠ z.lmeta.id) →
    FreshAt kind k z.lmeta →
    HasFreshCompletion kind k
      (ghostStep hpsi ring step G e)

/--
Pure one-step same-ID survival residual.

The no-prior-completion premise, terminal-age premise, ID uniqueness, and
fresh kinematics are not needed for this local survivor statement.  The
remaining work is exactly the selected-color value-row plus the no-overtake
bookkeeping for the interacted pair.
-/
def Lemma4RightmostInitiatorSurvivalStateLocalResidual : Prop :=
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
    Lemma4RightmostAt ring k kind G x z →
    e = shiftRight ring k x.val →
    ((∃ zL : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).left =
          some zL ∧
        zL.lmeta.id = z.lmeta.id) ∨
      (∃ zR : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).right =
          some zR ∧
        zR.lmeta.id = z.lmeta.id)) →
    let i := shiftRight ring k x.val
    let G' := ghostStep hpsi ring step G e
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

theorem lemma4RightmostInitiatorAgedTerminalRow_of_terminalStateLocalResidual
    (hlocal :
      Lemma4RightmostInitiatorTerminalStateLocalResidual) :
    Lemma4RightmostInitiatorAgedTerminalRow := by
  unfold Lemma4RightmostInitiatorAgedTerminalRow
  intro n psi kappa hpsi
  intro ring k kind step G e x z
  intro hCd hCd' hcovered hsound _huniq hkin
  intro _hnoPrior hage hright htrack
  intro hleft hrightOut hfresh
  exact
    hlocal
      hpsi ring k kind step G e x z
      hCd hCd' hcovered hsound hkin
      hage hright htrack
      hleft hrightOut hfresh

theorem lemma4RightmostInitiatorAgedSurvivalRow_of_survivalStateLocalResidual
    (hlocal :
      Lemma4RightmostInitiatorSurvivalStateLocalResidual) :
    Lemma4RightmostInitiatorAgedSurvivalRow := by
  unfold Lemma4RightmostInitiatorAgedSurvivalRow
  intro n psi kappa hpsi
  intro ring k kind step G e x z
  intro hCd hCd' hcovered hsound _huniq _hkin
  intro _hnoPrior _hage hright htrack hsame
  exact
    hlocal
      hpsi ring k kind step G e x z
      hCd hCd' hcovered hsound
      hright htrack hsame

theorem lemma4RightmostInitiatorAgedNoPriorCompletionRow_of_stateLocalResiduals
    (hTerminal :
      Lemma4RightmostInitiatorTerminalStateLocalResidual)
    (hSurvival :
      Lemma4RightmostInitiatorSurvivalStateLocalResidual) :
    Lemma4RightmostInitiatorAgedNoPriorCompletionRow :=
  lemma4RightmostInitiatorAgedNoPriorCompletionRow_of_local_rows
    (lemma4RightmostInitiatorAgedSurvivalRow_of_survivalStateLocalResidual
      hSurvival)
    (lemma4RightmostInitiatorAgedTerminalRow_of_terminalStateLocalResidual
      hTerminal)

end PPL

#print axioms PPL.lemma4RightmostInitiatorAgedTerminalRow_of_terminalStateLocalResidual
#print axioms PPL.lemma4RightmostInitiatorAgedSurvivalRow_of_survivalStateLocalResidual
#print axioms PPL.lemma4RightmostInitiatorAgedNoPriorCompletionRow_of_stateLocalResiduals
