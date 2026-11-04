import Leader.PPL.TokenCompletion.RightmostInitiatorAged
import Leader.PPL.TokenCompletion.GhostStepMirror

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Selected-pair deletion/collision row.

If neither selected output carries the tracked lineage ID and the tracked
rightmost owner is nonfresh, then the complete first disjunct follows.
The only nonlocal bookkeeping is excluded by pre-step lineage-ID uniqueness:
an off-pair post owner is a framed pre owner, hence cannot share the tracked
ID at a different site.
-/
def Lemma4RightmostInitiatorAgedDeletionRow : Prop :=
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
    GhostIdsUniqueAt step G →
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
    ¬ FreshAt kind k z.lmeta →
    let G' := ghostStep hpsi ring step G e
    ¬ FreshAt kind k z.lmeta ∧
      ∀ j : Fin n, ∀ z' : GhostToken n psi,
        ghostTokenAt kind G' j = some z' →
        z'.lmeta.id ≠ z.lmeta.id

/--
Selected-pair survival row.

This is the exact same-ID physical residual.  It is deliberately stated
directly in the third-disjunct form needed by the aged rightmost row.
It covers either selected endpoint retaining the tracked lineage ID.
-/
def Lemma4RightmostInitiatorAgedSurvivalRow : Prop :=
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

/--
Terminal-completion row.

This is the corrected fresh-disappearance case.  The hypotheses say that the
tracked rightmost initiator is fresh, still below the terminal move count, and
that neither selected output retains its lineage ID.  The required conclusion
is exactly that the selected move has logged a fresh completion.

The S3.9 witness fails the age premise here.
-/
def Lemma4RightmostInitiatorAgedTerminalRow : Prop :=
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
Public bookkeeping lemma mirroring the deletion half of
lemma4SweepPairResult_to_outcome.

If the tracked owner is the initiator before the step and neither selected
output carries its lineage ID, no post-step site can carry that ID.
-/
theorem rightmostInitiatorNoSameId_post
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi)
    (huniq : GhostIdsUniqueAt step G)
    (howner :
      ghostTokenAt kind G e = some z)
    (hleft :
      ∀ zL : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).left =
          some zL →
        zL.lmeta.id ≠ z.lmeta.id)
    (hright :
      ∀ zR : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).right =
          some zR →
        zR.lmeta.id ≠ z.lmeta.id) :
    ∀ j : Fin n, ∀ z' : GhostToken n psi,
      ghostTokenAt kind
          (ghostStep hpsi ring step G e) j =
        some z' →
      z'.lmeta.id ≠ z.lmeta.id := by
  intro j z' hpost hid
  by_cases hje : j = e
  · subst j
    have hout :
        (ghostStepSelectedPair
            hpsi ring step G e kind).left =
          some z' := by
      exact
        (ghostTokenAt_ghostStep_initiator
          hpsi ring step G e kind).symm.trans hpost
    exact hleft z' hout hid
  · by_cases hjr : j = ring.rightNeighbor e
    · subst j
      have hne :
          ring.rightNeighbor e ≠ e := hje
      have hout :
          (ghostStepSelectedPair
              hpsi ring step G e kind).right =
            some z' := by
        exact
          (ghostTokenAt_ghostStep_responder_of_ne
            hpsi ring step G e kind hne).symm.trans hpost
      exact hright z' hout hid
    · have hpre :
          ghostTokenAt kind G j = some z' := by
        exact
          (ghostTokenAt_ghostStep_frame
            hpsi ring step G e j kind hje hjr).symm.trans hpost
      have hji : j = e :=
        huniq.1 kind j e z' z hpre howner hid
      exact hje hji

theorem lemma4RightmostInitiatorAgedDeletionRow_proved :
    Lemma4RightmostInitiatorAgedDeletionRow := by
  unfold Lemma4RightmostInitiatorAgedDeletionRow
  intro n psi kappa hpsi
  intro ring k kind step G e x z
  intro huniq hright htrack
  intro hleft hrightOut hnotFresh
  dsimp only
  refine ⟨hnotFresh, ?_⟩

  have hrightData := hright
  unfold Lemma4RightmostAt at hrightData
  dsimp only at hrightData

  have howner :
      ghostTokenAt kind G e = some z := by
    rw [htrack]
    exact hrightData.1

  exact
    rightmostInitiatorNoSameId_post
      hpsi ring kind step G e z
      huniq howner hleft hrightOut

/--
Three-way assembly.

The selected pair is classified by whether either endpoint keeps the tracked
lineage ID.  Same-ID survival is delegated to the survival row.  If neither
endpoint keeps the ID, freshness separates ordinary deletion from the
terminal-completion case.
-/
theorem lemma4RightmostInitiatorAgedNoPriorCompletionRow_of_rows
    (hDeletion :
      Lemma4RightmostInitiatorAgedDeletionRow)
    (hSurvival :
      Lemma4RightmostInitiatorAgedSurvivalRow)
    (hTerminal :
      Lemma4RightmostInitiatorAgedTerminalRow) :
    Lemma4RightmostInitiatorAgedNoPriorCompletionRow := by
  unfold Lemma4RightmostInitiatorAgedNoPriorCompletionRow
  intro n psi kappa hpsi
  intro ring k kind step G e x z
  intro hCd hCd' hcovered hsound huniq hkin
  intro hnoPrior hage hright htrack
  classical

  by_cases hleft :
      ∃ zL : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).left =
          some zL ∧
        zL.lmeta.id = z.lmeta.id
  · dsimp only
    exact
      Or.inr
        (Or.inr
          (hSurvival
            hpsi ring k kind step G e x z
            hCd hCd' hcovered hsound huniq hkin
            hnoPrior hage hright htrack
            (Or.inl hleft)))

  · by_cases hrightOut :
        ∃ zR : GhostToken n psi,
          (ghostStepSelectedPair
              hpsi ring step G e kind).right =
            some zR ∧
          zR.lmeta.id = z.lmeta.id
    · dsimp only
      exact
        Or.inr
          (Or.inr
            (hSurvival
              hpsi ring k kind step G e x z
              hCd hCd' hcovered hsound huniq hkin
              hnoPrior hage hright htrack
              (Or.inr hrightOut)))

    · have hleftNo :
          ∀ zL : GhostToken n psi,
            (ghostStepSelectedPair
                hpsi ring step G e kind).left =
              some zL →
            zL.lmeta.id ≠ z.lmeta.id := by
        intro zL hout hid
        exact hleft ⟨zL, hout, hid⟩

      have hrightNo :
          ∀ zR : GhostToken n psi,
            (ghostStepSelectedPair
                hpsi ring step G e kind).right =
              some zR →
            zR.lmeta.id ≠ z.lmeta.id := by
        intro zR hout hid
        exact hrightOut ⟨zR, hout, hid⟩

      by_cases hfresh :
          FreshAt kind k z.lmeta
      · dsimp only
        exact
          Or.inr
            (Or.inl
              (hTerminal
                hpsi ring k kind step G e x z
                hCd hCd' hcovered hsound huniq hkin
                hnoPrior hage hright htrack
                hleftNo hrightNo hfresh))

      · dsimp only
        exact
          Or.inl
            (hDeletion
              hpsi ring k kind step G e x z
              huniq hright htrack
              hleftNo hrightNo hfresh)

theorem lemma4RightmostInitiatorAgedNoPriorCompletionRow_of_local_rows
    (hSurvival :
      Lemma4RightmostInitiatorAgedSurvivalRow)
    (hTerminal :
      Lemma4RightmostInitiatorAgedTerminalRow) :
    Lemma4RightmostInitiatorAgedNoPriorCompletionRow :=
  lemma4RightmostInitiatorAgedNoPriorCompletionRow_of_rows
    lemma4RightmostInitiatorAgedDeletionRow_proved
    hSurvival
    hTerminal

end PPL

#print axioms PPL.rightmostInitiatorNoSameId_post
#print axioms PPL.lemma4RightmostInitiatorAgedDeletionRow_proved
#print axioms PPL.lemma4RightmostInitiatorAgedNoPriorCompletionRow_of_rows
#print axioms PPL.lemma4RightmostInitiatorAgedNoPriorCompletionRow_of_local_rows
