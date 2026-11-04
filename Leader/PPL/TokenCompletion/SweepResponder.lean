import Leader.PPL.TokenCompletion.SweepRows
import Leader.PPL.TokenCompletion.GhostStepMirror

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Public responder equation in the exact form used by the local row audit.
This includes the singleton alias case.
-/
theorem sweepResponderPost_eq_selectedPair
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e)
        (ring.rightNeighbor e) =
      if ring.rightNeighbor e = e then
        (ghostStepSelectedPair
          hpsi ring step G e kind).left
      else
        (ghostStepSelectedPair
          hpsi ring step G e kind).right := by
  exact
    ghostTokenAt_ghostStep_responder
      hpsi ring step G e kind

/--
Non-singleton responder specialization.  This is the exact bridge from a
selected-pair right survivor to the global post-step responder owner.
-/
theorem sweepResponderPost_eq_selectedPair_of_ne
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (kind : TokenKind)
    (hne : ring.rightNeighbor e ≠ e) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e)
        (ring.rightNeighbor e) =
      (ghostStepSelectedPair
        hpsi ring step G e kind).right := by
  exact
    ghostTokenAt_ghostStep_responder_of_ne
      hpsi ring step G e kind hne

/--
The only branch not closed in this bounded round.

If either selected-pair output still carries the tracked responder lineage,
then the step must satisfy the non-deletion part of
`Lemma4SweepPairOwnerResult`: either a completion was logged, or a same-ID
in-window survivor has the required freshness, validity, monotone progress,
and exact service progress.

The literal branch split is only:
* responder live-shadow stay;
* `c = -1` responder-to-initiator turn to `+psi`;
* `c ≤ -2` responder-to-initiator move to `c+1`.

A same-color collision deletes the left contender, not the tracked responder.
The `c=-1` turn lands in the positive validity band under pre/post `C_d`;
the ordinary negative move preserves the target coordinate.
-/
def Lemma4SweepResponderSameIdBranch : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    GhostSound G →
    GhostIdsUniqueAt step G →
    Lemma4FreshKinematics ring k G →
    Lemma4InWindow ring k psi
      (ring.rightNeighbor e) →
    ghostTokenAt kind G (ring.rightNeighbor e) =
      some z →
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
    HasFreshCompletion kind k
        (ghostStep hpsi ring step G e) ∨
      ∃ j : Fin n, ∃ z' : GhostToken n psi,
        Lemma4InWindow ring k psi j ∧
          ((j = e ∧
              (ghostStepSelectedPair
                  hpsi ring step G e kind).left =
                some z') ∨
            (j = ring.rightNeighbor e ∧
              (ghostStepSelectedPair
                  hpsi ring step G e kind).right =
                some z')) ∧
          z'.lmeta.id = z.lmeta.id ∧
          (FreshAt kind k z.lmeta →
            FreshAt kind k z'.lmeta) ∧
          ValidToken kind
            (ghostStep hpsi ring step G e).phys j ∧
          lemma4TokenProgress
              kind
              (G.phys (ring.rightNeighbor e))
              z.value ≤
            lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys j)
              z'.value ∧
          (e =
              lemma4ServiceEdge
                ring kind G (ring.rightNeighbor e) z →
            lemma4TokenProgress
                kind
                ((ghostStep hpsi ring step G e).phys j)
                z'.value =
              lemma4TokenProgress
                  kind
                  (G.phys (ring.rightNeighbor e))
                  z.value +
                1)

/--
If neither selected endpoint output carries the tracked lineage ID, the
deletion disjunct of `Lemma4SweepPairOwnerResult` is immediate.
-/
theorem sweepResponderDeletion_of_no_sameId
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi)
    (hleft :
      ¬ ∃ zL : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).left =
          some zL ∧
        zL.lmeta.id = z.lmeta.id)
    (hright :
      ¬ ∃ zR : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).right =
          some zR ∧
        zR.lmeta.id = z.lmeta.id) :
    (∀ zL : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).left =
          some zL →
        zL.lmeta.id ≠ z.lmeta.id) ∧
      (∀ zR : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).right =
          some zR →
        zR.lmeta.id ≠ z.lmeta.id) := by
  constructor
  · intro zL hL hid
    exact hleft ⟨zL, hL, hid⟩
  · intro zR hR hid
    exact hright ⟨zR, hR, hid⟩

/--
Reduction of `Lemma4SweepResponderLiteralCases` to exactly one finite
same-ID responder branch.

All no-survivor collision/deletion cases are closed here.  Thus the only
remaining obligation is the literal responder stay / negative-move /
negative-turn branch recorded by `Lemma4SweepResponderSameIdBranch`.
-/
theorem lemma4SweepResponderLiteralCases_of_sameIdBranch
    (hsame : Lemma4SweepResponderSameIdBranch) :
    Lemma4SweepResponderLiteralCases := by
  unfold Lemma4SweepResponderLiteralCases
  intro n psi kappa hpsi
  intro ring k kind step G e z
  intro hCd hCd' hcovered hsound huniq hkin
  intro hwin howner

  unfold Lemma4SweepPairOwnerResult
  classical

  by_cases hleft :
      ∃ zL : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).left =
          some zL ∧
        zL.lmeta.id = z.lmeta.id
  · exact
      Or.inr
        (hsame
          hpsi ring k kind step G e z
          hCd hCd' hcovered hsound huniq hkin
          hwin howner (Or.inl hleft))

  · by_cases hright :
        ∃ zR : GhostToken n psi,
          (ghostStepSelectedPair
              hpsi ring step G e kind).right =
            some zR ∧
          zR.lmeta.id = z.lmeta.id
    · exact
        Or.inr
          (hsame
            hpsi ring k kind step G e z
            hCd hCd' hcovered hsound huniq hkin
            hwin howner (Or.inr hright))

    · exact
        Or.inl
          (sweepResponderDeletion_of_no_sameId
            hpsi ring kind step G e z
            hleft hright)

end PPL

#print axioms PPL.sweepResponderPost_eq_selectedPair
#print axioms PPL.sweepResponderPost_eq_selectedPair_of_ne
#print axioms PPL.sweepResponderDeletion_of_no_sameId
#print axioms PPL.lemma4SweepResponderLiteralCases_of_sameIdBranch
