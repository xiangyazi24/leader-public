import Leader.PPL.TokenCompletion.SweepRows
import Leader.PPL.TokenCompletion.GhostStepMirror


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/--
The only branch not closed in this bounded round.


If either selected-pair output still carries the tracked lineage id, then the
step must already satisfy the non-deletion part of Lemma4SweepPairOwnerResult:
either a fresh completion was logged, or a same-id in-window survivor has
preserved freshness/validity and the required progress inequalities.


All collision/deletion cases are discharged by the reduction below.  In
particular, no fresh/nonfresh distinction is needed for deletion in the sweep
interface.
-/
def Lemma4SweepInitiatorSameIdBranch : Prop :=
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
    Lemma4InWindow ring k psi e →
    ghostTokenAt kind G e = some z →
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
              kind (G.phys e) z.value ≤
            lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys j)
              z'.value ∧
          (e = lemma4ServiceEdge ring kind G e z →
            lemma4TokenProgress
                kind
                ((ghostStep hpsi ring step G e).phys j)
                z'.value =
              lemma4TokenProgress
                  kind (G.phys e) z.value +
                1)


/--
If neither endpoint output has the tracked id, the deletion branch of
Lemma4SweepPairOwnerResult is immediate.
-/
private theorem sweepInitiatorDeletion_of_no_sameId
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
Reduction of the requested sweep-initiator row to exactly one selected-pair
same-id branch.


The two no-tracked-id-survives cases are closed here.  Thus the remaining
residual contains no deletion/collision bookkeeping: it is only the branch in
which the tracked lineage survives one of the two selected outputs.
-/
theorem lemma4SweepInitiatorLiteralCases_of_sameIdBranch
    (hsame : Lemma4SweepInitiatorSameIdBranch) :
    Lemma4SweepInitiatorLiteralCases := by
  unfold Lemma4SweepInitiatorLiteralCases
  intro n psi kappa hpsi
  intro ring k kind step G e z
  intro hCd hCd' hcovered hsound huniq hkin hwin howner


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
          (sweepInitiatorDeletion_of_no_sameId
            hpsi ring kind step G e z
            hleft hright)


end PPL


#print axioms PPL.lemma4SweepInitiatorLiteralCases_of_sameIdBranch
