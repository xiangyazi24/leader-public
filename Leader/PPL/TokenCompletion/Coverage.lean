import Leader.PPL.TokenCompletion.HalfPowerDynamics
import Leader.PPL.TransitionFacts

namespace PPL

set_option autoImplicit false
set_option Elab.async false

/-!
# Lemma 4 coverage step

Truth audit.

The old revived-unowned-token witness has pre-distances [0,0,2,3] for
psi=2, black, k=0, so it is not C_d: C_d requires [0,1,2,3].
Under both pre- and post-C_d, every in-window dist/last pair is equal across
the interaction. Algorithm 3 preserves those fields (the public
moveToken_* projections below), and Algorithm 5 also frames them. Therefore
an in-window invalid raw token cannot be made valid by a transient Algorithm-2
dist write and then survive to the post-state.

The only finite row work left in this bounded round is at the two touched
sites.  It has two logically separate outputs:

* post-valid selected-color physical coverage;
* ancestry of a post selected-color owner (fresh at k, or descended from an
  in-window pre-owner).

Both are exact one-interaction endpoint facts.  Everything else is proved
below.
-/

/-! ## 1. Initial ownership mirror -/

private def coverageLocalValid {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  Or
    (And (0 < c)
      (And (((psi : Nat) : Int) <= target)
        (target <= (((2 * psi - 1 : Nat)) : Int))))
    (And (c < 0)
      (And (1 <= target)
        (target <= (((psi - 1 : Nat)) : Int))))

private instance instDecidableCoverageLocalValid
    {psi kappa : Nat}
    (kind : TokenKind) (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (coverageLocalValid kind q t) := by
  unfold coverageLocalValid
  infer_instance

private noncomputable def coverageInitialOwned
    {n psi kappa : Nat}
    (kind : TokenKind) (C : Config n psi kappa)
    (i : Fin n) : Option (GhostToken n psi) := by
  classical
  exact
    match tokenAt kind (C i) with
    | none => none
    | some t =>
        if coverageLocalValid kind (C i) t then
          some
            { value := t
              lmeta :=
                { id := .initial kind i
                  birthSite := i
                  birthStep := 0
                  moves := 0 } }
        else
          none

private theorem ghostTokenAt_initial_eq_coverage
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (kind : TokenKind) (i : Fin n) :
    ghostTokenAt kind (initialGhost C) i =
      coverageInitialOwned kind C i := by
  cases kind <;> rfl

private theorem lemma4InitialGhostCovered
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (C : Config n psi kappa) :
    Lemma4GhostCoveredWindow ring k kind (initialGhost C) := by
  classical
  intro i _hwin hvalid
  change ValidToken kind C i at hvalid
  unfold ValidToken at hvalid
  cases ht : tokenAt kind (C i) with
  | none =>
      rw [ht] at hvalid
      exact False.elim hvalid
  | some t =>
      rw [ht] at hvalid
      dsimp only at hvalid
      have hlocal :
          coverageLocalValid kind (C i) t := by
        exact hvalid
      let z : GhostToken n psi :=
        { value := t
          lmeta :=
            { id := .initial kind i
              birthSite := i
              birthStep := 0
              moves := 0 } }
      refine ⟨z, ?_⟩
      rw [ghostTokenAt_initial_eq_coverage]
      simp [coverageInitialOwned, ht, hlocal, z]

/-! ## 2. C_d freezes in-window geometry -/

private theorem lemma4CdWindowGeometryEq
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind)
    (C C' : Config n psi kappa)
    (hC : Cd ring k kind C)
    (hC' : Cd ring k kind C')
    (i : Fin n)
    (hi : Lemma4InWindow ring k psi i) :
    And
      ((C i).dist = (C' i).dist)
      ((C i).last = (C' i).last) := by
  rcases hi with ⟨x, rfl⟩
  have h0 := hC x
  have h1 := hC' x
  dsimp only at h0 h1
  constructor
  · apply Fin.ext
    exact h0.1.trans h1.1.symm
  · exact h0.2.trans h1.2.symm

/-! ## 3. Public Algorithm-3 field adapters -/

private theorem lemma4MoveTokenDistLast
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    And
      (And
        ((moveToken hpsi kind l r).1.dist = l.dist)
        ((moveToken hpsi kind l r).1.last = l.last))
      (And
        ((moveToken hpsi kind l r).2.dist = r.dist)
        ((moveToken hpsi kind l r).2.last = r.last)) := by
  have hi :=
    moveToken_initiator_fields hpsi kind l r
  rcases
      moveToken_responder_fields hpsi kind l r with
    hr | hr
  · cases kind <;>
      simp_all [eraseKindToken, eraseKindTokenId]
  · cases kind <;>
      simp_all
        [eraseKindToken, eraseKindTokenId, birthFields]

private theorem lemma4MoveTokenView4Cases
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (kind : TokenKind)
    (l r : State psi kappa) :
    And
      (PPL.Elim.view4 (moveToken hpsi kind l r).1 =
        PPL.Elim.view4 l)
      (Or
        (PPL.Elim.view4 (moveToken hpsi kind l r).2 =
          PPL.Elim.view4 r)
        (PPL.Elim.view4 (moveToken hpsi kind l r).2 =
          (⟨true, (2 : Fin 3), true, false⟩ :
            PPL.Elim.Cell4))) := by
  exact moveToken_view4_cases hpsi kind l r

/-! ## 4. Untouched-site facts -/

private theorem lemma4GhostStepPhysOther
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (hie : i ≠ e)
    (hir : i ≠ ring.rightNeighbor e) :
    (ghostStep hpsi ring step G e).phys i =
      G.phys i := by
  change
    (if i = e then _
      else if i = ring.rightNeighbor e then _
      else G.phys i) =
      G.phys i
  rw [if_neg hie, if_neg hir]

private theorem lemma4GhostStepOwnerOther
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (kind : TokenKind)
    (hie : i ≠ e)
    (hir : i ≠ ring.rightNeighbor e) :
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) i =
      ghostTokenAt kind G i := by
  cases kind with
  | black =>
      change
        (if i = e then _
          else if i = ring.rightNeighbor e then _
          else G.black i) =
        G.black i
      rw [if_neg hie, if_neg hir]
  | white =>
      change
        (if i = e then _
          else if i = ring.rightNeighbor e then _
          else G.white i) =
        G.white i
      rw [if_neg hie, if_neg hir]

/-!
## 5. The two finite touched-endpoint residuals

These are strictly smaller than Lemma4CoverageStep.

They contain:
* no initial-ghost branch;
* no off-pair site;
* no schedule induction;
* no probability or source-correctness predicate.

The intended proof is the finite expansion of the selected-color
ghostMoveToken row.  Use pre/post C_d plus lemma4CdWindowGeometryEq to rule
out the revived-unowned case, moveToken_initiator_fields /
moveToken_responder_fields for physical framing, and moveToken_view4_cases
for the responder birth alternative.  At the two window boundaries,
Definition-3 validity sends a crossing token into the wrong validity band, so
bumpTo drops the owner.
-/

/-- Every post-valid selected-color token at a touched in-window endpoint
has a post ghost owner. -/
def Lemma4CoverageTouchedCoverage : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n),
    Cd ring k kind G.phys ->
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys ->
    Lemma4GhostCoveredWindow ring k kind G ->
    Or (i = e) (i = ring.rightNeighbor e) ->
    Lemma4InWindow ring k psi i ->
    ValidToken kind
      (ghostStep hpsi ring step G e).phys i ->
    exists z : GhostToken n psi,
      ghostTokenAt kind
        (ghostStep hpsi ring step G e) i =
      some z

/-- Every touched in-window post owner is either the fresh birth at k or
descends from an in-window pre-owner with the same lineage id. -/
def Lemma4CoverageTouchedOrigin : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi),
    Cd ring k kind G.phys ->
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys ->
    Or (i = e) (i = ring.rightNeighbor e) ->
    Lemma4InWindow ring k psi i ->
    ghostTokenAt kind
        (ghostStep hpsi ring step G e) i =
      some z ->
    Or
      (FreshAt kind k z.lmeta)
      (exists j z0,
        And
          (Lemma4InWindow ring k psi j)
          (And
            (ghostTokenAt kind G j = some z0)
            (z.lmeta.id = z0.lmeta.id)))

/-! ## 6. Full coverage-step assembly -/

theorem lemma4CoverageStep
    (htouched : Lemma4CoverageTouchedCoverage)
    (horigin : Lemma4CoverageTouchedOrigin) :
    Lemma4CoverageStep := by
  intro n psi kappa hpsi ring k kind
  constructor
  · intro C _hCd
    exact
      lemma4InitialGhostCovered
        ring k kind C
  · intro C0 pre G e _hrun
    intro hCd hCd' hcovered
    dsimp only
    constructor
    · intro i hiwin hvalid
      by_cases hie : i = e
      · exact
          htouched
            hpsi ring k kind pre.length
            G e i hCd hCd' hcovered
            (Or.inl hie) hiwin hvalid
      · by_cases hir :
          i = ring.rightNeighbor e
        · exact
            htouched
              hpsi ring k kind pre.length
              G e i hCd hCd' hcovered
              (Or.inr hir) hiwin hvalid
        · have hphys :=
            lemma4GhostStepPhysOther
              hpsi ring pre.length G e i
              hie hir
          have hvalid0 :
              ValidToken kind G.phys i := by
            unfold ValidToken at hvalid ⊢
            rw [hphys] at hvalid
            exact hvalid
          obtain ⟨z, hz⟩ :=
            hcovered i hiwin hvalid0
          refine ⟨z, ?_⟩
          rw [
            lemma4GhostStepOwnerOther
              hpsi ring pre.length
              G e i kind hie hir]
          exact hz
    · intro i z hiwin howner
      by_cases hie : i = e
      · exact
          horigin
            hpsi ring k kind pre.length
            G e i z hCd hCd'
            (Or.inl hie) hiwin howner
      · by_cases hir :
          i = ring.rightNeighbor e
        · exact
            horigin
              hpsi ring k kind pre.length
              G e i z hCd hCd'
              (Or.inr hir) hiwin howner
        · have howner0 :
              ghostTokenAt kind G i = some z := by
            rw [
              ← lemma4GhostStepOwnerOther
                hpsi ring pre.length
                G e i kind hie hir]
            exact howner
          exact
            Or.inr
              ⟨i, z, hiwin, howner0, rfl⟩

end PPL

#print axioms PPL.lemma4CoverageStep
#check PPL.Lemma4CoverageTouchedCoverage
#check PPL.Lemma4CoverageTouchedOrigin
