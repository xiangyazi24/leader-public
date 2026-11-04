import Leader.PPL.TokenCompletion.RunFacts
import Leader.PPL.TokenCompletion.CoverageRows
import Leader.PPL.TokenCompletion.RightmostRows


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/--
A `C_d` window with `psi ≥ 2` cannot exist on the singleton ring.
This is the responder/off-pair copy of the helper.
-/
private theorem lemma4ResponderCd_two_le_n
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
Exact state-local literal row for the case in which the tracked rightmost
owner is the responder `ring.rightNeighbor e`.


The run history has already been converted to `GhostSound`, ID uniqueness,
and fresh-lineage kinematics.  What remains is only the selected-colour
one-interaction row.
-/
def Lemma4RightmostResponderLiteralCases : Prop :=
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
    Lemma4RightmostAt ring k kind G x z →
    ring.rightNeighbor e =
      shiftRight ring k x.val →
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
Exact state-local endpoint no-overtake row for an interaction whose two
endpoints are disjoint from the tracked rightmost owner.


Only an endpoint lying strictly to the right of the frontier is queried in the
conclusion.  The intended literal proof is birth localization plus the fact
that a valid selected-colour token outside the `2 * psi` window cannot enter
it as a valid owner.
-/
def Lemma4RightmostOffPairLiteralCases : Prop :=
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
    Lemma4RightmostAt ring k kind G x z →
    e ≠ shiftRight ring k x.val →
    ring.rightNeighbor e ≠
      shiftRight ring k x.val →
    ∀ y : Fin (2 * psi),
      x.val < y.val →
      (shiftRight ring k y.val = e ∨
        shiftRight ring k y.val =
          ring.rightNeighbor e) →
      ghostTokenAt kind
          (ghostStep hpsi ring step G e)
          (shiftRight ring k y.val) =
        none


/--
Run-history adapter for the responder branch.
-/
theorem lemma4RightmostResponderBranch_of_literalCases
    (hsound : Lemma4CoverageGhostRunSound)
    (hliteral : Lemma4RightmostResponderLiteralCases) :
    Lemma4RightmostResponderBranch := by
  unfold Lemma4RightmostResponderBranch
  intro n psi kappa hpsi
  intro ring k kind C0 pre G e x z
  intro hG hCd hCd' hcovered hright htrack


  have hsoundG : GhostSound G := by
    rw [hG]
    exact hsound hpsi ring C0 pre


  have hn2 : 2 ≤ n :=
    lemma4ResponderCd_two_le_n
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
      hsoundG huniq hkin
      hright htrack


/--
Run-history adapter for the off-pair endpoint no-overtake branch.
-/
theorem lemma4RightmostOffPairEndpointNoOvertake_of_literalCases
    (hsound : Lemma4CoverageGhostRunSound)
    (hliteral : Lemma4RightmostOffPairLiteralCases) :
    Lemma4RightmostOffPairEndpointNoOvertake := by
  unfold Lemma4RightmostOffPairEndpointNoOvertake
  intro n psi kappa hpsi
  intro ring k kind C0 pre G e x z
  intro hG hCd hCd' hcovered hright hie hir


  have hsoundG : GhostSound G := by
    rw [hG]
    exact hsound hpsi ring C0 pre


  have hn2 : 2 ≤ n :=
    lemma4ResponderCd_two_le_n
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


  exact
    hliteral
      hpsi ring k kind pre.length
      G e x z
      hCd hCd' hcovered
      hsoundG huniq hkin
      hright hie hir


end PPL


#print axioms PPL.lemma4RightmostResponderBranch_of_literalCases
#print axioms PPL.lemma4RightmostOffPairEndpointNoOvertake_of_literalCases
#check PPL.Lemma4RightmostResponderLiteralCases
#check PPL.Lemma4RightmostOffPairLiteralCases
