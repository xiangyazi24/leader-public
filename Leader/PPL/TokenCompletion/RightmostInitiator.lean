import Leader.PPL.TokenCompletion.RunFacts
import Leader.PPL.TokenCompletion.CoverageRows
import Leader.PPL.TokenCompletion.RightmostRows

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
A source `C_d` window with `psi >= 2` cannot live on the singleton ring:
window coordinates 0 and 1 would be the same physical site but `C_d` assigns
them distinct `dist` values.  This is exactly the small-size fact needed by
`ghostIdsUnique_run`; no global fit hypothesis is added to the leaf.
-/
private theorem lemma4Cd_two_le_n
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
Exact state-local literal initiator row.

Compared with the earlier row, this has no fabricated `hn4` or `hfit` binders, and
the post-`C_d` hypothesis is the actual physical state of `ghostStep`.
The three run-history facts are explicit local hypotheses; in particular ID
uniqueness is retained because the deletion disjunct can need it.
The conclusion is the public unfolded equivalent of the private
`rightmostRowsOutcome` used by `Lemma4RightmostInitiatorBranch`.
-/
def Lemma4RightmostInitiatorLiteralCases : Prop :=
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
Adapter from the exact public initiator leaf to the finite literal row.

`GhostSound` and fresh-lineage kinematics come from the actual ghost run.
For ID uniqueness, `C_d` first supplies `2 <= n`, after which the compiled
`ghostIdsUnique_run` theorem applies.
-/
theorem lemma4RightmostInitiatorBranch_of_literalCases
    (hsound : Lemma4CoverageGhostRunSound)
    (hliteral : Lemma4RightmostInitiatorLiteralCases) :
    Lemma4RightmostInitiatorBranch := by
  unfold Lemma4RightmostInitiatorBranch
  intro n psi kappa hpsi
  intro ring k kind C0 pre G e x z
  intro hG hCd hCd' hcovered hright htrack

  have hsoundG : GhostSound G := by
    rw [hG]
    exact hsound hpsi ring C0 pre

  have hn2 : 2 ≤ n :=
    lemma4Cd_two_le_n
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

end PPL

#print axioms PPL.lemma4RightmostInitiatorBranch_of_literalCases
