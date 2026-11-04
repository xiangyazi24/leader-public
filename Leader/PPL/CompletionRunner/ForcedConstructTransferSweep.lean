import Leader.PPL.CompletionRunner.ForcedConstructTransfer
import Leader.PPL.TokenCompletion.StepPropsClosed

/-!
# Step-parametric Lemma 4: scoped prime `SweepMissingRows`

The ordinary producer `lemma4SweepMissingRows_of_literal` (SweepRows:603)
consumes its run hypothesis only through `GhostSound G`,
`GhostIdsUniqueAt pre.length G` and `Lemma4FreshKinematics ring k G`
(SweepRows:616-634).  Everything after that is state-local: the private
adapters `lemma4SweepInitiator_of_literal` (:518),
`lemma4SweepResponder_of_literal` (:554) and `lemma4SweepOwnerFrame` (:427),
and the three closed literal rows.

1. `ordSweep_ofFacts`: the ordinary assembly for an arbitrary `G` and clock
   `step` carrying those three facts (no run hypothesis);
2. `primeSweep_ofFacts`: the same conclusion for `ghostStepPrime`, through
   the one-step bridge under `PreludeAgree` (the conclusion reads the
   post-state through the ghost maps, the completion log, `ValidToken` and
   `lemma4TokenProgress` only);
3. `prime_sweepMissingRows_scoped`: along prime runs from
   `L18RiskySweepPrefix2 ring root psi C0` (`3 ≤ n`, `psi < n`), the three
   facts and `PreludeAgree` come from `PrimeRunInv`.
-/

namespace PPL
namespace Lemma4Generic

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL.Convergence.L18

/-! ## 1. Transfer helpers -/

/-- `HasFreshCompletion` reads only the completion log. -/
theorem hasFreshCompletion_of_completed {n psi kappa : Nat} (kind : TokenKind)
    (k : Fin n) {G G' : GhostConfig n psi kappa} (h : G.completed = G'.completed) :
    HasFreshCompletion kind k G ↔ HasFreshCompletion kind k G' := by
  unfold HasFreshCompletion
  rw [h]

/-- The bridge, with the completion log. -/
theorem prime_ordinary_views' {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (t : Nat) (G : GhostConfig n psi kappa) (e : Fin n)
    (hpre : PreludeAgree hpsi (G.phys e) (G.phys (ring.rightNeighbor e))) :
    (ghostStepPrime hpsi ring t G e).completed =
      (ghostStep hpsi ring t G e).completed :=
  (ghostStepPrime_bridge hpsi ring t G e hpre).2.2.1

/-- `Lemma4RightmostAt` reads the ghost map and `ValidToken`. -/
theorem rightmostAt_transfer {n psi kappa : Nat} {ring : DirectedRing n} {k : Fin n}
    {kind : TokenKind} {G G' : GhostConfig n psi kappa}
    (hown : ∀ j, ghostTokenAt kind G' j = ghostTokenAt kind G j)
    (hag : ∀ j, PhysAgree (G'.phys j) (G.phys j))
    (x : Fin (2 * psi)) (z : GhostToken n psi)
    (h : Lemma4RightmostAt ring k kind G x z) :
    Lemma4RightmostAt ring k kind G' x z := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(hown _).trans h1, (validToken_of_physAgree hag kind _).2 h2, ?_⟩
  intro y hy
  exact (hown _).trans (h3 y hy)

/-! ## 2. Ordinary assembly without the run hypothesis -/

/-- The ordinary `SweepMissingRows` assembly for an arbitrary `G` and clock
`step` carrying soundness, ID uniqueness and fresh kinematics. -/
theorem ordSweep_ofFacts {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n) (hsound : GhostSound G)
    (huniq : GhostIdsUniqueAt step G) (hkin : Lemma4FreshKinematics ring k G)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (ghostStep hpsi ring step G e).phys)
    (hcovered : Lemma4GhostCoveredWindow ring k kind G) :
    (∀ (i : Fin n) (z : GhostToken n psi),
        Lemma4InWindow ring k psi i →
        ghostTokenAt kind G i = some z →
        Lemma4SweepOwnerOutcome hpsi ring k kind step G e i z) ∧
      ((¬ ∃ i : Fin n, ∃ z : GhostToken n psi,
          Lemma4InWindow ring k psi i ∧ ghostTokenAt kind G i = some z) →
        e = k →
        HasFreshCompletion kind k (ghostStep hpsi ring step G e) ∨
          ∃ x : Fin (2 * psi), ∃ z : GhostToken n psi,
            Lemma4RightmostAt ring k kind (ghostStep hpsi ring step G e) x z ∧
              FreshAt kind k z.lmeta) := by
  have hn2 : 2 ≤ n :=
    (privc% Leader.PPL.TokenCompletion.SweepRows PPL.lemma4SweepCd_two_le_n)
      hpsi ring k kind G.phys hCd
  constructor
  · intro i z hwin howner
    by_cases hie : i = e
    · subst i
      exact (privc% Leader.PPL.TokenCompletion.SweepRows
          PPL.lemma4SweepInitiator_of_literal)
        lemma4SweepInitiatorLiteralCases_closed
        hpsi ring k kind step G e z hn2 hCd hCd' hcovered hsound huniq hkin
        hwin howner
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        exact (privc% Leader.PPL.TokenCompletion.SweepRows
            PPL.lemma4SweepResponder_of_literal)
          lemma4SweepResponderLiteralCases_closed
          hpsi ring k kind step G e z hn2 hCd hCd' hcovered hsound huniq hkin
          hwin howner
      · exact (privc% Leader.PPL.TokenCompletion.SweepRows
            PPL.lemma4SweepOwnerFrame)
          hpsi ring k kind step G e i z hsound hwin howner hie hir
  · intro hempty hek
    exact lemma4SweepEmptyBirthLiteralCases_proved hpsi ring k kind step G e
      hCd hCd' hcovered hsound huniq hkin hempty hek

/-! ## 3. Prime transfer -/

/-- Prime `SweepMissingRows` body for an arbitrary `G` with the three facts
and `PreludeAgree` on the selected pair. -/
theorem primeSweep_ofFacts {n psi kappa : Nat} (hpsi : 2 ≤ psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind) (step : Nat)
    (G : GhostConfig n psi kappa) (e : Fin n) (hsound : GhostSound G)
    (huniq : GhostIdsUniqueAt step G) (hkin : Lemma4FreshKinematics ring k G)
    (hpre : PreludeAgree hpsi (G.phys e) (G.phys (ring.rightNeighbor e)))
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (ghostStepPrime hpsi ring step G e).phys)
    (hcovered : Lemma4GhostCoveredWindow ring k kind G) :
    let G' := ghostStepPrime hpsi ring step G e
    And
      (forall (i : Fin n) (z : GhostToken n psi),
        Lemma4InWindow ring k psi i ->
        ghostTokenAt kind G i = some z ->
        Or
          (forall (j : Fin n) (z' : GhostToken n psi),
            ghostTokenAt kind G' j = some z' ->
            z'.lmeta.id ≠ z.lmeta.id)
          (Or
            (HasFreshCompletion kind k G')
            (exists j : Fin n, exists z' : GhostToken n psi,
              And
                (Lemma4InWindow ring k psi j)
                (And
                  (ghostTokenAt kind G' j = some z')
                  (And
                    (z'.lmeta.id = z.lmeta.id)
                    (And
                      (FreshAt kind k z.lmeta ->
                        FreshAt kind k z'.lmeta)
                      (And
                        (ValidToken kind G'.phys j)
                        (And
                          (lemma4TokenProgress
                              kind (G.phys i) z.value <=
                            lemma4TokenProgress
                              kind (G'.phys j) z'.value)
                          (e =
                              lemma4ServiceEdge
                                ring kind G i z ->
                            lemma4TokenProgress
                                kind (G'.phys j) z'.value =
                              lemma4TokenProgress
                                kind (G.phys i) z.value + 1)))))))))
      (Not
          (exists i : Fin n, exists z : GhostToken n psi,
            And
              (Lemma4InWindow ring k psi i)
              (ghostTokenAt kind G i = some z)) ->
        e = k ->
        Or
          (HasFreshCompletion kind k G')
          (exists x : Fin (2 * psi),
            exists z : GhostToken n psi,
              And
                (Lemma4RightmostAt ring k kind G' x z)
                (FreshAt kind k z.lmeta))) := by
  obtain ⟨hown, hag⟩ := prime_ordinary_views hpsi ring step G e hpre kind
  have hcomp := prime_ordinary_views' hpsi ring step G e hpre
  have hCdO : Cd ring k kind (ghostStep hpsi ring step G e).phys :=
    cd_of_physAgree hag hCd'
  obtain ⟨h1, h2⟩ := ordSweep_ofFacts hpsi ring k kind step G e hsound huniq hkin
    hCd hCdO hcovered
  have hP : ∀ j v, lemma4TokenProgress kind ((ghostStepPrime hpsi ring step G e).phys j) v =
      lemma4TokenProgress kind ((ghostStep hpsi ring step G e).phys j) v :=
    fun j v => progress_of_dist kind (hag j).2.2.1 v
  have hF := hasFreshCompletion_of_completed kind k hcomp
  dsimp only
  constructor
  · intro i z hwin howner
    have hO := h1 i z hwin howner
    unfold Lemma4SweepOwnerOutcome at hO
    rcases hO with hgone | hdone | ⟨j, z', hjwin, hjown, hid, hfr, hvalid, hle, hserv⟩
    · left
      intro j z' hj
      exact hgone j z' ((hown j).symm.trans hj)
    · exact Or.inr (Or.inl (hF.2 hdone))
    · refine Or.inr (Or.inr ⟨j, z', hjwin, (hown j).trans hjown, hid, hfr,
        (validToken_of_physAgree hag kind j).2 hvalid, ?_, ?_⟩)
      · rw [hP]
        exact hle
      · intro hedge
        rw [hP]
        exact hserv hedge
  · intro hempty hek
    rcases h2 hempty hek with hdone | ⟨x, z, hR, hfr⟩
    · exact Or.inl (hF.2 hdone)
    · exact Or.inr ⟨x, z, rightmostAt_transfer hown hag x z hR, hfr⟩

/-- Scoped prime `SweepMissingRows` (`SweepMissingRows primeRunner` body)
along prime runs from an `L18RiskySweepPrefix2 … psi` configuration. -/
theorem prime_sweepMissingRows_scoped {n psi kappa : Nat} (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi) (hlt : psi < n) (ring : DirectedRing n) (root k : Fin n)
    (kind : TokenKind) (C0 : Config n psi kappa)
    (h0 : L18RiskySweepPrefix2 ring root psi C0)
    (pre : DetSchedule n) (G : GhostConfig n psi kappa) (e : Fin n)
    (hrun : G = primeRunner.run hpsi ring 0 (initialGhost C0) pre)
    (hCd : Cd ring k kind G.phys)
    (hCd' : Cd ring k kind (primeRunner.gstep hpsi ring pre.length G e).phys)
    (hcovered : Lemma4GhostCoveredWindow ring k kind G) :
    let G' := primeRunner.gstep hpsi ring pre.length G e
    And
      (forall (i : Fin n) (z : GhostToken n psi),
        Lemma4InWindow ring k psi i ->
        ghostTokenAt kind G i = some z ->
        Or
          (forall (j : Fin n) (z' : GhostToken n psi),
            ghostTokenAt kind G' j = some z' ->
            z'.lmeta.id ≠ z.lmeta.id)
          (Or
            (HasFreshCompletion kind k G')
            (exists j : Fin n, exists z' : GhostToken n psi,
              And
                (Lemma4InWindow ring k psi j)
                (And
                  (ghostTokenAt kind G' j = some z')
                  (And
                    (z'.lmeta.id = z.lmeta.id)
                    (And
                      (FreshAt kind k z.lmeta ->
                        FreshAt kind k z'.lmeta)
                      (And
                        (ValidToken kind G'.phys j)
                        (And
                          (lemma4TokenProgress
                              kind (G.phys i) z.value <=
                            lemma4TokenProgress
                              kind (G'.phys j) z'.value)
                          (e =
                              lemma4ServiceEdge
                                ring kind G i z ->
                            lemma4TokenProgress
                                kind (G'.phys j) z'.value =
                              lemma4TokenProgress
                                kind (G.phys i) z.value + 1)))))))))
      (Not
          (exists i : Fin n, exists z : GhostToken n psi,
            And
              (Lemma4InWindow ring k psi i)
              (ghostTokenAt kind G i = some z)) ->
        e = k ->
        Or
          (HasFreshCompletion kind k G')
          (exists x : Fin (2 * psi),
            exists z : GhostToken n psi,
              And
                (Lemma4RightmostAt ring k kind G' x z)
                (FreshAt kind k z.lmeta))) := by
  have hI : PrimeRunInv ring root pre.length G := by
    rw [hrun]
    exact primeRunInv_of_run hn3 hpsi hlt ring root C0 h0 pre
  exact primeSweep_ofFacts hpsi ring k kind pre.length G e hI.2.1 hI.2.2.1
    (hI.2.2.2.1 k) (preludeAgree_of_CDLAt hpsi ring root G.phys e hI.1.1)
    hCd hCd' hcovered

end Lemma4Generic
end PPL

#print axioms PPL.Lemma4Generic.ordSweep_ofFacts
#print axioms PPL.Lemma4Generic.primeSweep_ofFacts
#print axioms PPL.Lemma4Generic.prime_sweepMissingRows_scoped
