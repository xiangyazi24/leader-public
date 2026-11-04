import Leader.PPL.TokenCompletion.RightmostResponder
import Leader.PPL.TokenCompletion.GhostStepMirror
import Leader.PPL.TokenCompletion.RunFacts
import Leader.PPL.TransitionFacts




namespace PPL




set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false




/--
Finite literal selected-pair row.


This is deliberately stronger than the final rightmost conclusion in one
useful way: it records which of the three responder offset cases occurred.
There is no schedule induction here.


The collision case is included implicitly in every branch: when both
selected-colour endpoints carry a token, Algorithm 3 deletes the left
contender before the responder-side moveLeft split, so the tracked right
responder still follows the same offset case below.
-/
def Lemma4RightmostResponderSelectedPairCases : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi),
    Cd ring k kind G.phys ->
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys ->
    Lemma4GhostCoveredWindow ring k kind G ->
    GhostSound G ->
    GhostIdsUniqueAt step G ->
    Lemma4FreshKinematics ring k G ->
    Lemma4RightmostAt ring k kind G x z ->
    ring.rightNeighbor e =
      shiftRight ring k x.val ->
    let i := shiftRight ring k x.val
    let G' := ghostStep hpsi ring step G e
    let c := decodeOffset psi (tokenCode z.value)
    Or
      (And
        (0 < c)
        (And
          (Lemma4RightmostAt ring k kind G' x z)
          (And
            (lemma4TokenProgress kind
                (G.phys i) z.value <=
              lemma4TokenProgress kind
                (G'.phys (shiftRight ring k x.val))
                z.value)
            (e =
                lemma4ServiceEdge ring kind G i z ->
              lemma4TokenProgress kind
                  (G'.phys (shiftRight ring k x.val))
                  z.value =
                lemma4TokenProgress kind
                    (G.phys i) z.value +
                  1))))
      (Or
        (And
          (c = -1)
          (exists y : Fin (2 * psi),
            exists z' : GhostToken n psi,
              And
                (Lemma4RightmostAt
                  ring k kind G' y z')
                (And
                  (z'.lmeta.id = z.lmeta.id)
                  (And
                    (FreshAt kind k z.lmeta ->
                      FreshAt kind k z'.lmeta)
                    (And
                      (lemma4TokenProgress kind
                          (G.phys i) z.value <=
                        lemma4TokenProgress kind
                          (G'.phys
                            (shiftRight ring k y.val))
                          z'.value)
                      (e =
                          lemma4ServiceEdge
                            ring kind G i z ->
                        lemma4TokenProgress kind
                            (G'.phys
                              (shiftRight ring k y.val))
                            z'.value =
                          lemma4TokenProgress kind
                              (G.phys i) z.value +
                            1))))))
        (And
          (c <= -2)
          (exists y : Fin (2 * psi),
            exists z' : GhostToken n psi,
              And
                (Lemma4RightmostAt
                  ring k kind G' y z')
                (And
                  (z'.lmeta.id = z.lmeta.id)
                  (And
                    (FreshAt kind k z.lmeta ->
                      FreshAt kind k z'.lmeta)
                    (And
                      (lemma4TokenProgress kind
                          (G.phys i) z.value <=
                        lemma4TokenProgress kind
                          (G'.phys
                            (shiftRight ring k y.val))
                          z'.value)
                      (e =
                          lemma4ServiceEdge
                            ring kind G i z ->
                        lemma4TokenProgress kind
                            (G'.phys
                              (shiftRight ring k y.val))
                            z'.value =
                          lemma4TokenProgress kind
                              (G.phys i) z.value +
                            1)))))))




/--
Once the finite selected-pair classification is available, the public
rightmost-responder literal leaf is immediate.  The responder never needs
the deletion or completion disjunct: all three literal offset cases retain
the same lineage as a rightmost survivor.
-/
theorem lemma4RightmostResponderLiteralCases_of_selectedPairCases
    (hcases : Lemma4RightmostResponderSelectedPairCases) :
    Lemma4RightmostResponderLiteralCases := by
  unfold Lemma4RightmostResponderLiteralCases
  intro n psi kappa hpsi
  intro ring k kind step G e x z
  intro hCd hCd' hcovered hsound huniq hkin
  intro hright htrack
  dsimp only


  have h :=
    hcases
      hpsi ring k kind step G e x z
      hCd hCd' hcovered hsound huniq hkin
      hright htrack
  dsimp only at h


  rcases h with hpos | hrest
  · rcases hpos with
      ⟨_hc, hrightPost, hmono, hservice⟩
    exact
      Or.inr
        (Or.inr
          ⟨x, z,
            hrightPost,
            rfl,
            (fun hfresh => hfresh),
            hmono,
            hservice⟩)


  · rcases hrest with hturn | hneg
    · rcases hturn with
        ⟨_hc, y, z', hrightPost,
          hid, hfresh, hmono, hservice⟩
      exact
        Or.inr
          (Or.inr
            ⟨y, z',
              hrightPost,
              hid,
              hfresh,
              hmono,
              hservice⟩)


    · rcases hneg with
        ⟨_hc, y, z', hrightPost,
          hid, hfresh, hmono, hservice⟩
      exact
        Or.inr
          (Or.inr
            ⟨y, z',
              hrightPost,
              hid,
              hfresh,
              hmono,
              hservice⟩)




end PPL




#print axioms PPL.lemma4RightmostResponderLiteralCases_of_selectedPairCases
