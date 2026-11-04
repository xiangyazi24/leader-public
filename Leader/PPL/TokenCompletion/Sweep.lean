import Leader.PPL.TokenCompletion.CoverageRows
import Leader.PPL.TokenCompletion.RightmostRows

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Paper Lemma 4, source-sweep sentence:
tokens already in the C_d window are advanced by their next R/L service
interaction (or are deleted by collision), while an empty selected source
u_k creates the fresh token when its source edge is serviced.

This is deliberately one literal-interaction interface. It supplies only
the two cases not exported by Lemma4CoverageStep and
Lemma4RightmostProgressStep:
* arbitrary (not necessarily globally-rightmost) owner ancestry/freshness/
  progress through one ghostStep;
* the empty-window source-birth case at e = k.
-/
def Lemma4SweepMissingRows : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (e : Fin n),
    G = ghostRun hpsi ring 0 (initialGhost C0) pre ->
    Cd ring k kind G.phys ->
    Cd ring k kind
      (ghostStep hpsi ring pre.length G e).phys ->
    Lemma4GhostCoveredWindow ring k kind G ->
    let G' := ghostStep hpsi ring pre.length G e
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
                (FreshAt kind k z.lmeta)))

private def lemma4SweepRun
    {S E : Type}
    (step : S -> E -> S) :
    S -> List E -> S
  | s, [] => s
  | s, e :: rest =>
      lemma4SweepRun step (step s e) rest

/--
The scheduler-gap combinatorics required by both Lemma-4 clauses.

In the cons Sublist constructor, the schedule fires a non-word letter:
hskip absorbs it without consuming the prescribed word.
In cons_cons, the fired letter is the next prescribed letter:
htake consumes it.
slnil is the endpoint.
-/
theorem lemma4Sweep_sublist_induction
    {S E : Type}
    (step : S -> E -> S)
    (Inv : List E -> S -> Prop)
    (hskip :
      forall (s : S) (e : E) (word : List E),
        Inv word s ->
        Inv word (step s e))
    (htake :
      forall (s : S) (e : E) (word : List E),
        Inv (e :: word) s ->
        Inv word (step s e))
    {word schedule : List E}
    (hsub : word.Sublist schedule)
    (s : S)
    (hinv : Inv word s) :
    Inv [] (lemma4SweepRun step s schedule) := by
  induction hsub generalizing s with
  | slnil =>
      exact hinv
  | @cons l1 l2 e h ih =>
      simp only [lemma4SweepRun]
      exact
        ih (step s e)
          (hskip s e l1 hinv)
  | @cons_cons l1 l2 e h ih =>
      simp only [lemma4SweepRun]
      exact
        ih (step s e)
          (htake s e l1 hinv)

/-
The requested theorem cannot honestly be filled from the two current
interfaces alone:

theorem lemma4HalfPowerDynamicsCovered_of_steps
    (hcov : Lemma4CoverageStep)
    (hright : Lemma4RightmostProgressStep)
    (hrows : Lemma4SweepMissingRows) :
    Lemma4HalfPowerDynamicsCovered := ...

After hrows, the remaining obligation is pure source-sweep geometry:
instantiate lemma4Sweep_sublist_induction with the purge and fresh-frontier
invariants, and show that one complete
seqR(k,2*psi-1) ++ seqL(k+2*psi-1,2*psi-1)
block services every surviving lineage through one macro-stage.
No additional protocol row should be hidden in that combinatorial lemma.
-/

end PPL

#print axioms PPL.lemma4Sweep_sublist_induction
