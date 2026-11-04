import Leader.PPL.TokenCompletion.Sweep
import Leader.PPL.TokenCompletion.HalfPowerDynamics
import Leader.PPL.TokenCompletion.SweepRows

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Missing one-step interface for the first-half purge.

Unlike `Lemma4SweepMissingRows`, this cannot discharge the tracked old-owner
obligation merely because some unrelated fresh lineage has completed.  For a
nonfresh in-window owner it exposes either actual disappearance of that
lineage ID, or an in-window same-ID survivor with the same monotone/exact
service progress data used by the sweep geometry.
-/
def Lemma4SweepOldOwnerProgressStep : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (e : Fin n),
    G = ghostRun hpsi ring 0 (initialGhost C0) pre →
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring pre.length G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    ∀ (i : Fin n) (z : GhostToken n psi),
      Lemma4InWindow ring k psi i →
      ghostTokenAt kind G i = some z →
      ¬ FreshAt kind k z.lmeta →
      let G' := ghostStep hpsi ring pre.length G e
      (∀ (j : Fin n) (z' : GhostToken n psi),
          ghostTokenAt kind G' j = some z' →
          z'.lmeta.id ≠ z.lmeta.id) ∨
        ∃ j : Fin n, ∃ z' : GhostToken n psi,
          Lemma4InWindow ring k psi j ∧
            ghostTokenAt kind G' j = some z' ∧
            z'.lmeta.id = z.lmeta.id ∧
            ValidToken kind G'.phys j ∧
            lemma4TokenProgress
                kind (G.phys i) z.value ≤
              lemma4TokenProgress
                kind (G'.phys j) z'.value ∧
            (e = lemma4ServiceEdge ring kind G i z →
              lemma4TokenProgress
                  kind (G'.phys j) z'.value =
                lemma4TokenProgress
                    kind (G.phys i) z.value +
                  1)

end PPL

#print axioms PPL.Lemma4SweepOldOwnerProgressStep
