import Leader.PPL.ReachCPB.MismatchCompletionHistSplit
import Leader.PPL.ReachCPB.MismatchHistLastFrame
import Leader.PPL.ReachCPB.MismatchHistBadBorder

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Exact residual after LastFrame, BadBorder, and the new frozen-id theorem.

The intended proof of this Prop is the missing fresh-lineage
payload/comparison-prefix induction.  A genuinely new selected fresh completion
must be the terminal c = 1 comparison.  All earlier comparisons of that
post-epoch lineage matched in the non-CPB Detect suffix; its payload is the
add-one bit of the frozen source segment; hence the fixed bad-border equation
forces this final comparison to disagree and the literal row creates a leader.
-/
def Lemma16MismatchHistNewFreshForcesCPB : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (e : Fin n),
    let G :=
      PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre
    Lemma16MismatchLineageHistory
      hpsi ring C0 pre k kind →
    LastReadyCapped ring G.phys →
    Lemma16BadBorderWitness ring G.phys b k kind →
    let G' :=
      PPL.ghostStep hpsi ring pre.length G e
    ∀ m : PPL.LineageMeta n,
      m ∈ G'.completed →
      PPL.FreshCompletion (psi := psi) kind k m →
      m ∉ G.completed →
      PPL.CPB ring G'.phys

theorem lemma16MismatchHistNoNewFreshBranch_of_newFreshForcesCPB
    (hforce : Lemma16MismatchHistNewFreshForcesCPB) :
    Lemma16MismatchHistNoNewFreshBranch := by
  unfold Lemma16MismatchHistNoNewFreshBranch
  intro n psi kappa hpsi hn3 ring C0 pre b k kind e
  dsimp only
  intro hhistory hready hbad hnotCPB m hm hfresh

  by_cases hold :
      m ∈
        (PPL.ghostRun hpsi ring 0
          (PPL.initialGhost C0) pre).completed
  · exact hold
  · have hcpb :
        PPL.CPB ring
          (PPL.ghostStep hpsi ring pre.length
            (PPL.ghostRun hpsi ring 0
              (PPL.initialGhost C0) pre) e).phys :=
      hforce
        hpsi hn3 ring C0 pre b k kind e
        hhistory hready hbad
        m hm hfresh hold
    exact False.elim (hnotCPB hcpb)

theorem lemma16MismatchCompletionStepSpecHist_closed_of_newFreshForcesCPB
    (hforce : Lemma16MismatchHistNewFreshForcesCPB) :
    Lemma16MismatchCompletionStepSpecHist :=
  lemma16MismatchCompletionStepSpecHist_of_branches
    lemma16MismatchHistLastFrameBranch_proved
    lemma16MismatchHistBadBorderBranch_proved
    (lemma16MismatchHistNoNewFreshBranch_of_newFreshForcesCPB hforce)

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16MismatchHistNoNewFreshBranch_of_newFreshForcesCPB
#print axioms PPL.Convergence.ReachCPB.lemma16MismatchCompletionStepSpecHist_closed_of_newFreshForcesCPB
