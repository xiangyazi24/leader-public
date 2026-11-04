import Leader.PPL.ReachCPB.MismatchCompletionHist
import Leader.PPL.ReachCPB.StepDetectPersistence


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/-!
# Lemma 16 mismatch completion: historical split


Truth audit: the Hist carrier is consistent with the literal ghost row and the
earlier stale-source witness does not satisfy it.


The old witness has birthStep = 0
(ReachCPBMismatchCompletionRefute.lean:105-112).  Its only possible history
epoch would therefore be epoch 0, but its initial configuration has clock 0 at
sites 1 and 2 while kappa = 1 (same file:58-62), so that prefix is not
LastReadyCapped.  Thus the kernel-checked unrestricted counterexample is
excluded, rather than merely hidden by a stronger conclusion.


For a genuinely historical fresh lineage, the source-freeze mechanism is:


* Lemma16MismatchLineageHistory stores a LastReadyCapped epoch and requires
  epoch <= birthStep for every live selected-colour lineage born at k
  (ReachCPBMismatchCompletionHist.lean:133-148).
* The compiled lemma16DetectPersistenceCappedStepSpec_proved says that one
  capped-Detect step reaches CPB or keeps DetectReadyCapped and frames every
  dist field (ReachCPBStepDetectPersistence.lean:524-540); its proof turns any
  newly present leader into CPB (same file:712-718).  CPB is absorbing by
  cpb_run_closed (ReachCPB.lean:458-483).
* At a positive c = 1 comparison, Algorithm 3 births a leader when mode=true
  and the token bit disagrees with id; the only id assignment is the
  mode=false branch (Transition.lean:304-318).  Hence along a non-CPB suffix
  starting at the history epoch, capped Detect keeps the physical id bits
  frozen.
* At c = -1 the ghost/physical token turns and copies the current source l.id
  into its positive-going payload (TokenCorrectness.lean:277-285 and
  :306-315).  Since the lineage was born no earlier than the capped epoch,
  that captured bit equals the same source bit at the current endpoint.
* A completion is logged by bumpTo exactly when the incremented lineage move
  count reaches tokenTrajectoryMoves (TokenCorrectness.lean:216-220);
  ghostStep appends the black/white done lists to completed
  (TokenCorrectness.lean:337-354).  The c=1 positive branch is the final
  comparison branch used by the refutation (same file:251-259).
  FreshCompletion itself requires a born lineage at k and the exact move count
  (TokenCorrectness.lean:545-555).


Thus the only genuinely historical residual below is the last branch:
a newly logged fresh completion must force CPB because the captured source
bits are no longer stale and the recorded predecessor-border equation is bad.
The first two residuals are ordinary one-interaction physical framing.
-/


/--
One-step last-field frame in the non-CPB branch.


The DetectReadyCapped and dist parts are already compiled in
lemma16DetectPersistenceCappedStepSpec_proved
(ReachCPBStepDetectPersistence.lean:524-540) and are reused by the assembly
below.  This residual asks only for the remaining LastReady field.
The selected-pair producer already exists as lemma16LastPairRowSpec_proved
(ReachCPBLastPairRow.lean:480-544): under the capped leaderless zero-signal
successor-dist row it gives the exact last output formula.
-/
def Lemma16MismatchHistLastFrameBranch : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n),
    let G :=
      PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre
    LastReadyCapped ring G.phys ->
    let G' :=
      PPL.ghostStep hpsi ring pre.length G e
    Not (PPL.CPB ring G'.phys) ->
    forall i : Fin n,
      (G'.phys i).last = false


/--
One-step persistence of the fixed bad predecessor-border witness, conditional
on not having reached CPB.


The witness fields are IsBorder, predecessor-border geometry, Cd, and the
segment-ID mismatch (ReachCPBMismatchCapped.lean:248-266).  The compiled
Detect persistence row frames dist.  Last is isolated above.  The remaining
identifier fact is the literal Algorithm-3 row: in Detect mode a mismatching
c=1 comparison performs leaderBirth, while an id write occurs only in
Construct/mode=false (Transition.lean:311-317); the former is CPB by
ReachCPBStepDetectPersistence.lean:712-718.  Hence the non-CPB branch frames
the segment id bits as required.
-/
def Lemma16MismatchHistBadBorderBranch : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (e : Fin n),
    let G :=
      PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre
    LastReadyCapped ring G.phys ->
    Lemma16BadBorderWitness ring G.phys b k kind ->
    let G' :=
      PPL.ghostStep hpsi ring pre.length G e
    Not (PPL.CPB ring G'.phys) ->
    Lemma16BadBorderWitness ring G'.phys b k kind


/--
The single history-specific one-interaction residual.


If the next physical state is not CPB, no selected fresh completion can be new
at this step.  A candidate new member of completed comes from gb.done or
gw.done in ghostStep (TokenCorrectness.lean:337-354); bumpTo preserves
id/birthSite/birthStep and only increments moves (lines 216-220).
FreshCompletion therefore identifies a pre-step live lineage to which
Lemma16MismatchLineageHistory applies.  Its c=-1 source bit was captured after
the capped epoch, so the Detect/non-CPB id frame makes that bit current.
The bad segment equation must then expose a c=1 disagreement, whose literal
mode=true branch creates a leader instead of silently completing.
-/
def Lemma16MismatchHistNoNewFreshBranch : Prop :=
  forall {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (hn3 : 3 <= n)
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
      hpsi ring C0 pre k kind ->
    LastReadyCapped ring G.phys ->
    Lemma16BadBorderWitness ring G.phys b k kind ->
    let G' :=
      PPL.ghostStep hpsi ring pre.length G e
    Not (PPL.CPB ring G'.phys) ->
    forall m : PPL.LineageMeta n,
      m ∈ G'.completed ->
      PPL.FreshCompletion (psi := psi) kind k m ->
      m ∈ G.completed


theorem lemma16MismatchCompletionStepSpecHist_of_branches
    (hLast : Lemma16MismatchHistLastFrameBranch)
    (hBad : Lemma16MismatchHistBadBorderBranch)
    (hFresh : Lemma16MismatchHistNoNewFreshBranch) :
    Lemma16MismatchCompletionStepSpecHist := by
  unfold Lemma16MismatchCompletionStepSpecHist
  intro n psi kappa hpsi hn3 ring C0 pre b k kind e
  dsimp only
  intro hhistory hready hbad


  let G :=
    PPL.ghostRun hpsi ring 0
      (PPL.initialGhost C0) pre
  let G' :=
    PPL.ghostStep hpsi ring pre.length G e


  change
    Or
      (PPL.CPB ring G'.phys)
      (And
        (LastReadyCapped ring G'.phys)
        (And
          (Lemma16BadBorderWitness ring G'.phys b k kind)
          (forall m : PPL.LineageMeta n,
            m ∈ G'.completed ->
            PPL.FreshCompletion (psi := psi) kind k m ->
            m ∈ G.completed)))


  by_cases hcpb : PPL.CPB ring G'.phys
  · exact Or.inl hcpb
  · have hdetect0 :=
      lemma16DetectPersistenceCappedStepSpec_proved
        hn3 hpsi ring G.phys e hready.1.1
    dsimp only at hdetect0


    have hphys :
        G'.phys =
          PopulationProtocol.step
            (PPL.protocol psi kappa) ring G.phys e := by
      rfl
    rw [← hphys] at hdetect0


    have hdetect :
        And
          (DetectReadyCapped ring G'.phys)
          (forall i : Fin n,
            (G'.phys i).dist = (G.phys i).dist) := by
      rcases hdetect0 with hcpb' | hkeep
      · exact False.elim (hcpb hcpb')
      · exact hkeep


    have hsucc :
        forall i : Fin n,
          (G'.phys (ring.rightNeighbor i)).dist.val =
            ((G'.phys i).dist.val + 1) % (2 * psi) := by
      intro i
      rw [hdetect.2 (ring.rightNeighbor i), hdetect.2 i]
      exact hready.1.2 i


    have hlast :
        forall i : Fin n,
          (G'.phys i).last = false :=
      hLast hpsi hn3 ring C0 pre e hready hcpb


    have hready' :
        LastReadyCapped ring G'.phys := by
      unfold LastReadyCapped DistReadyCapped
      exact
        And.intro
          (And.intro hdetect.1 hsucc)
          hlast


    have hbad' :
        Lemma16BadBorderWitness ring G'.phys b k kind :=
      hBad hpsi hn3 ring C0 pre b k kind e
        hready hbad hcpb


    have hfresh :
        forall m : PPL.LineageMeta n,
          m ∈ G'.completed ->
          PPL.FreshCompletion (psi := psi) kind k m ->
          m ∈ G.completed :=
      hFresh hpsi hn3 ring C0 pre b k kind e
        hhistory hready hbad hcpb


    exact
      Or.inr
        (And.intro hready'
          (And.intro hbad' hfresh))


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16MismatchCompletionStepSpecHist_of_branches
