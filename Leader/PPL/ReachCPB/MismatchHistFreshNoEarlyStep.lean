-- Leader/PPL/ReachCPB/MismatchHistFreshNoEarlyStep.lean
import Leader.PPL.ReachCPB.MismatchHistFreshNoEarly

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

/-!
A. Clock preservation.

Truth argument:
* a post live owner is either an old shadow/descendant, whose born timestamp
  was < step, or the unique kind-local birth made by this interaction, whose
  timestamp is exactly step;
* an old completion keeps its old timestamp bound;
* every genuinely new done record is the advance of an old selected live
  source.  A current birth starts at moves = 0 and, even if immediately
  bumped, reaches moves = 1; for psi >= 2 this is strictly below
  tokenTrajectoryMoves psi, so a current birth cannot enter done.

Thus both clocks advance from step to step+1.  No uniqueness or lineage
coherence is needed in this row.
-/
def Lemma16FreshNoEarlyCompletionIdStepClockRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n),
    PPL.GhostIdsBefore step G →
    (∀ (m : PPL.LineageMeta n),
      m ∈ G.completed →
      ∀ (kind : PPL.TokenKind) (s : Nat),
        m.id = .born kind s →
        s < step) →
    PPL.GhostIdsBefore
        (step + 1)
        (PPL.ghostStep hpsi ring step G e) ∧
      ∀ (m : PPL.LineageMeta n),
        m ∈
            (PPL.ghostStep
              hpsi ring step G e).completed →
        ∀ (kind : PPL.TokenKind) (s : Nat),
          m.id = .born kind s →
          s < step + 1

/-!
B. Separation from the old completed list.

Truth argument:
Take a fresh subterminal post owner z.

If z is a current-step birth, z.id = .born kind step.  An old completed
record with that ID contradicts the pre completed-clock clause.

Otherwise the selected-pair/frame mirror gives an old owner z0 with the same
id and birthSite, and with either unchanged moves or one extra move.  Hence
post subterminal implies z0 was pre subterminal.  FreshAt is preserved because
id and birthSite are unchanged, so the pre no-early clause excludes every
old completed record with z0.id = z.id.

This row does not need GhostIdsUnique or coherence and never reasons about a
new done record.
-/
def Lemma16FreshNoEarlyCompletionIdStepOldCompletedRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n),
    (∀ (m : PPL.LineageMeta n),
      m ∈ G.completed →
      ∀ (bornKind : PPL.TokenKind) (s : Nat),
        m.id = .born bornKind s →
        s < step) →
    (∀ (k : Fin n) (kind : PPL.TokenKind),
      Lemma16FreshNoEarlyCompletionId kind k G) →
    ∀ (k : Fin n) (kind : PPL.TokenKind)
      (i : Fin n) (z : PPL.GhostToken n psi),
      PPL.ghostTokenAt kind
          (PPL.ghostStep hpsi ring step G e) i =
        some z →
      PPL.FreshAt kind k z.lmeta →
      z.lmeta.moves <
        PPL.tokenTrajectoryMoves psi →
      ∀ m : PPL.LineageMeta n,
        m ∈ G.completed →
        m.id ≠ z.lmeta.id

/-!
C. Separation from newly appended completions.

Truth argument:
Let m be new in G'.completed.  The done-provenance mirror
(doneProvGhostStep_eq / doneProvGhostStep_completed / bump_done_source)
reduces m to an exact terminal advance of an OLD selected endpoint source.
A current-step birth cannot be this source of a done record (moves 0 -> 1,
while tokenTrajectoryMoves psi > 1).

Now suppose m.id = z.id for a post fresh subterminal owner z.

* If z were a current-step birth, its ID would be .born kind step.  Since the
  done source is old with the same ID, GhostIdsBefore step G gives step < step,
  impossible.
* Otherwise z also descends from an old source z0.  Coherence forces the done
  source to live in the same color as z; GhostIdsUnique then identifies its
  old site with z0's site, and the Option equality identifies the actual
  source token.
* The finite selected-pair branches are linear.  If that source emits done,
  its advance has moves exactly tokenTrajectoryMoves psi.  It is either
  deleted or the surviving same-lineage output is that terminal advance.
  Therefore it cannot be the assumed post owner with moves strictly below
  terminal.

This is the only residual that needs the no-cloning/selected-pair case split.
The self-neighbor case is covered by the same literal pair semantics:
setTwo keeps the left result, yielding deletion or the terminal advance.
-/
def Lemma16FreshNoEarlyCompletionIdStepNewCompletedRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n),
    PPL.GhostIdsUnique G →
    Lemma16GhostLineageCoherent G →
    PPL.GhostIdsBefore step G →
    ∀ (k : Fin n) (kind : PPL.TokenKind)
      (i : Fin n) (z : PPL.GhostToken n psi),
      PPL.ghostTokenAt kind
          (PPL.ghostStep hpsi ring step G e) i =
        some z →
      PPL.FreshAt kind k z.lmeta →
      z.lmeta.moves <
        PPL.tokenTrajectoryMoves psi →
      ∀ m : PPL.LineageMeta n,
        m ∈
            (PPL.ghostStep
              hpsi ring step G e).completed →
        m ∉ G.completed →
        m.id ≠ z.lmeta.id

/--
The original one-step history row follows by:
1. Row A for the two clock conjuncts;
2. split an arbitrary post completion m on m ∈ G.completed;
3. Row B in the old-list arm and Row C in the genuinely-new arm.
-/
theorem
    lemma16FreshNoEarlyCompletionIdStepHistoryRow_proved_of_localRows
    (hClock :
      Lemma16FreshNoEarlyCompletionIdStepClockRow)
    (hOld :
      Lemma16FreshNoEarlyCompletionIdStepOldCompletedRow)
    (hNew :
      Lemma16FreshNoEarlyCompletionIdStepNewCompletedRow) :
    Lemma16FreshNoEarlyCompletionIdStepHistoryRow := by
  unfold
    Lemma16FreshNoEarlyCompletionIdStepClockRow
    at hClock
  unfold
    Lemma16FreshNoEarlyCompletionIdStepOldCompletedRow
    at hOld
  unfold
    Lemma16FreshNoEarlyCompletionIdStepNewCompletedRow
    at hNew
  unfold
    Lemma16FreshNoEarlyCompletionIdStepHistoryRow

  intro n psi kappa hpsi ring step G e
  intro huniq hcoh hhist

  have hclock :=
    hClock hpsi ring step G e
      hhist.1 hhist.2.1

  refine ⟨hclock.1, ?_⟩
  refine ⟨hclock.2, ?_⟩

  intro k kind
  unfold Lemma16FreshNoEarlyCompletionId
  intro i z howner hfresh hyoung
  unfold Lemma16NoPriorCompletionId
  intro m hm

  by_cases hold : m ∈ G.completed
  · exact
      hOld hpsi ring step G e
        hhist.2.1 hhist.2.2
        k kind i z
        howner hfresh hyoung
        m hold
  · exact
      hNew hpsi ring step G e
        huniq hcoh hhist.1
        k kind i z
        howner hfresh hyoung
        m hm hold

#print axioms
  PPL.Convergence.ReachCPB.lemma16FreshNoEarlyCompletionIdStepHistoryRow_proved_of_localRows

end PPL.Convergence.ReachCPB
