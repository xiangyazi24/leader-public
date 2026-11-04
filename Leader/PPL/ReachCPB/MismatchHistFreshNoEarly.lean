import Leader.PPL.ReachCPB.MismatchHistFreshAge
import Leader.PPL.ReachCPB.MismatchHistFreshDistCanon

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! The no-early definitions `Lemma16FreshNoEarlyCompletionId` and
`Lemma16FreshNoEarlyCompletionIdCanon` are those of
`ReachCPBMismatchHistFreshDistCanon`. -/

/-! -------------------------------------------------------------------------
    2. Exact carried history and one-step residual
------------------------------------------------------------------------- -/

/--
The induction carries exactly the history not present in GhostIdsUniqueAt:

* every live born ID predates the current global step;
* every completed born ID predates the current global step;
* every fresh live subterminal owner has no same-ID completed record.

The first clause is GhostIdsBefore.  The second is its completion-side
analogue and is what prevents a current-step birth from aliasing an older
completion.
-/
def Lemma16FreshNoEarlyCompletionIdHistory
    {n psi kappa : Nat}
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa) : Prop :=
  PPL.GhostIdsBefore step G ∧
    (∀ (m : PPL.LineageMeta n),
      m ∈ G.completed →
      ∀ (kind : PPL.TokenKind) (s : Nat),
        m.id = .born kind s →
        s < step) ∧
    ∀ (k : Fin n) (kind : PPL.TokenKind),
      Lemma16FreshNoEarlyCompletionId kind k G

/--
Exact remaining local row.

Its proof is a finite selected-pair/bumpTo case split:

* old completions are preserved and same-lineage live moves never decrease;
* a new done record is emitted only after ghostStepLineageAdvance and only
  at exact terminal move count;
* GhostIdsUnique excludes a selected same-ID source from also surviving at a
  distinct frame site;
* Lemma16GhostLineageCoherent excludes opposite-color ID aliasing;
* the two clock clauses rule out reuse by a current-step birth.

No scheduler suffix, Dist, Last, CPB, or L16 geometry premise is needed.
-/
def Lemma16FreshNoEarlyCompletionIdStepHistoryRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (step : Nat)
    (G : PPL.GhostConfig n psi kappa)
    (e : Fin n),
    PPL.GhostIdsUnique G →
    Lemma16GhostLineageCoherent G →
    Lemma16FreshNoEarlyCompletionIdHistory step G →
    Lemma16FreshNoEarlyCompletionIdHistory
      (step + 1)
      (PPL.ghostStep hpsi ring step G e)

/-! -------------------------------------------------------------------------
    3. Base case and canonical live-ID uniqueness for all ring sizes
------------------------------------------------------------------------- -/

private theorem lemma16FreshNoEarlyCompletionIdHistory_initial
    {n psi kappa : Nat}
    (C0 : Config n psi kappa) :
    Lemma16FreshNoEarlyCompletionIdHistory
      0 (PPL.initialGhost C0) := by
  refine ⟨(PPL.ghostIdsUnique_initial C0).2, ?_⟩
  refine ⟨?_, ?_⟩
  · intro m hm kind s hid
    change m ∈ ([] : List (PPL.LineageMeta n)) at hm
    simp at hm
  · intro k kind
    unfold Lemma16FreshNoEarlyCompletionId
    intro i z howner hfresh hyoung
    unfold Lemma16NoPriorCompletionId
    intro m hm
    change m ∈ ([] : List (PPL.LineageMeta n)) at hm
    simp at hm

/--
ghostIdsUnique_run requires 2 ≤ n.  The requested theorem only has a
DirectedRing n, so the singleton case is discharged directly: any two Fin n
sites are equal when n < 2 and a site exists.
-/
private theorem lemma16GhostIdsUniqueCanon_anyN
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n) :
    PPL.GhostIdsUnique
      (PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre) := by
  by_cases hn2 : 2 ≤ n
  · exact
      (PPL.ghostIdsUnique_run
        hpsi hn2 ring C0 pre).1
  · unfold PPL.GhostIdsUnique
    intro kind i j zi zj hi hj hid
    apply Fin.ext
    have hii := i.isLt
    have hjj := j.isLt
    omega

/-! -------------------------------------------------------------------------
    4. Core-only snoc induction and pre ++ [e] transport
------------------------------------------------------------------------- -/

private theorem lemma16ListSnocInduction
    {α : Type}
    (P : List α → Prop)
    (hnil : P [])
    (hsnoc :
      ∀ (xs : List α) (x : α),
        P xs → P (xs ++ [x])) :
    ∀ xs : List α, P xs := by
  have hrev :
      ∀ ys : List α, P ys.reverse := by
    intro ys
    induction ys with
    | nil =>
        simpa using hnil
    | cons x ys ih =>
        have hs := hsnoc ys.reverse x ih
        simpa using hs
  intro xs
  have hx := hrev xs.reverse
  simpa using hx

private theorem
    lemma16FreshNoEarlyCompletionIdHistory_snoc
    (hStep : Lemma16FreshNoEarlyCompletionIdStepHistoryRow)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n)
    (hpre :
      Lemma16FreshNoEarlyCompletionIdHistory
        pre.length
        (PPL.ghostRun hpsi ring 0
          (PPL.initialGhost C0) pre)) :
    Lemma16FreshNoEarlyCompletionIdHistory
      (pre ++ [e]).length
      (PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) (pre ++ [e])) := by
  unfold Lemma16FreshNoEarlyCompletionIdStepHistoryRow at hStep

  let G :=
    PPL.ghostRun hpsi ring 0
      (PPL.initialGhost C0) pre

  have huniq : PPL.GhostIdsUnique G := by
    simpa [G] using
      lemma16GhostIdsUniqueCanon_anyN
        hpsi ring C0 pre

  have hcoh : Lemma16GhostLineageCoherent G := by
    have hprod :
        Lemma16GhostLineageCoherentRunProducer :=
      lemma16GhostLineageCoherentRunProducer_proved
    unfold Lemma16GhostLineageCoherentRunProducer at hprod
    simpa [G] using
      hprod hpsi ring C0 pre

  have hnext :
      Lemma16FreshNoEarlyCompletionIdHistory
        (pre.length + 1)
        (PPL.ghostStep hpsi ring pre.length G e) :=
    hStep
      hpsi ring pre.length G e
      huniq hcoh
      (by simpa [G] using hpre)

  have happ :
      PPL.ghostRun hpsi ring 0
          (PPL.initialGhost C0) (pre ++ [e]) =
        PPL.ghostStep hpsi ring pre.length G e := by
    rw [
      lemma16PostEpochGhostRun_append
        hpsi ring 0 (PPL.initialGhost C0)
        pre [e]]
    simp only [Nat.zero_add, PPL.ghostRun]
    try rfl

  rw [happ]
  simpa using hnext

private theorem
    lemma16FreshNoEarlyCompletionIdHistory_run_of_stepHistoryRow
    (hStep : Lemma16FreshNoEarlyCompletionIdStepHistoryRow)
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n) :
    Lemma16FreshNoEarlyCompletionIdHistory
      pre.length
      (PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre) := by
  exact
    lemma16ListSnocInduction
      (P := fun pre : DetSchedule n =>
        Lemma16FreshNoEarlyCompletionIdHistory
          pre.length
          (PPL.ghostRun hpsi ring 0
            (PPL.initialGhost C0) pre))
      (lemma16FreshNoEarlyCompletionIdHistory_initial C0)
      (fun pre e ih =>
        lemma16FreshNoEarlyCompletionIdHistory_snoc
          hStep hpsi ring C0 pre e ih)
      pre

/-! -------------------------------------------------------------------------
    5. Requested canonical theorem reduced to the exact residual
------------------------------------------------------------------------- -/

theorem
    lemma16FreshNoEarlyCompletionIdCanon_proved_of_stepHistoryRow
    (hStep : Lemma16FreshNoEarlyCompletionIdStepHistoryRow) :
    Lemma16FreshNoEarlyCompletionIdCanon := by
  unfold Lemma16FreshNoEarlyCompletionIdCanon
  intro n psi kappa hpsi ring C0 pre k kind
  have hhist :=
    lemma16FreshNoEarlyCompletionIdHistory_run_of_stepHistoryRow
      hStep hpsi ring C0 pre
  exact hhist.2.2 k kind

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16FreshNoEarlyCompletionIdCanon_proved_of_stepHistoryRow
