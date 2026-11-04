import Leader.PPL.SPLEntry.GappedCompose
import Leader.PPL.SPLEntry.RiskySweepLetterInductive


namespace PPL.Convergence.L18


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL


/-!
# Gapped scoped risky-flush reduction


The selected-letter row is already proved as
  L18RiskySweepLetterRow2
in L18RiskySweepLetter2.lean.


The only new semantic row below is the inserted-letter frame for the
already-cleared risky prefix.  It deliberately makes no assertion about
sites at or beyond the current frontier.
-/


/--
One arbitrary inserted P_PL-prime letter preserves the risky-sweep prefix.


This is strictly weaker than the refuted L18RiskySweepLetterRow:
there is no future-site/no-new-risk clause.  Risk is allowed to move around
at offsets >= j; only the already-cleared prefix < j is protected.
-/
def L18GappedRiskyInsertedStepRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (j : Nat)
    (C : Config n psi kappa)
    (e : Fin n),
    j ≤ psi →
    L18RiskySweepPrefix2 ring root j C →
    L18RiskySweepPrefix2 ring root j
      (pprimeStep ring C e)


/--
Run a suffix of the selected clockwise sweep through an arbitrary scheduler
word.  Inserted letters use L18GappedRiskyInsertedStepRow; a matched selected
letter advances the frontier using the already-proved
L18RiskySweepLetterRow2.
-/
private theorem q20209_gappedRiskRange
    (hInserted : L18GappedRiskyInsertedStepRow)
    (hSelected : L18RiskySweepLetterRow2)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n) :
    ∀ (k m : Nat)
      (C : Config n psi kappa)
      (schedule : DetSchedule n),
      k + m ≤ psi →
      L18RiskySweepPrefix2 ring root k C →
      (l18GappedRightRange ring root k m).Sublist
        schedule →
      L18RiskySweepPrefix2 ring root (k + m)
        (runPPrime ring C schedule) := by
  unfold L18GappedRiskyInsertedStepRow at hInserted
  unfold L18RiskySweepLetterRow2 at hSelected
  intro k m C schedule
  intro hbound hPrefix hsub
  induction schedule generalizing C k m with
  | nil =>
      cases m with
      | zero =>
          simpa [l18GappedRightRange, runPPrime]
            using hPrefix
      | succ m =>
          have hlen := hsub.length_le
          simp [l18GappedRightRange] at hlen


  | cons fired rest ih =>
      cases m with
      | zero =>
          have hp :=
            hInserted
              hn3 hpsi hlt
              ring root k C fired
              (by omega)
              hPrefix
          have htail :=
            ih
              (C := pprimeStep ring C fired)
              (k := k) (m := 0)
              (by omega)
              hp
              (List.nil_sublist rest)
          simpa [runPPrime] using htail


      | succ m =>
          let requested :=
            shiftRight ring root k
          let tail :=
            l18GappedRightRange
              ring root (k + 1) m


          have hword :
              l18GappedRightRange
                  ring root k (m + 1) =
                requested :: tail := by
            rfl
          rw [hword] at hsub


          by_cases hfire : fired = requested
          · subst fired


            have htailSub :
                tail.Sublist rest := by
              rcases
                  List.sublist_cons_iff.mp hsub with
                hskip | ⟨tail', heq, ht⟩
              · exact
                  (List.sublist_cons_self
                    requested tail).trans hskip
              · cases heq
                exact ht


            have hp0 :=
              hSelected
                hn3 hpsi hlt
                ring root C k
                (by omega)
                hPrefix.1
                hPrefix.2
            dsimp only at hp0


            have hp :
                L18RiskySweepPrefix2
                  ring root (k + 1)
                  (pprimeStep ring C requested) := by
              simpa [L18RiskySweepPrefix2]
                using hp0


            have htail :=
              ih
                (C := pprimeStep ring C requested)
                (k := k + 1) (m := m)
                (by omega)
                hp
                (by
                  simpa [tail] using htailSub)


            have hidx :
                k + 1 + m = k + (m + 1) := by
              omega
            rw [hidx] at htail
            simpa [runPPrime] using htail


          · have htailSub :
                (requested :: tail).Sublist rest := by
              rcases
                  List.sublist_cons_iff.mp hsub with
                hskip | ⟨tail', heq, _ht⟩
              · exact hskip
              · have hhead :
                    requested = fired :=
                  (List.cons.inj heq).1
                exact
                  False.elim
                    (hfire hhead.symm)


            have hp :=
              hInserted
                hn3 hpsi hlt
                ring root k C fired
                (by omega)
                hPrefix


            have htail :=
              ih
                (C := pprimeStep ring C fired)
                (k := k) (m := m + 1)
                hbound
                hp
                (by
                  rw [hword]
                  exact htailSub)
            simpa [runPPrime] using htail


/--
One selected sweep, allowed to occur only as an ordered subsequence, clears
all risky sites.  The final conversion uses the landed fact that every risky
host has rooted offset < psi when psi < n.
-/
private theorem q20209_gappedSingleSweep
    (hInserted : L18GappedRiskyInsertedStepRow)
    (hSelected : L18RiskySweepLetterRow2)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (schedule : DetSchedule n)
    (hC : CDLAt ring root C)
    (hsub :
      (PPL.seqR ring root psi).Sublist schedule) :
    let D := runPPrime ring C schedule
    CDLAt ring root D ∧
      L18NoRiskyAt ring root D := by
  have hzero :
      L18RiskySweepPrefix2
        ring root 0 C := by
    unfold L18RiskySweepPrefix2
    refine ⟨hC, ?_⟩
    intro i hi
    omega


  have hsub' :
      (l18GappedRightRange
          ring root 0 psi).Sublist schedule := by
    rw [l18GappedRightRange_zero]
    exact hsub


  have hfinal :
      L18RiskySweepPrefix2
        ring root psi
        (runPPrime ring C schedule) := by
    simpa using
      q20209_gappedRiskRange
        hInserted hSelected
        hn3 hpsi hlt
        ring root
        0 psi C schedule
        (by omega)
        hzero
        hsub'


  dsimp only
  refine ⟨hfinal.1, ?_⟩
  unfold L18NoRiskyAt
  intro i hR
  have hoff :
      cyclicOffset ring root i < psi :=
    l18Risk2RiskyHostOffset_lt_psi
      hlt ring root
      (runPPrime ring C schedule)
      i hR
  exact hfinal.2 i hoff hR


/--
Local copy of the pure-list append/subsequence split from
L18GappedCompose.lean.  The original helper is private to that module.
-/
private theorem q20209_sublistAppendSplit
    {A : Type}
    (a b w : List A)
    (hsub : (a ++ b).Sublist w) :
    ∃ u v : List A,
      w = u ++ v ∧
        a.Sublist u ∧
        b.Sublist v := by
  induction w generalizing a with
  | nil =>
      cases a with
      | nil =>
          refine
            ⟨[], [], rfl,
              List.Sublist.slnil, ?_⟩
          simpa using hsub
      | cons x xs =>
          have hlen := hsub.length_le
          simp at hlen


  | cons y ys ih =>
      cases a with
      | nil =>
          refine
            ⟨[], y :: ys, rfl,
              List.Sublist.slnil, ?_⟩
          simpa using hsub


      | cons x xs =>
          have hs :
              (x :: (xs ++ b)).Sublist
                (y :: ys) := by
            simpa only [List.cons_append]
              using hsub


          rcases
              List.sublist_cons_iff.mp hs with
            hskip | ⟨tail, heq, htake⟩
          · rcases
                ih (a := x :: xs) hskip with
              ⟨u, v, hw, hu, hv⟩
            refine
              ⟨y :: u, v, ?_, ?_, hv⟩
            · simp only [List.cons_append, hw]
            · exact List.Sublist.cons y hu


          · cases heq
            rcases
                ih (a := xs) htake with
              ⟨u, v, hw, hu, hv⟩
            refine
              ⟨y :: u, v, ?_, ?_, hv⟩
            · simp only [List.cons_append, hw]
            · exact
                List.Sublist.cons_cons y hu


/--
Adapter from the two one-step rows:
  * selected frontier advancement;
  * arbitrary inserted-letter prefix preservation.


The result is stronger than the target's disjunction: the endpoint always
has CDLAt and L18NoRiskyAt.
-/
theorem l18GappedRiskyFlushPhaseScoped_of_rows
    (hInserted : L18GappedRiskyInsertedStepRow)
    (hSelected : L18RiskySweepLetterRow2) :
    L18GappedRiskyFlushPhaseScoped := by
  unfold L18GappedRiskyFlushPhaseScoped
  intro n psi kappa
  intro hn3 hpsi hlt
  intro ring root C schedule
  intro hC hsub


  let w : DetSchedule n :=
    PPL.seqR ring root psi


  have htwo :
      (w ++ w).Sublist schedule := by
    simpa
      [l18RiskyFlushWord,
        PPL.wordPower, w]
      using hsub


  obtain ⟨u, v, hsched, hu, hv⟩ :=
    q20209_sublistAppendSplit
      w w schedule htwo


  have h1 :
      CDLAt ring root
          (runPPrime ring C u) ∧
        L18NoRiskyAt ring root
          (runPPrime ring C u) := by
    simpa [w] using
      q20209_gappedSingleSweep
        hInserted hSelected
        hn3 hpsi hlt
        ring root C u
        hC hu


  have h2 :
      CDLAt ring root
          (runPPrime ring
            (runPPrime ring C u) v) ∧
        L18NoRiskyAt ring root
          (runPPrime ring
            (runPPrime ring C u) v) := by
    simpa [w] using
      q20209_gappedSingleSweep
        hInserted hSelected
        hn3 hpsi hlt
        ring root
        (runPPrime ring C u) v
        h1.1 hv


  refine Or.inr ?_
  dsimp only
  rw [hsched, runPPrime_append]
  exact h2


/--
Only one new leaf remains: the inserted-step prefix frame.  The selected
frontier row is already proved on main.
-/
theorem l18GappedRiskyFlushPhaseScoped_of_insertedStepRow
    (hInserted : L18GappedRiskyInsertedStepRow) :
    L18GappedRiskyFlushPhaseScoped :=
  l18GappedRiskyFlushPhaseScoped_of_rows
    hInserted
    l18RiskySweepLetterRow2_proved


end PPL.Convergence.L18


#print axioms   PPL.Convergence.L18.l18GappedRiskyFlushPhaseScoped_of_rows
#print axioms   PPL.Convergence.L18.l18GappedRiskyFlushPhaseScoped_of_insertedStepRow
