import Leader.PPL.Modes.MidEntryTraversalHistoryInvariant




namespace PPL.Modes.Lemma5




set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false




open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9




/-!
# Lemma 5(i): budget-aware traversal invariant


The old traversal invariants were stronger than the ABC consumer needs:
they constrained every prefix even after the encounter event B had already
fired.  This file keeps only the pre-B/pre-C region.


B-good is the literal stopped-host budget
  stoppedPredictableHostHits ≤ 24 * n.
C-good is the negation of q19765TTLBad.


Once either guard is lost, q19998TraversalBudgetPrefix is an implication
with false antecedent and imposes no further physical condition.
-/




def q19998TraversalBudgetGood
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (h : Nat)
    (pre : DetSchedule n) : Prop :=
  let host := q19765TraversalHost ring D
  let stop := q19765TraversalStopB ring D
  stoppedPredictableHostHits
        ring host stop pre ≤ 24 * n ∧
    q19765TTLBad
        psi h ring host stop pre = false




/--
The budgeted prefix record.


While neither B nor C has fired:
1. the predictable current-max host still has positive reset signal;
2. every greedily matched letter of the rotated word has a concrete
   Algorithm-4 clock-reset witness;
3. completion of all n matched letters records the exact
   allClockResetsSeenB consequence consumed by the ABC residual.


Clause 3 is bookkeeping closure of clause 2, included here so the only
remaining unproved physical declaration in this file is the one-letter row.
-/
def q19998TraversalBudgetPrefix
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (start : Fin n)
    (h : Nat)
    (pre : DetSchedule n) : Prop :=
  let host := q19765TraversalHost ring D
  let Cpre := runPPL ring D pre
  let x := host pre
  let r :=
    q19844TraversalMatchedPrefixLength
      ring start pre
  q19998TraversalBudgetGood
      ring D h pre →
    0 < (Cpre x).signalR.val ∧
      (∀ j : Nat,
        j < r →
          q19844TraversalResetWitness
            ring D start pre j) ∧
      (r = n →
        allClockResetsSeenB
            ring D pre = true)




/--
The requested invariant is scoped only to prefixes of a legal paper sweep.
Every sweep has exact length lemma5PaperSweepHorizon n because it is drawn
from allSchedules at that horizon.
-/
def Lemma5iTraversalBudgetInvariant : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hkappa : 48 * psi ≤ kappa)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring →
    maxResetSignalB D = true →
    let start := q19765MaxSignalSite ring D
    let h := (D start).hits.val
    ∀ sweep : DetSchedule n,
      sweep ∈
          allSchedules n
            (lemma5PaperSweepHorizon n) →
      ∀ pre rest : DetSchedule n,
        sweep = pre ++ rest →
        q19998TraversalBudgetPrefix
          ring D start h pre




/-!
The two greedy-word facts are repeated under public names because the
corresponding helpers in Lemma5iRetimedTraversalHistInvariant are private.
-/




theorem q19998TraversalMatchedPrefixLength_nil
    {n : Nat}
    (ring : DirectedRing n)
    (start : Fin n) :
    q19844TraversalMatchedPrefixLength
        ring start [] =
      0 := by
  simp [
    q19844TraversalMatchedPrefixLength,
    PPLLOrderedWordScheduler.greedyWordRun,
    PPLLOrderedWordScheduler.greedyWordRunFrom,
    PPL.seqR
  ]




theorem
    q19998TraversalMatchedPrefixLength_eq_n_of_sublist
    {n : Nat}
    (ring : DirectedRing n)
    (start : Fin n)
    (pre : DetSchedule n)
    (hsub :
      (PPL.seqR ring start n).Sublist pre) :
    q19844TraversalMatchedPrefixLength
        ring start pre =
      n := by
  have hdone :
      (PPLLOrderedWordScheduler.greedyWordRun
        start
        (PPL.seqR ring start n)
        pre).pending = [] :=
    (PPLLOrderedWordScheduler.greedyWordRun_done_iff_sublist
      start
      (PPL.seqR ring start n)
      pre).2 hsub
  unfold q19844TraversalMatchedPrefixLength
  rw [hdone]
  simp




/-!
Empty prefix.  The reset frontier is vacuous because its matched length is
zero, while maxResetSignalB supplies a positive kappa-valued start signal.
-/




theorem q19998TraversalBudgetPrefix_nil
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hkappa : 48 * psi ≤ kappa)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (hmax : maxResetSignalB D = true) :
    q19998TraversalBudgetPrefix
      ring D
      (q19765MaxSignalSite ring D)
      (D
        (q19765MaxSignalSite ring D)).hits.val
      [] := by
  have hsig :=
    lemma5iRetimedTraversalABC_startSignal_eq_kappa
      ring D hmax
  have hkpos : 0 < kappa := by
    omega


  unfold q19998TraversalBudgetPrefix
  dsimp only
  intro _hbudget
  refine ⟨?_, ?_, ?_⟩


  · have hp :
        0 <
          (D
            (q19765MaxSignalSite ring D)).signalR.val := by
      rw [hsig]
      exact hkpos
    simpa [
      q19765TraversalHost,
      runPPL,
      runPopulationSchedule
    ] using hp


  · intro j hj
    rw [
      q19998TraversalMatchedPrefixLength_nil
        ring
        (q19765MaxSignalSite ring D)
    ] at hj
    omega


  · intro hr
    rw [
      q19998TraversalMatchedPrefixLength_nil
        ring
        (q19765MaxSignalSite ring D)
    ] at hr
    have hf : False := by
      omega
    exact False.elim hf




/-!
Exact remaining physical row.


TRUTH AUDIT:
* N=3: 24*n=72.  Its first 192 letters are H=1, so the
  73rd scheduler letter is the first one with stopped hits 73 > 72.
* N=4: 24*n=96.  After the initial stopped T and 95 repeated
  H letters the count is 96; the next repeated H, overall letter 97,
  is the first one with count 97 > 96.  The legal n=4 sweep horizon is
  only 96 letters anyway.


Thus neither known refutation reaches its bad transition while this row has a
post-step good-budget obligation.


The intended proof is the literal cold/H/T transition split.  This declaration
is the only physical proof debt intentionally left in this file.
-/
def Lemma5iTraversalBudgetOneStep : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hkappa : 48 * psi ≤ kappa)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa),
    SignalLineageOwnership
      (psi := psi) (kappa := kappa) ring →
    maxResetSignalB D = true →
    let start := q19765MaxSignalSite ring D
    let h := (D start).hits.val
    ∀ (pre : DetSchedule n) (e : Fin n),
      (pre ++ [e]).length ≤
          lemma5PaperSweepHorizon n →
      q19998TraversalBudgetPrefix
          ring D start h pre →
        q19998TraversalBudgetPrefix
          ring D start h (pre ++ [e])




/-!
Finite append closure from the one-letter row.  The length premise keeps every
induction step inside the paper sweep horizon.
-/




theorem q19998TraversalBudgetPrefix_append
    (hstep : Lemma5iTraversalBudgetOneStep)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hkappa : 48 * psi ≤ kappa)
    (hnpow : n ≤ 2 ^ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (hlineage :
      SignalLineageOwnership
        (psi := psi) (kappa := kappa) ring)
    (hmax : maxResetSignalB D = true)
    (pre rest : DetSchedule n)
    (hlen :
      (pre ++ rest).length ≤
        lemma5PaperSweepHorizon n)
    (hinv :
      q19998TraversalBudgetPrefix
        ring D
        (q19765MaxSignalSite ring D)
        (D
          (q19765MaxSignalSite ring D)).hits.val
        pre) :
    q19998TraversalBudgetPrefix
      ring D
      (q19765MaxSignalSite ring D)
      (D
        (q19765MaxSignalSite ring D)).hits.val
      (pre ++ rest) := by
  induction rest generalizing pre with
  | nil =>
      simpa using hinv
  | cons e tail ih =>
      have hlocal :=
        hstep
          hn3 hpsi hkappa hnpow
          ring D hlineage hmax
      dsimp only at hlocal


      have hfirstLe :
          (pre ++ [e]).length ≤
            (pre ++ (e :: tail)).length := by
        simp only [
          List.length_append,
          List.length_cons,
          List.length_nil
        ]
        omega


      have hfirst :
          (pre ++ [e]).length ≤
            lemma5PaperSweepHorizon n :=
        Nat.le_trans hfirstLe hlen


      have hnext :
          q19998TraversalBudgetPrefix
            ring D
            (q19765MaxSignalSite ring D)
            (D
              (q19765MaxSignalSite ring D)).hits.val
            (pre ++ [e]) :=
        hlocal pre e hfirst hinv


      have htailLen :
          ((pre ++ [e]) ++ tail).length ≤
            lemma5PaperSweepHorizon n := by
        simpa [List.append_assoc] using hlen


      have htail :=
        ih
          (pre := pre ++ [e])
          htailLen hnext


      simpa [List.append_assoc] using htail




/--
The one-letter row implies exactly the requested all-prefix budget invariant,
with no claim about schedules longer than the paper sweep.
-/
theorem lemma5iTraversalBudgetInvariant_of_oneStep
    (hstep : Lemma5iTraversalBudgetOneStep) :
    Lemma5iTraversalBudgetInvariant := by
  unfold Lemma5iTraversalBudgetInvariant
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring D hlineage hmax
  dsimp only
  intro sweep hsweep pre rest hsplit


  have hslen :=
    allSchedules_schedule_length
      n
      (lemma5PaperSweepHorizon n)
      sweep hsweep


  have hprelen :
      pre.length ≤
        lemma5PaperSweepHorizon n := by
    rw [hsplit, List.length_append] at hslen
    omega


  have hbase :
      q19998TraversalBudgetPrefix
        ring D
        (q19765MaxSignalSite ring D)
        (D
          (q19765MaxSignalSite ring D)).hits.val
        [] :=
    q19998TraversalBudgetPrefix_nil
      hn3 hpsi hkappa ring D hmax


  have happ :=
    q19998TraversalBudgetPrefix_append
      hstep
      hn3 hpsi hkappa hnpow
      ring D hlineage hmax
      [] pre
      (by simpa using hprelen)
      hbase


  simpa using happ




/--
The corrected ABC residual is an immediate consumer of the budget invariant.


If A fires, we are done.
If B fires, we are done.
If C fires, we are done.
Otherwise A=false gives the full rotated word as a sublist, while B=false and
C=false activate the budget invariant at the full sweep.  Its completion
clause gives allClockResetsSeenB=true, contradicting the residual premise that
some clock never reset.
-/
theorem
    lemma5iRetimedTraversalABCSweepResidualCorrected_of_budgetInvariant
    (hbudget : Lemma5iTraversalBudgetInvariant) :
    Lemma5iRetimedTraversalABCSweepResidualCorrected := by
  unfold
    Lemma5iRetimedTraversalABCSweepResidualCorrected
  intro n psi kappa
  intro hn3 hpsi hkappa hnpow
  intro ring D hlineage hmax


  let start :=
    q19765MaxSignalSite ring D
  let host :=
    q19765TraversalHost ring D
  let stop :=
    q19765TraversalStopB ring D
  let h :=
    (D start).hits.val


  change
    (D start).signalR.val = kappa ∧
      h ≤ psi ∧
      ∀ sweep : DetSchedule n,
        sweep ∈
            allSchedules n
              (lemma5PaperSweepHorizon n) →
        !allClockResetsSeenB ring D sweep =
            true →
        ((q19765RotatedMiss
              ring start sweep ||
            q19765EncounterBad
              ring host stop sweep) ||
          q19765TTLBad
            psi h ring host stop sweep) =
          true


  have hsig :
      (D start).signalR.val = kappa := by
    simpa [start] using
      lemma5iRetimedTraversalABC_startSignal_eq_kappa
        ring D hmax


  have hh :
      h ≤ psi := by
    simpa [h, start] using
      lemma5iRetimedTraversalABC_initialHits_le_psi
        ring D


  refine ⟨hsig, hh, ?_⟩
  intro sweep hsweep hbad


  cases hA :
      q19765RotatedMiss
        ring start sweep with
  | true =>
      simp [hA]


  | false =>
      have hsub :
          (PPL.seqR ring start n).Sublist
            sweep := by
        by_cases hs :
            (PPL.seqR ring start n).Sublist
              sweep
        · exact hs
        · have hAt :
              q19765RotatedMiss
                  ring start sweep =
                true := by
            unfold q19765RotatedMiss
            simp [hs]
          rw [hAt] at hA
          contradiction


      cases hB :
          q19765EncounterBad
            ring host stop sweep with
      | true =>
          simp [hA, hB]


      | false =>
          cases hC :
              q19765TTLBad
                psi h ring host stop sweep with
          | true =>
              simp [hA, hB, hC]


          | false =>
              have hnotB :
                  ¬
                    24 * n <
                      stoppedPredictableHostHits
                        ring host stop sweep := by
                apply of_decide_eq_false
                simpa [q19765EncounterBad]
                  using hB


              have hhits :
                  stoppedPredictableHostHits
                      ring host stop sweep ≤
                    24 * n := by
                omega


              have hpref0 :=
                hbudget
                  hn3 hpsi hkappa hnpow
                  ring D hlineage hmax
              dsimp only at hpref0


              have hpref :
                  q19998TraversalBudgetPrefix
                    ring D start h sweep := by
                simpa [start, h] using
                  hpref0
                    sweep hsweep
                    sweep [] (by simp)


              have hgood :
                  q19998TraversalBudgetGood
                    ring D h sweep := by
                unfold q19998TraversalBudgetGood
                dsimp only
                exact
                  ⟨by
                    simpa [host, stop] using hhits,
                   by
                    simpa [host, stop] using hC⟩


              unfold q19998TraversalBudgetPrefix at hpref
              dsimp only at hpref


              have hstate :=
                hpref hgood


              have hr :
                  q19844TraversalMatchedPrefixLength
                      ring start sweep =
                    n :=
                q19998TraversalMatchedPrefixLength_eq_n_of_sublist
                  ring start sweep hsub


              have hall :
                  allClockResetsSeenB
                      ring D sweep =
                    true :=
                hstate.2.2 hr


              have hf : False := by
                have hb := hbad
                simp [hall] at hb


              exact False.elim hf




end PPL.Modes.Lemma5




#print axioms PPL.Modes.Lemma5.lemma5iTraversalBudgetInvariant_of_oneStep
#print axioms PPL.Modes.Lemma5.lemma5iRetimedTraversalABCSweepResidualCorrected_of_budgetInvariant
