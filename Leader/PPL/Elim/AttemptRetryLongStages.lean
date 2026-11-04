import Leader.PPL.Elim.AttemptRetryLong
import Leader.Core.PredictableCounterRaceFiniteTree


namespace PPL.Convergence.LDLocal


set_option autoImplicit false
set_option Elab.async false


open FiniteUniformStoppingTree


/-!
# Long-attempt retry mass: concrete stage counts and finite-prefix splice


This file removes the existential ambiguity in
`LongAttemptRetryStageFactorSpec`.


The two public masses below are literal finite-horizon counts over
`longAttemptKernel`:


* `longRaceMass`: progress-race target-win-or-still-active mass;
* `longIncidentMass`: incident-orientation retained-or-still-active mass.


They are defined by one generic cut-count recursion.  A good cut pads the
remaining scheduler suffix, a bad cut contributes zero, and an unresolved
active node keeps its literal kernel successor.  Hence every count below is
on the actual attempt tree, with the active residual kept at every horizon.


The first physical race is not a single `twoTargetStep`: after a target or
attacker service edge the race normally remains active with an updated phase.
It is a predictable multi-hit counter race.  The second incident-orientation
stage is the literal one-hit `L_j` versus `R_j` two-target race.  The helper
`counterRace_first_or_active_half` below is the exact finite-horizon
counter-race analogue of `twoTarget_first_or_active_half`.
-/


/-! ## Generic cut count -/


/-- Count full scheduler words which have either reached a designated good
handoff or are still active before a designated bad handoff.


At a good handoff the remaining suffix is padding, hence `n^T`.
At a bad handoff or completed retry the contribution is zero.
An ordinary attempt success is also padded by all remaining raw words. -/
def longCutCount
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (good bad : A -> Bool) :
    AttemptNode A S -> Nat -> Nat
  | .success, T => n ^ T
  | .retry _, _ => 0
  | .active a, 0 =>
      if good a then 1
      else if bad a then 0
      else 1
  | .active a, T + 1 =>
      if good a then n ^ (T + 1)
      else if bad a then 0
      else
        (List.ofFn (fun e : Fin n =>
          longCutCount K good bad (K.step a e) T)).sum


private theorem value_le_mul_of_one_le
    (d x : Nat) (hd : 1 <= d) :
    x <= d * x := by
  have h := Nat.mul_le_mul_right x hd
  simpa using h


/-- Finite-prefix splice.


The first cut process and second cut process follow the same literal kernel
until the first process reaches its good handoff.  If every such handoff has a
uniform denominator-`d` continuation in the second process, then the whole
padded first-stage mass is at most `d` times the second-stage mass.


No fixed handoff time and no independence premise occurs. -/
theorem longCutCount_splice
    {A S : Type} {n d : Nat}
    (K : RetryKernel A S n)
    (goodA badA goodB badB : A -> Bool)
    (hd : 1 <= d)
    (hbefore :
      forall a,
        goodA a = false ->
        badA a = false ->
        And (goodB a = false) (badB a = false))
    (hhandoff :
      forall a,
        goodA a = true ->
        forall T,
          n ^ T <=
            d * longCutCount K goodB badB (.active a) T) :
    forall x T,
      longCutCount K goodA badA x T <=
        d * longCutCount K goodB badB x T := by
  intro x T
  induction T generalizing x with
  | zero =>
      cases x with
      | success =>
          simpa [longCutCount] using
            value_le_mul_of_one_le d 1 hd
      | retry s =>
          simp [longCutCount]
      | active a =>
          cases hga : goodA a with
          | true =>
              simpa [longCutCount, hga] using
                hhandoff a hga 0
          | false =>
              cases hba : badA a with
              | true =>
                  simp [longCutCount, hga, hba]
              | false =>
                  have hb := hbefore a hga hba
                  simpa [longCutCount, hga, hba, hb.1, hb.2] using
                    value_le_mul_of_one_le d 1 hd
  | succ T ih =>
      cases x with
      | success =>
          simpa [longCutCount] using
            value_le_mul_of_one_le d (n ^ (T + 1)) hd
      | retry s =>
          simp [longCutCount]
      | active a =>
          cases hga : goodA a with
          | true =>
              simpa [longCutCount, hga] using
                hhandoff a hga (T + 1)
          | false =>
              cases hba : badA a with
              | true =>
                  simp [longCutCount, hga, hba]
              | false =>
                  have hb := hbefore a hga hba
                  simp only [longCutCount, hga, hba, if_false,
                    hb.1, hb.2, Bool.false_eq_true, ↓reduceIte]
                  rw [<- ofFn_sum_mul_left]
                  exact
                    ofFn_sum_le
                      (fun e : Fin n =>
                        longCutCount K goodA badA (K.step a e) T)
                      (fun e : Fin n =>
                        d * longCutCount K goodB badB (K.step a e) T)
                      (fun e => ih (K.step a e))


/-! ## Full nonretry mass is the old attemptNonRetryCount -/


def retryNonRetryNodeCount
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (x : AttemptNode A S) (T : Nat) : Nat :=
  activeCount (retryAsStopStep K) (retryAsStopNode x) T +
    successCount (retryAsStopStep K) (retryAsStopNode x) T


theorem longCutCount_full_eq_retryNonRetryNodeCount
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n) :
    forall x T,
      longCutCount K (fun _ => false) (fun _ => false) x T =
        retryNonRetryNodeCount K x T := by
  intro x T
  induction T generalizing x with
  | zero =>
      cases x <;> rfl
  | succ T ih =>
      cases x with
      | success =>
          simp [longCutCount, retryNonRetryNodeCount,
            activeCount, successCount, retryAsStopNode,
            treeWeight_success, activeWeight, successWeight]
      | retry s =>
          simp [longCutCount, retryNonRetryNodeCount,
            activeCount, successCount, retryAsStopNode,
            treeWeight_failure, activeWeight, successWeight]
      | active a =>
          change
            (List.ofFn (fun e : Fin n =>
              longCutCount K
                (fun _ => false) (fun _ => false)
                (K.step a e) T)).sum =
            (List.ofFn (fun e : Fin n =>
              treeWeight (retryAsStopStep K) activeWeight
                (retryAsStopNode (K.step a e)) T)).sum +
            (List.ofFn (fun e : Fin n =>
              treeWeight (retryAsStopStep K) successWeight
                (retryAsStopNode (K.step a e)) T)).sum
          rw [<- ofFn_sum_add]
          apply ofFn_sum_eq
          intro e
          simpa [retryNonRetryNodeCount, activeCount, successCount] using
            ih (K.step a e)


/-! ## Correct abstract first-factor model -/


/-- The actual progress phase is a multi-hit counter race.  From equal
counters, exact success/failure symmetry plus the node partition gives the
same finite-horizon "winner or still active is at least half" statement used
for restart accounting. -/
theorem counterRace_first_or_active_half
    {X : Type} {n d : Nat}
    (first second : X -> Fin n)
    (next : X -> Fin n -> X)
    (hdistinct : forall x, first x ≠ second x)
    (st : PredictableCounterRaceFiniteTree.ActiveRaceState X d)
    (hcounters : st.firstHits = st.secondHits)
    (T : Nat) :
    n ^ T <=
      2 *
        (activeCount
            (PredictableCounterRaceFiniteTree.counterRaceStep
              first second next)
            (.active st) T +
          successCount
            (PredictableCounterRaceFiniteTree.counterRaceStep
              first second next)
            (.active st) T) := by
  have heq :=
    PredictableCounterRaceFiniteTree.successCount_eq_failureCount_of_counters_eq
      first second next hdistinct st hcounters T
  have hp :=
    node_count_partition
      (PredictableCounterRaceFiniteTree.counterRaceStep
        first second next)
      (.active st) T
  omega


/-! ## Concrete cuts on LongAttemptState -/


/-- First physical handoff into the progress race, or a state already beyond
that handoff.  Including later good stages makes the cut nesting pointwise. -/
def longProgressHandoffCut
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Bool
  | .live _ _ (.race _ _) => true
  | .live _ _ (.incident _) => true
  | .live _ _ (.retained _ _) => true
  | _ => false


/-- Progress race has been won: target is already Ready, or the monitor has
entered the incident/retained suffix. -/
def longRaceWonCut
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Bool
  | .live _ _ (.race .ready _) => true
  | .live _ _ (.incident _) => true
  | .live _ _ (.retained _ _) => true
  | _ => false


/-- Incident orientation has selected the retained branch. -/
def longIncidentWonCut
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Bool
  | .live _ _ (.retained _ _) => true
  | _ => false


/-- Recovery is the bad terminal for every cut above.  Because a preceding
good cut pads immediately, later recovery is never seen by an earlier cut. -/
def longRecoveryCut
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Bool
  | .live _ _ (.recovery _ _) => true
  | _ => false


noncomputable def longProgressEntryMassFrom
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F) (T : Nat) : Nat :=
  longCutCount
    (longAttemptKernel ring F)
    (longProgressHandoffCut ring F)
    (longRecoveryCut ring F)
    (.active a) T


/-- Concrete progress-race target-win-or-still-active mass. -/
noncomputable def longRaceMassFrom
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F) (T : Nat) : Nat :=
  longCutCount
    (longAttemptKernel ring F)
    (longRaceWonCut ring F)
    (longRecoveryCut ring F)
    (.active a) T


/-- Concrete incident-orientation retained-or-still-active mass. -/
noncomputable def longIncidentMassFrom
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F) (T : Nat) : Nat :=
  longCutCount
    (longAttemptKernel ring F)
    (longIncidentWonCut ring F)
    (longRecoveryCut ring F)
    (.active a) T


noncomputable def longFullMassFrom
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F) (T : Nat) : Nat :=
  longCutCount
    (longAttemptKernel ring F)
    (fun _ => false)
    (fun _ => false)
    (.active a) T


noncomputable def longProgressEntryMass
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (T : Nat) : Nat :=
  longProgressEntryMassFrom ring F
    ((longAttemptKernel ring F).start s) T


/-- The requested concrete raceMass on the complete long attempt. -/
noncomputable def longRaceMass
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (T : Nat) : Nat :=
  longRaceMassFrom ring F
    ((longAttemptKernel ring F).start s) T


/-- The requested concrete incidentMass on the complete long attempt. -/
noncomputable def longIncidentMass
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (T : Nat) : Nat :=
  longIncidentMassFrom ring F
    ((longAttemptKernel ring F).start s) T


noncomputable def longFullMass
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (T : Nat) : Nat :=
  longFullMassFrom ring F
    ((longAttemptKernel ring F).start s) T


theorem longFullMassFrom_eq_attemptNonRetryCount
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F) (T : Nat) :
    longFullMassFrom ring F a T =
      attemptNonRetryCount
        (longAttemptKernel ring F) a T := by
  unfold longFullMassFrom attemptNonRetryCount
  have h :=
    longCutCount_full_eq_retryNonRetryNodeCount
      (longAttemptKernel ring F) (.active a) T
  unfold retryNonRetryNodeCount at h
  simpa only [retryAsStopNode] using h


theorem longFullMass_eq_attemptNonRetryCount
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (T : Nat) :
    longFullMass ring F s T =
      attemptNonRetryCount
        (longAttemptKernel ring F)
        ((longAttemptKernel ring F).start s) T := by
  exact
    longFullMassFrom_eq_attemptNonRetryCount
      ring F ((longAttemptKernel ring F).start s) T


/-! ## Pointwise cut nesting -/


private theorem longProgress_before_race_before
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (hentry : longProgressHandoffCut ring F a = false)
    (hrec : longRecoveryCut ring F a = false) :
    And (longRaceWonCut ring F a = false)
      (longRecoveryCut ring F a = false) := by
  refine ⟨?_, hrec⟩
  cases a with
  | junk C =>
      rfl
  | live C hgood stage =>
      cases stage <;>
        simp_all [longProgressHandoffCut,
          longRaceWonCut, longRecoveryCut]


private theorem longRace_before_incident_before
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (hrace : longRaceWonCut ring F a = false)
    (hrec : longRecoveryCut ring F a = false) :
    And (longIncidentWonCut ring F a = false)
      (longRecoveryCut ring F a = false) := by
  refine ⟨?_, hrec⟩
  cases a with
  | junk C =>
      rfl
  | live C hgood stage =>
      cases stage <;>
        simp_all [longRaceWonCut,
          longIncidentWonCut, longRecoveryCut]


/-! ## One concrete residual, no existential masses


This is the remaining physical proof surface.


* `prefixPadding`: no retry/recovery occurs before the first progress-race
  handoff, so the padded entry mass is the complete scheduler space.
* `progressHalf`: at every actual progress-race entry, the literal
  multi-hit race dominates the equal `2b`-versus-`2b` predictable counter
  race.  `counterRace_first_or_active_half` is the abstract counting leaf.
* `incidentHalf`: at every progress-good handoff, the literal
  `L_j`/ `R_j` orientation suffix dominates
  `twoTarget_first_or_active_half`.
* `retainedQuarter`: at every actual retained entry, the raw long-attempt
  nonretry suffix has denominator four.  This is the physical handoff to
  `retainedTrial_cost_nr`, target-cycle compensation,
  `retained_collapse_moment`, `W2_scaled`, and the weighted
  change-of-measure theorems.


Unlike the old `LongAttemptRetryStageFactorSpec`, all masses here are fixed
definitions over `longAttemptKernel`; there are no existential witnesses.
-/
def LongAttemptConcreteStageFactorSpec : Prop :=
  forall (hSealed : SealedStepSpec),
    forall {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 <= F.b ->
      2 * F.b + 1 <= F.a ->
      And
        (forall s,
          AttemptGood ring F s ->
          forall T,
            longProgressEntryMass ring F s T = n ^ T)
        (And
          (forall a,
            longProgressHandoffCut ring F a = true ->
            forall T,
              n ^ T <=
                2 * longRaceMassFrom ring F a T)
          (And
            (forall a,
              longRaceWonCut ring F a = true ->
              forall T,
                n ^ T <=
                  2 * longIncidentMassFrom ring F a T)
            (forall a,
              longIncidentWonCut ring F a = true ->
              forall T,
                n ^ T <=
                  4 * longFullMassFrom ring F a T)))


/-- The concrete local facts splice to the three global factors with the
requested concrete raceMass and incidentMass. -/
theorem longAttemptConcreteStageInequalities
    (hstage : LongAttemptConcreteStageFactorSpec) :
    forall (hSealed : SealedStepSpec),
      forall {n : Nat} (ring : DirectedRing n)
        {C0 : Config n} (F : TripleFrame ring C0),
        2 <= F.b ->
        2 * F.b + 1 <= F.a ->
        forall s,
          AttemptGood ring F s ->
          forall T,
            And
              (n ^ T <= 2 * longRaceMass ring F s T)
              (And
                (longRaceMass ring F s T <=
                  2 * longIncidentMass ring F s T)
                (longIncidentMass ring F s T <=
                  4 *
                    attemptNonRetryCount
                      (longAttemptKernel ring F)
                      ((longAttemptKernel ring F).start s) T)) := by
  intro hSealed n ring C0 F hb hab s hgood T
  rcases hstage hSealed ring F hb hab with
    ⟨hprefix, hprogress, hincident, hretained⟩


  have hspliceProgress :=
    longCutCount_splice
      (K := longAttemptKernel ring F)
      (goodA := longProgressHandoffCut ring F)
      (badA := longRecoveryCut ring F)
      (goodB := longRaceWonCut ring F)
      (badB := longRecoveryCut ring F)
      (d := 2)
      (by decide)
      (fun a ha hb =>
        longProgress_before_race_before ring F a ha hb)
      (fun a ha U => by
        simpa [longRaceMassFrom] using
          hprogress a ha U)
      (.active ((longAttemptKernel ring F).start s)) T


  have hfirst :
      n ^ T <= 2 * longRaceMass ring F s T := by
    calc
      n ^ T = longProgressEntryMass ring F s T :=
        (hprefix s hgood T).symm
      _ <= 2 * longRaceMass ring F s T := by
        simpa [longProgressEntryMass, longProgressEntryMassFrom,
          longRaceMass, longRaceMassFrom] using hspliceProgress


  have hspliceIncident :=
    longCutCount_splice
      (K := longAttemptKernel ring F)
      (goodA := longRaceWonCut ring F)
      (badA := longRecoveryCut ring F)
      (goodB := longIncidentWonCut ring F)
      (badB := longRecoveryCut ring F)
      (d := 2)
      (by decide)
      (fun a ha hb =>
        longRace_before_incident_before ring F a ha hb)
      (fun a ha U => by
        simpa [longIncidentMassFrom] using
          hincident a ha U)
      (.active ((longAttemptKernel ring F).start s)) T


  have hsecond :
      longRaceMass ring F s T <=
        2 * longIncidentMass ring F s T := by
    simpa [longRaceMass, longRaceMassFrom,
      longIncidentMass, longIncidentMassFrom] using hspliceIncident


  have hspliceRetained :=
    longCutCount_splice
      (K := longAttemptKernel ring F)
      (goodA := longIncidentWonCut ring F)
      (badA := longRecoveryCut ring F)
      (goodB := fun _ => false)
      (badB := fun _ => false)
      (d := 4)
      (by decide)
      (fun _ _ _ => ⟨rfl, rfl⟩)
      (fun a ha U => by
        simpa [longFullMassFrom] using
          hretained a ha U)
      (.active ((longAttemptKernel ring F).start s)) T


  have hthird0 :
      longIncidentMass ring F s T <=
        4 * longFullMass ring F s T := by
    simpa [longIncidentMass, longIncidentMassFrom,
      longFullMass, longFullMassFrom] using hspliceRetained


  have hthird :
      longIncidentMass ring F s T <=
        4 *
          attemptNonRetryCount
            (longAttemptKernel ring F)
            ((longAttemptKernel ring F).start s) T := by
    rw [longFullMass_eq_attemptNonRetryCount ring F s T] at hthird0
    exact hthird0


  exact ⟨hfirst, hsecond, hthird⟩


/-- The old existential stage-factor interface follows by choosing the two
concrete masses defined above. -/
theorem longAttemptRetryStageFactors_of_concreteCounts
    (hstage : LongAttemptConcreteStageFactorSpec) :
    LongAttemptRetryStageFactorSpec := by
  unfold LongAttemptRetryStageFactorSpec
  intro hSealed n ring C0 F hb hab s hgood T
  have h :=
    longAttemptConcreteStageInequalities
      hstage hSealed ring F hb hab s hgood T
  exact
    ⟨longRaceMass ring F s T,
      longIncidentMass ring F s T,
      h.1, h.2.1, h.2.2⟩


/-- Consequently the requested long-attempt retry mass follows from exactly
the concrete per-stage residual above. -/
theorem longAttemptRetryMassSpec_of_concreteCounts
    (hstage : LongAttemptConcreteStageFactorSpec) :
    LongAttemptRetryMassSpec := by
  exact
    longAttemptRetryMassSpec_of_stageFactors
      (longAttemptRetryStageFactors_of_concreteCounts hstage)


end PPL.Convergence.LDLocal


#print axioms PPL.Convergence.LDLocal.longCutCount_splice
#print axioms PPL.Convergence.LDLocal.counterRace_first_or_active_half
#print axioms PPL.Convergence.LDLocal.longCutCount_full_eq_retryNonRetryNodeCount
#print axioms PPL.Convergence.LDLocal.longAttemptConcreteStageInequalities
