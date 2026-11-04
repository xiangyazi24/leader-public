import Leader.PPL.Elim.AttemptRetryLongStages

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-!
# Corrected concrete long-stage factors

LongAttemptConcreteStageFactorSpec is too strong because its progress row is
pointwise over the raw LongAttemptState datatype. In particular it demands
the half-factor from synthetic race states such as target phase .ret 0,
although such a phase is not a legal sealed phase and is not reached from a
good long-kernel start.

The correction below is path-based rather than a guessed phase formula:
factor rows are required only on active descendants of the literal
longAttemptKernel start for an AttemptGood configuration. This is the right
carrier for the equal-counter argument: the proof of the progress row may
transport the counter equality along the actual path, while impossible raw
constructors no longer generate obligations.

All three local factor rows are restricted, not only progressHalf. This keeps
the interface robust against the same raw-state defect in later synthetic
.incident or .retained states.
-/

/-! ## Active reachability in a retry kernel -/

/-- Reachability through active children only. Success and retry are terminal,
so they do not create further active states. -/
inductive RetryActiveReachable
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n) (root : A) : A -> Prop where
  | root :
      RetryActiveReachable K root root
  | step {a a' : A} :
      RetryActiveReachable K root a ->
      (e : Fin n) ->
      K.step a e = .active a' ->
      RetryActiveReachable K root a'

/-- The invariant requested by the corrected factor rows: the state comes from
a genuinely good physical start and is an active descendant of that start. -/
def LongAttemptReachableGood
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (a : LongAttemptState ring F) : Prop :=
  And
    (AttemptGood ring F s)
    (RetryActiveReachable
      (longAttemptKernel ring F)
      ((longAttemptKernel ring F).start s)
      a)

/-- Non-vacuity: every good kernel start belongs to the corrected invariant. -/
theorem longAttemptReachableGood_start
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n)
    (hs : AttemptGood ring F s) :
    LongAttemptReachableGood ring F s
      ((longAttemptKernel ring F).start s) := by
  exact
    And.intro hs
      (RetryActiveReachable.root)

/-- Closure is built into the path invariant. -/
theorem longAttemptReachableGood_active_step
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n)
    {a a' : LongAttemptState ring F}
    (e : Fin n)
    (hreach : LongAttemptReachableGood ring F s a)
    (hstep :
      (longAttemptKernel ring F).step a e = .active a') :
    LongAttemptReachableGood ring F s a' := by
  exact
    And.intro hreach.1
      (RetryActiveReachable.step hreach.2 e hstep)

/-! ## Reachability-aware cut splice -/

theorem reachable_value_le_mul_of_one_le
    (d x : Nat) (hd : 1 <= d) :
    x <= d * x := by
  have h := Nat.mul_le_mul_right x hd
  simpa using h

/-- Reachability-aware version of longCutCount_splice.

The old splice asks for the handoff continuation at every raw state satisfying
the Boolean cut. Here it is required only for active states reachable from
the chosen root. The induction itself transports reachability to every active
child, so no probabilistic or independence premise is added. -/
theorem longCutCount_splice_reachable
    {A S : Type} {n d : Nat}
    (K : RetryKernel A S n)
    (root : A)
    (goodA badA goodB badB : A -> Bool)
    (hd : 1 <= d)
    (hbefore :
      forall a,
        goodA a = false ->
        badA a = false ->
        And (goodB a = false) (badB a = false))
    (hhandoff :
      forall a,
        RetryActiveReachable K root a ->
        goodA a = true ->
        forall T,
          n ^ T <=
            d * longCutCount K goodB badB (.active a) T) :
    forall T,
      longCutCount K goodA badA (.active root) T <=
        d * longCutCount K goodB badB (.active root) T := by
  intro T
  have haux :
      forall a,
        RetryActiveReachable K root a ->
        forall U,
          longCutCount K goodA badA (.active a) U <=
            d * longCutCount K goodB badB (.active a) U := by
    intro a hreach U
    induction U generalizing a with
    | zero =>
        cases hga : goodA a with
        | true =>
            simpa [longCutCount, hga] using
              hhandoff a hreach hga 0
        | false =>
            cases hba : badA a with
            | true =>
                simp [longCutCount, hga, hba]
            | false =>
                have hb := hbefore a hga hba
                simpa [longCutCount, hga, hba, hb.1, hb.2] using
                  reachable_value_le_mul_of_one_le d 1 hd
    | succ U ih =>
        cases hga : goodA a with
        | true =>
            simpa [longCutCount, hga] using
              hhandoff a hreach hga (U + 1)
        | false =>
            cases hba : badA a with
            | true =>
                simp [longCutCount, hga, hba]
            | false =>
                have hb := hbefore a hga hba
                simp only [longCutCount, hga, hba, if_false,
                  hb.1, hb.2, Bool.false_eq_true, ↓reduceIte]
                rw [<- ofFn_sum_mul_left]
                apply ofFn_sum_le
                intro e
                cases hstep : K.step a e with
                | success =>
                    simpa [longCutCount] using
                      reachable_value_le_mul_of_one_le
                        d (n ^ U) hd
                | retry s =>
                    simp [longCutCount]
                | active a' =>
                    exact
                      ih a'
                        (RetryActiveReachable.step
                          hreach e hstep)
  exact haux root RetryActiveReachable.root T

/-! ## Public cut-nesting copies

The originals in LDLocalAttemptRetryLongStages are private, so this new file
repeats the two tiny datatype facts under new public names.
-/

theorem longProgress_before_race_before_corrected
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (hentry : longProgressHandoffCut ring F a = false)
    (hrec : longRecoveryCut ring F a = false) :
    And (longRaceWonCut ring F a = false)
      (longRecoveryCut ring F a = false) := by
  refine And.intro ?_ hrec
  cases a with
  | junk C =>
      rfl
  | live C hgood stage =>
      cases stage <;>
        simp_all [longProgressHandoffCut,
          longRaceWonCut, longRecoveryCut]

theorem longRace_before_incident_before_corrected
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (hrace : longRaceWonCut ring F a = false)
    (hrec : longRecoveryCut ring F a = false) :
    And (longIncidentWonCut ring F a = false)
      (longRecoveryCut ring F a = false) := by
  refine And.intro ?_ hrec
  cases a with
  | junk C =>
      rfl
  | live C hgood stage =>
      cases stage <;>
        simp_all [longRaceWonCut,
          longIncidentWonCut, longRecoveryCut]

/-! ## Corrected physical residual -/

/-- Corrected replacement for LongAttemptConcreteStageFactorSpec.

The prefix statement is already rooted at a good start. Each subsequent row
now carries the same good start and an explicit active-reachability witness.
Thus the progress-half proof is permitted to use the equal-counter invariant
transported from the actual race entrance; the synthetic .race (.ret 0) _
counterexample no longer lies in its quantifier domain.

The same reachability restriction is applied to the incident and retained
rows, preventing an analogous raw-constructor defect from reappearing there.
-/
def LongAttemptConcreteStageFactorSpecCorrected : Prop :=
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
          (forall s a,
            LongAttemptReachableGood ring F s a ->
            longProgressHandoffCut ring F a = true ->
            forall T,
              n ^ T <=
                2 * longRaceMassFrom ring F a T)
          (And
            (forall s a,
              LongAttemptReachableGood ring F s a ->
              longRaceWonCut ring F a = true ->
              forall T,
                n ^ T <=
                  2 * longIncidentMassFrom ring F a T)
            (forall s a,
              LongAttemptReachableGood ring F s a ->
              longIncidentWonCut ring F a = true ->
              forall T,
                n ^ T <=
                  4 * longFullMassFrom ring F a T)))

/-! ## Corrected assembly -/

/-- The corrected reachable rows give exactly the same three global finite-tree
factors as the old pointwise spec. -/
theorem longAttemptConcreteStageInequalities_corrected
    (hstage : LongAttemptConcreteStageFactorSpecCorrected) :
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
    longCutCount_splice_reachable
      (K := longAttemptKernel ring F)
      (root := (longAttemptKernel ring F).start s)
      (goodA := longProgressHandoffCut ring F)
      (badA := longRecoveryCut ring F)
      (goodB := longRaceWonCut ring F)
      (badB := longRecoveryCut ring F)
      (d := 2)
      (by decide)
      (fun a ha hr =>
        longProgress_before_race_before_corrected
          ring F a ha hr)
      (fun a hreach ha U => by
        have hgoodReach :
            LongAttemptReachableGood ring F s a :=
          And.intro hgood hreach
        simpa [longRaceMassFrom] using
          hprogress s a hgoodReach ha U)
      T

  have hfirst :
      n ^ T <= 2 * longRaceMass ring F s T := by
    calc
      n ^ T = longProgressEntryMass ring F s T :=
        (hprefix s hgood T).symm
      _ <= 2 * longRaceMass ring F s T := by
        simpa [longProgressEntryMass,
          longProgressEntryMassFrom,
          longRaceMass, longRaceMassFrom] using
            hspliceProgress

  have hspliceIncident :=
    longCutCount_splice_reachable
      (K := longAttemptKernel ring F)
      (root := (longAttemptKernel ring F).start s)
      (goodA := longRaceWonCut ring F)
      (badA := longRecoveryCut ring F)
      (goodB := longIncidentWonCut ring F)
      (badB := longRecoveryCut ring F)
      (d := 2)
      (by decide)
      (fun a ha hr =>
        longRace_before_incident_before_corrected
          ring F a ha hr)
      (fun a hreach ha U => by
        have hgoodReach :
            LongAttemptReachableGood ring F s a :=
          And.intro hgood hreach
        simpa [longIncidentMassFrom] using
          hincident s a hgoodReach ha U)
      T

  have hsecond :
      longRaceMass ring F s T <=
        2 * longIncidentMass ring F s T := by
    simpa [longRaceMass, longRaceMassFrom,
      longIncidentMass, longIncidentMassFrom] using
        hspliceIncident

  have hspliceRetained :=
    longCutCount_splice_reachable
      (K := longAttemptKernel ring F)
      (root := (longAttemptKernel ring F).start s)
      (goodA := longIncidentWonCut ring F)
      (badA := longRecoveryCut ring F)
      (goodB := fun _ => false)
      (badB := fun _ => false)
      (d := 4)
      (by decide)
      (fun _ _ _ => And.intro rfl rfl)
      (fun a hreach ha U => by
        have hgoodReach :
            LongAttemptReachableGood ring F s a :=
          And.intro hgood hreach
        simpa [longFullMassFrom] using
          hretained s a hgoodReach ha U)
      T

  have hthird0 :
      longIncidentMass ring F s T <=
        4 * longFullMass ring F s T := by
    simpa [longIncidentMass, longIncidentMassFrom,
      longFullMass, longFullMassFrom] using
        hspliceRetained

  have hthird :
      longIncidentMass ring F s T <=
        4 *
          attemptNonRetryCount
            (longAttemptKernel ring F)
            ((longAttemptKernel ring F).start s) T := by
    rw [longFullMass_eq_attemptNonRetryCount
      ring F s T] at hthird0
    exact hthird0

  exact And.intro hfirst (And.intro hsecond hthird)

/-- The original downstream existential interface is recovered without ever
asserting the false raw-state factor spec. -/
theorem longAttemptRetryStageFactors_of_concreteCounts_corrected
    (hstage : LongAttemptConcreteStageFactorSpecCorrected) :
    LongAttemptRetryStageFactorSpec := by
  unfold LongAttemptRetryStageFactorSpec
  intro hSealed n ring C0 F hb hab s hgood T
  have h :=
    longAttemptConcreteStageInequalities_corrected
      hstage hSealed ring F hb hab s hgood T
  exact
    ⟨longRaceMass ring F s T,
      longIncidentMass ring F s T,
      h.1, h.2.1, h.2.2⟩

/-- Hence the same long retry-mass theorem follows from the corrected,
reachable-only concrete rows. -/
theorem longAttemptRetryMassSpec_of_concreteCounts_corrected
    (hstage : LongAttemptConcreteStageFactorSpecCorrected) :
    LongAttemptRetryMassSpec := by
  exact
    longAttemptRetryMassSpec_of_stageFactors
      (longAttemptRetryStageFactors_of_concreteCounts_corrected
        hstage)

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.longAttemptReachableGood_start
#print axioms PPL.Convergence.LDLocal.longAttemptReachableGood_active_step
#print axioms PPL.Convergence.LDLocal.reachable_value_le_mul_of_one_le
#print axioms PPL.Convergence.LDLocal.longCutCount_splice_reachable
#print axioms PPL.Convergence.LDLocal.longProgress_before_race_before_corrected
#print axioms PPL.Convergence.LDLocal.longRace_before_incident_before_corrected
#print axioms PPL.Convergence.LDLocal.longAttemptConcreteStageInequalities_corrected
#print axioms PPL.Convergence.LDLocal.longAttemptRetryStageFactors_of_concreteCounts_corrected
#print axioms PPL.Convergence.LDLocal.longAttemptRetryMassSpec_of_concreteCounts_corrected
