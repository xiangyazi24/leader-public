import Leader.PPL.Elim.AttemptRetryLongStagesCorrected


namespace PPL.Convergence.LDLocal


set_option autoImplicit false
set_option Elab.async false


open FiniteUniformStoppingTree


/-!
# First-cut long retry factors


The corrected spec `LongAttemptConcreteStageFactorSpecCorrected` is too broad because active reachability includes descendants after a cut.
The generic carrier below records the active path only while the cut is false,
then records exactly the first active child on which the cut becomes true.
-/


/-! ## 1. Generic first-cut carriers -/


inductive RetryActiveBeforeCut
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (cut : A -> Bool) (root : A) : A -> Prop where
  | root (hroot : cut root = false) :
      RetryActiveBeforeCut K cut root root
  | step {a a' : A} :
      RetryActiveBeforeCut K cut root a ->
      (e : Fin n) ->
      K.step a e = .active a' ->
      cut a' = false ->
      RetryActiveBeforeCut K cut root a'


def RetryFirstCutReachable
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (cut : A -> Bool) (root a : A) : Prop :=
  Or
    (And (a = root) (cut root = true))
    (Exists fun p =>
      And
        (RetryActiveBeforeCut K cut root p)
        (Exists fun e : Fin n =>
          And (K.step p e = .active a)
            (cut a = true)))


theorem retryActiveBeforeCut_cut_false
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (cut : A -> Bool) (root a : A)
    (h : RetryActiveBeforeCut K cut root a) :
    cut a = false := by
  cases h with
  | root hroot =>
      exact hroot
  | step h e hstep hcut =>
      exact hcut


theorem retryActiveBeforeCut_to_reachable
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (cut : A -> Bool) (root a : A)
    (h : RetryActiveBeforeCut K cut root a) :
    RetryActiveReachable K root a := by
  induction h with
  | root hroot =>
      exact RetryActiveReachable.root
  | step h e hstep hcut ih =>
      exact RetryActiveReachable.step ih e hstep


theorem retryFirstCut_to_reachable
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (cut : A -> Bool) (root a : A)
    (h : RetryFirstCutReachable K cut root a) :
    RetryActiveReachable K root a := by
  rcases h with hroot | hstep
  · exact hroot.1 ▸ RetryActiveReachable.root
  · rcases hstep with ⟨p, hp, e, hpa, hcut⟩
    exact
      RetryActiveReachable.step
        (retryActiveBeforeCut_to_reachable
          K cut root p hp)
        e hpa


theorem retryFirstCut_of_before_step
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (cut : A -> Bool) (root p a : A)
    (hp : RetryActiveBeforeCut K cut root p)
    (e : Fin n)
    (hstep : K.step p e = .active a)
    (hcut : cut a = true) :
    RetryFirstCutReachable K cut root a := by
  exact Or.inr
    ⟨p, hp, e, And.intro hstep hcut⟩


/-! ## 2. First-cut splice -/


private theorem longCutCount_splice_firstCut_aux
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
        RetryFirstCutReachable K goodA root a ->
        goodA a = true ->
        forall T,
          n ^ T <= d * longCutCount K goodB badB (.active a) T)
    (a : A)
    (ha : RetryActiveBeforeCut K goodA root a) :
    forall T,
      longCutCount K goodA badA (.active a) T <=
        d * longCutCount K goodB badB (.active a) T := by
  intro T
  induction T generalizing a with
  | zero =>
      have hga :=
        retryActiveBeforeCut_cut_false
          K goodA root a ha
      by_cases hba : badA a = true
      · simp [longCutCount, hga, hba]
      · have hba0 : badA a = false := by
          cases h : badA a with
          | false => rfl
          | true => exact False.elim (hba h)
        have hb := hbefore a hga hba0
        simp [longCutCount, hga, hba0, hb.1, hb.2]
        exact hd
  | succ T ih =>
      have hga :=
        retryActiveBeforeCut_cut_false
          K goodA root a ha
      by_cases hba : badA a = true
      · simp [longCutCount, hga, hba]
      · have hba0 : badA a = false := by
          cases h : badA a with
          | false => rfl
          | true => exact False.elim (hba h)
        have hb := hbefore a hga hba0
        simp only [longCutCount, hga, hba0, hb.1, hb.2,
          Bool.false_eq_true, if_false]
        have hpoint :
            forall e : Fin n,
              longCutCount K goodA badA (K.step a e) T <=
                d * longCutCount K goodB badB (K.step a e) T := by
          intro e
          cases hstep : K.step a e with
          | success =>
              unfold longCutCount
              calc
                n ^ T = 1 * n ^ T := (Nat.one_mul _).symm
                _ <= d * n ^ T :=
                  Nat.mul_le_mul_right (n ^ T) hd
          | retry s =>
              simp [longCutCount]
          | active a' =>
              by_cases hcut : goodA a' = true
              · have hleft :
                    longCutCount K goodA badA (.active a') T =
                      n ^ T := by
                  cases T <;> simp [longCutCount, hcut]
                rw [hleft]
                exact
                  hhandoff a'
                    (retryFirstCut_of_before_step
                      K goodA root a a' ha e hstep hcut)
                    hcut T
              · have hcut0 : goodA a' = false := by
                  cases h : goodA a' with
                  | false => rfl
                  | true => exact False.elim (hcut h)
                exact
                  ih a'
                    (RetryActiveBeforeCut.step
                      ha e hstep hcut0)
        have hsum :=
          ofFn_sum_le
            (fun e : Fin n =>
              longCutCount K goodA badA (K.step a e) T)
            (fun e : Fin n =>
              d * longCutCount K goodB badB (K.step a e) T)
            hpoint
        calc
          (List.ofFn (fun e : Fin n =>
            longCutCount K goodA badA (K.step a e) T)).sum
              <=
            (List.ofFn (fun e : Fin n =>
              d * longCutCount K goodB badB (K.step a e) T)).sum :=
            hsum
          _ =
            d *
              (List.ofFn (fun e : Fin n =>
                longCutCount K goodB badB (K.step a e) T)).sum :=
            ofFn_sum_mul_left d
              (fun e : Fin n =>
                longCutCount K goodB badB (K.step a e) T)


theorem longCutCount_splice_firstCut
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
        RetryFirstCutReachable K goodA root a ->
        goodA a = true ->
        forall T,
          n ^ T <= d * longCutCount K goodB badB (.active a) T) :
    forall T,
      longCutCount K goodA badA (.active root) T <=
        d * longCutCount K goodB badB (.active root) T := by
  intro T
  cases hroot : goodA root with
  | true =>
      have hleft :
          longCutCount K goodA badA (.active root) T =
            n ^ T := by
        cases T <;> simp [longCutCount, hroot]
      rw [hleft]
      exact
        hhandoff root
          (Or.inl (And.intro rfl hroot))
          hroot T
  | false =>
      exact
        longCutCount_splice_firstCut_aux
          K root goodA badA goodB badB hd hbefore hhandoff
          root
          (RetryActiveBeforeCut.root hroot)
          T


/-! ## 3. Long first-cut carriers and the first-cut statement -/


def LongAttemptFirstProgressGood
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (a : LongAttemptState ring F) : Prop :=
  And
    (AttemptGood ring F s)
    (RetryFirstCutReachable
      (longAttemptKernel ring F)
      (longProgressHandoffCut ring F)
      ((longAttemptKernel ring F).start s)
      a)


def LongAttemptFirstRaceGood
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (a : LongAttemptState ring F) : Prop :=
  And
    (AttemptGood ring F s)
    (RetryFirstCutReachable
      (longAttemptKernel ring F)
      (longRaceWonCut ring F)
      ((longAttemptKernel ring F).start s)
      a)


def LongAttemptFirstIncidentGood
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (a : LongAttemptState ring F) : Prop :=
  And
    (AttemptGood ring F s)
    (RetryFirstCutReachable
      (longAttemptKernel ring F)
      (longIncidentWonCut ring F)
      ((longAttemptKernel ring F).start s)
      a)


/-- Non-vacuity constructor: an actual first handoff from a before-cut path is
a first-cut state, with the original good start retained. -/
theorem longAttempt_firstProgressHandoff_is_firstCut
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n)
    (hs : AttemptGood ring F s)
    (p a : LongAttemptState ring F)
    (hp :
      RetryActiveBeforeCut
        (longAttemptKernel ring F)
        (longProgressHandoffCut ring F)
        ((longAttemptKernel ring F).start s)
        p)
    (e : Fin n)
    (hstep :
      (longAttemptKernel ring F).step p e = .active a)
    (hcut : longProgressHandoffCut ring F a = true) :
    LongAttemptFirstProgressGood ring F s a := by
  exact
    And.intro hs
      (retryFirstCut_of_before_step
        (longAttemptKernel ring F)
        (longProgressHandoffCut ring F)
        ((longAttemptKernel ring F).start s)
        p a hp e hstep hcut)


def LongAttemptFirstCutStageFactorSpec : Prop :=
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
            LongAttemptFirstProgressGood ring F s a ->
            longProgressHandoffCut ring F a = true ->
            forall T,
              n ^ T <= 2 * longRaceMassFrom ring F a T)
          (And
            (forall s a,
              LongAttemptFirstRaceGood ring F s a ->
              longRaceWonCut ring F a = true ->
              forall T,
                n ^ T <= 2 * longIncidentMassFrom ring F a T)
            (forall s a,
              LongAttemptFirstIncidentGood ring F s a ->
              longIncidentWonCut ring F a = true ->
              forall T,
                n ^ T <= 4 * longFullMassFrom ring F a T)))


/-! ## 4. The first-cut spec still implies the global retry-mass theorem -/


theorem longAttemptFirstCutStageInequalities
    (hstage : LongAttemptFirstCutStageFactorSpec) :
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
    ⟨hprefix, hprogress, hrace, hincident⟩


  let root : LongAttemptState ring F :=
    (longAttemptKernel ring F).start s


  have hspliceProgress :=
    longCutCount_splice_firstCut
      (K := longAttemptKernel ring F)
      (root := root)
      (goodA := longProgressHandoffCut ring F)
      (badA := longRecoveryCut ring F)
      (goodB := longRaceWonCut ring F)
      (badB := longRecoveryCut ring F)
      (d := 2)
      (by decide)
      (fun a ha hb =>
        longProgress_before_race_before_corrected ring F a ha hb)
      (fun a hfirst ha U => by
        simpa [longRaceMassFrom] using
          hprogress s a
            (And.intro hgood hfirst)
            ha U)
      T


  have hfirst :
      n ^ T <= 2 * longRaceMass ring F s T := by
    calc
      n ^ T = longProgressEntryMass ring F s T :=
        (hprefix s hgood T).symm
      _ <= 2 * longRaceMass ring F s T := by
        simpa [root, longProgressEntryMass,
          longProgressEntryMassFrom,
          longRaceMass, longRaceMassFrom]
          using hspliceProgress


  have hspliceIncident :=
    longCutCount_splice_firstCut
      (K := longAttemptKernel ring F)
      (root := root)
      (goodA := longRaceWonCut ring F)
      (badA := longRecoveryCut ring F)
      (goodB := longIncidentWonCut ring F)
      (badB := longRecoveryCut ring F)
      (d := 2)
      (by decide)
      (fun a ha hb =>
        longRace_before_incident_before_corrected ring F a ha hb)
      (fun a hfirst ha U => by
        simpa [longIncidentMassFrom] using
          hrace s a
            (And.intro hgood hfirst)
            ha U)
      T


  have hsecond :
      longRaceMass ring F s T <=
        2 * longIncidentMass ring F s T := by
    simpa [root, longRaceMass, longRaceMassFrom,
      longIncidentMass, longIncidentMassFrom]
      using hspliceIncident


  have hspliceRetained :=
    longCutCount_splice_firstCut
      (K := longAttemptKernel ring F)
      (root := root)
      (goodA := longIncidentWonCut ring F)
      (badA := longRecoveryCut ring F)
      (goodB := fun _ => false)
      (badB := fun _ => false)
      (d := 4)
      (by decide)
      (fun _ _ _ => And.intro rfl rfl)
      (fun a hfirst ha U => by
        simpa [longFullMassFrom] using
          hincident s a
            (And.intro hgood hfirst)
            ha U)
      T


  have hthird0 :
      longIncidentMass ring F s T <=
        4 * longFullMass ring F s T := by
    simpa [root, longIncidentMass, longIncidentMassFrom,
      longFullMass, longFullMassFrom] using hspliceRetained


  have hthird :
      longIncidentMass ring F s T <=
        4 *
          attemptNonRetryCount
            (longAttemptKernel ring F)
            ((longAttemptKernel ring F).start s) T := by
    rw [longFullMass_eq_attemptNonRetryCount ring F s T] at hthird0
    exact hthird0


  exact And.intro hfirst (And.intro hsecond hthird)


theorem longAttemptRetryStageFactors_of_firstCutCounts
    (hstage : LongAttemptFirstCutStageFactorSpec) :
    LongAttemptRetryStageFactorSpec := by
  unfold LongAttemptRetryStageFactorSpec
  intro hSealed n ring C0 F hb hab s hgood T
  have h :=
    longAttemptFirstCutStageInequalities
      hstage hSealed ring F hb hab s hgood T
  exact
    ⟨longRaceMass ring F s T,
      longIncidentMass ring F s T,
      h.1, h.2.1, h.2.2⟩


theorem longAttemptRetryMassSpec_of_firstCutCounts
    (hstage : LongAttemptFirstCutStageFactorSpec) :
    LongAttemptRetryMassSpec := by
  exact
    longAttemptRetryMassSpec_of_stageFactors
      (longAttemptRetryStageFactors_of_firstCutCounts hstage)


/-! ## 5. Entry-mass repair -/


/-- Public mirror of the private long-start CR choice. -/
private noncomputable def publicRowsCRInitMode
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n)
    (hPB : PPL.Elim.PB ring D)
    (halive : ¬ EndpointDeleted A D)
    (hclean : ¬ CleanReady A D) : CRMode :=
  Classical.choose
    (crRankInit ring A D hPB
      (by
        intro hdone
        rcases hdone with hdel | hready
        · exact halive hdel
        · exact hclean hready))


private noncomputable def publicRowsAfterTargetStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : LongStage := by
  classical
  if hA : CleanReady F.A D then
    exact .liveWait .ready .ready
  else
    exact .attackerCR .ready
      (publicRowsCRInitMode ring F.A D hgood.1
        (by
          intro h
          exact hgood.2.1 (endpointA_deleted_tagged F D h))
        hA)


private noncomputable def publicRowsInitialStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : LongStage := by
  classical
  if hB : CleanReady F.B D then
    exact publicRowsAfterTargetStage ring F D hgood
  else
    exact .targetCR
      (publicRowsCRInitMode ring F.B D hgood.1
        (by
          intro h
          exact hgood.2.1 (endpointB_deleted_tagged F D h))
        hB)


private noncomputable def publicRowsStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) : LongAttemptState ring F := by
  classical
  if hgood : AttemptGood ring F D then
    exact .live D hgood (publicRowsInitialStage ring F D hgood)
  else
    exact .junk D


theorem longStart_eq_publicRowsStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) :
    (longAttemptKernel ring F).start D =
      publicRowsStart ring F D := by
  rfl


def LongProgressEntryOneStep : Prop :=
  forall {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F) (e : Fin n),
    longProgressHandoffCut ring F a = false ->
    longRecoveryCut ring F a = false ->
    match (longAttemptKernel ring F).step a e with
    | .success => True
    | .retry _ => False
    | .active a' => longRecoveryCut ring F a' = false


/--
Public-interface residual for the private target-CR handoff constructor.

The source definition longAfterTargetStage in LDLocalAttempt.lean has exactly
two outputs: liveWait ready ready when CleanReady F.A holds, and attackerCR
ready _ otherwise.  Hence it never produces recovery.  Current main exports no
public output-classification theorem for that private definition, so the exact
fact needed by this downstream row is kept explicit here.
-/
def LongTargetCRDoneRecoveryFree : Prop :=
  forall {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (mode : CRMode) (e : Fin n)
    (a' : LongAttemptState ring F),
    CRModeHolds F.B C mode ->
    CRDone F.B (stepE ring C e) ->
    (longAttemptKernel ring F).step
        (.live C hgood (.targetCR mode)) e = .active a' ->
    longRecoveryCut ring F a' = false


theorem longProgressEntryOneStep
    (hAfter : LongTargetCRDoneRecoveryFree) :
    LongProgressEntryOneStep := by
  unfold LongProgressEntryOneStep
  intro n ring C0 F a e hentry hrec
  classical
  cases a with
  | junk C =>
      simp only [longAttemptKernel]
      unfold longStep
      exact True.intro
  | live C hgood stage =>
      cases stage with
      | targetCR mode =>
          simp only [longAttemptKernel]
          unfold longStep
          dsimp only
          by_cases htag : TaggedDeleted F (stepE ring C e)
          · rw [dif_pos htag]
            exact True.intro
          · rw [dif_neg htag]
            by_cases hmode : CRModeHolds F.B C mode
            · rw [dif_pos hmode]
              by_cases hdone : CRDone F.B (stepE ring C e)
              · rw [dif_pos hdone]
                apply hAfter ring F C hgood mode e
                · exact hmode
                · exact hdone
                · simp only [longAttemptKernel]
                  unfold longStep
                  dsimp only
                  rw [dif_neg htag, dif_pos hmode, dif_pos hdone]
              · rw [dif_neg hdone]
                simp [longRecoveryCut]
            · rw [dif_neg hmode]
              simp [longRecoveryCut]
      | attackerCR targetPhase mode =>
          simp only [longAttemptKernel]
          unfold longStep
          dsimp only
          by_cases htag : TaggedDeleted F (stepE ring C e)
          · rw [dif_pos htag]
            exact True.intro
          · rw [dif_neg htag]
            by_cases hmode : CRModeHolds F.A C mode
            · rw [dif_pos hmode]
              by_cases hdone : CRDone F.A (stepE ring C e)
              · rw [dif_pos hdone]
                simp [longRecoveryCut]
              · rw [dif_neg hdone]
                simp [longRecoveryCut]
            · rw [dif_neg hmode]
              simp [longRecoveryCut]
      | liveWait targetPhase attackPhase =>
          simp only [longAttemptKernel]
          unfold longStep
          dsimp only
          by_cases htag : TaggedDeleted F (stepE ring C e)
          · rw [dif_pos htag]
            exact True.intro
          · rw [dif_neg htag]
            by_cases hfire :
                attackPhase = .ready ∧ e = F.A.left
            · by_cases hnear : F.a - 2 * F.b <= 1
              · simp [hfire, hnear, longRecoveryCut]
              · simp [hfire, hnear, longRecoveryCut]
            · simp [hfire, longRecoveryCut]
      | advance targetPhase attackPhase =>
          simp only [longAttemptKernel]
          unfold longStep
          dsimp only
          by_cases htag : TaggedDeleted F (stepE ring C e)
          · rw [dif_pos htag]
            exact True.intro
          · rw [dif_neg htag]
            by_cases hreach :
                nextSectorPhase F.A attackPhase e =
                  .live (F.a - 2 * F.b)
            · simp [hreach, longRecoveryCut]
            · simp [hreach, longRecoveryCut]
      | race targetPhase attackPhase =>
          unfold longProgressHandoffCut at hentry
          cases hentry
      | incident attackPhase =>
          unfold longProgressHandoffCut at hentry
          cases hentry
      | retained targetPhase attackPhase =>
          unfold longProgressHandoffCut at hentry
          cases hentry
      | recovery targetPhase attackPhase =>
          unfold longRecoveryCut at hrec
          cases hrec
      | stuck =>
          simp only [longAttemptKernel]
          unfold longStep
          dsimp only
          by_cases htag : TaggedDeleted F (stepE ring C e)
          · rw [dif_pos htag]
            exact True.intro
          · rw [dif_neg htag]
            simp [longRecoveryCut]


theorem longProgressStart_before
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s) :
    And
      (longProgressHandoffCut ring F
        ((longAttemptKernel ring F).start s) = false)
      (longRecoveryCut ring F
        ((longAttemptKernel ring F).start s) = false) := by
  classical
  rw [longStart_eq_publicRowsStart]
  unfold publicRowsStart
  rw [dif_pos hs]
  unfold publicRowsInitialStage
  by_cases hB : CleanReady F.B s
  · rw [dif_pos hB]
    unfold publicRowsAfterTargetStage
    by_cases hA : CleanReady F.A s
    · rw [dif_pos hA]
      exact And.intro rfl rfl
    · rw [dif_neg hA]
      exact And.intro rfl rfl
  · rw [dif_neg hB]
    exact And.intro rfl rfl


theorem longProgressEntryMassFrom_eq_pow
    (hAfter : LongTargetCRDoneRecoveryFree)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (hentry : longProgressHandoffCut ring F a = false)
    (hrec : longRecoveryCut ring F a = false) :
    forall T,
      longProgressEntryMassFrom ring F a T = n ^ T := by
  intro T
  induction T generalizing a with
  | zero =>
      simp [longProgressEntryMassFrom, longCutCount, hentry, hrec]
  | succ T ih =>
      have hchild :
          forall e : Fin n,
            longCutCount
                (longAttemptKernel ring F)
                (longProgressHandoffCut ring F)
                (longRecoveryCut ring F)
                ((longAttemptKernel ring F).step a e) T =
              n ^ T := by
        intro e
        have hrow :=
          longProgressEntryOneStep
            hAfter ring F a e hentry hrec
        cases hstep :
            (longAttemptKernel ring F).step a e with
        | success =>
            simp [longCutCount]
        | retry s =>
            rw [hstep] at hrow
            exact False.elim hrow
        | active a' =>
            have hrec' :
                longRecoveryCut ring F a' = false := by
              simpa [hstep] using hrow
            cases hcut :
                longProgressHandoffCut ring F a' with
            | true =>
                cases T with
                | zero =>
                    simp [longCutCount, hcut]
                | succ U =>
                    simp [longCutCount, hcut]
            | false =>
                simpa [longProgressEntryMassFrom] using
                  ih a' hcut hrec'
      unfold longProgressEntryMassFrom
      simp only [longCutCount, hentry, hrec,
        Bool.false_eq_true, if_false]
      calc
        (List.ofFn (fun e : Fin n =>
          longCutCount
            (longAttemptKernel ring F)
            (longProgressHandoffCut ring F)
            (longRecoveryCut ring F)
            ((longAttemptKernel ring F).step a e) T)).sum =
            (List.ofFn (fun _ : Fin n => n ^ T)).sum :=
          ofFn_sum_eq _ _ hchild
        _ = n * n ^ T := ofFn_sum_const n (n ^ T)
        _ = n ^ (T + 1) := by
          rw [Nat.pow_succ]
          ac_rfl


theorem longProgressEntryMass_eq_pow
    (_hSealed : SealedStepSpec)
    (hAfter : LongTargetCRDoneRecoveryFree)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (_hb : 2 <= F.b)
    (_hab : 2 * F.b + 1 <= F.a) :
    forall s,
      AttemptGood ring F s ->
      forall T,
        longProgressEntryMass ring F s T = n ^ T := by
  intro s hs T
  have hstart := longProgressStart_before ring F s hs
  have h :=
    longProgressEntryMassFrom_eq_pow
      hAfter ring F
      ((longAttemptKernel ring F).start s)
      hstart.1 hstart.2 T
  change
    longProgressEntryMassFrom ring F
      ((longAttemptKernel ring F).start s) T = n ^ T
  exact h


/-!
The theorem above is first-cut conjunct 1 and repairs all four draft
errors: targetCR is split on the post-step A CleanReady test, the two start
goals are discharged by explicit B/A classification, and the impossible retry
branch is eliminated by rewriting the exact step equation into the row fact.
-/


/-! ## 6. Closed counterexample to the corrected spec: finite mirrors and the one bounded residual -/


private abbrev correctedCexRing : DirectedRing 7 := ⟨by decide⟩


private abbrev correctedCexQ0 : Fin 7 := ⟨0, by decide⟩
private abbrev correctedCexQ1 : Fin 7 := ⟨1, by decide⟩
private abbrev correctedCexQ2 : Fin 7 := ⟨2, by decide⟩
private abbrev correctedCexQ3 : Fin 7 := ⟨3, by decide⟩
private abbrev correctedCexQ4 : Fin 7 := ⟨4, by decide⟩
private abbrev correctedCexQ5 : Fin 7 := ⟨5, by decide⟩
private abbrev correctedCexQ6 : Fin 7 := ⟨6, by decide⟩


private def correctedCexFollower : PPL.Elim.Cell4 where
  leader := false
  bullet := 0
  shield := false
  signalB := false


private def correctedCexLeaderHot : PPL.Elim.Cell4 where
  leader := true
  bullet := 0
  shield := true
  signalB := true


private def correctedCexStart : Config 7 :=
  fun x =>
    if x = correctedCexQ0 then correctedCexLeaderHot
    else if x = correctedCexQ5 then correctedCexLeaderHot
    else correctedCexFollower


private def correctedCexFrameA : SectorFrame correctedCexRing correctedCexStart where
  left := correctedCexQ0
  right := correctedCexQ5
  gap := 5
  gap_pos := by decide
  gap_lt_n := by decide
  left_ne_right := by decide
  right_eq := by rfl
  left_leader := by rfl
  right_leader := by rfl
  interior_follower := by
    intro q hq0 hq5
    have hcases :
        Or (q = 1) (Or (q = 2) (Or (q = 3) (q = 4))) := by
      omega
    rcases hcases with h | h | h | h <;> subst q <;> rfl


private def correctedCexFrameB : SectorFrame correctedCexRing correctedCexStart where
  left := correctedCexQ5
  right := correctedCexQ0
  gap := 2
  gap_pos := by decide
  gap_lt_n := by decide
  left_ne_right := by decide
  right_eq := by rfl
  left_leader := by rfl
  right_leader := by rfl
  interior_follower := by
    intro q hq0 hq2
    have hq : q = 1 := by omega
    subst q
    rfl


private def correctedCexFrame : TripleFrame correctedCexRing correctedCexStart where
  i := correctedCexQ0
  j := correctedCexQ5
  k := correctedCexQ0
  a := 5
  b := 2
  A := correctedCexFrameA
  B := correctedCexFrameB
  A_left := rfl
  A_right := rfl
  A_gap := rfl
  B_left := rfl
  B_right := rfl
  B_gap := rfl
  span := Or.inl (And.intro rfl rfl)


private theorem correctedCex_fin7_cases (e : Fin 7) :
    Or (e = correctedCexQ0)
      (Or (e = correctedCexQ1)
        (Or (e = correctedCexQ2)
          (Or (e = correctedCexQ3)
            (Or (e = correctedCexQ4)
              (Or (e = correctedCexQ5) (e = correctedCexQ6)))))) := by
  rcases e with ⟨v, hv⟩
  rcases v with _ | _ | _ | _ | _ | _ | _ | v
  · exact Or.inl (by apply Fin.ext; rfl)
  · exact Or.inr (Or.inl (by apply Fin.ext; rfl))
  · exact Or.inr (Or.inr (Or.inl (by apply Fin.ext; rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (by apply Fin.ext; rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by apply Fin.ext; rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by apply Fin.ext; rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (by apply Fin.ext; rfl))))))
  · omega


/-- Bool mirror for closed configuration equality. -/
private def correctedCexConfigEqB (C D : Config 7) : Bool :=
  decide
    (And (C correctedCexQ0 = D correctedCexQ0)
      (And (C correctedCexQ1 = D correctedCexQ1)
        (And (C correctedCexQ2 = D correctedCexQ2)
          (And (C correctedCexQ3 = D correctedCexQ3)
            (And (C correctedCexQ4 = D correctedCexQ4)
              (And (C correctedCexQ5 = D correctedCexQ5)
                (C correctedCexQ6 = D correctedCexQ6)))))))


private theorem correctedCexConfigEqB_true_iff (C D : Config 7) :
    correctedCexConfigEqB C D = true ↔ C = D := by
  unfold correctedCexConfigEqB
  rw [decide_eq_true_eq]
  constructor
  · intro h
    funext x
    rcases correctedCex_fin7_cases x with
      hx | hx | hx | hx | hx | hx | hx
    · subst x; exact h.1
    · subst x; exact h.2.1
    · subst x; exact h.2.2.1
    · subst x; exact h.2.2.2.1
    · subst x; exact h.2.2.2.2.1
    · subst x; exact h.2.2.2.2.2.1
    · subst x; exact h.2.2.2.2.2.2
  · intro h
    subst D
    exact
      And.intro rfl
        (And.intro rfl
          (And.intro rfl
            (And.intro rfl
              (And.intro rfl
                (And.intro rfl rfl)))))


/-- Bool mirror for the two tagged leaders. -/
private def correctedCexTaggedAliveB (C : Config 7) : Bool :=
  decide
    (And ((C correctedCexQ0).leader = true)
      ((C correctedCexQ5).leader = true))


private theorem correctedCexTaggedAliveB_true_iff (C : Config 7) :
    correctedCexTaggedAliveB C = true ↔
      ¬ TaggedDeleted correctedCexFrame C := by
  unfold correctedCexTaggedAliveB
  rw [decide_eq_true_eq]
  unfold TaggedDeleted
  simp only [correctedCexFrame]
  cases h0 : (C correctedCexQ0).leader <;>
    cases h5 : (C correctedCexQ5).leader <;>
    simp [h0, h5]


private theorem correctedCexStart_pbB :
    PPL.Elim.pbB correctedCexRing correctedCexStart = true := by
  decide


private theorem correctedCexStart_pb :
    PPL.Elim.PB correctedCexRing correctedCexStart :=
  (PPL.Elim.pbB_true_iff correctedCexRing correctedCexStart).1 correctedCexStart_pbB


private theorem correctedCexStart_good :
    AttemptGood correctedCexRing correctedCexFrame correctedCexStart :=
  attemptGood_initial correctedCexRing correctedCexStart correctedCexStart_pb correctedCexFrame


private theorem correctedCexStart_cleanA :
    CleanReady correctedCexFrame.A correctedCexStart := by
  apply And.intro rfl
  intro q hq
  change q < 5 at hq
  have hcases :
      Or (q = 0) (Or (q = 1) (Or (q = 2) (Or (q = 3) (q = 4)))) := by
    omega
  rcases hcases with h | h | h | h | h <;> subst q <;> rfl


private theorem correctedCexStart_cleanB :
    CleanReady correctedCexFrame.B correctedCexStart := by
  apply And.intro rfl
  intro q hq
  change q < 2 at hq
  have hcases : Or (q = 0) (q = 1) := by
    omega
  rcases hcases with h | h <;> subst q <;> rfl


private def correctedCexC1 : Config 7 := stepE correctedCexRing correctedCexStart correctedCexQ5
private def correctedCexC2 : Config 7 := stepE correctedCexRing correctedCexC1 correctedCexQ0
private def correctedCexC3 : Config 7 := stepE correctedCexRing correctedCexC2 correctedCexQ1
private def correctedCexC4 : Config 7 := stepE correctedCexRing correctedCexC3 correctedCexQ2
private def correctedCexC5 : Config 7 := stepE correctedCexRing correctedCexC4 correctedCexQ3


private theorem correctedCexC1_alive : ¬ TaggedDeleted correctedCexFrame correctedCexC1 := by
  apply (correctedCexTaggedAliveB_true_iff correctedCexC1).1
  decide


private theorem correctedCexC2_alive : ¬ TaggedDeleted correctedCexFrame correctedCexC2 := by
  apply (correctedCexTaggedAliveB_true_iff correctedCexC2).1
  decide


private theorem correctedCexC3_alive : ¬ TaggedDeleted correctedCexFrame correctedCexC3 := by
  apply (correctedCexTaggedAliveB_true_iff correctedCexC3).1
  decide


private theorem correctedCexC4_alive : ¬ TaggedDeleted correctedCexFrame correctedCexC4 := by
  apply (correctedCexTaggedAliveB_true_iff correctedCexC4).1
  decide


private theorem correctedCexC5_alive : ¬ TaggedDeleted correctedCexFrame correctedCexC5 := by
  apply (correctedCexTaggedAliveB_true_iff correctedCexC5).1
  decide


private theorem correctedCexGood1 : AttemptGood correctedCexRing correctedCexFrame correctedCexC1 :=
  attemptGood_step correctedCexRing correctedCexFrame correctedCexStart correctedCexQ5 correctedCexStart_good correctedCexC1_alive


private theorem correctedCexGood2 : AttemptGood correctedCexRing correctedCexFrame correctedCexC2 :=
  attemptGood_step correctedCexRing correctedCexFrame correctedCexC1 correctedCexQ0 correctedCexGood1 correctedCexC2_alive


private theorem correctedCexGood3 : AttemptGood correctedCexRing correctedCexFrame correctedCexC3 :=
  attemptGood_step correctedCexRing correctedCexFrame correctedCexC2 correctedCexQ1 correctedCexGood2 correctedCexC3_alive


private theorem correctedCexGood4 : AttemptGood correctedCexRing correctedCexFrame correctedCexC4 :=
  attemptGood_step correctedCexRing correctedCexFrame correctedCexC3 correctedCexQ2 correctedCexGood3 correctedCexC4_alive


private theorem correctedCexGood5 : AttemptGood correctedCexRing correctedCexFrame correctedCexC5 :=
  attemptGood_step correctedCexRing correctedCexFrame correctedCexC4 correctedCexQ3 correctedCexGood4 correctedCexC5_alive


private def correctedCexS0 : LongAttemptState correctedCexRing correctedCexFrame :=
  .live correctedCexStart correctedCexStart_good (.liveWait .ready .ready)


private def correctedCexS1 : LongAttemptState correctedCexRing correctedCexFrame :=
  .live correctedCexC1 correctedCexGood1 (.liveWait (.live 1) .ready)


private def correctedCexS2 : LongAttemptState correctedCexRing correctedCexFrame :=
  .live correctedCexC2 correctedCexGood2 (.race (.live 1) (.live 1))


private def correctedCexS3 : LongAttemptState correctedCexRing correctedCexFrame :=
  .live correctedCexC3 correctedCexGood3 (.race (.live 1) (.live 2))


private def correctedCexS4 : LongAttemptState correctedCexRing correctedCexFrame :=
  .live correctedCexC4 correctedCexGood4 (.race (.live 1) (.live 3))


private def correctedCexS5 : LongAttemptState correctedCexRing correctedCexFrame :=
  .live correctedCexC5 correctedCexGood5 (.race (.live 1) (.live 4))


private theorem correctedCex_start_eq_s0 :
    (longAttemptKernel correctedCexRing correctedCexFrame).start correctedCexStart = correctedCexS0 := by
  rw [longStart_eq_publicRowsStart]
  unfold publicRowsStart
  rw [dif_pos correctedCexStart_good]
  unfold publicRowsInitialStage
  rw [dif_pos correctedCexStart_cleanB]
  unfold publicRowsAfterTargetStage
  rw [dif_pos correctedCexStart_cleanA]
  rfl


private theorem correctedCex_step0 :
    (longAttemptKernel correctedCexRing correctedCexFrame).step correctedCexS0 correctedCexQ5 =
      .active correctedCexS1 := by
  have htag :
      ¬ TaggedDeleted correctedCexFrame
        (stepE correctedCexRing correctedCexStart correctedCexQ5) := by
    change ¬ TaggedDeleted correctedCexFrame correctedCexC1
    exact correctedCexC1_alive
  simp only [longAttemptKernel]
  unfold correctedCexS0 correctedCexS1
  unfold longStep
  dsimp only
  rw [dif_neg htag]
  try dsimp only
  have hfire :
      ¬ (SectorPhase.ready = SectorPhase.ready ∧
        correctedCexQ5 = correctedCexFrame.A.left) := by
    decide
  rw [dif_neg hfire]
  have hB :
      nextSectorPhase correctedCexFrame.B SectorPhase.ready correctedCexQ5 =
        SectorPhase.live 1 := by
    decide
  have hA :
      nextSectorPhase correctedCexFrame.A SectorPhase.ready correctedCexQ5 =
        SectorPhase.ready := by
    decide
  rw [hB, hA]
  rfl


private theorem correctedCex_step1 :
    (longAttemptKernel correctedCexRing correctedCexFrame).step correctedCexS1 correctedCexQ0 =
      .active correctedCexS2 := by
  have htag :
      ¬ TaggedDeleted correctedCexFrame
        (stepE correctedCexRing correctedCexC1 correctedCexQ0) := by
    change ¬ TaggedDeleted correctedCexFrame correctedCexC2
    exact correctedCexC2_alive
  simp only [longAttemptKernel]
  unfold correctedCexS1 correctedCexS2
  unfold longStep
  dsimp only
  rw [dif_neg htag]
  try dsimp only
  have hfire :
      SectorPhase.ready = SectorPhase.ready ∧
        correctedCexQ0 = correctedCexFrame.A.left := by
    exact And.intro rfl rfl
  rw [dif_pos hfire]
  have hnear :
      correctedCexFrame.a - 2 * correctedCexFrame.b <= 1 := by
    decide
  first | rw [dif_pos hnear] | rw [if_pos hnear]
  have hB :
      nextSectorPhase correctedCexFrame.B (SectorPhase.live 1) correctedCexQ0 =
        SectorPhase.live 1 := by
    decide
  have hA :
      nextSectorPhase correctedCexFrame.A SectorPhase.ready correctedCexQ0 =
        SectorPhase.live 1 := by
    decide
  rw [hB, hA]
  rfl


private theorem correctedCex_step2 :
    (longAttemptKernel correctedCexRing correctedCexFrame).step correctedCexS2 correctedCexQ1 =
      .active correctedCexS3 := by
  have htag :
      ¬ TaggedDeleted correctedCexFrame
        (stepE correctedCexRing correctedCexC2 correctedCexQ1) := by
    change ¬ TaggedDeleted correctedCexFrame correctedCexC3
    exact correctedCexC3_alive
  simp only [longAttemptKernel]
  unfold correctedCexS2 correctedCexS3
  unfold longStep
  dsimp only
  rw [dif_neg htag]
  try dsimp only
  have hready :
      ¬ (SectorPhase.live 1 = SectorPhase.ready) := by
    decide
  rw [dif_neg hready]
  have hhit :
      ¬ (Exists fun p =>
        And (SectorPhase.live 1 = SectorPhase.live p)
          (And
            (correctedCexQ1 = advance correctedCexRing correctedCexFrame.A.left p)
            (p + 1 = correctedCexFrame.a))) := by
    intro h
    rcases h with ⟨p, hp, _he, hend⟩
    change p + 1 = 5 at hend
    injection hp with hp'
    omega
  first | rw [dif_neg hhit] | rw [if_neg hhit]
  have hB :
      nextSectorPhase correctedCexFrame.B (SectorPhase.live 1) correctedCexQ1 =
        SectorPhase.live 1 := by
    decide
  have htarget :
      ¬ (nextSectorPhase correctedCexFrame.B (SectorPhase.live 1) correctedCexQ1 =
        SectorPhase.ready) := by
    rw [hB]
    decide
  first | rw [dif_neg htarget] | rw [if_neg htarget]
  have hA :
      nextSectorPhase correctedCexFrame.A (SectorPhase.live 1) correctedCexQ1 =
        SectorPhase.live 2 := by
    decide
  rw [hB, hA]
  rfl


private theorem correctedCex_step3 :
    (longAttemptKernel correctedCexRing correctedCexFrame).step correctedCexS3 correctedCexQ2 =
      .active correctedCexS4 := by
  have htag :
      ¬ TaggedDeleted correctedCexFrame
        (stepE correctedCexRing correctedCexC3 correctedCexQ2) := by
    change ¬ TaggedDeleted correctedCexFrame correctedCexC4
    exact correctedCexC4_alive
  simp only [longAttemptKernel]
  unfold correctedCexS3 correctedCexS4
  unfold longStep
  dsimp only
  rw [dif_neg htag]
  try dsimp only
  have hready :
      ¬ (SectorPhase.live 1 = SectorPhase.ready) := by
    decide
  rw [dif_neg hready]
  have hhit :
      ¬ (Exists fun p =>
        And (SectorPhase.live 2 = SectorPhase.live p)
          (And
            (correctedCexQ2 = advance correctedCexRing correctedCexFrame.A.left p)
            (p + 1 = correctedCexFrame.a))) := by
    intro h
    rcases h with ⟨p, hp, _he, hend⟩
    change p + 1 = 5 at hend
    injection hp with hp'
    omega
  first | rw [dif_neg hhit] | rw [if_neg hhit]
  have hB :
      nextSectorPhase correctedCexFrame.B (SectorPhase.live 1) correctedCexQ2 =
        SectorPhase.live 1 := by
    decide
  have htarget :
      ¬ (nextSectorPhase correctedCexFrame.B (SectorPhase.live 1) correctedCexQ2 =
        SectorPhase.ready) := by
    rw [hB]
    decide
  first | rw [dif_neg htarget] | rw [if_neg htarget]
  have hA :
      nextSectorPhase correctedCexFrame.A (SectorPhase.live 2) correctedCexQ2 =
        SectorPhase.live 3 := by
    decide
  rw [hB, hA]
  rfl


private theorem correctedCex_step4 :
    (longAttemptKernel correctedCexRing correctedCexFrame).step correctedCexS4 correctedCexQ3 =
      .active correctedCexS5 := by
  have htag :
      ¬ TaggedDeleted correctedCexFrame
        (stepE correctedCexRing correctedCexC4 correctedCexQ3) := by
    change ¬ TaggedDeleted correctedCexFrame correctedCexC5
    exact correctedCexC5_alive
  simp only [longAttemptKernel]
  unfold correctedCexS4 correctedCexS5
  unfold longStep
  dsimp only
  rw [dif_neg htag]
  try dsimp only
  have hready :
      ¬ (SectorPhase.live 1 = SectorPhase.ready) := by
    decide
  rw [dif_neg hready]
  have hhit :
      ¬ (Exists fun p =>
        And (SectorPhase.live 3 = SectorPhase.live p)
          (And
            (correctedCexQ3 = advance correctedCexRing correctedCexFrame.A.left p)
            (p + 1 = correctedCexFrame.a))) := by
    intro h
    rcases h with ⟨p, hp, _he, hend⟩
    change p + 1 = 5 at hend
    injection hp with hp'
    omega
  first | rw [dif_neg hhit] | rw [if_neg hhit]
  have hB :
      nextSectorPhase correctedCexFrame.B (SectorPhase.live 1) correctedCexQ3 =
        SectorPhase.live 1 := by
    decide
  have htarget :
      ¬ (nextSectorPhase correctedCexFrame.B (SectorPhase.live 1) correctedCexQ3 =
        SectorPhase.ready) := by
    rw [hB]
    decide
  first | rw [dif_neg htarget] | rw [if_neg htarget]
  have hA :
      nextSectorPhase correctedCexFrame.A (SectorPhase.live 3) correctedCexQ3 =
        SectorPhase.live 4 := by
    decide
  rw [hB, hA]
  rfl


theorem correctedCex_midRace_reachable_good :
    LongAttemptReachableGood correctedCexRing correctedCexFrame correctedCexStart correctedCexS5 := by
  have hroot :
      RetryActiveReachable
        (longAttemptKernel correctedCexRing correctedCexFrame)
        ((longAttemptKernel correctedCexRing correctedCexFrame).start correctedCexStart)
        ((longAttemptKernel correctedCexRing correctedCexFrame).start correctedCexStart) :=
    RetryActiveReachable.root
  have h01 :
      (longAttemptKernel correctedCexRing correctedCexFrame).step
          ((longAttemptKernel correctedCexRing correctedCexFrame).start correctedCexStart) correctedCexQ5 =
        .active correctedCexS1 := by
    rw [correctedCex_start_eq_s0]
    exact correctedCex_step0
  have h1 :=
    RetryActiveReachable.step hroot correctedCexQ5 h01
  have h2 :=
    RetryActiveReachable.step h1 correctedCexQ0 correctedCex_step1
  have h3 :=
    RetryActiveReachable.step h2 correctedCexQ1 correctedCex_step2
  have h4 :=
    RetryActiveReachable.step h3 correctedCexQ2 correctedCex_step3
  have h5 :=
    RetryActiveReachable.step h4 correctedCexQ3 correctedCex_step4
  exact And.intro correctedCexStart_good h5


theorem correctedCex_midRace_progressCut :
    longProgressHandoffCut correctedCexRing correctedCexFrame correctedCexS5 = true := by
  rfl


/-! Pure mirror of the two-state race recurrence. -/
private def correctedCexRacePairMass : Nat -> Nat × Nat
  | 0 => (1, 1)
  | T + 1 =>
      let m := correctedCexRacePairMass T
      (5 * m.1 + m.2,
        5 * m.2 + 7 ^ T)


theorem correctedCexRacePairMass_five :
    (correctedCexRacePairMass 5).1 = 8108 := by
  decide


/--
Smallest bounded residual left by this connector-only round.


It is one closed fixed-word count/refinement: the real longCutCount at the
kernel-checked reachable state correctedCexS5 equals the finite two-state mirror above.
The mirror itself is closed by decide.  Expanding this residual requires only
the seven closed children of correctedCexS5 and of its edge-6 successor; no reachability,
first-cut, or scheduler-splice reasoning remains.
-/
def LongAttemptCorrectedCexMidRaceMassRefinement : Prop :=
  longRaceMassFrom correctedCexRing correctedCexFrame correctedCexS5 5 =
    (correctedCexRacePairMass 5).1


theorem correctedCex_midRace_mass_8108
    (hrefine : LongAttemptCorrectedCexMidRaceMassRefinement) :
    longRaceMassFrom correctedCexRing correctedCexFrame correctedCexS5 5 = 8108 := by
  rw [hrefine]
  exact correctedCexRacePairMass_five


/--
Conditional only on the single closed fixed-word residual above, the corrected
spec is formally refuted.  Once LongAttemptCorrectedCexMidRaceMassRefinement is discharged this
has exactly the requested no-argument type.
-/
theorem longAttemptConcreteStageFactorSpecCorrected_false
    (hrefine : LongAttemptCorrectedCexMidRaceMassRefinement) :
    ¬ LongAttemptConcreteStageFactorSpecCorrected := by
  intro hstage
  have hb : 2 <= correctedCexFrame.b := by
    change 2 <= 2
    decide
  have hab : 2 * correctedCexFrame.b + 1 <= correctedCexFrame.a := by
    change 5 <= 5
    decide
  have hrows :=
    hstage sealedStepSpec correctedCexRing correctedCexFrame hb hab
  have hhalf :=
    hrows.2.1
      correctedCexStart correctedCexS5
      correctedCex_midRace_reachable_good
      correctedCex_midRace_progressCut
      5
  have hmass := correctedCex_midRace_mass_8108 hrefine
  rw [hmass] at hhalf
  have hnot : ¬ ((7 : Nat) ^ 5 <= 2 * 8108) := by
    decide
  exact hnot hhalf


/-! ## 7. First-cut conjunct 1 packaged with the first-cut interface -/


theorem longAttemptFirstCutStageFactorSpec_entry
    (hSealed : SealedStepSpec)
    (hAfter : LongTargetCRDoneRecoveryFree)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a) :
    forall s,
      AttemptGood ring F s ->
      forall T,
        longProgressEntryMass ring F s T = n ^ T :=
  longProgressEntryMass_eq_pow hSealed hAfter ring F hb hab


end PPL.Convergence.LDLocal


#print axioms PPL.Convergence.LDLocal.retryActiveBeforeCut_cut_false
#print axioms PPL.Convergence.LDLocal.retryActiveBeforeCut_to_reachable
#print axioms PPL.Convergence.LDLocal.retryFirstCut_to_reachable
#print axioms PPL.Convergence.LDLocal.retryFirstCut_of_before_step
#print axioms PPL.Convergence.LDLocal.longCutCount_splice_firstCut
#print axioms PPL.Convergence.LDLocal.longAttempt_firstProgressHandoff_is_firstCut
#print axioms PPL.Convergence.LDLocal.longAttemptFirstCutStageInequalities
#print axioms PPL.Convergence.LDLocal.longAttemptRetryStageFactors_of_firstCutCounts
#print axioms PPL.Convergence.LDLocal.longAttemptRetryMassSpec_of_firstCutCounts
#print axioms PPL.Convergence.LDLocal.longStart_eq_publicRowsStart
#print axioms PPL.Convergence.LDLocal.LongTargetCRDoneRecoveryFree
#print axioms PPL.Convergence.LDLocal.longProgressEntryOneStep
#print axioms PPL.Convergence.LDLocal.longProgressStart_before
#print axioms PPL.Convergence.LDLocal.longProgressEntryMassFrom_eq_pow
#print axioms PPL.Convergence.LDLocal.longProgressEntryMass_eq_pow
#print axioms PPL.Convergence.LDLocal.correctedCex_midRace_reachable_good
#print axioms PPL.Convergence.LDLocal.correctedCex_midRace_progressCut
#print axioms PPL.Convergence.LDLocal.correctedCexRacePairMass_five
#print axioms PPL.Convergence.LDLocal.correctedCex_midRace_mass_8108
#print axioms PPL.Convergence.LDLocal.longAttemptConcreteStageFactorSpecCorrected_false
#print axioms PPL.Convergence.LDLocal.longAttemptFirstCutStageFactorSpec_entry


