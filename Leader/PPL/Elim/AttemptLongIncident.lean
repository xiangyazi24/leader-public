import Leader.PPL.Elim.AttemptLongRace

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-!
# First-cut incident and full factors

Truth audit.

Conjunct 3 is true without a new residual.  In fact the literal kernel proof
below needs only longRaceWonCut = true, not the first-cut witness.  The live
cut states are race ready _, incident _, and retained _ _.  In the first two,
L_j is the good orientation edge, R_j is the bad orientation edge, and every
other nondeleted child stays in the incident recursion.  Retained is already
at the good cut.

Conjunct 4 is true at the intended first incident cut, but current main still
does not export the physical retained/recovery quarter producer.  The one new
residual below is a bounded one-step Bellman certificate on the active subtree
rooted at the exact first incident cut.  It does not assume the desired
quarter inequality.

The source facts behind that producer are retainedTrial_cost_nr together with
controlRowSpec_proved, target_cycle_pathwise, compensator_cleared,
retained_collapse_moment, W2_scaled, weighted_changeOfMeasure_nonretry, and
weighted_changeOfMeasure_success.  The first-cut carrier excludes the old
synthetic raw-state defects.

Also, longFullMassFrom really is nonretry mass: longCutCount with both cuts
constantly false gives n^T on success, zero on retry, and recursively counts
active children; longCutCount_full_eq_retryNonRetryNodeCount states this
identification explicitly.
-/

private def incident_Lj_ne_Rj
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    Not (L_j F = R_j F) := by
  unfold L_j R_j
  exact
    leftNeighbor_ne_self_control ring
      (frame_two_le_control F) F.j

private def incident_ready_other
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (e : Fin n)
    (hL : Not (e = L_j F))
    (hR : Not (e = R_j F)) :
    nextSectorPhase F.B .ready e = .ready := by
  have hin : Not (e = sealedIncomingEdge F.B) := by
    intro he
    apply hL
    exact he.trans (sealedIncomingEdge_B_eq_L_j F)
  have hout : Not (e = F.B.left) := by
    intro he
    apply hR
    simpa [R_j] using he.trans F.B_left
  simp [nextSectorPhase, hin, hout]

private def incident_longCutCount_good
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (good bad : A -> Bool)
    (a : A)
    (hg : good a = true) :
    forall T,
      longCutCount K good bad (.active a) T = n ^ T := by
  intro T
  cases T <;>
    simp [longCutCount, hg]

private def incident_incident_left_full
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n)
    (hgood : AttemptGood ring F C)
    (attackPhase : SectorPhase)
    (T : Nat) :
    longCutCount
        (longAttemptKernel ring F)
        (longIncidentWonCut ring F)
        (longRecoveryCut ring F)
        ((longAttemptKernel ring F).step
          (.live C hgood (.incident attackPhase))
          (L_j F))
        T =
      n ^ T := by
  classical
  let D := stepE ring C (L_j F)
  by_cases htag : TaggedDeleted F D
  · have hs :
        (longAttemptKernel ring F).step
            (.live C hgood (.incident attackPhase))
            (L_j F) =
          .success := by
      simp [longAttemptKernel, longStep, D, htag]
    rw [hs]
    simp only [longCutCount]
  · let hgoodD : AttemptGood ring F D :=
      attemptGood_step ring F C (L_j F) hgood htag
    have hLR : Not (L_j F = R_j F) :=
      incident_Lj_ne_Rj ring F
    have hs :
        (longAttemptKernel ring F).step
            (.live C hgood (.incident attackPhase))
            (L_j F) =
          .active
            (.live D hgoodD
              (.retained
                (nextSectorPhase F.B .ready (L_j F))
                (nextSectorPhase F.A attackPhase (L_j F)))) := by
      simp [longAttemptKernel, longStep, D, hgoodD, htag, hLR]
    rw [hs]
    exact
      incident_longCutCount_good
        (longAttemptKernel ring F)
        (longIncidentWonCut ring F)
        (longRecoveryCut ring F)
        (.live D hgoodD
          (.retained
            (nextSectorPhase F.B .ready (L_j F))
            (nextSectorPhase F.A attackPhase (L_j F))))
        rfl T

private def incident_incident_half
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n)
    (hgood : AttemptGood ring F C)
    (attackPhase : SectorPhase) :
    forall T,
      n ^ T <=
        2 *
          longIncidentMassFrom ring F
            (.live C hgood (.incident attackPhase)) T := by
  classical
  intro T
  induction T generalizing C attackPhase with
  | zero =>
      simp [longIncidentMassFrom, longCutCount,
        longIncidentWonCut, longRecoveryCut]
  | succ T ih =>
      let state : LongAttemptState ring F :=
        .live C hgood (.incident attackPhase)
      let child : Fin n -> Nat :=
        fun e =>
          longCutCount
            (longAttemptKernel ring F)
            (longIncidentWonCut ring F)
            (longRecoveryCut ring F)
            ((longAttemptKernel ring F).step state e)
            T
      let lower : Fin n -> Nat :=
        fun e =>
          if e = L_j F then
            2 * n ^ T
          else if e = R_j F then
            0
          else
            n ^ T

      have hLR : Not (L_j F = R_j F) :=
        incident_Lj_ne_Rj ring F

      have hpoint :
          forall e : Fin n,
            lower e <= 2 * child e := by
        intro e
        by_cases hL : e = L_j F
        · subst e
          simp only [lower, if_pos rfl]
          dsimp only [child]
          rw [incident_incident_left_full
            ring F C hgood attackPhase T]
          exact Nat.le_refl _
        · by_cases hR : e = R_j F
          · simp [lower, hL, hR, Ne.symm hLR]
          · simp only [lower, if_neg hL, if_neg hR]
            let D := stepE ring C e
            by_cases htag : TaggedDeleted F D
            · have hs :
                  (longAttemptKernel ring F).step state e =
                    .success := by
                simp [state, longAttemptKernel, longStep,
                  D, htag]
              dsimp only [child]
              rw [hs]
              simp only [longCutCount]
              rw [Nat.two_mul]
              exact Nat.le_add_left _ _
            · let hgoodD : AttemptGood ring F D :=
                attemptGood_step ring F C e hgood htag
              have hready :
                  nextSectorPhase F.B .ready e = .ready :=
                incident_ready_other ring F e hL hR
              have hs :
                  (longAttemptKernel ring F).step state e =
                    .active
                      (.live D hgoodD
                        (.incident
                          (nextSectorPhase
                            F.A attackPhase e))) := by
                simp [state, longAttemptKernel, longStep,
                  D, hgoodD, htag, hL, hR, hready]
              dsimp only [child]
              rw [hs]
              have hi :=
                ih
                  (C := D)
                  (hgood := hgoodD)
                  (attackPhase :=
                    nextSectorPhase F.A attackPhase e)
              simpa [longIncidentMassFrom] using hi

      have hsumLower :
          (List.ofFn lower).sum = n * n ^ T := by
        have hs :=
          PredictableTwoTargetFiniteTree.ofFn_sum_two_values_else_const
            (L_j F) (R_j F) lower (n ^ T) hLR
            (by
              intro e hL hR
              simp [lower, hL, hR])
        calc
          (List.ofFn lower).sum =
              lower (L_j F) +
                lower (R_j F) +
                  (n - 2) * n ^ T := hs
          _ =
              2 * n ^ T + (n - 2) * n ^ T := by
            simp [lower, hLR, Ne.symm hLR]
          _ =
              (2 + (n - 2)) * n ^ T := by
            rw [Nat.add_mul]
          _ = n * n ^ T := by
            have hn2 := frame_two_le_control F
            rw [show 2 + (n - 2) = n by omega]

      have hsum :=
        ofFn_sum_le
          lower
          (fun e => 2 * child e)
          hpoint

      change
        n ^ (T + 1) <=
          2 * (List.ofFn child).sum

      calc
        n ^ (T + 1) = n * n ^ T := by
          rw [Nat.pow_succ]
          ac_rfl
        _ = (List.ofFn lower).sum :=
          hsumLower.symm
        _ <=
            (List.ofFn
              (fun e => 2 * child e)).sum :=
          hsum
        _ = 2 * (List.ofFn child).sum :=
          ofFn_sum_mul_left 2 child

private def incident_race_ready_left_full
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n)
    (hgood : AttemptGood ring F C)
    (attackPhase : SectorPhase)
    (T : Nat) :
    longCutCount
        (longAttemptKernel ring F)
        (longIncidentWonCut ring F)
        (longRecoveryCut ring F)
        ((longAttemptKernel ring F).step
          (.live C hgood (.race .ready attackPhase))
          (L_j F))
        T =
      n ^ T := by
  classical
  let D := stepE ring C (L_j F)
  by_cases htag : TaggedDeleted F D
  · have hs :
        (longAttemptKernel ring F).step
            (.live C hgood (.race .ready attackPhase))
            (L_j F) =
          .success := by
      simp [longAttemptKernel, longStep, D, htag]
    rw [hs]
    simp only [longCutCount]
  · let hgoodD : AttemptGood ring F D :=
      attemptGood_step ring F C (L_j F) hgood htag
    have hLR : Not (L_j F = R_j F) :=
      incident_Lj_ne_Rj ring F
    have hs :
        (longAttemptKernel ring F).step
            (.live C hgood (.race .ready attackPhase))
            (L_j F) =
          .active
            (.live D hgoodD
              (.retained
                (nextSectorPhase F.B .ready (L_j F))
                (nextSectorPhase F.A attackPhase (L_j F)))) := by
      simp [longAttemptKernel, longStep, D, hgoodD, htag, hLR]
    rw [hs]
    exact
      incident_longCutCount_good
        (longAttemptKernel ring F)
        (longIncidentWonCut ring F)
        (longRecoveryCut ring F)
        (.live D hgoodD
          (.retained
            (nextSectorPhase F.B .ready (L_j F))
            (nextSectorPhase F.A attackPhase (L_j F))))
        rfl T

private def incident_race_ready_half
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n)
    (hgood : AttemptGood ring F C)
    (attackPhase : SectorPhase) :
    forall T,
      n ^ T <=
        2 *
          longIncidentMassFrom ring F
            (.live C hgood (.race .ready attackPhase)) T := by
  classical
  intro T
  cases T with
  | zero =>
      simp [longIncidentMassFrom, longCutCount,
        longIncidentWonCut, longRecoveryCut]
  | succ T =>
      let state : LongAttemptState ring F :=
        .live C hgood (.race .ready attackPhase)
      let child : Fin n -> Nat :=
        fun e =>
          longCutCount
            (longAttemptKernel ring F)
            (longIncidentWonCut ring F)
            (longRecoveryCut ring F)
            ((longAttemptKernel ring F).step state e)
            T
      let lower : Fin n -> Nat :=
        fun e =>
          if e = L_j F then
            2 * n ^ T
          else if e = R_j F then
            0
          else
            n ^ T

      have hLR : Not (L_j F = R_j F) :=
        incident_Lj_ne_Rj ring F

      have hpoint :
          forall e : Fin n,
            lower e <= 2 * child e := by
        intro e
        by_cases hL : e = L_j F
        · subst e
          simp only [lower, if_pos rfl]
          dsimp only [child]
          rw [incident_race_ready_left_full
            ring F C hgood attackPhase T]
          exact Nat.le_refl _
        · by_cases hR : e = R_j F
          · simp [lower, hL, hR, Ne.symm hLR]
          · simp only [lower, if_neg hL, if_neg hR]
            let D := stepE ring C e
            by_cases htag : TaggedDeleted F D
            · have hs :
                  (longAttemptKernel ring F).step state e =
                    .success := by
                simp [state, longAttemptKernel, longStep,
                  D, htag]
              dsimp only [child]
              rw [hs]
              simp only [longCutCount]
              rw [Nat.two_mul]
              exact Nat.le_add_left _ _
            · let hgoodD : AttemptGood ring F D :=
                attemptGood_step ring F C e hgood htag
              have hs :
                  (longAttemptKernel ring F).step state e =
                    .active
                      (.live D hgoodD
                        (.incident
                          (nextSectorPhase
                            F.A attackPhase e))) := by
                simp [state, longAttemptKernel, longStep,
                  D, hgoodD, htag, hL, hR]
              dsimp only [child]
              rw [hs]
              exact
                incident_incident_half
                  ring F D hgoodD
                  (nextSectorPhase F.A attackPhase e)
                  T

      have hsumLower :
          (List.ofFn lower).sum = n * n ^ T := by
        have hs :=
          PredictableTwoTargetFiniteTree.ofFn_sum_two_values_else_const
            (L_j F) (R_j F) lower (n ^ T) hLR
            (by
              intro e hL hR
              simp [lower, hL, hR])
        calc
          (List.ofFn lower).sum =
              lower (L_j F) +
                lower (R_j F) +
                  (n - 2) * n ^ T := hs
          _ =
              2 * n ^ T + (n - 2) * n ^ T := by
            simp [lower, hLR, Ne.symm hLR]
          _ =
              (2 + (n - 2)) * n ^ T := by
            rw [Nat.add_mul]
          _ = n * n ^ T := by
            have hn2 := frame_two_le_control F
            rw [show 2 + (n - 2) = n by omega]

      have hsum :=
        ofFn_sum_le
          lower
          (fun e => 2 * child e)
          hpoint

      change
        n ^ (T + 1) <=
          2 * (List.ofFn child).sum

      calc
        n ^ (T + 1) = n * n ^ T := by
          rw [Nat.pow_succ]
          ac_rfl
        _ = (List.ofFn lower).sum :=
          hsumLower.symm
        _ <=
            (List.ofFn
              (fun e => 2 * child e)).sum :=
          hsum
        _ = 2 * (List.ofFn child).sum :=
          ofFn_sum_mul_left 2 child

/--
Conjunct 3 of LongAttemptFirstCutStageFactorSpec.

The first-cut witness is intentionally stronger than needed here.  The
literal race/incident L_j versus R_j recursion proves the factor two for every
state satisfying longRaceWonCut = true.
-/
theorem longIncidentFactor_proved :
    forall (hSealed : SealedStepSpec),
      forall {n : Nat} (ring : DirectedRing n)
        {C0 : Config n} (F : TripleFrame ring C0),
        2 <= F.b ->
        2 * F.b + 1 <= F.a ->
        forall s a,
          LongAttemptFirstRaceGood ring F s a ->
          longRaceWonCut ring F a = true ->
          forall T,
            n ^ T <=
              2 * longIncidentMassFrom ring F a T := by
  intro _hSealed n ring C0 F _hb _hab
  intro s a hfirst hcut T
  cases a with
  | junk C =>
      simp [longRaceWonCut] at hcut
  | live C hgood stage =>
      cases stage with
      | targetCR mode =>
          simp [longRaceWonCut] at hcut
      | attackerCR targetPhase mode =>
          simp [longRaceWonCut] at hcut
      | liveWait targetPhase attackPhase =>
          simp [longRaceWonCut] at hcut
      | advance targetPhase attackPhase =>
          simp [longRaceWonCut] at hcut
      | race targetPhase attackPhase =>
          cases targetPhase with
          | ready =>
              exact
                incident_race_ready_half
                  ring F C hgood attackPhase T
          | dummy p =>
              simp [longRaceWonCut] at hcut
          | live p =>
              simp [longRaceWonCut] at hcut
          | ret q =>
              simp [longRaceWonCut] at hcut
      | incident attackPhase =>
          exact
            incident_incident_half
              ring F C hgood attackPhase T
      | retained targetPhase attackPhase =>
          cases T <;>
            simp [longIncidentMassFrom, longCutCount,
              longIncidentWonCut, longRecoveryCut] <;>
            omega
      | recovery targetPhase attackPhase =>
          simp [longRaceWonCut] at hcut
      | stuck =>
          simp [longRaceWonCut] at hcut

private def incidentQuarterNodeValue
    {A S : Type}
    (phi : A -> Nat) :
    AttemptNode A S -> Nat
  | .success => 4
  | .retry _ => 0
  | .active a => phi a

/--
The single new leaf for conjunct 4.

For the exact first incident-won cut root, expose a bounded potential phi
with root credit at least one, value at most four on every active descendant,
and one-step Bellman row

  n * phi(b) <= sum_e nodeValue(phi, K.step b e).

This is strictly weaker than the requested quarter inequality: it is only a
local one-letter certificate.  The finite-tree telescope below derives the
factor four.

The intended producer is the retained/recovery analysis already present in
the repository: retainedTrial_cost_nr via controlRowSpec_proved,
target_cycle_pathwise, compensator_cleared, retained_collapse_moment,
W2_scaled, weighted_changeOfMeasure_nonretry, and
weighted_changeOfMeasure_success.  The LongAttemptFirstIncidentGood
hypothesis supplies the actual first-cut carrier needed to exclude synthetic
raw retained states.
-/
def LongFirstIncidentQuarterBellman : Prop :=
  forall (hSealed : SealedStepSpec),
    forall {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 <= F.b ->
      2 * F.b + 1 <= F.a ->
      forall s a,
        LongAttemptFirstIncidentGood ring F s a ->
        longIncidentWonCut ring F a = true ->
        Exists fun phi : LongAttemptState ring F -> Nat =>
          And
            (1 <= phi a)
            (And
              (forall b,
                RetryActiveReachable
                    (longAttemptKernel ring F) a b ->
                  phi b <= 4)
              (forall b,
                RetryActiveReachable
                    (longAttemptKernel ring F) a b ->
                  n * phi b <=
                    (List.ofFn
                      (fun e : Fin n =>
                        incidentQuarterNodeValue phi
                          ((longAttemptKernel ring F).step
                            b e))).sum))

private def incident_quarterBellmanMass
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (root : A)
    (phi : A -> Nat)
    (hcap :
      forall b,
        RetryActiveReachable K root b ->
          phi b <= 4)
    (hrow :
      forall b,
        RetryActiveReachable K root b ->
          n * phi b <=
            (List.ofFn
              (fun e : Fin n =>
                incidentQuarterNodeValue phi
                  (K.step b e))).sum) :
    forall b,
      RetryActiveReachable K root b ->
      forall T,
        phi b * n ^ T <=
          4 *
            longCutCount
              K
              (fun _ => false)
              (fun _ => false)
              (.active b) T := by
  intro b hreach T
  induction T generalizing b with
  | zero =>
      have hc := hcap b hreach
      simpa [longCutCount] using hc
  | succ T ih =>
      have hscale :
          phi b * n ^ (T + 1) <=
            (List.ofFn
              (fun e : Fin n =>
                n ^ T *
                  incidentQuarterNodeValue phi
                    (K.step b e))).sum := by
        calc
          phi b * n ^ (T + 1) =
              n ^ T * (n * phi b) := by
            rw [Nat.pow_succ]
            ac_rfl
          _ <=
              n ^ T *
                (List.ofFn
                  (fun e : Fin n =>
                    incidentQuarterNodeValue phi
                      (K.step b e))).sum :=
            Nat.mul_le_mul_left
              (n ^ T) (hrow b hreach)
          _ =
              (List.ofFn
                (fun e : Fin n =>
                  n ^ T *
                    incidentQuarterNodeValue phi
                      (K.step b e))).sum :=
            (ofFn_sum_mul_left
              (n ^ T)
              (fun e : Fin n =>
                incidentQuarterNodeValue phi
                  (K.step b e))).symm

      have hchild :
          forall e : Fin n,
            n ^ T *
                incidentQuarterNodeValue phi
                  (K.step b e) <=
              4 *
                longCutCount
                  K
                  (fun _ => false)
                  (fun _ => false)
                  (K.step b e) T := by
        intro e
        cases hs : K.step b e with
        | success =>
            simp [incidentQuarterNodeValue,
              longCutCount, hs]
            try (exact Nat.le_of_eq (Nat.mul_comm _ _))
        | retry s =>
            simp [incidentQuarterNodeValue,
              longCutCount, hs]
        | active b' =>
            have hreach' :
                RetryActiveReachable K root b' :=
              RetryActiveReachable.step
                hreach e hs
            have hi := ih b' hreach'
            simpa [incidentQuarterNodeValue,
              hs, Nat.mul_comm] using hi

      have hsum :=
        ofFn_sum_le
          (fun e : Fin n =>
            n ^ T *
              incidentQuarterNodeValue phi
                (K.step b e))
          (fun e : Fin n =>
            4 *
              longCutCount
                K
                (fun _ => false)
                (fun _ => false)
                (K.step b e) T)
          hchild

      calc
        phi b * n ^ (T + 1) <=
            (List.ofFn
              (fun e : Fin n =>
                n ^ T *
                  incidentQuarterNodeValue phi
                    (K.step b e))).sum :=
          hscale
        _ <=
            (List.ofFn
              (fun e : Fin n =>
                4 *
                  longCutCount
                    K
                    (fun _ => false)
                    (fun _ => false)
                    (K.step b e) T)).sum :=
          hsum
        _ =
            4 *
              (List.ofFn
                (fun e : Fin n =>
                  longCutCount
                    K
                    (fun _ => false)
                    (fun _ => false)
                    (K.step b e) T)).sum :=
          ofFn_sum_mul_left
            4
            (fun e : Fin n =>
              longCutCount
                K
                (fun _ => false)
                (fun _ => false)
                (K.step b e) T)
        _ =
            4 *
              longCutCount
                K
                (fun _ => false)
                (fun _ => false)
                (.active b) (T + 1) := by
          simp [longCutCount]

/--
Conjunct 4 of LongAttemptFirstCutStageFactorSpec from the one local
first-incident Bellman leaf.
-/
theorem longFullFactor_proved
    (hQuarter : LongFirstIncidentQuarterBellman) :
    forall (hSealed : SealedStepSpec),
      forall {n : Nat} (ring : DirectedRing n)
        {C0 : Config n} (F : TripleFrame ring C0),
        2 <= F.b ->
        2 * F.b + 1 <= F.a ->
        forall s a,
          LongAttemptFirstIncidentGood ring F s a ->
          longIncidentWonCut ring F a = true ->
          forall T,
            n ^ T <=
              4 * longFullMassFrom ring F a T := by
  intro hSealed n ring C0 F hb hab
  intro s a hfirst hcut T
  obtain ⟨phi, hroot, hcap, hrow⟩ :=
    hQuarter hSealed ring F hb hab
      s a hfirst hcut

  have htree :=
    incident_quarterBellmanMass
      (longAttemptKernel ring F)
      a phi hcap hrow
      a RetryActiveReachable.root T

  have hbase :
      n ^ T <= phi a * n ^ T := by
    have hm :=
      Nat.mul_le_mul_right
        (n ^ T) hroot
    simpa using hm

  exact
    Nat.le_trans hbase
      (by
        simpa [longFullMassFrom] using htree)

/--
Assembly of all four first-cut conjuncts.

Conjunct 1 is closed unconditionally by
longAttemptFirstCutStageFactorSpec_entry_closed.
Conjunct 2 uses only LongFirstProgressRaceCounterRefinement.
Conjunct 3 is unconditional.
Conjunct 4 uses only LongFirstIncidentQuarterBellman.
-/
theorem longAttemptFirstCutStageFactorSpec_of_leaves
    (hRace : LongFirstProgressRaceCounterRefinement)
    (hQuarter : LongFirstIncidentQuarterBellman) :
    LongAttemptFirstCutStageFactorSpec := by
  unfold LongAttemptFirstCutStageFactorSpec
  intro hSealed n ring C0 F hb hab
  refine
    And.intro
      (longAttemptFirstCutStageFactorSpec_entry_closed
        ring F hb hab)
      ?_
  refine
    And.intro
      (longRaceFactor_proved
        hRace hSealed ring F hb hab)
      ?_
  refine
    And.intro
      (longIncidentFactor_proved
        hSealed ring F hb hab)
      (longFullFactor_proved
        hQuarter hSealed ring F hb hab)

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.longIncidentFactor_proved
#print axioms PPL.Convergence.LDLocal.longFullFactor_proved
#print axioms PPL.Convergence.LDLocal.longAttemptFirstCutStageFactorSpec_of_leaves
