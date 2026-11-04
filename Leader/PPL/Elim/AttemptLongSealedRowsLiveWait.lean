import Leader.PPL.Elim.AttemptLongSealedRows
import Leader.PPL.Elim.AttemptLongTargetCleanReadyDone
import Leader.PPL.Elim.AttemptCostModerateSealed


namespace PPL.Convergence.LDLocal


set_option autoImplicit false
set_option Elab.async false


open FiniteUniformStoppingTree


/-!
The path-qualified Advance residual.


The first-cut witness is used only to recover the semantic phase witness for
the actual descendant.  Once an Advance node is legitimate, its Bellman row
is local: exactly one attacker-sector service letter decreases
longAdvancePhaseUnits by one (or hands off to Race with the same one-unit
drop), and every other surviving letter preserves the Advance potential.
-/


/-! ## Small phase lemmas -/


private def longLiveWaitNonLive : SectorPhase -> Prop
  | .live _ => False
  | _ => True


private theorem longLiveWaitNonLive_next
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (ph : SectorPhase)
    (h : longLiveWaitNonLive ph)
    (e : Fin n)
    (hfire : Not (ph = .ready ∧ e = A.left)) :
    longLiveWaitNonLive (nextSectorPhase A ph e) := by
  cases ph with
  | ready =>
      have hsrc : e ≠ A.left := by
        intro he
        exact hfire (And.intro rfl he)
      by_cases hin : e = sealedIncomingEdge A
      · simp [nextSectorPhase, hin, longLiveWaitNonLive]
      · simp [nextSectorPhase, hin, hsrc, longLiveWaitNonLive]
  | dummy p =>
      by_cases hs : e = advance ring A.left p
      · by_cases hlt : p + 1 < A.gap
        · simp [nextSectorPhase, hs, hlt, longLiveWaitNonLive]
        · by_cases hgap : A.gap = 1
          · simp [nextSectorPhase, hs, hlt, hgap,
              longLiveWaitNonLive]
          · simp [nextSectorPhase, hs, hlt, hgap,
              longLiveWaitNonLive]
      · simp [nextSectorPhase, hs, longLiveWaitNonLive]
  | live p =>
      exact False.elim h
  | ret q =>
      by_cases hs : e = advance ring A.left (q - 1)
      · by_cases hq : q = 1
        · simp [nextSectorPhase, hs, hq, longLiveWaitNonLive]
        · simp [nextSectorPhase, hs, hq, longLiveWaitNonLive]
      · simp [nextSectorPhase, hs, longLiveWaitNonLive]


private theorem longLiveWaitLiveNext_bounds
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (p : Nat)
    (hphase : PhaseHolds A C (.live p))
    (e : Fin n)
    (hterminal :
      Not (e = advance ring A.left p ∧ p + 1 = A.gap)) :
    Exists fun p' =>
      And
        (nextSectorPhase A (.live p) e = .live p')
        (And (p <= p') (p' <= p + 1)) := by
  have hp : p < A.gap := hphase.2.1.1
  by_cases hs : e = advance ring A.left p
  · by_cases hlt : p + 1 < A.gap
    · refine Exists.intro (p + 1) ?_
      exact
        And.intro
          (by simp [nextSectorPhase, hs, hlt])
          (And.intro (by omega) (by omega))
    · have heq : p + 1 = A.gap := by omega
      exact False.elim (hterminal (And.intro hs heq))
  · refine Exists.intro p ?_
    exact
      And.intro
        (by simp [nextSectorPhase, hs])
        (And.intro (Nat.le_refl p) (by omega))


private theorem longLiveWaitPhaseDebt_le
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (A : SectorFrame ring C0)
    (C : Config n) (ph : SectorPhase)
    (h : PhaseHolds A C ph) :
    phaseDebt A.gap ph <= 2 * A.gap - 1 := by
  cases ph with
  | ready =>
      simp [phaseDebt]
  | dummy p =>
      have hp : p < A.gap := h.2.1.1
      simp [phaseDebt]
      omega
  | live p =>
      have hp : p < A.gap := h.2.1.1
      simp [phaseDebt]
      omega
  | ret q =>
      have hq : q < A.gap := h.2.2.1
      simp [phaseDebt]
      omega


private theorem longLiveWaitPhaseReady
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n)
    (hInterior : CRInteriorFollowers A C)
    (hclean : CleanReady A C) :
    PhaseHolds A C .ready := by
  exact And.intro hInterior hclean


/-! ## Literal-start mirror, avoiding private upstream names -/


private noncomputable def longLiveWaitCRInitMode
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n)
    (hPB : PPL.Elim.PB ring D)
    (halive : Not (EndpointDeleted A D))
    (hclean : Not (CleanReady A D)) : CRMode :=
  Classical.choose
    (crRankInit ring A D hPB
      (by
        intro hdone
        rcases hdone with hdel | hready
        · exact halive hdel
        · exact hclean hready))


private noncomputable def longLiveWaitAfterTargetStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : LongStage := by
  classical
  if hA : CleanReady F.A D then
    exact .liveWait .ready .ready
  else
    exact .attackerCR .ready
      (longLiveWaitCRInitMode ring F.A D hgood.1
        (moderateSealed_notEndpointA F D hgood) hA)


private noncomputable def longLiveWaitInitialStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : LongStage := by
  classical
  if hB : CleanReady F.B D then
    exact longLiveWaitAfterTargetStage ring F D hgood
  else
    exact .targetCR
      (longLiveWaitCRInitMode ring F.B D hgood.1
        (moderateSealed_notEndpointB F D hgood) hB)


private noncomputable def longLiveWaitStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) : LongAttemptState ring F := by
  classical
  if hgood : AttemptGood ring F D then
    exact .live D hgood
      (longLiveWaitInitialStage ring F D hgood)
  else
    exact .junk D


private theorem longLiveWait_start_eq
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) :
    (longAttemptKernel ring F).start D =
      longLiveWaitStart ring F D := by
  rfl


/-! ## Minimal provenance invariant through the first post-CR cut -/


private def longLiveWaitPreInvariant
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Prop
  | .junk _ => False
  | .live C _ stage =>
      match stage with
      | .targetCR _ => True
      | .attackerCR targetPhase _ =>
          PhaseHolds F.B C targetPhase
      | .stuck => True
      | _ => False


private def longLiveWaitPostInvariant
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Prop
  | .junk _ => False
  | .live C _ stage =>
      match stage with
      | .liveWait targetPhase attackPhase =>
          longStageLegit F C
            (.liveWait targetPhase attackPhase)
      | .advance targetPhase attackPhase =>
          longStageLegit F C
            (.advance targetPhase attackPhase)
      | .race _ _ => True
      | .incident _ => True
      | .retained _ _ => True
      | .recovery _ _ => True
      | _ => False


private theorem longLiveWait_pre_start
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s)
    (hcut :
      longPostCRCutCorrected F
        ((longAttemptKernel ring F).start s) = false) :
    longLiveWaitPreInvariant F
      ((longAttemptKernel ring F).start s) := by
  classical
  rw [longLiveWait_start_eq] at hcut ⊢
  unfold longLiveWaitStart at hcut ⊢
  rw [dif_pos hs] at hcut ⊢
  unfold longLiveWaitInitialStage at hcut ⊢
  by_cases hB : CleanReady F.B s
  · rw [dif_pos hB] at hcut ⊢
    unfold longLiveWaitAfterTargetStage at hcut ⊢
    by_cases hA : CleanReady F.A s
    · rw [dif_pos hA] at hcut ⊢
      simp [longPostCRCutCorrected] at hcut
    · rw [dif_neg hA] at hcut ⊢
      exact
        longLiveWaitPhaseReady
          F.B s hs.2.2.2 hB
  · rw [dif_neg hB] at hcut ⊢
    exact True.intro


private theorem longLiveWait_pre_step
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (ha : longLiveWaitPreInvariant F a)
    (e : Fin n) (a' : LongAttemptState ring F)
    (hstep :
      (longAttemptKernel ring F).step a e = .active a')
    (hcut : longPostCRCutCorrected F a' = false) :
    longLiveWaitPreInvariant F a' := by
  classical
  cases a with
  | junk C =>
      exact False.elim ha
  | live C hgood stage =>
      simp only [longAttemptKernel] at hstep
      unfold longStep at hstep
      dsimp only at hstep
      by_cases htag : TaggedDeleted F (stepE ring C e)
      · rw [dif_pos htag] at hstep
        cases hstep
      · rw [dif_neg htag] at hstep
        cases stage with
        | targetCR mode =>
            dsimp only at hstep
            by_cases hmode : CRModeHolds F.B C mode
            · rw [dif_pos hmode] at hstep
              by_cases hdone :
                  CRDone F.B (stepE ring C e)
              · rw [dif_pos hdone] at hstep
                cases hstep
                have hcleanB :
                    CleanReady F.B (stepE ring C e) := by
                  rcases hdone with hdel | hclean
                  · exact False.elim
                      (htag
                        (endpointB_deleted_tagged
                          F (stepE ring C e) hdel))
                  · exact hclean
                have hgoodD :=
                  attemptGood_step ring F C e hgood htag
                have hBready :
                    PhaseHolds F.B
                      (stepE ring C e) .ready :=
                  longLiveWaitPhaseReady
                    F.B (stepE ring C e)
                    hgoodD.2.2.2 hcleanB
                revert hcut
                unfoldLongAfterTargetStage
                by_cases hA :
                    CleanReady F.A (stepE ring C e)
                · rw [dif_pos hA]
                  intro hcut
                  simp [longPostCRCutCorrected] at hcut
                · rw [dif_neg hA]
                  intro _hcut
                  exact hBready
              · rw [dif_neg hdone] at hstep
                cases hstep
                exact True.intro
            · rw [dif_neg hmode] at hstep
              cases hstep
              exact True.intro
        | attackerCR targetPhase mode =>
            dsimp only at hstep
            have haB : PhaseHolds F.B C targetPhase := by
              simpa [longLiveWaitPreInvariant] using ha
            by_cases hmode : CRModeHolds F.A C mode
            · rw [dif_pos hmode] at hstep
              have hBnext :=
                moderateSealed_phaseBNext
                  hSealed ring F C hgood
                  targetPhase haB e htag
              by_cases hdone :
                  CRDone F.A (stepE ring C e)
              · rw [dif_pos hdone] at hstep
                cases hstep
                simp [longPostCRCutCorrected] at hcut
              · rw [dif_neg hdone] at hstep
                cases hstep
                exact hBnext
            · rw [dif_neg hmode] at hstep
              cases hstep
              exact True.intro
        | liveWait targetPhase attackPhase =>
            exact False.elim ha
        | advance targetPhase attackPhase =>
            exact False.elim ha
        | race targetPhase attackPhase =>
            exact False.elim ha
        | incident attackPhase =>
            exact False.elim ha
        | retained targetPhase attackPhase =>
            exact False.elim ha
        | recovery targetPhase attackPhase =>
            exact False.elim ha
        | stuck =>
            dsimp only at hstep
            cases hstep
            exact True.intro


private theorem longLiveWait_pre_before
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s)
    (a : LongAttemptState ring F)
    (h :
      RetryActiveBeforeCutCorrected
        (longAttemptKernel ring F)
        (longPostCRCutCorrected F)
        ((longAttemptKernel ring F).start s)
        a) :
    longLiveWaitPreInvariant F a := by
  induction h with
  | root hroot =>
      exact longLiveWait_pre_start ring F s hs hroot
  | step h e hstep hcut ih =>
      exact
        longLiveWait_pre_step
          hSealed ring F _ ih e _ hstep hcut


private theorem longLiveWait_start_post
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s)
    (hcut :
      longPostCRCutCorrected F
        ((longAttemptKernel ring F).start s) = true) :
    longLiveWaitPostInvariant F
      ((longAttemptKernel ring F).start s) := by
  classical
  rw [longLiveWait_start_eq] at hcut ⊢
  unfold longLiveWaitStart at hcut ⊢
  rw [dif_pos hs] at hcut ⊢
  unfold longLiveWaitInitialStage at hcut ⊢
  by_cases hB : CleanReady F.B s
  · rw [dif_pos hB] at hcut ⊢
    unfold longLiveWaitAfterTargetStage at hcut ⊢
    by_cases hA : CleanReady F.A s
    · rw [dif_pos hA] at hcut ⊢
      have hBready :=
        longLiveWaitPhaseReady
          F.B s hs.2.2.2 hB
      have hAready :=
        longLiveWaitPhaseReady
          F.A s hs.2.2.1 hA
      have hlegit :
          longStageLegit F s (.liveWait .ready .ready) :=
        And.intro hBready
          (And.intro hAready True.intro)
      simpa [longLiveWaitPostInvariant] using hlegit
    · rw [dif_neg hA] at hcut ⊢
      simp [longPostCRCutCorrected] at hcut
  · rw [dif_neg hB] at hcut ⊢
    simp [longPostCRCutCorrected] at hcut


private theorem longLiveWait_first_post
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s)
    (carrier : LongAttemptState ring F)
    (hfirst :
      RetryFirstCutReachableCorrected
        (longAttemptKernel ring F)
        (longPostCRCutCorrected F)
        ((longAttemptKernel ring F).start s)
        carrier) :
    longLiveWaitPostInvariant F carrier := by
  classical
  rcases hfirst with hroot | hstep
  · rcases hroot with ⟨hEq, hcut⟩
    subst carrier
    exact longLiveWait_start_post ring F s hs hcut
  · rcases hstep with
      ⟨p, hbefore, e, hstep, hcut⟩
    have hp :=
      longLiveWait_pre_before
        hSealed ring F s hs p hbefore
    cases p with
    | junk C =>
        exact False.elim hp
    | live C hgood stage =>
        simp only [longAttemptKernel] at hstep
        unfold longStep at hstep
        dsimp only at hstep
        by_cases htag : TaggedDeleted F (stepE ring C e)
        · rw [dif_pos htag] at hstep
          cases hstep
        · rw [dif_neg htag] at hstep
          cases stage with
          | targetCR mode =>
              dsimp only at hstep
              by_cases hmode : CRModeHolds F.B C mode
              · rw [dif_pos hmode] at hstep
                by_cases hdone :
                    CRDone F.B (stepE ring C e)
                · rw [dif_pos hdone] at hstep
                  cases hstep
                  have hcleanB :
                      CleanReady F.B (stepE ring C e) := by
                    rcases hdone with hdel | hclean
                    · exact False.elim
                        (htag
                          (endpointB_deleted_tagged
                            F (stepE ring C e) hdel))
                    · exact hclean
                  have hgoodD :=
                    attemptGood_step ring F C e hgood htag
                  have hBready :=
                    longLiveWaitPhaseReady
                      F.B (stepE ring C e)
                      hgoodD.2.2.2 hcleanB
                  revert hcut
                  unfoldLongAfterTargetStage
                  by_cases hA :
                      CleanReady F.A (stepE ring C e)
                  · rw [dif_pos hA]
                    intro _hcut
                    have hAready :=
                      longLiveWaitPhaseReady
                        F.A (stepE ring C e)
                        hgoodD.2.2.1 hA
                    have hlegit :
                        longStageLegit F (stepE ring C e)
                          (.liveWait .ready .ready) :=
                      And.intro hBready
                        (And.intro hAready True.intro)
                    simpa [longLiveWaitPostInvariant] using hlegit
                  · rw [dif_neg hA]
                    intro hcut
                    simp [longPostCRCutCorrected] at hcut
                · rw [dif_neg hdone] at hstep
                  cases hstep
                  simp [longPostCRCutCorrected] at hcut
              · rw [dif_neg hmode] at hstep
                cases hstep
                simp [longPostCRCutCorrected] at hcut
          | attackerCR targetPhase mode =>
              dsimp only at hstep
              have hpB : PhaseHolds F.B C targetPhase := by
                simpa [longLiveWaitPreInvariant] using hp
              by_cases hmode : CRModeHolds F.A C mode
              · rw [dif_pos hmode] at hstep
                have hBnext :=
                  moderateSealed_phaseBNext
                    hSealed ring F C hgood
                    targetPhase hpB e htag
                by_cases hdone :
                    CRDone F.A (stepE ring C e)
                · rw [dif_pos hdone] at hstep
                  cases hstep
                  have hgoodD :=
                    attemptGood_step ring F C e hgood htag
                  have hcleanA :
                      CleanReady F.A (stepE ring C e) := by
                    rcases hdone with hdel | hclean
                    · exact False.elim
                        (htag
                          (endpointA_deleted_tagged
                            F (stepE ring C e) hdel))
                    · exact hclean
                  have hAready :=
                    longLiveWaitPhaseReady
                      F.A (stepE ring C e)
                      hgoodD.2.2.1 hcleanA
                  have hlegit :
                      longStageLegit F (stepE ring C e)
                        (.liveWait
                          (nextSectorPhase F.B targetPhase e)
                          .ready) :=
                    And.intro hBnext
                      (And.intro hAready True.intro)
                  simpa [longLiveWaitPostInvariant] using hlegit
                · rw [dif_neg hdone] at hstep
                  cases hstep
                  simp [longPostCRCutCorrected] at hcut
              · rw [dif_neg hmode] at hstep
                cases hstep
                simp [longPostCRCutCorrected] at hcut
          | liveWait targetPhase attackPhase =>
              exact False.elim hp
          | advance targetPhase attackPhase =>
              exact False.elim hp
          | race targetPhase attackPhase =>
              exact False.elim hp
          | incident attackPhase =>
              exact False.elim hp
          | retained targetPhase attackPhase =>
              exact False.elim hp
          | recovery targetPhase attackPhase =>
              exact False.elim hp
          | stuck =>
              dsimp only at hstep
              cases hstep
              simp [longPostCRCutCorrected] at hcut


private theorem longLiveWait_post_step
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (a : LongAttemptState ring F)
    (ha : longLiveWaitPostInvariant F a)
    (e : Fin n) (a' : LongAttemptState ring F)
    (hstep :
      (longAttemptKernel ring F).step a e = .active a') :
    longLiveWaitPostInvariant F a' := by
  classical
  cases a with
  | junk C =>
      exact False.elim ha
  | live C hgood stage =>
      simp only [longAttemptKernel] at hstep
      unfold longStep at hstep
      dsimp only at hstep
      by_cases htag : TaggedDeleted F (stepE ring C e)
      · rw [dif_pos htag] at hstep
        cases hstep
      · rw [dif_neg htag] at hstep
        have hgoodD :=
          attemptGood_step ring F C e hgood htag
        cases stage with
        | targetCR mode =>
            exact False.elim ha
        | attackerCR targetPhase mode =>
            exact False.elim ha
        | liveWait targetPhase attackPhase =>
            dsimp only at hstep
            dsimp only [longLiveWaitPostInvariant, longStageLegit] at ha
            rcases ha with ⟨hB, hA, hnon⟩
            have hBnext :=
              moderateSealed_phaseBNext
                hSealed ring F C hgood
                targetPhase hB e htag
            have hAnext :=
              moderateSealed_phaseANext
                hSealed ring F C hgood
                attackPhase hA e htag
            have hnon0 : longLiveWaitNonLive attackPhase := by
              revert hnon
              cases attackPhase <;> simp [longLiveWaitNonLive]
            by_cases hfire :
                attackPhase = .ready ∧ e = F.A.left
            · rw [dif_pos hfire] at hstep
              have hgap : F.A.gap ≠ 1 := by
                intro hg
                have ha1 : F.a = 1 := by
                  rw [← F.A_gap]
                  exact hg
                omega
              have hnextA :
                  nextSectorPhase F.A attackPhase e = .live 1 := by
                rw [hfire.1, hfire.2]
                simp [nextSectorPhase,
                  left_ne_sealedIncomingEdge F.A, hgap]
              by_cases hnear :
                  F.a - 2 * F.b <= 1
              · rw [dif_pos hnear] at hstep
                cases hstep
                exact True.intro
              · rw [dif_neg hnear] at hstep
                cases hstep
                have hlegit :
                    longStageLegit F (stepE ring C e)
                      (.advance
                        (nextSectorPhase F.B targetPhase e)
                        (nextSectorPhase F.A attackPhase e)) :=
                  And.intro hBnext
                    (And.intro hAnext
                      ⟨1, hnextA, by omega, by omega⟩)
                simpa [longLiveWaitPostInvariant] using hlegit
            · rw [dif_neg hfire] at hstep
              cases hstep
              have hnonNext :=
                longLiveWaitNonLive_next
                  F.A attackPhase hnon0 e hfire
              have hlegit :
                  longStageLegit F (stepE ring C e)
                    (.liveWait
                      (nextSectorPhase F.B targetPhase e)
                      (nextSectorPhase F.A attackPhase e)) :=
                And.intro hBnext
                  (And.intro hAnext
                    (by
                      generalize nextSectorPhase F.A attackPhase e = q at hnonNext ⊢
                      revert hnonNext
                      cases q <;> simp [longLiveWaitNonLive]))
              simpa [longLiveWaitPostInvariant] using hlegit
        | advance targetPhase attackPhase =>
            dsimp only at hstep
            have haLegit :
                longStageLegit F C
                  (.advance targetPhase attackPhase) := by
              simpa [longLiveWaitPostInvariant] using ha
            dsimp only [longStageLegit] at haLegit
            rcases haLegit with
              ⟨hB, hA, p, hattack, hp0, hpCut⟩
            subst attackPhase
            have hBnext :=
              moderateSealed_phaseBNext
                hSealed ring F C hgood
                targetPhase hB e htag
            have hAnext :=
              moderateSealed_phaseANext
                hSealed ring F C hgood
                (.live p) hA e htag
            have hnotTerminal :
                Not
                  (e = advance ring F.A.left p ∧
                    p + 1 = F.A.gap) := by
              intro ht
              have hgap : F.A.gap = F.a := F.A_gap
              omega
            obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
              longLiveWaitLiveNext_bounds
                F.A C p hA e hnotTerminal
            by_cases hreach :
                nextSectorPhase F.A (.live p) e =
                  .live (F.a - 2 * F.b)
            · rw [dif_pos hreach] at hstep
              cases hstep
              exact True.intro
            · rw [dif_neg hreach] at hstep
              cases hstep
              have hp'Cut :
                  p' < F.a - 2 * F.b := by
                have hle :
                    p' <= F.a - 2 * F.b := by
                  omega
                cases Nat.lt_or_eq_of_le hle with
                | inl hlt =>
                    exact hlt
                | inr heq =>
                    exact False.elim
                      (hreach (by rw [hnextA, heq]))
              have hlegit :
                  longStageLegit F (stepE ring C e)
                    (.advance
                      (nextSectorPhase F.B targetPhase e)
                      (nextSectorPhase F.A (.live p) e)) :=
                And.intro hBnext
                  (And.intro hAnext
                    ⟨p', hnextA, by omega, hp'Cut⟩)
              simpa [longLiveWaitPostInvariant] using hlegit
        | race targetPhase attackPhase =>
            dsimp only at hstep
            by_cases hready : targetPhase = .ready
            · rw [dif_pos hready] at hstep
              by_cases hout : e = R_j F
              · rw [dif_pos hout] at hstep
                cases hstep
                exact True.intro
              · rw [dif_neg hout] at hstep
                by_cases hin : e = L_j F
                · rw [dif_pos hin] at hstep
                  cases hstep
                  exact True.intro
                · rw [dif_neg hin] at hstep
                  cases hstep
                  exact True.intro
            · rw [dif_neg hready] at hstep
              by_cases hhit :
                  Exists fun p =>
                    attackPhase = .live p ∧
                      e = advance ring F.A.left p ∧
                      p + 1 = F.a
              · rw [dif_pos hhit] at hstep
                cases hstep
                exact True.intro
              · rw [dif_neg hhit] at hstep
                by_cases htarget :
                    nextSectorPhase F.B targetPhase e = .ready
                · rw [dif_pos htarget] at hstep
                  cases hstep
                  exact True.intro
                · rw [dif_neg htarget] at hstep
                  cases hstep
                  exact True.intro
        | incident attackPhase =>
            dsimp only at hstep
            by_cases hout : e = R_j F
            · rw [dif_pos hout] at hstep
              cases hstep
              exact True.intro
            · rw [dif_neg hout] at hstep
              by_cases hin : e = L_j F
              · rw [dif_pos hin] at hstep
                cases hstep
                exact True.intro
              · rw [dif_neg hin] at hstep
                by_cases hready :
                    nextSectorPhase F.B .ready e = .ready
                · rw [dif_pos hready] at hstep
                  cases hstep
                  exact True.intro
                · rw [dif_neg hready] at hstep
                  cases hstep
                  exact True.intro
        | retained targetPhase attackPhase =>
            dsimp only at hstep
            by_cases hfail :
                targetPhase = .ready ∧ e = R_j F
            · rw [dif_pos hfail] at hstep
              cases hstep
              exact True.intro
            · rw [dif_neg hfail] at hstep
              cases hstep
              exact True.intro
        | recovery targetPhase attackPhase =>
            dsimp only at hstep
            by_cases hready :
                nextSectorPhase F.B targetPhase e = .ready
            · rw [dif_pos hready] at hstep
              cases hstep
            · rw [dif_neg hready] at hstep
              cases hstep
              exact True.intro
        | stuck =>
            exact False.elim ha


private theorem longLiveWait_after_path
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (s : Config n) (hs : AttemptGood ring F s)
    (carrier a : LongAttemptState ring F)
    (hfirst :
      RetryFirstCutReachableCorrected
        (longAttemptKernel ring F)
        (longPostCRCutCorrected F)
        ((longAttemptKernel ring F).start s)
        carrier)
    (hafter :
      RetryActiveAfterCutCorrected
        (longAttemptKernel ring F)
        (longPostCRCutCorrected F)
        carrier a) :
    longLiveWaitPostInvariant F a := by
  have hcarrier :=
    longLiveWait_first_post
      hSealed ring F s hs carrier hfirst
  induction hafter with
  | root hcut =>
      exact hcarrier
  | step h e hstep hcut ih =>
      exact
        longLiveWait_post_step
          hSealed ring F hb hab
          _ ih e _ hstep




/-! ## Literal LiveWait children -/


private theorem longLiveWait_children_cut
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase attackPhase : SectorPhase) :
    ∀ e a',
      (longAttemptKernel ring F).step
          (.live C hgood
            (.liveWait targetPhase attackPhase)) e =
        .active a' →
      longPostCRCutCorrected F a' = true := by
  intro e a' hstep
  classical
  simp only [longAttemptKernel] at hstep
  unfold longStep at hstep
  dsimp only at hstep
  by_cases htag : TaggedDeleted F (stepE ring C e)
  · rw [dif_pos htag] at hstep
    cases hstep
  · rw [dif_neg htag] at hstep
    by_cases hfire :
        attackPhase = .ready ∧ e = F.A.left
    · rw [dif_pos hfire] at hstep
      by_cases hnear :
          F.a - 2 * F.b ≤ 1
      · rw [dif_pos hnear] at hstep
        cases hstep
        rfl
      · rw [dif_neg hnear] at hstep
        cases hstep
        rfl
    · rw [dif_neg hfire] at hstep
      cases hstep
      rfl


private theorem longLiveWait_children_legit
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (hab : 2 * F.b + 1 ≤ F.a)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase attackPhase : SectorPhase)
    (hlegit :
      longStageLegit F C
        (.liveWait targetPhase attackPhase)) :
    ∀ e a',
      (longAttemptKernel ring F).step
          (.live C hgood
            (.liveWait targetPhase attackPhase)) e =
        .active a' →
      match a' with
      | .junk _ => False
      | .live D _ stage' =>
          longStageLegit F D stage' := by
  intro e a' hstep
  classical
  dsimp only [longStageLegit] at hlegit
  rcases hlegit with ⟨hB, hA, hnon⟩
  have hnon0 : longLiveWaitNonLive attackPhase := by
    revert hnon
    cases attackPhase <;> simp [longLiveWaitNonLive]
  simp only [longAttemptKernel] at hstep
  unfold longStep at hstep
  dsimp only at hstep
  by_cases htag : TaggedDeleted F (stepE ring C e)
  · rw [dif_pos htag] at hstep
    cases hstep
  · rw [dif_neg htag] at hstep
    have hBnext :=
      moderateSealed_phaseBNext
        hSealed ring F C hgood
        targetPhase hB e htag
    have hAnext :=
      moderateSealed_phaseANext
        hSealed ring F C hgood
        attackPhase hA e htag
    by_cases hfire :
        attackPhase = .ready ∧ e = F.A.left
    · rw [dif_pos hfire] at hstep
      have hgap : F.A.gap ≠ 1 := by
        intro hg
        have ha1 : F.a = 1 := by
          rw [← F.A_gap]
          exact hg
        omega
      have hnextA :
          nextSectorPhase F.A attackPhase e = .live 1 := by
        rw [hfire.1, hfire.2]
        simp [nextSectorPhase,
          left_ne_sealedIncomingEdge F.A, hgap]
      by_cases hnear :
          F.a - 2 * F.b ≤ 1
      · rw [dif_pos hnear] at hstep
        cases hstep
        exact
          And.intro hBnext
            (And.intro hAnext
              ⟨1, hnextA, by omega⟩)
      · rw [dif_neg hnear] at hstep
        cases hstep
        exact
          And.intro hBnext
            (And.intro hAnext
              ⟨1, hnextA, by omega, by omega⟩)
    · rw [dif_neg hfire] at hstep
      cases hstep
      have hnonNext :=
        longLiveWaitNonLive_next
          F.A attackPhase hnon0 e hfire
      exact
        And.intro hBnext
          (And.intro hAnext
            (by
              generalize
                nextSectorPhase F.A attackPhase e = q at hnonNext ⊢
              revert hnonNext
              cases q <;> simp [longLiveWaitNonLive]))


/-! ## LiveWait Bellman row -/


private theorem longLiveWait_node_le
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (hab : 2 * F.b + 1 ≤ F.a)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase attackPhase : SectorPhase)
    (hB : PhaseHolds F.B C targetPhase)
    (e : Fin n) :
    attemptNodePotLong
        (longRawPhiCorrected ring F)
        ((longAttemptKernel ring F).step
          (.live C hgood
            (.liveWait targetPhase attackPhase)) e) ≤
      n *
        (longLaunchPhaseUnits F.a
            (nextSectorPhase F.A attackPhase e) +
          longAdvanceReserveUnits F) := by
  classical
  simp only [longAttemptKernel]
  unfold longStep
  dsimp only
  by_cases htag : TaggedDeleted F (stepE ring C e)
  · rw [dif_pos htag]
    simp [attemptNodePotLong]
  · rw [dif_neg htag]
    have hBnext :=
      moderateSealed_phaseBNext
        hSealed ring F C hgood
        targetPhase hB e htag
    by_cases hfire :
        attackPhase = .ready ∧ e = F.A.left
    · rw [dif_pos hfire]
      have hgap : F.A.gap ≠ 1 := by
        intro hg
        have ha1 : F.a = 1 := by
          rw [← F.A_gap]
          exact hg
        omega
      have hnextA :
          nextSectorPhase F.A attackPhase e = .live 1 := by
        rw [hfire.1, hfire.2]
        simp [nextSectorPhase,
          left_ne_sealedIncomingEdge F.A, hgap]
      by_cases hnear :
          F.a - 2 * F.b ≤ 1
      · rw [dif_pos hnear]
        have hdebt :=
          longLiveWaitPhaseDebt_le
            F.B (stepE ring C e)
            (nextSectorPhase F.B targetPhase e)
            hBnext
        rw [F.B_gap] at hdebt
        have hchild :
            phaseDebt F.b
                (nextSectorPhase F.B targetPhase e) +
                longIncidentReserveUnits F ≤
              longAdvanceReserveUnits F := by
          unfold longAdvanceReserveUnits
            longRaceReserveUnits
          omega
        have hmul :=
          Nat.mul_le_mul_left n hchild
        simp only [attemptNodePotLong,
          longRawPhiCorrected, longStageUnits]
        rw [hnextA]
        simp only [longLaunchPhaseUnits, Nat.zero_add]
        simpa using hmul
      · rw [dif_neg hnear]
        have hinner :
            longAdvancePhaseUnits F (.live 1) +
                longRaceReserveUnits F ≤
              longAdvanceReserveUnits F := by
          simp only [longAdvancePhaseUnits]
          unfold longAdvanceReserveUnits
          omega
        have hmul :=
          Nat.mul_le_mul_left n hinner
        simp only [attemptNodePotLong,
          longRawPhiCorrected, longStageUnits]
        rw [hnextA]
        simp only [longLaunchPhaseUnits, Nat.zero_add]
        simpa using hmul
    · rw [dif_neg hfire]
      simp [attemptNodePotLong,
        longRawPhiCorrected, longStageUnits]


private def longLiveWaitServiceOffset : SectorPhase → Nat
  | .ready => 0
  | .dummy p => p
  | .live p => p
  | .ret q => q - 1


private def longLiveWaitService
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (A : SectorFrame ring C0)
    (ph : SectorPhase) : Fin n :=
  advance ring A.left (longLiveWaitServiceOffset ph)


private theorem longLiveWait_next_eq_self_of_ne_service
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (A : SectorFrame ring C0)
    (ph : SectorPhase)
    (hnon : longLiveWaitNonLive ph)
    (hnot : ph ≠ .ready)
    (e : Fin n)
    (hne : e ≠ longLiveWaitService A ph) :
    nextSectorPhase A ph e = ph := by
  cases ph with
  | ready =>
      exact False.elim (hnot rfl)
  | dummy p =>
      have hne' : e ≠ advance ring A.left p := by
        simpa [longLiveWaitService,
          longLiveWaitServiceOffset] using hne
      simp [nextSectorPhase, hne']
  | live p =>
      exact False.elim hnon
  | ret q =>
      have hne' :
          e ≠ advance ring A.left (q - 1) := by
        simpa [longLiveWaitService,
          longLiveWaitServiceOffset] using hne
      simp [nextSectorPhase, hne']


private theorem longLiveWait_debt_service
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (A : SectorFrame ring C0)
    (C : Config n)
    (ph : SectorPhase)
    (hphase : PhaseHolds A C ph)
    (hnon : longLiveWaitNonLive ph)
    (hnot : ph ≠ .ready) :
    phaseDebt A.gap
        (nextSectorPhase A ph
          (longLiveWaitService A ph)) + 1 =
      phaseDebt A.gap ph := by
  cases ph with
  | ready =>
      exact False.elim (hnot rfl)
  | dummy p =>
      have hp : p < A.gap := hphase.2.1.1
      by_cases hn : p + 1 < A.gap
      · simp [longLiveWaitService,
          longLiveWaitServiceOffset,
          nextSectorPhase, phaseDebt, hn]
        omega
      · by_cases hg : A.gap = 1
        · simp [longLiveWaitService,
            longLiveWaitServiceOffset,
            nextSectorPhase, phaseDebt, hn, hg]
          omega
        · simp [longLiveWaitService,
            longLiveWaitServiceOffset,
            nextSectorPhase, phaseDebt, hn, hg]
          omega
  | live p =>
      exact False.elim hnon
  | ret q =>
      have hq0 : 0 < q := hphase.2.1
      by_cases hq1 : q = 1
      · simp [longLiveWaitService,
          longLiveWaitServiceOffset,
          nextSectorPhase, phaseDebt, hq1]
      · simp [longLiveWaitService,
          longLiveWaitServiceOffset,
          nextSectorPhase, phaseDebt, hq1]
        omega


private theorem longLiveWait_launch_eq_debt
    (d : Nat) (ph : SectorPhase)
    (hnon : longLiveWaitNonLive ph) :
    longLaunchPhaseUnits d ph =
      phaseDebt d ph + 2 * d := by
  cases ph with
  | ready =>
      simp [longLaunchPhaseUnits, phaseDebt]
  | dummy p =>
      rfl
  | live p =>
      exact False.elim hnon
  | ret q =>
      simp [longLaunchPhaseUnits, phaseDebt]


private theorem longLiveWait_nonready_bellman
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (hab : 2 * F.b + 1 ≤ F.a)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase attackPhase : SectorPhase)
    (hB : PhaseHolds F.B C targetPhase)
    (hA : PhaseHolds F.A C attackPhase)
    (hnon : longLiveWaitNonLive attackPhase)
    (hnot : attackPhase ≠ .ready) :
    n +
        (List.ofFn (fun e : Fin n =>
          attemptNodePotLong
            (longRawPhiCorrected ring F)
            ((longAttemptKernel ring F).step
              (.live C hgood
                (.liveWait targetPhase attackPhase)) e))).sum ≤
      n * longRawPhiCorrected ring F
        (.live C hgood
          (.liveWait targetPhase attackPhase)) := by
  classical
  let service : Fin n :=
    longLiveWaitService F.A attackPhase
  let c : Nat :=
    n *
      (longLaunchPhaseUnits F.a attackPhase +
        longAdvanceReserveUnits F)
  let ca : Nat :=
    n *
      ((longLaunchPhaseUnits F.a attackPhase - 1) +
        longAdvanceReserveUnits F)
  let f : Fin n → Nat :=
    fun e =>
      attemptNodePotLong
        (longRawPhiCorrected ring F)
        ((longAttemptKernel ring F).step
          (.live C hgood
            (.liveWait targetPhase attackPhase)) e)


  have hfireService :
      ¬(attackPhase = .ready ∧ service = F.A.left) := by
    intro h
    exact hnot h.1
  have hnonNext :
      longLiveWaitNonLive
        (nextSectorPhase F.A attackPhase service) :=
    longLiveWaitNonLive_next
      F.A attackPhase hnon service hfireService
  have hdebt :=
    longLiveWait_debt_service
      F.A C attackPhase hA hnon hnot
  rw [F.A_gap] at hdebt
  have hlaunchNext :=
    longLiveWait_launch_eq_debt
      F.a
      (nextSectorPhase F.A attackPhase service)
      hnonNext
  have hlaunchCurrent :=
    longLiveWait_launch_eq_debt
      F.a attackPhase hnon
  have hdrop :
      longLaunchPhaseUnits F.a
          (nextSectorPhase F.A attackPhase service) + 1 =
        longLaunchPhaseUnits F.a attackPhase := by
    have hdebt' :
        phaseDebt F.a
            (nextSectorPhase F.A attackPhase service) + 1 =
          phaseDebt F.a attackPhase := hdebt
    rw [hlaunchNext, hlaunchCurrent]
    omega


  have hservice : f service ≤ ca := by
    have hnode :=
      longLiveWait_node_le
        hSealed ring F hb hab
        C hgood targetPhase attackPhase hB service
    have hinner :
        longLaunchPhaseUnits F.a
              (nextSectorPhase F.A attackPhase service) +
              longAdvanceReserveUnits F ≤
          (longLaunchPhaseUnits F.a attackPhase - 1) +
            longAdvanceReserveUnits F := by
      omega
    exact
      Nat.le_trans hnode
        (Nat.mul_le_mul_left n hinner)


  have hother :
      ∀ e, e ≠ service → f e ≤ c := by
    intro e hne
    have hsame :=
      longLiveWait_next_eq_self_of_ne_service
        F.A attackPhase hnon hnot e hne
    have hnode :=
      longLiveWait_node_le
        hSealed ring F hb hab
        C hgood targetPhase attackPhase hB e
    rw [hsame] at hnode
    simpa [c] using hnode


  have hpos :
      0 < longLaunchPhaseUnits F.a attackPhase := by
    omega
  have hsplit :
      longLaunchPhaseUnits F.a attackPhase =
        (longLaunchPhaseUnits F.a attackPhase - 1) + 1 := by
    omega
  have hpay : n + ca ≤ c := by
    have heq : n + ca = c := by
      dsimp [ca, c]
      rw [hsplit]
      simp only [Nat.mul_add, Nat.mul_one,
        Nat.add_sub_cancel] at *
      omega
    exact Nat.le_of_eq heq


  have hrow :=
    moderateSealed_oneExceptionBound
      service f hservice hother hpay
  simpa [f, c, longRawPhiCorrected,
    longStageUnits] using hrow


private theorem longLiveWait_ready_bellman
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (hab : 2 * F.b + 1 ≤ F.a)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase : SectorPhase)
    (hB : PhaseHolds F.B C targetPhase) :
    n +
        (List.ofFn (fun e : Fin n =>
          attemptNodePotLong
            (longRawPhiCorrected ring F)
            ((longAttemptKernel ring F).step
              (.live C hgood
                (.liveWait targetPhase .ready)) e))).sum ≤
      n * longRawPhiCorrected ring F
        (.live C hgood
          (.liveWait targetPhase .ready)) := by
  classical
  let incoming := sealedIncomingEdge F.A
  let source := F.A.left
  have hsourceIncoming : source ≠ incoming := by
    exact left_ne_sealedIncomingEdge F.A
  have hincomingSource : incoming ≠ source :=
    Ne.symm hsourceIncoming
  have hgap : F.A.gap ≠ 1 := by
    intro hg
    have ha1 : F.a = 1 := by
      rw [← F.A_gap]
      exact hg
    omega


  let f : Fin n → Nat :=
    fun e =>
      attemptNodePotLong
        (longRawPhiCorrected ring F)
        ((longAttemptKernel ring F).step
          (.live C hgood
            (.liveWait targetPhase .ready)) e)
  let c : Nat :=
    n *
      (longLaunchPhaseUnits F.a .ready +
        longAdvanceReserveUnits F)
  let cin : Nat :=
    n *
      (longLaunchPhaseUnits F.a (.dummy 0) +
        longAdvanceReserveUnits F)
  let cout : Nat :=
    n * longAdvanceReserveUnits F


  have hin : f incoming ≤ cin := by
    have hnode :=
      longLiveWait_node_le
        hSealed ring F hb hab
        C hgood targetPhase .ready hB incoming
    have hnextA :
        nextSectorPhase F.A .ready incoming =
          .dummy 0 := by
      simp [incoming, nextSectorPhase]
    rw [hnextA] at hnode
    simpa [cin] using hnode


  have hout : f source ≤ cout := by
    have hnode :=
      longLiveWait_node_le
        hSealed ring F hb hab
        C hgood targetPhase .ready hB source
    have hnextA :
        nextSectorPhase F.A .ready source =
          .live 1 := by
      simp [source, incoming, nextSectorPhase,
        hsourceIncoming, hgap]
    rw [hnextA] at hnode
    simpa [cout, longLaunchPhaseUnits] using hnode


  have hother :
      ∀ e, e ≠ incoming → e ≠ source → f e ≤ c := by
    intro e hei hes
    have hnode :=
      longLiveWait_node_le
        hSealed ring F hb hab
        C hgood targetPhase .ready hB e
    have hnextA :
        nextSectorPhase F.A .ready e = .ready := by
      simp [incoming, source, nextSectorPhase, hei, hes]
    rw [hnextA] at hnode
    simpa [c] using hnode


  have hinner :
      1 +
          (longLaunchPhaseUnits F.a (.dummy 0) +
            longAdvanceReserveUnits F) +
          longAdvanceReserveUnits F =
        (longLaunchPhaseUnits F.a .ready +
            longAdvanceReserveUnits F) +
          (longLaunchPhaseUnits F.a .ready +
            longAdvanceReserveUnits F) := by
    simp [longLaunchPhaseUnits, phaseDebt]
    omega


  have hpay : n + cin + cout ≤ c + c := by
    apply Nat.le_of_eq
    dsimp [cin, cout, c]
    calc
      n +
          n *
            (longLaunchPhaseUnits F.a (.dummy 0) +
              longAdvanceReserveUnits F) +
          n * longAdvanceReserveUnits F =
        n *
          (1 +
              (longLaunchPhaseUnits F.a (.dummy 0) +
                longAdvanceReserveUnits F) +
              longAdvanceReserveUnits F) := by
            simp only [Nat.mul_add, Nat.mul_one]
      _ =
        n *
          ((longLaunchPhaseUnits F.a .ready +
              longAdvanceReserveUnits F) +
            (longLaunchPhaseUnits F.a .ready +
              longAdvanceReserveUnits F)) := by
            rw [hinner]
      _ =
        n *
            (longLaunchPhaseUnits F.a .ready +
              longAdvanceReserveUnits F) +
          n *
            (longLaunchPhaseUnits F.a .ready +
              longAdvanceReserveUnits F) := by
            rw [Nat.mul_add]


  have hrow :=
    moderateSealed_twoExceptionBound
      incoming source f hincomingSource
      hin hout hother hpay
  simpa [f, c, longRawPhiCorrected,
    longStageUnits] using hrow


private theorem longLiveWait_bellman_corrected
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (hab : 2 * F.b + 1 ≤ F.a)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase attackPhase : SectorPhase)
    (hlegit :
      longStageLegit F C
        (.liveWait targetPhase attackPhase)) :
    n +
        (List.ofFn (fun e : Fin n =>
          attemptNodePotLong
            (longRawPhiCorrected ring F)
            ((longAttemptKernel ring F).step
              (.live C hgood
                (.liveWait targetPhase attackPhase)) e))).sum ≤
      n * longRawPhiCorrected ring F
        (.live C hgood
          (.liveWait targetPhase attackPhase)) := by
  dsimp only [longStageLegit] at hlegit
  rcases hlegit with ⟨hB, hA, hnon⟩
  have hnon0 : longLiveWaitNonLive attackPhase := by
    revert hnon
    cases attackPhase <;> simp [longLiveWaitNonLive]
  cases attackPhase with
  | ready =>
      exact
        longLiveWait_ready_bellman
          hSealed ring F hb hab
          C hgood targetPhase hB
  | dummy p =>
      exact
        longLiveWait_nonready_bellman
          hSealed ring F hb hab
          C hgood targetPhase (.dummy p)
          hB hA
          (by simp [longLiveWaitNonLive])
          (by simp)
  | live p =>
      exact False.elim hnon0
  | ret q =>
      exact
        longLiveWait_nonready_bellman
          hSealed ring F hb hab
          C hgood targetPhase (.ret q)
          hB hA
          (by simp [longLiveWaitNonLive])
          (by simp)


private theorem longLiveWait_local_row
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (hab : 2 * F.b + 1 ≤ F.a)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase attackPhase : SectorPhase)
    (hlegit :
      longStageLegit F C
        (.liveWait targetPhase attackPhase)) :
    LongLocalStageRow
      ring F C hgood
        (.liveWait targetPhase attackPhase) := by
  refine And.intro ?_ ?_
  · exact
      longLiveWait_children_legit
        hSealed ring F hb hab
        C hgood targetPhase attackPhase hlegit
  · exact
      longLiveWait_bellman_corrected
        hSealed ring F hb hab
        C hgood targetPhase attackPhase hlegit


/-! ## Requested residual -/


theorem longLiveWaitPostCarrierResidual_proved :
    LongLiveWaitPostCarrierResidual := by
  unfold LongLiveWaitPostCarrierResidual
  intro hSealed n ring C0 F hb hab
  intro s carrier C hgoodC targetPhase attackPhase
  intro hgoodS hfirst hafter


  have hinv :=
    longLiveWait_after_path
      hSealed ring F hb hab
      s hgoodS carrier
      (.live C hgoodC
        (.liveWait targetPhase attackPhase))
      hfirst hafter
  have hlegit :
      longStageLegit F C
        (.liveWait targetPhase attackPhase) := by
    simpa [longLiveWaitPostInvariant] using hinv


  refine And.intro ?_ ?_
  · simpa [longSemanticGoodCorrected] using hlegit
  · refine And.intro ?_ ?_
    · exact
        longLiveWait_children_cut
          ring F C hgoodC
          targetPhase attackPhase
    · exact
        longLiveWait_local_row
          hSealed ring F hb hab
          C hgoodC targetPhase attackPhase hlegit


end PPL.Convergence.LDLocal


#print axioms PPL.Convergence.LDLocal.longLiveWaitPostCarrierResidual_proved


