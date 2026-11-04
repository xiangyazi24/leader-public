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

private def longAdvanceNonLive : SectorPhase -> Prop
  | .live _ => False
  | _ => True

private theorem longAdvanceNonLive_next
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (ph : SectorPhase)
    (h : longAdvanceNonLive ph)
    (e : Fin n)
    (hfire : Not (ph = .ready /\ e = A.left)) :
    longAdvanceNonLive (nextSectorPhase A ph e) := by
  cases ph with
  | ready =>
      have hsrc : e ≠ A.left := by
        intro he
        exact hfire (And.intro rfl he)
      by_cases hin : e = sealedIncomingEdge A
      · simp [nextSectorPhase, hin, longAdvanceNonLive]
      · simp [nextSectorPhase, hin, hsrc, longAdvanceNonLive]
  | dummy p =>
      by_cases hs : e = advance ring A.left p
      · by_cases hlt : p + 1 < A.gap
        · simp [nextSectorPhase, hs, hlt, longAdvanceNonLive]
        · by_cases hgap : A.gap = 1
          · simp [nextSectorPhase, hs, hlt, hgap,
              longAdvanceNonLive]
          · simp [nextSectorPhase, hs, hlt, hgap,
              longAdvanceNonLive]
      · simp [nextSectorPhase, hs, longAdvanceNonLive]
  | live p =>
      exact False.elim h
  | ret q =>
      by_cases hs : e = advance ring A.left (q - 1)
      · by_cases hq : q = 1
        · simp [nextSectorPhase, hs, hq, longAdvanceNonLive]
        · simp [nextSectorPhase, hs, hq, longAdvanceNonLive]
      · simp [nextSectorPhase, hs, longAdvanceNonLive]

private theorem longAdvanceLiveNext_bounds
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (p : Nat)
    (hphase : PhaseHolds A C (.live p))
    (e : Fin n)
    (hterminal :
      Not (e = advance ring A.left p /\ p + 1 = A.gap)) :
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

private theorem longAdvancePhaseDebt_le
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

private theorem longAdvancePhaseReady
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n)
    (hInterior : CRInteriorFollowers A C)
    (hclean : CleanReady A C) :
    PhaseHolds A C .ready := by
  exact And.intro hInterior hclean

/-! ## Literal-start mirror, avoiding private upstream names -/

private noncomputable def longAdvanceCRInitMode
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

private noncomputable def longAdvanceAfterTargetStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : LongStage := by
  classical
  if hA : CleanReady F.A D then
    exact .liveWait .ready .ready
  else
    exact .attackerCR .ready
      (longAdvanceCRInitMode ring F.A D hgood.1
        (moderateSealed_notEndpointA F D hgood) hA)

private noncomputable def longAdvanceInitialStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : LongStage := by
  classical
  if hB : CleanReady F.B D then
    exact longAdvanceAfterTargetStage ring F D hgood
  else
    exact .targetCR
      (longAdvanceCRInitMode ring F.B D hgood.1
        (moderateSealed_notEndpointB F D hgood) hB)

private noncomputable def longAdvanceStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) : LongAttemptState ring F := by
  classical
  if hgood : AttemptGood ring F D then
    exact .live D hgood
      (longAdvanceInitialStage ring F D hgood)
  else
    exact .junk D

private theorem longAdvance_start_eq
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) :
    (longAttemptKernel ring F).start D =
      longAdvanceStart ring F D := by
  rfl

/-! ## Minimal provenance invariant through the first post-CR cut -/

private def longAdvancePreInvariant
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

private def longAdvancePostInvariant
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

private theorem longAdvance_pre_start
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s)
    (hcut :
      longPostCRCutCorrected F
        ((longAttemptKernel ring F).start s) = false) :
    longAdvancePreInvariant F
      ((longAttemptKernel ring F).start s) := by
  classical
  rw [longAdvance_start_eq] at hcut ⊢
  unfold longAdvanceStart at hcut ⊢
  rw [dif_pos hs] at hcut ⊢
  unfold longAdvanceInitialStage at hcut ⊢
  by_cases hB : CleanReady F.B s
  · rw [dif_pos hB] at hcut ⊢
    unfold longAdvanceAfterTargetStage at hcut ⊢
    by_cases hA : CleanReady F.A s
    · rw [dif_pos hA] at hcut ⊢
      simp [longPostCRCutCorrected] at hcut
    · rw [dif_neg hA] at hcut ⊢
      exact
        longAdvancePhaseReady
          F.B s hs.2.2.2 hB
  · rw [dif_neg hB] at hcut ⊢
    exact True.intro

private theorem longAdvance_pre_step
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (ha : longAdvancePreInvariant F a)
    (e : Fin n) (a' : LongAttemptState ring F)
    (hstep :
      (longAttemptKernel ring F).step a e = .active a')
    (hcut : longPostCRCutCorrected F a' = false) :
    longAdvancePreInvariant F a' := by
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
                  longAdvancePhaseReady
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
            change PhaseHolds F.B C targetPhase at ha
            by_cases hmode : CRModeHolds F.A C mode
            · rw [dif_pos hmode] at hstep
              have hBnext :=
                moderateSealed_phaseBNext
                  hSealed ring F C hgood
                  targetPhase ha e htag
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

private theorem longAdvance_pre_before
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
    longAdvancePreInvariant F a := by
  induction h with
  | root hroot =>
      exact longAdvance_pre_start ring F s hs hroot
  | step h e hstep hcut ih =>
      exact
        longAdvance_pre_step
          hSealed ring F _ ih e _ hstep hcut

private theorem longAdvance_start_post
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s)
    (hcut :
      longPostCRCutCorrected F
        ((longAttemptKernel ring F).start s) = true) :
    longAdvancePostInvariant F
      ((longAttemptKernel ring F).start s) := by
  classical
  rw [longAdvance_start_eq] at hcut ⊢
  unfold longAdvanceStart at hcut ⊢
  rw [dif_pos hs] at hcut ⊢
  unfold longAdvanceInitialStage at hcut ⊢
  by_cases hB : CleanReady F.B s
  · rw [dif_pos hB] at hcut ⊢
    unfold longAdvanceAfterTargetStage at hcut ⊢
    by_cases hA : CleanReady F.A s
    · rw [dif_pos hA] at hcut ⊢
      have hBready :=
        longAdvancePhaseReady
          F.B s hs.2.2.2 hB
      have hAready :=
        longAdvancePhaseReady
          F.A s hs.2.2.1 hA
      change longStageLegit F s (.liveWait .ready .ready)
      exact
        And.intro hBready
          (And.intro hAready True.intro)
    · rw [dif_neg hA] at hcut ⊢
      simp [longPostCRCutCorrected] at hcut
  · rw [dif_neg hB] at hcut ⊢
    simp [longPostCRCutCorrected] at hcut

private theorem longAdvance_first_post
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
    longAdvancePostInvariant F carrier := by
  classical
  rcases hfirst with hroot | hstep
  · rcases hroot with ⟨hEq, hcut⟩
    subst carrier
    exact longAdvance_start_post ring F s hs hcut
  · rcases hstep with
      ⟨p, hbefore, e, hstep, hcut⟩
    have hp :=
      longAdvance_pre_before
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
                    longAdvancePhaseReady
                      F.B (stepE ring C e)
                      hgoodD.2.2.2 hcleanB
                  revert hcut
                  unfoldLongAfterTargetStage
                  by_cases hA :
                      CleanReady F.A (stepE ring C e)
                  · rw [dif_pos hA]
                    intro _hcut
                    have hAready :=
                      longAdvancePhaseReady
                        F.A (stepE ring C e)
                        hgoodD.2.2.1 hA
                    change
                      longStageLegit F (stepE ring C e)
                        (.liveWait .ready .ready)
                    exact
                      And.intro hBready
                        (And.intro hAready True.intro)
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
              change PhaseHolds F.B C targetPhase at hp
              by_cases hmode : CRModeHolds F.A C mode
              · rw [dif_pos hmode] at hstep
                have hBnext :=
                  moderateSealed_phaseBNext
                    hSealed ring F C hgood
                    targetPhase hp e htag
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
                    longAdvancePhaseReady
                      F.A (stepE ring C e)
                      hgoodD.2.2.1 hcleanA
                  change
                    longStageLegit F (stepE ring C e)
                      (.liveWait
                        (nextSectorPhase F.B targetPhase e)
                        .ready)
                  exact
                    And.intro hBnext
                      (And.intro hAready True.intro)
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

private theorem longAdvance_post_step
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (a : LongAttemptState ring F)
    (ha : longAdvancePostInvariant F a)
    (e : Fin n) (a' : LongAttemptState ring F)
    (hstep :
      (longAttemptKernel ring F).step a e = .active a') :
    longAdvancePostInvariant F a' := by
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
            dsimp only [longAdvancePostInvariant, longStageLegit] at ha
            rcases ha with ⟨hB, hA, hnon⟩
            have hBnext :=
              moderateSealed_phaseBNext
                hSealed ring F C hgood
                targetPhase hB e htag
            have hAnext :=
              moderateSealed_phaseANext
                hSealed ring F C hgood
                attackPhase hA e htag
            have hnon0 : longAdvanceNonLive attackPhase := by
              revert hnon
              cases attackPhase <;> simp [longAdvanceNonLive]
            by_cases hfire :
                attackPhase = .ready /\ e = F.A.left
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
                change
                  longStageLegit F (stepE ring C e)
                    (.advance
                      (nextSectorPhase F.B targetPhase e)
                      (nextSectorPhase F.A attackPhase e))
                exact
                  And.intro hBnext
                    (And.intro hAnext
                      ⟨1, hnextA, by omega, by omega⟩)
            · rw [dif_neg hfire] at hstep
              cases hstep
              have hnonNext :=
                longAdvanceNonLive_next
                  F.A attackPhase hnon0 e hfire
              change
                longStageLegit F (stepE ring C e)
                  (.liveWait
                    (nextSectorPhase F.B targetPhase e)
                    (nextSectorPhase F.A attackPhase e))
              exact
                And.intro hBnext
                  (And.intro hAnext
                    (by
                      generalize nextSectorPhase F.A attackPhase e = q at hnonNext ⊢
                      revert hnonNext
                      cases q <;> simp [longAdvanceNonLive]))
        | advance targetPhase attackPhase =>
            dsimp only at hstep
            change
              PhaseHolds F.B C targetPhase /\
                PhaseHolds F.A C attackPhase /\
                Exists fun p =>
                  attackPhase = .live p /\
                    0 < p /\
                    p < F.a - 2 * F.b at ha
            rcases ha with
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
                  (e = advance ring F.A.left p /\
                    p + 1 = F.A.gap) := by
              intro ht
              have hgap : F.A.gap = F.a := F.A_gap
              omega
            obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
              longAdvanceLiveNext_bounds
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
              change
                longStageLegit F (stepE ring C e)
                  (.advance
                    (nextSectorPhase F.B targetPhase e)
                    (nextSectorPhase F.A (.live p) e))
              exact
                And.intro hBnext
                  (And.intro hAnext
                    ⟨p', hnextA, by omega, hp'Cut⟩)
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
                    attackPhase = .live p /\
                      e = advance ring F.A.left p /\
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
                targetPhase = .ready /\ e = R_j F
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

private theorem longAdvance_after_path
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
    longAdvancePostInvariant F a := by
  have hcarrier :=
    longAdvance_first_post
      hSealed ring F s hs carrier hfirst
  induction hafter with
  | root hcut =>
      exact hcarrier
  | step h e hstep hcut ih =>
      exact
        longAdvance_post_step
          hSealed ring F hb hab
          _ ih e _ hstep

/-! ## Literal Advance children -/

private theorem longAdvance_children_cut
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase attackPhase : SectorPhase) :
    forall e a',
      (longAttemptKernel ring F).step
          (.live C hgood
            (.advance targetPhase attackPhase)) e =
        .active a' ->
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
    by_cases hreach :
        nextSectorPhase F.A attackPhase e =
          .live (F.a - 2 * F.b)
    · rw [dif_pos hreach] at hstep
      cases hstep
      rfl
    · rw [dif_neg hreach] at hstep
      cases hstep
      rfl

private theorem longAdvance_children_legit
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase attackPhase : SectorPhase)
    (hlegit :
      longStageLegit F C
        (.advance targetPhase attackPhase)) :
    forall e a',
      (longAttemptKernel ring F).step
          (.live C hgood
            (.advance targetPhase attackPhase)) e =
        .active a' ->
      match a' with
      | .junk _ => False
      | .live D _ stage' =>
          longStageLegit F D stage' := by
  intro e a' hstep
  classical
  change
    PhaseHolds F.B C targetPhase /\
      PhaseHolds F.A C attackPhase /\
      Exists fun p =>
        attackPhase = .live p /\
          0 < p /\
          p < F.a - 2 * F.b at hlegit
  rcases hlegit with
    ⟨hB, hA, p, hattack, hp0, hpCut⟩
  subst attackPhase
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
        (.live p) hA e htag
    have hnotTerminal :
        Not
          (e = advance ring F.A.left p /\
            p + 1 = F.A.gap) := by
      intro ht
      have hgap : F.A.gap = F.a := F.A_gap
      omega
    obtain ⟨p', hnextA, hpLower, hpUpper⟩ :=
      longAdvanceLiveNext_bounds
        F.A C p hA e hnotTerminal
    by_cases hreach :
        nextSectorPhase F.A (.live p) e =
          .live (F.a - 2 * F.b)
    · rw [dif_pos hreach] at hstep
      cases hstep
      exact
        And.intro hBnext
          (And.intro hAnext
            ⟨F.a - 2 * F.b, hreach, by omega⟩)
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
      exact
        And.intro hBnext
          (And.intro hAnext
            ⟨p', hnextA, by omega, hp'Cut⟩)

/-! ## Advance Bellman row -/

private theorem longAdvance_bellman_corrected
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase attackPhase : SectorPhase)
    (hlegit :
      longStageLegit F C
        (.advance targetPhase attackPhase)) :
    n +
        (List.ofFn (fun e : Fin n =>
          attemptNodePotLong
            (longRawPhiCorrected ring F)
            ((longAttemptKernel ring F).step
              (.live C hgood
                (.advance targetPhase attackPhase)) e))).sum <=
      n * longRawPhiCorrected ring F
        (.live C hgood
          (.advance targetPhase attackPhase)) := by
  classical
  change
    PhaseHolds F.B C targetPhase /\
      PhaseHolds F.A C attackPhase /\
      Exists fun p =>
        attackPhase = .live p /\
          0 < p /\
          p < F.a - 2 * F.b at hlegit
  rcases hlegit with
    ⟨hB, hA, p, hattack, hp0, hpCut⟩
  subst attackPhase

  let service : Fin n :=
    advance ring F.A.left p
  let c : Nat :=
    n *
      ((F.a - 2 * F.b - p) +
        longRaceReserveUnits F)
  let ca : Nat :=
    n *
      ((F.a - 2 * F.b - p - 1) +
        longRaceReserveUnits F)
  let f : Fin n -> Nat :=
    fun e =>
      attemptNodePotLong
        (longRawPhiCorrected ring F)
        ((longAttemptKernel ring F).step
          (.live C hgood
            (.advance targetPhase (.live p))) e)

  have hservice : f service <= ca := by
    dsimp [f]
    simp only [longAttemptKernel]
    unfold longStep
    dsimp only
    by_cases htag :
        TaggedDeleted F (stepE ring C service)
    · rw [dif_pos htag]
      simp [attemptNodePotLong]
    · rw [dif_neg htag]
      have hBnext :=
        moderateSealed_phaseBNext
          hSealed ring F C hgood
          targetPhase hB service htag
      have hpGap : p + 1 < F.A.gap := by
        rw [F.A_gap]
        omega
      have hnextA :
          nextSectorPhase F.A (.live p) service =
            .live (p + 1) := by
        simp [service, nextSectorPhase, hpGap]
      by_cases hreach :
          nextSectorPhase F.A (.live p) service =
            .live (F.a - 2 * F.b)
      · rw [dif_pos hreach]
        have hpCross :
            p + 1 = F.a - 2 * F.b := by
          rw [hnextA] at hreach
          injection hreach
        have hdebt :=
          longAdvancePhaseDebt_le
            F.B (stepE ring C service)
            (nextSectorPhase F.B targetPhase service)
            hBnext
        rw [F.B_gap] at hdebt
        have hchild :
            phaseDebt F.b
                (nextSectorPhase F.B targetPhase service) +
                longIncidentReserveUnits F <=
              longRaceReserveUnits F := by
          unfold longRaceReserveUnits
          exact
            Nat.add_le_add_right
              hdebt (longIncidentReserveUnits F)
        have hmul :=
          Nat.mul_le_mul_left n hchild
        have hzero :
            F.a - 2 * F.b - p - 1 = 0 := by
          omega
        simp only [attemptNodePotLong,
          longRawPhiCorrected, longStageUnits]
        simpa [ca, hzero] using hmul
      · rw [dif_neg hreach]
        have hdelta :
            F.a - 2 * F.b - (p + 1) =
              F.a - 2 * F.b - p - 1 := by
          omega
        simp only [attemptNodePotLong,
          longRawPhiCorrected, longStageUnits]
        rw [hnextA]
        simp only [longAdvancePhaseUnits]
        simpa [ca, hdelta]

  have hother :
      forall e, e ≠ service -> f e <= c := by
    intro e hne
    dsimp [f]
    simp only [longAttemptKernel]
    unfold longStep
    dsimp only
    by_cases htag :
        TaggedDeleted F (stepE ring C e)
    · rw [dif_pos htag]
      simp [attemptNodePotLong]
    · rw [dif_neg htag]
      have hnextA :
          nextSectorPhase F.A (.live p) e =
            .live p := by
        simp [service, nextSectorPhase, hne]
      have hnotReach :
          Not
            (nextSectorPhase F.A (.live p) e =
              .live (F.a - 2 * F.b)) := by
        intro heq
        rw [hnextA] at heq
        injection heq with hpEq
        omega
      rw [dif_neg hnotReach]
      simp only [attemptNodePotLong,
        longRawPhiCorrected, longStageUnits]
      rw [hnextA]
      simp only [longAdvancePhaseUnits]
      simpa [c]

  have hsplit :
      F.a - 2 * F.b - p =
        (F.a - 2 * F.b - p - 1) + 1 := by
    omega
  have hpay : n + ca <= c := by
    have heq : n + ca = c := by
      dsimp [ca, c]
      rw [hsplit]
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel] at *
      omega
    exact Nat.le_of_eq heq

  have hrow :=
    moderateSealed_oneExceptionBound
      service f hservice hother hpay
  simpa [f, c, longRawPhiCorrected,
    longStageUnits, longAdvancePhaseUnits] using hrow

private theorem longAdvance_local_row
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase attackPhase : SectorPhase)
    (hlegit :
      longStageLegit F C
        (.advance targetPhase attackPhase)) :
    LongLocalStageRow
      ring F C hgood
        (.advance targetPhase attackPhase) := by
  refine And.intro ?_ ?_
  · exact
      longAdvance_children_legit
        hSealed ring F hb hab
        C hgood targetPhase attackPhase hlegit
  · change
      n +
          (List.ofFn (fun e : Fin n =>
            attemptNodePotLong
              (longRawPhiCorrected ring F)
              ((longAttemptKernel ring F).step
                (.live C hgood
                  (.advance targetPhase attackPhase)) e))).sum <=
        n * longRawPhiCorrected ring F
          (.live C hgood
            (.advance targetPhase attackPhase))
    exact
      longAdvance_bellman_corrected
        hSealed ring F hb hab
        C hgood targetPhase attackPhase hlegit

/-! ## Requested residual -/

theorem longAdvancePostCarrierResidual_proved :
    LongAdvancePostCarrierResidual := by
  unfold LongAdvancePostCarrierResidual
  intro hSealed n ring C0 F hb hab
  intro s carrier C hgoodC targetPhase attackPhase
  intro hgoodS hfirst hafter

  have hinv :=
    longAdvance_after_path
      hSealed ring F hb hab
      s hgoodS carrier
      (.live C hgoodC
        (.advance targetPhase attackPhase))
      hfirst hafter
  have hlegit :
      longStageLegit F C
        (.advance targetPhase attackPhase) := by
    change
      longStageLegit F C
        (.advance targetPhase attackPhase) at hinv
    exact hinv

  refine And.intro ?_ ?_
  · change
      longStageLegit F C
        (.advance targetPhase attackPhase)
    exact hlegit
  · refine And.intro ?_ ?_
    · exact
        longAdvance_children_cut
          ring F C hgoodC
          targetPhase attackPhase
    · change
        LongLocalStageRow
          ring F C hgoodC
            (.advance targetPhase attackPhase)
      exact
        longAdvance_local_row
          hSealed ring F hb hab
          C hgoodC targetPhase attackPhase hlegit

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.longAdvancePostCarrierResidual_proved
