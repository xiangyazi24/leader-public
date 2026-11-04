import Leader.PPL.Elim.AttemptLongRace

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-! ## Pure sector phase bookkeeping used by the race refinement -/

def LongRacePhaseLegal
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) : SectorPhase -> Prop
  | .ready => True
  | .dummy p => p < A.gap
  | .live p => 0 < p ∧ p < A.gap
  | .ret q => 0 < q ∧ q < A.gap

def longRacePhaseServiceOffset : SectorPhase -> Nat
  | .ready => 0
  | .dummy p => p
  | .live p => p
  | .ret q => q - 1

def longRacePhaseService
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (ph : SectorPhase) : Fin n :=
  advance ring A.left (longRacePhaseServiceOffset ph)

private theorem longRacePhaseLegal_next
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (ph : SectorPhase) (e : Fin n) :
    LongRacePhaseLegal A ph ->
      LongRacePhaseLegal A (nextSectorPhase A ph e) := by
  intro h
  cases ph with
  | ready =>
      by_cases hi : e = sealedIncomingEdge A
      · subst e
        simp [nextSectorPhase, LongRacePhaseLegal, A.gap_pos]
      · by_cases hl : e = A.left
        · rw [hl] at hi ⊢
          by_cases hg : A.gap = 1
          · simp [nextSectorPhase, LongRacePhaseLegal, hi, hg]
          · have hgap0 : 0 < A.gap := A.gap_pos
            have h1 : 1 < A.gap := by omega
            simp [nextSectorPhase, LongRacePhaseLegal, hi, hg, h1]
        · simp [nextSectorPhase, LongRacePhaseLegal, hi, hl]
  | dummy p =>
      change p < A.gap at h
      by_cases hs : e = advance ring A.left p
      · subst e
        by_cases hn : p + 1 < A.gap
        · simp [nextSectorPhase, LongRacePhaseLegal, hn]
        · by_cases hg : A.gap = 1
          · simp [nextSectorPhase, LongRacePhaseLegal, hn, hg]
          · simp [nextSectorPhase, LongRacePhaseLegal, hn, hg]
            omega
      · simp [nextSectorPhase, LongRacePhaseLegal, hs]
        exact h
  | live p =>
      rcases h with ⟨hp0, hp⟩
      by_cases hs : e = advance ring A.left p
      · subst e
        by_cases hn : p + 1 < A.gap
        · simp [nextSectorPhase, LongRacePhaseLegal, hn]
        · by_cases hg : A.gap = 1
          · simp [nextSectorPhase, LongRacePhaseLegal, hn, hg]
          · simp [nextSectorPhase, LongRacePhaseLegal, hn, hg]
            omega
      · simp [nextSectorPhase, LongRacePhaseLegal, hs]
        exact ⟨hp0, hp⟩
  | ret q =>
      rcases h with ⟨hq0, hq⟩
      by_cases hs : e = advance ring A.left (q - 1)
      · subst e
        by_cases hq1 : q = 1
        · simp [nextSectorPhase, LongRacePhaseLegal, hq1]
        · simp [nextSectorPhase, LongRacePhaseLegal, hq1]
          omega
      · simp [nextSectorPhase, LongRacePhaseLegal, hs]
        exact ⟨hq0, hq⟩

private theorem longRacePhaseServiceOffset_lt
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (ph : SectorPhase)
    (h : LongRacePhaseLegal A ph) :
    longRacePhaseServiceOffset ph < A.gap := by
  cases ph with
  | ready =>
      simp [longRacePhaseServiceOffset, A.gap_pos]
  | dummy p =>
      simpa [LongRacePhaseLegal, longRacePhaseServiceOffset] using h
  | live p =>
      exact h.2
  | ret q =>
      have hq := h.2
      simp [longRacePhaseServiceOffset]
      omega

private theorem longRacePhase_next_eq_self_of_ne_service
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (ph : SectorPhase) (e : Fin n)
    (hlegal : LongRacePhaseLegal A ph)
    (hnot : ph ≠ .ready)
    (hne : e ≠ longRacePhaseService A ph) :
    nextSectorPhase A ph e = ph := by
  cases ph with
  | ready =>
      exact False.elim (hnot rfl)
  | dummy p =>
      have hne' : e ≠ advance ring A.left p := by
        simpa [longRacePhaseService,
          longRacePhaseServiceOffset] using hne
      simp [nextSectorPhase, hne']
  | live p =>
      have hne' : e ≠ advance ring A.left p := by
        simpa [longRacePhaseService,
          longRacePhaseServiceOffset] using hne
      simp [nextSectorPhase, hne']
  | ret q =>
      have hne' : e ≠ advance ring A.left (q - 1) := by
        simpa [longRacePhaseService,
          longRacePhaseServiceOffset] using hne
      simp [nextSectorPhase, hne']

private theorem longRacePhaseDebt_service
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (ph : SectorPhase)
    (hlegal : LongRacePhaseLegal A ph)
    (hnot : ph ≠ .ready) :
    phaseDebt A.gap
        (nextSectorPhase A ph (longRacePhaseService A ph)) + 1 =
      phaseDebt A.gap ph := by
  cases ph with
  | ready =>
      exact False.elim (hnot rfl)
  | dummy p =>
      change p < A.gap at hlegal
      by_cases hn : p + 1 < A.gap
      · simp [longRacePhaseService, longRacePhaseServiceOffset,
          nextSectorPhase, phaseDebt, hn]
        omega
      · by_cases hg : A.gap = 1
        · simp [longRacePhaseService, longRacePhaseServiceOffset,
            nextSectorPhase, phaseDebt, hn, hg]
          omega
        · simp [longRacePhaseService, longRacePhaseServiceOffset,
            nextSectorPhase, phaseDebt, hn, hg]
          omega
  | live p =>
      rcases hlegal with ⟨hp0, hp⟩
      by_cases hn : p + 1 < A.gap
      · simp [longRacePhaseService, longRacePhaseServiceOffset,
          nextSectorPhase, phaseDebt, hn]
        omega
      · by_cases hg : A.gap = 1
        · simp [longRacePhaseService, longRacePhaseServiceOffset,
            nextSectorPhase, phaseDebt, hn, hg]
          omega
        · simp [longRacePhaseService, longRacePhaseServiceOffset,
            nextSectorPhase, phaseDebt, hn, hg]
          omega
  | ret q =>
      rcases hlegal with ⟨hq0, hq⟩
      by_cases hq1 : q = 1
      · simp [longRacePhaseService, longRacePhaseServiceOffset,
          nextSectorPhase, phaseDebt, hq1]
      · simp [longRacePhaseService, longRacePhaseServiceOffset,
          nextSectorPhase, phaseDebt, hq1]
        omega

private theorem longRacePhaseDebt_pos
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (ph : SectorPhase)
    (hlegal : LongRacePhaseLegal A ph)
    (hnot : ph ≠ .ready) :
    0 < phaseDebt A.gap ph := by
  cases ph with
  | ready =>
      exact False.elim (hnot rfl)
  | dummy p =>
      change p < A.gap at hlegal
      simp [phaseDebt]
      omega
  | live p =>
      have hp := hlegal.2
      simp [phaseDebt]
      omega
  | ret q =>
      simpa [phaseDebt] using hlegal.1

private theorem longRacePhaseDebt_le
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (ph : SectorPhase)
    (hlegal : LongRacePhaseLegal A ph) :
    phaseDebt A.gap ph <= 2 * A.gap - 1 := by
  cases ph with
  | ready =>
      simp [phaseDebt]
  | dummy p =>
      change p < A.gap at hlegal
      simp [phaseDebt]
      omega
  | live p =>
      have hp := hlegal.2
      simp [phaseDebt]
      omega
  | ret q =>
      have hq := hlegal.2
      simp [phaseDebt]
      omega

/-!
The explicit first-cut invariant.

Before the first progress handoff, the only stage information needed by the
race proof is that every stored B-sector target phase is a legal descendant of
ready.  The target-CR stage has not exposed a target phase yet, and stuck is
harmless.  Race/incident/retained/recovery are excluded: any of those would
already be at or beyond a handoff.
-/
def LongFirstProgressRacePreInvariant
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Prop
  | .junk _ => False
  | .live _ _ stage =>
      match stage with
      | .targetCR _ => True
      | .attackerCR targetPhase _ =>
          LongRacePhaseLegal F.B targetPhase
      | .liveWait targetPhase _ =>
          LongRacePhaseLegal F.B targetPhase
      | .advance targetPhase _ =>
          LongRacePhaseLegal F.B targetPhase
      | .stuck => True
      | .race _ _ => False
      | .incident _ => False
      | .retained _ _ => False
      | .recovery _ _ => False

private noncomputable def raceRefineCRInitMode
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

private noncomputable def raceRefineAfterTargetStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : LongStage := by
  classical
  if hA : CleanReady F.A D then
    exact .liveWait .ready .ready
  else
    exact .attackerCR .ready
      (raceRefineCRInitMode ring F.A D hgood.1
        (by
          intro h
          exact hgood.2.1 (endpointA_deleted_tagged F D h))
        hA)

private noncomputable def raceRefineInitialStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : LongStage := by
  classical
  if hB : CleanReady F.B D then
    exact raceRefineAfterTargetStage ring F D hgood
  else
    exact .targetCR
      (raceRefineCRInitMode ring F.B D hgood.1
        (by
          intro h
          exact hgood.2.1 (endpointB_deleted_tagged F D h))
        hB)

private noncomputable def raceRefineStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) : LongAttemptState ring F := by
  classical
  if hgood : AttemptGood ring F D then
    exact .live D hgood (raceRefineInitialStage ring F D hgood)
  else
    exact .junk D

private theorem longStart_eq_raceRefineStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) :
    (longAttemptKernel ring F).start D =
      raceRefineStart ring F D := by
  rfl

private theorem longFirstProgressRacePreInvariant_start
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s) :
    LongFirstProgressRacePreInvariant ring F
      ((longAttemptKernel ring F).start s) := by
  classical
  rw [longStart_eq_raceRefineStart]
  unfold raceRefineStart
  rw [dif_pos hs]
  unfold raceRefineInitialStage
  by_cases hB : CleanReady F.B s
  · rw [dif_pos hB]
    unfold raceRefineAfterTargetStage
    by_cases hA : CleanReady F.A s
    · rw [dif_pos hA]
      simp [LongFirstProgressRacePreInvariant, LongRacePhaseLegal]
    · rw [dif_neg hA]
      simp [LongFirstProgressRacePreInvariant, LongRacePhaseLegal]
  · rw [dif_neg hB]
    simp [LongFirstProgressRacePreInvariant]

private theorem longTargetCR_child_preInvariant
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (mode : CRMode) (e : Fin n)
    (a' : LongAttemptState ring F)
    (hstep :
      (longAttemptKernel ring F).step
        (.live C hgood (.targetCR mode)) e = .active a') :
    LongFirstProgressRacePreInvariant ring F a' := by
  classical
  simp only [longAttemptKernel] at hstep
  unfold longStep at hstep
  dsimp only at hstep
  by_cases htag : TaggedDeleted F (stepE ring C e)
  · rw [dif_pos htag] at hstep
    cases hstep
  · rw [dif_neg htag] at hstep
    by_cases hmode : CRModeHolds F.B C mode
    · rw [dif_pos hmode] at hstep
      by_cases hdone : CRDone F.B (stepE ring C e)
      · rw [dif_pos hdone] at hstep
        cases hstep
        unfoldLongAfterTargetStage
        by_cases hA : CleanReady F.A (stepE ring C e)
        · rw [dif_pos hA]
          simp [LongFirstProgressRacePreInvariant,
            LongRacePhaseLegal]
        · rw [dif_neg hA]
          simp [LongFirstProgressRacePreInvariant,
            LongRacePhaseLegal]
      · rw [dif_neg hdone] at hstep
        cases hstep
        simp [LongFirstProgressRacePreInvariant]
    · rw [dif_neg hmode] at hstep
      cases hstep
      simp [LongFirstProgressRacePreInvariant]

private theorem longAttackerCR_child_preInvariant
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase : SectorPhase) (mode : CRMode) (e : Fin n)
    (a' : LongAttemptState ring F)
    (hlegal : LongRacePhaseLegal F.B targetPhase)
    (hstep :
      (longAttemptKernel ring F).step
        (.live C hgood (.attackerCR targetPhase mode)) e =
          .active a') :
    LongFirstProgressRacePreInvariant ring F a' := by
  classical
  have hnext :=
    longRacePhaseLegal_next F.B targetPhase e hlegal
  simp only [longAttemptKernel] at hstep
  unfold longStep at hstep
  dsimp only at hstep
  by_cases htag : TaggedDeleted F (stepE ring C e)
  · rw [dif_pos htag] at hstep
    cases hstep
  · rw [dif_neg htag] at hstep
    by_cases hmode : CRModeHolds F.A C mode
    · rw [dif_pos hmode] at hstep
      by_cases hdone : CRDone F.A (stepE ring C e)
      · rw [dif_pos hdone] at hstep
        cases hstep
        simpa [LongFirstProgressRacePreInvariant] using hnext
      · rw [dif_neg hdone] at hstep
        cases hstep
        simpa [LongFirstProgressRacePreInvariant] using hnext
    · rw [dif_neg hmode] at hstep
      cases hstep
      simp [LongFirstProgressRacePreInvariant]

private theorem longFirstProgressRacePreInvariant_step
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (ha : LongFirstProgressRacePreInvariant ring F a)
    (e : Fin n) (a' : LongAttemptState ring F)
    (hstep : (longAttemptKernel ring F).step a e = .active a')
    (hcut : longProgressHandoffCut ring F a' = false) :
    LongFirstProgressRacePreInvariant ring F a' := by
  classical
  cases a with
  | junk C =>
      have hf : False := by
        simpa [LongFirstProgressRacePreInvariant] using ha
      exact hf.elim
  | live C hgood stage =>
      cases stage with
      | targetCR mode =>
          exact
            longTargetCR_child_preInvariant
              ring F C hgood mode e a' hstep
      | attackerCR targetPhase mode =>
          have hlegal :
              LongRacePhaseLegal F.B targetPhase := by
            simpa [LongFirstProgressRacePreInvariant] using ha
          exact
            longAttackerCR_child_preInvariant
              ring F C hgood targetPhase mode e a'
              hlegal hstep
      | liveWait targetPhase attackPhase =>
          have hlegal :
              LongRacePhaseLegal F.B targetPhase := by
            simpa [LongFirstProgressRacePreInvariant] using ha
          have hnext :=
            longRacePhaseLegal_next F.B targetPhase e hlegal
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
              by_cases hnear : F.a - 2 * F.b <= 1
              · rw [dif_pos hnear] at hstep
                cases hstep
                simp [longProgressHandoffCut] at hcut
              · rw [dif_neg hnear] at hstep
                cases hstep
                simpa [LongFirstProgressRacePreInvariant] using hnext
            · rw [dif_neg hfire] at hstep
              cases hstep
              simpa [LongFirstProgressRacePreInvariant] using hnext
      | advance targetPhase attackPhase =>
          have hlegal :
              LongRacePhaseLegal F.B targetPhase := by
            simpa [LongFirstProgressRacePreInvariant] using ha
          have hnext :=
            longRacePhaseLegal_next F.B targetPhase e hlegal
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
              simp [longProgressHandoffCut] at hcut
            · rw [dif_neg hreach] at hstep
              cases hstep
              simpa [LongFirstProgressRacePreInvariant] using hnext
      | race targetPhase attackPhase =>
          have hf : False := by
            simpa [LongFirstProgressRacePreInvariant] using ha
          exact hf.elim
      | incident attackPhase =>
          have hf : False := by
            simpa [LongFirstProgressRacePreInvariant] using ha
          exact hf.elim
      | retained targetPhase attackPhase =>
          have hf : False := by
            simpa [LongFirstProgressRacePreInvariant] using ha
          exact hf.elim
      | recovery targetPhase attackPhase =>
          have hf : False := by
            simpa [LongFirstProgressRacePreInvariant] using ha
          exact hf.elim
      | stuck =>
          simp only [longAttemptKernel] at hstep
          unfold longStep at hstep
          dsimp only at hstep
          by_cases htag : TaggedDeleted F (stepE ring C e)
          · rw [dif_pos htag] at hstep
            cases hstep
          · rw [dif_neg htag] at hstep
            cases hstep
            simp [LongFirstProgressRacePreInvariant]

private theorem longFirstProgressRacePreInvariant_before
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hs : AttemptGood ring F s)
    (a : LongAttemptState ring F)
    (hbefore :
      RetryActiveBeforeCut
        (longAttemptKernel ring F)
        (longProgressHandoffCut ring F)
        ((longAttemptKernel ring F).start s) a) :
    LongFirstProgressRacePreInvariant ring F a := by
  induction hbefore with
  | root hroot =>
      exact longFirstProgressRacePreInvariant_start ring F s hs
  | step h e hstep hcut ih =>
      exact
        longFirstProgressRacePreInvariant_step
          ring F _ ih e _ hstep hcut

private theorem longFirstProgressRace_child_shape
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (a : LongAttemptState ring F)
    (ha : LongFirstProgressRacePreInvariant ring F a)
    (e : Fin n)
    (C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase attackPhase : SectorPhase)
    (hstep :
      (longAttemptKernel ring F).step a e =
        .active (.live C hgood (.race targetPhase attackPhase))) :
    And
      (LongRacePhaseLegal F.B targetPhase)
      (attackPhase = .live (F.a - 2 * F.b)) := by
  classical
  cases a with
  | junk D =>
      have hf : False := by
        simpa [LongFirstProgressRacePreInvariant] using ha
      exact hf.elim
  | live D hgoodD stage =>
      cases stage with
      | targetCR mode =>
          have hi :=
            longTargetCR_child_preInvariant
              ring F D hgoodD mode e
              (.live C hgood (.race targetPhase attackPhase))
              hstep
          have hf : False := by
            simpa [LongFirstProgressRacePreInvariant] using hi
          exact hf.elim
      | attackerCR oldTarget mode =>
          have hlegal :
              LongRacePhaseLegal F.B oldTarget := by
            simpa [LongFirstProgressRacePreInvariant] using ha
          have hi :=
            longAttackerCR_child_preInvariant
              ring F D hgoodD oldTarget mode e
              (.live C hgood (.race targetPhase attackPhase))
              hlegal hstep
          have hf : False := by
            simpa [LongFirstProgressRacePreInvariant] using hi
          exact hf.elim
      | liveWait oldTarget oldAttack =>
          have hlegal :
              LongRacePhaseLegal F.B oldTarget := by
            simpa [LongFirstProgressRacePreInvariant] using ha
          have hnext :=
            longRacePhaseLegal_next F.B oldTarget e hlegal
          simp only [longAttemptKernel] at hstep
          unfold longStep at hstep
          dsimp only at hstep
          by_cases htag : TaggedDeleted F (stepE ring D e)
          · rw [dif_pos htag] at hstep
            cases hstep
          · rw [dif_neg htag] at hstep
            by_cases hfire :
                oldAttack = .ready ∧ e = F.A.left
            · rw [dif_pos hfire] at hstep
              by_cases hnear : F.a - 2 * F.b <= 1
              · rw [dif_pos hnear] at hstep
                have hp0 : F.a - 2 * F.b = 1 := by
                  omega
                have hgap : F.A.gap ≠ 1 := by
                  rw [F.A_gap]
                  omega
                have hA :
                    nextSectorPhase F.A oldAttack e =
                      .live (F.a - 2 * F.b) := by
                  rw [hfire.1, hfire.2, hp0]
                  simp [nextSectorPhase,
                    left_ne_sealedIncomingEdge F.A, hgap]
                cases hstep
                exact And.intro hnext hA
              · rw [dif_neg hnear] at hstep
                cases hstep
            · rw [dif_neg hfire] at hstep
              cases hstep
      | advance oldTarget oldAttack =>
          have hlegal :
              LongRacePhaseLegal F.B oldTarget := by
            simpa [LongFirstProgressRacePreInvariant] using ha
          have hnext :=
            longRacePhaseLegal_next F.B oldTarget e hlegal
          simp only [longAttemptKernel] at hstep
          unfold longStep at hstep
          dsimp only at hstep
          by_cases htag : TaggedDeleted F (stepE ring D e)
          · rw [dif_pos htag] at hstep
            cases hstep
          · rw [dif_neg htag] at hstep
            by_cases hreach :
                nextSectorPhase F.A oldAttack e =
                  .live (F.a - 2 * F.b)
            · rw [dif_pos hreach] at hstep
              cases hstep
              exact And.intro hnext hreach
            · rw [dif_neg hreach] at hstep
              cases hstep
      | race oldTarget oldAttack =>
          have hf : False := by
            simpa [LongFirstProgressRacePreInvariant] using ha
          exact hf.elim
      | incident oldAttack =>
          have hf : False := by
            simpa [LongFirstProgressRacePreInvariant] using ha
          exact hf.elim
      | retained oldTarget oldAttack =>
          have hf : False := by
            simpa [LongFirstProgressRacePreInvariant] using ha
          exact hf.elim
      | recovery oldTarget oldAttack =>
          have hf : False := by
            simpa [LongFirstProgressRacePreInvariant] using ha
          exact hf.elim
      | stuck =>
          simp only [longAttemptKernel] at hstep
          unfold longStep at hstep
          dsimp only at hstep
          by_cases htag : TaggedDeleted F (stepE ring D e)
          · rw [dif_pos htag] at hstep
            cases hstep
          · rw [dif_neg htag] at hstep
            cases hstep

private theorem longFirstProgressRace_shape
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (s C : Config n) (hgood : AttemptGood ring F C)
    (targetPhase attackPhase : SectorPhase)
    (hfirst :
      LongAttemptFirstProgressGood ring F s
        (.live C hgood (.race targetPhase attackPhase))) :
    And
      (LongRacePhaseLegal F.B targetPhase)
      (attackPhase = .live (F.a - 2 * F.b)) := by
  rcases hfirst with ⟨hs, hreach⟩
  rcases hreach with hroot | hstep
  · rcases hroot with ⟨hroot, _⟩
    have hstart :=
      longProgressStart_before ring F s hs
    have hfalse :
        longProgressHandoffCut ring F
            (.live C hgood (.race targetPhase attackPhase)) =
          false := by
      rw [hroot]
      exact hstart.1
    simp [longProgressHandoffCut] at hfalse
  · rcases hstep with ⟨p, hp, e, hpa, _⟩
    have hinv :=
      longFirstProgressRacePreInvariant_before
        ring F s hs p hp
    exact
      longFirstProgressRace_child_shape
        ring F hb hab p hinv e
        C hgood targetPhase attackPhase hpa

/-! ## Counter-race maps and the simulation invariant -/

def longRaceCounterFirst
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (x : LongAttemptState ring F) : Fin n :=
  match x with
  | .live _ _ (.race targetPhase _) =>
      longRacePhaseService F.B targetPhase
  | _ => R_j F

def longRaceCounterSecondRaw
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (x : LongAttemptState ring F) : Fin n :=
  match x with
  | .live _ _ (.race _ (.live p)) =>
      advance ring F.A.left p
  | _ => L_j F

def longRaceCounterSecond
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (x : LongAttemptState ring F) : Fin n :=
  if longRaceCounterFirst ring F x =
      longRaceCounterSecondRaw ring F x then
    ring.leftNeighbor (longRaceCounterFirst ring F x)
  else
    longRaceCounterSecondRaw ring F x

noncomputable def longRaceCounterNext
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (x : LongAttemptState ring F) (e : Fin n) :
    LongAttemptState ring F :=
  match (longAttemptKernel ring F).step x e with
  | .active y => y
  | .success => x
  | .retry _ => x

private theorem longRaceCounterFirst_ne_second
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (x : LongAttemptState ring F) :
    longRaceCounterFirst ring F x ≠
      longRaceCounterSecond ring F x := by
  have hn2 : 2 <= n := by
    have hlt := F.B.gap_lt_n
    rw [F.B_gap] at hlt
    omega
  unfold longRaceCounterSecond
  by_cases h :
      longRaceCounterFirst ring F x =
        longRaceCounterSecondRaw ring F x
  · rw [if_pos h]
    intro heq
    exact
      (leftNeighbor_ne_self_control
        ring hn2 (longRaceCounterFirst ring F x))
        heq.symm
  · rw [if_neg h]
    exact h

private theorem longRaceTargetService_ne_attackService
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (targetPhase : SectorPhase)
    (hlegal : LongRacePhaseLegal F.B targetPhase)
    (p : Nat) (hp : p < F.a) :
    longRacePhaseService F.B targetPhase ≠
      advance ring F.A.left p := by
  have hq0 :=
    longRacePhaseServiceOffset_lt
      F.B targetPhase hlegal
  have hq :
      longRacePhaseServiceOffset targetPhase < F.b := by
    simpa [F.B_gap] using hq0
  have habn : F.a + F.b <= n := by
    rcases F.span with h | h
    · omega
    · omega
  have haN : F.a < n := by
    have h := F.A.gap_lt_n
    simpa [F.A_gap] using h
  have hpN : p < n := Nat.lt_trans hp haN
  have haqN :
      F.a + longRacePhaseServiceOffset targetPhase < n := by
    omega
  have hBstart :
      F.B.left = advance ring F.A.left F.a := by
    calc
      F.B.left = F.j := F.B_left
      _ = F.A.right := F.A_right.symm
      _ = advance ring F.A.left F.A.gap := F.A.right_eq.symm
      _ = advance ring F.A.left F.a := by rw [F.A_gap]
  have hsvc :
      longRacePhaseService F.B targetPhase =
        advance ring F.A.left
          (F.a + longRacePhaseServiceOffset targetPhase) := by
    unfold longRacePhaseService
    rw [hBstart, advance_add]
  intro heq
  rw [hsvc] at heq
  have hoff :=
    advance_injective_below_rows
      ring F.A.left haqN hpN heq
  omega

/--
Simulation invariant for an unresolved literal race.

The attacker starts exactly at a-2b and its abstract second counter is its
literal live-phase displacement.  The target counter is coupled to remaining
phase debt: firstHits + phaseDebt never exceeds 2b-1.  Therefore the target
can become ready no later than the abstract first counter can finish, while
the attack recovery edge is exactly the 2b-th abstract second hit.
-/
def LongRaceCounterSimulationInvariant
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (st :
      PredictableCounterRaceFiniteTree.ActiveRaceState
        (LongAttemptState ring F) (2 * F.b)) : Prop :=
  Exists fun C : Config n =>
    Exists fun hgood : AttemptGood ring F C =>
      Exists fun targetPhase : SectorPhase =>
        Exists fun p : Nat =>
          And
            (st.payload =
              .live C hgood (.race targetPhase (.live p)))
            (And
              (LongRacePhaseLegal F.B targetPhase)
              (And
                (targetPhase ≠ .ready)
                (And
                  (p =
                    (F.a - 2 * F.b) + st.secondHits)
                  (st.firstHits +
                      phaseDebt F.b targetPhase <=
                    2 * F.b - 1))))

noncomputable def longRaceCounterKeepMass
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (x :
      FiniteUniformStoppingTree.StopNode
        (PredictableCounterRaceFiniteTree.ActiveRaceState
          (LongAttemptState ring F) (2 * F.b)))
    (T : Nat) : Nat :=
  treeWeight
    (PredictableCounterRaceFiniteTree.counterRaceStep
      (longRaceCounterFirst ring F)
      (longRaceCounterSecond ring F)
      (longRaceCounterNext ring F))
    (fun y => activeWeight y + successWeight y)
    x T

private theorem longRaceCounterKeepMass_le_pow
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (x :
      FiniteUniformStoppingTree.StopNode
        (PredictableCounterRaceFiniteTree.ActiveRaceState
          (LongAttemptState ring F) (2 * F.b)))
    (T : Nat) :
    longRaceCounterKeepMass ring F x T <= n ^ T := by
  unfold longRaceCounterKeepMass
  calc
    treeWeight
        (PredictableCounterRaceFiniteTree.counterRaceStep
          (longRaceCounterFirst ring F)
          (longRaceCounterSecond ring F)
          (longRaceCounterNext ring F))
        (fun y => activeWeight y + successWeight y)
        x T <=
      treeWeight
        (PredictableCounterRaceFiniteTree.counterRaceStep
          (longRaceCounterFirst ring F)
          (longRaceCounterSecond ring F)
          (longRaceCounterNext ring F))
        oneWeight x T := by
          apply treeWeight_mono
          intro y
          cases y <;>
            simp [activeWeight, successWeight, oneWeight]
    _ = n ^ T :=
      treeWeight_one
        (PredictableCounterRaceFiniteTree.counterRaceStep
          (longRaceCounterFirst ring F)
          (longRaceCounterSecond ring F)
          (longRaceCounterNext ring F))
        x T

private theorem longRaceCounterKeepMass_failure
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (T : Nat) :
    longRaceCounterKeepMass ring F
        (FiniteUniformStoppingTree.StopNode.failure) T = 0 := by
  unfold longRaceCounterKeepMass
  rw [treeWeight_failure]
  simp [activeWeight, successWeight]

private theorem longCutCount_good_eq_pow
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (good bad : A -> Bool)
    (a : A) (hg : good a = true)
    (T : Nat) :
    longCutCount K good bad (.active a) T = n ^ T := by
  cases T <;> simp [longCutCount, hg]

private theorem longCutCount_bad_eq_zero
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (good bad : A -> Bool)
    (a : A)
    (hg : good a = false)
    (hb : bad a = true)
    (T : Nat) :
    longCutCount K good bad (.active a) T = 0 := by
  cases T <;> simp [longCutCount, hg, hb]

private theorem longRaceCounterKeepMass_le_literal
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (st :
      PredictableCounterRaceFiniteTree.ActiveRaceState
        (LongAttemptState ring F) (2 * F.b))
    (hsync : LongRaceCounterSimulationInvariant ring F st) :
    forall T,
      longRaceCounterKeepMass ring F (.active st) T <=
        longRaceMassFrom ring F st.payload T := by
  intro T
  induction T generalizing st with
  | zero =>
      rcases hsync with
        ⟨C, hgood, targetPhase, p,
          hpayload, hlegal, hnot, hp, hcredit⟩
      have hgoodCut :
          longRaceWonCut ring F st.payload = false := by
        rw [hpayload]
        simp [longRaceWonCut, hnot]
      have hbadCut :
          longRecoveryCut ring F st.payload = false := by
        rw [hpayload]
        rfl
      simp [longRaceCounterKeepMass, treeWeight,
        longRaceMassFrom, longCutCount, hgoodCut, hbadCut,
        activeWeight, successWeight]
  | succ T ih =>
      rcases hsync with
        ⟨C, hgood, targetPhase, p,
          hpayload, hlegal, hnot, hp, hcredit⟩

      have hdle : 2 * F.b <= F.a := by omega
      have hp0pos : 0 < F.a - 2 * F.b := by omega
      have hpA : p < F.a := by
        have hs := st.second_lt
        omega
      have hpPos : 0 < p := by omega
      have hattackLegal :
          LongRacePhaseLegal F.A (.live p) := by
        change 0 < p ∧ p < F.A.gap
        rw [F.A_gap]
        exact ⟨hpPos, hpA⟩

      have hgeom :
          longRacePhaseService F.B targetPhase ≠
            advance ring F.A.left p :=
        longRaceTargetService_ne_attackService
          ring F targetPhase hlegal p hpA

      have hfirstEq :
          longRaceCounterFirst ring F st.payload =
            longRacePhaseService F.B targetPhase := by
        rw [hpayload]
        rfl
      have hrawEq :
          longRaceCounterSecondRaw ring F st.payload =
            advance ring F.A.left p := by
        rw [hpayload]
        rfl
      have hsecondEq :
          longRaceCounterSecond ring F st.payload =
            advance ring F.A.left p := by
        unfold longRaceCounterSecond
        rw [hfirstEq, hrawEq]
        rw [if_neg hgeom]

      have hdebtPos0 :=
        longRacePhaseDebt_pos
          F.B targetPhase hlegal hnot
      have hdebtPos :
          0 < phaseDebt F.b targetPhase := by
        simpa [F.B_gap] using hdebtPos0
      have hfirstNot :
          st.firstHits + 1 ≠ 2 * F.b := by
        intro heq
        omega

      have hgoodCut :
          longRaceWonCut ring F st.payload = false := by
        rw [hpayload]
        simp [longRaceWonCut, hnot]
      have hbadCut :
          longRecoveryCut ring F st.payload = false := by
        rw [hpayload]
        rfl

      unfold longRaceCounterKeepMass
      simp only [treeWeight, stepNode]
      simp only [← longRaceCounterKeepMass.eq_1]
      unfold longRaceMassFrom
      simp [longCutCount, hgoodCut, hbadCut]
      apply ofFn_sum_le
      intro e

      by_cases hfirst :
          e = longRacePhaseService F.B targetPhase
      · subst e
        have heFirst :
            longRacePhaseService F.B targetPhase =
              longRaceCounterFirst ring F st.payload :=
          hfirstEq.symm
        have hfirstLt :
            st.firstHits + 1 < 2 * F.b := by
          omega

        by_cases htag :
            TaggedDeleted F
              (stepE ring C
                (longRacePhaseService F.B targetPhase))
        · have hstepSuccess :
              (longAttemptKernel ring F).step st.payload
                  (longRacePhaseService F.B targetPhase) =
                .success := by
            rw [hpayload]
            simp only [longAttemptKernel]
            unfold longStep
            dsimp only
            rw [dif_pos htag]
          rw [hstepSuccess]
          simpa [longCutCount] using
            (longRaceCounterKeepMass_le_pow
              ring F
              (PredictableCounterRaceFiniteTree.counterRaceStep
                (longRaceCounterFirst ring F)
                (longRaceCounterSecond ring F)
                (longRaceCounterNext ring F)
                st
                (longRacePhaseService F.B targetPhase))
              T)
        · have hgoodD :
              AttemptGood ring F
                (stepE ring C
                  (longRacePhaseService F.B targetPhase)) :=
            attemptGood_step ring F C
              (longRacePhaseService F.B targetPhase)
              hgood htag

          have hnohit :
              ¬ Exists fun q =>
                And ((.live p : SectorPhase) = .live q)
                  (And
                    (longRacePhaseService F.B targetPhase =
                      advance ring F.A.left q)
                    (q + 1 = F.a)) := by
            intro h
            rcases h with ⟨q, hq, he, hterm⟩
            have hqp : q = p := by
              cases hq
              rfl
            subst q
            exact hgeom he

          have hattackNext :
              nextSectorPhase F.A (.live p)
                  (longRacePhaseService F.B targetPhase) =
                .live p := by
            exact
              longRacePhase_next_eq_self_of_ne_service
                F.A (.live p)
                (longRacePhaseService F.B targetPhase)
                hattackLegal
                (by intro h; cases h)
                (by
                  simpa [longRacePhaseService,
                    longRacePhaseServiceOffset] using hgeom)

          by_cases htarget :
              nextSectorPhase F.B targetPhase
                  (longRacePhaseService F.B targetPhase) =
                .ready
          · let child : LongAttemptState ring F :=
              .live
                (stepE ring C
                  (longRacePhaseService F.B targetPhase))
                hgoodD
                (.incident (.live p))
            have hstepGood :
                (longAttemptKernel ring F).step st.payload
                    (longRacePhaseService F.B targetPhase) =
                  .active child := by
              rw [hpayload]
              simp only [longAttemptKernel]
              unfold longStep
              dsimp only
              rw [dif_neg htag, dif_neg hnot,
                dif_neg hnohit, dif_pos htarget]
              rw [hattackNext]
            rw [hstepGood]
            have hpow :=
              longRaceCounterKeepMass_le_pow
                ring F
                (PredictableCounterRaceFiniteTree.counterRaceStep
                  (longRaceCounterFirst ring F)
                  (longRaceCounterSecond ring F)
                  (longRaceCounterNext ring F)
                  st
                  (longRacePhaseService F.B targetPhase))
                T
            have hgoodChild :
                longRaceWonCut ring F child = true := by
              simp [child, longRaceWonCut]
            rw [
              longCutCount_good_eq_pow
                (longAttemptKernel ring F)
                (longRaceWonCut ring F)
                (longRecoveryCut ring F)
                child hgoodChild T
            ]
            exact hpow
          · have htargetLegal :=
              longRacePhaseLegal_next
                F.B targetPhase
                (longRacePhaseService F.B targetPhase)
                hlegal
            have hdebt0 :=
              longRacePhaseDebt_service
                F.B targetPhase hlegal hnot
            have hdebt :
                phaseDebt F.b
                    (nextSectorPhase F.B targetPhase
                      (longRacePhaseService F.B targetPhase)) +
                    1 =
                  phaseDebt F.b targetPhase := by
              simpa [F.B_gap] using hdebt0

            let child : LongAttemptState ring F :=
              .live
                (stepE ring C
                  (longRacePhaseService F.B targetPhase))
                hgoodD
                (.race
                  (nextSectorPhase F.B targetPhase
                    (longRacePhaseService F.B targetPhase))
                  (.live p))

            have hstepRace :
                (longAttemptKernel ring F).step st.payload
                    (longRacePhaseService F.B targetPhase) =
                  .active child := by
              rw [hpayload]
              simp only [longAttemptKernel]
              unfold longStep
              dsimp only
              rw [dif_neg htag, dif_neg hnot,
                dif_neg hnohit, dif_neg htarget]
              rw [hattackNext]

            have hnext :
                longRaceCounterNext ring F st.payload
                    (longRacePhaseService F.B targetPhase) =
                  child := by
              unfold longRaceCounterNext
              rw [hstepRace]

            let st' :
                PredictableCounterRaceFiniteTree.ActiveRaceState
                  (LongAttemptState ring F) (2 * F.b) :=
              { payload := child
                firstHits := st.firstHits + 1
                secondHits := st.secondHits
                first_lt := hfirstLt
                second_lt := st.second_lt }

            have hcounter :
                PredictableCounterRaceFiniteTree.counterRaceStep
                    (longRaceCounterFirst ring F)
                    (longRaceCounterSecond ring F)
                    (longRaceCounterNext ring F)
                    st
                    (longRacePhaseService F.B targetPhase) =
                  .active st' := by
              unfold PredictableCounterRaceFiniteTree.counterRaceStep
              rw [dif_pos heFirst, dif_neg hfirstNot, hnext]
              try rfl

            have hsync' :
                LongRaceCounterSimulationInvariant
                  ring F st' := by
              refine
                ⟨stepE ring C
                    (longRacePhaseService F.B targetPhase),
                  hgoodD,
                  nextSectorPhase F.B targetPhase
                    (longRacePhaseService F.B targetPhase),
                  p, rfl,
                  htargetLegal, htarget, ?_, ?_⟩
              · dsimp [st']
                exact hp
              · dsimp [st']
                omega

            rw [hcounter, hstepRace]
            change
              longRaceCounterKeepMass ring F (.active st') T <=
                longRaceMassFrom ring F child T
            exact ih st' hsync'

      · by_cases hsecond :
            e = advance ring F.A.left p
        · subst e
          have heFirst :
              advance ring F.A.left p ≠
                longRaceCounterFirst ring F st.payload := by
            rw [hfirstEq]
            exact hgeom.symm
          have heSecond :
              advance ring F.A.left p =
                longRaceCounterSecond ring F st.payload :=
            hsecondEq.symm

          by_cases htag :
              TaggedDeleted F
                (stepE ring C (advance ring F.A.left p))
          · have hstepSuccess :
                (longAttemptKernel ring F).step st.payload
                    (advance ring F.A.left p) =
                  .success := by
              rw [hpayload]
              simp only [longAttemptKernel]
              unfold longStep
              dsimp only
              rw [dif_pos htag]
            rw [hstepSuccess]
            simpa [longCutCount] using
              (longRaceCounterKeepMass_le_pow
                ring F
                (PredictableCounterRaceFiniteTree.counterRaceStep
                  (longRaceCounterFirst ring F)
                  (longRaceCounterSecond ring F)
                  (longRaceCounterNext ring F)
                  st (advance ring F.A.left p))
                T)
          · have hgoodD :
                AttemptGood ring F
                  (stepE ring C (advance ring F.A.left p)) :=
              attemptGood_step ring F C
                (advance ring F.A.left p) hgood htag

            by_cases hterm :
                st.secondHits + 1 = 2 * F.b
            · have hpterm : p + 1 = F.a := by
                omega
              have hhit :
                  Exists fun q =>
                    And ((.live p : SectorPhase) = .live q)
                      (And
                        (advance ring F.A.left p =
                          advance ring F.A.left q)
                        (q + 1 = F.a)) :=
                ⟨p, rfl, rfl, hpterm⟩
              have hstepBad :
                  (longAttemptKernel ring F).step st.payload
                      (advance ring F.A.left p) =
                    .active
                      (.live
                        (stepE ring C (advance ring F.A.left p))
                        hgoodD
                        (.recovery
                          (nextSectorPhase F.B targetPhase
                            (advance ring F.A.left p))
                          (nextSectorPhase F.A (.live p)
                            (advance ring F.A.left p)))) := by
                rw [hpayload]
                simp only [longAttemptKernel]
                unfold longStep
                dsimp only
                rw [dif_neg htag, dif_neg hnot, dif_pos hhit]
              have hcounter :
                  PredictableCounterRaceFiniteTree.counterRaceStep
                      (longRaceCounterFirst ring F)
                      (longRaceCounterSecond ring F)
                      (longRaceCounterNext ring F)
                      st (advance ring F.A.left p) =
                    .failure := by
                unfold PredictableCounterRaceFiniteTree.counterRaceStep
                rw [dif_neg heFirst, dif_pos heSecond, dif_pos hterm]
              rw [hcounter, hstepBad]
              have hgoodBad :
                  longRaceWonCut ring F
                    (.live
                      (stepE ring C (advance ring F.A.left p))
                      hgoodD
                      (.recovery
                        (nextSectorPhase F.B targetPhase
                          (advance ring F.A.left p))
                        (nextSectorPhase F.A (.live p)
                          (advance ring F.A.left p)))) = false := by
                rfl
              have hbadBad :
                  longRecoveryCut ring F
                    (.live
                      (stepE ring C (advance ring F.A.left p))
                      hgoodD
                      (.recovery
                        (nextSectorPhase F.B targetPhase
                          (advance ring F.A.left p))
                        (nextSectorPhase F.A (.live p)
                          (advance ring F.A.left p)))) = true := by
                rfl
              rw [
                longCutCount_bad_eq_zero
                  (longAttemptKernel ring F)
                  (longRaceWonCut ring F)
                  (longRecoveryCut ring F)
                  (.live
                    (stepE ring C (advance ring F.A.left p))
                    hgoodD
                    (.recovery
                      (nextSectorPhase F.B targetPhase
                        (advance ring F.A.left p))
                      (nextSectorPhase F.A (.live p)
                        (advance ring F.A.left p))))
                  hgoodBad hbadBad T
              ]
              have hz :=
                longRaceCounterKeepMass_failure ring F T
              omega
            · have hsecondLt :
                  st.secondHits + 1 < 2 * F.b := by
                omega
              have hpnext : p + 1 < F.a := by
                omega
              have hnohit :
                  ¬ Exists fun q =>
                    And ((.live p : SectorPhase) = .live q)
                      (And
                        (advance ring F.A.left p =
                          advance ring F.A.left q)
                        (q + 1 = F.a)) := by
                intro h
                rcases h with ⟨q, hq, he, hqa⟩
                have hqp : q = p := by
                  cases hq
                  rfl
                subst q
                exact (by omega : p + 1 ≠ F.a) hqa

              have htargetSame :
                  nextSectorPhase F.B targetPhase
                      (advance ring F.A.left p) =
                    targetPhase := by
                exact
                  longRacePhase_next_eq_self_of_ne_service
                    F.B targetPhase (advance ring F.A.left p)
                    hlegal hnot hgeom.symm
              have htargetNot :
                  nextSectorPhase F.B targetPhase
                      (advance ring F.A.left p) ≠ .ready := by
                rw [htargetSame]
                exact hnot
              have hattackNext :
                  nextSectorPhase F.A (.live p)
                      (advance ring F.A.left p) =
                    .live (p + 1) := by
                simp [nextSectorPhase, F.A_gap, hpnext]

              let child : LongAttemptState ring F :=
                .live
                  (stepE ring C (advance ring F.A.left p))
                  hgoodD
                  (.race targetPhase (.live (p + 1)))

              have hstepRace :
                  (longAttemptKernel ring F).step st.payload
                      (advance ring F.A.left p) =
                    .active child := by
                rw [hpayload]
                simp only [longAttemptKernel]
                unfold longStep
                dsimp only
                rw [dif_neg htag, dif_neg hnot,
                  dif_neg hnohit, dif_neg htargetNot]
                rw [htargetSame, hattackNext]

              have hnext :
                  longRaceCounterNext ring F st.payload
                      (advance ring F.A.left p) =
                    child := by
                unfold longRaceCounterNext
                rw [hstepRace]

              let st' :
                  PredictableCounterRaceFiniteTree.ActiveRaceState
                    (LongAttemptState ring F) (2 * F.b) :=
                { payload := child
                  firstHits := st.firstHits
                  secondHits := st.secondHits + 1
                  first_lt := st.first_lt
                  second_lt := hsecondLt }

              have hcounter :
                  PredictableCounterRaceFiniteTree.counterRaceStep
                      (longRaceCounterFirst ring F)
                      (longRaceCounterSecond ring F)
                      (longRaceCounterNext ring F)
                      st (advance ring F.A.left p) =
                    .active st' := by
                unfold PredictableCounterRaceFiniteTree.counterRaceStep
                rw [dif_neg heFirst, dif_pos heSecond,
                  dif_neg hterm, hnext]
                try rfl

              have hsync' :
                  LongRaceCounterSimulationInvariant
                    ring F st' := by
                refine
                  ⟨stepE ring C (advance ring F.A.left p),
                    hgoodD, targetPhase, p + 1,
                    rfl, hlegal, hnot, ?_, ?_⟩
                · dsimp [st']
                  omega
                · dsimp [st']
                  exact hcredit

              rw [hcounter, hstepRace]
              change
                longRaceCounterKeepMass ring F (.active st') T <=
                  longRaceMassFrom ring F child T
              exact ih st' hsync'

        · have heFirst :
              e ≠ longRaceCounterFirst ring F st.payload := by
            rw [hfirstEq]
            exact hfirst
          have heSecond :
              e ≠ longRaceCounterSecond ring F st.payload := by
            rw [hsecondEq]
            exact hsecond

          by_cases htag : TaggedDeleted F (stepE ring C e)
          · have hstepSuccess :
                (longAttemptKernel ring F).step st.payload e =
                  .success := by
              rw [hpayload]
              simp only [longAttemptKernel]
              unfold longStep
              dsimp only
              rw [dif_pos htag]
            rw [hstepSuccess]
            simpa [longCutCount] using
              (longRaceCounterKeepMass_le_pow
                ring F
                (PredictableCounterRaceFiniteTree.counterRaceStep
                  (longRaceCounterFirst ring F)
                  (longRaceCounterSecond ring F)
                  (longRaceCounterNext ring F)
                  st e)
                T)
          · have hgoodD :
                AttemptGood ring F (stepE ring C e) :=
              attemptGood_step ring F C e hgood htag
            have hnohit :
                ¬ Exists fun q =>
                  And ((.live p : SectorPhase) = .live q)
                    (And
                      (e = advance ring F.A.left q)
                      (q + 1 = F.a)) := by
              intro h
              rcases h with ⟨q, hq, he, hqa⟩
              have hqp : q = p := by
                cases hq
                rfl
              subst q
              exact hsecond he
            have htargetSame :
                nextSectorPhase F.B targetPhase e =
                  targetPhase :=
              longRacePhase_next_eq_self_of_ne_service
                F.B targetPhase e hlegal hnot hfirst
            have htargetNot :
                nextSectorPhase F.B targetPhase e ≠ .ready := by
              rw [htargetSame]
              exact hnot
            have hattackNext :
                nextSectorPhase F.A (.live p) e =
                  .live p := by
              exact
                longRacePhase_next_eq_self_of_ne_service
                  F.A (.live p) e
                  hattackLegal
                  (by intro h; cases h)
                  (by
                    simpa [longRacePhaseService,
                      longRacePhaseServiceOffset] using hsecond)

            let child : LongAttemptState ring F :=
              .live (stepE ring C e) hgoodD
                (.race targetPhase (.live p))

            have hstepRace :
                (longAttemptKernel ring F).step st.payload e =
                  .active child := by
              rw [hpayload]
              simp only [longAttemptKernel]
              unfold longStep
              dsimp only
              rw [dif_neg htag, dif_neg hnot,
                dif_neg hnohit, dif_neg htargetNot]
              rw [htargetSame, hattackNext]

            have hnext :
                longRaceCounterNext ring F st.payload e =
                  child := by
              unfold longRaceCounterNext
              rw [hstepRace]

            let st' :
                PredictableCounterRaceFiniteTree.ActiveRaceState
                  (LongAttemptState ring F) (2 * F.b) :=
              { payload := child
                firstHits := st.firstHits
                secondHits := st.secondHits
                first_lt := st.first_lt
                second_lt := st.second_lt }

            have hcounter :
                PredictableCounterRaceFiniteTree.counterRaceStep
                    (longRaceCounterFirst ring F)
                    (longRaceCounterSecond ring F)
                    (longRaceCounterNext ring F)
                    st e =
                  .active st' := by
              simp [PredictableCounterRaceFiniteTree.counterRaceStep,
                heFirst, heSecond, st', hnext]

            have hsync' :
                LongRaceCounterSimulationInvariant
                  ring F st' := by
              refine
                ⟨stepE ring C e, hgoodD,
                  targetPhase, p, rfl,
                  hlegal, hnot, ?_, ?_⟩
              · dsimp [st']
                exact hp
              · dsimp [st']
                exact hcredit

            rw [hcounter, hstepRace]
            change
              longRaceCounterKeepMass ring F (.active st') T <=
                longRaceMassFrom ring F child T
            exact ih st' hsync'

theorem longFirstProgressRaceCounterRefinement_proved :
    LongFirstProgressRaceCounterRefinement := by
  unfold LongFirstProgressRaceCounterRefinement
  intro _hSealed n ring C0 F hb hab
  intro s C hgood targetPhase attackPhase hfirst

  have hshape :=
    longFirstProgressRace_shape
      ring F hb hab s C hgood
      targetPhase attackPhase hfirst
  rcases hshape with ⟨hlegal, hattack⟩
  subst attackPhase

  have hd : 0 < 2 * F.b := by omega
  let a0 : LongAttemptState ring F :=
    .live C hgood
      (.race targetPhase (.live (F.a - 2 * F.b)))
  let st :
      PredictableCounterRaceFiniteTree.ActiveRaceState
        (LongAttemptState ring F) (2 * F.b) :=
    PredictableCounterRaceFiniteTree.initialState a0 (2 * F.b) hd

  refine ⟨st, rfl, ?_⟩
  refine ⟨longRaceCounterFirst ring F, ?_⟩
  refine ⟨longRaceCounterSecond ring F, ?_⟩
  refine ⟨longRaceCounterNext ring F, ?_, ?_⟩
  · intro x
    exact longRaceCounterFirst_ne_second ring F hb x
  · intro T
    change
      activeCount
          (PredictableCounterRaceFiniteTree.counterRaceStep
            (longRaceCounterFirst ring F)
            (longRaceCounterSecond ring F)
            (longRaceCounterNext ring F))
          (.active st) T +
        successCount
          (PredictableCounterRaceFiniteTree.counterRaceStep
            (longRaceCounterFirst ring F)
            (longRaceCounterSecond ring F)
            (longRaceCounterNext ring F))
          (.active st) T <=
        longRaceMassFrom ring F a0 T

    by_cases hready : targetPhase = .ready
    · have hkeep :=
        longRaceCounterKeepMass_le_pow
          ring F (.active st) T
      unfold longRaceCounterKeepMass at hkeep
      rw [
        treeWeight_add
          (PredictableCounterRaceFiniteTree.counterRaceStep
            (longRaceCounterFirst ring F)
            (longRaceCounterSecond ring F)
            (longRaceCounterNext ring F))
          activeWeight successWeight
          (.active st) T
      ] at hkeep
      change
        activeCount
            (PredictableCounterRaceFiniteTree.counterRaceStep
              (longRaceCounterFirst ring F)
              (longRaceCounterSecond ring F)
              (longRaceCounterNext ring F))
            (.active st) T +
          successCount
            (PredictableCounterRaceFiniteTree.counterRaceStep
              (longRaceCounterFirst ring F)
              (longRaceCounterSecond ring F)
              (longRaceCounterNext ring F))
            (.active st) T <=
          n ^ T at hkeep
      have hmass :
          longRaceMassFrom ring F a0 T = n ^ T := by
        unfold longRaceMassFrom
        cases T <;>
          simp [longCutCount, a0, longRaceWonCut, hready]
      rw [hmass]
      exact hkeep
    · have hdebt0 :=
        longRacePhaseDebt_le
          F.B targetPhase hlegal
      have hdebt :
          phaseDebt F.b targetPhase <= 2 * F.b - 1 := by
        simpa [F.B_gap] using hdebt0
      have hsync :
          LongRaceCounterSimulationInvariant ring F st := by
        refine
          ⟨C, hgood, targetPhase,
            F.a - 2 * F.b, ?_,
            hlegal, hready, ?_, ?_⟩
        · rfl
        · dsimp [st, PredictableCounterRaceFiniteTree.initialState]
        · simpa [st, PredictableCounterRaceFiniteTree.initialState] using
            hdebt

      have hkeep :=
        longRaceCounterKeepMass_le_literal
          ring F hb hab st hsync T
      unfold longRaceCounterKeepMass at hkeep
      rw [
        treeWeight_add
          (PredictableCounterRaceFiniteTree.counterRaceStep
            (longRaceCounterFirst ring F)
            (longRaceCounterSecond ring F)
            (longRaceCounterNext ring F))
          activeWeight successWeight
          (.active st) T
      ] at hkeep
      change
        activeCount
            (PredictableCounterRaceFiniteTree.counterRaceStep
              (longRaceCounterFirst ring F)
              (longRaceCounterSecond ring F)
              (longRaceCounterNext ring F))
            (.active st) T +
          successCount
            (PredictableCounterRaceFiniteTree.counterRaceStep
              (longRaceCounterFirst ring F)
              (longRaceCounterSecond ring F)
              (longRaceCounterNext ring F))
            (.active st) T <=
          longRaceMassFrom ring F a0 T at hkeep
      exact hkeep

theorem longRaceFactor_closed :
    forall (hSealed : SealedStepSpec),
      forall {n : Nat} (ring : DirectedRing n)
        {C0 : Config n} (F : TripleFrame ring C0),
        2 <= F.b ->
        2 * F.b + 1 <= F.a ->
        forall s a,
          LongAttemptFirstProgressGood ring F s a ->
          longProgressHandoffCut ring F a = true ->
          forall T,
            n ^ T <= 2 * longRaceMassFrom ring F a T :=
  longRaceFactor_proved
    longFirstProgressRaceCounterRefinement_proved

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.longFirstProgressRaceCounterRefinement_proved
#print axioms PPL.Convergence.LDLocal.longRaceFactor_closed
