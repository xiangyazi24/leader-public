import Leader.PPL.Elim.AttemptCostLongLive

/-!
# LD(736): long-attempt one-letter splice

Truth audit: LongStageSingleInteractionSpec is consistent with the literal
longAttemptKernel on every legitimate stage.

No concrete counterexample was found.  In particular:

* targetCR / attackerCR have the physical strict service guaranteed by the
  corrected CR rows;
* liveWait / advance / recovery have the expected one-service debt;
* race / incident use the two distinct L_j/R_j scheduler letters;
* retained is dominated by the controlled retained Bellman row plus the
  common recovery reserve.

The only bounded-round proof obligations left below are two stage-row
packages.  They are deliberately smaller than LongStageSingleInteractionSpec:
all start classification, reachable-domain reduction, cap removal, paper
budget arithmetic, and final Bellman assembly are proved here.

The first package is the two CR rows.  Its subtle point is that longStep's
private attemptCRNextMode is chosen from the nonincrease half of
crRankStep_proved.  At the required edge the literal CR row is strict, but the
proof must connect that strict physical classification to the exact chosen
witness.

The second package is the six post-CR rows.  Its intended discharge is exactly
the already-proved machinery SealedStepSpec /
nextSectorPhase for liveWait, advance, and recovery; the two predictable
L_j/R_j exceptions for race and incident; and controlRetainedBellman
(controlRowSpec_proved / retainedTrial_cost_nr) for retained.  The raw
Ready-time R_j branch is recovery, while the controlled row redirects R_j to
L_j, so the common recovery reserve pays that one mismatch.
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-! ## 1. Public mirrors of the private long-start CR choices -/

private theorem longStep_notEndpointA
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ¬ EndpointDeleted F.A D := by
  intro h
  exact hgood.2.1 (endpointA_deleted_tagged F D h)

private theorem longStep_notEndpointB
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ¬ EndpointDeleted F.B D := by
  intro h
  exact hgood.2.1 (endpointB_deleted_tagged F D h)

private noncomputable def longStepCRInitMode
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

private theorem longStepCRInitMode_spec
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n)
    (hPB : PPL.Elim.PB ring D)
    (halive : ¬ EndpointDeleted A D)
    (hclean : ¬ CleanReady A D) :
    And
      (CRModeHolds A D
        (longStepCRInitMode ring A D hPB halive hclean))
      (crRank A
          (longStepCRInitMode ring A D hPB halive hclean) ≤
        3 * A.gap) := by
  unfold longStepCRInitMode
  exact
    Classical.choose_spec
      (crRankInit ring A D hPB
        (by
          intro hdone
          rcases hdone with hdel | hready
          · exact halive hdel
          · exact hclean hready))

private noncomputable def longStepAfterTargetStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    LongStage := by
  classical
  if hA : CleanReady F.A D then
    exact .liveWait .ready .ready
  else
    exact .attackerCR .ready
      (longStepCRInitMode
        ring F.A D hgood.1
        (longStep_notEndpointA F D hgood) hA)

private noncomputable def longStepInitialStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    LongStage := by
  classical
  if hB : CleanReady F.B D then
    exact longStepAfterTargetStage ring F D hgood
  else
    exact .targetCR
      (longStepCRInitMode
        ring F.B D hgood.1
        (longStep_notEndpointB F D hgood) hB)

private noncomputable def longStepStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) :
    LongAttemptState ring F := by
  classical
  if hgood : AttemptGood ring F D then
    exact .live D hgood
      (longStepInitialStage ring F D hgood)
  else
    exact .junk D

private theorem longStart_eq_longStepStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) :
    (longAttemptKernel ring F).start D =
      longStepStart ring F D := by
  rfl

private theorem longPhaseReady_of_interior_clean
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n)
    (hInterior : CRInteriorFollowers A C)
    (hclean : CleanReady A C) :
    PhaseHolds A C .ready := by
  exact And.intro hInterior hclean

private theorem longAfterTargetStage_legit
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D)
    (hBready : PhaseHolds F.B D .ready) :
    longStageLegit F D
      (longStepAfterTargetStage ring F D hgood) := by
  classical
  by_cases hA : CleanReady F.A D
  · have hAready :
        PhaseHolds F.A D .ready :=
      longPhaseReady_of_interior_clean
        F.A D hgood.2.2.1 hA
    simpa [longStepAfterTargetStage, hA,
      longStageLegit] using
      (And.intro hBready
        (And.intro hAready True.intro))
  · have hinit :=
      longStepCRInitMode_spec
        ring F.A D hgood.1
        (longStep_notEndpointA F D hgood) hA
    simpa [longStepAfterTargetStage, hA,
      longStageLegit] using
      (And.intro hBready hinit.1)

private theorem longInitialStage_legit
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    longStageLegit F D
      (longStepInitialStage ring F D hgood) := by
  classical
  by_cases hB : CleanReady F.B D
  · have hBready :
        PhaseHolds F.B D .ready :=
      longPhaseReady_of_interior_clean
        F.B D hgood.2.2.2 hB
    simpa [longStepInitialStage, hB] using
      longAfterTargetStage_legit
        ring F D hgood hBready
  · have hinit :=
      longStepCRInitMode_spec
        ring F.B D hgood.1
        (longStep_notEndpointB F D hgood) hB
    simpa [longStepInitialStage, hB,
      longStageLegit] using hinit.1

private def longSemanticGood
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F → Prop
  | .junk _ => False
  | .live C _ stage => longStageLegit F C stage

private theorem longLiveGood_semantic
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (ha : longLiveGood ring F a) :
    longSemanticGood F a := by
  cases a with
  | junk C =>
      rcases ha with hstart | hsemantic
      · rcases hstart with ⟨s, hs, hEq⟩
        rw [longStart_eq_longStepStart] at hEq
        classical
        simp only [longStepStart, dif_pos hs] at hEq
        cases hEq
      · exact hsemantic
  | live C hgood stage =>
      rcases ha with hstart | hsemantic
      · rcases hstart with ⟨s, hs, hEq⟩
        rw [longStart_eq_longStepStart] at hEq
        classical
        simp only [longStepStart, dif_pos hs] at hEq
        cases hEq
        exact longInitialStage_legit ring F _ hs
      · exact hsemantic

/-! ## 2. Every legitimate raw stage reserve is below the paper cap -/

private theorem phaseDebt_le_of_holds_long
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (A : SectorFrame ring C0)
    (C : Config n) (ph : SectorPhase)
    (h : PhaseHolds A C ph) :
    phaseDebt A.gap ph ≤ 2 * A.gap - 1 := by
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

private def longNoLive : SectorPhase → Prop
  | .live _ => False
  | _ => True

private theorem longLaunchPhaseUnits_le_four_gap
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (A : SectorFrame ring C0)
    (C : Config n) (ph : SectorPhase)
    (h : PhaseHolds A C ph)
    (hnolive : longNoLive ph) :
    longLaunchPhaseUnits A.gap ph ≤ 4 * A.gap := by
  cases ph with
  | ready =>
      simp [longLaunchPhaseUnits]
      omega
  | dummy p =>
      have hp : p < A.gap := h.2.1.1
      simp [longLaunchPhaseUnits, phaseDebt]
      omega
  | live p =>
      exact False.elim hnolive
  | ret q =>
      have hq : q < A.gap := h.2.2.1
      simp [longLaunchPhaseUnits]
      omega

private theorem longStageUnits_le_paper
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (hab : 2 * F.b + 1 ≤ F.a)
    (C : Config n) (stage : LongStage)
    (h : longStageLegit F C stage) :
    longStageUnits F stage ≤
      longAttemptPaperBudgetLong F := by
  rw [← longTargetCRReserveUnits_eq_paper F]
  cases stage with
  | targetCR mode =>
      have hv :=
        crModeHolds_valid F.B C mode h
      have hr :=
        crRank_le_three_gap F.B mode hv
      rw [F.B_gap] at hr
      simp only [longStageUnits]
      unfold longTargetCRReserveUnits
      omega
  | attackerCR targetPhase mode =>
      have hm : CRModeHolds F.A C mode := h.2
      have hv :=
        crModeHolds_valid F.A C mode hm
      have hr :=
        crRank_le_three_gap F.A mode hv
      rw [F.A_gap] at hr
      simp only [longStageUnits]
      unfold longTargetCRReserveUnits
        longAttackerCRReserveUnits
      omega
  | liveWait targetPhase attackPhase =>
      have hA : PhaseHolds F.A C attackPhase :=
        h.2.1
      have hnolive : longNoLive attackPhase := by
        have h22 := h.2.2
        cases attackPhase <;> first | exact trivial | exact h22
      have hl :=
        longLaunchPhaseUnits_le_four_gap
          F.A C attackPhase hA hnolive
      rw [F.A_gap] at hl
      simp only [longStageUnits]
      unfold longTargetCRReserveUnits
        longAttackerCRReserveUnits
        longLaunchReserveUnits
      omega
  | advance targetPhase attackPhase =>
      rcases h.2.2 with
        ⟨p, hphase, hp0, hpcut⟩
      subst attackPhase
      simp only [longStageUnits,
        longAdvancePhaseUnits]
      unfold longTargetCRReserveUnits
        longAttackerCRReserveUnits
        longLaunchReserveUnits
        longAdvanceReserveUnits
        longRaceReserveUnits
        longIncidentReserveUnits
        longRetainedReserveUnits
        longRecoveryReserveUnits
      omega
  | race targetPhase attackPhase =>
      have hd :=
        phaseDebt_le_of_holds_long
          F.B C targetPhase h.1
      rw [F.B_gap] at hd
      simp only [longStageUnits]
      unfold longTargetCRReserveUnits
        longAttackerCRReserveUnits
        longLaunchReserveUnits
        longAdvanceReserveUnits
        longRaceReserveUnits
      omega
  | incident attackPhase =>
      simp only [longStageUnits]
      unfold longTargetCRReserveUnits
        longAttackerCRReserveUnits
        longLaunchReserveUnits
        longAdvanceReserveUnits
        longRaceReserveUnits
      omega
  | retained targetPhase attackPhase =>
      rcases h.2.2.1 with
        ⟨p, hphase, hrem⟩
      subst attackPhase
      simp only [longStageUnits,
        longRetainedPhaseUnits]
      unfold longTargetCRReserveUnits
        longAttackerCRReserveUnits
        longLaunchReserveUnits
        longAdvanceReserveUnits
        longRaceReserveUnits
        longIncidentReserveUnits
        longRetainedReserveUnits
      omega
  | recovery targetPhase attackPhase =>
      have hd :
          phaseDebt F.b targetPhase ≤
            longRecoveryReserveUnits F :=
        h.2.2
      simp only [longStageUnits]
      unfold longTargetCRReserveUnits
        longAttackerCRReserveUnits
        longLaunchReserveUnits
        longAdvanceReserveUnits
        longRaceReserveUnits
        longIncidentReserveUnits
        longRetainedReserveUnits
      omega
  | stuck =>
      exact False.elim h

/-! ## 3. Remove the entry cap on semantic stages -/

private def longRawPhi
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F → Nat
  | .junk _ => 0
  | .live _ _ stage =>
      n * longStageUnits F stage

private theorem longLivePhi_le_rawPhi
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F) :
    longLivePhi ring F a ≤
      longRawPhi ring F a := by
  cases a with
  | junk C =>
      simp [longLivePhi, longRawPhi]
  | live C hgood stage =>
      simp only [longLivePhi, longRawPhi]
      exact
        Nat.mul_le_mul_left n
          (Nat.min_le_left _ _)

private theorem longLivePhi_eq_rawPhi_of_legit
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (hab : 2 * F.b + 1 ≤ F.a)
    (C : Config n) (hgood : AttemptGood ring F C)
    (stage : LongStage)
    (hlegit : longStageLegit F C stage) :
    longLivePhi ring F
        (.live C hgood stage) =
      longRawPhi ring F
        (.live C hgood stage) := by
  have hcap :=
    longStageUnits_le_paper
      F hb hab C stage hlegit
  simp [longLivePhi, longRawPhi,
    Nat.min_eq_left hcap]

private theorem attemptNodePotLong_mono_local
    {A S : Type}
    (Phi Psi : A → Nat)
    (h : ∀ a, Phi a ≤ Psi a)
    (z : AttemptNode A S) :
    attemptNodePotLong Phi z ≤
      attemptNodePotLong Psi z := by
  cases z with
  | success =>
      exact Nat.le_refl _
  | retry s =>
      exact Nat.le_refl _
  | active a =>
      exact h a

/-! ## 4. Exact per-stage row interface -/

/--
One stage-local row: active children stay in the semantic stage domain and the
uncapped scheduler-scaled potential satisfies the one-letter Bellman row.
-/
def LongLocalStageRow
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (stage : LongStage) : Prop :=
  And
    (∀ e a',
      (longAttemptKernel ring F).step
          (.live C hgood stage) e = .active a' →
      match a' with
      | .junk _ => False
      | .live D _ stage' =>
          longStageLegit F D stage')
    (n +
        (List.ofFn (fun e : Fin n =>
          attemptNodePotLong
            (longRawPhi ring F)
            ((longAttemptKernel ring F).step
              (.live C hgood stage) e))).sum ≤
      n *
        longRawPhi ring F
          (.live C hgood stage))

/--
Residual row package 1: the two CR stages.

The required-edge issue is deliberately visible here.  The concrete child
mode is the private Classical.choose made from the nonincrease half of
crRankStep_proved.  The literal CR stage proofs do make the required physical
letter strict; this package is the small theorem that transports that fact to
the exact chosen child while also checking the CR-done handoff reserve.
-/
def LongCRStageRowsSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 ≤ F.b →
      2 * F.b + 1 ≤ F.a →
      And
        (∀ C (hgood : AttemptGood ring F C)
            (mode : CRMode),
          longStageLegit F C (.targetCR mode) →
          LongLocalStageRow
            ring F C hgood (.targetCR mode))
        (∀ C (hgood : AttemptGood ring F C)
            (targetPhase : SectorPhase)
            (mode : CRMode),
          longStageLegit F C
              (.attackerCR targetPhase mode) →
          LongLocalStageRow
            ring F C hgood
              (.attackerCR targetPhase mode))

/--
Residual row package 2: the six post-CR stages.

The six clauses are independent stage rows, grouped into one Prop only to stay
within the bounded-round two-residual limit.
-/
def LongSealedControlStageRowsSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 ≤ F.b →
      2 * F.b + 1 ≤ F.a →
      And
        (∀ C (hgood : AttemptGood ring F C)
            (targetPhase attackPhase : SectorPhase),
          longStageLegit F C
              (.liveWait targetPhase attackPhase) →
          LongLocalStageRow
            ring F C hgood
              (.liveWait targetPhase attackPhase))
        (And
          (∀ C (hgood : AttemptGood ring F C)
              (targetPhase attackPhase : SectorPhase),
            longStageLegit F C
                (.advance targetPhase attackPhase) →
            LongLocalStageRow
              ring F C hgood
                (.advance targetPhase attackPhase))
          (And
            (∀ C (hgood : AttemptGood ring F C)
                (targetPhase attackPhase : SectorPhase),
              longStageLegit F C
                  (.race targetPhase attackPhase) →
              LongLocalStageRow
                ring F C hgood
                  (.race targetPhase attackPhase))
            (And
              (∀ C (hgood : AttemptGood ring F C)
                  (attackPhase : SectorPhase),
                longStageLegit F C
                    (.incident attackPhase) →
                LongLocalStageRow
                  ring F C hgood
                    (.incident attackPhase))
              (And
                (∀ C (hgood : AttemptGood ring F C)
                    (targetPhase attackPhase : SectorPhase),
                  longStageLegit F C
                      (.retained targetPhase attackPhase) →
                  LongLocalStageRow
                    ring F C hgood
                      (.retained targetPhase attackPhase))
                (∀ C (hgood : AttemptGood ring F C)
                    (targetPhase attackPhase : SectorPhase),
                  longStageLegit F C
                      (.recovery targetPhase attackPhase) →
                  LongLocalStageRow
                    ring F C hgood
                      (.recovery targetPhase attackPhase))))))

/-! ## 5. Bellman assembly from the two bounded stage-row packages -/

private theorem longLocalRow_for_stage
    (hCR : LongCRStageRowsSpec)
    (hPost : LongSealedControlStageRowsSpec)
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 ≤ F.b)
    (hab : 2 * F.b + 1 ≤ F.a)
    (C : Config n) (hgood : AttemptGood ring F C)
    (stage : LongStage)
    (hlegit : longStageLegit F C stage) :
    LongLocalStageRow ring F C hgood stage := by
  have hcr :=
    hCR hSealed ring F hb hab
  have hpost :=
    hPost hSealed ring F hb hab
  cases stage with
  | targetCR mode =>
      exact hcr.1 C hgood mode hlegit
  | attackerCR targetPhase mode =>
      exact hcr.2 C hgood targetPhase mode hlegit
  | liveWait targetPhase attackPhase =>
      exact
        hpost.1 C hgood
          targetPhase attackPhase hlegit
  | advance targetPhase attackPhase =>
      exact
        hpost.2.1 C hgood
          targetPhase attackPhase hlegit
  | race targetPhase attackPhase =>
      exact
        hpost.2.2.1 C hgood
          targetPhase attackPhase hlegit
  | incident attackPhase =>
      exact
        hpost.2.2.2.1 C hgood
          attackPhase hlegit
  | retained targetPhase attackPhase =>
      exact
        hpost.2.2.2.2.1 C hgood
          targetPhase attackPhase hlegit
  | recovery targetPhase attackPhase =>
      exact
        hpost.2.2.2.2.2 C hgood
          targetPhase attackPhase hlegit
  | stuck =>
      exact False.elim hlegit

/--
Conditional close of the exact requested single-interaction theorem.

Only LongCRStageRowsSpec and LongSealedControlStageRowsSpec remain.
-/
theorem longStageSingleInteraction
    (hCR : LongCRStageRowsSpec)
    (hPost : LongSealedControlStageRowsSpec) :
    LongStageSingleInteractionSpec := by
  unfold LongStageSingleInteractionSpec
  intro hSealed n ring C0 F hb hab
  refine And.intro ?_ ?_
  · intro a ha e a' hstep
    have hsemantic :=
      longLiveGood_semantic ring F a ha
    cases a with
    | junk C =>
        exact False.elim hsemantic
    | live C hgood stage =>
        have hlocal :=
          longLocalRow_for_stage
            hCR hPost hSealed
            ring F hb hab
            C hgood stage hsemantic
        exact Or.inr (hlocal.1 e a' hstep)
  · intro a ha
    have hsemantic :=
      longLiveGood_semantic ring F a ha
    cases a with
    | junk C =>
        exact False.elim hsemantic
    | live C hgood stage =>
        have hlocal :=
          longLocalRow_for_stage
            hCR hPost hSealed
            ring F hb hab
            C hgood stage hsemantic
        have hpoint :
            ∀ e : Fin n,
              attemptNodePotLong
                  (longLivePhi ring F)
                  ((longAttemptKernel ring F).step
                    (.live C hgood stage) e) ≤
                attemptNodePotLong
                  (longRawPhi ring F)
                  ((longAttemptKernel ring F).step
                    (.live C hgood stage) e) := by
          intro e
          exact
            attemptNodePotLong_mono_local
              (longLivePhi ring F)
              (longRawPhi ring F)
              (longLivePhi_le_rawPhi ring F)
              ((longAttemptKernel ring F).step
                (.live C hgood stage) e)
        have hsum :=
          FiniteUniformStoppingTree.ofFn_sum_le
            (fun e : Fin n =>
              attemptNodePotLong
                (longLivePhi ring F)
                ((longAttemptKernel ring F).step
                  (.live C hgood stage) e))
            (fun e : Fin n =>
              attemptNodePotLong
                (longRawPhi ring F)
                ((longAttemptKernel ring F).step
                  (.live C hgood stage) e))
            hpoint
        have hparent :=
          longLivePhi_eq_rawPhi_of_legit
            ring F hb hab C hgood stage hsemantic
        calc
          n +
              (List.ofFn (fun e : Fin n =>
                attemptNodePotLong
                  (longLivePhi ring F)
                  ((longAttemptKernel ring F).step
                    (.live C hgood stage) e))).sum
              ≤
            n +
              (List.ofFn (fun e : Fin n =>
                attemptNodePotLong
                  (longRawPhi ring F)
                  ((longAttemptKernel ring F).step
                    (.live C hgood stage) e))).sum :=
            Nat.add_le_add_left hsum n
          _ ≤
            n *
              longRawPhi ring F
                (.live C hgood stage) :=
            hlocal.2
          _ =
            n *
              longLivePhi ring F
                (.live C hgood stage) := by
            rw [hparent]

/--
Conditional close of LongAttemptCostSpec from exactly the same two residual
row packages.
-/
theorem longAttemptCostSpec_closed
    (hCR : LongCRStageRowsSpec)
    (hPost : LongSealedControlStageRowsSpec) :
    LongAttemptCostSpec :=
  longAttemptCostSpec_proved
    (longStageSingleInteraction hCR hPost)

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.longStep_notEndpointA
#print axioms PPL.Convergence.LDLocal.longStep_notEndpointB
#print axioms PPL.Convergence.LDLocal.longStepCRInitMode_spec
#print axioms PPL.Convergence.LDLocal.longStart_eq_longStepStart
#print axioms PPL.Convergence.LDLocal.longPhaseReady_of_interior_clean
#print axioms PPL.Convergence.LDLocal.longAfterTargetStage_legit
#print axioms PPL.Convergence.LDLocal.longInitialStage_legit
#print axioms PPL.Convergence.LDLocal.longLiveGood_semantic
#print axioms PPL.Convergence.LDLocal.phaseDebt_le_of_holds_long
#print axioms PPL.Convergence.LDLocal.longLaunchPhaseUnits_le_four_gap
#print axioms PPL.Convergence.LDLocal.longStageUnits_le_paper
#print axioms PPL.Convergence.LDLocal.longLivePhi_le_rawPhi
#print axioms PPL.Convergence.LDLocal.longLivePhi_eq_rawPhi_of_legit
#print axioms PPL.Convergence.LDLocal.attemptNodePotLong_mono_local
#print axioms PPL.Convergence.LDLocal.longLocalRow_for_stage
#print axioms PPL.Convergence.LDLocal.longStageSingleInteraction
#print axioms PPL.Convergence.LDLocal.longAttemptCostSpec_closed
