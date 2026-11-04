import Leader.PPL.Elim.AttemptCostLongStep


namespace PPL.Convergence.LDLocal


set_option autoImplicit false
set_option Elab.async false


open FiniteUniformStoppingTree


/-!
# Corrected long sealed/control rows

The old LongSealedControlStageRowsSpec quantified over every semantic post-CR
stage.  That includes the synthetic race target .live 0 refuted by the
long-sealed counterexample.

The corrected carrier is path based.  Before the first post-CR cut, CR rows
are supplied by LongCRStageRowsSpec.  At the first post-CR active node we
record a first-cut witness, and thereafter every active node carries a path
from that witness.  The sealed/control package is required only on those
descendants.

This is the same first-cut discipline as LongAttemptFirstHandoffGoodRowsA: the
quantifier carries the actual good start and a first-cut provenance witness,
rather than merely asserting that an arbitrary raw constructor looks
semantically plausible.
-/


/-! ## 1. Public mirrors of the literal good start -/


private theorem longCorrected_notEndpointA
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    Not (EndpointDeleted F.A D) := by
  intro h
  exact hgood.2.1 (endpointA_deleted_tagged F D h)


private theorem longCorrected_notEndpointB
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    Not (EndpointDeleted F.B D) := by
  intro h
  exact hgood.2.1 (endpointB_deleted_tagged F D h)


private noncomputable def longCorrectedCRInitMode
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


private theorem longCorrectedCRInitMode_spec
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n)
    (hPB : PPL.Elim.PB ring D)
    (halive : Not (EndpointDeleted A D))
    (hclean : Not (CleanReady A D)) :
    And
      (CRModeHolds A D
        (longCorrectedCRInitMode ring A D hPB halive hclean))
      (crRank A
          (longCorrectedCRInitMode ring A D hPB halive hclean) <=
        3 * A.gap) := by
  unfold longCorrectedCRInitMode
  exact
    Classical.choose_spec
      (crRankInit ring A D hPB
        (by
          intro hdone
          rcases hdone with hdel | hready
          · exact halive hdel
          · exact hclean hready))


private noncomputable def longCorrectedAfterTargetStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : LongStage := by
  classical
  if hA : CleanReady F.A D then
    exact .liveWait .ready .ready
  else
    exact .attackerCR .ready
      (longCorrectedCRInitMode
        ring F.A D hgood.1
        (longCorrected_notEndpointA F D hgood) hA)


private noncomputable def longCorrectedInitialStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) : LongStage := by
  classical
  if hB : CleanReady F.B D then
    exact longCorrectedAfterTargetStage ring F D hgood
  else
    exact .targetCR
      (longCorrectedCRInitMode
        ring F.B D hgood.1
        (longCorrected_notEndpointB F D hgood) hB)


private noncomputable def longCorrectedStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) : LongAttemptState ring F := by
  classical
  if hgood : AttemptGood ring F D then
    exact .live D hgood
      (longCorrectedInitialStage ring F D hgood)
  else
    exact .junk D


private theorem longStart_eq_longCorrectedStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) :
    (longAttemptKernel ring F).start D =
      longCorrectedStart ring F D := by
  rfl


private theorem longCorrectedPhaseReady
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n)
    (hInterior : CRInteriorFollowers A C)
    (hclean : CleanReady A C) :
    PhaseHolds A C .ready := by
  exact And.intro hInterior hclean


private theorem longCorrectedAfterTargetStage_legit
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D)
    (hBready : PhaseHolds F.B D .ready) :
    longStageLegit F D
      (longCorrectedAfterTargetStage ring F D hgood) := by
  classical
  by_cases hA : CleanReady F.A D
  · have hAready :
        PhaseHolds F.A D .ready :=
      longCorrectedPhaseReady
        F.A D hgood.2.2.1 hA
    simpa [longCorrectedAfterTargetStage, hA,
      longStageLegit] using
      (And.intro hBready
        (And.intro hAready True.intro))
  · have hinit :=
      longCorrectedCRInitMode_spec
        ring F.A D hgood.1
        (longCorrected_notEndpointA F D hgood) hA
    simpa [longCorrectedAfterTargetStage, hA,
      longStageLegit] using
      (And.intro hBready hinit.1)


private theorem longCorrectedInitialStage_legit
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    longStageLegit F D
      (longCorrectedInitialStage ring F D hgood) := by
  classical
  by_cases hB : CleanReady F.B D
  · have hBready :
        PhaseHolds F.B D .ready :=
      longCorrectedPhaseReady
        F.B D hgood.2.2.2 hB
    simpa [longCorrectedInitialStage, hB] using
      longCorrectedAfterTargetStage_legit
        ring F D hgood hBready
  · have hinit :=
      longCorrectedCRInitMode_spec
        ring F.B D hgood.1
        (longCorrected_notEndpointB F D hgood) hB
    simpa [longCorrectedInitialStage, hB,
      longStageLegit] using hinit.1


def longSemanticGoodCorrected
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Prop
  | .junk _ => False
  | .live C _ stage => longStageLegit F C stage


private theorem longCorrectedStart_semantic
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    longSemanticGoodCorrected F
      ((longAttemptKernel ring F).start D) := by
  rw [longStart_eq_longCorrectedStart]
  classical
  simp only [longCorrectedStart, dif_pos hgood]
  exact
    longCorrectedInitialStage_legit
      ring F D hgood


/-! ## 2. First post-CR cut carrier -/


def longPostCRCutCorrected
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Bool
  | .junk _ => false
  | .live _ _ stage =>
      match stage with
      | .targetCR _ => false
      | .attackerCR _ _ => false
      | .liveWait _ _ => true
      | .advance _ _ => true
      | .race _ _ => true
      | .incident _ => true
      | .retained _ _ => true
      | .recovery _ _ => true
      | .stuck => false


inductive RetryActiveBeforeCutCorrected
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (cut : A -> Bool) (root : A) : A -> Prop where
  | root (hroot : cut root = false) :
      RetryActiveBeforeCutCorrected K cut root root
  | step {a a' : A} :
      RetryActiveBeforeCutCorrected K cut root a ->
      (e : Fin n) ->
      K.step a e = .active a' ->
      cut a' = false ->
      RetryActiveBeforeCutCorrected K cut root a'


def RetryFirstCutReachableCorrected
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (cut : A -> Bool) (root a : A) : Prop :=
  Or
    (And (a = root) (cut root = true))
    (Exists fun p =>
      And
        (RetryActiveBeforeCutCorrected K cut root p)
        (Exists fun e : Fin n =>
          And (K.step p e = .active a)
            (cut a = true)))


inductive RetryActiveAfterCutCorrected
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (cut : A -> Bool) (root : A) : A -> Prop where
  | root (hroot : cut root = true) :
      RetryActiveAfterCutCorrected K cut root root
  | step {a a' : A} :
      RetryActiveAfterCutCorrected K cut root a ->
      (e : Fin n) ->
      K.step a e = .active a' ->
      cut a' = true ->
      RetryActiveAfterCutCorrected K cut root a'


theorem retryActiveBeforeCutCorrected_cut_false
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n)
    (cut : A -> Bool) (root a : A)
    (h : RetryActiveBeforeCutCorrected K cut root a) :
    cut a = false := by
  cases h with
  | root hroot =>
      exact hroot
  | step h e hstep hcut =>
      exact hcut


/-- Row package for one actual post-CR descendant. -/
def LongReachableLocalStageRowCorrected
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Prop
  | .junk _ => False
  | .live C hgood stage =>
      LongLocalStageRow ring F C hgood stage


/-- Besides the row itself, retain post-cut closure and the semantic witness.
The closure bit is structural for the six post-CR constructors, and makes the
reachable Bellman carrier explicit rather than smuggling it through the
semantic predicate. -/
def LongPostCarrierPackageCorrected
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F) : Prop :=
  And
    (longSemanticGoodCorrected F a)
    (And
      (forall e a',
        (longAttemptKernel ring F).step a e = .active a' ->
        longPostCRCutCorrected F a' = true)
      (LongReachableLocalStageRowCorrected ring F a))


/-- Corrected replacement for LongSealedControlStageRowsSpec.

The six sealed/control rows are requested only after an actual first post-CR
cut of a literal good start, and only along active descendants that remain
after that cut. -/
def LongSealedControlStageRowsSpecCorrected : Prop :=
  forall (hSealed : SealedStepSpec),
    forall {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 <= F.b ->
      2 * F.b + 1 <= F.a ->
      forall s carrier a,
        AttemptGood ring F s ->
        RetryFirstCutReachableCorrected
          (longAttemptKernel ring F)
          (longPostCRCutCorrected F)
          ((longAttemptKernel ring F).start s)
          carrier ->
        RetryActiveAfterCutCorrected
          (longAttemptKernel ring F)
          (longPostCRCutCorrected F)
          carrier a ->
        LongPostCarrierPackageCorrected
          ring F a


/-- Non-vacuity witness: if a literal good start is already CleanReady on both
sectors, that literal start is itself the first post-CR carrier and its own
after-cut descendant. -/
theorem longReadyStart_firstCarrier_corrected
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hPB : PPL.Elim.PB ring C0)
    (hA : CleanReady F.A C0)
    (hB : CleanReady F.B C0) :
    And
      (RetryFirstCutReachableCorrected
        (longAttemptKernel ring F)
        (longPostCRCutCorrected F)
        ((longAttemptKernel ring F).start C0)
        ((longAttemptKernel ring F).start C0))
      (RetryActiveAfterCutCorrected
        (longAttemptKernel ring F)
        (longPostCRCutCorrected F)
        ((longAttemptKernel ring F).start C0)
        ((longAttemptKernel ring F).start C0)) := by
  have hgood :
      AttemptGood ring F C0 :=
    attemptGood_initial ring C0 hPB F
  have hcut :
      longPostCRCutCorrected F
          ((longAttemptKernel ring F).start C0) = true := by
    rw [longStart_eq_longCorrectedStart]
    simp [longCorrectedStart, hgood,
      longCorrectedInitialStage, hB,
      longCorrectedAfterTargetStage, hA,
      longPostCRCutCorrected]
  exact
    And.intro
      (Or.inl (And.intro rfl hcut))
      (RetryActiveAfterCutCorrected.root hcut)


/-! ## 3. Raw stage potential and the paper cap -/


def longRawPhiCorrected
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F -> Nat
  | .junk _ => 0
  | .live _ _ stage =>
      n * longStageUnits F stage


private theorem phaseDebt_le_of_holds_corrected
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


private def longNoLiveCorrected : SectorPhase -> Prop
  | .live _ => False
  | _ => True


private theorem longLaunchPhaseUnits_le_four_gap_corrected
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (A : SectorFrame ring C0)
    (C : Config n) (ph : SectorPhase)
    (h : PhaseHolds A C ph)
    (hnolive : longNoLiveCorrected ph) :
    longLaunchPhaseUnits A.gap ph <= 4 * A.gap := by
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


private theorem longStageUnits_le_paper_corrected
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (C : Config n) (stage : LongStage)
    (h : longStageLegit F C stage) :
    longStageUnits F stage <=
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
      have hnolive : longNoLiveCorrected attackPhase := by
        have h22 := h.2.2
        cases attackPhase <;>
          first | exact trivial | exact h22
      have hl :=
        longLaunchPhaseUnits_le_four_gap_corrected
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
        phaseDebt_le_of_holds_corrected
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
          phaseDebt F.b targetPhase <=
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


private theorem longRawPhiCorrected_le_entry_of_semantic
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (a : LongAttemptState ring F)
    (hsem : longSemanticGoodCorrected F a) :
    longRawPhiCorrected ring F a <=
      n * longAttemptPaperBudgetLong F := by
  cases a with
  | junk C =>
      exact False.elim hsem
  | live C hgood stage =>
      change longStageLegit F C stage at hsem
      change
        n * longStageUnits F stage <=
          n * longAttemptPaperBudgetLong F
      exact
        Nat.mul_le_mul_left n
          (longStageUnits_le_paper_corrected
            F hb hab C stage hsem)


/-! ## 4. Closed carrier used by the generic Bellman theorem -/


inductive LongCostCarrierCorrected
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) :
    LongAttemptState ring F -> Prop where
  | pre {a : LongAttemptState ring F} :
      RetryActiveBeforeCutCorrected
        (longAttemptKernel ring F)
        (longPostCRCutCorrected F)
        ((longAttemptKernel ring F).start s)
        a ->
      longSemanticGoodCorrected F a ->
      LongCostCarrierCorrected ring F s a
  | post {carrier a : LongAttemptState ring F} :
      RetryFirstCutReachableCorrected
        (longAttemptKernel ring F)
        (longPostCRCutCorrected F)
        ((longAttemptKernel ring F).start s)
        carrier ->
      RetryActiveAfterCutCorrected
        (longAttemptKernel ring F)
        (longPostCRCutCorrected F)
        carrier a ->
      LongCostCarrierCorrected ring F s a


private def longCostGoodCorrected
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F) : Prop :=
  Exists fun s : Config n =>
    And
      (AttemptGood ring F s)
      (LongCostCarrierCorrected ring F s a)


private theorem longCostCarrier_start_corrected
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) (hgood : AttemptGood ring F s) :
    LongCostCarrierCorrected ring F s
      ((longAttemptKernel ring F).start s) := by
  have hsem :=
    longCorrectedStart_semantic
      ring F s hgood
  cases hcut :
      longPostCRCutCorrected F
        ((longAttemptKernel ring F).start s) with
  | false =>
      exact
        LongCostCarrierCorrected.pre
          (RetryActiveBeforeCutCorrected.root hcut)
          hsem
  | true =>
      exact
        LongCostCarrierCorrected.post
          (Or.inl (And.intro rfl hcut))
          (RetryActiveAfterCutCorrected.root hcut)


private theorem longPreCarrier_row_corrected
    (hCR : LongCRStageRowsSpec)
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (s : Config n)
    (a : LongAttemptState ring F)
    (hbefore :
      RetryActiveBeforeCutCorrected
        (longAttemptKernel ring F)
        (longPostCRCutCorrected F)
        ((longAttemptKernel ring F).start s)
        a)
    (hsem : longSemanticGoodCorrected F a) :
    LongReachableLocalStageRowCorrected ring F a := by
  have hcut :=
    retryActiveBeforeCutCorrected_cut_false
      (longAttemptKernel ring F)
      (longPostCRCutCorrected F)
      ((longAttemptKernel ring F).start s)
      a hbefore
  cases a with
  | junk C =>
      exact False.elim hsem
  | live C hgood stage =>
      change longStageLegit F C stage at hsem
      change LongLocalStageRow ring F C hgood stage
      have hcr :=
        hCR hSealed ring F hb hab
      cases stage with
      | targetCR mode =>
          exact hcr.1 C hgood mode hsem
      | attackerCR targetPhase mode =>
          exact
            hcr.2 C hgood targetPhase mode hsem
      | liveWait targetPhase attackPhase =>
          simp [longPostCRCutCorrected] at hcut
      | advance targetPhase attackPhase =>
          simp [longPostCRCutCorrected] at hcut
      | race targetPhase attackPhase =>
          simp [longPostCRCutCorrected] at hcut
      | incident attackPhase =>
          simp [longPostCRCutCorrected] at hcut
      | retained targetPhase attackPhase =>
          simp [longPostCRCutCorrected] at hcut
      | recovery targetPhase attackPhase =>
          simp [longPostCRCutCorrected] at hcut
      | stuck =>
          have hf : False := by
            simpa [longStageLegit] using hsem
          exact False.elim hf


private theorem longCostCarrier_semantic_row_corrected
    (hCR : LongCRStageRowsSpec)
    (hPost : LongSealedControlStageRowsSpecCorrected)
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (s : Config n) (hgoodS : AttemptGood ring F s)
    (a : LongAttemptState ring F)
    (ha : LongCostCarrierCorrected ring F s a) :
    And
      (longSemanticGoodCorrected F a)
      (LongReachableLocalStageRowCorrected ring F a) := by
  cases ha with
  | pre hbefore hsem =>
      exact
        And.intro hsem
          (longPreCarrier_row_corrected
            hCR hSealed ring F hb hab
            s a hbefore hsem)
  | post hfirst hafter =>
      have hp :=
        hPost hSealed ring F hb hab
          s _ a hgoodS hfirst hafter
      exact And.intro hp.1 hp.2.2


private theorem longReachableLocalStageRow_child_semantic_corrected
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (hrow : LongReachableLocalStageRowCorrected ring F a)
    (e : Fin n) (a' : LongAttemptState ring F)
    (hstep :
      (longAttemptKernel ring F).step a e = .active a') :
    longSemanticGoodCorrected F a' := by
  cases a with
  | junk C =>
      exact False.elim hrow
  | live C hgood stage =>
      change LongLocalStageRow ring F C hgood stage at hrow
      have hc := hrow.1 e a' hstep
      cases a' with
      | junk D =>
          exact hc
      | live D hgoodD stageD =>
          exact hc


private theorem longCostCarrier_step_corrected
    (hCR : LongCRStageRowsSpec)
    (hPost : LongSealedControlStageRowsSpecCorrected)
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a)
    (s : Config n) (hgoodS : AttemptGood ring F s)
    (a : LongAttemptState ring F)
    (ha : LongCostCarrierCorrected ring F s a)
    (e : Fin n) (a' : LongAttemptState ring F)
    (hstep :
      (longAttemptKernel ring F).step a e = .active a') :
    LongCostCarrierCorrected ring F s a' := by
  cases ha with
  | pre hbefore hsem =>
      have hp :=
        longCostCarrier_semantic_row_corrected
          hCR hPost hSealed ring F hb hab
          s hgoodS a
          (LongCostCarrierCorrected.pre hbefore hsem)
      have hsem' :=
        longReachableLocalStageRow_child_semantic_corrected
          ring F a hp.2 e a' hstep
      cases hcut :
          longPostCRCutCorrected F a' with
      | false =>
          exact
            LongCostCarrierCorrected.pre
              (RetryActiveBeforeCutCorrected.step
                hbefore e hstep hcut)
              hsem'
      | true =>
          have hfirst :
              RetryFirstCutReachableCorrected
                (longAttemptKernel ring F)
                (longPostCRCutCorrected F)
                ((longAttemptKernel ring F).start s)
                a' :=
            Or.inr
              (Exists.intro a
                (And.intro hbefore
                  (Exists.intro e
                    (And.intro hstep hcut))))
          exact
            LongCostCarrierCorrected.post
              hfirst
              (RetryActiveAfterCutCorrected.root hcut)
  | post hfirst hafter =>
      have hp :=
        hPost hSealed ring F hb hab
          s _ a hgoodS hfirst hafter
      have hcut' :=
        hp.2.1 e a' hstep
      exact
        LongCostCarrierCorrected.post
          hfirst
          (RetryActiveAfterCutCorrected.step
            hafter e hstep hcut')


private theorem longReachableLocalStageRow_bellman_corrected
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (a : LongAttemptState ring F)
    (hrow : LongReachableLocalStageRowCorrected ring F a) :
    n +
        (List.ofFn (fun e : Fin n =>
          attemptNodePotLong
            (longRawPhiCorrected ring F)
            ((longAttemptKernel ring F).step a e))).sum <=
      n * longRawPhiCorrected ring F a := by
  cases a with
  | junk C =>
      exact False.elim hrow
  | live C hgood stage =>
      change LongLocalStageRow ring F C hgood stage at hrow
      change
        n +
            (List.ofFn (fun e : Fin n =>
              attemptNodePotLong
                (longRawPhiCorrected ring F)
                ((longAttemptKernel ring F).step
                  (.live C hgood stage) e))).sum <=
          n *
            longRawPhiCorrected ring F
              (.live C hgood stage)
      exact hrow.2


/-! ## 5. Corrected Bellman consumer -/


theorem longStageBellmanCost_corrected
    (hCR : LongCRStageRowsSpec)
    (hPost : LongSealedControlStageRowsSpecCorrected) :
    LongStageBellmanCostSpec := by
  unfold LongStageBellmanCostSpec
  intro hSealed n ring C0 F hb hab
  refine
    ⟨longCostGoodCorrected ring F,
      longRawPhiCorrected ring F,
      ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact
      Exists.intro s
        (And.intro hs
          (longCostCarrier_start_corrected
            ring F s hs))
  · intro a ha e a' hstep
    rcases ha with ⟨s, hs, hcarrier⟩
    exact
      Exists.intro s
        (And.intro hs
          (longCostCarrier_step_corrected
            hCR hPost hSealed
            ring F hb hab
            s hs a hcarrier e a' hstep))
  · intro a ha
    rcases ha with ⟨s, hs, hcarrier⟩
    have hp :=
      longCostCarrier_semantic_row_corrected
        hCR hPost hSealed
        ring F hb hab
        s hs a hcarrier
    exact
      longReachableLocalStageRow_bellman_corrected
        ring F a hp.2
  · intro s hs
    have hsem :=
      longCorrectedStart_semantic
        ring F s hs
    exact
      longRawPhiCorrected_le_entry_of_semantic
        ring F hb hab
        ((longAttemptKernel ring F).start s)
        hsem


theorem longAttemptCostSpec_closed_corrected
    (hCR : LongCRStageRowsSpec)
    (hPost : LongSealedControlStageRowsSpecCorrected) :
    LongAttemptCostSpec :=
  longAttemptCostSpec_of_stageBellman_Long
    (longStageBellmanCost_corrected hCR hPost)


end PPL.Convergence.LDLocal


#print axioms PPL.Convergence.LDLocal.longReadyStart_firstCarrier_corrected
#print axioms PPL.Convergence.LDLocal.longStageBellmanCost_corrected
#print axioms PPL.Convergence.LDLocal.longAttemptCostSpec_closed_corrected

