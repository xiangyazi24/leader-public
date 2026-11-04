import Leader.PPL.Elim.AttemptRetryModerateLift
import Leader.PPL.Elim.AttemptCostModerateLive


namespace PPL.Convergence.LDLocal


set_option autoImplicit false
set_option Elab.async false


open FiniteUniformStoppingTree




/-! ## Definitionally identical public-name mirror of the private start helpers -/


private theorem spliceModerate_notEndpointA
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ¬ EndpointDeleted F.A D := by
  intro h
  exact hgood.2.1 (endpointA_deleted_tagged F D h)


private theorem spliceModerate_notEndpointB
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ¬ EndpointDeleted F.B D := by
  intro h
  exact hgood.2.1 (endpointB_deleted_tagged F D h)


private noncomputable def spliceModerateCRInitMode
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


private noncomputable def spliceModerateAfterAttackStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ModerateStage := by
  classical
  if hB : CleanReady F.B D then
    exact .dummyWait .ready .ready
  else
    exact .targetCR .ready
      (spliceModerateCRInitMode
        ring F.B D hgood.1
        (spliceModerate_notEndpointB F D hgood) hB)


private noncomputable def spliceModerateInitialStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ModerateStage := by
  classical
  if hA : CleanReady F.A D then
    exact spliceModerateAfterAttackStage ring F D hgood
  else
    exact .attackCR
      (spliceModerateCRInitMode
        ring F.A D hgood.1
        (spliceModerate_notEndpointA F D hgood) hA)


private noncomputable def spliceModerateStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) :
    ModerateAttemptState ring F := by
  classical
  if hgood : AttemptGood ring F D then
    exact .live D hgood
      (spliceModerateInitialStage ring F D hgood)
  else
    exact .junk D


private theorem moderateStart_eq_spliceModerateStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) :
    (moderateAttemptKernel ring F).start D =
      spliceModerateStart ring F D := by
  rfl


/-! ## Concrete pre-vulnerable and vulnerable relations -/


private def moderatePre
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    ModerateAttemptState ring F → Prop
  | .junk _ => True
  | .live C _ stage =>
      match stage with
      | .attackCR _ => True
      | .targetCR attackPhase _ =>
          PhaseHolds F.A C attackPhase
      | .dummyWait attackPhase targetPhase =>
          And
            (PhaseHolds F.A C attackPhase)
            (PhaseHolds F.B C targetPhase)
      | .vulnerable _ _ => False
      | .recovery _ _ => False
      | .stuck => True


/-- A concrete vulnerable attempt state is related to a File-5 vulnerable
state exactly when the physical configuration and the two stored phase labels
agree.  The File-5 proof fields live in the right-hand witness. -/
private def moderateVulnerableRel
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    ModerateAttemptState ring F →
      VulnerableState F → Prop
  | .junk _, _ => False
  | .live C _ stage, x =>
      match stage with
      | .vulnerable attackPhase targetPhase =>
          And
            (x.cfg = C)
            (And
              (x.attackPhase = attackPhase)
              (x.targetPhase = targetPhase))
      | _ => False


/-! ## Reconstruct the phase proof payload carried propositionally by pre -/


private theorem moderatePhaseAReady
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n)
    (hgood : AttemptGood ring F C)
    (hclean : CleanReady F.A C) :
    PhaseHolds F.A C .ready := by
  exact
    And.intro
      (by
        simpa [SectorInteriorFollowers, CRInteriorFollowers]
          using hgood.2.2.1)
      hclean


private theorem moderatePhaseBReady
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n)
    (hgood : AttemptGood ring F C)
    (hclean : CleanReady F.B C) :
    PhaseHolds F.B C .ready := by
  exact
    And.intro
      (by
        simpa [SectorInteriorFollowers, CRInteriorFollowers]
          using hgood.2.2.2)
      hclean


private theorem moderatePhaseANext
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n)
    (hgood : AttemptGood ring F C)
    (ph : SectorPhase)
    (hph : PhaseHolds F.A C ph)
    (e : Fin n)
    (hnot :
      ¬ TaggedDeleted F (stepE ring C e)) :
    PhaseHolds F.A (stepE ring C e)
      (nextSectorPhase F.A ph e) := by
  have hcur : ¬ EndpointDeleted F.A C := by
    intro hdel
    exact hgood.2.1
      (endpointA_deleted_tagged F C hdel)
  have hnext :
      ¬ EndpointDeleted F.A (stepE ring C e) := by
    intro hdel
    exact hnot
      (endpointA_deleted_tagged
        F (stepE ring C e) hdel)
  rcases
      hSealed ring F.A C ph hph hcur e with
    hdel | hsurvive
  · exact False.elim (hnext hdel)
  · rcases hsurvive with
      ⟨ph', hph', htr⟩
    have heq :
        ph' = nextSectorPhase F.A ph e := by
      simpa [PhaseTransition] using htr
    rw [heq] at hph'
    exact hph'


private theorem moderatePhaseBNext
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n)
    (hgood : AttemptGood ring F C)
    (ph : SectorPhase)
    (hph : PhaseHolds F.B C ph)
    (e : Fin n)
    (hnot :
      ¬ TaggedDeleted F (stepE ring C e)) :
    PhaseHolds F.B (stepE ring C e)
      (nextSectorPhase F.B ph e) := by
  have hcur : ¬ EndpointDeleted F.B C := by
    intro hdel
    exact hgood.2.1
      (endpointB_deleted_tagged F C hdel)
  have hnext :
      ¬ EndpointDeleted F.B (stepE ring C e) := by
    intro hdel
    exact hnot
      (endpointB_deleted_tagged
        F (stepE ring C e) hdel)
  rcases
      hSealed ring F.B C ph hph hcur e with
    hdel | hsurvive
  · exact False.elim (hnext hdel)
  · rcases hsurvive with
      ⟨ph', hph', htr⟩
    have heq :
        ph' = nextSectorPhase F.B ph e := by
      simpa [PhaseTransition] using htr
    rw [heq] at hph'
    exact hph'


private theorem moderateDummyZeroUnshielded
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n)
    (hphase : PhaseHolds F.B C (.dummy 0)) :
    (C F.j).shield = false := by
  have hs :
      (C F.B.left).shield = false :=
    hphase.2.2.1
  simpa [F.B_left] using hs


/-! ## Every concrete start is pre-vulnerable -/


private theorem moderateStart_pre
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : Config n) :
    moderatePre F
      ((moderateAttemptKernel ring F).start s) := by
  classical
  rw [moderateStart_eq_spliceModerateStart]
  by_cases hgood : AttemptGood ring F s
  · simp only [spliceModerateStart, dif_pos hgood]
    by_cases hA : CleanReady F.A s
    · have hAready :=
        moderatePhaseAReady F s hgood hA
      simp only [spliceModerateInitialStage, dif_pos hA]
      by_cases hB : CleanReady F.B s
      · have hBready :=
          moderatePhaseBReady F s hgood hB
        simpa
          [spliceModerateAfterAttackStage,
            hB, moderatePre]
          using And.intro hAready hBready
      · simpa
          [spliceModerateAfterAttackStage,
            hB, moderatePre]
          using hAready
    · simp
        [spliceModerateInitialStage,
          hA, moderatePre]
  · simp
      [spliceModerateStart, hgood, moderatePre]


/-! ## Concrete vulnerable state simulates vulnerableStep -/


private theorem moderateVulnerableSimulation
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    RetryFailureSimulation
      (moderateAttemptKernel ring F)
      (vulnerableStep hSealed F)
      (moderateVulnerableRel F) := by
  refine {
    success := ?_
    active := ?_
  }
  · intro a x e hrel hv
    cases a with
    | junk C =>
        simp [moderateVulnerableRel] at hrel
    | live C hgood stage =>
        cases stage with
        | attackCR mode =>
            simp [moderateVulnerableRel] at hrel
        | targetCR attackPhase mode =>
            simp [moderateVulnerableRel] at hrel
        | dummyWait attackPhase targetPhase =>
            simp [moderateVulnerableRel] at hrel
        | recovery attackPhase targetPhase =>
            simp [moderateVulnerableRel] at hrel
        | stuck =>
            simp [moderateVulnerableRel] at hrel
        | vulnerable attackPhase targetPhase =>
            have hr :
                And
                  (x.cfg = C)
                  (And
                    (x.attackPhase = attackPhase)
                    (x.targetPhase = targetPhase)) := by
              simpa [moderateVulnerableRel] using hrel
            rcases hr with ⟨hcfg, hrest⟩
            rcases hrest with ⟨hattack, htarget⟩
            subst C
            subst attackPhase
            subst targetPhase
            classical
            by_cases hfail :
                And
                  (x.targetPhase = .ready)
                  (e = R_j F)
            · have hbad : False := by
                simpa [vulnerableStep, hfail]
                  using hv
              exact False.elim hbad
            · let D := stepE ring x.cfg e
              by_cases htag : TaggedDeleted F D
              · simpa
                  [moderateAttemptKernel,
                    moderateStep, D, htag]
              · have hbad : False := by
                  simpa
                    [vulnerableStep, hfail,
                      D, htag]
                    using hv
                exact False.elim hbad
  · intro a x e x' hrel hv
    cases a with
    | junk C =>
        simp [moderateVulnerableRel] at hrel
    | live C hgood stage =>
        cases stage with
        | attackCR mode =>
            simp [moderateVulnerableRel] at hrel
        | targetCR attackPhase mode =>
            simp [moderateVulnerableRel] at hrel
        | dummyWait attackPhase targetPhase =>
            simp [moderateVulnerableRel] at hrel
        | recovery attackPhase targetPhase =>
            simp [moderateVulnerableRel] at hrel
        | stuck =>
            simp [moderateVulnerableRel] at hrel
        | vulnerable attackPhase targetPhase =>
            have hr :
                And
                  (x.cfg = C)
                  (And
                    (x.attackPhase = attackPhase)
                    (x.targetPhase = targetPhase)) := by
              simpa [moderateVulnerableRel] using hrel
            rcases hr with ⟨hcfg, hrest⟩
            rcases hrest with ⟨hattack, htarget⟩
            subst C
            subst attackPhase
            subst targetPhase
            classical
            by_cases hfail :
                And
                  (x.targetPhase = .ready)
                  (e = R_j F)
            · have hbad : False := by
                simpa [vulnerableStep, hfail]
                  using hv
              exact False.elim hbad
            · let D := stepE ring x.cfg e
              by_cases htag : TaggedDeleted F D
              · have hbad : False := by
                  simpa
                    [vulnerableStep, hfail,
                      D, htag]
                    using hv
                exact False.elim hbad
              · have hnot :
                    ¬ TaggedDeleted F
                      (stepE ring x.cfg e) := by
                  simpa [D] using htag
                have hport :
                    x.targetPhase = .ready →
                      e ≠ F.j := by
                  intro hready he
                  apply hfail
                  exact
                    And.intro
                      hready
                      (by simpa [R_j] using he)
                let child :=
                  vulnerableChild
                    hSealed F x e hport hnot
                have hvchild :
                    vulnerableStep hSealed F x e =
                      .active child := by
                  simp
                    [vulnerableStep, hfail,
                      hnot, child]
                have hchildEq : child = x' := by
                  have hnodes :
                      (StopNode.active child :
                        StopNode (VulnerableState F)) =
                        .active x' :=
                    hvchild.symm.trans hv
                  injection hnodes
                subst x'
                have hgoodD :
                    AttemptGood ring F D := by
                  simpa [D] using
                    (attemptGood_step
                      ring F x.cfg e hgood hnot)
                let a' : ModerateAttemptState ring F :=
                  .live D hgoodD
                    (.vulnerable
                      (nextSectorPhase
                        F.A x.attackPhase e)
                      (nextSectorPhase
                        F.B x.targetPhase e))
                refine ⟨a', ?_, ?_⟩
                · simpa
                    [moderateAttemptKernel,
                      moderateStep, D, hnot,
                      hfail, a']
                · have hAeq :
                      child.attackPhase =
                        nextSectorPhase
                          F.A x.attackPhase e := by
                    simpa [child, PhaseTransition]
                      using
                        (vulnerableChild_attack_transition
                          hSealed F x e hport hnot)
                  have hBeq :
                      child.targetPhase =
                        nextSectorPhase
                          F.B x.targetPhase e := by
                    simpa [child, PhaseTransition]
                      using
                        (vulnerableChild_target_transition
                          hSealed F x e hport hnot)
                  change
                    And
                      (child.cfg = D)
                      (And
                        (child.attackPhase =
                          nextSectorPhase
                            F.A x.attackPhase e)
                        (child.targetPhase =
                          nextSectorPhase
                            F.B x.targetPhase e))
                  exact
                    And.intro rfl
                      (And.intro hAeq hBeq)


/-! ## Pre-vulnerable closure and first-entry reconstruction -/


private theorem moderatePre_step
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    ∀ a e,
      moderatePre F a →
      Or
        ((moderateAttemptKernel ring F).step a e =
          .success)
        (∃ a',
          And
            ((moderateAttemptKernel ring F).step a e =
              .active a')
            (Or
              (moderatePre F a')
              (∃ x : VulnerableState F,
                And
                  (x.targetPhase = .dummy 0)
                  (moderateVulnerableRel F a' x)))) := by
  classical
  intro a e ha
  cases a with
  | junk C =>
      exact
        Or.inl
          (by
            simp
              [moderateAttemptKernel,
                moderateStep])
  | live C hgood stage =>
      let D := stepE ring C e
      by_cases htag : TaggedDeleted F D
      · exact
          Or.inl
            (by
              simpa
                [moderateAttemptKernel,
                  moderateStep, D, htag])
      · have hnot :
            ¬ TaggedDeleted F
              (stepE ring C e) := by
          simpa [D] using htag
        have hgoodD :
            AttemptGood ring F D := by
          simpa [D] using
            (attemptGood_step
              ring F C e hgood hnot)
        cases stage with
        | attackCR mode =>
            by_cases hmode :
                CRModeHolds F.A C mode
            · by_cases hdone :
                  CRDone F.A D
              · have hnotA :
                    ¬ EndpointDeleted F.A D := by
                  intro hdel
                  exact htag
                    (endpointA_deleted_tagged
                      F D hdel)
                have hdone' :
                    Or
                      (EndpointDeleted F.A D)
                      (CleanReady F.A D) := by
                  simpa [CRDone] using hdone
                have hcleanA :
                    CleanReady F.A D :=
                  Or.resolve_left hdone' hnotA
                let a' : ModerateAttemptState ring F :=
                  (moderateAttemptKernel ring F).start D
                have hstep :
                    (moderateAttemptKernel ring F).step
                        (.live C hgood (.attackCR mode)) e =
                      .active a' := by
                  dsimp [a']
                  rw [moderateStart_eq_spliceModerateStart]
                  simp
                    [moderateAttemptKernel,
                      moderateStep, D, htag,
                      hmode, hdone,
                      spliceModerateStart,
                      hgoodD,
                      spliceModerateInitialStage,
                      hcleanA]
                  all_goals rfl
                refine Or.inr ⟨a', ?_⟩
                exact
                  And.intro hstep
                    (Or.inl
                      (moderateStart_pre ring F D))
              · simp
                  [moderateAttemptKernel,
                    moderateStep, D, htag,
                    hmode, hdone,
                    moderatePre,
                    moderateVulnerableRel]
            · simp
                [moderateAttemptKernel,
                  moderateStep, D, htag,
                  hmode, moderatePre,
                  moderateVulnerableRel]
        | targetCR attackPhase mode =>
            have hA :
                PhaseHolds
                  F.A C attackPhase := by
              simpa [moderatePre] using ha
            have hA' :
                PhaseHolds
                  F.A D
                    (nextSectorPhase
                      F.A attackPhase e) := by
              simpa [D] using
                (moderatePhaseANext
                  hSealed ring F C hgood
                  attackPhase hA e hnot)
            by_cases hmode :
                CRModeHolds F.B C mode
            · by_cases hdone :
                  CRDone F.B D
              · have hnotB :
                    ¬ EndpointDeleted F.B D := by
                  intro hdel
                  exact htag
                    (endpointB_deleted_tagged
                      F D hdel)
                have hdone' :
                    Or
                      (EndpointDeleted F.B D)
                      (CleanReady F.B D) := by
                  simpa [CRDone] using hdone
                have hcleanB :
                    CleanReady F.B D :=
                  Or.resolve_left hdone' hnotB
                have hBready :=
                  moderatePhaseBReady
                    F D hgoodD hcleanB
                simpa
                  [moderateAttemptKernel,
                    moderateStep, D, htag,
                    hmode, hdone,
                    moderatePre,
                    moderateVulnerableRel]
                  using
                    And.intro hA' hBready
              · simpa
                  [moderateAttemptKernel,
                    moderateStep, D, htag,
                    hmode, hdone,
                    moderatePre,
                    moderateVulnerableRel]
                  using hA'
            · simp
                [moderateAttemptKernel,
                  moderateStep, D, htag,
                  hmode, moderatePre,
                  moderateVulnerableRel]
        | dummyWait attackPhase targetPhase =>
            have hs :
                And
                  (PhaseHolds
                    F.A C attackPhase)
                  (PhaseHolds
                    F.B C targetPhase) := by
              simpa [moderatePre] using ha
            have hA' :
                PhaseHolds
                  F.A D
                    (nextSectorPhase
                      F.A attackPhase e) := by
              simpa [D] using
                (moderatePhaseANext
                  hSealed ring F C hgood
                  attackPhase hs.1 e hnot)
            have hB' :
                PhaseHolds
                  F.B D
                    (nextSectorPhase
                      F.B targetPhase e) := by
              simpa [D] using
                (moderatePhaseBNext
                  hSealed ring F C hgood
                  targetPhase hs.2 e hnot)
            by_cases hhit :
                And
                  (targetPhase = .ready)
                  (e = sealedIncomingEdge F.B)
            · have hBdummy :
                  PhaseHolds F.B D (.dummy 0) := by
                have ht := hB'
                rw [hhit.1, hhit.2] at ht
                simpa [nextSectorPhase] using ht
              have hunshielded :
                  (D F.j).shield = false :=
                moderateDummyZeroUnshielded
                  F D hBdummy
              let x : VulnerableState F := {
                cfg := D
                attackPhase :=
                  nextSectorPhase
                    F.A attackPhase e
                targetPhase := .dummy 0
                hAttack := hA'
                hTarget := hBdummy
                alive := hgoodD.2.1
                targetUnshielded := hunshielded
              }
              let a' : ModerateAttemptState ring F :=
                .live D hgoodD
                  (.vulnerable
                    (nextSectorPhase
                      F.A attackPhase e)
                    (.dummy 0))
              have hstep :
                  (moderateAttemptKernel ring F).step
                      (.live C hgood
                        (.dummyWait
                          attackPhase targetPhase))
                      e =
                    .active a' := by
                simp
                  [moderateAttemptKernel,
                    moderateStep, D, htag,
                    hhit, a']
                all_goals exact dif_neg (by simpa [D, hhit.2] using htag)
              have hrelEntry :
                  moderateVulnerableRel F a' x := by
                dsimp [a', x, moderateVulnerableRel]
                exact
                  And.intro rfl
                    (And.intro rfl rfl)
              refine Or.inr ⟨a', ?_⟩
              exact
                And.intro hstep
                  (Or.inr
                    ⟨x,
                      And.intro
                        (by rfl)
                        hrelEntry⟩)
            · simpa
                [moderateAttemptKernel,
                  moderateStep, D, htag,
                  hhit, moderatePre,
                  moderateVulnerableRel]
                using And.intro hA' hB'
        | vulnerable attackPhase targetPhase =>
            have hfalse : False := by
              simpa [moderatePre] using ha
            exact False.elim hfalse
        | recovery attackPhase targetPhase =>
            have hfalse : False := by
              simpa [moderatePre] using ha
            exact False.elim hfalse
        | stuck =>
            simp
              [moderateAttemptKernel,
                moderateStep, D, htag,
                moderatePre,
                moderateVulnerableRel]


/-! ## Closed first-vulnerable splice -/


theorem moderateFirstVulnerableSplice :
    ModerateFirstVulnerableSpliceSpec := by
  intro hSealed
  intro n ring C0 F _hb
  refine
    ⟨moderatePre F,
      moderateVulnerableRel F,
      ?_⟩
  exact
    And.intro
      (moderateStart_pre ring F)
      (And.intro
        (moderateVulnerableSimulation
          hSealed ring F)
        (moderatePre_step
          hSealed ring F))


theorem moderateAttemptRetryMassSpec_closed :
    ModerateAttemptRetryMassSpec :=
  moderateAttemptRetryMassSpec_proved
    moderateFirstVulnerableSplice


end PPL.Convergence.LDLocal



#print axioms PPL.Convergence.LDLocal.moderateAttemptRetryMassSpec_closed
