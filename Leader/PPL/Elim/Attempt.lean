import Leader.PPL.Elim.ModerateRegime
import Leader.PPL.Elim.SealedStep
import Leader.PPL.Elim.CleanLiveCost

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-! ## Fixed-frame survivor domain -/

def AttemptGood
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) : Prop :=
  PPL.Elim.PB ring D ∧
    ¬ TaggedDeleted F D ∧
    CRInteriorFollowers F.A D ∧
    CRInteriorFollowers F.B D

theorem attemptGood_initial
    {n : Nat} (ring : DirectedRing n)
    (C : Config n) (hPB : PPL.Elim.PB ring C)
    (F : TripleFrame ring C) :
    AttemptGood ring F C := by
  refine ⟨hPB, ?_, F.A.interior_follower, F.B.interior_follower⟩
  intro h
  rcases h with hi | hj | hk
  · have ht : (C F.i).leader = true := by
      rw [← F.A_left]
      exact F.A.left_leader
    rw [hi] at ht
    cases ht
  · have ht : (C F.j).leader = true := by
      rw [← F.A_right]
      exact F.A.right_leader
    rw [hj] at ht
    cases ht
  · have ht : (C F.k).leader = true := by
      rw [← F.B_right]
      exact F.B.right_leader
    rw [hk] at ht
    cases ht

theorem attemptGood_step
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (e : Fin n)
    (hgood : AttemptGood ring F D)
    (hnot : ¬ TaggedDeleted F (stepE ring D e)) :
    AttemptGood ring F (stepE ring D e) := by
  exact ⟨
    pbStepClosure ring D e hgood.1,
    hnot,
    crInteriorFollowers_step F.A D e hgood.2.2.1,
    crInteriorFollowers_step F.B D e hgood.2.2.2
  ⟩

private theorem attemptGood_notEndpointA
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ¬ EndpointDeleted F.A D := by
  intro h
  exact hgood.2.1 (endpointA_deleted_tagged F D h)

private theorem attemptGood_notEndpointB
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ¬ EndpointDeleted F.B D := by
  intro h
  exact hgood.2.1 (endpointB_deleted_tagged F D h)

/-! ## Reusable CR choices -/

private noncomputable def attemptCRInitMode
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

private noncomputable def attemptCRNextMode
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n) (mode : CRMode)
    (hPB : PPL.Elim.PB ring D)
    (hInterior : CRInteriorFollowers A D)
    (hmode : CRModeHolds A D mode)
    (e : Fin n)
    (hnotDone : ¬ CRDone A (stepE ring D e)) : CRMode :=
  Classical.choose
    (by
      rcases
          (crRankStep_proved ring A D mode hPB hInterior hmode).1 e with
        hdone | hnext
      · exact False.elim (hnotDone hdone)
      · exact hnext)

/-! ## Moderate physical attempt -/

inductive ModerateStage where
  | attackCR (mode : CRMode)
  | targetCR (attackPhase : SectorPhase) (mode : CRMode)
  | dummyWait (attackPhase targetPhase : SectorPhase)
  | vulnerable (attackPhase targetPhase : SectorPhase)
  | recovery (attackPhase targetPhase : SectorPhase)
  | stuck
  deriving DecidableEq

inductive ModerateAttemptState
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) where
  | junk (cfg : Config n)
  | live (cfg : Config n)
      (good : AttemptGood ring F cfg)
      (stage : ModerateStage)

def moderateConfig
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} {F : TripleFrame ring C0} :
    ModerateAttemptState ring F → Config n
  | .junk C => C
  | .live C _ _ => C

private noncomputable def moderateAfterAttackStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ModerateStage := by
  classical
  by_cases hB : CleanReady F.B D
  · exact .dummyWait .ready .ready
  · exact .targetCR .ready
      (attemptCRInitMode ring F.B D hgood.1
        (attemptGood_notEndpointB F D hgood) hB)

private noncomputable def moderateInitialStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ModerateStage := by
  classical
  by_cases hA : CleanReady F.A D
  · exact moderateAfterAttackStage ring F D hgood
  · exact .attackCR
      (attemptCRInitMode ring F.A D hgood.1
        (attemptGood_notEndpointA F D hgood) hA)

noncomputable def moderateStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) :
    ModerateAttemptState ring F := by
  classical
  by_cases hgood : AttemptGood ring F D
  · exact .live D hgood (moderateInitialStage ring F D hgood)
  · exact .junk D

noncomputable def moderateStep
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    ModerateAttemptState ring F →
      Fin n →
      AttemptNode (ModerateAttemptState ring F) (Config n) := by
  classical
  intro s e
  cases s with
  | junk C =>
      exact .success
  | live C hgood stage =>
      let D := stepE ring C e
      if htag : TaggedDeleted F D then
        exact .success
      else
        have hgoodD : AttemptGood ring F D :=
          attemptGood_step ring F C e hgood htag
        let nextA := fun ph => nextSectorPhase F.A ph e
        let nextB := fun ph => nextSectorPhase F.B ph e
        cases stage with
        | attackCR mode =>
            by_cases hmode : CRModeHolds F.A C mode
            · by_cases hdone : CRDone F.A D
              · exact .active
                  (.live D hgoodD
                    (moderateAfterAttackStage ring F D hgoodD))
              · exact .active
                  (.live D hgoodD
                    (.attackCR
                      (attemptCRNextMode ring F.A C mode
                        hgood.1 hgood.2.2.1 hmode e hdone)))
            · exact .active (.live D hgoodD .stuck)
        | targetCR attackPhase mode =>
            by_cases hmode : CRModeHolds F.B C mode
            · by_cases hdone : CRDone F.B D
              · exact .active
                  (.live D hgoodD
                    (.dummyWait (nextA attackPhase) .ready))
              · exact .active
                  (.live D hgoodD
                    (.targetCR (nextA attackPhase)
                      (attemptCRNextMode ring F.B C mode
                        hgood.1 hgood.2.2.2 hmode e hdone)))
            · exact .active (.live D hgoodD .stuck)
        | dummyWait attackPhase targetPhase =>
            if hhit :
                targetPhase = .ready ∧
                  e = sealedIncomingEdge F.B then
              exact .active
                (.live D hgoodD
                  (.vulnerable (nextA attackPhase) (.dummy 0)))
            else
              exact .active
                (.live D hgoodD
                  (.dummyWait (nextA attackPhase) (nextB targetPhase)))
        | vulnerable attackPhase targetPhase =>
            if hfail :
                targetPhase = .ready ∧ e = R_j F then
              exact .active
                (.live D hgoodD
                  (.recovery (nextA attackPhase) (nextB targetPhase)))
            else
              exact .active
                (.live D hgoodD
                  (.vulnerable (nextA attackPhase) (nextB targetPhase)))
        | recovery attackPhase targetPhase =>
            if hready : nextB targetPhase = .ready then
              exact .retry D
            else
              exact .active
                (.live D hgoodD
                  (.recovery (nextA attackPhase) (nextB targetPhase)))
        | stuck =>
            exact .active (.live D hgoodD .stuck)

noncomputable def moderateAttemptKernel
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    RetryKernel (ModerateAttemptState ring F) (Config n) n where
  start := moderateStart ring F
  step := moderateStep ring F
  valid := fun _ => True
  retry_valid := by
    intro _ _ _ _
    trivial

/-! ## Long physical attempt -/

inductive LongStage where
  | targetCR (mode : CRMode)
  | attackerCR (targetPhase : SectorPhase) (mode : CRMode)
  | liveWait (targetPhase attackPhase : SectorPhase)
  | advance (targetPhase attackPhase : SectorPhase)
  | race (targetPhase attackPhase : SectorPhase)
  | incident (attackPhase : SectorPhase)
  | retained (targetPhase attackPhase : SectorPhase)
  | recovery (targetPhase attackPhase : SectorPhase)
  | stuck
  deriving DecidableEq

inductive LongAttemptState
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) where
  | junk (cfg : Config n)
  | live (cfg : Config n)
      (good : AttemptGood ring F cfg)
      (stage : LongStage)

def longConfig
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} {F : TripleFrame ring C0} :
    LongAttemptState ring F → Config n
  | .junk C => C
  | .live C _ _ => C

private noncomputable def longAfterTargetStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    LongStage := by
  classical
  by_cases hA : CleanReady F.A D
  · exact .liveWait .ready .ready
  · exact .attackerCR .ready
      (attemptCRInitMode ring F.A D hgood.1
        (attemptGood_notEndpointA F D hgood) hA)

private noncomputable def longInitialStage
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    LongStage := by
  classical
  by_cases hB : CleanReady F.B D
  · exact longAfterTargetStage ring F D hgood
  · exact .targetCR
      (attemptCRInitMode ring F.B D hgood.1
        (attemptGood_notEndpointB F D hgood) hB)

noncomputable def longStart
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) :
    LongAttemptState ring F := by
  classical
  by_cases hgood : AttemptGood ring F D
  · exact .live D hgood (longInitialStage ring F D hgood)
  · exact .junk D

noncomputable def longStep
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    LongAttemptState ring F →
      Fin n →
      AttemptNode (LongAttemptState ring F) (Config n) := by
  classical
  intro s e
  cases s with
  | junk C =>
      exact .success
  | live C hgood stage =>
      let D := stepE ring C e
      if htag : TaggedDeleted F D then
        exact .success
      else
        have hgoodD : AttemptGood ring F D :=
          attemptGood_step ring F C e hgood htag
        let nextA := fun ph => nextSectorPhase F.A ph e
        let nextB := fun ph => nextSectorPhase F.B ph e
        cases stage with
        | targetCR mode =>
            by_cases hmode : CRModeHolds F.B C mode
            · by_cases hdone : CRDone F.B D
              · exact .active
                  (.live D hgoodD
                    (longAfterTargetStage ring F D hgoodD))
              · exact .active
                  (.live D hgoodD
                    (.targetCR
                      (attemptCRNextMode ring F.B C mode
                        hgood.1 hgood.2.2.2 hmode e hdone)))
            · exact .active (.live D hgoodD .stuck)
        | attackerCR targetPhase mode =>
            by_cases hmode : CRModeHolds F.A C mode
            · by_cases hdone : CRDone F.A D
              · exact .active
                  (.live D hgoodD
                    (.liveWait (nextB targetPhase) .ready))
              · exact .active
                  (.live D hgoodD
                    (.attackerCR (nextB targetPhase)
                      (attemptCRNextMode ring F.A C mode
                        hgood.1 hgood.2.2.1 hmode e hdone)))
            · exact .active (.live D hgoodD .stuck)
        | liveWait targetPhase attackPhase =>
            if hfire :
                attackPhase = .ready ∧ e = F.A.left then
              if hnear : F.a - 2 * F.b ≤ 1 then
                exact .active
                  (.live D hgoodD
                    (.race (nextB targetPhase) (nextA attackPhase)))
              else
                exact .active
                  (.live D hgoodD
                    (.advance (nextB targetPhase) (nextA attackPhase)))
            else
              exact .active
                (.live D hgoodD
                  (.liveWait (nextB targetPhase) (nextA attackPhase)))
        | advance targetPhase attackPhase =>
            if hreach :
                nextA attackPhase = .live (F.a - 2 * F.b) then
              exact .active
                (.live D hgoodD
                  (.race (nextB targetPhase) (nextA attackPhase)))
            else
              exact .active
                (.live D hgoodD
                  (.advance (nextB targetPhase) (nextA attackPhase)))
        | race targetPhase attackPhase =>
            if hready : targetPhase = .ready then
              if hout : e = R_j F then
                exact .active
                  (.live D hgoodD
                    (.recovery (nextB targetPhase) (nextA attackPhase)))
              else if hin : e = L_j F then
                exact .active
                  (.live D hgoodD
                    (.retained (nextB targetPhase) (nextA attackPhase)))
              else
                exact .active
                  (.live D hgoodD
                    (.incident (nextA attackPhase)))
            else
              if hhit :
                  ∃ p, attackPhase = .live p ∧
                    e = advance ring F.A.left p ∧ p + 1 = F.a then
                exact .active
                  (.live D hgoodD
                    (.recovery (nextB targetPhase) (nextA attackPhase)))
              else if htarget : nextB targetPhase = .ready then
                exact .active
                  (.live D hgoodD (.incident (nextA attackPhase)))
              else
                exact .active
                  (.live D hgoodD
                    (.race (nextB targetPhase) (nextA attackPhase)))
        | incident attackPhase =>
            if hout : e = R_j F then
              exact .active
                (.live D hgoodD
                  (.recovery (nextB .ready) (nextA attackPhase)))
            else if hin : e = L_j F then
              exact .active
                (.live D hgoodD
                  (.retained (nextB .ready) (nextA attackPhase)))
            else if hready : nextB .ready = .ready then
              exact .active
                (.live D hgoodD (.incident (nextA attackPhase)))
            else
              exact .active
                (.live D hgoodD
                  (.race (nextB .ready) (nextA attackPhase)))
        | retained targetPhase attackPhase =>
            if hfail :
                targetPhase = .ready ∧ e = R_j F then
              exact .active
                (.live D hgoodD
                  (.recovery (nextB targetPhase) (nextA attackPhase)))
            else
              exact .active
                (.live D hgoodD
                  (.retained (nextB targetPhase) (nextA attackPhase)))
        | recovery targetPhase attackPhase =>
            if hready : nextB targetPhase = .ready then
              exact .retry D
            else
              exact .active
                (.live D hgoodD
                  (.recovery (nextB targetPhase) (nextA attackPhase)))
        | stuck =>
            exact .active (.live D hgoodD .stuck)

noncomputable def longAttemptKernel
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0) :
    RetryKernel (LongAttemptState ring F) (Config n) n where
  start := longStart ring F
  step := longStep ring F
  valid := fun _ => True
  retry_valid := by
    intro _ _ _ _
    trivial

/-! ## Generic exact physical domination -/

structure PhysicalRetrySimulation
    {A : Type} {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (K : RetryKernel A (Config n) n)
    (cfg : A → Config n)
    (good : Config n → Prop)
    (sound : A → Prop) : Prop where
  start_cfg :
    ∀ s, good s → cfg (K.start s) = s
  start_sound :
    ∀ s, good s → sound (K.start s)
  active_cfg :
    ∀ a e a', sound a →
      K.step a e = .active a' →
      cfg a' = stepE ring (cfg a) e
  active_sound :
    ∀ a e a', sound a →
      K.step a e = .active a' →
      sound a'
  retry_cfg :
    ∀ a e s', sound a →
      K.step a e = .retry s' →
      s' = stepE ring (cfg a) e
  retry_good :
    ∀ a e s', sound a →
      K.step a e = .retry s' →
      good s'
  success_tagged :
    ∀ a e, sound a →
      K.step a e = .success →
      TaggedDeleted F (stepE ring (cfg a) e)

theorem physicalRetry_active_domination
    {A : Type} {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (K : RetryKernel A (Config n) n)
    (cfg : A → Config n)
    (good : Config n → Prop)
    (sound : A → Prop)
    (hSim : PhysicalRetrySimulation ring F K cfg good sound) :
    ∀ a, sound a → ∀ T,
      costNumerator
          (stepE ring) (TaggedDeleted F) (cfg a) T ≤
        repeatCostActive K a T := by
  intro a ha T
  induction T generalizing a with
  | zero =>
      exact Nat.le_refl _
  | succ T ih =>
      by_cases htag : TaggedDeleted F (cfg a)
      · rw [costNumerator_terminal
          (stepE ring) (TaggedDeleted F) (cfg a) htag]
        exact Nat.zero_le _
      · rw [costNumerator_succ
          (stepE ring) (TaggedDeleted F) (cfg a) htag T]
        simp only [repeatCostActive]
        apply Nat.add_le_add_left
        apply ofFn_sum_le
        intro e
        cases hstep : K.step a e with
        | success =>
            have hs := hSim.success_tagged a e ha hstep
            rw [costNumerator_terminal
              (stepE ring) (TaggedDeleted F)
              (stepE ring (cfg a) e) hs]
            simp
        | active a' =>
            have hcfg := hSim.active_cfg a e a' ha hstep
            have hsnd := hSim.active_sound a e a' ha hstep
            simpa [hstep, hcfg] using ih a' hsnd
        | retry s' =>
            have hcfg := hSim.retry_cfg a e s' ha hstep
            have hgood := hSim.retry_good a e s' ha hstep
            have hsnd := hSim.start_sound s' hgood
            have hstart := hSim.start_cfg s' hgood
            have h1 := ih (K.start s') hsnd
            rw [hstart] at h1
            rw [← hcfg]
            simpa [hstep] using h1

theorem physicalRetry_domination
    {A : Type} {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (K : RetryKernel A (Config n) n)
    (cfg : A → Config n)
    (good : Config n → Prop)
    (sound : A → Prop)
    (hSim : PhysicalRetrySimulation ring F K cfg good sound)
    (s : Config n) (hs : good s) :
    ∀ T,
      costNumerator
          (stepE ring) (TaggedDeleted F) s T ≤
        repeatCostNumerator K s T := by
  intro T
  unfold repeatCostNumerator
  have h :=
    physicalRetry_active_domination
      ring F K cfg good sound hSim
      (K.start s) (hSim.start_sound s hs) T
  simpa [hSim.start_cfg s hs] using h

/-! ## Exact remaining R1 obligations for the concrete kernels -/

def ModerateSimulationSpec : Prop :=
  ∀ {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0),
    PhysicalRetrySimulation
      ring F
      (moderateAttemptKernel ring F)
      moderateConfig
      (AttemptGood ring F)
      (fun a =>
        match a with
        | .junk _ => False
        | .live _ _ _ => True)

def ModerateAttemptCostSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 ≤ F.b →
      F.a ≤ 2 * F.b →
      ∀ s T,
        attemptCostNumerator
            (moderateAttemptKernel ring F)
            (.active ((moderateAttemptKernel ring F).start s)) T ≤
          n ^ T * (n * (8 * F.a + 7 * F.b))

def ModerateAttemptRetryMassSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 ≤ F.b →
      F.a ≤ 2 * F.b →
      ∀ s T,
        96 * retryCount
            (moderateAttemptKernel ring F)
            (.active ((moderateAttemptKernel ring F).start s)) T ≤
          95 * n ^ T

def LongSimulationSpec : Prop :=
  ∀ {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0),
    PhysicalRetrySimulation
      ring F
      (longAttemptKernel ring F)
      longConfig
      (AttemptGood ring F)
      (fun a =>
        match a with
        | .junk _ => False
        | .live _ _ _ => True)

def LongAttemptCostSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 ≤ F.b →
      2 * F.b + 1 ≤ F.a →
      ∀ s T,
        attemptCostNumerator
            (longAttemptKernel ring F)
            (.active ((longAttemptKernel ring F).start s)) T ≤
          n ^ T * (7 * n * (F.a + F.b))

def LongAttemptRetryMassSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 ≤ F.b →
      2 * F.b + 1 ≤ F.a →
      ∀ s T,
        16 * retryCount
            (longAttemptKernel ring F)
            (.active ((longAttemptKernel ring F).start s)) T ≤
          15 * n ^ T

def LongAttemptProducerSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      (C : Config n)
      (hPB : PPL.Elim.PB ring C)
      (h2 : 2 ≤ PPL.Elim.leaderCount C)
      (F : TripleFrame ring C),
      2 ≤ F.b →
      2 * F.b + 1 ≤ F.a →
      ∃ AttemptState : Type,
        ∃ K : RetryKernel AttemptState (Config n) n,
          K.valid C ∧
          (∀ s, K.valid s → ∀ T,
            attemptCostNumerator K (.active (K.start s)) T ≤
              n ^ T * (7 * n * (F.a + F.b))) ∧
          (∀ s, K.valid s → ∀ T,
            16 * retryCount K (.active (K.start s)) T ≤
              15 * n ^ T) ∧
          (∀ T,
            costNumerator
                (stepE ring) (TaggedDeleted F) C T ≤
              repeatCostNumerator K C T)

/-! ## Producer assembly once the six precise R1 residuals close -/

theorem moderateAttemptProducer_of_attempt_specs
    (hSim : ModerateSimulationSpec)
    (hCost : ModerateAttemptCostSpec)
    (hRetry : ModerateAttemptRetryMassSpec) :
    ModerateAttemptProducerSpec := by
  unfold ModerateAttemptProducerSpec
  intro hSealed n ring C hPB F hb hab
  let K := moderateAttemptKernel ring F
  have hgood : AttemptGood ring F C :=
    attemptGood_initial ring C hPB F
  refine ⟨ModerateAttemptState ring F, K, ?_, ?_, ?_, ?_⟩
  · trivial
  · intro s _ T
    exact hCost hSealed ring F hb hab s T
  · intro s _ T
    exact hRetry hSealed ring F hb hab s T
  · intro T
    exact
      physicalRetry_domination
        ring F K moderateConfig
        (AttemptGood ring F)
        (fun a =>
          match a with
          | .junk _ => False
          | .live _ _ _ => True)
        (hSim ring F) C hgood T

theorem longAttemptProducer_of_attempt_specs
    (hSim : LongSimulationSpec)
    (hCost : LongAttemptCostSpec)
    (hRetry : LongAttemptRetryMassSpec) :
    LongAttemptProducerSpec := by
  unfold LongAttemptProducerSpec
  intro hSealed n ring C hPB _h2 F hb hab
  let K := longAttemptKernel ring F
  have hgood : AttemptGood ring F C :=
    attemptGood_initial ring C hPB F
  refine ⟨LongAttemptState ring F, K, ?_, ?_, ?_, ?_⟩
  · trivial
  · intro s _ T
    exact hCost hSealed ring F hb hab s T
  · intro s _ T
    exact hRetry hSealed ring F hb hab s T
  · intro T
    exact
      physicalRetry_domination
        ring F K longConfig
        (AttemptGood ring F)
        (fun a =>
          match a with
          | .junk _ => False
          | .live _ _ _ => True)
        (hSim ring F) C hgood T

theorem longBoundaryPhysical_of_longAttempt
    (hLong : LongAttemptProducerSpec) :
    LongBoundaryPhysicalSpec := by
  unfold LongBoundaryPhysicalSpec
  intro hSweep hReturn hSealed
  constructor
  · intro n ring C hPB h2 F hb hab
    exact hLong hSealed ring C hPB h2 F hb hab
  · intro n ring C hPB h2 F hb T
    exact
      boundary_ld_sealed hSealed
        ring C hPB h2 F hb T

/-! ## Constant audit -/

theorem moderate_736_coefficient
    (a b : Nat) (hab : a ≤ 2 * b) :
    96 * (8 * a + 7 * b) ≤
      736 * (a + b) := by
  omega

theorem long_736_coefficient
    (n a b : Nat) :
    16 * (7 * n * (a + b)) ≤
      736 * n * (a + b) := by
  have h : 112 ≤ 736 := by decide
  calc
    16 * (7 * n * (a + b)) =
        112 * (n * (a + b)) := by
      rw [show (112 : Nat) = 16 * 7 by rfl]
      simp only [Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ 736 * (n * (a + b)) :=
      Nat.mul_le_mul_right _ h
    _ = 736 * n * (a + b) := by
      ac_rfl

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.attemptGood_initial
#print axioms PPL.Convergence.LDLocal.attemptGood_step
#print axioms PPL.Convergence.LDLocal.physicalRetry_active_domination
#print axioms PPL.Convergence.LDLocal.physicalRetry_domination
#print axioms PPL.Convergence.LDLocal.moderateAttemptProducer_of_attempt_specs
#print axioms PPL.Convergence.LDLocal.longAttemptProducer_of_attempt_specs
#print axioms PPL.Convergence.LDLocal.longBoundaryPhysical_of_longAttempt
#print axioms PPL.Convergence.LDLocal.moderate_736_coefficient
#print axioms PPL.Convergence.LDLocal.long_736_coefficient
