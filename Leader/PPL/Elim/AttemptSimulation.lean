import Leader.PPL.Elim.Attempt

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

theorem moderateSimulationSpec_proved :
    ModerateSimulationSpec := by
  classical
  unfold ModerateSimulationSpec
  intro n ring C0 F
  have hstepPhysical :
      ∀ (a : ModerateAttemptState ring F) (e : Fin n),
        (match a with
          | .junk _ => False
          | .live _ _ _ => True) →
        match (moderateAttemptKernel ring F).step a e with
        | .active a' =>
            moderateConfig a' =
                stepE ring (moderateConfig a) e ∧
              (match a' with
                | .junk _ => False
                | .live _ _ _ => True)
        | .success =>
            TaggedDeleted F
              (stepE ring (moderateConfig a) e)
        | .retry s' =>
            s' = stepE ring (moderateConfig a) e ∧
              AttemptGood ring F s' := by
    intro a e ha
    cases a with
    | junk C =>
        exact False.elim ha
    | live C hgood stage =>
        by_cases htag :
            TaggedDeleted F (stepE ring C e)
        · simp only [moderateAttemptKernel]
          unfold moderateStep
          dsimp only
          rw [dif_pos htag]
          exact htag
        · have hgoodD :
              AttemptGood ring F (stepE ring C e) :=
            attemptGood_step ring F C e hgood htag
          simp only [moderateAttemptKernel]
          unfold moderateStep
          dsimp only
          rw [dif_neg htag]
          cases stage <;>
            repeat' split <;>
            (try simp_all [moderateConfig]) <;> (repeat' (split at *)) <;> simp_all [moderateConfig]

  refine
    { start_cfg := ?_
      start_sound := ?_
      active_cfg := ?_
      active_sound := ?_
      retry_cfg := ?_
      retry_good := ?_
      success_tagged := ?_ }
  · intro s hs
    simp [moderateAttemptKernel, moderateStart,
      moderateConfig, hs]
  · intro s hs
    simp [moderateAttemptKernel, moderateStart, hs]
  · intro a e a' ha hstep
    have h := hstepPhysical a e ha
    simp only [hstep] at h
    exact h.1
  · intro a e a' ha hstep
    have h := hstepPhysical a e ha
    simp only [hstep] at h
    exact h.2
  · intro a e s' ha hstep
    have h := hstepPhysical a e ha
    simp only [hstep] at h
    exact h.1
  · intro a e s' ha hstep
    have h := hstepPhysical a e ha
    simp only [hstep] at h
    exact h.2
  · intro a e ha hstep
    have h := hstepPhysical a e ha
    simpa only [hstep] using h

theorem longSimulationSpec_proved :
    LongSimulationSpec := by
  classical
  unfold LongSimulationSpec
  intro n ring C0 F
  have hstepPhysical :
      ∀ (a : LongAttemptState ring F) (e : Fin n),
        (match a with
          | .junk _ => False
          | .live _ _ _ => True) →
        match (longAttemptKernel ring F).step a e with
        | .active a' =>
            longConfig a' =
                stepE ring (longConfig a) e ∧
              (match a' with
                | .junk _ => False
                | .live _ _ _ => True)
        | .success =>
            TaggedDeleted F
              (stepE ring (longConfig a) e)
        | .retry s' =>
            s' = stepE ring (longConfig a) e ∧
              AttemptGood ring F s' := by
    intro a e ha
    cases a with
    | junk C =>
        exact False.elim ha
    | live C hgood stage =>
        by_cases htag :
            TaggedDeleted F (stepE ring C e)
        · simp only [longAttemptKernel]
          unfold longStep
          dsimp only
          rw [dif_pos htag]
          exact htag
        · have hgoodD :
              AttemptGood ring F (stepE ring C e) :=
            attemptGood_step ring F C e hgood htag
          simp only [longAttemptKernel]
          unfold longStep
          dsimp only
          rw [dif_neg htag]
          cases stage <;>
            repeat' split <;>
            (try simp_all [longConfig]) <;> (repeat' (split at *)) <;> simp_all [longConfig]

  refine
    { start_cfg := ?_
      start_sound := ?_
      active_cfg := ?_
      active_sound := ?_
      retry_cfg := ?_
      retry_good := ?_
      success_tagged := ?_ }
  · intro s hs
    simp [longAttemptKernel, longStart,
      longConfig, hs]
  · intro s hs
    simp [longAttemptKernel, longStart, hs]
  · intro a e a' ha hstep
    have h := hstepPhysical a e ha
    simp only [hstep] at h
    exact h.1
  · intro a e a' ha hstep
    have h := hstepPhysical a e ha
    simp only [hstep] at h
    exact h.2
  · intro a e s' ha hstep
    have h := hstepPhysical a e ha
    simp only [hstep] at h
    exact h.1
  · intro a e s' ha hstep
    have h := hstepPhysical a e ha
    simp only [hstep] at h
    exact h.2
  · intro a e ha hstep
    have h := hstepPhysical a e ha
    simpa only [hstep] using h

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.moderateSimulationSpec_proved
#print axioms PPL.Convergence.LDLocal.longSimulationSpec_proved
