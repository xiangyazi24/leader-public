import Leader.PPL.Elim.AttemptLongFirstCut

namespace PPL.Convergence.LDLocal

set_option autoImplicit false

/-- Unfold the private `longAfterTargetStage` of `LDLocalAttempt.lean`
(same pattern as `unfoldFinishModes` in `ClockSuffixBridge.lean`). -/
elab "unfoldLongAfterTargetStage" : tactic => do
  let c := Lean.mkIdent
    ((((((`_private.Leader.PPL.Elim.Attempt).num 0).str "PPL").str
      "Convergence").str "LDLocal").str "longAfterTargetStage")
  let tac ← `(tactic| unfold $c:ident)
  Lean.Elab.Tactic.evalTactic tac

/-- Source fact: `longAfterTargetStage` only returns `.liveWait .ready .ready`
or `.attackerCR .ready _`, so the target-CR done branch never enters recovery. -/
theorem longTargetCRDoneRecoveryFree_proved :
    LongTargetCRDoneRecoveryFree := by
  unfold LongTargetCRDoneRecoveryFree
  intro n ring C0 F C hgood mode e a' hmode hdone hstep
  classical
  simp only [longAttemptKernel] at hstep
  unfold longStep at hstep
  dsimp only at hstep
  by_cases htag : TaggedDeleted F (stepE ring C e)
  · rw [dif_pos htag] at hstep
    cases hstep
  · rw [dif_neg htag, dif_pos hmode, dif_pos hdone] at hstep
    cases hstep
    unfoldLongAfterTargetStage
    by_cases hA : CleanReady F.A (stepE ring C e)
    · rw [dif_pos hA]
      first | rfl | simp [longRecoveryCut]
    · rw [dif_neg hA]
      first | rfl | simp [longRecoveryCut]

theorem longAttemptFirstCutStageFactorSpec_entry_closed
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (hb : 2 <= F.b)
    (hab : 2 * F.b + 1 <= F.a) :
    forall s,
      AttemptGood ring F s ->
      forall T,
        longProgressEntryMass ring F s T = n ^ T :=
  longAttemptFirstCutStageFactorSpec_entry sealedStepSpec
    longTargetCRDoneRecoveryFree_proved ring F hb hab

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.longTargetCRDoneRecoveryFree_proved
#print axioms PPL.Convergence.LDLocal.longAttemptFirstCutStageFactorSpec_entry_closed
