import Leader.Wu.Birth.ShortDoneTerminalConsumer
import Leader.Wu.Birth.FullHostRulerCounterexample
import Leader.Wu.WriteSeq.RulerBridge


namespace Q11475Counterexample


open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLWriteSeqRulerBridge
open BirthFullHostRulerCounterexample


set_option autoImplicit false


private theorem h2 : 0 < 2 := by decide
private theorem hwidth2 : 0 < 2 := by decide
private theorem hle2 : 2 ≤ 2 := Nat.le_refl 2


/-- Same complete stable ruler fields; only target component 0 gets
    arbitrary comparison garbage. -/
def badCore (i : Fin 8) : AgentState 2 :=
  if _h : i = 2 then
    { stableCore i with
      state := .CHECK_ready,
      path := .some 0 1 }
  else
    stableCore i


private theorem badCore_domain (i : Fin 8) :
    (badCore i).inProtocolDomain 2 := by
  by_cases h : i = 2
  · subst i
    simp [badCore, stableCore,
      PPLLNoCheckBirthOutputLegitimacy.trapCore,
      PPLLNoCheckBirthConditionTwoProtocol.PeaceView.toState,
      AgentState.inProtocolDomain]
  · simp [badCore, h]
    exact stableCore_domain 2 i


/-- Full expiring records: all fields are inherited from the concrete
    `stableCore`; the only raw modifications are the two fields above. -/
def badInitial (i : Fin 8) : ExpiringAgentState 2 2 16 :=
  ⟨⟨BoundedAgentState.ofDomain (badCore i) (badCore_domain i), false⟩,
    ⟨0, Nat.zero_lt_succ 16⟩⟩


/-- The reference source group is 00 and the selected larger group is 01.
    Only comparison state/path were changed, so the ruler arithmetic is the
    same as for `stableCore`. -/
theorem selected_source_target :
    groupID ringEight.hn badCore (0 : Fin 8) = 0 ∧
    groupID ringEight.hn badCore (2 : Fin 8) = 1 ∧
    (badCore (groupOffset ringEight (0 : Fin 8) 0)).bit = false ∧
    (badCore (groupOffset ringEight (2 : Fin 8) 0)).bit = false ∧
    (badCore (groupOffset ringEight (0 : Fin 8) 1)).bit = false ∧
    (badCore (groupOffset ringEight (2 : Fin 8) 1)).bit = true := by
  decide


/-- All local first-CHECK fields except source ancestry have the intended
    target-side shape; the forged path payload is 1 although source bit 0 is
    false. -/
theorem first_field_failure :
    (badCore 2).label.val = 0 ∧
    (badCore 2).state = .CHECK_ready ∧
    (badCore 2).bit =
      (badCore (groupOffset ringEight (2 : Fin 8) 0)).bit ∧
    (badCore 2).path ≠
      .some 0
        (boolBitValue
          ((badCore (groupOffset ringEight (0 : Fin 8) 0)).bit)) := by
  decide


/-- One genuine CURRENT-host interaction, deliberately on an unrelated edge. -/
def afterOne : Fin 8 → ExpiringAgentState 2 2 16 :=
  BirthShortDoneTerminalConsumer.step
    h2 hwidth2 hle2 ringEight badInitial (4 : Fin 8)


/-- `step_other` proves that the forged target component survives the current
    interaction unchanged. -/
theorem forged_component_survives_current_step :
    afterOne 2 = badInitial 2 := by
  unfold afterOne
  exact BirthShortDoneTerminalConsumer.step_other
    h2 hwidth2 hle2 ringEight badInitial
    (4 : Fin 8) (2 : Fin 8) (by decide) (by decide)


end Q11475Counterexample


#print axioms Q11475Counterexample.selected_source_target
#print axioms Q11475Counterexample.first_field_failure
#print axioms Q11475Counterexample.forged_component_survives_current_step
