import Leader.Wu.Birth.ShortDoneTerminalOpenMatchedHandoffCounterexample
import Leader.Wu.Birth.ShortDoneTerminalOpenMatchedHandoffFlagOneCounterexample
import Leader.Wu.Entrance.WriterScopeFixtures
import Leader.Wu.Birth.FirstLeaderComposition


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B6WriterPremiseStage1


open PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair BirthGenerationDone


variable {ψ κ τ : Nat}


/-! ## 1. Exact prepared-responder premise -/


/-- The corrected B6 writer premise, stated directly on the prepared
responder.  All three writer coordinates must be idle. -/
def PreparedResponderWriterPremise
    (r : AuthorizedAgentState ψ) : Prop :=
  r.core.path3 = none ∧
    r.core.write = .none ∧
    r.core.write_state = .none


instance instDecidablePreparedResponderWriterPremiseLocal (r : AuthorizedAgentState ψ) :
    Decidable (PreparedResponderWriterPremise r) := by
  unfold PreparedResponderWriterPremise
  (try dsimp only)
  infer_instance

/-- `BirthPhaseFirstLeaderComposition.CorrectedWriterPremiseAt` is exactly the
pullback of `PreparedResponderWriterPremise` through `prepareExpiringDisposal`.
There is no strengthening or weakening here. -/
theorem preparedWriterPremise_agrees_with_composition
    (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    PreparedResponderWriterPremise
        ((prepareExpiringDisposal hψ u).core.erase) ↔
      BirthPhaseFirstLeaderComposition.CorrectedWriterPremiseAt hψ u := by
  rfl


/-! ## 2. Literal responder records from the five certified witnesses


The source leaves keep their concrete responder constants private.  These are
the same raw responder records, restated here so that the five premise checks
can be exported from one importable Stage-1 file.
-/


private theorem onePos : 0 < 1 := by decide


private def peace1 (j : Fin 1) : PeaceView 1 :=
  { leader := false
    label := j
    shield := false
    bullet := 0
    signal_B := 0 }


private def rawBase (j : Fin 1) : AgentState 1 :=
  PeaceView.toState (peace1 j)


/-- Flag-zero `path3`, which later generates increment. -/
private def flagZeroGeneratedIncrementRaw : AgentState 1 :=
  { rawBase 0 with
      path3 := some ⟨0, 0, 0⟩ }


/-- Flag-one `path3` and resident bit one, which later selects
fresh overwrite. -/
private def flagOneGeneratedOverwriteRaw : AgentState 1 :=
  { rawBase 0 with
      bit := true
      path3 := some ⟨0, 0, 1⟩ }


/-- Overwrite is already the active writer state. -/
private def activeOverwriteRaw : AgentState 1 :=
  { flagOneGeneratedOverwriteRaw with
      write_state := .overwrite }


/-- Overwrite is already queued while the writer is in departure. -/
private def queuedOverwriteRaw : AgentState 1 :=
  { flagOneGeneratedOverwriteRaw with
      write_state := .depart
      write := .overwrite }


/-- Increment is already the active writer state. -/
private def activeIncrementRaw : AgentState 1 :=
  { flagOneGeneratedOverwriteRaw with
      write_state := .increment_group }


private theorem flagZeroGeneratedIncrementRawDomain :
    flagZeroGeneratedIncrementRaw.inProtocolDomain 0 := by
  simp [flagZeroGeneratedIncrementRaw, rawBase, peace1,
    PeaceView.toState, AgentState.inProtocolDomain]


private theorem flagOneGeneratedOverwriteRawDomain :
    flagOneGeneratedOverwriteRaw.inProtocolDomain 0 := by
  simp [flagOneGeneratedOverwriteRaw, rawBase, peace1,
    PeaceView.toState, AgentState.inProtocolDomain]


private theorem activeOverwriteRawDomain :
    activeOverwriteRaw.inProtocolDomain 0 := by
  simp [activeOverwriteRaw, flagOneGeneratedOverwriteRaw,
    rawBase, peace1, PeaceView.toState, AgentState.inProtocolDomain]


private theorem queuedOverwriteRawDomain :
    queuedOverwriteRaw.inProtocolDomain 0 := by
  simp [queuedOverwriteRaw, flagOneGeneratedOverwriteRaw,
    rawBase, peace1, PeaceView.toState, AgentState.inProtocolDomain]


private theorem activeIncrementRawDomain :
    activeIncrementRaw.inProtocolDomain 0 := by
  simp [activeIncrementRaw, flagOneGeneratedOverwriteRaw,
    rawBase, peace1, PeaceView.toState, AgentState.inProtocolDomain]


private def packZeroStall
    (u : AgentState 1) (hu : u.inProtocolDomain 0) :
    ExpiringAgentState 1 0 1 :=
  ⟨⟨BoundedAgentState.ofDomain u hu, false⟩, 0⟩


private def packFreshStall
    (u : AgentState 1) (hu : u.inProtocolDomain 0) :
    ExpiringAgentState 1 0 1 :=
  ⟨⟨BoundedAgentState.ofDomain u hu, false⟩, freshStall 1⟩


/-- Exact responder input from the flag-zero witness. -/
private def flagZeroGeneratedIncrementInput : ExpiringAgentState 1 0 1 :=
  packZeroStall
    flagZeroGeneratedIncrementRaw flagZeroGeneratedIncrementRawDomain


/-- Exact responder input from the flag-one overwrite witness. -/
private def flagOneGeneratedOverwriteInput : ExpiringAgentState 1 0 1 :=
  packFreshStall
    flagOneGeneratedOverwriteRaw flagOneGeneratedOverwriteRawDomain


/-- Exact responder input from `B6WriterScopeAudit.activeOverwrite_fullHost`. -/
private def activeOverwriteInput : ExpiringAgentState 1 0 1 :=
  packZeroStall activeOverwriteRaw activeOverwriteRawDomain


/-- Exact responder input from
`B6WriterScopeAudit.queuedOverwriteCommand_fullHost`. -/
private def queuedOverwriteInput : ExpiringAgentState 1 0 1 :=
  packZeroStall queuedOverwriteRaw queuedOverwriteRawDomain


/-- Exact responder input from
`B6WriterScopeAudit.activeIncrementState_fullHost`. -/
private def activeIncrementInput : ExpiringAgentState 1 0 1 :=
  packZeroStall activeIncrementRaw activeIncrementRawDomain


private def prepared
    (u : ExpiringAgentState 1 0 1) : AuthorizedAgentState 1 :=
  (prepareExpiringDisposal onePos u).core.erase


/-! ## 3. All five certified lanes violate the corrected premise -/


/-- Flag-zero generated increment: prepared `path3` is non-idle. -/
theorem flagZeroGeneratedIncrement_violates_premise :
    ¬ PreparedResponderWriterPremise
      (prepared flagZeroGeneratedIncrementInput) := by
  decide


/-- Flag-one generated overwrite: prepared `path3` is non-idle. -/
theorem flagOneGeneratedOverwrite_violates_premise :
    ¬ PreparedResponderWriterPremise
      (prepared flagOneGeneratedOverwriteInput) := by
  decide


/-- Pre-existing queued overwrite command: the corrected premise rejects the
prepared responder. -/
theorem queuedOverwriteCommand_violates_premise :
    ¬ PreparedResponderWriterPremise
      (prepared queuedOverwriteInput) := by
  decide


/-- Pre-existing active overwrite state: the corrected premise rejects the
prepared responder. -/
theorem activeOverwriteState_violates_premise :
    ¬ PreparedResponderWriterPremise
      (prepared activeOverwriteInput) := by
  decide


/-- Pre-existing active increment state: the corrected premise rejects the
prepared responder. -/
theorem activeIncrementState_violates_premise :
    ¬ PreparedResponderWriterPremise
      (prepared activeIncrementInput) := by
  decide


end B6WriterPremiseStage1


#print axioms B6WriterPremiseStage1.preparedWriterPremise_agrees_with_composition
#print axioms B6WriterPremiseStage1.flagZeroGeneratedIncrement_violates_premise
#print axioms B6WriterPremiseStage1.flagOneGeneratedOverwrite_violates_premise
#print axioms B6WriterPremiseStage1.queuedOverwriteCommand_violates_premise
#print axioms B6WriterPremiseStage1.activeOverwriteState_violates_premise
#print axioms B6WriterPremiseStage1.activeIncrementState_violates_premise
