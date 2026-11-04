import Leader.Wu.Entrance.PreWriterFramesCheck
import Leader.Wu.Entrance.WriteSeqGenerateDisabled


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B6WriterLanesA


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLWriteIncrementGate
  PPLLWriteSeqPersistenceRepair
open BirthStationaryWrite BirthShortDoneTerminalHost
open B6WriterPremiseStage1 B6WriterPremiseStage2
  B6MicroAlg18Disabled B6PreWriterFramesA B6PreWriterFramesC


variable {ψ : Nat}


/-- Responder writer lane is completely idle. -/
def RightIdle (u : AgentState ψ) : Prop :=
  u.path3 = none ∧ u.write = .none ∧ u.write_state = .none


/-- The sanitation/GROUP_INFO input to Algorithm 18 preserves the prepared
responder's idle writer triple and physical bit. -/
theorem algorithm18Input_right_idle
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hr : PreparedResponderWriterPremise r) :
    let q := algorithm18Input hψ l r
    RightIdle q.2 ∧ q.2.bit = r.core.bit := by
  rcases hr with ⟨hp3, hw, hs⟩
  unfold algorithm18Input clearInputIncrementPair
  dsimp only
  have hc : clearIncrementAction r.core = r.core := by
    simp [clearIncrementAction, hw]
  rw [hc]
  simp [RightIdle, groupInfo, hp3, hw, hs]


/-- Algorithm-16 preparation preserves an idle responder writer lane and bit. -/
theorem prepare_right_idle
    (hψ : 0 < ψ) (l r : AgentState ψ) (hr : RightIdle r) :
    let q := writeSeqPrepareTransport hψ l r
    RightIdle q.2 ∧ q.2.bit = r.bit := by
  rcases hr with ⟨hp3, hw, hs⟩
  simp [writeSeqPrepareTransport, writeSeqReadyTransport,
    writeSeqSetWriteReadyTransport, writeSeqCompare, writeSeqCheckBit,
    writeSeqCommands, writeSeqSetWriteAct, writeSeqFinalR,
    RightIdle, hp3, hw, hs]


/-- The prepared-increment gate preserves an idle writer lane and bit. -/
theorem gate_right_idle
    (u : AgentState ψ) (h : RightIdle u) :
    RightIdle (gatePreparedIncrement u) ∧
      (gatePreparedIncrement u).bit = u.bit := by
  rcases h with ⟨hp3, hw, hs⟩
  simp [gatePreparedIncrement, clearIncrementAction,
    RightIdle, hp3, hw, hs]


end B6WriterLanesA


#print axioms B6WriterLanesA.algorithm18Input_right_idle
#print axioms B6WriterLanesA.prepare_right_idle
#print axioms B6WriterLanesA.gate_right_idle
