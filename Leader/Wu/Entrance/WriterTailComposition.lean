import Leader.Wu.Entrance.WriterPipelineBridge

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6WriterCompose

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLWriteIncrementGate
  PPLLWriteSeqPersistenceRepair
open BirthStationaryWrite BirthShortDoneTerminalHost
open B6WriterPremiseStage1 B6WriterPremiseStage2
  B6MicroAlg18Disabled B6PreWriterFramesA B6PreWriterFramesC

variable {ψ κ width : Nat}

attribute [local irreducible]
  stationaryPersistentAuthorizedRow rowPreWriterInput
  algorithm18Input writeSeqGenerate
  swPersistentThroughPrepare stationaryPersistentRaw
  writeSeqPrepareTransport writeSeqAfterPrepareComparisonTransport
  gatePreparedIncrement writeActionPreservingComparison moveWsigStopAligned

/-- Missing public writer seam.  Algorithm 18 itself is already framed by
`algorithm18_responder_writer_fields_unchanged`; this hypothesis packages only
the still-unexported responder-bit/writer-state transport through the remaining
stationary writer and its authorized wrapper. -/
def MissingWriterTailFrameAt {ψ : Nat} (hψ : 0 < ψ) : Prop :=
  ∀ (l r : AuthorizedAgentState ψ),
    MissingLeftFollowerConjunct l ->
    PreparedResponderWriterPremise r ->
    (let q := algorithm18Input hψ l r
     let a := writeSeqGenerate hψ q.1 q.2
     a.2.path3 = q.2.path3 ∧
       a.2.write = q.2.write ∧
       a.2.write_state = q.2.write_state ∧
       a.2.bit = q.2.bit) ->
    (let out := stationaryPersistentAuthorizedRow hψ l r
     out.2.core.bit = r.core.bit ∧
       (out.2.core.write_state = .none ∨
         out.2.core.write_state = .depart))

/-- Pure-composition form of B6 micro 3c-2.  No writer stage is unfolded. -/
theorem stage3_writer_output_responder_frame
    (hψ : 0 < ψ)
    (hWriterTail : MissingWriterTailFrameAt hψ)
    (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) (h : Stage3PreparedHypotheses l r) :
    let w := rowPreWriterInput hψ hwidth hle κ l r
    let w' := stationaryPersistentAuthorizedRow hψ w.1 w.2
    w'.2.core.bit = r.core.bit ∧
      (w'.2.core.write_state = .none ∨
        w'.2.core.write_state = .depart) := by
  let w := rowPreWriterInput hψ hwidth hle κ l r
  have hi :
      w.1.core.leader = false ∧
        w.2.core.path3 = none ∧
        w.2.core.write = .none ∧
        w.2.core.write_state = .none := by
    exact stage3_writer_input_idle hψ hwidth hle κ l r h
  have hb : w.2.core.bit = r.core.bit := by
    exact B6WriterOpaqueBridge.rowPreWriterInput_right_bit
      hψ hwidth hle κ l r
  have hl : MissingLeftFollowerConjunct w.1 := by
    exact hi.1
  have hr : PreparedResponderWriterPremise w.2 := by
    exact ⟨hi.2.1, hi.2.2.1, hi.2.2.2⟩
  have h18 :
      (let q := algorithm18Input hψ w.1 w.2
       let a := writeSeqGenerate hψ q.1 q.2
       a.2.path3 = q.2.path3 ∧
         a.2.write = q.2.write ∧
         a.2.write_state = q.2.write_state ∧
         a.2.bit = q.2.bit) := by
    exact algorithm18_responder_writer_fields_unchanged hψ w.1 w.2 hl
  have hw :
      (let out := stationaryPersistentAuthorizedRow hψ w.1 w.2
       out.2.core.bit = w.2.core.bit ∧
         (out.2.core.write_state = .none ∨
           out.2.core.write_state = .depart)) := by
    exact hWriterTail w.1 w.2 hl hr h18
  have hwBit :
      (stationaryPersistentAuthorizedRow hψ w.1 w.2).2.core.bit =
        w.2.core.bit := by
    exact hw.1
  have hwState :
      (stationaryPersistentAuthorizedRow hψ w.1 w.2).2.core.write_state = .none ∨
        (stationaryPersistentAuthorizedRow hψ w.1 w.2).2.core.write_state = .depart := by
    exact hw.2
  have houtBit :
      (stationaryPersistentAuthorizedRow hψ w.1 w.2).2.core.bit =
        r.core.bit := by
    exact hwBit.trans hb
  exact ⟨houtBit, hwState⟩

end B6WriterCompose

#print axioms B6WriterCompose.stage3_writer_output_responder_frame
