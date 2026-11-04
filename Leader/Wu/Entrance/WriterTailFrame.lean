import Leader.Wu.Entrance.WriterTailComposition
import Leader.Wu.Entrance.WriterLanePrepare
import Leader.Wu.Entrance.WriterLaneAction
import Leader.Wu.Entrance.WriterPipelineBridge

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6WriterTailFrame

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLWriteIncrementGate
  PPLLWriteSeqPersistenceRepair
open BirthStationaryWrite BirthShortDoneTerminalHost
open B6WriterPremiseStage1 B6WriterPremiseStage2
  B6MicroAlg18Disabled B6PreWriterFramesA B6PreWriterFramesC

variable {ψ width : Nat}

attribute [local irreducible]
  stationaryPersistentAuthorizedRow rowPreWriterInput
  algorithm18Input writeSeqGenerate
  swPersistentThroughPrepare stationaryPersistentRaw
  writeSeqPrepareTransport writeSeqAfterPrepareComparisonTransport
  gatePreparedIncrement writeActionPreservingComparison moveWsigStopAligned

/-- The two lane files use definitionally identical tiny idle predicates. -/
private theorem rightIdleA_to_B (u : AgentState ψ)
    (h : B6WriterLanesA.RightIdle u) :
    B6WriterLanesB.RightIdle u := by
  have h3 : u.path3 = none := h.1
  have hw : u.write = .none := h.2.1
  have hs : u.write_state = .none := h.2.2
  exact ⟨h3, hw, hs⟩

/-- The missing writer tail is the proved prepare/gate lane followed by the
    proved action/move lane.  The actual writer row is connected only through
    `B6WriterOpaqueBridge`; no writer definition is unfolded here. -/
theorem missingWriterTailFrame (hψ : 0 < ψ) :
    B6WriterCompose.MissingWriterTailFrameAt hψ := by
  intro l r _hl hr h18
  let q := algorithm18Input hψ l r
  let a := writeSeqGenerate hψ q.1 q.2
  have hi :
      B6WriterLanesA.RightIdle q.2 ∧ q.2.bit = r.core.bit := by
    exact B6WriterLanesA.algorithm18Input_right_idle hψ l r hr
  have h18' :
      a.2.path3 = q.2.path3 ∧
        a.2.write = q.2.write ∧
        a.2.write_state = q.2.write_state ∧
        a.2.bit = q.2.bit := by
    exact h18
  have hq3 : q.2.path3 = none := hi.1.1
  have hqw : q.2.write = .none := hi.1.2.1
  have hqs : q.2.write_state = .none := hi.1.2.2
  have haIdle : B6WriterLanesA.RightIdle a.2 := by
    exact ⟨h18'.1.trans hq3,
      h18'.2.1.trans hqw,
      h18'.2.2.1.trans hqs⟩
  have haBit : a.2.bit = r.core.bit := by
    exact h18'.2.2.2.trans hi.2

  let p := writeSeqPrepareTransport hψ a.1 a.2
  have hp :
      B6WriterLanesA.RightIdle p.2 ∧ p.2.bit = a.2.bit := by
    exact B6WriterLanesA.prepare_right_idle hψ a.1 a.2 haIdle

  let gl := gatePreparedIncrement p.1
  let gr := gatePreparedIncrement p.2
  have hg :
      B6WriterLanesA.RightIdle gr ∧ gr.bit = p.2.bit := by
    exact B6WriterLanesA.gate_right_idle p.2 hp.1
  have hgr : B6WriterLanesB.RightIdle gr := by
    exact rightIdleA_to_B gr hg.1

  let x := writeActionPreservingComparison hψ gl gr
  have hx :
      x.2.bit = gr.bit ∧
        (x.2.write_state = .none ∨ x.2.write_state = .depart) := by
    exact B6WriterLanesB.action_right_safe hψ gl gr hgr

  let m := moveWsigStopAligned hψ x.1 x.2
  have hm :
      m.2.bit = x.2.bit ∧
        (m.2.write_state = .none ∨ m.2.write_state = .depart) := by
    exact B6WriterLanesB.move_right_safe hψ x.1 x.2 hx.2
  have hb : m.2.bit = r.core.bit := by
    exact hm.1.trans
      (hx.1.trans (hg.2.trans (hp.2.trans haBit)))

  have hout :
      (stationaryPersistentAuthorizedRow hψ l r).2.core = m.2 := by
    exact B6WriterOpaqueBridge.stationaryPersistentAuthorizedRow_right_core_eq_pipeline
      hψ l r
  have houtBit :
      (stationaryPersistentAuthorizedRow hψ l r).2.core.bit = m.2.bit := by
    exact congrArg (fun u : AgentState ψ => u.bit) hout
  have houtState :
      (stationaryPersistentAuthorizedRow hψ l r).2.core.write_state =
        m.2.write_state := by
    exact congrArg (fun u : AgentState ψ => u.write_state) hout
  have hfinalBit :
      (stationaryPersistentAuthorizedRow hψ l r).2.core.bit =
        r.core.bit := by
    exact houtBit.trans hb
  have hfinalState :
      (stationaryPersistentAuthorizedRow hψ l r).2.core.write_state = .none ∨
        (stationaryPersistentAuthorizedRow hψ l r).2.core.write_state = .depart := by
    rcases hm.2 with hn | hd
    · exact Or.inl (houtState.trans hn)
    · exact Or.inr (houtState.trans hd)
  exact ⟨hfinalBit, hfinalState⟩

/-- B6 micro 3c-2 with the writer-tail premise discharged. -/
theorem stage3_writer_output_responder_frame
    (hψ : 0 < ψ)
    (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) (h : Stage3PreparedHypotheses l r) :
    let w := rowPreWriterInput hψ hwidth hle κ l r
    let w' := stationaryPersistentAuthorizedRow hψ w.1 w.2
    w'.2.core.bit = r.core.bit ∧
      (w'.2.core.write_state = .none ∨
        w'.2.core.write_state = .depart) := by
  exact B6WriterCompose.stage3_writer_output_responder_frame
    hψ (missingWriterTailFrame hψ) hwidth hle κ l r h

end B6WriterTailFrame

#print axioms B6WriterTailFrame.missingWriterTailFrame
#print axioms B6WriterTailFrame.stage3_writer_output_responder_frame
