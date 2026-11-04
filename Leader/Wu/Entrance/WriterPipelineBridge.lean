import Leader.Wu.Entrance.PreWriterFramesCheck
import Leader.Wu.Entrance.WriteSeqGenerateDisabled

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6WriterOpaqueBridge

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

/-- Recover the responder bit from the already-proved pre-writer frame without
    unfolding `rowPreWriterInput`. -/
theorem rowPreWriterInput_right_bit
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    (rowPreWriterInput hψ hwidth hle κ l r).2.core.bit = r.core.bit := by
  have hf :
      PreWriterFrame (rowPreWriterInput hψ hwidth hle κ l r) =
        PreWriterFrame (l, r) := by
    exact rowPreWriterInput_frame hψ hwidth hle κ l r
  have hb :
      (PreWriterFrame (rowPreWriterInput hψ hwidth hle κ l r)).rightBit =
        (PreWriterFrame (l, r)).rightBit := by
    exact congrArg PreWriterFrameView.rightBit hf
  exact hb

/-- One-definition bridge: expose only `algorithm18Input`. -/
theorem algorithm18Input_eq_prefix
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    algorithm18Input hψ l r =
      groupInfo hψ
        (clearInputIncrementPair l.core r.core).1
        (clearInputIncrementPair l.core r.core).2 := by
  unfold algorithm18Input
  rfl

/-- One-definition bridge: expose only `swPersistentThroughPrepare`. -/
theorem swPersistentThroughPrepare_eq_pipeline
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    swPersistentThroughPrepare hψ l.core r.core =
      (let q := algorithm18Input hψ l r
       let a := writeSeqGenerate hψ q.1 q.2
       writeSeqPrepareTransport hψ a.1 a.2) := by
  let g := groupInfo hψ
    (clearInputIncrementPair l.core r.core).1
    (clearInputIncrementPair l.core r.core).2
  have hq : algorithm18Input hψ l r = g := by
    exact algorithm18Input_eq_prefix hψ l r
  have h0 :
      swPersistentThroughPrepare hψ l.core r.core =
        (let a := writeSeqGenerate hψ g.1 g.2
         writeSeqPrepareTransport hψ a.1 a.2) := by
    unfold swPersistentThroughPrepare
    rfl
  have h1 :
      (let a := writeSeqGenerate hψ g.1 g.2
       writeSeqPrepareTransport hψ a.1 a.2) =
        (let q := algorithm18Input hψ l r
         let a := writeSeqGenerate hψ q.1 q.2
         writeSeqPrepareTransport hψ a.1 a.2) := by
    exact congrArg
      (fun z : AgentState ψ × AgentState ψ =>
        let a := writeSeqGenerate hψ z.1 z.2
        writeSeqPrepareTransport hψ a.1 a.2)
      hq.symm
  exact h0.trans h1

/-- One-definition bridge: expose only the Algorithm-19/20 suffix wrapper. -/
theorem writeSeqAfterPrepareComparisonTransport_eq_pipeline
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    writeSeqAfterPrepareComparisonTransport hψ l r =
      (let x := writeActionPreservingComparison hψ l r
       moveWsigStopAligned hψ x.1 x.2) := by
  unfold writeSeqAfterPrepareComparisonTransport
  rfl

/-- One-definition bridge: expose only `stationaryPersistentRaw`; all inner
    writer stages stay opaque and are connected by the two bridge lemmas above. -/
theorem stationaryPersistentRaw_eq_pipeline
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    let q := algorithm18Input hψ l r
    let a := writeSeqGenerate hψ q.1 q.2
    let p := writeSeqPrepareTransport hψ a.1 a.2
    let gl := gatePreparedIncrement p.1
    let gr := gatePreparedIncrement p.2
    let x := writeActionPreservingComparison hψ gl gr
    let m := moveWsigStopAligned hψ x.1 x.2
    stationaryPersistentRaw hψ l.core r.core = m := by
  let q := algorithm18Input hψ l r
  let a := writeSeqGenerate hψ q.1 q.2
  let p := writeSeqPrepareTransport hψ a.1 a.2
  let gl := gatePreparedIncrement p.1
  let gr := gatePreparedIncrement p.2
  let x := writeActionPreservingComparison hψ gl gr
  let m := moveWsigStopAligned hψ x.1 x.2
  have hp : swPersistentThroughPrepare hψ l.core r.core = p := by
    exact swPersistentThroughPrepare_eq_pipeline hψ l r
  have h0 :
      stationaryPersistentRaw hψ l.core r.core =
        writeSeqAfterPrepareComparisonTransport hψ
          (gatePreparedIncrement (swPersistentThroughPrepare hψ l.core r.core).1)
          (gatePreparedIncrement (swPersistentThroughPrepare hψ l.core r.core).2) := by
    unfold stationaryPersistentRaw
    rfl
  have h1 :
      writeSeqAfterPrepareComparisonTransport hψ
          (gatePreparedIncrement (swPersistentThroughPrepare hψ l.core r.core).1)
          (gatePreparedIncrement (swPersistentThroughPrepare hψ l.core r.core).2) =
        writeSeqAfterPrepareComparisonTransport hψ gl gr := by
    exact congrArg
      (fun z : AgentState ψ × AgentState ψ =>
        writeSeqAfterPrepareComparisonTransport hψ
          (gatePreparedIncrement z.1) (gatePreparedIncrement z.2))
      hp
  have h2 : writeSeqAfterPrepareComparisonTransport hψ gl gr = m := by
    exact writeSeqAfterPrepareComparisonTransport_eq_pipeline hψ gl gr
  exact h0.trans (h1.trans h2)

/-- The public authorized row has exactly the same responder core as the opaque
    raw pipeline above.  No authorized-row definition is unfolded here. -/
theorem stationaryPersistentAuthorizedRow_right_core_eq_pipeline
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    let q := algorithm18Input hψ l r
    let a := writeSeqGenerate hψ q.1 q.2
    let p := writeSeqPrepareTransport hψ a.1 a.2
    let gl := gatePreparedIncrement p.1
    let gr := gatePreparedIncrement p.2
    let x := writeActionPreservingComparison hψ gl gr
    let m := moveWsigStopAligned hψ x.1 x.2
    (stationaryPersistentAuthorizedRow hψ l r).2.core = m.2 := by
  let q := algorithm18Input hψ l r
  let a := writeSeqGenerate hψ q.1 q.2
  let p := writeSeqPrepareTransport hψ a.1 a.2
  let gl := gatePreparedIncrement p.1
  let gr := gatePreparedIncrement p.2
  let x := writeActionPreservingComparison hψ gl gr
  let m := moveWsigStopAligned hψ x.1 x.2
  have hc :
      ((stationaryPersistentAuthorizedRow hψ l r).1.core,
        (stationaryPersistentAuthorizedRow hψ l r).2.core) =
        stationaryPersistentRaw hψ l.core r.core := by
    exact stationaryPersistentAuthorizedRow_core hψ l r
  have hcR :
      (stationaryPersistentAuthorizedRow hψ l r).2.core =
        (stationaryPersistentRaw hψ l.core r.core).2 := by
    exact congrArg (fun z : AgentState ψ × AgentState ψ => z.2) hc
  have hraw : stationaryPersistentRaw hψ l.core r.core = m := by
    exact stationaryPersistentRaw_eq_pipeline hψ l r
  have hrawR : (stationaryPersistentRaw hψ l.core r.core).2 = m.2 := by
    exact congrArg (fun z : AgentState ψ × AgentState ψ => z.2) hraw
  exact hcR.trans hrawR

end B6WriterOpaqueBridge

#print axioms B6WriterOpaqueBridge.rowPreWriterInput_right_bit
#print axioms B6WriterOpaqueBridge.stationaryPersistentAuthorizedRow_right_core_eq_pipeline
