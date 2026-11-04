import Leader.Wu.Entrance.WriterTailFrame
import Leader.Wu.Entrance.PostWriterFrames
import Leader.Wu.Elimination.BirthDispatcherMetadata
import Leader.Wu.Birth.ShortDoneTerminalConsumer

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6WriterPremiseDischarge

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair
open BirthSigMoveDisposalRepair BirthShortDoneCuts BirthStationaryWrite
  BirthShortDoneTerminalHost
open B6WriterPremiseStage1 B6WriterPremiseStage2
  B6MicroAlg18Disabled B6PreWriterFramesC
open B6PostWriterThreading

variable {ψ κ τ width : Nat}

private theorem ordinaryMetadata_is_marked_writer_unfold
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    doneOrdinaryMetadataEntryWidth hψ hwidth hle κ
        (normalizeDeletion l) (normalizeDeletion r) =
      let w := B6PostWriterThreading.writerOutput hψ hwidth hle κ l r
      markLeaderBirth
        (K2BirthDispatcher.authBirth (normalizeDeletion l) (normalizeDeletion r) w) w := by
  rfl

attribute [local irreducible]
  stationaryPersistentAuthorizedRow rowPreWriterInput
  algorithm18Input writeSeqGenerate
  swPersistentThroughPrepare stationaryPersistentRaw
  writeSeqPrepareTransport writeSeqAfterPrepareComparisonTransport
  gatePreparedIncrement writeActionPreservingComparison moveWsigStopAligned
  B6PostWriterThreading.writerOutput

theorem missingWriterTailFrame (hψ : 0 < ψ) :
    B6WriterCompose.MissingWriterTailFrameAt hψ := by
  exact B6WriterTailFrame.missingWriterTailFrame hψ

theorem stage3_writer_output_responder_frame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) (h : Stage3PreparedHypotheses l r) :
    let w := rowPreWriterInput hψ hwidth hle κ l r
    let w' := stationaryPersistentAuthorizedRow hψ w.1 w.2
    w'.2.core.bit = r.core.bit ∧
      (w'.2.core.write_state = .none ∨ w'.2.core.write_state = .depart) := by
  exact B6WriterTailFrame.stage3_writer_output_responder_frame
    hψ hwidth hle κ l r h

private theorem writerOutput_eq_stage3
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    let w := rowPreWriterInput hψ hwidth hle κ l r
    B6PostWriterThreading.writerOutput hψ hwidth hle κ l r =
      stationaryPersistentAuthorizedRow hψ w.1 w.2 := by
  unfold B6PostWriterThreading.writerOutput
  rfl

theorem writerOutput_responder_frame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) (h : Stage3PreparedHypotheses l r) :
    (B6PostWriterThreading.writerOutput hψ hwidth hle κ l r).2.core.bit = r.core.bit ∧
      ((B6PostWriterThreading.writerOutput hψ hwidth hle κ l r).2.core.write_state = .none ∨
       (B6PostWriterThreading.writerOutput hψ hwidth hle κ l r).2.core.write_state = .depart) := by
  let w := rowPreWriterInput hψ hwidth hle κ l r
  let out := stationaryPersistentAuthorizedRow hψ w.1 w.2
  have hf : out.2.core.bit = r.core.bit ∧
      (out.2.core.write_state = .none ∨ out.2.core.write_state = .depart) := by
    exact B6WriterTailFrame.stage3_writer_output_responder_frame hψ hwidth hle κ l r h
  have heq : B6PostWriterThreading.writerOutput hψ hwidth hle κ l r = out := by
    exact writerOutput_eq_stage3 hψ hwidth hle κ l r
  have hb := congrArg
    (fun q : AuthorizedAgentState ψ × AuthorizedAgentState ψ => q.2.core.bit) heq
  have hs := congrArg
    (fun q : AuthorizedAgentState ψ × AuthorizedAgentState ψ => q.2.core.write_state) heq
  constructor
  · exact hb.trans hf.1
  · rcases hf.2 with hn | hd
    · exact Or.inl (hs.trans hn)
    · exact Or.inr (hs.trans hd)

def PostWriterRightGuards
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) : Prop :=
  let w := B6PostWriterThreading.writerOutput hψ hwidth hle κ l r
  K2BirthDispatcher.authBirth (normalizeDeletion l) (normalizeDeletion r) w = false ∧
    deletionActive w.2 = false ∧ w.2.core.leader = false

theorem postWriterRightHypotheses_of_stage3
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) (h : Stage3PreparedHypotheses l r)
    (hg : PostWriterRightGuards hψ hwidth hle κ l r) :
    PostWriterRightHypotheses hψ hwidth hle κ l r r.core.bit := by
  have hf := writerOutput_responder_frame hψ hwidth hle κ l r h
  unfold PostWriterRightGuards at hg
  unfold PostWriterRightHypotheses
  exact ⟨hg.1, hg.2.1, hg.2.2, hf.1⟩

private theorem ordinaryMetadata_is_marked_writer
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    doneOrdinaryMetadataEntryWidth hψ hwidth hle κ
        (normalizeDeletion l) (normalizeDeletion r) =
      let w := B6PostWriterThreading.writerOutput hψ hwidth hle κ l r
      markLeaderBirth
        (K2BirthDispatcher.authBirth (normalizeDeletion l) (normalizeDeletion r) w) w := by
  exact ordinaryMetadata_is_marked_writer_unfold hψ hwidth hle κ l r

private theorem row_right_bit_eq_metadata
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    (row hψ hwidth hle l r).2.core.erase.core.bit =
      (metadata hψ hwidth hle l r).2.core.core.bit := by
  unfold BirthShortDoneTerminalHost.row
  exact B6PostWriterThreading.finalPhysical_right_bit hψ l r _ _

theorem row_right_bit_of_stage3
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hstage : Stage3PreparedHypotheses
      (preparedEndpoint hψ l) (preparedEndpoint hψ r))
    (hguards : PostWriterRightGuards hψ hwidth hle κ
      (preparedEndpoint hψ l) (preparedEndpoint hψ r)) :
    (row hψ hwidth hle l r).2.core.erase.core.bit =
      (preparedEndpoint hψ r).core.bit := by
  let lp := preparedEndpoint hψ l
  let rp := preparedEndpoint hψ r
  let w := B6PostWriterThreading.writerOutput hψ hwidth hle κ lp rp
  have hg := hguards
  change K2BirthDispatcher.authBirth
      (normalizeDeletion lp) (normalizeDeletion rp) w = false ∧
    deletionActive w.2 = false ∧ w.2.core.leader = false at hg
  have hopen := stage3_priority_open lp rp hstage
  have hmeta : doneMetadataAuthorizedEntryWidth hψ hwidth hle κ lp rp = w := by
    have hom : doneOrdinaryMetadataEntryWidth hψ hwidth hle κ
        (normalizeDeletion lp) (normalizeDeletion rp) =
        markLeaderBirth
          (K2BirthDispatcher.authBirth (normalizeDeletion lp) (normalizeDeletion rp) w) w := by
      exact ordinaryMetadata_is_marked_writer hψ hwidth hle κ lp rp
    have hmark : markLeaderBirth
        (K2BirthDispatcher.authBirth (normalizeDeletion lp) (normalizeDeletion rp) w) w = w := by
      exact B6PostWriterThreading.markLeaderBirth_frame_of_no_birth _ w hg.1
    unfold doneMetadataAuthorizedEntryWidth
    dsimp only
    simp only [hopen.2, Bool.false_eq_true, if_false, hopen.1]
    exact hom.trans hmark
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let q := doneMetadataBoundedEntryWidth hψ hwidth hle l0.core r0.core
  have hr : q.2.erase = w.2 := by
    exact (B6PostWriterThreading.boundedReification_right_erase
      hψ hwidth hle l0.core r0.core).trans (congrArg Prod.snd hmeta)
  let baseR : ExpiringAgentState ψ κ τ := ⟨q.2, r0.stall⟩
  have hc : deletionActive baseR.core.erase = false := by
    change deletionActive q.2.erase = false
    rw [hr]
    exact hg.2.1
  have he := B6PostWriterThreading.deletionPriorityExpireOne_leader_bit_of_closed
    r0 baseR hc
  have hb := congrArg (fun u : AuthorizedAgentState ψ => u.core.bit) hr
  change q.2.core.bit = w.2.core.bit at hb
  have hentry : (doneMetadataEntryWidth hψ hwidth hle l r).2.core.core.bit = w.2.core.bit := by
    change (deletionPriorityExpireOne τ r0 baseR).core.core.bit = w.2.core.bit
    exact he.2.trans hb
  have hm := congrArg (fun u : ExpiringAgentState ψ κ τ => u.core.core.bit)
    (BirthShortDoneTerminalConsumer.metadata_field_frame hψ hwidth hle l r).2
  change (metadata hψ hwidth hle l r).2.core.core.bit =
    (doneMetadataEntryWidth hψ hwidth hle l r).2.core.core.bit at hm
  exact (row_right_bit_eq_metadata hψ hwidth hle l r).trans
    (hm.trans (hentry.trans
      (writerOutput_responder_frame hψ hwidth hle κ lp rp hstage).1))

theorem fullHostResponderBitPreservation_of_postWriterGuards
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hguards : PostWriterRightGuards hψ hwidth hle κ
      (preparedEndpoint hψ l) (preparedEndpoint hψ r)) :
    FullHostResponderBitPreservationStatement hψ hwidth hle l r := by
  intro hstage
  exact row_right_bit_of_stage3 hψ hwidth hle l r hstage hguards

end B6WriterPremiseDischarge

#print axioms B6WriterPremiseDischarge.missingWriterTailFrame
#print axioms B6WriterPremiseDischarge.stage3_writer_output_responder_frame
#print axioms B6WriterPremiseDischarge.writerOutput_responder_frame
#print axioms B6WriterPremiseDischarge.row_right_bit_of_stage3
#print axioms B6WriterPremiseDischarge.fullHostResponderBitPreservation_of_postWriterGuards
