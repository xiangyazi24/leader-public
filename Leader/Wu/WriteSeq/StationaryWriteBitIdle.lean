import Leader.Wu.WriteSeq.StationaryWrite
import Leader.Wu.Entrance.PassiveWriterPost


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C


open PPLL PPLLRepair PPLLDomain PPLLWriteIncrementGate
open PPLLWriteSeqPersistenceRepair
open BirthStationaryWrite WriterProducerRepair


variable {ψ κ : Nat}

section Q14347IrreducibleCuts

-- The barrier must cover the PERSISTENT stack this file actually uses; the
-- older `stationaryRaw` row does not occur here, so making it opaque changed
-- nothing and the result type at the bounded-row projection still drove the
-- kernel through the whole persistent writer pipeline.
attribute [local irreducible]
  BirthStationaryWrite.stationaryPersistentBoundedRow
  BirthStationaryWrite.stationaryPersistentAuthorizedRow
  BirthStationaryWrite.stationaryPersistentRaw


theorem stationaryPersistentRaw_bit_frame_of_passive
    (hψ : 0 < ψ) (l r : AgentState ψ)
    (hlLead : l.leader = false)
    (hl : l.path3 = none ∧ l.write = .none ∧
      (l.write_state = .none ∨ l.write_state = .depart))
    (hr : r.path3 = none ∧ r.write = .none ∧
      (r.write_state = .none ∨ r.write_state = .depart)) :
    let q := stationaryPersistentRaw hψ l r
    q.1.bit = l.bit ∧ q.2.bit = r.bit := by
  have h := B6WriterSilence.stationaryPersistentRaw_empty_of_left_follower
    hψ l r hlLead hl.1 hr.1
  dsimp only at h ⊢
  exact h.2.2


theorem stationaryPersistentBoundedRow_bit_frame
    (hψ : 0 < ψ)
    (l r : PPLLAuthorizedComparisonRepair.AuthorizedBoundedAgentState ψ κ)
    (hlLead : l.core.leader = false)
    (hl : BoundedWriterPassive l.core)
    (hr : BoundedWriterPassive r.core) :
    let q := stationaryPersistentBoundedRow hψ l r
    q.1.core.bit = l.core.bit ∧ q.2.core.bit = r.core.bit := by
  have ha := B6WriterSilence.stationaryPersistentAuthorizedRow_empty_of_left_follower
    hψ l.erase r.erase
    (by
      simpa [PPLLAuthorizedComparisonRepair.AuthorizedBoundedAgentState.erase,
        BoundedAgentState.erase] using hlLead)
    (by
      simpa [B6WriterSilence.EmptyWriter,
        PPLLAuthorizedComparisonRepair.AuthorizedBoundedAgentState.erase,
        BoundedAgentState.erase] using hl.1)
    (by
      simpa [B6WriterSilence.EmptyWriter,
        PPLLAuthorizedComparisonRepair.AuthorizedBoundedAgentState.erase,
        BoundedAgentState.erase] using hr.1)
  let q := stationaryPersistentBoundedRow hψ l r
  have he := stationaryPersistentBoundedRow_erase hψ l r
  dsimp only at ha ⊢
  have hb :
      ((stationaryPersistentAuthorizedRow hψ l.erase r.erase).1.core.bit,
       (stationaryPersistentAuthorizedRow hψ l.erase r.erase).2.core.bit) =
        (l.core.bit, r.core.bit) := by
    apply Prod.ext
    · simpa [PPLLAuthorizedComparisonRepair.AuthorizedBoundedAgentState.erase,
        BoundedAgentState.erase] using ha.2.2.1
    · simpa [PPLLAuthorizedComparisonRepair.AuthorizedBoundedAgentState.erase,
        BoundedAgentState.erase] using ha.2.2.2
  have hq :
      (q.1.core.bit, q.2.core.bit) =
        ((stationaryPersistentAuthorizedRow hψ l.erase r.erase).1.core.bit,
         (stationaryPersistentAuthorizedRow hψ l.erase r.erase).2.core.bit) := by
    have hp := congrArg
      (fun z : PPLLAuthorizedComparisonRepair.AuthorizedAgentState ψ ×
          PPLLAuthorizedComparisonRepair.AuthorizedAgentState ψ =>
        (z.1.core.bit, z.2.core.bit)) he
    simpa [q,
      PPLLAuthorizedComparisonRepair.AuthorizedBoundedAgentState.erase,
      BoundedAgentState.erase] using hp
  have h := hq.trans hb
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

end Q14347IrreducibleCuts

end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
