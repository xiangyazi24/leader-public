import Leader.Wu.WriteSeq.StationaryWriteBitIdle
import Leader.Wu.Safety.PermitRepairQuietLapWriterPassive

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
open BirthStationaryWrite

variable {ψ κ : Nat}

attribute [local irreducible]
  BirthStationaryWrite.stationaryPersistentBoundedRow
  BirthStationaryWrite.stationaryPersistentAuthorizedRow
  BirthStationaryWrite.stationaryPersistentRaw

private theorem rawPassive_of_boundedWriterPassive
    (u : BoundedAgentState ψ κ) (h : BoundedWriterPassive u) :
    R1CandidatePrime.WriterPassive u.erase := by
  simpa [BoundedWriterPassive, R1CandidatePrime.WriterPassive,
    BoundedAgentState.erase] using h

private theorem rawFollower_of_boundedFollower
    (u : BoundedAgentState ψ κ) (h : u.leader = false) :
    u.erase.leader = false := by
  simpa [BoundedAgentState.erase] using h

theorem stationaryPersistentBoundedRow_writerPassive
    (hψ : 0 < ψ)
    (l r :
      PPLLAuthorizedComparisonRepair.AuthorizedBoundedAgentState ψ κ)
    (hLead : l.core.leader = false)
    (hl : BoundedWriterPassive l.core)
    (hr : BoundedWriterPassive r.core) :
    let q := stationaryPersistentBoundedRow hψ l r
    BoundedWriterPassive q.1.core ∧
      BoundedWriterPassive q.2.core := by
  have hraw :=
    R1CandidatePrime.stationary_follower_writerPassive
      hψ l.core.erase r.core.erase
      (rawFollower_of_boundedFollower l.core hLead)
      (rawPassive_of_boundedWriterPassive l.core hl)
      (rawPassive_of_boundedWriterPassive r.core hr)

  let q := stationaryPersistentBoundedRow hψ l r
  have he := stationaryPersistentBoundedRow_erase hψ l r
  have heCore :=
    congrArg
      (fun z :
          PPLLAuthorizedComparisonRepair.AuthorizedAgentState ψ ×
            PPLLAuthorizedComparisonRepair.AuthorizedAgentState ψ =>
        (z.1.core, z.2.core))
      he
  have heCore' :
      (q.1.core.erase, q.2.core.erase) =
        ((stationaryPersistentAuthorizedRow hψ l.erase r.erase).1.core,
          (stationaryPersistentAuthorizedRow hψ l.erase r.erase).2.core) := by
    simpa [q,
      PPLLAuthorizedComparisonRepair.AuthorizedBoundedAgentState.erase] using
      heCore

  have hc := stationaryPersistentAuthorizedRow_core hψ l.erase r.erase
  have hc' :
      ((stationaryPersistentAuthorizedRow hψ l.erase r.erase).1.core,
        (stationaryPersistentAuthorizedRow hψ l.erase r.erase).2.core) =
        stationaryPersistentRaw hψ l.core.erase r.core.erase := by
    simpa [PPLLAuthorizedComparisonRepair.AuthorizedBoundedAgentState.erase]
      using hc

  have hout :
      (q.1.core.erase, q.2.core.erase) =
        stationaryPersistentRaw hψ l.core.erase r.core.erase :=
    heCore'.trans hc'

  dsimp only at hraw
  have hL : R1CandidatePrime.WriterPassive q.1.core.erase := by
    have h1 := congrArg Prod.fst hout
    dsimp only at h1
    rw [h1]
    exact hraw.1
  have hR : R1CandidatePrime.WriterPassive q.2.core.erase := by
    have h2' := congrArg Prod.snd hout
    dsimp only at h2'
    rw [h2']
    exact hraw.2

  change BoundedWriterPassive q.1.core ∧
    BoundedWriterPassive q.2.core
  constructor
  · simpa [BoundedWriterPassive, R1CandidatePrime.WriterPassive,
      BoundedAgentState.erase] using hL
  · simpa [BoundedWriterPassive, R1CandidatePrime.WriterPassive,
      BoundedAgentState.erase] using hR

theorem stationaryPersistentBoundedRow_strict_writer_fields
    (hψ : 0 < ψ)
    (l r :
      PPLLAuthorizedComparisonRepair.AuthorizedBoundedAgentState ψ κ)
    (hLead : l.core.leader = false)
    (hl : BoundedWriterPassive l.core)
    (hr : BoundedWriterPassive r.core) :
    let q := stationaryPersistentBoundedRow hψ l r
    q.1.core.write = .none ∧
      (q.1.core.write_state = .none ∨
        q.1.core.write_state = .depart) ∧
      q.2.core.write = .none ∧
      (q.2.core.write_state = .none ∨
        q.2.core.write_state = .depart) := by
  have h := stationaryPersistentBoundedRow_writerPassive
    hψ l r hLead hl hr
  dsimp only at h ⊢
  exact ⟨h.1.2.1, h.1.2.2, h.2.2.1, h.2.2.2⟩

theorem stationaryPersistentWriterPassiveObligation_holds
    (hψ : 0 < ψ) :
    StationaryPersistentWriterPassiveObligation (κ := κ) hψ := by
  unfold StationaryPersistentWriterPassiveObligation
  intro l r hLead hl hr
  exact stationaryPersistentBoundedRow_writerPassive
    hψ l r hLead hl hr

end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
