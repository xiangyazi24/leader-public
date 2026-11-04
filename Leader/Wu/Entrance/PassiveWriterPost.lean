import Leader.Wu.Entrance.PassivePost
import Leader.Wu.Entrance.PassiveProjection
import Leader.Wu.Entrance.CheckWriteStateFrame
import Leader.Wu.Entrance.WriterSilence
import Leader.Wu.Coherence.WriterLease
import Leader.Wu.WriteSeq.WriterProducerRepair

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthLeaderlessBirthMassRenewal
open WriterProducerRepair BirthStationaryWrite

variable {n ψ κ τ width : Nat}

attribute [local irreducible]
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  BirthCheckPermitRepair.permitFix
  BirthShortDoneCuts.beforeWriteWidth
  PPLLLeaderCreationCleanupRepair.markLeaderBirth
  WriterProducerRepair.stationaryProducerRow

/-- The three fields occurring literally in `FinalWriterPassive`, at the
bounded core used immediately around the R2 writer. -/
def BoundedWriterPassive (u : BoundedAgentState ψ κ) : Prop :=
  u.path3 = none ∧
    u.write = .none ∧
    (u.write_state = .none ∨ u.write_state = .depart)

/-- A passive writer cell is not a lease producer. -/
theorem producerActive_false_of_boundedWriterPassive
    (u : BoundedAgentState ψ κ) (h : BoundedWriterPassive u) :
    producerActive u = false := by
  rcases h with ⟨_hp, _hw, hs | hs⟩
  · simp [producerActive, hs]
  · simp [producerActive, hs]

/-- Consequently `R2F.tick` may zero fuel, but cannot change the resident
agent on a writer-passive cell. -/
theorem tick_agent_eq_of_boundedWriterPassive
    (u : R2F.WCell ψ κ) (h : BoundedWriterPassive u.agent.core) :
    (R2F.tick u).agent = u.agent := by
  have ha : producerActive u.agent.core = false :=
    producerActive_false_of_boundedWriterPassive u.agent.core h
  simp [R2F.tick, ha]

/-- The root-start half of the producer guard is also false for a follower. -/
theorem producerStarts_false_of_follower_local
    (u : BoundedAgentState ψ κ) (h : u.leader = false) :
    producerStarts u = false := by
  simp [producerStarts, h]

/-- Exact remaining writer-stage fact needed for B4 passive closure.

This is deliberately a named Prop on the literal stationary persistent writer,
not on `stationaryProducerMainComparisonFrame`: the latter omits all three
writer fields.  `B6WriterSilence` already supplies the `path3 = none` part;
the missing work is the strict `write/.write_state` part. -/
def StationaryPersistentWriterPassiveObligation
    (hψ : 0 < ψ) : Prop :=
  ∀ (l r : AuthorizedBoundedAgentState ψ κ),
    l.core.leader = false →
    BoundedWriterPassive l.core →
    BoundedWriterPassive r.core →
    let q := stationaryPersistentBoundedRow hψ l r
    BoundedWriterPassive q.1.core ∧
      BoundedWriterPassive q.2.core

/-- Equivalent R2F-facing formulation.  Passive inputs make the
`producerActive || producerActive || producerStarts` guard false, so proving
this reduces to `StationaryPersistentWriterPassiveObligation`. -/
def StationaryProducerWriterPassiveObligation
    (hψ : 0 < ψ) : Prop :=
  ∀ (l r : R2F.WCell ψ κ),
    l.agent.core.leader = false →
    BoundedWriterPassive l.agent.core →
    BoundedWriterPassive r.agent.core →
    let q := R2F.stationaryProducerRow hψ l r
    BoundedWriterPassive q.1.agent.core ∧
      BoundedWriterPassive q.2.agent.core

/-- Public spelling of the body hidden by the actual q13267 CHECK cut. -/
private def q13818_checkedPublic
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
      hψ hw hle κ l.erase r.erase
  let hq :=
    BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth_domain
      (κ := κ) hψ hw hle l.erase r.erase
      l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (R2.ofAuth q.1 hq.1, R2.ofAuth q.2 hq.2)

private def q13818_permitPublic
    (u : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ :=
  let f : AuthorizedAgentState ψ :=
    BirthCheckPermitRepair.permitFix u.erase
  let hf : f.core.inProtocolDomain κ := by
    change (BirthCheckPermitRepair.permitFix u.erase).core.inProtocolDomain κ
    rw [BirthCheckPermitRepair.permitFix_core]
    exact u.core.erase_inProtocolDomain
  R2.ofAuth f hf

/-- Everything before the stationary writer now has the required public
certificates.  These aliases make the intended splice explicit without
re-unfolding the enormous CHECK prefix. -/
theorem checked_writeState_frame
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let c := q13818_checkedPublic hψ hw hle l r
    c.1.core.write_state = l.core.write_state ∧
      c.2.core.write_state = r.core.write_state := by
  exact R2.q13267_checkedBounded_writeState
    (κ := κ) hψ hw hle l r

/-- Permit carries all three writer fields because it carries the whole core. -/
theorem permit_core_frame
    (u : AuthorizedBoundedAgentState ψ κ) :
    (q13818_permitPublic u).core = u.core := by
  exact R2.q13267_permitBounded_core (κ := κ) u


/-- The public path3 certificate through the actual R1 pre-writer cut. -/
theorem preWriter_path3_frame
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (cap : Nat) (l r : AuthorizedAgentState ψ) :
    let q := B6WriterSilence.r1WriterInput hψ hw hle cap l r
    q.1.core.path3 = l.core.path3 ∧
      q.2.core.path3 = r.core.path3 := by
  have h := B6WriterSilence.r1WriterInput_fields
    hψ hw hle cap l r
  exact ⟨h.2.2.1, h.2.2.2⟩

/-
To finish `finalWriterPassive_stepConcrete` without adding a false premise,
prove `StationaryPersistentWriterPassiveObligation` (or directly the R2F form)
from `stationaryPersistentBoundedRow` / `stationaryPersistentRaw`.

The required proof should use the already-public
  B6WriterSilence.stationaryPersistentAuthorizedRow_empty_of_left_follower
for the `path3 = none` coordinates and then do the small remaining writer
substage case split for `write` and `write_state`.  With passive inputs the
producer lease branch is already disabled by the lemmas above.

After that seam is public, the q13267 mark cut and the row tail can be composed,
and `stepConcrete_base_eq_step1_of_passive_admitted` lifts the resulting bare-R1
postcondition back to the concrete HOST step.  I do not claim that composition
here because it would hide the only missing semantic lemma behind a hypothesis.
-/

end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
