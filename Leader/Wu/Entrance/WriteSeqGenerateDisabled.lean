import Leader.Wu.Entrance.WriterPremiseLeftFollower


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B6MicroAlg18Disabled


open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
open PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair
open BirthSigMoveDisposalRepair BirthStationaryWrite
open BirthShortDoneTerminalHost
open B6WriterPremiseStage1 B6WriterPremiseStage2


variable {ψ κ τ width : Nat}


/-- Exact input pair seen by Algorithm 18 inside the stationary persistent
writer: input-increment sanitation, then Algorithm 17 GROUP_INFO. -/
def algorithm18Input
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let q0 := clearInputIncrementPair l.core r.core
  groupInfo hψ q0.1 q0.2


private theorem clearIncrementAction_leader
    (u : AgentState ψ) :
    (clearIncrementAction u).leader = u.leader := by
  unfold clearIncrementAction
  split <;> rfl


private theorem groupInfo_left_leader
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    (groupInfo hψ l r).1.leader = l.leader := by
  exact congrArg (fun q => q.1.1)
    (BirthStationaryWrite.swGroupFrame hψ l r)


/-- The two stages before Algorithm 18 preserve the source-side leader bit. -/
private theorem algorithm18Input_left_leader
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    (algorithm18Input hψ l r).1.leader = l.core.leader := by
  unfold algorithm18Input
  dsimp only [clearInputIncrementPair]
  calc
    (groupInfo hψ
        (clearIncrementAction l.core)
        (clearIncrementAction r.core)).1.leader =
        (clearIncrementAction l.core).leader :=
      groupInfo_left_leader hψ
        (clearIncrementAction l.core)
        (clearIncrementAction r.core)
    _ = l.core.leader := clearIncrementAction_leader l.core


/-- Under the missing B6 source conjunct, the literal Algorithm-18 guard is
false at its actual stationary-writer input.  No responder-side premise is
needed for this local exclusion. -/
theorem algorithm18_guard_false_of_missingLeftFollower
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hleft : MissingLeftFollowerConjunct l) :
    ¬ ((algorithm18Input hψ l r).1.leader = true ∧
       (algorithm18Input hψ l r).1.gen_ws = true) := by
  change l.core.leader = false at hleft
  intro hguard
  have hleader : (algorithm18Input hψ l r).1.leader = false :=
    (algorithm18Input_left_leader hψ l r).trans hleft
  rw [hleader] at hguard
  cases hguard.1


/-- Algorithm 18 is therefore literally disabled: `writeSeqGenerate` returns
its input pair unchanged. -/
theorem writeSeqGenerate_disabled_of_missingLeftFollower
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hleft : MissingLeftFollowerConjunct l) :
    writeSeqGenerate hψ
        (algorithm18Input hψ l r).1
        (algorithm18Input hψ l r).2 =
      algorithm18Input hψ l r := by
  unfold writeSeqGenerate
  rw [if_neg
    (algorithm18_guard_false_of_missingLeftFollower hψ l r hleft)]


/-- Consequently Algorithm 18 cannot manufacture a responder writer carrier,
command, active writer state, or bit change from this source. -/
theorem algorithm18_responder_writer_fields_unchanged
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hleft : MissingLeftFollowerConjunct l) :
    let q := algorithm18Input hψ l r
    let out := writeSeqGenerate hψ q.1 q.2
    out.2.path3 = q.2.path3 ∧
      out.2.write = q.2.write ∧
      out.2.write_state = q.2.write_state ∧
      out.2.bit = q.2.bit := by
  dsimp only
  rw [writeSeqGenerate_disabled_of_missingLeftFollower hψ l r hleft]
  exact ⟨rfl, rfl, rfl, rfl⟩


/-! ## Exact full-row endpoint for the next composition round -/


/-- The preparation cut used by Stage 1 and Stage 2. -/
def preparedEndpoint
    (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    AuthorizedAgentState ψ :=
  (prepareExpiringDisposal hψ u).core.erase


/-- Exactly the Stage-2 requested conditions plus the one source-side conjunct
identified by the counterexample.  `RequestedPreparedHypotheses` already
contains reset-free endpoints, both path2 fields empty, both deletion gates
open, responder probe false, the DISAPPEAR disjunction, and the Stage-1
`PreparedResponderWriterPremise`. -/
def Stage3PreparedHypotheses
    (l r : AuthorizedAgentState ψ) : Prop :=
  RequestedPreparedHypotheses l r ∧
    MissingLeftFollowerConjunct l


/-- Exact item-2 statement.  This is a proposition definition, not an unproved
theorem declaration: the remaining work is to transport the prepared-source
facts through the pre-writer prefix and compose the already-audited five
responder-side lane blockers with the Algorithm-18 exclusion above. -/
def FullHostResponderBitPreservationStatement
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) : Prop :=
  let leftPrepared := preparedEndpoint hψ l
  let rightPrepared := preparedEndpoint hψ r
  Stage3PreparedHypotheses leftPrepared rightPrepared →
    (BirthShortDoneTerminalHost.row
      hψ hwidth hle l r).2.core.erase.core.bit =
      rightPrepared.core.bit


#print axioms B6MicroAlg18Disabled.algorithm18_guard_false_of_missingLeftFollower
#print axioms B6MicroAlg18Disabled.writeSeqGenerate_disabled_of_missingLeftFollower
#print axioms B6MicroAlg18Disabled.algorithm18_responder_writer_fields_unchanged


end B6MicroAlg18Disabled
