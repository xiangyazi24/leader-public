import Leader.Wu.Entrance.WriterPremisePrepared

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6WriterPremiseStage2

open PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair BirthGenerationDone
open PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair
open K2BirthDispatcher K2BirthLeaderNormalize
  BirthArrivalCaptureRepair BirthShortDoneTerminalHost
  BirthShortDoneTerminalEntryCut BirthShortDoneCuts
open BirthStationaryWrite
open B6WriterPremiseStage1

variable {ψ : Nat}

/-! ## 1. The exact hypothesis list requested for Stage 2 -/

/-- Stage 1's corrected responder-writer premise, together with the reset,
path2, probe, deletion-open, and disjunctive DISAPPEAR hypotheses.
Deliberately no left-follower hypothesis is hidden here. -/
def RequestedPreparedHypotheses
    (l r : AuthorizedAgentState ψ) : Prop :=
  l.core.reset_cmd = false ∧
    r.core.reset_cmd = false ∧
    l.core.path2 = none ∧
    r.core.path2 = none ∧
    deletionActive l = false ∧
    deletionActive r = false ∧
    r.core.probe = false ∧
    (l.core.p_carry = false ∨ r.core.p = false) ∧
    PreparedResponderWriterPremise r

/-- The source-side conjunct missing from `RequestedPreparedHypotheses`.
On the matched B6 route this is the existing left-follower fact. -/
def MissingLeftFollowerConjunct
    (l : AuthorizedAgentState ψ) : Prop :=
  l.core.leader = false

/-! ## 2. Smallest fresh-generation witness

`ψ = 1` cannot realize Algorithm 18's fresh responder flip: its responder
would have to be both nonzero-labeled and terminal.  Thus `ψ = 2` is the
smallest literal carrier for this escaping lane.
-/

private theorem twoPos : 0 < 2 := by decide
private theorem widthPos : 0 < 2 := by decide
private theorem widthLe : 2 ≤ 2 := by decide

private def peace2 (leader : Bool) (j : Fin 2) : PeaceView 2 :=
  { leader := leader
    label := j
    shield := false
    bullet := 0
    signal_B := 0 }

private def rawBase (leader : Bool) (j : Fin 2) : AgentState 2 :=
  PeaceView.toState (peace2 leader j)

/-- Label-zero leader with a live writer-generation source.  All unrelated
raw controls are at the `PeaceView.toState` defaults. -/
private def leftRaw : AgentState 2 :=
  { rawBase true 0 with gen_ws := true }

/-- Terminal follower.  In particular, every Stage-1 responder-writer
coordinate is initially idle. -/
private def rightRaw : AgentState 2 :=
  rawBase false 1

private theorem leftRawDomain : leftRaw.inProtocolDomain 0 := by
  simp [leftRaw, rawBase, peace2,
    PeaceView.toState, AgentState.inProtocolDomain]

private theorem rightRawDomain : rightRaw.inProtocolDomain 0 := by
  simp [rightRaw, rawBase, peace2,
    PeaceView.toState, AgentState.inProtocolDomain]

private def pack
    (u : AgentState 2) (hu : u.inProtocolDomain 0) :
    ExpiringAgentState 2 0 1 :=
  ⟨⟨BoundedAgentState.ofDomain u hu, false⟩, 0⟩

private def leftInput : ExpiringAgentState 2 0 1 :=
  pack leftRaw leftRawDomain

private def rightInput : ExpiringAgentState 2 0 1 :=
  pack rightRaw rightRawDomain

private def prepared
    (u : ExpiringAgentState 2 0 1) : AuthorizedAgentState 2 :=
  (prepareExpiringDisposal twoPos u).core.erase

private def normalized
    (u : ExpiringAgentState 2 0 1) : AuthorizedAgentState 2 :=
  normalizeDeletion (prepared u)

private def throughCheck :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  doneThroughCheckEntryWidth twoPos widthPos widthLe 0
    (normalized leftInput) (normalized rightInput)

private def writerInput :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  BirthShortDoneCuts.beforeWriteWidth twoPos widthPos widthLe
    throughCheck.1 throughCheck.2

private def writerPrepared : AgentState 2 × AgentState 2 :=
  BirthStationaryWrite.swPersistentThroughPrepare twoPos
    writerInput.1.core writerInput.2.core

private def outR : ExpiringAgentState 2 0 1 :=
  (BirthShortDoneTerminalHost.row
    twoPos widthPos widthLe leftInput rightInput).2

/-! ## 3. The escape -/

/-- Every hypothesis of `RequestedPreparedHypotheses` holds on the prepared
pair, including the corrected Stage-1 writer premise and DISAPPEAR disjunction. -/
theorem witness_satisfies_requested_hypotheses :
    RequestedPreparedHypotheses
      (prepared leftInput) (prepared rightInput) := by
  unfold RequestedPreparedHypotheses PreparedResponderWriterPremise
  decide

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 32768 in
/-- The pre-writer prefix preserves the left generation source.  Therefore the
Algorithm-18 guard is open despite the responder being writer-idle. -/
theorem algorithm18_guard_escapes_stage1 :
    writerInput.1.core.leader = true ∧
    writerInput.1.core.gen_ws = true ∧
    writerInput.2.core.path3 = none ∧
    writerInput.2.core.write = .none ∧
    writerInput.2.core.write_state = .none := by
  decide

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 32768 in
/-- The bit has already changed at `swPersistentThroughPrepare`, i.e. inside
the fresh-generation half of the stationary writer, before Algorithm 19 can
use any pre-existing responder command/state. -/
theorem algorithm18_fresh_generation_changes_responder_bit :
    writerPrepared.2.bit ≠ writerInput.2.core.bit := by
  decide

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 32768 in
/-- The same change survives the remainder of the literal full terminal host.
Thus the Stage-2 preservation statement, with only the requested hypotheses,
is false. -/
theorem full_host_changes_prepared_responder_bit :
    outR.core.erase.core.bit ≠ (prepared rightInput).core.bit := by
  decide

/-- The witness fails exactly the missing source-side condition. -/
theorem witness_violates_missing_left_follower :
    ¬ MissingLeftFollowerConjunct (prepared leftInput) := by
  unfold MissingLeftFollowerConjunct
  decide

end B6WriterPremiseStage2

#print axioms B6WriterPremiseStage2.witness_satisfies_requested_hypotheses
#print axioms B6WriterPremiseStage2.algorithm18_guard_escapes_stage1
#print axioms B6WriterPremiseStage2.algorithm18_fresh_generation_changes_responder_bit
#print axioms B6WriterPremiseStage2.full_host_changes_prepared_responder_bit
#print axioms B6WriterPremiseStage2.witness_violates_missing_left_follower
