import Std.Tactic

/-!
# Protected commit lifecycle for one selected short gap

This file fixes the semantic order of one clean capture after incidence choice
has selected an endpoint-disjoint `out1 -> in0` short gap.  The target actor is
already `FREE/home`; consequently the proposal returns `FINAL` directly.  The
`PROV`/poll loop belongs to arbitrary-residue cleanup, not to this normal path.

The lifecycle has one leader-clearing action.  Depositing `FINAL` only protects
and launches the commit carrier.  The target remains a leader until that carrier
reaches an edge incident to the still-held target.  The same local interaction
clears the target and launches a committed receipt.  Receipt return and target
residue cleanup are independent postcommit obligations; both precede `clean`.

This is a finite semantic quotient.  Its macro steps name completed persistent
services and do not prove their literal pair rows, transport implementation, or
arbitrary-state cleanup rank.  Those are the remaining physical refinement.
-/

namespace ShortGapCaptureLifecycle

inductive Outcome where
  | kept
  | deleted
  deriving DecidableEq, Repr

inductive PostCommitSide where
  | sourceAck
  | targetCleanup
  deriving DecidableEq, Repr

/-- Root-last postcommit obligations.  The source stays protected until its
committed receipt returns; the deleted target keeps a retirement wall until its
local residue is clean. -/
structure PostCommitObligations where
  sourceAckPending : Bool
  targetCleanupPending : Bool
  deriving DecidableEq, Repr

def PostCommitObligations.full : PostCommitObligations :=
  { sourceAckPending := true, targetCleanupPending := true }

def PostCommitObligations.discharge
    (obligations : PostCommitObligations) (side : PostCommitSide) :
    PostCommitObligations :=
  match side with
  | .sourceAck => { obligations with sourceAckPending := false }
  | .targetCleanup => { obligations with targetCleanupPending := false }

def PostCommitObligations.pending
    (obligations : PostCommitObligations) (side : PostCommitSide) : Prop :=
  match side with
  | .sourceAck => obligations.sourceAckPending = true
  | .targetCleanup => obligations.targetCleanupPending = true

def PostCommitObligations.done
    (obligations : PostCommitObligations) : Prop :=
  obligations.sourceAckPending = false /\
    obligations.targetCleanupPending = false

/-- Accepted clean-path control states.  In-flight names are proof-level
semantic classes; a physical implementation uses a bounded cursor. -/
inductive Control where
  | candidate
  | proposalOutbound
  | finalReturning
  | finalReady
  | protectedCommitOutbound
  | committed (obligations : PostCommitObligations)
  | aborting
  | clean (outcome : Outcome)
  deriving DecidableEq, Repr

/-- The source leader is framed throughout this one-candidate quotient. -/
def sourceLeader (_ : Control) : Bool := true

/-- The target leader falls only when the protected commit reaches it. -/
def targetLeader : Control -> Bool
  | .committed _ => false
  | .clean .deleted => false
  | _ => true

/-- Commit protection begins only after the matching FINAL is deposited and
persists through both postcommit obligations. -/
def commitProtected : Control -> Prop
  | .protectedCommitOutbound => True
  | .committed _ => True
  | _ => False

inductive Action where
  | launchProposal
  | proposalAtCleanTarget
  | returnFinal
  | acceptFinal
  | commitAtTarget
  | dischargePostCommit (side : PostCommitSide)
  | finishCommitted
  | revokePrecommit
  | finishAbort
  deriving DecidableEq, Repr

def Action.isAbort : Action -> Prop
  | .revokePrecommit | .finishAbort => True
  | _ => False

/-- One semantic macro transition.  `proposalAtCleanTarget` contains the
accepted guard that the selected target actor is `FREE/home`. -/
inductive Step : Control -> Action -> Control -> Prop where
  | launchProposal :
      Step .candidate .launchProposal .proposalOutbound
  | proposalAtCleanTarget :
      Step .proposalOutbound .proposalAtCleanTarget .finalReturning
  | returnFinal :
      Step .finalReturning .returnFinal .finalReady
  | acceptFinal :
      Step .finalReady .acceptFinal .protectedCommitOutbound
  | commitAtTarget :
      Step .protectedCommitOutbound .commitAtTarget
        (.committed .full)
  | dischargePostCommit
      (obligations : PostCommitObligations) (side : PostCommitSide)
      (pending : obligations.pending side) :
      Step (.committed obligations) (.dischargePostCommit side)
        (.committed (obligations.discharge side))
  | finishCommitted
      (obligations : PostCommitObligations) (done : obligations.done) :
      Step (.committed obligations) .finishCommitted (.clean .deleted)
  | revokeCandidate :
      Step .candidate .revokePrecommit .aborting
  | revokeProposal :
      Step .proposalOutbound .revokePrecommit .aborting
  | revokeFinalReturning :
      Step .finalReturning .revokePrecommit .aborting
  | revokeFinalReady :
      Step .finalReady .revokePrecommit .aborting
  | finishAbort :
      Step .aborting .finishAbort (.clean .kept)

private def boolWeight (value : Bool) : Nat := if value then 1 else 0

def PostCommitObligations.count
    (obligations : PostCommitObligations) : Nat :=
  boolWeight obligations.sourceAckPending +
    boolWeight obligations.targetCleanupPending

/-- Acyclicity rank for the semantic quotient.  It is not a physical
interaction bound. -/
def debt : Control -> Nat
  | .candidate => 10
  | .proposalOutbound => 9
  | .finalReturning => 8
  | .finalReady => 7
  | .protectedCommitOutbound => 6
  | .committed obligations => obligations.count + 1
  | .aborting => 1
  | .clean _ => 0

theorem discharge_count_lt
    (obligations : PostCommitObligations) (side : PostCommitSide)
    (pending : obligations.pending side) :
    (obligations.discharge side).count < obligations.count := by
  cases obligations with
  | mk sourceAckPending targetCleanupPending =>
      cases side <;> cases sourceAckPending <;>
        cases targetCleanupPending <;>
        simp_all [PostCommitObligations.pending,
          PostCommitObligations.discharge, PostCommitObligations.count,
          boolWeight]

/-- Every accepted macro step strictly lowers the finite semantic debt. -/
theorem Step.debt_lt {before after : Control} {action : Action}
    (step : Step before action after) : debt after < debt before := by
  cases step with
  | launchProposal | proposalAtCleanTarget | returnFinal | acceptFinal |
      commitAtTarget | revokeCandidate | revokeProposal |
      revokeFinalReturning | revokeFinalReady | finishAbort =>
      decide
  | dischargePostCommit obligations side pending =>
      simpa [debt] using discharge_count_lt obligations side pending
  | finishCommitted obligations done =>
      simp [debt]

/-- FINAL acceptance is a protection edge, not the deletion edge. -/
theorem acceptFinal_frames_targetLeader :
    targetLeader .finalReady = true /\
      targetLeader .protectedCommitOutbound = true := by
  decide

/-- The target leader changes from true to false exactly on the protected
target-local commit action. -/
theorem Step.targetLeader_falls_iff_commit
    {before after : Control} {action : Action}
    (step : Step before action after) :
    (targetLeader before = true /\ targetLeader after = false) <->
      action = .commitAtTarget := by
  cases step <;>
    simp [targetLeader]

/-- Once target deletion has committed, no accepted successor resurrects it. -/
theorem Step.targetDeletion_irreversible
    {before after : Control} {action : Action}
    (step : Step before action after) (deleted : targetLeader before = false) :
    targetLeader after = false := by
  cases step <;> simp [targetLeader] at deleted ⊢

theorem Step.sourceLeader_preserved
    {before after : Control} {action : Action}
    (_step : Step before action after) :
    sourceLeader before = sourceLeader after := rfl

/-- Revocation and abort cleanup are unavailable after FINAL has been accepted.
The physical refinement must preserve this guard while the carrier is remote. -/
theorem Step.protected_not_abort
    {before after : Control} {action : Action}
    (step : Step before action after) (hprotected : commitProtected before) :
    ¬ action.isAbort := by
  cases step <;> simp_all [commitProtected, Action.isAbort]

/-- Discharging either postcommit side frames the other side. -/
theorem discharge_source_preserves_target
    (obligations : PostCommitObligations) :
    (obligations.discharge .sourceAck).targetCleanupPending =
      obligations.targetCleanupPending := rfl

theorem discharge_target_preserves_source
    (obligations : PostCommitObligations) :
    (obligations.discharge .targetCleanup).sourceAckPending =
      obligations.sourceAckPending := rfl

theorem discharge_full_both_orders_done :
    ((PostCommitObligations.full.discharge .sourceAck).discharge
        .targetCleanup).done /\
      ((PostCommitObligations.full.discharge .targetCleanup).discharge
        .sourceAck).done := by
  simp [PostCommitObligations.full, PostCommitObligations.discharge,
    PostCommitObligations.done]

/-- A finite trace of semantic macro actions. -/
inductive Trace : Control -> List Action -> Control -> Prop where
  | refl (control : Control) : Trace control [] control
  | cons {before middle after action actions}
      (head : Step before action middle)
      (tail : Trace middle actions after) :
      Trace before (action :: actions) after

def cleanCommitSchedule : List Action :=
  [ .launchProposal,
    .proposalAtCleanTarget,
    .returnFinal,
    .acceptFinal,
    .commitAtTarget,
    .dischargePostCommit .sourceAck,
    .dischargePostCommit .targetCleanup,
    .finishCommitted ]

/-- The clean selected lifecycle reaches a committed deletion, with source
receipt return before target cleanup in this representative interleaving. -/
theorem cleanCommitTrace :
    Trace .candidate cleanCommitSchedule (.clean .deleted) := by
  unfold cleanCommitSchedule
  exact .cons .launchProposal <|
    .cons .proposalAtCleanTarget <|
    .cons .returnFinal <|
    .cons .acceptFinal <|
    .cons .commitAtTarget <|
    .cons (.dischargePostCommit PostCommitObligations.full .sourceAck
      (by simp [PostCommitObligations.full,
        PostCommitObligations.pending])) <|
    .cons (.dischargePostCommit
      (PostCommitObligations.full.discharge .sourceAck) .targetCleanup
      (by simp [PostCommitObligations.full,
        PostCommitObligations.discharge,
        PostCommitObligations.pending])) <|
    .cons (.finishCommitted
      ((PostCommitObligations.full.discharge .sourceAck).discharge
        .targetCleanup)
      (by simp [PostCommitObligations.full,
        PostCommitObligations.discharge,
        PostCommitObligations.done])) <|
    .refl _

/-- Number of complete short-gap crossings charged by each clean action. -/
def Action.crossings : Action -> Nat
  | .proposalAtCleanTarget => 1
  | .returnFinal => 1
  | .commitAtTarget => 1
  | .dischargePostCommit .sourceAck => 1
  | _ => 0

def scheduleCrossings (actions : List Action) : Nat :=
  (actions.map Action.crossings).sum

/-- The clean commit uses exactly four gap crossings: proposal, FINAL return,
commit, and committed-receipt return. -/
theorem cleanCommitSchedule_crossings :
    scheduleCrossings cleanCommitSchedule = 4 := by
  decide

def Action.isCommit : Action -> Bool
  | .commitAtTarget => true
  | _ => false

def scheduleCommitCount (actions : List Action) : Nat :=
  (actions.map (fun action => if action.isCommit then 1 else 0)).sum

theorem cleanCommitSchedule_one_commit :
    scheduleCommitCount cleanCommitSchedule = 1 := by
  decide

end ShortGapCaptureLifecycle

#print axioms ShortGapCaptureLifecycle.Step.debt_lt
#print axioms ShortGapCaptureLifecycle.Step.targetLeader_falls_iff_commit
#print axioms ShortGapCaptureLifecycle.Step.targetDeletion_irreversible
#print axioms ShortGapCaptureLifecycle.Step.sourceLeader_preserved
#print axioms ShortGapCaptureLifecycle.Step.protected_not_abort
#print axioms ShortGapCaptureLifecycle.discharge_full_both_orders_done
#print axioms ShortGapCaptureLifecycle.cleanCommitTrace
#print axioms ShortGapCaptureLifecycle.cleanCommitSchedule_crossings
#print axioms ShortGapCaptureLifecycle.cleanCommitSchedule_one_commit
