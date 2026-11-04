import Leader.Wu.ShortGap.CleanupOwnedEntry
import Leader.Wu.ShortGap.CaptureCommitRows
import Leader.Wu.Protocol.RepairedAgentState


/-!
# Census of the cleanup-visible short-gap capture surface


This is an R1 census/design leaf.  It does not change the protocol row and it
uses no unrelated P_PLL field as capture state.


The current integrated cleanup host remains
`PPLLExpiringComparisonRepair.ExpiringAgentState`.  The exact capture actors,
reservation/proposal rows and post-FINAL commit/receipt rows exist on separate
ShortGap carriers.  `CaptureSurfaceTag` below is the smallest standalone local
surface alphabet used by this census; it is not claimed to replace the richer
operational ShortGap rows.
-/


namespace CleanupCaptureSurfaceCensus


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


/-- Objects requested by the cleanup surface census. -/
inductive SurfaceObject where
  | captureActor
  | lease
  | proposal
  | committedReceipt
  | sourceAckPending
  | targetCleanupPending
  deriving DecidableEq, Repr


def surfaceObjects : List SurfaceObject :=
  [ .captureActor, .lease, .proposal, .committedReceipt,
    .sourceAckPending, .targetCleanupPending ]


/-- Manual source census of the integrated `ExpiringAgentState` carrier.
This is data recording the inspected declaration, not Lean structure
reflection.  None of these six objects is a coordinate of that carrier. -/
def integratedExpiringHasExactEquivalent : SurfaceObject -> Bool
  | _ => false


theorem integratedExpiring_surface_absent (x : SurfaceObject) :
    integratedExpiringHasExactEquivalent x = false := by
  cases x <;> rfl


/-- Each requested object does have an exact representation somewhere in the
separate ShortGap physical/semantic development; the point of the census is
that those representations have not been integrated into `ExpiringAgentState`. -/
def separateShortGapHasExactEquivalent : SurfaceObject -> Bool
  | _ => true


theorem separateShortGap_surface_present (x : SurfaceObject) :
    separateShortGapHasExactEquivalent x = true := by
  cases x <;> rfl


/-! ## Source alphabets that can be checked directly -/


def actorValues : List ShortGapCaptureEntry.Actor :=
  [ .freeHome, .sourceLeased, .targetHeld ]


theorem actorValues_length : actorValues.length = 3 := by
  decide


theorem actorValues_nodup : actorValues.Nodup := by
  decide


theorem actorValues_complete (a : ShortGapCaptureEntry.Actor) :
    a ∈ actorValues := by
  cases a <;> decide


def incomingLeaseValues : List ShortGapCaptureReservation.InControl :=
  [ .open, .reserved, .accepted ]


theorem incomingLeaseValues_length : incomingLeaseValues.length = 3 := by
  decide


theorem incomingLeaseValues_nodup : incomingLeaseValues.Nodup := by
  decide


theorem incomingLeaseValues_complete
    (a : ShortGapCaptureReservation.InControl) :
    a ∈ incomingLeaseValues := by
  cases a <;> decide


def reservationMessageValues :
    List ShortGapCaptureReservation.CaptureMessage :=
  [ .proposal, .finalBack ]


theorem reservationMessageValues_length :
    reservationMessageValues.length = 2 := by
  decide


theorem reservationMessageValues_nodup :
    reservationMessageValues.Nodup := by
  decide


theorem reservationMessageValues_complete
    (m : ShortGapCaptureReservation.CaptureMessage) :
    m ∈ reservationMessageValues := by
  cases m <;> decide


def commitCarrierValues : List ShortGapCaptureCommitRows.CommitCarrier :=
  [ .none, .commit, .committedBack ]


theorem commitCarrierValues_length : commitCarrierValues.length = 3 := by
  decide


theorem commitCarrierValues_nodup : commitCarrierValues.Nodup := by
  decide


theorem commitCarrierValues_complete
    (c : ShortGapCaptureCommitRows.CommitCarrier) :
    c ∈ commitCarrierValues := by
  cases c <;> decide


def postCommitValues :
    List ShortGapCaptureLifecycle.PostCommitObligations :=
  [ ⟨false, false⟩, ⟨false, true⟩,
    ⟨true, false⟩, ⟨true, true⟩ ]


theorem postCommitValues_length : postCommitValues.length = 4 := by
  decide


theorem postCommitValues_nodup : postCommitValues.Nodup := by
  decide


theorem postCommitValues_complete
    (o : ShortGapCaptureLifecycle.PostCommitObligations) :
    o ∈ postCommitValues := by
  cases o with
  | mk sourceAckPending targetCleanupPending =>
      cases sourceAckPending <;> cases targetCleanupPending <;> decide


/-- The checked source really distinguishes the two precommit wire directions. -/
theorem proposal_ne_final :
    (ShortGapCaptureReservation.CaptureMessage.proposal :
      ShortGapCaptureReservation.CaptureMessage) ≠ .finalBack := by
  decide


/-- The committed receipt is a distinct physical carrier constructor. -/
theorem committedReceipt_ne_none :
    (ShortGapCaptureCommitRows.CommitCarrier.committedBack :
      ShortGapCaptureCommitRows.CommitCarrier) ≠ .none := by
  decide


/-- The physical source postcommit state is not the clean state. -/
theorem sourceAckPending_ne_clean :
    (ShortGapCaptureCommitRows.CommitCtl.committedReceived :
      ShortGapCaptureCommitRows.CommitCtl) ≠ .clean := by
  decide


/-- The physical target postcommit state is not the clean state. -/
theorem targetCleanupPending_ne_clean :
    (ShortGapCaptureCommitRows.CommitIn.committed :
      ShortGapCaptureCommitRows.CommitIn) ≠ .clean := by
  decide


/-- The semantic committed state starts with both obligations pending. -/
theorem fullPostCommit_both_pending :
    ShortGapCaptureLifecycle.PostCommitObligations.full.sourceAckPending = true ∧
      ShortGapCaptureLifecycle.PostCommitObligations.full.targetCleanupPending = true := by
  exact ⟨rfl, rfl⟩


/-! ## The four arbitrary-state hazards are derived, not stored -/


inductive SurfaceHazard where
  | forgedMaximumRankWork
  | staleCaptureActor
  | staleLease
  | partialPostcommitReceipt
  deriving DecidableEq, Repr


def surfaceHazards : List SurfaceHazard :=
  [ .forgedMaximumRankWork, .staleCaptureActor,
    .staleLease, .partialPostcommitReceipt ]


theorem surfaceHazards_length : surfaceHazards.length = 4 := by
  decide


/-- No independent protocol coordinate is allocated to the hazard predicates. -/
def hazardStateFactor : Nat := 1


theorem hazardStateFactor_eq_one : hazardStateFactor = 1 := rfl


/-! ## Minimal standalone cleanup-visible physical surface -/


/-- Local object/phase tag sufficient for the cleanup predicates.


`finalCarrier` and `protectedCommitCarrier` are included even though the user
surface names proposal and committed receipt explicitly: current source has
those two intermediate physical carriers, and collapsing them would lose the
precommit/protected/postcommit distinction required by the existing rows. -/
inductive CaptureSurfaceTag where
  | idle
  | sourceActorLeased
  | targetLeaseReserved
  | targetActorHeld
  | proposalCarrier
  | finalCarrier
  | protectedCommitCarrier
  | committedReceipt
  | sourceAckPending
  | targetCleanupPending
  deriving DecidableEq, Repr


def captureSurfaceTagValues : List CaptureSurfaceTag :=
  [ .idle, .sourceActorLeased, .targetLeaseReserved, .targetActorHeld,
    .proposalCarrier, .finalCarrier, .protectedCommitCarrier,
    .committedReceipt, .sourceAckPending, .targetCleanupPending ]


theorem captureSurfaceTagValues_length :
    captureSurfaceTagValues.length = 10 := by
  decide


theorem captureSurfaceTagValues_nodup :
    captureSurfaceTagValues.Nodup := by
  decide


theorem captureSurfaceTagValues_complete (x : CaptureSurfaceTag) :
    x ∈ captureSurfaceTagValues := by
  cases x <;> decide


/-- Exact state multiplier of the standalone cleanup-visible coordinate. -/
def captureSurfaceStateFactor : Nat := captureSurfaceTagValues.length


/-- Hazards are classifiers over the surface, so they contribute factor one. -/
def wholeSurfaceStateFactor : Nat :=
  captureSurfaceStateFactor * hazardStateFactor


theorem wholeSurfaceStateFactor_eq_ten :
    wholeSurfaceStateFactor = 10 := by
  decide


/-- Product-form physical realization if the operational capture controller is
not itself used as the representation of the cleanup surface. -/
structure CaptureExtendedExpiringAgentState (psi kappa tau : Nat) where
  core : PPLLExpiringComparisonRepair.ExpiringAgentState psi kappa tau
  captureSurface : CaptureSurfaceTag
  deriving DecidableEq, Repr


/-- Symbolic exact state-count multiplier for the product realization. -/
def captureExtendedStateCount (baseStateCount : Nat) : Nat :=
  baseStateCount * wholeSurfaceStateFactor


theorem captureExtendedStateCount_eq (baseStateCount : Nat) :
    captureExtendedStateCount baseStateCount = baseStateCount * 10 := by
  simp [captureExtendedStateCount, wholeSurfaceStateFactor,
    captureSurfaceStateFactor, captureSurfaceTagValues, hazardStateFactor]


end CleanupCaptureSurfaceCensus


#print axioms CleanupCaptureSurfaceCensus.integratedExpiring_surface_absent
#print axioms CleanupCaptureSurfaceCensus.separateShortGap_surface_present
#print axioms CleanupCaptureSurfaceCensus.actorValues_length
#print axioms CleanupCaptureSurfaceCensus.actorValues_nodup
#print axioms CleanupCaptureSurfaceCensus.actorValues_complete
#print axioms CleanupCaptureSurfaceCensus.incomingLeaseValues_length
#print axioms CleanupCaptureSurfaceCensus.incomingLeaseValues_nodup
#print axioms CleanupCaptureSurfaceCensus.incomingLeaseValues_complete
#print axioms CleanupCaptureSurfaceCensus.reservationMessageValues_length
#print axioms CleanupCaptureSurfaceCensus.reservationMessageValues_nodup
#print axioms CleanupCaptureSurfaceCensus.reservationMessageValues_complete
#print axioms CleanupCaptureSurfaceCensus.commitCarrierValues_length
#print axioms CleanupCaptureSurfaceCensus.commitCarrierValues_nodup
#print axioms CleanupCaptureSurfaceCensus.commitCarrierValues_complete
#print axioms CleanupCaptureSurfaceCensus.postCommitValues_length
#print axioms CleanupCaptureSurfaceCensus.postCommitValues_nodup
#print axioms CleanupCaptureSurfaceCensus.postCommitValues_complete
#print axioms CleanupCaptureSurfaceCensus.proposal_ne_final
#print axioms CleanupCaptureSurfaceCensus.committedReceipt_ne_none
#print axioms CleanupCaptureSurfaceCensus.sourceAckPending_ne_clean
#print axioms CleanupCaptureSurfaceCensus.targetCleanupPending_ne_clean
#print axioms CleanupCaptureSurfaceCensus.fullPostCommit_both_pending
#print axioms CleanupCaptureSurfaceCensus.surfaceHazards_length
#print axioms CleanupCaptureSurfaceCensus.hazardStateFactor_eq_one
#print axioms CleanupCaptureSurfaceCensus.captureSurfaceTagValues_length
#print axioms CleanupCaptureSurfaceCensus.captureSurfaceTagValues_nodup
#print axioms CleanupCaptureSurfaceCensus.captureSurfaceTagValues_complete
#print axioms CleanupCaptureSurfaceCensus.wholeSurfaceStateFactor_eq_ten
#print axioms CleanupCaptureSurfaceCensus.captureExtendedStateCount_eq
