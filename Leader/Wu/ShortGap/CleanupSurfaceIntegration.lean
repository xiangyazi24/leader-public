import Leader.Wu.ShortGap.CleanupCaptureSurfaceCensus
import Leader.Wu.ShortGap.CleanupOwnedEntry

namespace CleanupSurfaceIntegration

open PPLLExpiringComparisonRepair
open CleanupCaptureSurfaceCensus
open ShortGapCaptureReservation
open ShortGapCaptureCommitRows

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau mu omega : Nat}

/-! ## 1. Source carrier and the integrated physical state -/

/-- The cleanup theorem on current main is still over the expiring carrier. -/
theorem cleanupOwnedEntryConfig_is_expiring :
    CleanupOwnedEntry.Config n psi kappa tau =
      (Fin n -> ExpiringAgentState psi kappa tau) := by
  rfl

/-- Operational integration: retain the literal cleanup carrier and add the
already-physical short-gap reservation/commit controller. -/
structure IntegratedAgentState (psi kappa tau : Nat) where
  core : ExpiringAgentState psi kappa tau
  capture : ShortGapCaptureCommitRows.CNode
  deriving DecidableEq

abbrev Config (n psi kappa tau : Nat) :=
  Fin n -> IntegratedAgentState psi kappa tau

/-- Forget only the new short-gap controls. -/
def eraseCapture
    (u : IntegratedAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau :=
  u.core

/-- Project to the complete operational short-gap controller. -/
def shortGapView
    (u : IntegratedAgentState psi kappa tau) :
    ShortGapCaptureCommitRows.CNode :=
  u.capture

/-- Project further to the proposal/FINAL reservation carrier. -/
def reservationView
    (u : IntegratedAgentState psi kappa tau) :
    ShortGapCaptureReservation.Node :=
  u.capture.raw

/-! ## 2. Exact constant factor -/

/-- Constructor arithmetic for `Node`:
root = 3 choices * 4 cw * 3 ccw * 3 outgoing * 3 incoming;
interior = 7 selection slots + 2 capture messages. -/
def reservationNodeStateFactor : Nat :=
  3 * 4 * 3 * 3 * 3 + (7 + 2)

theorem reservationNodeStateFactor_eq :
    reservationNodeStateFactor = 333 := by
  decide

/-- `CNode = Node * Bool * CommitCtl * CommitIn * CommitCarrier`. -/
def captureControlStateFactor : Nat :=
  reservationNodeStateFactor * 2 * 5 * 4 * 3

theorem captureControlStateFactor_eq :
    captureControlStateFactor = 39960 := by
  decide

/-- Exact product count relative to any finite enumeration of the old carrier. -/
def integratedStateCount (baseStateCount : Nat) : Nat :=
  baseStateCount * captureControlStateFactor

theorem integratedStateCount_eq (baseStateCount : Nat) :
    integratedStateCount baseStateCount = baseStateCount * 39960 := by
  unfold integratedStateCount
  rw [captureControlStateFactor_eq]

/-- The cleanup observation is a projection and therefore adds no further
runtime coordinate once `CNode` is embedded. -/
def cleanupProjectionStateFactor : Nat := 1

theorem cleanupProjectionStateFactor_eq_one :
    cleanupProjectionStateFactor = 1 := rfl

/-- Constant multiplication preserves every previously proved finite upper
bound on the base carrier. -/
theorem integratedStateCount_mono
    (baseStateCount bound : Nat)
    (h : baseStateCount <= bound) :
    integratedStateCount baseStateCount <= bound * 39960 := by
  rw [integratedStateCount_eq]
  exact Nat.mul_le_mul_right 39960 h

/-! ## 3. Literal product row and immediate projections -/

/-- Existing cleanup row on the old physical coordinate. -/
def baseRow (hpsi : 0 < psi)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau :=
  (expiringProtocol hpsi kappa tau).transition l r

/-- Candidate integrated row: execute the old cleanup row and the existing
short-gap commit dispatcher on the same scheduled pair.  The nontrivial next
round is the cross-layer priority/no-backflow proof, not either projection. -/
def literalRow (hpsi : 0 < psi)
    (l r : IntegratedAgentState psi kappa tau) :
    IntegratedAgentState psi kappa tau ×
      IntegratedAgentState psi kappa tau :=
  let b := baseRow hpsi l.core r.core
  let c := ShortGapCaptureCommitRows.commitRow l.capture r.capture
  (⟨b.1, c.1⟩, ⟨b.2, c.2⟩)

/-- Ring scheduler lift of the integrated local row. -/
def literalStep (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : Config n psi kappa tau) (e : Fin n) :
    Config n psi kappa tau :=
  let j := ring.rightNeighbor e
  let q := literalRow hpsi (C e) (C j)
  fun i => if i = e then q.1 else if i = j then q.2 else C i

private def basePair
    (q : IntegratedAgentState psi kappa tau ×
      IntegratedAgentState psi kappa tau) :=
  (q.1.core, q.2.core)

private def capturePair
    (q : IntegratedAgentState psi kappa tau ×
      IntegratedAgentState psi kappa tau) :=
  (q.1.capture, q.2.capture)

private def reservationPair
    (q : IntegratedAgentState psi kappa tau ×
      IntegratedAgentState psi kappa tau) :=
  (q.1.capture.raw, q.2.capture.raw)

/-- The old cleanup physical row is literally the first projection. -/
theorem literalRow_base_projection
    (hpsi : 0 < psi)
    (l r : IntegratedAgentState psi kappa tau) :
    basePair (literalRow hpsi l r) =
      baseRow hpsi l.core r.core := by
  unfold basePair
  apply Prod.ext
  · unfold literalRow
    dsimp only
  · unfold literalRow
    dsimp only

/-- The full short-gap commit row is literally the second projection. -/
theorem literalRow_commit_projection
    (hpsi : 0 < psi)
    (l r : IntegratedAgentState psi kappa tau) :
    capturePair (literalRow hpsi l r) =
      ShortGapCaptureCommitRows.commitRow l.capture r.capture := by
  rfl

/-- On a genuine legacy capture interaction, the raw reservation projection
agrees with the existing `captureRow`. -/
theorem literalRow_capture_projection
    (hpsi : 0 < psi)
    (a b : ShortGapCaptureReservation.Node)
    (la lb : Bool)
    (h : ShortGapCaptureReservation.captureRow a b ≠ (a, b))
    (l r : ExpiringAgentState psi kappa tau) :
    reservationPair
        (literalRow hpsi
          ⟨l, ShortGapCaptureCommitRows.embed a la⟩
          ⟨r, ShortGapCaptureCommitRows.embed b lb⟩) =
      ShortGapCaptureReservation.captureRow a b := by
  change
    ShortGapCaptureCommitRows.projectPair
        (capturePair
          (literalRow hpsi
            ⟨l, ShortGapCaptureCommitRows.embed a la⟩
            ⟨r, ShortGapCaptureCommitRows.embed b lb⟩)) =
      ShortGapCaptureReservation.captureRow a b
  rw [literalRow_commit_projection hpsi
    ⟨l, ShortGapCaptureCommitRows.embed a la⟩
    ⟨r, ShortGapCaptureCommitRows.embed b lb⟩]
  exact ShortGapCaptureCommitRows.commitRow_agrees_captureRow a b la lb h

/-! ## 4. Cleanup surface as a physical projection -/

/-- Ten-case cleanup view, now derived from the richer operational controller.
The full `CNode` remains physical; this tag is only an observation. -/
def surfaceTag
    (u : ShortGapCaptureCommitRows.CNode) :
    CleanupCaptureSurfaceCensus.CaptureSurfaceTag :=
  match u.carrier with
  | .commit => .protectedCommitCarrier
  | .committedBack => .committedReceipt
  | .none =>
      if u.outgoing = .committedReceived then .sourceAckPending
      else if u.incoming = .committed then .targetCleanupPending
      else
        match u.raw with
        | .interior (.capture .proposal) => .proposalCarrier
        | .interior (.capture .finalBack) => .finalCarrier
        | .root .in0 _ .heldCandidate _ .reserved => .targetLeaseReserved
        | .root .in0 _ .heldCandidate _ .accepted => .targetActorHeld
        | .root .out1 _ .heldCandidate _ _ => .sourceActorLeased
        | _ => .idle

def tagLiveCarrier : CaptureSurfaceTag -> Bool
  | .proposalCarrier | .finalCarrier | .protectedCommitCarrier => true
  | _ => false

def tagLiveLease : CaptureSurfaceTag -> Bool
  | .sourceActorLeased | .targetLeaseReserved => true
  | _ => false

def tagLiveReceipt : CaptureSurfaceTag -> Bool
  | .committedReceipt | .sourceAckPending | .targetCleanupPending => true
  | _ => false

def tagLiveCaptureActor : CaptureSurfaceTag -> Bool
  | .sourceActorLeased | .targetActorHeld
  | .sourceAckPending | .targetCleanupPending => true
  | _ => false

/-- The proof-derived fields of `CleanupOwnedEntry.CleanupSurface` are not new
protocol coordinates.  They are kept as functions of the extended physical
configuration; only the four live-object observations below are fixed by the
physical `CNode` projection in this R1 integration leaf. -/
structure DerivedSurfaceData (n psi kappa tau : Nat) where
  certified : Config n psi kappa tau -> Bool
  carrierOwner : Config n psi kappa tau -> Fin n -> Option (Fin n)
  leaseOwner : Config n psi kappa tau -> Fin n -> Option (Fin n)
  receiptOwner : Config n psi kappa tau -> Fin n -> Option (Fin n)
  actorMember : Config n psi kappa tau -> Fin n -> Fin n -> Bool
  forgedMaximumRankWork : Config n psi kappa tau -> Fin n -> Bool
  staleCaptureActor : Config n psi kappa tau -> Fin n -> Bool
  staleLease : Config n psi kappa tau -> Fin n -> Bool
  partialPostcommitReceipt : Config n psi kappa tau -> Fin n -> Bool
  stalePresent :
    Config n psi kappa tau -> CleanupOwnedEntry.StaleKind -> Fin n -> Bool
  eraseDepth :
    Config n psi kappa tau -> CleanupOwnedEntry.StaleKind -> Fin n -> Nat
  rankCap : Nat

/-- Type-correct analogue of `CleanupOwnedEntry.CleanupSurface` on the extended
physical carrier.  The original record cannot itself be instantiated here
because its `Config` is definitionally fixed to `ExpiringAgentState`. -/
structure CleanupSurface (n psi kappa tau : Nat) where
  certified : Config n psi kappa tau -> Bool
  liveCarrier : Config n psi kappa tau -> Fin n -> Bool
  liveLease : Config n psi kappa tau -> Fin n -> Bool
  liveReceipt : Config n psi kappa tau -> Fin n -> Bool
  liveCaptureActor : Config n psi kappa tau -> Fin n -> Bool
  carrierOwner : Config n psi kappa tau -> Fin n -> Option (Fin n)
  leaseOwner : Config n psi kappa tau -> Fin n -> Option (Fin n)
  receiptOwner : Config n psi kappa tau -> Fin n -> Option (Fin n)
  actorMember : Config n psi kappa tau -> Fin n -> Fin n -> Bool
  forgedMaximumRankWork : Config n psi kappa tau -> Fin n -> Bool
  staleCaptureActor : Config n psi kappa tau -> Fin n -> Bool
  staleLease : Config n psi kappa tau -> Fin n -> Bool
  partialPostcommitReceipt : Config n psi kappa tau -> Fin n -> Bool
  stalePresent :
    Config n psi kappa tau -> CleanupOwnedEntry.StaleKind -> Fin n -> Bool
  eraseDepth :
    Config n psi kappa tau -> CleanupOwnedEntry.StaleKind -> Fin n -> Nat
  rankCap : Nat

/-- No physical surface field is supplied as an independent proof ghost:
all four live-object observations are projections of `CNode`. -/
def projectedCleanupSurface
    (D : DerivedSurfaceData n psi kappa tau) :
    CleanupSurface n psi kappa tau where
  certified := D.certified
  liveCarrier := fun C i => tagLiveCarrier (surfaceTag (C i).capture)
  liveLease := fun C i => tagLiveLease (surfaceTag (C i).capture)
  liveReceipt := fun C i => tagLiveReceipt (surfaceTag (C i).capture)
  liveCaptureActor := fun C i =>
    tagLiveCaptureActor (surfaceTag (C i).capture)
  carrierOwner := D.carrierOwner
  leaseOwner := D.leaseOwner
  receiptOwner := D.receiptOwner
  actorMember := D.actorMember
  forgedMaximumRankWork := D.forgedMaximumRankWork
  staleCaptureActor := D.staleCaptureActor
  staleLease := D.staleLease
  partialPostcommitReceipt := D.partialPostcommitReceipt
  stalePresent := D.stalePresent
  eraseDepth := D.eraseDepth
  rankCap := D.rankCap

@[simp] theorem projectedCleanupSurface_liveCarrier
    (D : DerivedSurfaceData n psi kappa tau)
    (C : Config n psi kappa tau) (i : Fin n) :
    (projectedCleanupSurface D).liveCarrier C i =
      tagLiveCarrier (surfaceTag (C i).capture) := rfl

@[simp] theorem projectedCleanupSurface_liveLease
    (D : DerivedSurfaceData n psi kappa tau)
    (C : Config n psi kappa tau) (i : Fin n) :
    (projectedCleanupSurface D).liveLease C i =
      tagLiveLease (surfaceTag (C i).capture) := rfl

@[simp] theorem projectedCleanupSurface_liveReceipt
    (D : DerivedSurfaceData n psi kappa tau)
    (C : Config n psi kappa tau) (i : Fin n) :
    (projectedCleanupSurface D).liveReceipt C i =
      tagLiveReceipt (surfaceTag (C i).capture) := rfl

@[simp] theorem projectedCleanupSurface_liveCaptureActor
    (D : DerivedSurfaceData n psi kappa tau)
    (C : Config n psi kappa tau) (i : Fin n) :
    (projectedCleanupSurface D).liveCaptureActor C i =
      tagLiveCaptureActor (surfaceTag (C i).capture) := rfl

/-! ## 5. Refinement obligation named for the next proof round -/

/-- Exactly the two short-gap projection obligations required of the integrated
literal row.  For the product row above they are immediate; what remains later
is the cross-layer cleanup/short-gap priority and closure proof. -/
def ShortGapProjectionRefinement (hpsi : 0 < psi) : Prop :=
  (forall l r : IntegratedAgentState psi kappa tau,
    capturePair (literalRow hpsi l r) =
      ShortGapCaptureCommitRows.commitRow l.capture r.capture) /\
  (forall (a b : ShortGapCaptureReservation.Node) (la lb : Bool)
      (h : ShortGapCaptureReservation.captureRow a b ≠ (a, b))
      (l r : ExpiringAgentState psi kappa tau),
    reservationPair
        (literalRow hpsi
          ⟨l, ShortGapCaptureCommitRows.embed a la⟩
          ⟨r, ShortGapCaptureCommitRows.embed b lb⟩) =
      ShortGapCaptureReservation.captureRow a b)

theorem shortGapProjectionRefinement (hpsi : 0 < psi) :
    ShortGapProjectionRefinement (kappa := kappa) (tau := tau) hpsi := by
  constructor
  · intro l r
    exact literalRow_commit_projection hpsi l r
  · intro a b la lb h l r
    exact literalRow_capture_projection hpsi a b la lb h l r

end CleanupSurfaceIntegration

#print axioms CleanupSurfaceIntegration.cleanupOwnedEntryConfig_is_expiring
#print axioms CleanupSurfaceIntegration.reservationNodeStateFactor_eq
#print axioms CleanupSurfaceIntegration.captureControlStateFactor_eq
#print axioms CleanupSurfaceIntegration.integratedStateCount_eq
#print axioms CleanupSurfaceIntegration.cleanupProjectionStateFactor_eq_one
#print axioms CleanupSurfaceIntegration.integratedStateCount_mono
#print axioms CleanupSurfaceIntegration.literalRow_base_projection
#print axioms CleanupSurfaceIntegration.literalRow_commit_projection
#print axioms CleanupSurfaceIntegration.literalRow_capture_projection
#print axioms CleanupSurfaceIntegration.projectedCleanupSurface_liveCarrier
#print axioms CleanupSurfaceIntegration.projectedCleanupSurface_liveLease
#print axioms CleanupSurfaceIntegration.projectedCleanupSurface_liveReceipt
#print axioms CleanupSurfaceIntegration.projectedCleanupSurface_liveCaptureActor
#print axioms CleanupSurfaceIntegration.shortGapProjectionRefinement
