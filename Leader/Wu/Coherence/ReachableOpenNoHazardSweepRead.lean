import Leader.Wu.Coherence.ReachableOpenNoHazardHandoff
import Leader.Wu.Coherence.ReachableOwnershipPayload

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableOpenNoHazard3

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31OpenNoHazard
open R2CoherenceV31OpenNoHazardClose
open R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachableSweep
open R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachableOpenNoHazard
open R2CoherenceV31ReachablePlus
open R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3
open R2CoherenceV31ReachableOpenNoHazard2
open R2CoherenceV31ReachablePlus4

variable {n ψ κ τ : Nat}

/-- The named transport closes now that
`openROwnerFresh_openNoHazard_reach` is public.

The public theorem is already arbitrary-owner: it does not assume that
`owner` currently carries `.openR`.  Its state-side hypothesis is
`ElectionGeometryV31 ring C`, obtained here from the quarantine trace. -/
theorem openNoHazardOwnerFreshTransport
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    OpenNoHazardOwnerFreshTransportV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro hChain C e owner hTrace hOld hb
  have hGeom : ElectionGeometryV31 ring C :=
    electionGeometry_of_quarantineTrace hψ h2 ring C hTrace
  exact openROwnerFresh_openNoHazard_reach
    hψ h2 ring hChain C e owner hGeom hb hOld

/-- The first strengthened clause from Plus3 therefore transports with no
new seam beyond the existing chain-origin assumption. -/
theorem openNoHazard_preserves_scrubLIncoming_plus4
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hChain : SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2)
    (C : FC n ψ κ τ) (e : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4V31 ring C)
    (hb : branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    ScrubLIncomingOpenRFreshV31 ring
      (stepV3 hψ h2 ring C e) := by
  exact openNoHazard_preserves_scrubLIncoming_of_ownerFreshTransport
    hψ h2 ring
      (openNoHazardOwnerFreshTransport
        (κ := κ) (τ := τ) hψ h2 ring)
      hChain C e hTrace hPlus.1 hb

private theorem branch_openNoHazard_tokens_none3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openNoHazard) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

/-- A current live sweep front cannot be either endpoint of the unrelated
open/no-hazard service: the front has token `.sweep`, while both serviced
endpoints have token `.none`.  This does *not* exclude the sweep responder or
later suffix cells from being serviced. -/
theorem openNoHazard_live_sweep_front_not_served
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e sweep : Fin n)
    (hb : branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .openNoHazard)
    (hSweep : (C sweep).ctl.tok = .sweep) :
    sweep ≠ e ∧ sweep ≠ ring.rightNeighbor e := by
  have hNone := branch_openNoHazard_tokens_none3 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb
  constructor
  · intro h
    subst sweep
    simp [hNone.1] at hSweep
  · intro h
    subst sweep
    simp [hNone.2] at hSweep

/-- The cells read by the wide sweep/openR compatibility clause: the explicit
responder plus the remaining suffix beginning at the sweep front. -/
def InSweepWideReadV31
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (sweep p : Fin n) : Prop :=
  p = ring.rightNeighbor sweep ∨
    ∃ d : Fin (ψ - (raw (C sweep)).label.val),
      R2Coherence.fwd ring sweep d.val = p

/-- STOP: first obligation not supplied by Plus4.

For `SweepOpenRSafeAtV31`, the non-footprint disjunct transports because
`openNoHazard_step_frame` preserves every label.  A `MainClearV3` cell not in
the serviced pair transports by `stepV3_other`.  Thus the only unresolved
case is a cell which

* is read by a live sweep's responder/remaining suffix,
* is one of the two open/no-hazard endpoints,
* lies in the pending owner's freshness footprint, and
* was safe only because it was `MainClearV3`.

The open/no-hazard `install` changes `phys` at that endpoint.  The current
Plus4 additions do not close this case: S concerns incoming seek-created
sweeps; R1 concerns cells forward of a *current* `.openR`; R2 concerns an
`.openR` service versus surviving phase ownership.  None says that this
open/none endpoint remains main-clear. -/
def OpenNoHazardSweepReadMainClearTransportV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2 →
    ∀ (C : FC n ψ κ τ) (e sweep owner p : Fin n),
      ReachableFromQuarantineV31 hψ h2 ring C →
      ReachablePhaseFactsPlus4V31 ring C →
      branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
        .openNoHazard →
      (C sweep).ctl.tok = .sweep →
      PendingOpenROwnerV31 ring C owner →
      InSweepWideReadV31 ring C sweep p →
      (p = e ∨ p = ring.rightNeighbor e) →
      InOpenRFreshFootprintV31 ring C owner p →
      MainClearV3 (C p) →
        MainClearV3 (stepV3 hψ h2 ring C e p)

end R2CoherenceV31ReachableOpenNoHazard3
