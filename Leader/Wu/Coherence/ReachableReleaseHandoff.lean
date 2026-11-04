import Leader.Wu.Coherence.ReachableRelease

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableRelease2

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableRelease

variable {n ψ κ τ : Nat}

/-- P1-P7 under the already-named P7 residual.  The release guard
prepayment itself gives only `GroupOwnedClearV31 ring C e`, so it does not
close the arbitrary-window `OpenROwnerFreshV3` obligation. -/
theorem reachablePhaseFactsPlus_release_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hP7 : ReleaseScrubLIncomingOpenRFreshPreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    ReachablePhaseFactsPlusV31 ring (stepV3 hψ h2 ring C e) := by
  have hFacts : ReachablePhaseFactsV31 ring C := hPlus.1.1.1.1
  exact ⟨reachablePhaseFacts_release_step hψ h2 ring C e hFacts hb,
    hP7 C e hGeom hTrace hPlus hb⟩

/-- STOP: P8 is the first clause after conditional P7 that is not
prepaid by the current payload.

On the successor + writer-quiet + terminal RELEASE arm, the responder becomes
`.scrubL`.  If the initiator is a root, this creates a new
`PendingOpenROwnerV31` at that root.  The pre-state P8/P9 clauses need not have
mentioned this owner because the responder need not already have carried
`.scrubL`.  Conditional P7 supplies `OpenROwnerFreshV3` for the new owner, but
P8 needs `MainClearV3` (or exclusion from the freshness footprint) at every
live sweep front and responder.  `release_guard_prepays_owner` covers only the
release owner's own `GroupOwnedClearV31`; overlapping freshness windows can
cross that group boundary.  Strong R2, even when its guards apply, yields only
`PhaseOwnedV31`, not `MainClearV3`.

The post-state P7 premise below records that this audit continues conditionally
on the P7 residual.  No private `_rel` helper is made public: the stop occurs
before a P8/P9 label-transport theorem can be completed. -/
def ReleaseSweepOpenROverlapClearPreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release →
    ScrubLIncomingOpenRFreshV31 ring (stepV3 hψ h2 ring C e) →
      SweepOpenROverlapClearV31 ring (stepV3 hψ h2 ring C e)

/- `releaseStep_reachable_full` is intentionally not asserted.  After the
explicit P7 assumption, P8 is the first unclosed payload clause, so P9, S, R1,
and strong R2 are not attempted past this STOP. -/

end R2CoherenceV31ReachableRelease2
