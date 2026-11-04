import Leader.Wu.Coherence.ReachableOpenNoHazard
import Leader.Wu.Coherence.ReachableWideOverlapPayload

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableOpenNoHazard2

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
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

variable {n ψ κ τ : Nat}

/-- `openNoHazard` preserves controller and labels everywhere, so a pending
post-state openR owner was already pending before the service. -/
private theorem pendingOpenR_before_openNoHazard2
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (owner : Fin n)
    (hPost : PendingOpenROwnerV31 ring D owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases hPost with ⟨hScrub, hSucc, hRoot⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [(hF (ring.rightNeighbor owner)).2.2.2] at hScrub
    exact hScrub
  · have hL := congrArg Fin.val (hF owner).1
    have hR := congrArg Fin.val (hF (ring.rightNeighbor owner)).1
    unfold successorB at hSucc ⊢
    rw [hL, hR] at hSucc
    exact hSucc
  · have hL := congrArg Fin.val (hF owner).1
    unfold atRootB at hRoot ⊢
    rw [hL] at hRoot
    exact hRoot

/-- STOP: first non-exported obligation.

`Leader/Wu/Coherence/ReachableOpenNoHazard.lean:945-962` proves this
substance privately (after obtaining election geometry from reachability),
using exactly `SanitizedR2NewEqualFreshChainOriginNoMainMutation`.
A new importing module cannot name that private theorem. -/
def OpenNoHazardOwnerFreshTransportV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2 →
    ∀ (C : FC n ψ κ τ) (e owner : Fin n),
      ReachableFromQuarantineV31 hψ h2 ring C →
      OpenROwnerFreshV3 ring C owner →
      branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) =
        .openNoHazard →
      OpenROwnerFreshV3 ring (stepV3 hψ h2 ring C e) owner

/-- Exact reduction of the first new Plus3 clause to the missing public
owner-fresh transport.  No global unfolding of `stepV3`. -/
theorem openNoHazard_preserves_scrubLIncoming_of_ownerFreshTransport
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hTransport :
      OpenNoHazardOwnerFreshTransportV31
        (κ := κ) (τ := τ) hψ h2 ring)
    (hChain : SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2)
    (C : FC n ψ κ τ) (e : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus3V31 ring C)
    (hb : branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    ScrubLIncomingOpenRFreshV31 ring
      (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  intro owner hScrub hSucc hRoot
  have hPost : PendingOpenROwnerV31 ring D owner := by
    exact ⟨hScrub, hSucc, hRoot⟩
  have hPre := pendingOpenR_before_openNoHazard2 ring hF owner hPost
  have hOldFresh : OpenROwnerFreshV3 ring C owner := by
    exact hPlus.1.1.2 owner hPre.1 hPre.2.1 hPre.2.2
  exact hTransport hChain C e owner hTrace hOldFresh hb


end R2CoherenceV31ReachableOpenNoHazard2
