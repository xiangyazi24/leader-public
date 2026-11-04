import Leader.Wu.Coherence.ReachablePrepaid
import Leader.Wu.Coherence.ReachableOpenNoHazard

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachablePlus

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachableSweep
open R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachableOpenNoHazard

variable {n ψ κ τ : Nat}

/-- Downstream B-multi payload: the accepted reachable facts plus the pending
scrubL root-handoff freshness certificate. -/
def ReachablePhaseFactsPlusV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ReachablePhaseFactsV31 ring C ∧
    ScrubLIncomingOpenRFreshV31 ring C

/-- Entrance half for the new conjunct.
`quarantineInitV31` sets every controller to `.closing/.none`;
Leader/Wu/Coherence/BirthQuarantine.lean:21-25. -/
theorem scrubLIncomingOpenRFresh_quarantineInit
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    ScrubLIncomingOpenRFreshV31 ring (quarantineInitV31 C) := by
  intro e hScrub
  simp [quarantineInitV31, setControl] at hScrub

/-- Full strengthened entrance.  The old conjunct is supplied by
`reachablePhaseFacts_entrance`;
Leader/Wu/Coherence/ReachableFacts.lean:91-99. -/
theorem reachablePhaseFactsPlus_entrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ)
    (hBirth : BirthEntranceV1 hψ h2 ring C) :
    ReachablePhaseFactsPlusV31 ring C := by
  constructor
  · exact reachablePhaseFacts_entrance hψ h2 ring C hBirth
  · rcases hBirth.1 with ⟨_, D, _, hEq⟩
    rw [hEq]
    exact scrubLIncomingOpenRFresh_quarantineInit ring D

/-- Exact missing sweep interface.

The exported sweep theorem certifies only `PhaseMainClearV31`
(Leader/Wu/Coherence/ReachableSweep.lean:80-92), while the same module
explicitly records that the freshness half needs a trace-order/provenance lemma
(Leader/Wu/Coherence/ReachableSweep.lean:23-32).

A sweep can `clearMain` a served cell, so an overlapping pending-openR window
cannot be transported merely from the old B-multi payload.  This pointwise
statement is exactly the extra fact needed by the new conjunct. -/
def SweepPendingOpenRFreshTransportV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e owner : Fin n),
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsV31 ring C →
    ScrubLIncomingOpenRFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep →
    (stepV3 hψ h2 ring C e
        (ring.rightNeighbor owner)).ctl.tok = .scrubL →
    successorB
        (stepV3 hψ h2 ring C e owner)
        (stepV3 hψ h2 ring C e (ring.rightNeighbor owner)) = true →
    atRootB (stepV3 hψ h2 ring C e owner) = true →
      OpenROwnerFreshV3 ring (stepV3 hψ h2 ring C e) owner

/-- Requested sweep preservation reduced to the exact missing transport above.
No stronger claim is made. -/
theorem sweepStep_preserves_scrubLIncoming_of_transport
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hTransport :
      SweepPendingOpenRFreshTransportV31
        (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hPlus : ReachablePhaseFactsPlusV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hb : branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .sweep) :
    ScrubLIncomingOpenRFreshV31 ring
      (stepV3 hψ h2 ring C e) := by
  intro owner hScrub hSucc hRoot
  exact hTransport C e owner hTrace hPlus.1 hPlus.2 hb
    hScrub hSucc hRoot

/-
STOP.

The first preservation branch, `.sweep`, needs
`SweepPendingOpenRFreshTransportV31`, which is not exported or proved by the
current sweep module.  Therefore `.openNoHazard` and `.release` are
intentionally not attempted in this round.
-/

end R2CoherenceV31ReachablePlus
