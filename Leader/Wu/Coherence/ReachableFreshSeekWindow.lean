import Leader.Wu.Coherence.ReachableOpenHazardPrepaid
import Leader.Wu.Coherence.ReachableMixed
import Leader.Wu.Coherence.QuarantineTokens

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableFreshSeek

open PPLL PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure R2CoherenceV31BirthQuarantine
open R2CoherenceV31PhaseMainClear R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableOpenHazard
open R2CoherenceV31ReachableOpenHazard2
open R2CoherenceV31ReachableMixed

variable {n ψ κ τ : Nat}

/-- Shared fresh-seek payload.  It says that after either branch which can
introduce a seek, every post-state seek already has exactly the S window
required against every pending openR owner. -/
def FreshSeekWindowClearV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) : Prop :=
  ∀ (e pred owner : Fin n),
    (branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard ∨
      branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .mixed) →
    let D := stepV3 hψ h2 ring C e
    (D (ring.rightNeighbor pred)).ctl.tok = .seek →
    PendingOpenROwnerV31 ring D owner →
      (atRootB (D (ring.rightNeighbor pred)) = true →
        SweepOpenRSafeAtV31 ring D owner
            (ring.rightNeighbor (ring.rightNeighbor pred)) ∧
        ∀ d : Fin (ψ - (raw (D (ring.rightNeighbor pred))).label.val),
          SweepOpenRSafeAtV31 ring D owner
            (R2Coherence.fwd ring (ring.rightNeighbor pred) d.val)) ∧
      (atRootB (D (ring.rightNeighbor pred)) = false →
        atRootB (D pred) = true →
          SweepOpenRSafeAtV31 ring D owner (ring.rightNeighbor pred) ∧
          ∀ d : Fin (ψ - (raw (D pred)).label.val),
            SweepOpenRSafeAtV31 ring D owner
              (R2Coherence.fwd ring pred d.val))

/-- The exact R2 geometric bridge.  A pending owner is root and its successor
is scrubL.  The desired containment says every cell which its future openR
freshness certificate can read is in that scrubL-owned group. -/
def PendingOpenRFootprintInScrubGroupV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (owner p : Fin n),
    PendingOpenROwnerV31 ring C owner →
    InOpenRFreshFootprintV31 ring C owner p →
      InGroupOwnedFootprintV31 ring C (ring.rightNeighbor owner) p

/-- If the geometric containment is supplied, P5 makes every pending-owner
freshness-footprint cell main-clear. -/
theorem pendingOwner_safe_everywhere_of_containment
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hFacts : ReachablePhaseFactsV31 ring C)
    (hContain : PendingOpenRFootprintInScrubGroupV31 ring C)
    (owner p : Fin n) (hPending : PendingOpenROwnerV31 ring C owner) :
    SweepOpenRSafeAtV31 ring C owner p := by
  unfold SweepOpenRSafeAtV31
  by_cases hf : InOpenRFreshFootprintV31 ring C owner p
  · left
    rcases hFacts with ⟨_, _, _, _, hScrub, _⟩
    have hs := hScrub (ring.rightNeighbor owner) hPending.1
    have hg := hs.2.2
    rcases hContain owner p hPending hf with ⟨k, hk⟩
    unfold GroupOwnedClearV31 at hg
    rw [← hk]
    exact (hg k).1
  · exact Or.inr hf

theorem freshSeekWindowClear_quarantineInit
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) :
    FreshSeekWindowClearV31 hψ h2 ring (quarantineInitV31 C) := by
  intro e pred owner _hb
  dsimp only
  intro _hSeek hPending
  exact ((R2CoherenceV31QuarantineTokens.stepV3_from_quarantineInit_no_scrubL
    hψ h2 ring C e (ring.rightNeighbor owner)) hPending.1).elim


/-- `FreshSeekWindowClearV31` immediately discharges the
openHazard residual; its statement is exactly the fresh post-seek S window. -/
theorem openHazardFreshSeekPrepaid_of_freshSeekWindowClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hInv : ∀ C : FC n ψ κ τ,
      ReachableFromQuarantineV31 hψ h2 ring C →
      ElectionGeometryV31 ring C →
      ReachablePhaseFactsPlus4StrongR2V31 ring C →
      FreshSeekWindowClearV31 hψ h2 ring C) :
    OpenHazardFreshSeekPrepaidV31 (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e pred owner hTrace hGeom hPlus hb
  dsimp only
  intro hSeek _hOld hPending
  exact hInv C hTrace hGeom hPlus e pred owner (Or.inl hb) hSeek hPending

theorem mixedSeekIncomingSweepOpenROverlapClearWidePreservation_of_fresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hInv : ∀ C : FC n ψ κ τ,
      ReachableFromQuarantineV31 hψ h2 ring C →
      ElectionGeometryV31 ring C →
      ReachablePhaseFactsPlus4StrongR2V31 ring C →
      FreshSeekWindowClearV31 hψ h2 ring C) :
    MixedSeekIncomingSweepOpenROverlapClearWidePreservationV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace hPlus hb
  intro pred owner hSeek hPending
  exact hInv C hTrace hGeom hPlus e pred owner
    (Or.inr hb) hSeek hPending

/-- R2 reduction: if the footprint-containment theorem is proved for every
reachable state, then every pending owner is safe at every cell.  This is
strictly stronger than the windows needed by `FreshSeekWindowClearV31` and is
the source-level invariant suggested by the probe. -/
def PendingFootprintContainmentReachableV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    ReachableFromQuarantineV31 hψ h2 ring C →
    ElectionGeometryV31 ring C →
      PendingOpenRFootprintInScrubGroupV31 ring C

/-
STOP/R3.

The first clause not closed from the current exported API is
`PendingFootprintContainmentReachableV31` (equivalently the pointwise
`PendingOpenRFootprintInScrubGroupV31`).  `ElectionGeometryV31` gives the
root/successor label geometry, and P5 gives whole-group main-clear at the
scrubL successor; what is not exported is the arithmetic statement that the
existential `groupPos/prefixPos` definition of `InOpenRFreshFootprintV31` is
contained in that same group.

Smallest structural attack: n = ψ = 3 with labels 0,1,2.  Put a pending owner
at label 0, hence its label-1 successor carries `.scrubL`.  Try to make a
future seek at the root (service edge 2→0) and choose a non-main-clear cell in
the pending owner's freshness footprint/root-sweep window.  Such a raw state
would violate the proposed invariant.  But it cannot satisfy the existing P5
payload if footprint containment holds: the `.scrubL` at label 1 owns and
main-clears the whole 0,1,2 group.  Thus the branch which would have had to
create the bad state is an earlier scrubL-producing/releasing transition that
left a footprint cell non-main-clear.  The depth-32 BFS found no such reachable
state among 1,616,826 states; the source proof still needs the containment
lemma above rather than the finite probe.
-/

end R2CoherenceV31ReachableFreshSeek
