import Leader.Wu.Coherence.ReachableBirthLabelProfile
import Leader.Wu.Coherence.ReachableReleaseWide

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableReleaseOwner

open PPLL PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus2 R2CoherenceV31ReachablePlus3
open R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableRootSpacing2
open R2CoherenceV31ReachableRelease3

variable {n ψ κ τ : Nat}

/-- Root + literal successor + terminal is possible only at ψ = 2.
The responder is label 1. -/
theorem root_successor_terminal_forces_psi_two
    (l r : Cell ψ κ τ)
    (hroot : atRootB l = true)
    (hsucc : successorB l r = true)
    (hterm : atTerminalB r = true) :
    ψ = 2 ∧ (raw r).label.val = 1 := by
  have h0 : (raw l).label.val = 0 := by
    simpa [atRootB] using hroot
  have h1 : (raw r).label.val = (raw l).label.val + 1 := by
    simpa [successorB] using hsucc
  have ht : (raw r).label.val + 1 = ψ := by
    simpa [atTerminalB] using hterm
  constructor <;> omega

/-- The only structural fact still missing after ψ collapses to 2:
no computed two-cell window may hit the fresh root owner at offset 1
unless that window already computes the same root as its group start.

This is exactly the `ko = 1` case of the new-owner anchoring residual;
`ko = 0` is tautological after unfolding `groupPos`. -/
def ReleasePsi2IncomingWindowAnchoredV31
    (ring : DirectedRing n) (C : FC n 2 κ τ) (owner : Fin n) : Prop :=
  ∀ j : Fin n,
    R2Coherence.groupPos ring (eraseCfgV3 C) j 1 = owner →
      R2Coherence.groupStart ring (eraseCfgV3 C) j = owner

/-- P8 has a weaker escape hatch than anchoring: if the one overlapping
cell is main-clear, P8 can hold even when the incoming window is not anchored.
This names precisely that alternative rather than conflating it with the
structural anchoring statement. -/
def ReleasePsi2IncomingOverlapMainClearV31
    (ring : DirectedRing n) (C : FC n 2 κ τ) (owner : Fin n) : Prop :=
  ∀ j : Fin n,
    R2Coherence.groupPos ring (eraseCfgV3 C) j 1 = owner →
    R2Coherence.groupStart ring (eraseCfgV3 C) j ≠ owner →
      MainClearV3
        (C (R2Coherence.groupStart ring (eraseCfgV3 C) j))

/-- ElectionGeometry does not supply the missing incoming-window clause.
For an edge whose responder is root, its root disjunct already proves
`passiveEdgeOKV3`; no successor/label-1 conclusion is available. -/
theorem electionGeometry_root_edge_is_uninformative
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hGeom : ElectionGeometryV31 ring C)
    (pred : Fin n)
    (hroot : atRootB (C (ring.rightNeighbor pred)) = true) :
    passiveEdgeOKV3 (C pred) (C (ring.rightNeighbor pred)) = true := by
  simpa [passiveEdgeOKV3, hroot]

end R2CoherenceV31ReachableReleaseOwner
