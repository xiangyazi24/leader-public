import Leader.Wu.Coherence.ReachableOpenROverlap

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableOpenR4

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure2
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableOpenR2
open R2CoherenceV31ReachableOpenR3

variable {n ψ κ τ : Nat}

/-- First unclosed OpenR4 clause.

On the bad OPEN-R arm, `startClosing (C e)` creates a new `.seek` token at
`e`.  For S (`SeekIncomingSweepOpenROverlapClearWideV31`), the old S
hypothesis cannot cover that token.  The root case can be supplied from the
old openR owner's forward-main-clear suffix (R1).  The remaining case is the
second S arm: the new seek site `e` is non-root, while a predecessor `pred`
with `rightNeighbor pred = e` is root.  S then requires safety at `e` and on
the whole forward read rooted at `pred`.

The current strong-Plus4 payload contains no clause that implies this
predecessor-root-wide safety merely from an openR at `e` whose right edge is
non-successor.  This Prop records exactly that missing semantic bridge. -/
def OpenRBadNewSeekPredecessorRootPrepaidV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e pred owner : Fin n),
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR →
    successorB (C e) (C (ring.rightNeighbor e)) = false →
    ring.rightNeighbor pred = e →
    let D := stepV3 hψ h2 ring C e
    PendingOpenROwnerV31 ring D owner →
    atRootB (D e) = false →
    atRootB (D pred) = true →
      SweepOpenRSafeAtV31 ring D owner e ∧
      ∀ d : Fin (ψ - (raw (D pred)).label.val),
        SweepOpenRSafeAtV31 ring D owner
          (R2Coherence.fwd ring pred d.val)

/-
STOP at S, before asserting any S-preservation theorem.

Why this is first:
* good OPEN-R creates no `.seek`, so post-state seek owners are old owners;
* bad OPEN-R creates exactly the fresh left `.seek` via `startClosing`;
* the first (new-seek-at-root) S arm is R1-shaped;
* the second (new-seek-nonroot / predecessor-root) arm is the first place
  where the current payload gives no whole predecessor-root safety source.

Consequently `OpenRForwardMainClearV31` self-preservation,
`OpenRPhaseOwnershipDisjointStrongV31` self-preservation, and
`openRStep_reachable_full` are not asserted in this file, per the instruction
to stop at the first clause that cannot be closed.
-/


end R2CoherenceV31ReachableOpenR4
