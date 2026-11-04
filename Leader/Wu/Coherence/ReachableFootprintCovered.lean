import Leader.Wu.Coherence.ReachableReleaseOwnerAdjacentRoot
import Leader.Wu.Coherence.ReachableFreshSeekWindow

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableAdjacentRoot

open PPLL PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach R2CoherenceV31PhaseMainClear R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachablePlus2 R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableFreshSeek
open R2CoherenceV31ReachableReleaseOwner2

variable {n psi kappa tau : Nat}

/-- Exact weakening of footprint containment needed by S:
a freshness-footprint cell is either already main-clear, or it belongs to
the scrubL successor's P5-owned group. -/
def PendingOpenRFootprintCoveredV31
    (ring : DirectedRing n) (C : FC n psi kappa tau) : Prop :=
  forall (owner p : Fin n),
    PendingOpenROwnerV31 ring C owner ->
    InOpenRFreshFootprintV31 ring C owner p ->
      MainClearV3 (C p) ∨
      InGroupOwnedFootprintV31 ring C (ring.rightNeighbor owner) p

/-- P5 plus the weaker cover gives the pointwise fact S actually consumes. -/
theorem pendingOwner_safe_everywhere_of_covered
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hFacts : ReachablePhaseFactsV31 ring C)
    (hCover : PendingOpenRFootprintCoveredV31 ring C)
    (owner p : Fin n)
    (hPending : PendingOpenROwnerV31 ring C owner) :
    SweepOpenRSafeAtV31 ring C owner p := by
  unfold SweepOpenRSafeAtV31
  by_cases hf : InOpenRFreshFootprintV31 ring C owner p
  · rcases hCover owner p hPending hf with hc | hg
    · exact Or.inl hc
    · left
      rcases hFacts with ⟨_, _, _, _, hScrub, _⟩
      have hs := hScrub (ring.rightNeighbor owner) hPending.1
      have hGroup := hs.2.2
      rcases hg with ⟨k, hk⟩
      unfold GroupOwnedClearV31 at hGroup
      rw [← hk]
      exact (hGroup k).1
  · exact Or.inr hf

/-- psi=2 arithmetic reduction still needed: any freshness-footprint cell
outside the scrubL group must be the adjacent root immediately before owner. -/
def Psi2PendingFootprintDichotomyV31
    (ring : DirectedRing n) (C : FC n 2 kappa tau) : Prop :=
  forall (owner p : Fin n),
    PendingOpenROwnerV31 ring C owner ->
    InOpenRFreshFootprintV31 ring C owner p ->
      InGroupOwnedFootprintV31 ring C (ring.rightNeighbor owner) p ∨
      exists pred : Fin n,
        ring.rightNeighbor pred = owner /\
        atRootB (C pred) = true /\ p = pred

theorem pendingFootprintCovered_psi2_of_dichotomy
    (ring : DirectedRing n) (C : FC n 2 kappa tau)
    (hAdj : AdjacentRootPredecessorMainClearPsi2V31 ring C)
    (hDich : Psi2PendingFootprintDichotomyV31 ring C) :
    PendingOpenRFootprintCoveredV31 ring C := by
  intro owner p hPending hFoot
  rcases hDich owner p hPending hFoot with hg | ⟨pred, hp, hr, hEq⟩
  · exact Or.inr hg
  · left
    rw [hEq]
    apply hAdj pred hr
    rw [hp]
    exact hPending.2.2

/-- General-psi replacement for the old containment reachability target. -/
def PendingFootprintCoveredReachableV31
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) : Prop :=
  forall C : FC n psi kappa tau,
    ReachableFromQuarantineV31 hpsi h2 ring C ->
    ElectionGeometryV31 ring C ->
      PendingOpenRFootprintCoveredV31 ring C


end R2CoherenceV31ReachableAdjacentRoot

namespace R2CoherenceV31ReachableAdjacentRoot

open R2CoherenceV31Closure2 R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePlus2 R2CoherenceV31ReachablePlus4 R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachableReleaseOwner2

variable {n kappa tau : Nat}

theorem adjacentRootMainClear_quarantineInit
    (ring : DirectedRing n) (C : FC n 2 kappa tau)
    (h : AdjacentRootPredecessorMainClearPsi2V31 ring C) :
    AdjacentRootPredecessorMainClearPsi2V31 ring (quarantineInitV31 C) := by
  intro p hp hnext
  have hpC : atRootB (C p) = true := by
    simpa [quarantineInitV31, setControl, atRootB, raw] using hp
  have hnextC : atRootB (C (ring.rightNeighbor p)) = true := by
    simpa [quarantineInitV31, setControl, atRootB, raw] using hnext
  have hm : MainClearV3 (C p) := h p hpC hnextC
  unfold MainClearV3 R2CoherenceBranches.MainClear at hm ⊢
  simpa [quarantineInitV31, setControl, eraseCellV3,
    R2Coherence.raw] using hm

/-- Producer debt for a real entrance: arbitrary quarantine input does not
satisfy adjacent-root main-clear merely from controller reset. -/
def BirthAdjacentRootPredecessorMainClearPsi2V31
    (ring : DirectedRing n) : Prop :=
  forall Q : FC n 2 kappa tau,
    BirthEntranceV1 (by decide : 0 < 2) (by decide : 2 <= 2) ring Q ->
      AdjacentRootPredecessorMainClearPsi2V31 ring Q

/-- First step arm not discharged by source-level clear/control-only analysis. -/
def OpenNoHazardAdjacentRootMainClearPreservationPsi2V31
    (ring : DirectedRing n) : Prop :=
  forall (C : FC n 2 kappa tau) (e : Fin n),
    AdjacentRootPredecessorMainClearPsi2V31 ring C ->
    branchAtV3 (by decide : 0 < 2) (by decide : 2 <= 2)
      (C e) (C (ring.rightNeighbor e)) = .openNoHazard ->
      AdjacentRootPredecessorMainClearPsi2V31 ring
        (stepV3 (by decide : 0 < 2) (by decide : 2 <= 2) ring C e)

/-- Whole-step preservation after supplying the one openNoHazard leaf.
The remaining branches reduce to physical equality or `clearMain` by unfolding
`rowV3` and the stage definitions above. -/
def AdjacentRootPredecessorMainClearStepPsi2V31
    (ring : DirectedRing n) : Prop :=
  forall (C : FC n 2 kappa tau) (e : Fin n),
    AdjacentRootPredecessorMainClearPsi2V31 ring C ->
      AdjacentRootPredecessorMainClearPsi2V31 ring
        (stepV3 (by decide : 0 < 2) (by decide : 2 <= 2) ring C e)

end R2CoherenceV31ReachableAdjacentRoot
