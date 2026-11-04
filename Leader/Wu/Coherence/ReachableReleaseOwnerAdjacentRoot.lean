import Leader.Wu.Coherence.ReachableReleaseOwnerPsiTwo


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachableReleaseOwner2


open PPLL PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachableReleaseOwner


variable {n κ τ : Nat}


/-- ψ=2 replacement for the false anchoring invariant.
If two roots are physically adjacent, the predecessor root is main-clear. -/
def AdjacentRootPredecessorMainClearPsi2V31
    (ring : DirectedRing n) (C : FC n 2 κ τ) : Prop :=
  ∀ p : Fin n,
    atRootB (C p) = true →
    atRootB (C (ring.rightNeighbor p)) = true →
      MainClearV3 (C p)


/-- Pure arithmetic classification needed by the reduction below.
At ψ=2, every unanchored offset-1 window hitting a root owner comes from
an adjacent root immediately to its left. -/
def Psi2IncomingRootWindowClassifiedV31
    (ring : DirectedRing n) (C : FC n 2 κ τ) : Prop :=
  ∀ (owner j : Fin n),
    atRootB (C owner) = true →
    R2Coherence.groupPos ring (eraseCfgV3 C) j 1 = owner →
      R2Coherence.groupStart ring (eraseCfgV3 C) j = owner ∨
      (atRootB
          (C (R2Coherence.groupStart ring (eraseCfgV3 C) j)) = true ∧
       ring.rightNeighbor
          (R2Coherence.groupStart ring (eraseCfgV3 C) j) = owner)


/-- Once the ψ=2 arithmetic is isolated, the exact P8 residual is just
adjacent-root predecessor main-clear. -/
theorem incomingOverlapMainClear_of_adjacentRootMainClear
    (ring : DirectedRing n) (C : FC n 2 κ τ) (owner : Fin n)
    (hroot : atRootB (C owner) = true)
    (hClass : Psi2IncomingRootWindowClassifiedV31 ring C)
    (hAdj : AdjacentRootPredecessorMainClearPsi2V31 ring C) :
    ReleasePsi2IncomingOverlapMainClearV31 ring C owner := by
  intro j hhit hne
  rcases hClass owner j hroot hhit with hs | hs
  · exact False.elim (hne hs)
  · have hr :
        atRootB
          (C (ring.rightNeighbor
            (R2Coherence.groupStart ring (eraseCfgV3 C) j))) = true := by
      rw [hs.2]
      exact hroot
    exact hAdj _ hs.1 hr


/-- Cleaner formulation avoiding the rewrite above; use this if Lean rejects
that proof term after elaboration. -/
theorem incomingOverlapMainClear_of_adjacentRootMainClear'
    (ring : DirectedRing n) (C : FC n 2 κ τ) (owner : Fin n)
    (hroot : atRootB (C owner) = true)
    (hClass : Psi2IncomingRootWindowClassifiedV31 ring C)
    (hAdj : AdjacentRootPredecessorMainClearPsi2V31 ring C) :
    ReleasePsi2IncomingOverlapMainClearV31 ring C owner := by
  intro j hhit hne
  have hc := hClass owner j hroot hhit
  rcases hc with hc | hc
  · contradiction
  · have hr :
        atRootB
          (C (ring.rightNeighbor
            (R2Coherence.groupStart ring (eraseCfgV3 C) j))) = true := by
      rw [hc.2]
      exact hroot
    exact hAdj _ hc.1 hr


end R2CoherenceV31ReachableReleaseOwner2
