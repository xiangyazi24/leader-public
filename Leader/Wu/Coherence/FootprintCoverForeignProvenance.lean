import Leader.Wu.Coherence.RowFacts

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31FootprintCover2R

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus4 R2CoherenceV31ReachableAdjacentRoot
open R2CoherenceV31ReachableCover R2CoherenceV31ReachableCover2
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31FootprintCover
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31ReachableSoundFresh

variable {n ψ κ τ : Nat}

/-- The row main-clear fact, **proved** in `R2CoherenceV31RowFacts`.

It used to be threaded through this file as an unsupplied hypothesis `hMain`;
now that a producer exists, the hypothesis is gone from every signature and the
original `rowMainClear2` name is restored. -/
theorem rowMainClear2 : RowMainClearFactV31 ψ κ τ :=
  R2CoherenceV31RowFacts.rowMainClearFact_holds

/-- The row scrub-back fact, **proved** in `R2CoherenceV31RowFacts`.  Formerly
threaded as the unsupplied hypothesis `hScrub`; the hypothesis is gone and the
original `rowScrubBack2` name is restored. -/
theorem rowScrubBack2 : RowScrubBackFactV31 ψ κ τ :=
  R2CoherenceV31RowFacts.rowScrubBackFact_holds

/-- The row freshness fact, **proved** in `R2CoherenceV31RowFacts`.  Formerly
threaded as the unsupplied hypothesis `hFresh`; the hypothesis is gone and the
original `rowFresh4` name is restored in `R2CoherenceV31FootprintCover4`. -/
theorem rowFreshFact4 : RowFreshFactV31 ψ κ τ :=
  R2CoherenceV31RowFacts.rowFreshFact_holds

def PendingOwnerForeignFootprintMainClearV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ owner p : Fin n,
    PendingOpenROwnerV31 ring C owner →
    InOpenRFreshFootprintV31 ring C owner p →
    ¬ InGroupOwnedFootprintV31 ring C (ring.rightNeighbor owner) p →
      MainClearV3 (C p)

private theorem covered_of_foreign
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : PendingOwnerForeignFootprintMainClearV31 ring C) :
    PendingOpenRFootprintCoveredV31 ring C := by
  intro owner p hp hf
  by_cases hg : InGroupOwnedFootprintV31 ring C (ring.rightNeighbor owner) p
  · exact Or.inr hg
  · exact Or.inl (h owner p hp hf hg)

private theorem foreign_of_covered
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : PendingOpenRFootprintCoveredV31 ring C) :
    PendingOwnerForeignFootprintMainClearV31 ring C := by
  intro owner p hp hf hout
  rcases h owner p hp hf with hm | hg
  · exact hm
  · exact (hout hg).elim

private theorem mainClearStepR {b : BranchV3}
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b)
    (hn : b ≠ .openNoHazard) :
    CoverMainClearStepV31 C (stepV3 hψ h2 ring C e) := by
  have h := rowMainClear2 hψ h2 (C e) (C (ring.rightNeighbor e)) hb hn
  intro p hm
  by_cases hp : p = e
  · subst p; simpa [stepV3, protocolV3, PopulationProtocol.step] using h.1 hm
  · by_cases hq : p = ring.rightNeighbor e
    · subst p
      simpa [stepV3, protocolV3, PopulationProtocol.step, hp] using h.2 hm
    · rw [stepV3_other hψ h2 ring C e p hp hq]; exact hm

private theorem pendingBackR {b : BranchV3}
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b)
    (hr : b ≠ .release) (hs : b ≠ .scrubL)
    (hp : PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner) :
    PendingOpenROwnerV31 ring C owner := by
  have hrow := rowScrubBack2 hψ h2 (C e) (C (ring.rightNeighbor e)) hb hr hs
  have htok : ∀ p, (stepV3 hψ h2 ring C e p).ctl.tok = .scrubL →
      (C p).ctl.tok = .scrubL := by
    intro p ht
    by_cases he : p = e
    · subst p
      apply hrow.1
      simpa [stepV3, protocolV3, PopulationProtocol.step] using ht
    · by_cases hq : p = ring.rightNeighbor e
      · subst p
        apply hrow.2
        simpa [stepV3, protocolV3, PopulationProtocol.step, he] using ht
      · simpa [stepV3_other hψ h2 ring C e p he hq] using ht
  rcases hp with ⟨ht, hu, hz⟩
  refine ⟨htok _ ht, ?_, ?_⟩
  · have h0 := congrArg Fin.val
      (stepV3_labels_eq_or_held hψ h2 ring C e owner)
    have h1 := congrArg Fin.val
      (stepV3_labels_eq_or_held hψ h2 ring C e
        (ring.rightNeighbor owner))
    unfold successorB at hu ⊢
    simpa only [h0, h1] using hu
  · have h0 := congrArg Fin.val
      (stepV3_labels_eq_or_held hψ h2 ring C e owner)
    unfold atRootB at hz ⊢
    simpa only [h0] using hz

private theorem foreignSafeR {b : BranchV3}
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hP : PendingOwnerForeignFootprintMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b)
    (hr : b ≠ .release) (hs : b ≠ .scrubL) (hn : b ≠ .openNoHazard) :
    PendingOwnerForeignFootprintMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  have hMC := mainClearStepR hψ h2 ring C e hb hn
  have hNew : CoverNewPendingStepV31 ring C (stepV3 hψ h2 ring C e) := by
    intro owner p hpD hpC _
    exact (hpC (pendingBackR hψ h2 ring C e owner hb hr hs hpD)).elim
  have hCov := pendingCover_step_of_old_new ring
    (stepV3_labels_eq_or_held hψ h2 ring C e) hMC hNew
    (covered_of_foreign ring C hP)
  exact foreign_of_covered ring _ hCov

theorem foreignProvenance_seek_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (hP : PendingOwnerForeignFootprintMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    PendingOwnerForeignFootprintMainClearV31 ring (stepV3 hψ h2 ring C e) :=
  foreignSafeR hψ h2 ring C e hP hb (by decide) (by decide) (by decide)

theorem foreignProvenance_sweep_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (hP : PendingOwnerForeignFootprintMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    PendingOwnerForeignFootprintMainClearV31 ring (stepV3 hψ h2 ring C e) :=
  foreignSafeR hψ h2 ring C e hP hb (by decide) (by decide) (by decide)

theorem foreignProvenance_commit_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (hP : PendingOwnerForeignFootprintMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    PendingOwnerForeignFootprintMainClearV31 ring (stepV3 hψ h2 ring C e) :=
  foreignSafeR hψ h2 ring C e hP hb (by decide) (by decide) (by decide)

theorem foreignProvenance_openR_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (hP : PendingOwnerForeignFootprintMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR) :
    PendingOwnerForeignFootprintMainClearV31 ring (stepV3 hψ h2 ring C e) :=
  foreignSafeR hψ h2 ring C e hP hb (by decide) (by decide) (by decide)

theorem foreignProvenance_sealed_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (hP : PendingOwnerForeignFootprintMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sealed) :
    PendingOwnerForeignFootprintMainClearV31 ring (stepV3 hψ h2 ring C e) :=
  foreignSafeR hψ h2 ring C e hP hb (by decide) (by decide) (by decide)

theorem foreignProvenance_openHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (hP : PendingOwnerForeignFootprintMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    PendingOwnerForeignFootprintMainClearV31 ring (stepV3 hψ h2 ring C e) :=
  foreignSafeR hψ h2 ring C e hP hb (by decide) (by decide) (by decide)

theorem foreignProvenance_mixed_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (hP : PendingOwnerForeignFootprintMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .mixed) :
    PendingOwnerForeignFootprintMainClearV31 ring (stepV3 hψ h2 ring C e) :=
  foreignSafeR hψ h2 ring C e hP hb (by decide) (by decide) (by decide)

theorem foreignProvenance_scrubL_step_of_foreignPrefix
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hForeign : ScrubLContinuationForeignPrefixMainClearV31 (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hg : ElectionGeometryV31 ring C) (ht : ReachableFromQuarantineV31 hψ h2 ring C)
    (hp : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hP : PendingOwnerForeignFootprintMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL) :
    PendingOwnerForeignFootprintMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  have hMC := mainClearStepR hψ h2 ring C e hb (by decide)
  have hNew : CoverNewPendingStepV31 ring C (stepV3 hψ h2 ring C e) := by
    intro owner p hD hC hF
    have hn : R2CoherenceV31ReachableScrubL3.ScrubLContinuationNewPendingV31
        hψ h2 ring C e owner := ⟨hD, hC⟩
    exact (scrubLContinuationNewPendingCover_of_foreignPrefix
      (κ := κ) (τ := τ) hψ h2 ring hForeign C e owner hg ht hp hb hn) p hF
  have hCov := pendingCover_step_of_old_new ring
    (stepV3_labels_eq_or_held hψ h2 ring C e) hMC hNew
    (covered_of_foreign ring C hP)
  exact foreign_of_covered ring _ hCov


def PendingOwnerForeignFootprintMainClearReachableV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    ReachableFromQuarantineV31 hψ h2 ring C →
      PendingOwnerForeignFootprintMainClearV31 ring C

theorem pendingFootprintCovered_of_foreignProvenance
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : PendingOwnerForeignFootprintMainClearV31 ring C) :
    PendingOpenRFootprintCoveredV31 ring C :=
  covered_of_foreign ring C h

theorem foreignProvenance_of_pendingFootprintCovered
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : PendingOpenRFootprintCoveredV31 ring C) :
    PendingOwnerForeignFootprintMainClearV31 ring C :=
  foreign_of_covered ring C h

theorem pendingOwnerForeignFootprintMainClear_quarantineInit
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    PendingOwnerForeignFootprintMainClearV31 ring (quarantineInitV31 C) := by
  intro owner p hp _ _
  have hs := hp.1
  simp [quarantineInitV31, setControl] at hs

theorem pendingOwnerForeignFootprintMainClear_entrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (hB : BirthEntranceV1 hψ h2 ring C) :
    PendingOwnerForeignFootprintMainClearV31 ring C := by
  rcases hB.1 with ⟨_, Q, _, hEq⟩
  rw [hEq]
  exact pendingOwnerForeignFootprintMainClear_quarantineInit ring Q

theorem pendingFootprintCoveredReachable_of_foreignProvenance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hP : PendingOwnerForeignFootprintMainClearReachableV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring := by
  intro C hTrace _hGeom
  exact pendingFootprintCovered_of_foreignProvenance ring C (hP C hTrace)


end R2CoherenceV31FootprintCover2R
