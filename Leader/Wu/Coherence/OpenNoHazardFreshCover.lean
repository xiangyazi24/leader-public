import Leader.Wu.Coherence.FootprintCoverReleaseSeam
import Leader.Wu.Coherence.OpenNoHazardUnframedCarriers

set_option autoImplicit false
set_option Elab.async false

namespace R2CoherenceV31OpenNoHazardServedCover

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachablePlus2 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableAdjacentRoot
open R2CoherenceV31OpenNoHazard
open R2CoherenceV31FootprintCover2R R2CoherenceV31FootprintCover3
open R2CoherenceV31MainClearTruth
open R2CoherenceV31MainClearTruth.WeakFreshnessLayer

variable {n ψ κ τ : Nat}

/-- Exact foreign side required by Fresh, not by the old MainClear cover. -/
def PendingOwnerForeignFootprintFreshV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ owner p : Fin n,
    PendingOpenROwnerV31 ring C owner →
    InOpenRFreshFootprintV31 ring C owner p →
    ¬ InGroupOwnedFootprintV31 ring C (ring.rightNeighbor owner) p →
      FreshnessClearV31 (C p)

/-- Exact direct-side Fresh cover. -/
theorem pendingCoveredFresh_of_foreignFresh
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : PendingOwnerForeignFootprintFreshV31 ring C) :
    PendingOpenRFootprintCoveredFreshV31 ring C := by
  intro owner p hp hf
  by_cases hg :
      InGroupOwnedFootprintV31 ring C (ring.rightNeighbor owner) p
  · exact Or.inr hg
  · exact Or.inl (h owner p hp hf hg)

private theorem gp_eq
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [hLab i]

private theorem pp_eq
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [hLab i]

private theorem footprint_back
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n)
    (hf : InOpenRFreshFootprintV31 ring D owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  rcases hf with ⟨j, ko, q, ho, kD, hp⟩
  rw [gp_eq ring hLab j ko.val] at ho
  let f := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hq : R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = f := by
    simpa [f] using gp_eq ring hLab j q.val
  have hv :
      (raw (D (R2Coherence.groupPos ring
        (eraseCfgV3 D) j q.val))).label.val = (raw (C f)).label.val := by
    rw [hq]
    exact congrArg Fin.val (hLab f)
  let kC : Fin ((raw (C f)).label.val + 1) :=
    ⟨kD.val, by simpa only [hv] using kD.isLt⟩
  refine ⟨j, ko, q, ho, kC, ?_⟩
  have hpD : R2Coherence.prefixPos ring (eraseCfgV3 D) f kD.val = p := by
    simpa only [hq] using hp
  simpa [f, kC] using (pp_eq ring hLab f kD.val).symm.trans hpD

private theorem group_forward
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n)
    (hg : InGroupOwnedFootprintV31 ring C owner p) :
    InGroupOwnedFootprintV31 ring D owner p := by
  rcases hg with ⟨k, hk⟩
  exact ⟨k, (gp_eq ring hLab owner k.val).trans hk⟩

private theorem pending_back
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (owner : Fin n)
    (hp : PendingOpenROwnerV31 ring D owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases hp with ⟨hs, hu, hr⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [(hF (ring.rightNeighbor owner)).2.2.2] at hs
    exact hs
  · have hl := congrArg Fin.val (hF owner).1
    have hh := congrArg Fin.val (hF (ring.rightNeighbor owner)).1
    unfold successorB at hu ⊢
    simpa only [hl, hh] using hu
  · have hl := congrArg Fin.val (hF owner).1
    unfold atRootB at hr ⊢
    simpa only [hl] using hr

/-- OPEN-NO-HAZARD preserves the exact Fresh cover; no served disjointness. -/
theorem pendingCoveredFresh_openNoHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hCov : PendingOpenRFootprintCoveredFreshV31 ring C)
    (hb : branchAtV3 hψ h2
      (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    PendingOpenRFootprintCoveredFreshV31 ring
      (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label :=
    fun p => (hF p).1
  intro owner p hpD hfD
  have hpC := pending_back ring hF owner hpD
  have hfC := footprint_back ring hLab owner p hfD
  rcases hCov owner p hpC hfC with hc | hg
  · exact Or.inl (by
      simpa [D] using
        freshnessClear_openNoHazard_step hψ h2 ring C e p hb hc)
  · exact Or.inr (group_forward ring hLab _ _ hg)

theorem pendingSafeFresh_of_coveredFresh
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hPhase : PhaseMainClearV31 ring C)
    (hCover : PendingOpenRFootprintCoveredFreshV31 ring C)
    (owner p : Fin n) (hp : PendingOpenROwnerV31 ring C owner) :
    SweepOpenRSafeFreshV31 ring C owner p := by
  by_cases hf : InOpenRFreshFootprintV31 ring C owner p
  · rcases hCover owner p hp hf with hc | hg
    · exact Or.inl hc
    · left
      rcases hg with ⟨k, hk⟩
      have hGroup := hPhase.2.2.2.2 (ring.rightNeighbor owner) hp.1
      unfold GroupOwnedClearV31 at hGroup
      rw [← hk]
      exact freshnessClear_of_mainClear _ (hGroup k).1
  · exact Or.inr hf

end R2CoherenceV31OpenNoHazardServedCover
