import Leader.Wu.Coherence.FootprintCoverReleaseSeam
import Leader.Wu.Coherence.ReachableFreshCommitSealedSweep
import Leader.Wu.Coherence.OpenNoHazardFreshCover
import Leader.Wu.Coherence.ReleaseCoverGeneral


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31FootprintCover4


open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus4 R2CoherenceV31ReachableAdjacentRoot
open R2CoherenceV31ReachableCover R2CoherenceV31ReachableCover2
open R2CoherenceV31FootprintCover2R R2CoherenceV31FootprintCover3
open R2CoherenceV31OpenNoHazardServedCover R2CoherenceV31ReleaseCoverGeneral
open R2CoherenceV31MainClearTruth R2CoherenceV31MainClearTruth.WeakFreshnessLayer
open R2CoherenceV31ReachableSweepFresh R2CoherenceV31FreshnessClear
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31ReachableSoundFresh
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableScrubL3


variable {n ψ κ τ : Nat}


def PendingFootprintCoveredReachableFreshV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ, ReachableFromQuarantineV31 hψ h2 ring C →
    ElectionGeometryV31 ring C → PendingOpenRFootprintCoveredFreshV31 ring C


theorem foreignFresh_of_coveredFresh (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : PendingOpenRFootprintCoveredFreshV31 ring C) :
    PendingOwnerForeignFootprintFreshV31 ring C := by
  intro owner p hp hf hout
  rcases h owner p hp hf with hc | hg
  · exact hc
  · exact (hout hg).elim


theorem foreignFresh_entrance (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hB : BirthEntranceV1 hψ h2 ring C) :
    PendingOwnerForeignFootprintFreshV31 ring C := by
  intro owner p hp hf hout
  exact freshnessClear_of_mainClear _
    (pendingOwnerForeignFootprintMainClear_entrance hψ h2 ring C hB owner p hp hf hout)


private theorem gp4 (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change
    R2Coherence.fwd ring
        (R2Coherence.back ring i (raw (D i)).label.val) k =
      R2Coherence.fwd ring
        (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [h i]


private theorem pp4 (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change
    R2Coherence.back ring i ((raw (D i)).label.val - k) =
      R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [h i]


private theorem footprintBack4 (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n) (hf : InOpenRFreshFootprintV31 ring D owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  rcases hf with ⟨j, ko, q, ho, kD, hp⟩
  rw [gp4 ring h j ko.val] at ho
  let f := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hq : R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = f := by
    simpa [f] using gp4 ring h j q.val
  have hv : (raw (D (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val))).label.val =
      (raw (C f)).label.val := by rw [hq]; exact congrArg Fin.val (h f)
  let kC : Fin ((raw (C f)).label.val + 1) :=
    ⟨kD.val, by simpa only [hv] using kD.isLt⟩
  refine ⟨j, ko, q, ho, kC, ?_⟩
  have hp' : R2Coherence.prefixPos ring (eraseCfgV3 D) f kD.val = p := by
    simpa only [hq] using hp
  simpa [f, kC] using (pp4 ring h f kD.val).symm.trans hp'


private theorem groupForward4 (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (o p : Fin n) (hg : InGroupOwnedFootprintV31 ring C o p) :
    InGroupOwnedFootprintV31 ring D o p := by
  rcases hg with ⟨k, hk⟩
  exact ⟨k, (gp4 ring h o k.val).trans hk⟩


private theorem rowFresh4 {b : BranchV3}
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = b)
    (hn : b ≠ .openNoHazard) :
    (FreshnessClearV31 l →
      FreshnessClearV31 (rowV3 hψ (by decide) h2 l r).1) ∧
    (FreshnessClearV31 r →
      FreshnessClearV31 (rowV3 hψ (by decide) h2 l r).2) :=
  rowFreshFact4 hψ h2 l r hb hn


private theorem freshStep4 {b : BranchV3}
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b)
    (hn : b ≠ .openNoHazard) (hf : FreshnessClearV31 (C p)) :
    FreshnessClearV31 (stepV3 hψ h2 ring C e p) := by
  have h := rowFresh4 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb hn
  by_cases he : p = e
  · subst p
    simpa [stepV3, protocolV3, PopulationProtocol.step] using h.1 hf
  · by_cases hr : p = ring.rightNeighbor e
    · subst p
      simpa [stepV3, protocolV3, PopulationProtocol.step, he] using h.2 hf
    · rw [stepV3_other hψ h2 ring C e p he hr]
      exact hf

private theorem pendingBack4 {b : BranchV3}
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b)
    (hr : b ≠ .release) (hs : b ≠ .scrubL)
    (hp : PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner) :
    PendingOpenROwnerV31 ring C owner := by
  have hrow := rowScrubBack2 hψ h2
    (C e) (C (ring.rightNeighbor e)) hb hr hs
  have htok : ∀ p,
      (stepV3 hψ h2 ring C e p).ctl.tok = .scrubL →
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


private theorem foreignFresh_safe4 {b : BranchV3}
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hP : PendingOwnerForeignFootprintFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b)
    (hr : b ≠ .release) (hs : b ≠ .scrubL)
    (hn : b ≠ .openNoHazard) :
    PendingOwnerForeignFootprintFreshV31 ring
      (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label :=
    fun p => by
      simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  intro owner p hpD hfD houtD
  have hpC := pendingBack4 hψ h2 ring C e owner hb hr hs hpD
  have hfC := footprintBack4 ring hLab owner p hfD
  have houtC :
      ¬ InGroupOwnedFootprintV31 ring C
          (ring.rightNeighbor owner) p :=
    fun hg => houtD (groupForward4 ring hLab _ _ hg)
  exact freshStep4 hψ h2 ring C e p hb hn
    (hP owner p hpC hfC houtC)


theorem foreignFresh_seek_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hP : PendingOwnerForeignFootprintFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .seek) :
    PendingOwnerForeignFootprintFreshV31 ring (stepV3 hψ h2 ring C e) :=
  foreignFresh_safe4 hψ h2 ring C e hP hb
    (by decide) (by decide) (by decide)
theorem foreignFresh_sweep_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hP : PendingOwnerForeignFootprintFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    PendingOwnerForeignFootprintFreshV31 ring (stepV3 hψ h2 ring C e) :=
  foreignFresh_safe4 hψ h2 ring C e hP hb
    (by decide) (by decide) (by decide)
theorem foreignFresh_commit_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hP : PendingOwnerForeignFootprintFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    PendingOwnerForeignFootprintFreshV31 ring (stepV3 hψ h2 ring C e) :=
  foreignFresh_safe4 hψ h2 ring C e hP hb
    (by decide) (by decide) (by decide)
theorem foreignFresh_openR_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hP : PendingOwnerForeignFootprintFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR) :
    PendingOwnerForeignFootprintFreshV31 ring (stepV3 hψ h2 ring C e) :=
  foreignFresh_safe4 hψ h2 ring C e hP hb
    (by decide) (by decide) (by decide)
theorem foreignFresh_sealed_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hP : PendingOwnerForeignFootprintFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sealed) :
    PendingOwnerForeignFootprintFreshV31 ring (stepV3 hψ h2 ring C e) :=
  foreignFresh_safe4 hψ h2 ring C e hP hb
    (by decide) (by decide) (by decide)
theorem foreignFresh_openHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hP : PendingOwnerForeignFootprintFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    PendingOwnerForeignFootprintFreshV31 ring (stepV3 hψ h2 ring C e) :=
  foreignFresh_safe4 hψ h2 ring C e hP hb
    (by decide) (by decide) (by decide)
theorem foreignFresh_mixed_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hP : PendingOwnerForeignFootprintFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .mixed) :
    PendingOwnerForeignFootprintFreshV31 ring (stepV3 hψ h2 ring C e) :=
  foreignFresh_safe4 hψ h2 ring C e hP hb
    (by decide) (by decide) (by decide)


theorem foreignFresh_release_step_gt_two
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (h3 : 2 < ψ) (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hP : PendingOwnerForeignFootprintFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    PendingOwnerForeignFootprintFreshV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label :=
    fun p => by simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  intro owner p hpD hfD houtD
  by_cases hpC : PendingOpenROwnerV31 ring C owner
  · exact freshStep4 hψ h2 ring C e p hb (by decide)
      (hP owner p hpC (footprintBack4 ring hLab owner p hfD)
        (fun hg => houtD (groupForward4 ring hLab _ _ hg)))
  · have heq := releaseNewPending_forces_psi_two hψ h2 ring C e owner hb hpD hpC
    omega


theorem foreignFresh_scrubL_step_of_foreignPrefix
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hForeign : ScrubLContinuationForeignPrefixMainClearV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n) (hg : ElectionGeometryV31 ring C)
    (ht : ReachableFromQuarantineV31 hψ h2 ring C)
    (hp : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hP : PendingOwnerForeignFootprintFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL) :
    PendingOwnerForeignFootprintFreshV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label :=
    fun p => by simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  intro owner p hpD hfD houtD
  by_cases hpC : PendingOpenROwnerV31 ring C owner
  · exact freshStep4 hψ h2 ring C e p hb (by decide)
      (hP owner p hpC (footprintBack4 ring hLab owner p hfD)
        (fun hg0 => houtD (groupForward4 ring hLab _ _ hg0)))
  · have hn : ScrubLContinuationNewPendingV31 hψ h2 ring C e owner := ⟨hpD, hpC⟩
    have hc := scrubLContinuationNewPendingCover_of_foreignPrefix
      (κ := κ) (τ := τ) hψ h2 ring hForeign C e owner hg ht hp hb hn p hfD
    rcases hc with hm | hgroup
    · exact freshnessClear_of_mainClear _ hm
    · exact (houtD hgroup).elim


/-- No served-cell premise survives in Fresh currency. -/
theorem foreignFresh_openNoHazard_step (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hP : PendingOwnerForeignFootprintFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    PendingOwnerForeignFootprintFreshV31 ring (stepV3 hψ h2 ring C e) := by
  exact foreignFresh_of_coveredFresh ring _
    (pendingCoveredFresh_openNoHazard_step hψ h2 ring C e
      (pendingCoveredFresh_of_foreignFresh ring C hP) hb)

theorem foreignFresh_step_gt_two_of_scrubL
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (h3 : 2 < ψ)
    (ring : DirectedRing n)
    (hForeign : ScrubLContinuationForeignPrefixMainClearV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hg : ElectionGeometryV31 ring C)
    (ht : ReachableFromQuarantineV31 hψ h2 ring C)
    (hp : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hP : PendingOwnerForeignFootprintFreshV31 ring C) :
    PendingOwnerForeignFootprintFreshV31 ring (stepV3 hψ h2 ring C e) := by
  cases hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) with
  | seek => exact foreignFresh_seek_step hψ h2 ring C e hP hb
  | sweep => exact foreignFresh_sweep_step hψ h2 ring C e hP hb
  | commit => exact foreignFresh_commit_step hψ h2 ring C e hP hb
  | release => exact foreignFresh_release_step_gt_two hψ h2 h3 ring C e hP hb
  | scrubL => exact foreignFresh_scrubL_step_of_foreignPrefix hψ h2 ring hForeign C e hg ht hp hP hb
  | openR => exact foreignFresh_openR_step hψ h2 ring C e hP hb
  | sealed => exact foreignFresh_sealed_step hψ h2 ring C e hP hb
  | openHazard => exact foreignFresh_openHazard_step hψ h2 ring C e hP hb
  | openNoHazard => exact foreignFresh_openNoHazard_step hψ h2 ring C e hP hb
  | mixed => exact foreignFresh_mixed_step hψ h2 ring C e hP hb

open R2CoherenceV31ReachableFreshBranches1 in
open R2CoherenceV31ReachableFreshBranches1


private theorem traceStep4 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (h : ReachableFromQuarantineV31 hψ h2 ring C) :
    ReachableFromQuarantineV31 hψ h2 ring (stepV3 hψ h2 ring C e) := by
  rcases h with ⟨C0, w, hb, hC⟩
  refine ⟨C0, w ++ [e], hb, ?_⟩
  rw [List.foldl_append, ← hC]
  rfl


theorem pendingFootprintCoveredReachableFresh_of_scrubL_gt_two
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (h3 : 2 < ψ)
    (ring : DirectedRing n)
    (hPayload : Cover3PayloadReachableV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hForeign : ScrubLContinuationForeignPrefixMainClearV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    PendingFootprintCoveredReachableFreshV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C hTrace _hg
  rcases hTrace with ⟨C0, w, hBirth, hC⟩
  have h0 := foreignFresh_entrance hψ h2 ring C0 hBirth
  have carry : ∀ (v : List (Fin n)) (D : FC n ψ κ τ),
      ReachableFromQuarantineV31 hψ h2 ring D →
      ElectionGeometryV31 ring D →
      PendingOwnerForeignFootprintFreshV31 ring D →
      PendingOwnerForeignFootprintFreshV31 ring
        (v.foldl (stepV3 hψ h2 ring) D) := by
    intro v
    induction v with
    | nil => intro D _ _ hP; simpa using hP
    | cons e v ih =>
      intro D ht hg hP
      simp only [List.foldl_cons]
      have h1 := foreignFresh_step_gt_two_of_scrubL
        hψ h2 h3 ring hForeign D e hg ht
          (hPayload D ht) hP
      exact ih _ (traceStep4 hψ h2 ring D e ht)
        ((electionGeometryStepV31 (κ := κ) (τ := τ)
          hψ h2 ring) D e hg) h1
  have hF : PendingOwnerForeignFootprintFreshV31 ring C := by
    rw [hC]
    exact carry w C0 ⟨C0, [], hBirth, rfl⟩ hBirth.2 h0
  exact pendingCoveredFresh_of_foreignFresh ring C hF


theorem sweepStrongTailPreservationFresh_of_freshCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableFreshV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    R2CoherenceV31ReachableFreshBranches1.SweepStrongTailPreservationFreshV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hg ht hf hb
  rcases hf with ⟨hFacts, _h7, _h8, _h9, _hS, hR1, _hF⟩
  let D := stepV3 hψ h2 ring C e
  have htD : ReachableFromQuarantineV31 hψ h2 ring D := by
    simpa [D] using traceStep4 hψ h2 ring C e ht
  have hgD : ElectionGeometryV31 ring D := by
    simpa [D] using
      (electionGeometryStepV31 (κ := κ) (τ := τ) hψ h2 ring C e hg)
  have hcD := hCov D htD hgD
  have hPhaseD : PhaseMainClearV31 ring D := by
    simpa [D] using R2CoherenceV31ReachableSweep.sweepStep_reachable_phase
      hψ h2 ring C e ht hFacts hb
  have safe : ∀ owner p, PendingOpenROwnerV31 ring D owner →
      SweepOpenRSafeFreshV31 ring D owner p := by
    intro owner p hp
    exact pendingSafeFresh_of_coveredFresh ring D hPhaseD hcD owner p hp
  have hS : SeekIncomingSweepOpenROverlapFreshWideV31 ring D := by
    intro pred owner _ hp
    exact ⟨(fun _ => ⟨safe owner (ring.rightNeighbor (ring.rightNeighbor pred)) hp,
      fun d => safe owner (R2Coherence.fwd ring (ring.rightNeighbor pred) d.val) hp⟩),
      (fun _ _ => ⟨safe owner (ring.rightNeighbor pred) hp,
        fun d => safe owner (R2Coherence.fwd ring pred d.val) hp⟩)⟩
  have hR1D : OpenRForwardFreshnessClearV31 ring D := by
    simpa [D] using
      openRForwardFreshnessClear_sweep_step hψ h2 ring C e hR1 hb
  have hFD : R2CoherenceV31FreshnessClear.SweepPendingOpenRFootprintOwnedV31F ring D := by
    intro sweep owner p _ hp _ hfoot
    rcases safe owner p hp with hc | hout
    · exact Or.inr hc
    · exact (hout hfoot).elim
  exact ⟨hS, hR1D, hFD⟩


def freshResidualLedgerOpenCountAfterCover4 : Nat := 6



end R2CoherenceV31FootprintCover4
