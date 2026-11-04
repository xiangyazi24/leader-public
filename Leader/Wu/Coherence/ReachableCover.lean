import Leader.Wu.Coherence.ReachableScrubLNewPending
import Leader.Wu.Coherence.ReachableMixed
import Leader.Wu.Coherence.ReachableOpenHazardPrepaid


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachableCover


open PPLL PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableAdjacentRoot
open R2CoherenceV31ReachableScrubL3


variable {n ψ κ τ : Nat}


theorem pendingOpenRFootprintCovered_quarantineInit
    (ring : DirectedRing n) (C : FC n ψ κ τ) :
    PendingOpenRFootprintCoveredV31 ring (quarantineInitV31 C) := by
  intro owner p hp
  have hs := hp.1
  simp [quarantineInitV31, setControl] at hs


private theorem gpC (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [hL i]


private theorem ppC (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [hL i]


private theorem footprintBackC
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n)
    (h : InOpenRFreshFootprintV31 ring D owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  rcases h with ⟨j, ko, q, ho, kD, hp⟩
  rw [gpC ring hL j ko.val] at ho
  have hq := gpC ring hL j q.val
  let f := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hfd : R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = f := by
    simpa [f] using hq
  have hv :
      (raw (D (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val))).label.val =
        (raw (C f)).label.val := by
    rw [hfd]; exact congrArg Fin.val (hL f)
  have hk : kD.val < (raw (C f)).label.val + 1 := by
    simpa only [hv] using kD.isLt
  let kC : Fin ((raw (C f)).label.val + 1) := ⟨kD.val, hk⟩
  refine ⟨j, ko, q, ho, kC, ?_⟩
  have h0 : R2Coherence.prefixPos ring (eraseCfgV3 D) f kD.val = p := by
    simpa only [hfd] using hp
  simpa [f, kC] using (ppC ring hL f kD.val).symm.trans h0


private theorem groupFootForwardC
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n)
    (h : InGroupOwnedFootprintV31 ring C owner p) :
    InGroupOwnedFootprintV31 ring D owner p := by
  rcases h with ⟨k, hk⟩
  exact ⟨k, (gpC ring hL owner k.val).trans hk⟩


def CoverMainClearStepV31 (C D : FC n ψ κ τ) : Prop :=
  ∀ p : Fin n, MainClearV3 (C p) → MainClearV3 (D p)


def CoverNewPendingStepV31
    (ring : DirectedRing n) (C D : FC n ψ κ τ) : Prop :=
  ∀ (owner p : Fin n), PendingOpenROwnerV31 ring D owner →
    ¬ PendingOpenROwnerV31 ring C owner →
    InOpenRFreshFootprintV31 ring D owner p →
      MainClearV3 (D p) ∨
      InGroupOwnedFootprintV31 ring D (ring.rightNeighbor owner) p


theorem pendingCover_step_of_old_new
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (hMC : CoverMainClearStepV31 C D)
    (hNew : CoverNewPendingStepV31 ring C D)
    (hCov : PendingOpenRFootprintCoveredV31 ring C) :
    PendingOpenRFootprintCoveredV31 ring D := by
  intro owner p hpD hfD
  by_cases hpC : PendingOpenROwnerV31 ring C owner
  · have hfC := footprintBackC ring hL owner p hfD
    rcases hCov owner p hpC hfC with hm | hg
    · exact Or.inl (hMC p hm)
    · exact Or.inr (groupFootForwardC ring hL _ _ hg)
  · exact hNew owner p hpD hpC hfD


private theorem prefixSelfC
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    R2Coherence.prefixPos ring (eraseCfgV3 C) i
      (raw (C i)).label.val = i := by
  apply Fin.ext
  simp [R2Coherence.prefixPos, R2Coherence.back,
    Nat.add_mod, Nat.mod_eq_of_lt i.isLt]


theorem pendingOwnerFresh_of_covered
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hFacts : ReachablePhaseFactsV31 ring C)
    (hCov : PendingOpenRFootprintCoveredV31 ring C)
    (owner : Fin n) (hp : PendingOpenROwnerV31 ring C owner) :
    OpenROwnerFreshV3 ring C owner := by
  unfold OpenROwnerFreshV3 GroupIntrinsicFreshV3 IntrinsicFreshAtV3
  intro j ko hOwner q hEq
  let f := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hf : InOpenRFreshFootprintV31 ring C owner f := by
    let k : Fin ((raw (C f)).label.val + 1) :=
      ⟨(raw (C f)).label.val, Nat.lt_succ_self _⟩
    refine ⟨j, ko, q, hOwner, k, ?_⟩
    simpa [f, k] using prefixSelfC ring C f
  have hs := pendingOwner_safe_everywhere_of_covered
    ring C hFacts hCov owner f hp
  unfold SweepOpenRSafeAtV31 at hs
  rcases hs with hm | hout
  · have hn : (raw (C f)).state = .none := by
      unfold MainClearV3 R2CoherenceBranches.MainClear at hm
      change (C f).phys.base.core.core.state = .none
      exact hm.1
    rw [hn] at hEq
    cases hEq
  · exact (hout hf).elim
theorem scrubLIncomingOpenRFresh_of_covered
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (hFacts : ReachablePhaseFactsV31 ring C)
    (hCov : PendingOpenRFootprintCoveredV31 ring C) :
    ScrubLIncomingOpenRFreshV31 ring C := by
  intro owner hs hu hr
  exact pendingOwnerFresh_of_covered ring C hFacts hCov owner ⟨hs, hu, hr⟩

/-- Fixed-ψ=2 release reduction: this is exactly the pair of
primitives, with no release-specific freshness argument left. -/
theorem pendingOwnerCovered_psi2_of_primitives
    (ring : DirectedRing n) (C : FC n 2 κ τ)
    (hAdj : R2CoherenceV31ReachableReleaseOwner2.AdjacentRootPredecessorMainClearPsi2V31 ring C)
    (hDich : Psi2PendingFootprintDichotomyV31 ring C)
    (owner : Fin n) (hp : PendingOpenROwnerV31 ring C owner) :
    ∀ p, InOpenRFreshFootprintV31 ring C owner p →
      MainClearV3 (C p) ∨
      InGroupOwnedFootprintV31 ring C (ring.rightNeighbor owner) p := by
  intro p hf
  exact (pendingFootprintCovered_psi2_of_dichotomy
    ring C hAdj hDich) owner p hp hf


/-- First genuinely new general-ψ creation arm.  Every witness
has labels owner/e/right(e)=0/1/2 and therefore ψ≥3. -/
def ScrubLContinuationNewPendingCoverV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e owner : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL →
    ScrubLContinuationNewPendingV31 hψ h2 ring C e owner →
    ∀ p, InOpenRFreshFootprintV31 ring (stepV3 hψ h2 ring C e) owner p →
      MainClearV3 (stepV3 hψ h2 ring C e p) ∨
      InGroupOwnedFootprintV31 ring (stepV3 hψ h2 ring C e)
        (ring.rightNeighbor owner) p


theorem scrubL_newPending_forces_ge_three
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hNew : ScrubLContinuationNewPendingV31 hψ h2 ring C e owner) :
    3 ≤ ψ :=
  (scrubLContinuationNewPending_labels
    hψ h2 ring C e owner hGeom hPlus hb hNew).2.2.2


/-- Branch interface used by the simultaneous payload+cover induction. -/
def CoverPayloadStepV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (b : BranchV3) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    PendingOpenRFootprintCoveredV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = b →
      ReachablePhaseFactsPlus4StrongR2V31 ring (stepV3 hψ h2 ring C e) ∧
      PendingOpenRFootprintCoveredV31 ring (stepV3 hψ h2 ring C e)


private theorem traceStepC
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (h : ReachableFromQuarantineV31 hψ h2 ring C) :
    ReachableFromQuarantineV31 hψ h2 ring (stepV3 hψ h2 ring C e) := by
  rcases h with ⟨C0, w, hb, hC⟩
  refine ⟨C0, w ++ [e], hb, ?_⟩
  rw [List.foldl_append, ← hC]
  rfl


theorem pendingFootprintCoveredReachable_of_branchSteps
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hs : CoverPayloadStepV31 (κ := κ) (τ := τ) hψ h2 ring .seek)
    (hw : CoverPayloadStepV31 (κ := κ) (τ := τ) hψ h2 ring .sweep)
    (hc : CoverPayloadStepV31 (κ := κ) (τ := τ) hψ h2 ring .commit)
    (hr : CoverPayloadStepV31 (κ := κ) (τ := τ) hψ h2 ring .release)
    (hl : CoverPayloadStepV31 (κ := κ) (τ := τ) hψ h2 ring .scrubL)
    (ho : CoverPayloadStepV31 (κ := κ) (τ := τ) hψ h2 ring .openR)
    (hz : CoverPayloadStepV31 (κ := κ) (τ := τ) hψ h2 ring .sealed)
    (hh : CoverPayloadStepV31 (κ := κ) (τ := τ) hψ h2 ring .openHazard)
    (hn : CoverPayloadStepV31 (κ := κ) (τ := τ) hψ h2 ring .openNoHazard)
    (hm : CoverPayloadStepV31 (κ := κ) (τ := τ) hψ h2 ring .mixed) :
    PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring := by
  intro C hTrace _
  rcases hTrace with ⟨C0, w, hBirth, hC⟩
  have hP0 := R2CoherenceV31ReachableOpenNoHazard4.reachablePhaseFactsPlus4StrongR2_entrance hψ h2 ring C0 hBirth
  have hCov0 : PendingOpenRFootprintCoveredV31 ring C0 := by
    rcases hBirth.1 with ⟨_, Q, _, hEq⟩
    rw [hEq]
    exact pendingOpenRFootprintCovered_quarantineInit ring Q
  have carry : ∀ (v : List (Fin n)) (D : FC n ψ κ τ),
      ReachableFromQuarantineV31 hψ h2 ring D → ElectionGeometryV31 ring D →
      ReachablePhaseFactsPlus4StrongR2V31 ring D →
      PendingOpenRFootprintCoveredV31 ring D →
      ReachablePhaseFactsPlus4StrongR2V31 ring
          (v.foldl (stepV3 hψ h2 ring) D) ∧
      PendingOpenRFootprintCoveredV31 ring
          (v.foldl (stepV3 hψ h2 ring) D) := by
    intro v
    induction v with
    | nil => intro D _ _ hp hv; exact ⟨hp, hv⟩
    | cons e v ih =>
      intro D ht hg hp hv
      simp only [List.foldl_cons]
      have hnxt := by
        cases hb : branchAtV3 hψ h2 (D e) (D (ring.rightNeighbor e)) with
        | seek => exact hs D e hg ht hp hv hb
        | sweep => exact hw D e hg ht hp hv hb
        | commit => exact hc D e hg ht hp hv hb
        | release => exact hr D e hg ht hp hv hb
        | scrubL => exact hl D e hg ht hp hv hb
        | openR => exact ho D e hg ht hp hv hb
        | sealed => exact hz D e hg ht hp hv hb
        | openHazard => exact hh D e hg ht hp hv hb
        | openNoHazard => exact hn D e hg ht hp hv hb
        | mixed => exact hm D e hg ht hp hv hb
      exact ih _ (traceStepC hψ h2 ring D e ht)
        ((electionGeometryStepV31 (κ := κ) (τ := τ) hψ h2 ring) D e hg)
        hnxt.1 hnxt.2
  rw [hC]
  exact (carry w C0 ⟨C0, [], hBirth, rfl⟩ hBirth.2 hP0 hCov0).2

/-- Once the cover theorem above is installed, this closes the shared
openHazard/MIXED fresh-seek S residual without a separate seek invariant. -/
theorem freshSeekWindowClear_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring) :
    ∀ C : FC n ψ κ τ,
      ReachableFromQuarantineV31 hψ h2 ring C →
      ElectionGeometryV31 ring C →
      ReachablePhaseFactsPlus4StrongR2V31 ring C →
      R2CoherenceV31ReachableFreshSeek.FreshSeekWindowClearV31
        hψ h2 ring C := by
  intro C ht hg hp e pred owner hb
  dsimp only
  have htD := traceStepC hψ h2 ring C e ht
  have hgD := (electionGeometryStepV31 (κ := κ) (τ := τ) hψ h2 ring) C e hg
  have hvD := hCov _ htD hgD
  rcases hb with hb | hb
  · have hP3 := R2CoherenceV31ReachableOpenHazard.reachablePhaseFactsPlus3_openHazard_step hψ h2 ring C e hg ht hp hb
    exact (overlapSeek_of_cover ring _ hP3.1.1.1 hvD).2.2 pred owner
  · have hP3 := R2CoherenceV31ReachableMixed.reachablePhaseFactsPlus3_mixed_step hψ h2 ring C e hg ht hp hb
    exact (overlapSeek_of_cover ring _ hP3.1.1.1 hvD).2.2 pred owner


theorem openHazardFreshSeekPrepaid_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring) :
    R2CoherenceV31ReachableOpenHazard.OpenHazardFreshSeekPrepaidV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  exact R2CoherenceV31ReachableFreshSeek.openHazardFreshSeekPrepaid_of_freshSeekWindowClear hψ h2 ring
      (freshSeekWindowClear_of_reachableCover hψ h2 ring hCov)


theorem mixedS_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring) :
    R2CoherenceV31ReachableMixed.MixedSeekIncomingSweepOpenROverlapClearWidePreservationV31
      (κ := κ) (τ := τ) hψ h2 ring := by
  exact R2CoherenceV31ReachableFreshSeek.mixedSeekIncomingSweepOpenROverlapClearWidePreservation_of_fresh
    hψ h2 ring (freshSeekWindowClear_of_reachableCover hψ h2 ring hCov)


private theorem releasePostFactsCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hg : ElectionGeometryV31 ring C)
    (ht : ReachableFromQuarantineV31 hψ h2 ring C)
    (hp : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    ReachablePhaseFactsV31 ring (stepV3 hψ h2 ring C e) ∧
    PendingOpenRFootprintCoveredV31 ring (stepV3 hψ h2 ring C e) := by
  refine ⟨R2CoherenceV31ReachableRelease.reachablePhaseFacts_release_step
      hψ h2 ring C e hp.1.1.1.1 hb, ?_⟩
  exact hCov _ (traceStepC hψ h2 ring C e ht)
    ((electionGeometryStepV31 (κ := κ) (τ := τ) hψ h2 ring) C e hg)


theorem releaseP7_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring) :
    R2CoherenceV31ReachableRelease.ReleaseScrubLIncomingOpenRFreshPreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hg ht hp hb
  have h := releasePostFactsCover hψ h2 ring hCov C e hg ht hp hb
  exact scrubLIncomingOpenRFresh_of_covered ring _ h.1 h.2


theorem releaseP8_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring) :
    R2CoherenceV31ReachableRelease2.ReleaseSweepOpenROverlapClearPreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hg ht hp hb _
  have h := releasePostFactsCover hψ h2 ring hCov C e hg ht hp hb
  exact (overlapSeek_of_cover ring _ h.1 h.2).1


theorem releaseP9_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring) :
    R2CoherenceV31ReachableRelease3.ReleaseSweepOpenROverlapClearWidePreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hg ht hp hb _ _
  have h := releasePostFactsCover hψ h2 ring hCov C e hg ht hp hb
  exact (overlapSeek_of_cover ring _ h.1 h.2).2.1


theorem releaseS_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 ring) :
    R2CoherenceV31ReachableRelease3.ReleaseSeekIncomingSweepOpenROverlapClearWidePreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hg ht hp hb _
  have h := releasePostFactsCover hψ h2 ring hCov C e hg ht hp hb
  exact (overlapSeek_of_cover ring _ h.1 h.2).2.2

end R2CoherenceV31ReachableCover
