import Leader.Wu.Coherence.ReachableFreshReleaseMixedHazard
import Leader.Wu.Coherence.ReachableFreshSeekScrubLOpenR

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableSeekMixedFresh

open PPLL PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus2 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableAdjacentRoot
open R2CoherenceV31MainClearTruth R2CoherenceV31FreshnessClear
open R2CoherenceV31ReachableFreshBranches2
open R2CoherenceV31ReachableFreshBranches3
open R2CoherenceV31ReachableSoundParametric
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31ReachableSoundFresh
open R2CoherenceV31MainClearTruth.WeakFreshnessLayer

variable {n ψ κ τ : Nat}

private def SmallFrameSF (C D : FC n ψ κ τ) : Prop :=
  ∀ p, (D p).phys = (C p).phys ∧
    ((D p).ctl = (C p).ctl ∨
      (D p).ctl.tok = .none ∨ (D p).ctl.tok = .seek ∨
      (D p).ctl.tok = .sweep)

private theorem rawSF {C D : FC n ψ κ τ} (h : SmallFrameSF C D) (p : Fin n) :
    raw (D p) = raw (C p) :=
  congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core) (h p).1

private theorem labSF {C D : FC n ψ κ τ} (h : SmallFrameSF C D) (p : Fin n) :
    (raw (D p)).label = (raw (C p)).label :=
  congrArg (fun x : BoundedAgentState ψ κ => x.label) (rawSF h p)

private theorem gpSF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : SmallFrameSF C D) (i : Fin n) (k : Nat) :
    R2Coherence.groupPos r (eraseCfgV3 D) i k =
      R2Coherence.groupPos r (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd r (R2Coherence.back r i (raw (D i)).label.val) k =
    R2Coherence.fwd r (R2Coherence.back r i (raw (C i)).label.val) k
  rw [labSF h i]

private theorem ppSF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : SmallFrameSF C D) (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos r (eraseCfgV3 D) i k =
      R2Coherence.prefixPos r (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back r i ((raw (D i)).label.val - k) =
    R2Coherence.back r i ((raw (C i)).label.val - k)
  rw [labSF h i]

private theorem footprintBackSF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : SmallFrameSF C D) (o p : Fin n)
    (hf : InOpenRFreshFootprintV31 r D o p) :
    InOpenRFreshFootprintV31 r C o p := by
  rcases hf with ⟨j, ko, q, ho, k, hp⟩
  rw [gpSF r h j ko.val] at ho
  have hq := gpSF r h j q.val
  let f := R2Coherence.groupPos r (eraseCfgV3 C) j q.val
  have hfD : R2Coherence.groupPos r (eraseCfgV3 D) j q.val = f := by
    simpa [f] using hq
  have hv :
      (raw (D (R2Coherence.groupPos r (eraseCfgV3 D) j q.val))).label.val =
        (raw (C f)).label.val := by
    rw [hfD]
    exact congrArg Fin.val (labSF h f)
  have hk : k.val < (raw (C f)).label.val + 1 := by
    simpa only [hv] using k.isLt
  let kc : Fin ((raw (C f)).label.val + 1) := ⟨k.val, hk⟩
  refine ⟨j, ko, q, ho, kc, ?_⟩
  have hp' : R2Coherence.prefixPos r (eraseCfgV3 D) f k.val = p := by
    simpa only [hfD] using hp
  simpa [f, kc] using (ppSF r h f k.val).symm.trans hp'

private theorem ctlOldSF {C D : FC n ψ κ τ} (h : SmallFrameSF C D)
    (p : Fin n) {t : TokenV3} (ht : (D p).ctl.tok = t)
    (h0 : t ≠ .none) (hk : t ≠ .seek) (hw : t ≠ .sweep) :
    (D p).ctl = (C p).ctl := by
  rcases (h p).2 with hc | hnone | hseek | hsweep
  · exact hc
  · exact (h0 (ht.symm.trans hnone)).elim
  · exact (hk (ht.symm.trans hseek)).elim
  · exact (hw (ht.symm.trans hsweep)).elim

private theorem pendingBackSF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : SmallFrameSF C D) (o : Fin n) (hp : PendingOpenROwnerV31 r D o) :
    PendingOpenROwnerV31 r C o := by
  rcases hp with ⟨hs, hu, hr⟩
  have hc := ctlOldSF h (r.rightNeighbor o) hs (by decide) (by decide) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hc]; exact hs
  · unfold successorB at hu ⊢
    simpa only [rawSF h o, rawSF h (r.rightNeighbor o)] using hu
  · unfold atRootB at hr ⊢
    simpa only [rawSF h o] using hr

private theorem freshSF {C D : FC n ψ κ τ} (h : SmallFrameSF C D)
    (p : Fin n) (hf : FreshnessClearV31 (C p)) : FreshnessClearV31 (D p) := by
  unfold FreshnessClearV31 at hf ⊢
  rw [rawSF h p]
  exact hf

private theorem safeCoveredSF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : SmallFrameSF C D) (hf : ReachablePhaseFactsV31 r C)
    (hc : PendingOpenRFootprintCoveredV31 r C) (o p : Fin n)
    (hp : PendingOpenROwnerV31 r D o) : SweepOpenRSafeFreshV31 r D o p := by
  have hpC := pendingBackSF r h o hp
  rcases pendingOwner_safe_everywhere_of_covered r C hf hc o p hpC with hm | hout
  · exact Or.inl (freshSF h p (freshnessClear_of_mainClear _ hm))
  · exact Or.inr (fun hx => hout (footprintBackSF r h o p hx))

private theorem p8CoveredSF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : SmallFrameSF C D) (hf : ReachablePhaseFactsV31 r C)
    (hc : PendingOpenRFootprintCoveredV31 r C) : SweepOpenROverlapFreshV31 r D := by
  intro s o _ hp
  exact ⟨safeCoveredSF r h hf hc o s hp,
    safeCoveredSF r h hf hc o (r.rightNeighbor s) hp⟩

private theorem p9CoveredSF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : SmallFrameSF C D) (hf : ReachablePhaseFactsV31 r C)
    (hc : PendingOpenRFootprintCoveredV31 r C) : SweepOpenROverlapFreshWideV31 r D := by
  intro s o _ hp
  exact ⟨safeCoveredSF r h hf hc o (r.rightNeighbor s) hp,
    fun d => safeCoveredSF r h hf hc o (R2Coherence.fwd r s d.val) hp⟩

private theorem sCoveredSF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : SmallFrameSF C D) (hf : ReachablePhaseFactsV31 r C)
    (hc : PendingOpenRFootprintCoveredV31 r C) :
    SeekIncomingSweepOpenROverlapFreshWideV31 r D := by
  intro pred o _ hp
  constructor
  · intro _
    exact ⟨safeCoveredSF r h hf hc o (r.rightNeighbor (r.rightNeighbor pred)) hp,
      fun d => safeCoveredSF r h hf hc o (R2Coherence.fwd r (r.rightNeighbor pred) d.val) hp⟩
  · intro _ _
    exact ⟨safeCoveredSF r h hf hc o (r.rightNeighbor pred) hp,
      fun d => safeCoveredSF r h hf hc o (R2Coherence.fwd r pred d.val) hp⟩

private theorem r2CoveredSF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : SmallFrameSF C D) (hf : ReachablePhaseFactsV31 r C)
    (hc : PendingOpenRFootprintCoveredV31 r C) :
    SweepPendingOpenRFootprintOwnedV31F r D := by
  intro s o p _ hp _ hfoot
  rcases safeCoveredSF r h hf hc o p hp with hz | hout
  · exact Or.inr hz
  · exact (hout hfoot).elim

private theorem r1FrameSF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : SmallFrameSF C D) (hr : OpenRForwardFreshnessClearV31 r C) :
    OpenRForwardFreshnessClearV31 r D := by
  intro o ho d
  have hctl := ctlOldSF h o ho (by decide) (by decide) (by decide)
  have hoC : (C o).ctl.tok = .openR := by rw [← hctl]; exact ho
  have hv := congrArg Fin.val (labSF h o)
  have hd : d.val < ψ - (raw (C o)).label.val := by simpa only [hv] using d.isLt
  let dc : Fin (ψ - (raw (C o)).label.val) := ⟨d.val, hd⟩
  exact freshSF h _ (by simpa [dc] using hr o hoC dc)

private theorem simpleFrameSF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hr : rowV3 hψ (by decide : 0 < 2) h2 (C e) (C (r.rightNeighbor e)) =
        (C e, C (r.rightNeighbor e)) ∨
      rowV3 hψ (by decide : 0 < 2) h2 (C e) (C (r.rightNeighbor e)) =
        (C e, startClosing (C (r.rightNeighbor e))) ∨
      rowV3 hψ (by decide : 0 < 2) h2 (C e) (C (r.rightNeighbor e)) =
        (startClosing (C e), C (r.rightNeighbor e))) :
    SmallFrameSF C (stepV3 hψ h2 r C e) := by
  intro p
  rcases hr with hr | hr | hr
  all_goals
    by_cases hp : p = e
    · subst p
      simp [stepV3, protocolV3, PopulationProtocol.step, hr, startClosing, setControl]
    · by_cases hq : p = r.rightNeighbor e
      · subst p
        simp [stepV3, protocolV3, PopulationProtocol.step, hr, hp, startClosing, setControl]
      · rw [stepV3_other hψ h2 r C e p hp hq]
        exact ⟨rfl, Or.inl rfl⟩

private theorem seekTokSF (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .seek) : r.ctl.tok = .seek := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowSeekSF (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .seek) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = seekStageV3 l r := by
  simp [rowV3, seekTokSF hψ h2 l r hb]

private theorem frameSeekSF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .seek) :
    SmallFrameSF C (stepV3 hψ h2 r C e) := by
  intro p
  have hr := rowSeekSF hψ h2 (C e) (C (r.rightNeighbor e)) hb
  by_cases hp : p = e
  · subst p
    cases hR : atRootB (C (r.rightNeighbor e)) <;> cases hL : atRootB (C e) <;>
      simp [stepV3, protocolV3, PopulationProtocol.step, hr, seekStageV3, hR, hL, setControl]
  · by_cases hq : p = r.rightNeighbor e
    · subst p
      cases hR : atRootB (C (r.rightNeighbor e)) <;> cases hL : atRootB (C e) <;>
        simp [stepV3, protocolV3, PopulationProtocol.step, hr, hp, seekStageV3, hR, hL, setControl]
    · rw [stepV3_other hψ h2 r C e p hp hq]
      exact ⟨rfl, Or.inl rfl⟩

private theorem rowOHSF (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openHazard) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = (l, startClosing r) ∨
      rowV3 hψ (by decide : 0 < 2) h2 l r = (startClosing l, r) := by
  have hc : l.ctl.tok = .none ∧ r.ctl.tok = .none ∧ l.ctl.mark = .open ∧
      r.ctl.mark = .open ∧
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = true) := by
    unfold branchAtV3 at hb
    repeat' split at hb
    all_goals simp_all
  rcases hc with ⟨hln,hrn,hlo,hro,hh⟩
  let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
  by_cases he : endpointHazardV3 r.phys q.2
  · left; simp [rowV3, ordinaryStageV3, openStageV3, hln,hrn,hlo,hro,hh,q,he]
  · right; simp [rowV3, ordinaryStageV3, openStageV3, hln,hrn,hlo,hro,hh,q,he]

private theorem rowMixSF (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hg : passiveEdgeOKV3 l r = true)
    (hb : branchAtV3 hψ h2 l r = .mixed) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = (l, r) ∨
      rowV3 hψ (by decide : 0 < 2) h2 l r = (l, startClosing r) := by
  have hc : r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧ r.ctl.tok ≠ .commit ∧
      l.ctl.tok ≠ .release ∧ r.ctl.tok ≠ .scrubL ∧ l.ctl.tok ≠ .openR := by
    unfold branchAtV3 at hb
    repeat' split at hb
    all_goals simp_all
  rcases hc with ⟨hs,hw,hc,hr,hsl,ho⟩
  by_cases hn : l.ctl.tok = .none ∧ r.ctl.tok = .none
  · have hseal : ¬(l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) := by
      intro x; have y := hb; simp [branchAtV3,hs,hw,hc,hr,hsl,ho,hn,x] at y
    have hopen : ¬(l.ctl.mark = .open ∧ r.ctl.mark = .open) := by
      intro x; have y := hb; unfold branchAtV3 at y
      simp [hs,hw,hc,hr,hsl,ho,hn,hseal,x] at y
      split at y <;> simp_all
    right
    simpa [rowV3, ordinaryStageV3, hs,hw,hc,hr,hsl,ho,hn,hseal,hopen] using
      (normalizePassiveV3_good_edge l r hg)
  · left
    simp [rowV3, ordinaryStageV3, hs,hw,hc,hr,hsl,ho,hn]

private theorem frameOHSF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .openHazard) :
    SmallFrameSF C (stepV3 hψ h2 r C e) := by
  rcases rowOHSF hψ h2 (C e) (C (r.rightNeighbor e)) hb with h | h
  · exact simpleFrameSF hψ h2 r C e (Or.inr (Or.inl h))
  · exact simpleFrameSF hψ h2 r C e (Or.inr (Or.inr h))

private theorem frameMixSF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hg : ElectionGeometryV31 r C)
    (hb : branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .mixed) :
    SmallFrameSF C (stepV3 hψ h2 r C e) := by
  rcases rowMixSF hψ h2 (C e) (C (r.rightNeighbor e)) (hg e) hb with h | h
  · exact simpleFrameSF hψ h2 r C e (Or.inl h)
  · exact simpleFrameSF hψ h2 r C e (Or.inr (Or.inl h))

private theorem birthReachSF
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) (C : FC n ψ κ τ)
    (ht : ReachableFromV31 (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r C) :
    ReachableFromQuarantineV31 hψ h2 r C :=
  (reachableFromV31_birth_iff hψ h2 r C).1 ht

theorem seekSFresh_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31 (kappa:=κ) (tau:=τ) hψ h2 r) :
    SeekSFreshPreservationV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
  intro C e hg ht hf hb
  have hq := birthReachSF hψ h2 r C ht
  exact sCoveredSF r (frameSeekSF hψ h2 r C e hb) hf.1 (hCov C hq hg)

theorem seekR2Fresh_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31 (kappa:=κ) (tau:=τ) hψ h2 r) :
    SeekStrongR2FreshPreservationV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
  intro C e hg ht hf hb
  have hq := birthReachSF hψ h2 r C ht
  exact r2CoveredSF r (frameSeekSF hψ h2 r C e hb) hf.1 (hCov C hq hg)

theorem seekReplayFresh_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31 (kappa:=κ) (tau:=τ) hψ h2 r) :
    SeekFreshPrivateReplayV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
  intro hS hR2 C e hg ht hf hb
  have hq := birthReachSF hψ h2 r C ht
  have fr := frameSeekSF hψ h2 r C e hb
  have hc := hCov C hq hg
  have sD := hS C e hg ht hf hb
  have r2D := hR2 C e hg ht hf hb
  rcases hf with ⟨f,p7,p8,p9,s,r1,r2⟩
  have fD := R2CoherenceV31ReachableSeek.reachablePhaseFacts_seek_step hψ h2 r C e f hb
  have p7D := R2CoherenceV31ReachableSeek.scrubLIncoming_seek_step hψ h2 r C e p7 hb
  exact ⟨fD,p7D,p8CoveredSF r fr f hc,p9CoveredSF r fr f hc,
    sD,r1FrameSF r fr r1,r2D⟩

theorem mixedSFresh_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31 (kappa:=κ) (tau:=τ) hψ h2 r) :
    MixedSFreshV31 (κ:=κ) (τ:=τ) hψ h2 r := by
  intro C e hg ht hf hb
  exact sCoveredSF r (frameMixSF hψ h2 r C e hg hb) hf.1 (hCov C ht hg)

theorem mixedR1Fresh_frame
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) :
    MixedR1FreshV31 (κ:=κ) (τ:=τ) hψ h2 r := by
  intro C e hg _ hf hb
  exact r1FrameSF r (frameMixSF hψ h2 r C e hg hb) hf.2.2.2.2.2.1

theorem mixedR2Fresh_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31 (kappa:=κ) (tau:=τ) hψ h2 r) :
    MixedR2FreshV31 (κ:=κ) (τ:=τ) hψ h2 r := by
  intro C e hg ht hf hb
  exact r2CoveredSF r (frameMixSF hψ h2 r C e hg hb) hf.1 (hCov C ht hg)

theorem openHazardFreshSeekPrepaidFresh_of_reachableCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hCov : PendingFootprintCoveredReachableV31 (kappa:=κ) (tau:=τ) hψ h2 r) :
    OpenHazardFreshSeekPrepaidFreshV31 (κ:=κ) (τ:=τ) hψ h2 r := by
  intro C e pred owner ht hg hf hb
  dsimp only
  intro hseek _ hp
  have fr := frameOHSF hψ h2 r C e hb
  exact sCoveredSF r fr hf.1 (hCov C ht hg) pred owner hseek hp

def freshResidualLedgerOpenCountAfterSeekMixed : Nat := 10

end R2CoherenceV31ReachableSeekMixedFresh
