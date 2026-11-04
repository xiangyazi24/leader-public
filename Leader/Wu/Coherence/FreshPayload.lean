import Leader.Wu.Coherence.FreshnessClear


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31FreshnessClear


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31OpenNoHazard R2CoherenceV31PhaseMainClear
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachableOpenNoHazard3
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31MainClearTruth
open R2CoherenceV31MainClearTruth.WeakFreshnessLayer


variable {n ψ κ τ : Nat}


def SweepOpenROverlapFreshV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (e owner : Fin n),
    (C e).ctl.tok = .sweep → PendingOpenROwnerV31 ring C owner →
      SweepOpenRSafeFreshV31 ring C owner e ∧
      SweepOpenRSafeFreshV31 ring C owner (ring.rightNeighbor e)


def SweepOpenROverlapFreshWideV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (e owner : Fin n),
    (C e).ctl.tok = .sweep → PendingOpenROwnerV31 ring C owner →
      SweepOpenRSafeFreshV31 ring C owner (ring.rightNeighbor e) ∧
      ∀ d : Fin (ψ - (raw (C e)).label.val),
        SweepOpenRSafeFreshV31 ring C owner
          (R2Coherence.fwd ring e d.val)


def SeekIncomingSweepOpenROverlapFreshWideV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (e owner : Fin n),
    (C (ring.rightNeighbor e)).ctl.tok = .seek →
    PendingOpenROwnerV31 ring C owner →
      (atRootB (C (ring.rightNeighbor e)) = true →
        SweepOpenRSafeFreshV31 ring C owner
            (ring.rightNeighbor (ring.rightNeighbor e)) ∧
        ∀ d : Fin (ψ - (raw (C (ring.rightNeighbor e))).label.val),
          SweepOpenRSafeFreshV31 ring C owner
            (R2Coherence.fwd ring (ring.rightNeighbor e) d.val)) ∧
      (atRootB (C (ring.rightNeighbor e)) = false →
        atRootB (C e) = true →
          SweepOpenRSafeFreshV31 ring C owner (ring.rightNeighbor e) ∧
          ∀ d : Fin (ψ - (raw (C e)).label.val),
            SweepOpenRSafeFreshV31 ring C owner
              (R2Coherence.fwd ring e d.val))


def OpenRForwardFreshnessClearV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ e : Fin n, (C e).ctl.tok = .openR →
    ∀ d : Fin (ψ - (raw (C e)).label.val),
      FreshnessClearV31 (C (R2Coherence.fwd ring e d.val))


def SweepPendingOpenRFootprintOwnedV31F
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (sweep owner p : Fin n),
    (C sweep).ctl.tok = .sweep →
    PendingOpenROwnerV31 ring C owner →
    InSweepWideReadV31 ring C sweep p →
    InOpenRFreshFootprintV31 ring C owner p →
      PhaseOwnedV31 (C p) ∨ FreshnessClearV31 (C p)

def ReachablePhaseFactsFreshV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ReachablePhaseFactsV31 ring C ∧
  ScrubLIncomingOpenRFreshV31 ring C ∧
  SweepOpenROverlapFreshV31 ring C ∧
  SweepOpenROverlapFreshWideV31 ring C ∧
  SeekIncomingSweepOpenROverlapFreshWideV31 ring C ∧
  OpenRForwardFreshnessClearV31 ring C ∧
  SweepPendingOpenRFootprintOwnedV31F ring C


theorem openNoHazard_preserves_freshnessClear
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard)
    (hp : FreshnessClearV31 (C p)) :
    FreshnessClearV31 (stepV3 hψ h2 ring C e p) := by
  have hF := openNoHazard_step_frame hψ h2 ring C e hb
  unfold FreshnessClearV31 at hp ⊢
  exact (hF p).2.2.1.trans hp



private theorem gpFresh
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [h i]


private theorem ppFresh
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [h i]


private theorem footprintBackFresh
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n) (hF : InOpenRFreshFootprintV31 ring D owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  rcases hF with ⟨j, ko, q, hOwner, kD, hPrefix⟩
  rw [gpFresh ring hLab j ko.val] at hOwner
  have hq := gpFresh ring hLab j q.val
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hFront : R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = front := by
    simpa [front] using hq
  have hv :
      (raw (D (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val))).label.val =
        (raw (C front)).label.val := by
    rw [hFront]
    exact congrArg Fin.val (hLab front)
  have hk : kD.val < (raw (C front)).label.val + 1 := by
    simpa only [hv] using kD.isLt
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hk⟩
  refine ⟨j, ko, q, hOwner, kC, ?_⟩
  have h0 : R2Coherence.prefixPos ring (eraseCfgV3 D) front kD.val = p := by
    simpa only [hFront] using hPrefix
  have hc := (ppFresh ring hLab front kD.val).symm.trans h0
  simpa [front, kC] using hc


private theorem pendingBackFresh
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (owner : Fin n)
    (h : PendingOpenROwnerV31 ring D owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases h with ⟨hs, hsucc, hr⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [(hF (ring.rightNeighbor owner)).2.2.2] at hs
    exact hs
  · have hl := congrArg Fin.val (hF owner).1
    have hh := congrArg Fin.val (hF (ring.rightNeighbor owner)).1
    unfold successorB at hsucc ⊢
    simpa only [hl, hh] using hsucc
  · have hl := congrArg Fin.val (hF owner).1
    unfold atRootB at hr ⊢
    simpa only [hl] using hr


private theorem safeFresh_of_frame
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (owner p : Fin n)
    (h : SweepOpenRSafeFreshV31 ring C owner p) :
    SweepOpenRSafeFreshV31 ring D owner p := by
  rcases h with hc | hout
  · left
    unfold FreshnessClearV31 at hc ⊢
    exact (hF p).2.2.1.trans hc
  · right
    intro hf
    exact hout (footprintBackFresh ring (fun x => (hF x).1) owner p hf)


private theorem tailFresh_of_frame
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hF : OpenNoHazardFrameV31 C D) (owner base : Fin n)
    (h : ∀ d : Fin (ψ - (raw (C base)).label.val),
      SweepOpenRSafeFreshV31 ring C owner
        (R2Coherence.fwd ring base d.val)) :
    ∀ d : Fin (ψ - (raw (D base)).label.val),
      SweepOpenRSafeFreshV31 ring D owner
        (R2Coherence.fwd ring base d.val) := by
  intro dD
  have hv := congrArg Fin.val (hF base).1
  have hd : dD.val < ψ - (raw (C base)).label.val := by
    simpa only [hv] using dD.isLt
  let dC : Fin (ψ - (raw (C base)).label.val) := ⟨dD.val, hd⟩
  exact safeFresh_of_frame ring hF owner _ (by simpa [dC] using h dC)



theorem seekIncomingSweepOpenROverlapFreshWide_openNoHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hS : SeekIncomingSweepOpenROverlapFreshWideV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    SeekIncomingSweepOpenROverlapFreshWideV31 ring
      (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  intro pred owner hSeekD hPendingD
  have hSeekC := hSeekD
  rw [(hF (ring.rightNeighbor pred)).2.2.2] at hSeekC
  have hPendingC := pendingBackFresh ring hF owner hPendingD
  have hOld := hS pred owner hSeekC hPendingC
  constructor
  · intro hrD
    have hrC : atRootB (C (ring.rightNeighbor pred)) = true := by
      unfold atRootB at hrD ⊢
      have hv := congrArg Fin.val (hF (ring.rightNeighbor pred)).1
      rw [← hv]
      exact hrD
    rcases hOld.1 hrC with ⟨ha, ht⟩
    exact ⟨safeFresh_of_frame ring hF owner _ ha,
      tailFresh_of_frame ring hF owner (ring.rightNeighbor pred) ht⟩
  · intro hnD hrD
    have hnC : atRootB (C (ring.rightNeighbor pred)) = false := by
      unfold atRootB at hnD ⊢
      have hv := congrArg Fin.val (hF (ring.rightNeighbor pred)).1
      rw [← hv]
      exact hnD
    have hrC : atRootB (C pred) = true := by
      unfold atRootB at hrD ⊢
      have hv := congrArg Fin.val (hF pred).1
      rw [← hv]
      exact hrD
    rcases hOld.2 hnC hrC with ⟨ha, ht⟩
    exact ⟨safeFresh_of_frame ring hF owner _ ha,
      tailFresh_of_frame ring hF owner pred ht⟩


theorem openRForwardFreshnessClear_openNoHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hR1 : OpenRForwardFreshnessClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
    OpenRForwardFreshnessClearV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hF : OpenNoHazardFrameV31 C D := by
    simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
  intro owner hOpenD dD
  have hOpenC := hOpenD
  rw [(hF owner).2.2.2] at hOpenC
  have hv := congrArg Fin.val (hF owner).1
  have hd : dD.val < ψ - (raw (C owner)).label.val := by
    rw [← hv]
    exact dD.isLt
  let dC : Fin (ψ - (raw (C owner)).label.val) := ⟨dD.val, hd⟩
  have hOld := hR1 owner hOpenC dC
  unfold FreshnessClearV31 at hOld ⊢
  exact (hF (R2Coherence.fwd ring owner dD.val)).2.2.1.trans
    (by simpa [dC] using hOld)


theorem sweepOpenROverlapFresh_of_old
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : SweepOpenROverlapClearV31 ring C) :
    SweepOpenROverlapFreshV31 ring C := by
  intro e owner hs hp
  rcases h e owner hs hp with ⟨he, hr⟩
  exact ⟨sweepOpenRSafeFresh_of_old ring C owner e he,
    sweepOpenRSafeFresh_of_old ring C owner (ring.rightNeighbor e) hr⟩


theorem sweepOpenROverlapFreshWide_of_old
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : SweepOpenROverlapClearWideV31 ring C) :
    SweepOpenROverlapFreshWideV31 ring C := by
  intro e owner hs hp
  rcases h e owner hs hp with ⟨hr, ht⟩
  exact ⟨sweepOpenRSafeFresh_of_old ring C owner (ring.rightNeighbor e) hr,
    fun d => sweepOpenRSafeFresh_of_old ring C owner _ (ht d)⟩


theorem seekIncomingFreshWide_of_old
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : SeekIncomingSweepOpenROverlapClearWideV31 ring C) :
    SeekIncomingSweepOpenROverlapFreshWideV31 ring C := by
  intro e owner hs hp
  have ho := h e owner hs hp
  constructor
  · intro hr
    rcases ho.1 hr with ⟨ha, ht⟩
    exact ⟨sweepOpenRSafeFresh_of_old ring C owner _ ha,
      fun d => sweepOpenRSafeFresh_of_old ring C owner _ (ht d)⟩
  · intro hn hr
    rcases ho.2 hn hr with ⟨ha, ht⟩
    exact ⟨sweepOpenRSafeFresh_of_old ring C owner _ ha,
      fun d => sweepOpenRSafeFresh_of_old ring C owner _ (ht d)⟩


theorem openRForwardFreshnessClear_of_old
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : OpenRForwardMainClearV31 ring C) :
    OpenRForwardFreshnessClearV31 ring C := by
  intro e ho d
  exact freshnessClear_of_mainClear _ (h e ho d)


theorem reachablePhaseFactsFresh_of_oldStrong
    (ring : DirectedRing n) (C : FC n ψ κ τ)
    (h : ReachablePhaseFactsPlus4StrongR2V31 ring C) :
    ReachablePhaseFactsFreshV31 ring C := by
  rcases h with ⟨hP3, hS, hR1, hR2⟩
  rcases hP3 with ⟨hP2, hP9⟩
  rcases hP2 with ⟨hP, hP8⟩
  rcases hP with ⟨hFacts, hP7⟩
  exact ⟨hFacts, hP7,
    sweepOpenROverlapFresh_of_old ring C hP8,
    sweepOpenROverlapFreshWide_of_old ring C hP9,
    seekIncomingFreshWide_of_old ring C hS,
    openRForwardFreshnessClear_of_old ring C hR1,
    fun sweep owner p hs hp hr hf => Or.inl (hR2.2 sweep owner p hs hp hr hf)⟩


/-- Needed only if some future theorem insists on full MainClear across OPEN. -/
def OpenNoHazardGenerationColdStateV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) : Prop :=
  ∀ (l r : Cell ψ κ τ),
    branchAtV3 hψ h2 l r = .openNoHazard →
    let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
    (MainClearV3 l → q.1.base.core.core.state = .none) ∧
    (MainClearV3 r → q.2.base.core.core.state = .none)


theorem sweepPendingOpenRFootprintOwnedV31F_openNoHazard_step
   (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
   (C : FC n ψ κ τ) (e : Fin n)
   (hR2 : SweepPendingOpenRFootprintOwnedV31F ring C)
   (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openNoHazard) :
   SweepPendingOpenRFootprintOwnedV31F ring
     (stepV3 hψ h2 ring C e) := by
 let D := stepV3 hψ h2 ring C e
 have hF : OpenNoHazardFrameV31 C D := by
   simpa [D] using openNoHazard_step_frame hψ h2 ring C e hb
 intro s o p hsD hpD hrD hfD
 have hsC := hsD
 rw [(hF s).2.2.2] at hsC
 have hpC := pendingBackFresh ring hF o hpD
 have hrC : InSweepWideReadV31 ring C s p := by
   rcases hrD with h | ⟨d,hd⟩
   · exact Or.inl h
   · right
     have hv := congrArg Fin.val (hF s).1
     have hlt : d.val < ψ - (raw (C s)).label.val := by
       rw [← hv]
       exact d.isLt
     let dc : Fin (ψ - (raw (C s)).label.val) := ⟨d.val, hlt⟩
     exact ⟨dc, by simpa [dc] using hd⟩
 have hfC := footprintBackFresh ring (fun x => (hF x).1) o p hfD
 rcases hR2 s o p hsC hpC hrC hfC with ho | hc
 · left
   unfold PhaseOwnedV31 at ho ⊢
   rw [(hF p).2.2.2]
   exact ho
 · right
   unfold FreshnessClearV31 at hc ⊢
   exact (hF p).2.2.1.trans hc

end R2CoherenceV31FreshnessClear
