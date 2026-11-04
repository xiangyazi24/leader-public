import Leader.Wu.Coherence.FootprintCoverFresh
import Leader.Wu.Coherence.ReachableSweepFresh
import Leader.Wu.Coherence.ReachableSeekMixedFresh
import Leader.Wu.Coherence.ReachableScrubLFresh
import Leader.Wu.Coherence.FreshResidualLedger
import Leader.Wu.Coherence.ReplayCoresBirth

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31FootprintCover5
open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus2 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableFreshBranches1 R2CoherenceV31ReachableFreshBranches2
open R2CoherenceV31ReachableFreshBranches3 R2CoherenceV31MainClearTruth
open R2CoherenceV31MainClearTruth.WeakFreshnessLayer R2CoherenceV31FreshnessClear
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31ReachableSoundFresh
open R2CoherenceV31ReachableSoundParametric
variable {n ψ κ τ : Nat}

def FreshPhysFrameV31 (C D : FC n ψ κ τ) : Prop := ∀ p, (D p).phys = (C p).phys

def FreshSmallFrameV31 (C D : FC n ψ κ τ) : Prop := ∀ p,
  (D p).phys = (C p).phys ∧ ((D p).ctl = (C p).ctl ∨
    (D p).ctl.tok = .none ∨ (D p).ctl.tok = .seek ∨ (D p).ctl.tok = .sweep)

theorem physFrame_of_small {C D : FC n ψ κ τ} (h : FreshSmallFrameV31 C D) :
    FreshPhysFrameV31 C D := fun p => (h p).1

theorem raw_eq_of_physFrame {C D : FC n ψ κ τ} (h : FreshPhysFrameV31 C D) (p : Fin n) :
    raw (D p) = raw (C p) :=
  congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core) (h p)

theorem groupPos_eq_of_physFrame (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FreshPhysFrameV31 C D) (i : Fin n) (k : Nat) :
    R2Coherence.groupPos r (eraseCfgV3 D) i k =
      R2Coherence.groupPos r (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change
    R2Coherence.fwd r
        (R2Coherence.back r i (raw (D i)).label.val) k =
      R2Coherence.fwd r
        (R2Coherence.back r i (raw (C i)).label.val) k
  rw [congrArg
    (fun x : BoundedAgentState ψ κ => x.label.val)
    (raw_eq_of_physFrame h i)]

theorem prefixPos_eq_of_physFrame (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FreshPhysFrameV31 C D) (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos r (eraseCfgV3 D) i k =
      R2Coherence.prefixPos r (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change
    R2Coherence.back r i ((raw (D i)).label.val - k) =
      R2Coherence.back r i ((raw (C i)).label.val - k)
  rw [congrArg
    (fun x : BoundedAgentState ψ κ => x.label.val)
    (raw_eq_of_physFrame h i)]

theorem footprintBack_of_physFrame (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FreshPhysFrameV31 C D) {o p : Fin n}
    (hf : InOpenRFreshFootprintV31 r D o p) :
    InOpenRFreshFootprintV31 r C o p := by
  rcases hf with ⟨j, ko, q, ho, kD, hp⟩
  rw [groupPos_eq_of_physFrame r h j ko.val] at ho
  let f := R2Coherence.groupPos r (eraseCfgV3 C) j q.val
  have hq :
      R2Coherence.groupPos r (eraseCfgV3 D) j q.val = f := by
    simpa [f] using groupPos_eq_of_physFrame r h j q.val
  have hv :
      (raw (D (R2Coherence.groupPos r (eraseCfgV3 D) j q.val))).label.val =
        (raw (C f)).label.val := by
    rw [hq]
    exact congrArg
      (fun x : BoundedAgentState ψ κ => x.label.val)
      (raw_eq_of_physFrame h f)
  let kC : Fin ((raw (C f)).label.val + 1) :=
    ⟨kD.val, by simpa only [hv] using kD.isLt⟩
  refine ⟨j, ko, q, ho, kC, ?_⟩
  have hp' :
      R2Coherence.prefixPos r (eraseCfgV3 D) f kD.val = p := by
    simpa only [hq] using hp
  simpa [f, kC] using
    (prefixPos_eq_of_physFrame r h f kD.val).symm.trans hp'

theorem freshnessClear_of_physFrame {C D : FC n ψ κ τ} (h : FreshPhysFrameV31 C D)
    (p : Fin n) (hc : FreshnessClearV31 (C p)) : FreshnessClearV31 (D p) := by
  unfold FreshnessClearV31 at hc ⊢; rw [raw_eq_of_physFrame h p]; exact hc

theorem openROwnerFresh_of_physFrame (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FreshPhysFrameV31 C D) (o : Fin n)
    (hf : OpenROwnerFreshV3 r C o) : OpenROwnerFreshV3 r D o := by
  unfold OpenROwnerFreshV3 at hf ⊢
  intro j ko hit
  rw [groupPos_eq_of_physFrame r h j ko.val] at hit
  have hg := hf j ko hit
  unfold GroupIntrinsicFreshV3 at hg ⊢
  intro q
  let f := R2Coherence.groupPos r (eraseCfgV3 C) j q.val
  have hq :
      R2Coherence.groupPos r (eraseCfgV3 D) j q.val = f := by
    simpa [f] using groupPos_eq_of_physFrame r h j q.val
  rw [hq]
  have ho : IntrinsicFreshAtV3 r C f := by
    simpa [f] using hg q
  unfold IntrinsicFreshAtV3 at ho ⊢
  intro heq
  have heqC : (raw (C f)).state = .equal := by
    rw [← raw_eq_of_physFrame h f]
    exact heq
  intro kd
  have hv := congrArg
    (fun x : BoundedAgentState ψ κ => x.label.val)
    (raw_eq_of_physFrame h f)
  have hk : kd.val < (raw (C f)).label.val + 1 := by
    simpa only [← hv] using kd.isLt
  let kc : Fin ((raw (C f)).label.val + 1) := ⟨kd.val, hk⟩
  have hz := ho heqC kc
  rw [prefixPos_eq_of_physFrame r h f kd.val]
  let p := R2Coherence.prefixPos r (eraseCfgV3 C) f kd.val
  change R2Coherence.freshComponent (eraseCellV3 (D p)) kd.val
  have hz' : R2Coherence.freshComponent (eraseCellV3 (C p)) kd.val := by
    simpa [p, kc] using hz
  unfold R2Coherence.freshComponent at hz' ⊢
  change
    (raw (D p)).label.val = kd.val ∧
      (match (raw (D p)).path with
       | .bot => False
       | .some a b =>
           a.val = kd.val ∧ b.val = (if (raw (D p)).bit then 1 else 0))
  change
    (raw (C p)).label.val = kd.val ∧
      (match (raw (C p)).path with
       | .bot => False
       | .some a b =>
           a.val = kd.val ∧ b.val = (if (raw (C p)).bit then 1 else 0)) at hz'
  rw [raw_eq_of_physFrame h p]
  exact hz'




theorem ctlOld_of_small {C D : FC n ψ κ τ} (h : FreshSmallFrameV31 C D)
    (p : Fin n) {t : TokenV3} (ht : (D p).ctl.tok = t)
    (h0 : t ≠ .none) (hs : t ≠ .seek) (hw : t ≠ .sweep) : (D p).ctl = (C p).ctl := by
  rcases (h p).2 with hc | hc | hc | hc
  · exact hc
  · exact (h0 (ht.symm.trans hc)).elim
  · exact (hs (ht.symm.trans hc)).elim
  · exact (hw (ht.symm.trans hc)).elim

theorem pendingBack_of_small (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FreshSmallFrameV31 C D) (o : Fin n) (hp : PendingOpenROwnerV31 r D o) :
    PendingOpenROwnerV31 r C o := by
  rcases hp with ⟨ht,hu,hr⟩
  have hc := ctlOld_of_small h (r.rightNeighbor o) ht (by decide) (by decide) (by decide)
  refine ⟨by rw [← hc]; exact ht, ?_, ?_⟩
  · unfold successorB at hu ⊢; simpa only [raw_eq_of_physFrame (physFrame_of_small h) o,
      raw_eq_of_physFrame (physFrame_of_small h) (r.rightNeighbor o)] using hu
  · unfold atRootB at hr ⊢; simpa only [raw_eq_of_physFrame (physFrame_of_small h) o] using hr

theorem safeFresh_of_small (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FreshSmallFrameV31 C D) (hf : ReachablePhaseFactsV31 r C)
    (hc : PendingOpenRFootprintCoveredFreshV31 r C) (o p : Fin n)
    (hp : PendingOpenROwnerV31 r D o) : SweepOpenRSafeFreshV31 r D o p := by
  have hpC := pendingBack_of_small r h o hp
  have hs := R2CoherenceV31OpenNoHazardServedCover.pendingSafeFresh_of_coveredFresh
    r C (R2CoherenceV31ReachableSweep.phaseMainClear_of_reachablePhaseFacts r C hf) hc o p hpC
  rcases hs with hz | hout
  · exact Or.inl (freshnessClear_of_physFrame (physFrame_of_small h) p hz)
  · exact Or.inr (fun hx => hout (footprintBack_of_physFrame r (physFrame_of_small h) hx))

theorem overlap_of_safe (r : DirectedRing n) {D : FC n ψ κ τ}
    (hs : ∀ o p, PendingOpenROwnerV31 r D o → SweepOpenRSafeFreshV31 r D o p) :
    SweepOpenROverlapFreshV31 r D := by
  intro s o _ hp; exact ⟨hs o s hp, hs o (r.rightNeighbor s) hp⟩

theorem wide_of_safe (r : DirectedRing n) {D : FC n ψ κ τ}
    (hs : ∀ o p, PendingOpenROwnerV31 r D o → SweepOpenRSafeFreshV31 r D o p) :
    SweepOpenROverlapFreshWideV31 r D := by
  intro s o _ hp; exact ⟨hs o (r.rightNeighbor s) hp, fun d => hs o (R2Coherence.fwd r s d.val) hp⟩

theorem seekIncoming_of_safe (r : DirectedRing n) {D : FC n ψ κ τ}
    (hs : ∀ o p, PendingOpenROwnerV31 r D o → SweepOpenRSafeFreshV31 r D o p) :
    SeekIncomingSweepOpenROverlapFreshWideV31 r D := by
  intro p o _ hp; constructor
  · intro _; exact ⟨hs o (r.rightNeighbor (r.rightNeighbor p)) hp,
      fun d => hs o (R2Coherence.fwd r (r.rightNeighbor p) d.val) hp⟩
  · intro _ _; exact ⟨hs o (r.rightNeighbor p) hp, fun d => hs o (R2Coherence.fwd r p d.val) hp⟩

theorem strongR2_of_safe (r : DirectedRing n) {D : FC n ψ κ τ}
    (hs : ∀ o p, PendingOpenROwnerV31 r D o → SweepOpenRSafeFreshV31 r D o p) :
    SweepPendingOpenRFootprintOwnedV31F r D := by
  intro _ o p _ hp _ hfoot
  rcases hs o p hp with hz | hout
  · exact Or.inr hz
  · exact (hout hfoot).elim

private theorem traceStep5 (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (h : ReachableFromQuarantineV31 hψ h2 r C) :
    ReachableFromQuarantineV31 hψ h2 r (stepV3 hψ h2 r C e) := by
  rcases h with ⟨C0,w,hb,hC⟩; refine ⟨C0,w++[e],hb,?_⟩
  rw [List.foldl_append,←hC]; rfl

private theorem postCover5 (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (hc : R2CoherenceV31FootprintCover4.PendingFootprintCoveredReachableFreshV31
      (κ:=κ) (τ:=τ) hψ h2 r) (C : FC n ψ κ τ) (e : Fin n)
    (ht : ReachableFromQuarantineV31 hψ h2 r C) (hg : ElectionGeometryV31 r C) :
    PendingOpenRFootprintCoveredFreshV31 r (stepV3 hψ h2 r C e) :=
  hc _ (traceStep5 hψ h2 r C e ht)
    ((electionGeometryStepV31 (κ:=κ) (τ:=τ) hψ h2 r) C e hg)

private theorem birthTrace5 (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n) (C : FC n ψ κ τ)
    (h : ReachableFromV31 (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r C) :
    ReachableFromQuarantineV31 hψ h2 r C := (reachableFromV31_birth_iff hψ h2 r C).1 h

private theorem releasePhys5 (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .release) :
    FreshPhysFrameV31 C (stepV3 hψ h2 r C e) := by
  have hc :
      (C (r.rightNeighbor e)).ctl.tok ≠ .seek ∧
      (C e).ctl.tok ≠ .sweep ∧
      (C (r.rightNeighbor e)).ctl.tok ≠ .commit ∧
      (C e).ctl.tok = .release := by
    unfold branchAtV3 at hb
    repeat' split at hb
    all_goals simp_all
    all_goals grind
  rcases hc with ⟨hs, hw, hc, hr⟩
  have hrow :
      rowV3 hψ (by decide : 0<2) h2 (C e) (C (r.rightNeighbor e)) =
        releaseStageV3 (C e) (C (r.rightNeighbor e)) := by
    simp [rowV3, hs, hw, hc, hr]
  intro p
  by_cases pe : p = e <;> by_cases pr : p = r.rightNeighbor e
  all_goals
    simp_all [stepV3, protocolV3, PopulationProtocol.step, hrow,
      releaseStageV3, startClosing, setControl]
    repeat' split <;> simp_all

theorem releaseP7Fresh_of_freshCover_gt_two
    (hψ : 0<ψ) (h2 : 2≤ψ) (h3 : 2<ψ)
    (r : DirectedRing n)
    (_hc : R2CoherenceV31FootprintCover4.PendingFootprintCoveredReachableFreshV31
      (κ:=κ) (τ:=τ) hψ h2 r) :
    ReleaseP7FreshV31 (κ:=κ) (τ:=τ) hψ h2 r := by
  intro C e _ _ hf hb
  let D := stepV3 hψ h2 r C e
  intro o hs hu hr
  have hpD : PendingOpenROwnerV31 r D o := ⟨hs, hu, hr⟩
  have hpC : PendingOpenROwnerV31 r C o := by
    refine Classical.byContradiction (fun hn => ?_)
    have he :=
      R2CoherenceV31ReleaseCoverGeneral.releaseNewPending_forces_psi_two
        hψ h2 r C e o hb hpD hn
    have hfalse : False := by
      rw [he] at h3
      exact Nat.lt_irrefl 2 h3
    exact hfalse.elim
  exact openROwnerFresh_of_physFrame r (releasePhys5 hψ h2 r C e hb) o
    (hf.2.1 o hpC.1 hpC.2.1 hpC.2.2)


private theorem freshSafe_release5 (hψ : 0<ψ) (h2 : 2≤ψ) (r : DirectedRing n)
    (hc : R2CoherenceV31FootprintCover4.PendingFootprintCoveredReachableFreshV31
      (κ:=κ) (τ:=τ) hψ h2 r) (C : FC n ψ κ τ) (e : Fin n)
    (hg : ElectionGeometryV31 r C) (ht : ReachableFromQuarantineV31 hψ h2 r C)
    (hf : ReachablePhaseFactsFreshV31 r C)
    (hb : branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .release) :
    ∀ o p, PendingOpenROwnerV31 r (stepV3 hψ h2 r C e) o →
      SweepOpenRSafeFreshV31 r (stepV3 hψ h2 r C e) o p := by
  have fd := R2CoherenceV31ReachableRelease.reachablePhaseFacts_release_step hψ h2 r C e hf.1 hb
  exact fun o p hp => R2CoherenceV31OpenNoHazardServedCover.pendingSafeFresh_of_coveredFresh
    r _ (R2CoherenceV31ReachableSweep.phaseMainClear_of_reachablePhaseFacts r _ fd)
    (postCover5 hψ h2 r hc C e ht hg) o p hp

theorem releaseP8Fresh_of_freshCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hc : R2CoherenceV31FootprintCover4.PendingFootprintCoveredReachableFreshV31
      (κ := κ) (τ := τ) hψ h2 r) :
    ReleaseP8FreshV31 (κ := κ) (τ := τ) hψ h2 r := by
  intro C e hg ht hf hb
  exact overlap_of_safe r
    (freshSafe_release5 hψ h2 r hc C e hg ht hf hb)
theorem releaseP9Fresh_of_freshCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hc : R2CoherenceV31FootprintCover4.PendingFootprintCoveredReachableFreshV31
      (κ := κ) (τ := τ) hψ h2 r) :
    ReleaseP9FreshV31 (κ := κ) (τ := τ) hψ h2 r := by
  intro C e hg ht hf hb
  exact wide_of_safe r
    (freshSafe_release5 hψ h2 r hc C e hg ht hf hb)
theorem releaseSFresh_of_freshCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hc : R2CoherenceV31FootprintCover4.PendingFootprintCoveredReachableFreshV31
      (κ := κ) (τ := τ) hψ h2 r) :
    ReleaseSFreshV31 (κ := κ) (τ := τ) hψ h2 r := by
  intro C e hg ht hf hb
  exact seekIncoming_of_safe r
    (freshSafe_release5 hψ h2 r hc C e hg ht hf hb)
theorem releaseR2Fresh_of_freshCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hc : R2CoherenceV31FootprintCover4.PendingFootprintCoveredReachableFreshV31
      (κ := κ) (τ := τ) hψ h2 r) :
    ReleaseR2FreshV31 (κ := κ) (τ := τ) hψ h2 r := by
  intro C e hg ht hf hb
  exact strongR2_of_safe r
    (freshSafe_release5 hψ h2 r hc C e hg ht hf hb)

/-- Public retarget of the installed SWEEP-tail consumer. -/
theorem sweepStrongTailFresh_of_freshCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hc : R2CoherenceV31FootprintCover4.PendingFootprintCoveredReachableFreshV31
      (κ := κ) (τ := τ) hψ h2 r) :
    R2CoherenceV31ReachableFreshBranches1.SweepStrongTailPreservationFreshV31
      (κ:=κ) (τ:=τ) hψ h2 r :=
  R2CoherenceV31FootprintCover4.sweepStrongTailPreservationFresh_of_freshCover hψ h2 r hc

def SeekMixedHazardFreshCoverConsumersV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  SeekSFreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r ∧
  SeekStrongR2FreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r ∧
  SeekFreshPrivateReplayV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r ∧
  MixedSFreshV31 (κ := κ) (τ := τ) hψ h2 r ∧
  MixedR2FreshV31 (κ := κ) (τ := τ) hψ h2 r ∧
  OpenHazardFreshSeekPrepaidFreshV31 (κ := κ) (τ := τ) hψ h2 r

def ScrubLOpenRFreshCoverConsumersV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ScrubLP8FreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r ∧
  ScrubLP9FreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r ∧
  ScrubLSFreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r ∧
  ScrubLStrongR2FreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r ∧
  OpenRSFreshSourceV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r

private theorem simpleFrame5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hr : rowV3 hψ (by decide : 0 < 2) h2 (C e) (C (r.rightNeighbor e)) =
        (C e, C (r.rightNeighbor e)) ∨
      rowV3 hψ (by decide : 0 < 2) h2 (C e) (C (r.rightNeighbor e)) =
        (C e, startClosing (C (r.rightNeighbor e))) ∨
      rowV3 hψ (by decide : 0 < 2) h2 (C e) (C (r.rightNeighbor e)) =
        (startClosing (C e), C (r.rightNeighbor e))) :
    FreshSmallFrameV31 C (stepV3 hψ h2 r C e) := by
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

private theorem rowOH5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
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
  rcases hc with ⟨hln, hrn, hlo, hro, hh⟩
  let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
  by_cases he : endpointHazardV3 r.phys q.2
  · left; simp [rowV3, ordinaryStageV3, openStageV3, hln, hrn, hlo, hro, hh, q, he]
  · right; simp [rowV3, ordinaryStageV3, openStageV3, hln, hrn, hlo, hro, hh, q, he]

private theorem rowMix5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hg : passiveEdgeOKV3 l r = true)
    (hb : branchAtV3 hψ h2 l r = .mixed) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = (l, r) ∨
      rowV3 hψ (by decide : 0 < 2) h2 l r = (l, startClosing r) := by
  have hc : r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧ r.ctl.tok ≠ .commit ∧
      l.ctl.tok ≠ .release ∧ r.ctl.tok ≠ .scrubL ∧ l.ctl.tok ≠ .openR := by
    unfold branchAtV3 at hb
    repeat' split at hb
    all_goals simp_all
  rcases hc with ⟨hs, hw, hc, hr, hsl, ho⟩
  by_cases hn : l.ctl.tok = .none ∧ r.ctl.tok = .none
  · have hseal : ¬ (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) := by
      intro x
      have y := hb
      simp [branchAtV3, hs, hw, hc, hr, hsl, ho, hn, x] at y
    have hopen : ¬ (l.ctl.mark = .open ∧ r.ctl.mark = .open) := by
      intro x
      have y := hb
      unfold branchAtV3 at y
      simp [hs, hw, hc, hr, hsl, ho, hn, hseal, x] at y
      split at y <;> simp_all
    right
    simpa [rowV3, ordinaryStageV3, hs, hw, hc, hr, hsl, ho, hn, hseal, hopen] using
      (normalizePassiveV3_good_edge l r hg)
  · left
    simp [rowV3, ordinaryStageV3, hs, hw, hc, hr, hsl, ho, hn]

private theorem frameOH5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .openHazard) :
    FreshSmallFrameV31 C (stepV3 hψ h2 r C e) := by
  rcases rowOH5 hψ h2 (C e) (C (r.rightNeighbor e)) hb with h | h
  · exact simpleFrame5 hψ h2 r C e (Or.inr (Or.inl h))
  · exact simpleFrame5 hψ h2 r C e (Or.inr (Or.inr h))

private theorem frameMix5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (hg : ElectionGeometryV31 r C)
    (hb : branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .mixed) :
    FreshSmallFrameV31 C (stepV3 hψ h2 r C e) := by
  rcases rowMix5 hψ h2 (C e) (C (r.rightNeighbor e)) (hg e) hb with h | h
  · exact simpleFrame5 hψ h2 r C e (Or.inl h)
  · exact simpleFrame5 hψ h2 r C e (Or.inr (Or.inl h))

private theorem seekTok5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .seek) : r.ctl.tok = .seek := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem openRCond5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openR) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧ r.ctl.tok ≠ .commit ∧
      l.ctl.tok ≠ .release ∧ r.ctl.tok ≠ .scrubL ∧ l.ctl.tok = .openR := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem frameSeek5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .seek) :
    FreshSmallFrameV31 C (stepV3 hψ h2 r C e) := by
  intro p
  have hr : rowV3 hψ (by decide : 0 < 2) h2 (C e) (C (r.rightNeighbor e)) =
      seekStageV3 (C e) (C (r.rightNeighbor e)) := by
    simp [rowV3, seekTok5 hψ h2 _ _ hb]
  by_cases hp : p = e
  · subst p
    cases hR : atRootB (C (r.rightNeighbor e)) <;> cases hL : atRootB (C e) <;>
      simp [stepV3, protocolV3, PopulationProtocol.step, hr, seekStageV3, hR, hL, setControl]
  · by_cases hq : p = r.rightNeighbor e
    · subst p
      cases hR : atRootB (C (r.rightNeighbor e)) <;> cases hL : atRootB (C e) <;>
        simp [stepV3, protocolV3, PopulationProtocol.step, hr, hp,
          seekStageV3, hR, hL, setControl]
    · rw [stepV3_other hψ h2 r C e p hp hq]
      exact ⟨rfl, Or.inl rfl⟩

private theorem frameOpenRBad5
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .openR)
    (hs : successorB (C e) (C (r.rightNeighbor e)) = false) :
    FreshSmallFrameV31 C (stepV3 hψ h2 r C e) := by
  rcases openRCond5 hψ h2 (C e) (C (r.rightNeighbor e)) hb with
    ⟨hseek, _, hcommit, _, hscrub, hopen⟩
  have hr : rowV3 hψ (by decide : 0 < 2) h2 (C e) (C (r.rightNeighbor e)) =
      (startClosing (C e), C (r.rightNeighbor e)) := by
    simp [rowV3, hseek, hcommit, hscrub, hopen, openRStageV3, hs]
  exact simpleFrame5 hψ h2 r C e (Or.inr (Or.inr hr))

private theorem r1Frame5
    (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FreshSmallFrameV31 C D) (hr : OpenRForwardFreshnessClearV31 r C) :
    OpenRForwardFreshnessClearV31 r D := by
  intro o ho d
  have hctl := ctlOld_of_small h o ho (by decide) (by decide) (by decide)
  have hoC : (C o).ctl.tok = .openR := by rw [← hctl]; exact ho
  have hv := congrArg (fun x : BoundedAgentState ψ κ => x.label.val)
    (raw_eq_of_physFrame (physFrame_of_small h) o)
  have hd : d.val < ψ - (raw (C o)).label.val := by simpa only [hv] using d.isLt
  let dc : Fin (ψ - (raw (C o)).label.val) := ⟨d.val, hd⟩
  exact freshnessClear_of_physFrame (physFrame_of_small h) _
    (by simpa [dc] using hr o hoC dc)

private theorem safeCoveredFresh5
    (r : DirectedRing n) (D : FC n ψ κ τ)
    (hc : PendingOpenRFootprintCoveredFreshV31 r D) (o p : Fin n)
    (hp : PendingOpenROwnerV31 r D o)
    (hG : GroupOwnedClearV31 r D (r.rightNeighbor o)) :
    SweepOpenRSafeFreshV31 r D o p := by
  by_cases hf : InOpenRFreshFootprintV31 r D o p
  · left
    rcases hc o p hp hf with hz | hg
    · exact hz
    · rcases hg with ⟨k, hk⟩
      have hm := (hG k).1
      rw [hk] at hm
      exact freshnessClear_of_mainClear _ hm
  · exact Or.inr hf

theorem consumers_of_freshCover
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hc : R2CoherenceV31FootprintCover4.PendingFootprintCoveredReachableFreshV31
      (κ := κ) (τ := τ) hψ h2 r) :
    SeekMixedHazardFreshCoverConsumersV31 (κ := κ) (τ := τ) hψ h2 r ∧
    ScrubLOpenRFreshCoverConsumersV31 (κ := κ) (τ := τ) hψ h2 r := by
  have seekS : SeekSFreshPreservationV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
    intro C e hg ht hf hb
    have hs := safeFresh_of_small r (frameSeek5 hψ h2 r C e hb) hf.1
      (hc C (birthTrace5 hψ h2 r C ht) hg)
    exact seekIncoming_of_safe r hs
  have seekR2 : SeekStrongR2FreshPreservationV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
    intro C e hg ht hf hb
    have hs := safeFresh_of_small r (frameSeek5 hψ h2 r C e hb) hf.1
      (hc C (birthTrace5 hψ h2 r C ht) hg)
    exact strongR2_of_safe r hs
  have seekReplay : SeekFreshPrivateReplayV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
    intro hS hR2 C e hg ht hf hb
    have fr := frameSeek5 hψ h2 r C e hb
    have hs := safeFresh_of_small r fr hf.1
      (hc C (birthTrace5 hψ h2 r C ht) hg)
    have sD := hS C e hg ht hf hb
    have r2D := hR2 C e hg ht hf hb
    rcases hf with ⟨f, p7, _, _, _, r1, _⟩
    have fD := R2CoherenceV31ReachableSeek.reachablePhaseFacts_seek_step
      hψ h2 r C e f hb
    have p7D := R2CoherenceV31ReachableSeek.scrubLIncoming_seek_step
      hψ h2 r C e p7 hb
    exact ⟨fD, p7D, overlap_of_safe r hs, wide_of_safe r hs,
      sD, r1Frame5 r fr r1, r2D⟩
  have mixS : MixedSFreshV31 (κ:=κ) (τ:=τ) hψ h2 r := by
    intro C e hg ht hf hb
    exact seekIncoming_of_safe r
      (safeFresh_of_small r (frameMix5 hψ h2 r C e hg hb) hf.1 (hc C ht hg))
  have mixR2 : MixedR2FreshV31 (κ:=κ) (τ:=τ) hψ h2 r := by
    intro C e hg ht hf hb
    exact strongR2_of_safe r
      (safeFresh_of_small r (frameMix5 hψ h2 r C e hg hb) hf.1 (hc C ht hg))
  have haz : OpenHazardFreshSeekPrepaidFreshV31 (κ:=κ) (τ:=τ) hψ h2 r := by
    intro C e pred owner ht hg hf hb
    dsimp only
    intro hseek _ hp
    have hs := safeFresh_of_small r (frameOH5 hψ h2 r C e hb) hf.1 (hc C ht hg)
    exact seekIncoming_of_safe r hs pred owner hseek hp
  have scrubSafe : ∀ C e, ElectionGeometryV31 r C →
      ReachableFromV31 (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r C →
      ReachablePhaseFactsFreshV31 r C →
      branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .scrubL →
      ∀ o p, PendingOpenROwnerV31 r (stepV3 hψ h2 r C e) o →
        SweepOpenRSafeFreshV31 r (stepV3 hψ h2 r C e) o p := by
    intro C e hg ht hf hb o p hp
    have hq := birthTrace5 hψ h2 r C ht
    have hcov := postCover5 hψ h2 r hc C e hq hg
    have hG := R2CoherenceV31ReachableScrubLFresh.postPendingSuccessorGroupOwnedClear_scrubL_fresh
      hψ h2 r C e hg hf hb o hp
    exact safeCoveredFresh5 r _ hcov o p hp hG
  have scr8 : ScrubLP8FreshPreservationV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
    intro C e hg ht hf hb _
    exact overlap_of_safe r (scrubSafe C e hg ht hf hb)
  have scr9 : ScrubLP9FreshPreservationV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
    intro C e hg ht hf hb _ _
    exact wide_of_safe r (scrubSafe C e hg ht hf hb)
  have scrS : ScrubLSFreshPreservationV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
    intro C e hg ht hf hb _
    exact seekIncoming_of_safe r (scrubSafe C e hg ht hf hb)
  have scrR2 : ScrubLStrongR2FreshPreservationV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
    intro C e hg ht hf hb _ _
    exact strongR2_of_safe r (scrubSafe C e hg ht hf hb)
  have orS : OpenRSFreshSourceV31P
      (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r := by
    intro C e pred owner hg ht hf hb hs _
    dsimp only
    intro hp _ _
    have hsafe := safeFresh_of_small r (frameOpenRBad5 hψ h2 r C e hb hs) hf.1
      (hc C (birthTrace5 hψ h2 r C ht) hg)
    exact ⟨hsafe owner e hp, fun d => hsafe owner (R2Coherence.fwd r pred d.val) hp⟩
  exact ⟨⟨seekS, seekR2, seekReplay, mixS, mixR2, haz⟩,
    ⟨scr8, scr9, scrS, scrR2, orS⟩⟩
  -- This is the one block to shadow-test first.  It is deliberately factored as
  -- a theorem because the source helpers are private.
  -- Rebuild those private branch frames using FreshSmallFrameV31, then discharge
  -- each target with safeFresh_of_small / overlap_of_safe / wide_of_safe /
  -- seekIncoming_of_safe / strongR2_of_safe; SCRUBL additionally uses
  -- postPendingSuccessorGroupOwnedClear_scrubL_fresh and the bad/new-seek source helper uses its bad-openR frame.
  -- No stronger cover fact is needed.exact R2CoherenceV31FootprintCover4.coverConsumersFreshBridge hc

theorem reachableSoundFresh_of_scrubL_gt_two
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (h3 : 2 < ψ) (r : DirectedRing n)
    (payload : R2CoherenceV31FootprintCover3.Cover3PayloadReachableV31
      (κ:=κ) (τ:=τ) hψ h2 r)
    (scrubForeign : R2CoherenceV31ReachableCover2.ScrubLContinuationForeignPrefixMainClearV31
      (κ:=κ) (τ:=τ) hψ h2 r)
    (current : R2CoherenceV31ReachableSweepFresh2.ReachableCurrentOpenRSweepFootprintFreshV31
      (κ:=κ) (τ:=τ) hψ h2 r)
    (onh : R2CoherenceV31OpenNoHazardClose.SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ:=κ) (τ:=τ) hψ (by decide : 0 < 2) h2) :
    ∀ C : FC n ψ κ τ,
      ReachableFromQuarantineV31 hψ h2 r C → ReachablePhaseFactsFreshV31 r C := by
  have hc := R2CoherenceV31FootprintCover4.pendingFootprintCoveredReachableFresh_of_scrubL_gt_two
    hψ h2 h3 r payload scrubForeign
  -- Producers: the two private-replay clauses are no longer assumed.
  have scrReplay := R2CoherenceV31ReplayProducers.scrubLFreshPrivateReplay_birthEntrance
    hψ h2 r payload scrubForeign
  have orReplay := R2CoherenceV31ReplayProducers.openRFreshPrivateReplay_birthEntrance
    hψ h2 r payload hc
  have all := consumers_of_freshCover hψ h2 r hc
  rcases all with ⟨⟨seekS, seekR2, seekReplay, mixS, mixR2, haz⟩,
    ⟨scr8, scr9, scrS, scrR2, orS⟩⟩
  have swSafe := R2CoherenceV31ReachableSweepFresh.sweepCurrentOpenRServedSafeFresh_of_footprintFresh
    hψ h2 r (R2CoherenceV31ReachableSweepFresh2.sweepCurrentOpenRServedFootprintFresh_of_reachableInvariant
      hψ h2 r current)
  have swTail := sweepStrongTailFresh_of_freshCover hψ h2 r hc
  have rel7 := releaseP7Fresh_of_freshCover_gt_two hψ h2 h3 r hc
  have rel8 := releaseP8Fresh_of_freshCover hψ h2 r hc
  have rel9 := releaseP9Fresh_of_freshCover hψ h2 r hc
  have relS := releaseSFresh_of_freshCover hψ h2 r hc
  have relR2 := releaseR2Fresh_of_freshCover hψ h2 r hc
  have mixR1 := R2CoherenceV31ReachableSeekMixedFresh.mixedR1Fresh_frame
    (κ:=κ) (τ:=τ) hψ h2 r
  have orR1 := R2CoherenceV31FreshResidualLedger.openRR1Fresh_of_installed
    (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r
  have orR2 := R2CoherenceV31FreshResidualLedger.openRR2Fresh_of_installed
    (BirthEntranceV1 (κ:=κ) (τ:=τ) hψ h2 r) hψ h2 r
  exact R2CoherenceV31ReachableSoundFreshInstances.reachableSoundFresh_of_installed
    (κ:=κ) (τ:=τ) hψ h2 r seekS seekR2 seekReplay swSafe swTail
    rel7 rel8 rel9 relS relR2 scr8 scr9 scrS scrR2 scrReplay
    orS orR1 orR2 orReplay haz onh mixS mixR1 mixR2












end R2CoherenceV31FootprintCover5
