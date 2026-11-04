import Leader.Wu.Coherence.ReachableOpenHazard


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachableOpenHazard2


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableOpenHazard


variable {n ψ κ τ : Nat}


private theorem branch_openHazard_conditions2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openHazard) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .open ∧ r.ctl.mark = .open ∧
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = true) := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all


private theorem rowV3_openHazard_form2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openHazard) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = (l, startClosing r) ∨
      rowV3 hψ (by decide : 0 < 2) h2 l r = (startClosing l, r) := by
  rcases branch_openHazard_conditions2 hψ h2 l r hb with
    ⟨hln, hrn, hlo, hro, hHaz⟩
  let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
  by_cases hr : endpointHazardV3 r.phys q.2
  · left
    simp [rowV3, ordinaryStageV3, openStageV3,
      hln, hrn, hlo, hro, hHaz, q, hr]
  · right
    simp [rowV3, ordinaryStageV3, openStageV3,
      hln, hrn, hlo, hro, hHaz, q, hr]


private theorem openHazard_step_phys_eq2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    ∀ p, (stepV3 hψ h2 ring C e p).phys = (C p).phys := by
  intro p
  rcases rowV3_openHazard_form2 hψ h2
      (C e) (C (ring.rightNeighbor e)) hb with hrow | hrow
  all_goals
    by_cases hpe : p = e
    · subst p
      simp [stepV3, protocolV3, PopulationProtocol.step,
        hrow, startClosing, setControl]
    · by_cases hpr : p = ring.rightNeighbor e
      · subst p
        simp [stepV3, protocolV3, PopulationProtocol.step,
          hrow, hpe, startClosing, setControl]
      · exact congrArg Cell.phys
          (stepV3_other hψ h2 ring C e p hpe hpr)


private theorem openHazard_step_ctl_old_or_seek2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    (stepV3 hψ h2 ring C e p).ctl = (C p).ctl ∨
      ((stepV3 hψ h2 ring C e p).ctl.mark = .closing ∧
       (stepV3 hψ h2 ring C e p).ctl.tok = .seek) := by
  rcases rowV3_openHazard_form2 hψ h2
      (C e) (C (ring.rightNeighbor e)) hb with hrow | hrow
  all_goals
    by_cases hpe : p = e
    · subst p
      simp [stepV3, protocolV3, PopulationProtocol.step,
        hrow, startClosing, setControl]
    · by_cases hpr : p = ring.rightNeighbor e
      · subst p
        simp [stepV3, protocolV3, PopulationProtocol.step,
          hrow, hpe, startClosing, setControl]
      · left
        exact congrArg (fun x : Cell ψ κ τ => x.ctl)
          (stepV3_other hψ h2 ring C e p hpe hpr)


private theorem openHazard_post_nonseek_ctl_eq2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    {t : TokenV3} (ht : (stepV3 hψ h2 ring C e p).ctl.tok = t)
    (hne : t ≠ .seek) :
    (stepV3 hψ h2 ring C e p).ctl = (C p).ctl := by
  rcases openHazard_step_ctl_old_or_seek2 hψ h2 ring C e p hb with h | h
  · exact h
  · exact (hne (ht.symm.trans h.2)).elim


private theorem raw_eq_openHazard2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    raw (stepV3 hψ h2 ring C e p) = raw (C p) :=
  congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core)
    (openHazard_step_phys_eq2 hψ h2 ring C e hb p)


private theorem mainClear_phys_frame2 {u v : Cell ψ κ τ}
    (hp : u.phys = v.phys) (h : MainClearV3 v) : MainClearV3 u := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at h ⊢
  simpa [eraseCellV3, R2Coherence.raw, hp] using h

private theorem footprint_openHazard_to_before2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : InOpenRFreshFootprintV31 ring (stepV3 hψ h2 ring C e) owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  have hLab : ∀ x : Fin n,
      (raw (stepV3 hψ h2 ring C e x)).label = (raw (C x)).label := by
    intro x
    exact congrArg (fun s : BoundedAgentState ψ κ => s.label)
      (raw_eq_openHazard2 hψ h2 ring C e x hb)
  have hGP : ∀ (i : Fin n) (k : Nat),
      R2Coherence.groupPos ring
          (eraseCfgV3 (stepV3 hψ h2 ring C e)) i k =
        R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
    intro i k
    unfold R2Coherence.groupPos R2Coherence.groupStart
    change R2Coherence.fwd ring
        (R2Coherence.back ring i
          (raw (stepV3 hψ h2 ring C e i)).label.val) k =
      R2Coherence.fwd ring
        (R2Coherence.back ring i (raw (C i)).label.val) k
    rw [hLab i]
  have hPP : ∀ (i : Fin n) (k : Nat),
      R2Coherence.prefixPos ring
          (eraseCfgV3 (stepV3 hψ h2 ring C e)) i k =
        R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
    intro i k
    unfold R2Coherence.prefixPos
    change R2Coherence.back ring i
        ((raw (stepV3 hψ h2 ring C e i)).label.val - k) =
      R2Coherence.back ring i ((raw (C i)).label.val - k)
    rw [hLab i]
  rcases h with ⟨j, ko, q, hOwnerD, kD, hPrefixD⟩
  rw [hGP j ko.val] at hOwnerD
  have hGPq := hGP j q.val
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hFrontD :
      R2Coherence.groupPos ring
        (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val = front := by
    simpa [front] using hGPq
  have hLabelVal :
      (raw (stepV3 hψ h2 ring C e
        (R2Coherence.groupPos ring
          (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val))).label.val =
        (raw (C front)).label.val := by
    rw [hFrontD]
    exact congrArg (fun x : Fin ψ => x.val) (hLab front)
  have hkC : kD.val < (raw (C front)).label.val + 1 := by
    let m : Nat := kD.val
    have hmD : m <
        (raw (stepV3 hψ h2 ring C e
          (R2Coherence.groupPos ring
            (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val))).label.val + 1 :=
      kD.isLt
    simpa only [hLabelVal] using hmD
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
  refine ⟨j, ko, q, hOwnerD, kC, ?_⟩
  let m : Nat := kD.val
  have hPrefixD0 :
      R2Coherence.prefixPos ring
        (eraseCfgV3 (stepV3 hψ h2 ring C e))
        (R2Coherence.groupPos ring
          (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val) m = p := by
    simpa [m] using hPrefixD
  have hPrefixD1 :
      R2Coherence.prefixPos ring
        (eraseCfgV3 (stepV3 hψ h2 ring C e)) front m = p := by
    simpa only [hFrontD] using hPrefixD0
  have hPPm := hPP front m
  have hPrefixC :
      R2Coherence.prefixPos ring (eraseCfgV3 C) front m = p := by
    exact hPPm.symm.trans hPrefixD1
  have hFrontC :
      R2Coherence.groupPos ring (eraseCfgV3 C) j q.val = front := by
    rfl
  have hkCm : kC.val = m := by
    rfl
  simpa only [hFrontC, hkCm] using hPrefixC


private theorem pending_openHazard_to_before2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases h with ⟨hs, hSucc, hRoot⟩
  have hc := openHazard_post_nonseek_ctl_eq2 hψ h2 ring C e
    (ring.rightNeighbor owner) hb hs (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [hc] at hs
    exact hs
  · unfold successorB at hSucc ⊢
    rw [raw_eq_openHazard2 hψ h2 ring C e owner hb,
      raw_eq_openHazard2 hψ h2 ring C e (ring.rightNeighbor owner) hb] at hSucc
    exact hSucc
  · unfold atRootB at hRoot ⊢
    rw [raw_eq_openHazard2 hψ h2 ring C e owner hb] at hRoot
    exact hRoot


private theorem safeAt_openHazard_step2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : SweepOpenRSafeAtV31 ring C owner p) :
    SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner p := by
  rcases h with hm | hout
  · exact Or.inl (mainClear_phys_frame2
      (openHazard_step_phys_eq2 hψ h2 ring C e hb p) hm)
  · exact Or.inr (fun hf => hout
      (footprint_openHazard_to_before2 hψ h2 ring C e owner p hb hf))


private theorem safeWindow_openHazard_step2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e front owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : SweepOpenRSafeAtV31 ring C owner (ring.rightNeighbor front) ∧
      ∀ d : Fin (ψ - (raw (C front)).label.val),
        SweepOpenRSafeAtV31 ring C owner (R2Coherence.fwd ring front d.val)) :
    SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner
        (ring.rightNeighbor front) ∧
      ∀ d : Fin (ψ - (raw (stepV3 hψ h2 ring C e front)).label.val),
        SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner
          (R2Coherence.fwd ring front d.val) := by
  constructor
  · exact safeAt_openHazard_step2 hψ h2 ring C e owner
      (ring.rightNeighbor front) hb h.1
  · intro dD
    have hv := congrArg (fun x : BoundedAgentState ψ κ => x.label.val)
      (raw_eq_openHazard2 hψ h2 ring C e front hb)
    have hd : dD.val < ψ - (raw (C front)).label.val := by
      simpa only [hv] using dD.isLt
    let dC : Fin (ψ - (raw (C front)).label.val) := ⟨dD.val, hd⟩
    exact safeAt_openHazard_step2 hψ h2 ring C e owner
      (R2Coherence.fwd ring front dD.val) hb (by simpa [dC] using h.2 dC)


theorem seekIncomingSweepOpenROverlapClearWide_openHazard_of_fresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hFresh : OpenHazardFreshSeekPrepaidV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hGeom : R2CoherenceV31Closure.ElectionGeometryV31 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    SeekIncomingSweepOpenROverlapClearWideV31 ring
      (stepV3 hψ h2 ring C e) := by
  intro pred owner hSeekD hPendingD
  by_cases hSeekC : (C (ring.rightNeighbor pred)).ctl.tok = .seek
  · have hPendingC := pending_openHazard_to_before2
      hψ h2 ring C e owner hb hPendingD
    have hOld := hPlus.2.1 pred owner hSeekC hPendingC
    constructor
    · intro hRootD
      have hRootC : atRootB (C (ring.rightNeighbor pred)) = true := by
        unfold atRootB at hRootD ⊢
        rw [raw_eq_openHazard2 hψ h2 ring C e (ring.rightNeighbor pred) hb] at hRootD
        exact hRootD
      exact safeWindow_openHazard_step2 hψ h2 ring C e
        (ring.rightNeighbor pred) owner hb (hOld.1 hRootC)
    · intro hNotRootD hRootPredD
      have hNotRootC : atRootB (C (ring.rightNeighbor pred)) = false := by
        unfold atRootB at hNotRootD ⊢
        rw [raw_eq_openHazard2 hψ h2 ring C e (ring.rightNeighbor pred) hb] at hNotRootD
        exact hNotRootD
      have hRootPredC : atRootB (C pred) = true := by
        unfold atRootB at hRootPredD ⊢
        rw [raw_eq_openHazard2 hψ h2 ring C e pred hb] at hRootPredD
        exact hRootPredD
      exact safeWindow_openHazard_step2 hψ h2 ring C e pred owner hb
        (hOld.2 hNotRootC hRootPredC)
  · exact hFresh C e pred owner hTrace hGeom hPlus hb
      hSeekD hSeekC hPendingD


/-- R1 is frame-only: no `.openR` is created, labels and all physical fields
are unchanged. -/
theorem openRForwardMainClear_openHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hR1 : OpenRForwardMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    OpenRForwardMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  intro owner hOpenR dD
  have hc := openHazard_post_nonseek_ctl_eq2 hψ h2 ring C e owner hb hOpenR (by decide)
  have hOpenC : (C owner).ctl.tok = .openR := by simpa [hc] using hOpenR
  have hv := congrArg (fun x : BoundedAgentState ψ κ => x.label.val)
    (raw_eq_openHazard2 hψ h2 ring C e owner hb)
  have hd : dD.val < ψ - (raw (C owner)).label.val := by
    simpa only [hv] using dD.isLt
  let dC : Fin (ψ - (raw (C owner)).label.val) := ⟨dD.val, hd⟩
  exact mainClear_phys_frame2
    (openHazard_step_phys_eq2 hψ h2 ring C e hb
      (R2Coherence.fwd ring owner dD.val))
    (by simpa [dC] using hR1 owner hOpenC dC)

private theorem sweptFootprint_openHazard_to_before2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : InSweptOwnedFootprintV31 ring (stepV3 hψ h2 ring C e) owner p) :
    InSweptOwnedFootprintV31 ring C owner p := by
  rcases h with ⟨kD, hp⟩
  have hv := congrArg (fun s : BoundedAgentState ψ κ => s.label.val)
    (raw_eq_openHazard2 hψ h2 ring C e owner hb)
  let m : Nat := kD.val
  have hmD : m < (raw (stepV3 hψ h2 ring C e owner)).label.val :=
    kD.isLt
  have hk : m < (raw (C owner)).label.val := by
    simpa only [hv] using hmD
  let kC : Fin (raw (C owner)).label.val := ⟨m, hk⟩
  refine ⟨kC, ?_⟩
  change R2Coherence.groupPos ring (eraseCfgV3 C) owner m = p
  have hpM : R2Coherence.groupPos ring
      (eraseCfgV3 (stepV3 hψ h2 ring C e)) owner m = p := by
    simpa [m] using hp
  have hGPm : R2Coherence.groupPos ring
      (eraseCfgV3 (stepV3 hψ h2 ring C e)) owner m =
      R2Coherence.groupPos ring (eraseCfgV3 C) owner m := by
    unfold R2Coherence.groupPos R2Coherence.groupStart
    change R2Coherence.fwd ring
        (R2Coherence.back ring owner
          (raw (stepV3 hψ h2 ring C e owner)).label.val) m =
      R2Coherence.fwd ring
        (R2Coherence.back ring owner (raw (C owner)).label.val) m
    rw [hv]
  exact hGPm.symm.trans hpM


private theorem groupFootprint_openHazard_to_before2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : InGroupOwnedFootprintV31 ring (stepV3 hψ h2 ring C e) owner p) :
    InGroupOwnedFootprintV31 ring C owner p := by
  rcases h with ⟨k, hp⟩
  refine ⟨k, ?_⟩
  have hGP : R2Coherence.groupPos ring
      (eraseCfgV3 (stepV3 hψ h2 ring C e)) owner k.val =
      R2Coherence.groupPos ring (eraseCfgV3 C) owner k.val := by
    unfold R2Coherence.groupPos R2Coherence.groupStart
    change R2Coherence.fwd ring
        (R2Coherence.back ring owner
          (raw (stepV3 hψ h2 ring C e owner)).label.val) k.val =
      R2Coherence.fwd ring
        (R2Coherence.back ring owner (raw (C owner)).label.val) k.val
    rw [raw_eq_openHazard2 hψ h2 ring C e owner hb]
  exact hGP.symm.trans hp


private theorem phaseOwned_openHazard_step2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : PhaseOwnedV31 (C p)) : PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
  rcases openHazard_step_ctl_old_or_seek2 hψ h2 ring C e p hb with hc | hc
  · unfold PhaseOwnedV31 at h ⊢; simpa [hc] using h
  · unfold PhaseOwnedV31; left; rw [hc.1]; decide


private theorem carriesGroup_openHazard_to_before2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : CarriesGroupOwnedPhaseV31 (stepV3 hψ h2 ring C e) owner) :
    CarriesGroupOwnedPhaseV31 C owner := by
  rcases h with hc | hs | hr | hsl
  · have hctl := openHazard_post_nonseek_ctl_eq2 hψ h2 ring C e owner hb hc (by decide)
    exact Or.inl (by simpa [hctl] using hc)
  · rcases openHazard_step_ctl_old_or_seek2 hψ h2 ring C e owner hb with hctl | hnew
    · exact Or.inr (Or.inl (by simpa [hctl] using hs))
    · have hx : (R2Coherence.Mark.sealed : R2Coherence.Mark) = .closing := hs.symm.trans hnew.1
      cases hx
  · have hctl := openHazard_post_nonseek_ctl_eq2 hψ h2 ring C e owner hb hr (by decide)
    exact Or.inr (Or.inr (Or.inl (by simpa [hctl] using hr)))
  · have hctl := openHazard_post_nonseek_ctl_eq2 hψ h2 ring C e owner hb hsl (by decide)
    exact Or.inr (Or.inr (Or.inr (by simpa [hctl] using hsl)))


private theorem sweepWideRead_openHazard_to_before2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e sweep p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : R2CoherenceV31ReachableOpenNoHazard3.InSweepWideReadV31 ring
      (stepV3 hψ h2 ring C e) sweep p) :
    R2CoherenceV31ReachableOpenNoHazard3.InSweepWideReadV31 ring C sweep p := by
  rcases h with hresp | ⟨dD, hpos⟩
  · exact Or.inl hresp
  · right
    have hv := congrArg (fun s : BoundedAgentState ψ κ => s.label.val)
      (raw_eq_openHazard2 hψ h2 ring C e sweep hb)
    have hd : dD.val < ψ - (raw (C sweep)).label.val := by
      simpa only [hv] using dD.isLt
    let dC : Fin (ψ - (raw (C sweep)).label.val) := ⟨dD.val, hd⟩
    exact ⟨dC, by simpa [dC] using hpos⟩


theorem openRPhaseOwnershipDisjointStrong_openHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hStrong : OpenRPhaseOwnershipDisjointStrongV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    OpenRPhaseOwnershipDisjointStrongV31 ring (stepV3 hψ h2 ring C e) := by
  constructor
  · intro o owner hOpenD hSuccD hne
    have hctlO := openHazard_post_nonseek_ctl_eq2 hψ h2 ring C e o hb hOpenD (by decide)
    have hOpenC : (C o).ctl.tok = .openR := by simpa [hctlO] using hOpenD
    have hSuccC : successorB (C o) (C (ring.rightNeighbor o)) = true := by
      unfold successorB at hSuccD ⊢
      rw [raw_eq_openHazard2 hψ h2 ring C e o hb,
        raw_eq_openHazard2 hψ h2 ring C e (ring.rightNeighbor o) hb] at hSuccD
      exact hSuccD
    have hOld := hStrong.1 o owner hOpenC hSuccC hne
    refine ⟨?_, ?_, ?_⟩
    · intro hSweepD hFootD
      have hctl := openHazard_post_nonseek_ctl_eq2 hψ h2 ring C e owner hb hSweepD (by decide)
      exact (hOld.1 (by simpa [hctl] using hSweepD))
        (sweptFootprint_openHazard_to_before2 hψ h2 ring C e owner o hb hFootD)
    · intro hCarryD hFootD
      exact (hOld.2.1
        (carriesGroup_openHazard_to_before2 hψ h2 ring C e owner hb hCarryD))
        (groupFootprint_openHazard_to_before2 hψ h2 ring C e owner o hb hFootD)
    · intro hTermD
      have hTermC : atTerminalB (C (ring.rightNeighbor o)) = true := by
        unfold atTerminalB at hTermD ⊢
        rw [raw_eq_openHazard2 hψ h2 ring C e (ring.rightNeighbor o) hb] at hTermD
        exact hTermD
      have ht := hOld.2.2 hTermC
      constructor
      · intro hSweepD hFootD
        have hctl := openHazard_post_nonseek_ctl_eq2 hψ h2 ring C e owner hb hSweepD (by decide)
        exact (ht.1 (by simpa [hctl] using hSweepD))
          (sweptFootprint_openHazard_to_before2 hψ h2 ring C e owner
            (ring.rightNeighbor o) hb hFootD)
      · intro hCarryD hFootD
        exact (ht.2
          (carriesGroup_openHazard_to_before2 hψ h2 ring C e owner hb hCarryD))
          (groupFootprint_openHazard_to_before2 hψ h2 ring C e owner
            (ring.rightNeighbor o) hb hFootD)
  · intro sweep owner p hSweepD hPendingD hReadD hFootD
    have hctl := openHazard_post_nonseek_ctl_eq2 hψ h2 ring C e sweep hb hSweepD (by decide)
    have hSweepC : (C sweep).ctl.tok = .sweep := by simpa [hctl] using hSweepD
    have hPendingC := pending_openHazard_to_before2 hψ h2 ring C e owner hb hPendingD
    have hReadC := sweepWideRead_openHazard_to_before2
      hψ h2 ring C e sweep p hb hReadD
    have hFootC := footprint_openHazard_to_before2
      hψ h2 ring C e owner p hb hFootD
    exact phaseOwned_openHazard_step2 hψ h2 ring C e p hb
      (hStrong.2 sweep owner p hSweepC hPendingC hReadC hFootC)

/-- Full openHazard assembly.  The sole extra hypothesis is the exact fresh-seek
prepayment residual already named. -/
theorem openHazardStep_reachable_full
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hFresh : OpenHazardFreshSeekPrepaidV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : R2CoherenceV31Closure.ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    ReachablePhaseFactsPlus4StrongR2V31 ring
      (stepV3 hψ h2 ring C e) := by
  have hP3 := reachablePhaseFactsPlus3_openHazard_step
    hψ h2 ring C e hGeom hTrace hPlus hb
  have hS := seekIncomingSweepOpenROverlapClearWide_openHazard_of_fresh
    hψ h2 ring hFresh C e hTrace hGeom hPlus hb
  have hR1 := openRForwardMainClear_openHazard_step
    hψ h2 ring C e hPlus.2.2.1 hb
  have hR2 := openRPhaseOwnershipDisjointStrong_openHazard_step
    hψ h2 ring C e hPlus.2.2.2 hb
  exact ⟨hP3, hS, hR1, hR2⟩


end R2CoherenceV31ReachableOpenHazard2
