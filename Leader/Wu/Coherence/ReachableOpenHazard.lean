import Leader.Wu.Coherence.ReachableStrongOwnership
import Leader.Wu.Coherence.ReachableOpenRBadSeek

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableOpenHazard

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4

variable {n ψ κ τ : Nat}

private theorem branch_openHazard_conditions_oh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openHazard) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .open ∧ r.ctl.mark = .open ∧
      (let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
       pairHazardV3 l.phys r.phys q.1 q.2 = true) := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all

private theorem rowV3_openHazard_form_oh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .openHazard) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = (l, startClosing r) ∨
      rowV3 hψ (by decide : 0 < 2) h2 l r = (startClosing l, r) := by
  rcases branch_openHazard_conditions_oh hψ h2 l r hb with
    ⟨hln, hrn, hlo, hro, hHaz⟩
  let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
  by_cases hr : endpointHazardV3 r.phys q.2
  · left
    simp [rowV3, ordinaryStageV3, openStageV3,
      hln, hrn, hlo, hro, hHaz, q, hr]
  · right
    simp [rowV3, ordinaryStageV3, openStageV3,
      hln, hrn, hlo, hro, hHaz, q, hr]

private theorem openHazard_step_phys_eq_oh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    ∀ p, (stepV3 hψ h2 ring C e p).phys = (C p).phys := by
  intro p
  rcases rowV3_openHazard_form_oh hψ h2
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

private theorem openHazard_step_ctl_old_or_seek_oh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    (stepV3 hψ h2 ring C e p).ctl = (C p).ctl ∨
      ((stepV3 hψ h2 ring C e p).ctl.mark = .closing ∧
       (stepV3 hψ h2 ring C e p).ctl.tok = .seek) := by
  rcases rowV3_openHazard_form_oh hψ h2
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
        exact congrArg Cell.ctl
          (stepV3_other hψ h2 ring C e p hpe hpr)

private theorem openHazard_post_nonseek_ctl_eq_oh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    {t : TokenV3} (ht : (stepV3 hψ h2 ring C e p).ctl.tok = t)
    (hne : t ≠ .seek) :
    (stepV3 hψ h2 ring C e p).ctl = (C p).ctl := by
  rcases openHazard_step_ctl_old_or_seek_oh hψ h2 ring C e p hb with h | h
  · exact h
  · exact (hne (ht.symm.trans h.2)).elim

private theorem mainClear_of_phys_eq_oh {u v : Cell ψ κ τ}
    (hp : u.phys = v.phys) (h : MainClearV3 v) : MainClearV3 u := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at h ⊢
  simpa [eraseCellV3, R2Coherence.raw, hp] using h

private theorem phaseOwned_openHazard_step_oh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : PhaseOwnedV31 (C p)) : PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
  rcases openHazard_step_ctl_old_or_seek_oh hψ h2 ring C e p hb with hc | hc
  · unfold PhaseOwnedV31 at h ⊢; simpa [hc] using h
  · unfold PhaseOwnedV31; left; rw [hc.1]; decide

private theorem ownedClear_openHazard_step_oh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : MainClearV3 (C p) ∧ PhaseOwnedV31 (C p)) :
    MainClearV3 (stepV3 hψ h2 ring C e p) ∧
      PhaseOwnedV31 (stepV3 hψ h2 ring C e p) :=
  ⟨mainClear_of_phys_eq_oh
      (openHazard_step_phys_eq_oh hψ h2 ring C e hb p) h.1,
   phaseOwned_openHazard_step_oh hψ h2 ring C e p hb h.2⟩

private theorem raw_eq_openHazard_oh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    raw (stepV3 hψ h2 ring C e p) = raw (C p) := by
  exact congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core)
    (openHazard_step_phys_eq_oh hψ h2 ring C e hb p)

private theorem groupPos_openHazard_eq_oh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n) (k : Nat)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    R2Coherence.groupPos ring
      (eraseCfgV3 (stepV3 hψ h2 ring C e)) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring
      (R2Coherence.back ring i
        (raw (stepV3 hψ h2 ring C e i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [raw_eq_openHazard_oh hψ h2 ring C e i hb]

private theorem sweptPrefix_openHazard_step_oh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : SweptPrefixOwnedClearV31 ring C i) :
    SweptPrefixOwnedClearV31 ring (stepV3 hψ h2 ring C e) i := by
  unfold SweptPrefixOwnedClearV31 at h ⊢
  intro k
  have hv := congrArg (fun x : BoundedAgentState ψ κ => x.label.val)
    (raw_eq_openHazard_oh hψ h2 ring C e i hb)
  have hk : k.val < (raw (C i)).label.val := by simpa only [hv] using k.isLt
  let kc : Fin (raw (C i)).label.val := ⟨k.val, hk⟩
  rw [groupPos_openHazard_eq_oh hψ h2 ring C e i k.val hb]
  exact ownedClear_openHazard_step_oh hψ h2 ring C e _ hb (h kc)

private theorem groupOwned_openHazard_step_oh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : GroupOwnedClearV31 ring C i) :
    GroupOwnedClearV31 ring (stepV3 hψ h2 ring C e) i := by
  unfold GroupOwnedClearV31 at h ⊢
  intro k
  rw [groupPos_openHazard_eq_oh hψ h2 ring C e i k.val hb]
  exact ownedClear_openHazard_step_oh hψ h2 ring C e _ hb (h k)

private theorem openROwnerFresh_phys_frame_oh
    (ring : DirectedRing n) {C D : FC n ψ κ τ} (owner : Fin n)
    (hp : ∀ p, (D p).phys = (C p).phys)
    (h : OpenROwnerFreshV3 ring C owner) : OpenROwnerFreshV3 ring D owner := by
  have hRaw : ∀ p, raw (D p) = raw (C p) := fun p =>
    congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core) (hp p)
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label := fun p =>
    congrArg (fun x : BoundedAgentState ψ κ => x.label) (hRaw p)
  have hGP : ∀ (i : Fin n) (k : Nat),
      R2Coherence.groupPos ring (eraseCfgV3 D) i k =
        R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
    intro i k
    unfold R2Coherence.groupPos R2Coherence.groupStart
    change R2Coherence.fwd ring
        (R2Coherence.back ring i (raw (D i)).label.val) k =
      R2Coherence.fwd ring
        (R2Coherence.back ring i (raw (C i)).label.val) k
    rw [hLab i]
  have hPP : ∀ (i : Fin n) (k : Nat),
      R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
        R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
    intro i k
    unfold R2Coherence.prefixPos
    change R2Coherence.back ring i ((raw (D i)).label.val - k) =
      R2Coherence.back ring i ((raw (C i)).label.val - k)
    rw [hLab i]
  unfold OpenROwnerFreshV3 at h ⊢
  intro j ko hHitD
  rw [hGP j ko.val] at hHitD
  have hOldGroup := h j ko hHitD
  unfold GroupIntrinsicFreshV3 at hOldGroup ⊢
  intro q
  rw [hGP j q.val]
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  change IntrinsicFreshAtV3 ring D front
  have hOldFront : IntrinsicFreshAtV3 ring C front := by
    simpa [front] using hOldGroup q
  unfold IntrinsicFreshAtV3 at hOldFront ⊢
  intro hEqD
  have hState := congrArg
    (fun x : BoundedAgentState ψ κ => x.state) (hRaw front)
  have hEqC : (raw (C front)).state = .equal := by
    rw [← hState]
    exact hEqD
  have hOldAt := hOldFront hEqC
  intro kD
  have hv := congrArg Fin.val (hLab front)
  have hkC : kD.val < (raw (C front)).label.val + 1 := by
    simpa only [hv] using kD.isLt
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
  have hOldK := hOldAt kC
  rw [hPP front kD.val]
  let p := R2Coherence.prefixPos ring (eraseCfgV3 C) front kD.val
  change R2Coherence.freshComponent (eraseCellV3 (D p)) kD.val
  have hOldK' :
      R2Coherence.freshComponent (eraseCellV3 (C p)) kD.val := by
    simpa [p, kC] using hOldK
  unfold R2Coherence.freshComponent at hOldK' ⊢
  change (raw (D p)).label.val = kD.val ∧
    (match (raw (D p)).path with
     | .bot => False
     | .some lab b => lab.val = kD.val ∧
       b.val = (if (raw (D p)).bit then 1 else 0))
  change (raw (C p)).label.val = kD.val ∧
    (match (raw (C p)).path with
     | .bot => False
     | .some lab b => lab.val = kD.val ∧
       b.val = (if (raw (C p)).bit then 1 else 0)) at hOldK'
  rw [hRaw p]
  exact hOldK'

private theorem reachablePhaseFacts_openHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (h : ReachablePhaseFactsV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    ReachablePhaseFactsV31 ring (stepV3 hψ h2 ring C e) := by
  rcases h with ⟨h1,h2c,h3,h4,h5,h6⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    have hc := openHazard_post_nonseek_ctl_eq_oh hψ h2 ring C e i hb hi (by decide)
    apply sweptPrefix_openHazard_step_oh hψ h2 ring C e i hb
    exact h1 i (by simpa [hc] using hi)
  · intro i hi
    have hc := openHazard_post_nonseek_ctl_eq_oh hψ h2 ring C e i hb hi (by decide)
    exact groupOwned_openHazard_step_oh hψ h2 ring C e i hb
      (h2c i (by simpa [hc] using hi))
  · intro i hi
    rcases openHazard_step_ctl_old_or_seek_oh hψ h2 ring C e i hb with hc | hc
    · exact groupOwned_openHazard_step_oh hψ h2 ring C e i hb
        (h3 i (by simpa [hc] using hi))
    · have hx : (R2Coherence.Mark.sealed : R2Coherence.Mark) = .closing := hi.symm.trans hc.1
      cases hx
  · intro i hi
    have hc := openHazard_post_nonseek_ctl_eq_oh hψ h2 ring C e i hb hi (by decide)
    rcases h4 i (by simpa [hc] using hi) with ⟨hm,hg⟩
    exact ⟨by simpa [hc] using hm,
      groupOwned_openHazard_step_oh hψ h2 ring C e i hb hg⟩
  · intro i hi
    have hc := openHazard_post_nonseek_ctl_eq_oh hψ h2 ring C e i hb hi (by decide)
    rcases h5 i (by simpa [hc] using hi) with ⟨hm,hz,hg⟩
    refine ⟨by simpa [hc] using hm, ?_,
      groupOwned_openHazard_step_oh hψ h2 ring C e i hb hg⟩
    simpa [raw_eq_openHazard_oh hψ h2 ring C e i hb] using hz
  · intro i hi
    have hc := openHazard_post_nonseek_ctl_eq_oh hψ h2 ring C e i hb hi (by decide)
    rcases h6 i (by simpa [hc] using hi) with ⟨hm,hf⟩
    exact ⟨by simpa [hc] using hm,
      openROwnerFresh_phys_frame_oh ring i
        (openHazard_step_phys_eq_oh hψ h2 ring C e hb) hf⟩

private theorem footprint_openHazard_to_before_oh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : InOpenRFreshFootprintV31 ring (stepV3 hψ h2 ring C e) owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  rcases h with ⟨j, ko, q, hOwnerD, kD, hPrefixD⟩
  rw [groupPos_openHazard_eq_oh hψ h2 ring C e j ko.val hb] at hOwnerD
  have hGPq := groupPos_openHazard_eq_oh hψ h2 ring C e j q.val hb
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hFrontD : R2Coherence.groupPos ring
      (eraseCfgV3 (stepV3 hψ h2 ring C e)) j q.val = front := by
    simpa [front] using hGPq
  have hkD : kD.val <
      (raw (stepV3 hψ h2 ring C e front)).label.val + 1 := by
    simpa only [hFrontD] using kD.isLt
  have hv := congrArg
    (fun x : BoundedAgentState ψ κ => x.label.val)
    (raw_eq_openHazard_oh hψ h2 ring C e front hb)
  have hkC : kD.val < (raw (C front)).label.val + 1 := by
    simpa only [hv] using hkD
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
  refine ⟨j, ko, q, hOwnerD, kC, ?_⟩
  have hpD : R2Coherence.prefixPos ring
      (eraseCfgV3 (stepV3 hψ h2 ring C e)) front kD.val = p := by
    simpa only [hFrontD] using hPrefixD
  have hPP : R2Coherence.prefixPos ring
      (eraseCfgV3 (stepV3 hψ h2 ring C e)) front kD.val =
      R2Coherence.prefixPos ring (eraseCfgV3 C) front kD.val := by
    unfold R2Coherence.prefixPos
    change R2Coherence.back ring front
        ((raw (stepV3 hψ h2 ring C e front)).label.val - kD.val) =
      R2Coherence.back ring front ((raw (C front)).label.val - kD.val)
    rw [raw_eq_openHazard_oh hψ h2 ring C e front hb]
  exact hPP.symm.trans hpD

private theorem pending_openHazard_to_before_oh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases h with ⟨hs, hSucc, hRoot⟩
  have hc := openHazard_post_nonseek_ctl_eq_oh hψ h2 ring C e
    (ring.rightNeighbor owner) hb hs (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [hc] at hs
    exact hs
  · have hL := congrArg
      (fun x : BoundedAgentState ψ κ => x.label.val)
      (raw_eq_openHazard_oh hψ h2 ring C e owner hb)
    have hR := congrArg
      (fun x : BoundedAgentState ψ κ => x.label.val)
      (raw_eq_openHazard_oh hψ h2 ring C e (ring.rightNeighbor owner) hb)
    unfold successorB at hSucc ⊢
    rw [hL, hR] at hSucc
    exact hSucc
  · have hL := congrArg
      (fun x : BoundedAgentState ψ κ => x.label.val)
      (raw_eq_openHazard_oh hψ h2 ring C e owner hb)
    unfold atRootB at hRoot ⊢
    rw [hL] at hRoot
    exact hRoot

private theorem safeAt_openHazard_step_oh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard)
    (h : SweepOpenRSafeAtV31 ring C owner p) :
    SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) owner p := by
  rcases h with hm | hout
  · exact Or.inl (mainClear_of_phys_eq_oh
      (openHazard_step_phys_eq_oh hψ h2 ring C e hb p) hm)
  · exact Or.inr (fun hf => hout
      (footprint_openHazard_to_before_oh hψ h2 ring C e owner p hb hf))

private theorem scrubLIncoming_openHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (h : ScrubLIncomingOpenRFreshV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    ScrubLIncomingOpenRFreshV31 ring (stepV3 hψ h2 ring C e) := by
  intro owner hs hSucc hRoot
  have hp : PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner :=
    ⟨hs,hSucc,hRoot⟩
  have hpC := pending_openHazard_to_before_oh hψ h2 ring C e owner hb hp
  exact openROwnerFresh_phys_frame_oh ring owner
    (openHazard_step_phys_eq_oh hψ h2 ring C e hb)
    (h owner hpC.1 hpC.2.1 hpC.2.2)

private theorem wide_openHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (h : SweepOpenROverlapClearWideV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    SweepOpenROverlapClearWideV31 ring (stepV3 hψ h2 ring C e) := by
  intro sweep owner hs hp
  have hc := openHazard_post_nonseek_ctl_eq_oh hψ h2 ring C e sweep hb hs (by decide)
  have hsC : (C sweep).ctl.tok = .sweep := by simpa [hc] using hs
  have hpC := pending_openHazard_to_before_oh hψ h2 ring C e owner hb hp
  rcases h sweep owner hsC hpC with ⟨hr,hw⟩
  constructor
  · exact safeAt_openHazard_step_oh hψ h2 ring C e owner
      (ring.rightNeighbor sweep) hb hr
  · intro d
    have hv := congrArg (fun x : BoundedAgentState ψ κ => x.label.val)
      (raw_eq_openHazard_oh hψ h2 ring C e sweep hb)
    have hd : d.val < ψ - (raw (C sweep)).label.val := by
      simpa only [hv] using d.isLt
    let dc : Fin (ψ - (raw (C sweep)).label.val) := ⟨d.val, hd⟩
    exact safeAt_openHazard_step_oh hψ h2 ring C e owner
      (R2Coherence.fwd ring sweep d.val) hb (by simpa [dc] using hw dc)

theorem reachablePhaseFactsPlus3_openHazard_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (_hGeom : ElectionGeometryV31 ring C)
    (_hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard) :
    ReachablePhaseFactsPlus3V31 ring (stepV3 hψ h2 ring C e) := by
  rcases hPlus with ⟨hP3,_hS,_hR1,_hR2⟩
  rcases hP3 with ⟨hP2,hWide⟩
  rcases hP2 with ⟨hP,hPoint⟩
  rcases hP with ⟨hFacts,hIncoming⟩
  have hFactsD := reachablePhaseFacts_openHazard_step hψ h2 ring C e hFacts hb
  have hIncomingD := scrubLIncoming_openHazard_step hψ h2 ring C e hIncoming hb
  have hWideD := wide_openHazard_step hψ h2 ring C e hWide hb
  have hPointD := sweepOpenROverlapClearWide_implies_pointwise
    ring (stepV3 hψ h2 ring C e) hWideD
  exact ⟨⟨⟨hFactsD,hIncomingD⟩,hPointD⟩,hWideD⟩

/-- STOP: the hazardous arm creates a fresh `.seek` at one open endpoint.
The old S field has no premise about that token before this step.  This is the
exact missing piece: only post-state seeks which were not seeks before need a
new prepaid S window. -/
def OpenHazardFreshSeekPrepaidV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e pred owner : Fin n),
    ReachableFromQuarantineV31 hψ h2 ring C →
    ElectionGeometryV31 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openHazard →
    let D := stepV3 hψ h2 ring C e
    (D (ring.rightNeighbor pred)).ctl.tok = .seek →
    (C (ring.rightNeighbor pred)).ctl.tok ≠ .seek →
    PendingOpenROwnerV31 ring D owner →
      (atRootB (D (ring.rightNeighbor pred)) = true →
        SweepOpenRSafeAtV31 ring D owner
            (ring.rightNeighbor (ring.rightNeighbor pred)) ∧
        ∀ d : Fin (ψ - (raw (D (ring.rightNeighbor pred))).label.val),
          SweepOpenRSafeAtV31 ring D owner
            (R2Coherence.fwd ring (ring.rightNeighbor pred) d.val)) ∧
      (atRootB (D (ring.rightNeighbor pred)) = false →
        atRootB (D pred) = true →
          SweepOpenRSafeAtV31 ring D owner (ring.rightNeighbor pred) ∧
          ∀ d : Fin (ψ - (raw (D pred)).label.val),
            SweepOpenRSafeAtV31 ring D owner
              (R2Coherence.fwd ring pred d.val))

/-
STOP at S.  `openHazardStep_reachable_full` is intentionally not asserted:
R1 and strong R2 come after S in the requested clause order.
-/

end R2CoherenceV31ReachableOpenHazard
