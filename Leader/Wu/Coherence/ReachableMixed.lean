import Leader.Wu.Coherence.ReachableStrongOwnership

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableMixed

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear R2CoherenceV31BirthQuarantine
open R2CoherenceV31QuarantineReach R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4

variable {n ψ κ τ : Nat}

private theorem branch_mixed_priority_mix
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .mixed) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok ≠ .scrubL ∧ l.ctl.tok ≠ .openR := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowV3_mixed_shape
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hGood : passiveEdgeOKV3 l r = true)
    (hb : branchAtV3 hψ h2 l r = .mixed) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = (l, startClosing r) ∨
      rowV3 hψ (by decide : 0 < 2) h2 l r = (l, r) := by
  rcases branch_mixed_priority_mix hψ h2 l r hb with
    ⟨hSeek, hSweep, hCommit, hRelease, hScrub, hOpenR⟩
  by_cases hNone : l.ctl.tok = .none ∧ r.ctl.tok = .none
  · have hSeal : ¬ (l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed) := by
      intro hs
      have hx := hb
      simp [branchAtV3, hSeek, hSweep, hCommit, hRelease,
        hScrub, hOpenR, hNone, hs] at hx
    have hOpen : ¬ (l.ctl.mark = .open ∧ r.ctl.mark = .open) := by
      intro ho
      have hx := hb
      unfold branchAtV3 at hx
      simp [hSeek, hSweep, hCommit, hRelease, hScrub,
        hOpenR, hNone, hSeal, ho] at hx
      split at hx <;> simp_all
    left
    simpa [rowV3, ordinaryStageV3, hSeek, hSweep, hCommit,
      hRelease, hScrub, hOpenR, hNone, hSeal, hOpen] using
      (normalizePassiveV3_good_edge l r hGood)
  · right
    simp [rowV3, ordinaryStageV3, hSeek, hSweep, hCommit,
      hRelease, hScrub, hOpenR, hNone]

private theorem mixed_step_frame
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .mixed) :
    ∀ p : Fin n,
      (stepV3 hψ h2 ring C e p).phys = (C p).phys ∧
      ((stepV3 hψ h2 ring C e p).ctl = (C p).ctl ∨
       (stepV3 hψ h2 ring C e p).ctl = ⟨.closing, .seek⟩) := by
  intro p
  rcases rowV3_mixed_shape hψ h2 (C e) (C (ring.rightNeighbor e))
      (hGeom e) hb with hr | hr
  · by_cases hpe : p = e
    · subst p
      simp [stepV3, protocolV3, PopulationProtocol.step, hr]
    · by_cases hpr : p = ring.rightNeighbor e
      · subst p
        simp [stepV3, protocolV3, PopulationProtocol.step, hr, hpe,
          startClosing, setControl]
      · rw [stepV3_other hψ h2 ring C e p hpe hpr]
        exact ⟨rfl, Or.inl rfl⟩
  · by_cases hpe : p = e
    · subst p
      simp [stepV3, protocolV3, PopulationProtocol.step, hr]
    · by_cases hpr : p = ring.rightNeighbor e
      · subst p
        simp [stepV3, protocolV3, PopulationProtocol.step, hr, hpe]
      · rw [stepV3_other hψ h2 ring C e p hpe hpr]
        exact ⟨rfl, Or.inl rfl⟩

private theorem mixed_raw_eq
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .mixed) :
    raw (stepV3 hψ h2 ring C e p) = raw (C p) := by
  exact congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core)
    (mixed_step_frame hψ h2 ring C e hGeom hb p).1

private theorem mixed_ctl_eq_of_not_seek
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .mixed)
    {t : TokenV3} (ht : (stepV3 hψ h2 ring C e p).ctl.tok = t)
    (hne : t ≠ .seek) :
    (stepV3 hψ h2 ring C e p).ctl = (C p).ctl := by
  rcases (mixed_step_frame hψ h2 ring C e hGeom hb p).2 with h | h
  · exact h
  · rw [h] at ht
    exact (hne ht.symm).elim

private theorem mixed_ctl_eq_of_sealed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .mixed)
    (hm : (stepV3 hψ h2 ring C e p).ctl.mark = .sealed) :
    (stepV3 hψ h2 ring C e p).ctl = (C p).ctl := by
  rcases (mixed_step_frame hψ h2 ring C e hGeom hb p).2 with h | h
  · exact h
  · rw [h] at hm
    simp at hm


private theorem groupPos_eq_mix
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

private theorem prefixPos_eq_mix
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [hLab i]

private theorem mainClear_phys_mix
    {u v : Cell ψ κ τ} (hp : u.phys = v.phys)
    (hm : MainClearV3 v) : MainClearV3 u := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at hm ⊢
  simpa [eraseCellV3, R2Coherence.raw, hp] using hm

private theorem ownedClear_mixed
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .mixed)
    (hOld : MainClearV3 (C p) ∧ PhaseOwnedV31 (C p)) :
    MainClearV3 (stepV3 hψ h2 ring C e p) ∧
      PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
  constructor
  · exact mainClear_phys_mix
      (mixed_step_frame hψ h2 ring C e hGeom hb p).1 hOld.1
  · rcases (mixed_step_frame hψ h2 ring C e hGeom hb p).2 with h | h
    · unfold PhaseOwnedV31 at hOld ⊢
      rw [h]
      exact hOld.2
    · unfold PhaseOwnedV31
      rw [h]
      simp

private theorem swept_transport_mix
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (hMono : ∀ p, MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
      MainClearV3 (D p) ∧ PhaseOwnedV31 (D p))
    (i : Fin n) (hOld : SweptPrefixOwnedClearV31 ring C i) :
    SweptPrefixOwnedClearV31 ring D i := by
  unfold SweptPrefixOwnedClearV31 at hOld ⊢
  intro kD
  have hv := congrArg Fin.val (hLab i)
  have hkC : kD.val < (raw (C i)).label.val := by
    rw [← hv]
    exact kD.isLt
  let kC : Fin (raw (C i)).label.val := ⟨kD.val, hkC⟩
  rw [groupPos_eq_mix ring hLab i kD.val]
  exact hMono _ (by simpa [kC] using hOld kC)

private theorem group_transport_mix
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (hMono : ∀ p, MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
      MainClearV3 (D p) ∧ PhaseOwnedV31 (D p))
    (i : Fin n) (hOld : GroupOwnedClearV31 ring C i) :
    GroupOwnedClearV31 ring D i := by
  unfold GroupOwnedClearV31 at hOld ⊢
  intro k
  rw [groupPos_eq_mix ring hLab i k.val]
  exact hMono _ (hOld k)

private theorem ownerFresh_phys_mix
    (ring : DirectedRing n) {C D : FC n ψ κ τ} (owner : Fin n)
    (hPhys : ∀ p, (D p).phys = (C p).phys)
    (hFresh : OpenROwnerFreshV3 ring C owner) :
    OpenROwnerFreshV3 ring D owner := by
  have hRaw : ∀ p, raw (D p) = raw (C p) := fun p =>
    congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core) (hPhys p)
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label := fun p =>
    congrArg (fun x : BoundedAgentState ψ κ => x.label) (hRaw p)
  unfold OpenROwnerFreshV3 at hFresh ⊢
  intro j ko hHitD
  rw [groupPos_eq_mix ring hLab j ko.val] at hHitD
  have hOldGroup := hFresh j ko hHitD
  unfold GroupIntrinsicFreshV3 at hOldGroup ⊢
  intro q
  rw [groupPos_eq_mix ring hLab j q.val]
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hOldFront : IntrinsicFreshAtV3 ring C front := by
    simpa [front] using hOldGroup q
  unfold IntrinsicFreshAtV3 at hOldFront ⊢
  intro hEqD
  have hEqD' : (raw (D front)).state = .equal := by
    simpa only [front] using hEqD
  have hEqC : (raw (C front)).state = .equal := by
    rw [hRaw front] at hEqD'
    exact hEqD'
  intro kD
  have hv := congrArg Fin.val (hLab front)
  have hkC : kD.val < (raw (C front)).label.val + 1 := by
    rw [← hv]
    exact kD.isLt
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
  have hOldK := hOldFront hEqC kC
  rw [prefixPos_eq_mix ring hLab front kD.val]
  let p := R2Coherence.prefixPos ring (eraseCfgV3 C) front kD.val
  change R2Coherence.freshComponent (eraseCellV3 (D p)) kD.val
  have hOldK' : R2Coherence.freshComponent (eraseCellV3 (C p)) kD.val := by
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

private theorem footprint_after_mix_to_before
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n)
    (hFoot : InOpenRFreshFootprintV31 ring D owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  rcases hFoot with ⟨j, ko, q, hOwnerD, kD, hPrefixD⟩
  rw [groupPos_eq_mix ring hLab j ko.val] at hOwnerD
  have hGPq := groupPos_eq_mix ring hLab j q.val
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hFrontD : R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = front := by
    simpa [front] using hGPq
  have hkD : kD.val < (raw (D front)).label.val + 1 := by
    simpa only [hFrontD] using kD.isLt
  have hv : (raw (D front)).label.val = (raw (C front)).label.val :=
    congrArg Fin.val (hLab front)
  have hkC : kD.val < (raw (C front)).label.val + 1 := by
    rw [← hv]
    exact hkD
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
  refine ⟨j, ko, q, hOwnerD, kC, ?_⟩
  have hpD : R2Coherence.prefixPos ring (eraseCfgV3 D) front kD.val = p := by
    simpa only [hFrontD] using hPrefixD
  exact (prefixPos_eq_mix ring hLab front kD.val).symm.trans hpD


private theorem safeAt_transport_mix
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hPhys : ∀ p, (D p).phys = (C p).phys)
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n) (hOld : SweepOpenRSafeAtV31 ring C owner p) :
    SweepOpenRSafeAtV31 ring D owner p := by
  unfold SweepOpenRSafeAtV31 at hOld ⊢
  rcases hOld with hm | hout
  · exact Or.inl (mainClear_phys_mix (hPhys p) hm)
  · right
    intro hFoot
    exact hout (footprint_after_mix_to_before ring hLab owner p hFoot)

private theorem pending_before_mix
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .mixed)
    (hPost : PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) owner) :
    PendingOpenROwnerV31 ring C owner := by
  rcases hPost with ⟨hScrub, hSucc, hRoot⟩
  have hCtl := mixed_ctl_eq_of_not_seek hψ h2 ring C e
    (ring.rightNeighbor owner) hGeom hb hScrub (by decide)
  have hLab : ∀ p, (raw (stepV3 hψ h2 ring C e p)).label =
      (raw (C p)).label := fun p =>
    congrArg (fun x : BoundedAgentState ψ κ => x.label)
      (mixed_raw_eq hψ h2 ring C e p hGeom hb)
  refine ⟨?_, ?_, ?_⟩
  · rw [hCtl] at hScrub
    exact hScrub
  · unfold successorB at hSucc ⊢
    simpa [hLab owner, hLab (ring.rightNeighbor owner)] using hSucc
  · unfold atRootB at hRoot ⊢
    simpa [hLab owner] using hRoot

/-- All pre-S clauses transport through MIXED: the only possible new token is
`.seek`, while all physical fields and labels are framed. -/
theorem reachablePhaseFactsPlus3_mixed_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (_hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .mixed) :
    ReachablePhaseFactsPlus3V31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hPhys : ∀ p, (D p).phys = (C p).phys := fun p =>
    mixed_step_frame hψ h2 ring C e hGeom hb p |>.1
  have hRaw : ∀ p, raw (D p) = raw (C p) := fun p =>
    congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core) (hPhys p)
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label := fun p =>
    congrArg (fun x : BoundedAgentState ψ κ => x.label) (hRaw p)
  have hMono : ∀ p, MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
      MainClearV3 (D p) ∧ PhaseOwnedV31 (D p) := by
    intro p hp
    simpa [D] using ownedClear_mixed hψ h2 ring C e p hGeom hb hp
  rcases hPlus.1 with ⟨⟨⟨hFacts, hIncoming⟩, _hPoint⟩, hWide⟩
  rcases hFacts with ⟨hSweep, hCommit, hSealed, hRelease, hScrub, hOpenR⟩
  have hFactsD : ReachablePhaseFactsV31 ring D := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hc := mixed_ctl_eq_of_not_seek hψ h2 ring C e i hGeom hb hi (by decide)
      have hiC : (C i).ctl.tok = .sweep := by rw [hc] at hi; exact hi
      exact swept_transport_mix ring hLab hMono i (hSweep i hiC)
    · intro i hi
      have hc := mixed_ctl_eq_of_not_seek hψ h2 ring C e i hGeom hb hi (by decide)
      have hiC : (C i).ctl.tok = .commit := by rw [hc] at hi; exact hi
      exact group_transport_mix ring hLab hMono i (hCommit i hiC)
    · intro i hi
      have hc := mixed_ctl_eq_of_sealed hψ h2 ring C e i hGeom hb hi
      have hiC : (C i).ctl.mark = .sealed := by rw [hc] at hi; exact hi
      exact group_transport_mix ring hLab hMono i (hSealed i hiC)
    · intro i hi
      have hc := mixed_ctl_eq_of_not_seek hψ h2 ring C e i hGeom hb hi (by decide)
      have hiC : (C i).ctl.tok = .release := by rw [hc] at hi; exact hi
      rcases hRelease i hiC with ⟨hm, hg⟩
      exact ⟨by rw [hc]; exact hm, group_transport_mix ring hLab hMono i hg⟩
    · intro i hi
      have hc := mixed_ctl_eq_of_not_seek hψ h2 ring C e i hGeom hb hi (by decide)
      have hiC : (C i).ctl.tok = .scrubL := by rw [hc] at hi; exact hi
      rcases hScrub i hiC with ⟨hm, hz, hg⟩
      refine ⟨by rw [hc]; exact hm, ?_, group_transport_mix ring hLab hMono i hg⟩
      intro hzD
      apply hz
      exact (congrArg Fin.val (hLab i)).symm.trans hzD
    · intro i hi
      have hc := mixed_ctl_eq_of_not_seek hψ h2 ring C e i hGeom hb hi (by decide)
      have hiC : (C i).ctl.tok = .openR := by rw [hc] at hi; exact hi
      rcases hOpenR i hiC with ⟨hm, hf⟩
      exact ⟨by rw [hc]; exact hm, ownerFresh_phys_mix ring i hPhys hf⟩
  have hIncomingD : ScrubLIncomingOpenRFreshV31 ring D := by
    intro owner hScrubD hSuccD hRootD
    have hp := pending_before_mix hψ h2 ring C e owner hGeom hb
      ⟨hScrubD, hSuccD, hRootD⟩
    exact ownerFresh_phys_mix ring owner hPhys
      (hIncoming owner hp.1 hp.2.1 hp.2.2)
  have hWideD : SweepOpenROverlapClearWideV31 ring D := by
    intro sweep owner hSweepD hPendingD
    have hc := mixed_ctl_eq_of_not_seek hψ h2 ring C e sweep hGeom hb
      hSweepD (by decide)
    have hSweepC : (C sweep).ctl.tok = .sweep := by rw [hc] at hSweepD; exact hSweepD
    have hPendingC := pending_before_mix hψ h2 ring C e owner hGeom hb hPendingD
    have hOld := hWide sweep owner hSweepC hPendingC
    constructor
    · exact safeAt_transport_mix ring hPhys hLab owner (ring.rightNeighbor sweep) hOld.1
    · intro dD
      have hv := congrArg Fin.val (hLab sweep)
      have hdC : dD.val < ψ - (raw (C sweep)).label.val := by
        simpa only [hv] using dD.isLt
      let dC : Fin (ψ - (raw (C sweep)).label.val) := ⟨dD.val, hdC⟩
      exact safeAt_transport_mix ring hPhys hLab owner
        (R2Coherence.fwd ring sweep dD.val) (by simpa [dC] using hOld.2 dC)
  have hPointD := sweepOpenROverlapClearWide_implies_pointwise ring D hWideD
  exact ⟨⟨⟨hFactsD, hIncomingD⟩, hPointD⟩, hWideD⟩

/-- First unclosed conjunct after Plus3. Tokenless admitted MIXED creates a
fresh responder `.seek`; the pre-state S premise for that site was false, and
neither R1 nor strong R2 supplies the newly activated future-sweep window. -/
def MixedSeekIncomingSweepOpenROverlapClearWidePreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .mixed →
      SeekIncomingSweepOpenROverlapClearWideV31 ring
        (stepV3 hψ h2 ring C e)

/- STOP at S. `mixedStep_reachable_full` is intentionally not asserted. -/

end R2CoherenceV31ReachableMixed
