import Leader.Wu.Coherence.ReachableCommitGroup


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachableThreeBranches2


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePlus
open R2CoherenceV31ReachablePlus2 R2CoherenceV31ReachablePlus3
open R2CoherenceV31ReachablePlus4 R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableThreeBranches


variable {n ψ κ τ : Nat}


private theorem mod_add_mod_left_tb2 (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm


private theorem mod_add_mod_right_tb2 (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm


private theorem prefixPos_eq_groupPos_tb2
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) (k : Nat)
    (hk : k ≤ (R2Coherence.raw (C i)).label.val) :
    R2Coherence.prefixPos ring C i k = R2Coherence.groupPos ring C i k := by
  let L := (R2Coherence.raw (C i)).label.val
  let A := i.val + n
  let a := (L - k) % n
  let b := k % n
  have hkL : k ≤ L := by simpa [L] using hk
  have hn : 0 < n := ring.hn
  have ha : a < n := by exact Nat.mod_lt _ hn
  have hb : b < n := by exact Nat.mod_lt _ hn
  have hA : n ≤ A := by dsimp [A]; omega
  have hLmod : L % n = (a + b) % n := by
    calc
      L % n = (L - k + k) % n := by rw [Nat.sub_add_cancel hkL]
      _ = ((L - k) % n + k % n) % n := Nat.add_mod _ _ _
      _ = (a + b) % n := rfl
  apply Fin.ext
  change (A - a) % n = (((A - (L % n)) % n + k) % n)
  symm
  by_cases hsum : a + b < n
  · have hLm : L % n = a + b := by
      calc
        L % n = (a + b) % n := hLmod
        _ = a + b := Nat.mod_eq_of_lt hsum
    calc
      (((A - (L % n)) % n + k) % n) =
          (A - (L % n) + k) % n :=
        mod_add_mod_left_tb2 (A - (L % n)) k n
      _ = (A - (L % n) + b) % n := by
        simpa [b] using (mod_add_mod_right_tb2 (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hLm]
        have hnum : A - (a + b) + b = A - a := by omega
        rw [hnum]
  · have hsumGe : n ≤ a + b := by omega
    have hsumSub : a + b - n < n := by omega
    have hLm : L % n = a + b - n := by
      calc
        L % n = (a + b) % n := hLmod
        _ = (a + b - n) % n := Nat.mod_eq_sub_mod hsumGe
        _ = a + b - n := Nat.mod_eq_of_lt hsumSub
    calc
      (((A - (L % n)) % n + k) % n) =
          (A - (L % n) + k) % n :=
        mod_add_mod_left_tb2 (A - (L % n)) k n
      _ = (A - (L % n) + b) % n := by
        simpa [b] using (mod_add_mod_right_tb2 (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hLm]
        have hnum : A - (a + b - n) + b = n + (A - a) := by omega
        rw [hnum, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]


private theorem groupPos_label_self_tb2
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    R2Coherence.groupPos ring (eraseCfgV3 C) i (raw (C i)).label.val = i := by
  change R2Coherence.groupPos ring (eraseCfgV3 C) i
      (R2Coherence.raw ((eraseCfgV3 C) i)).label.val = i
  rw [← prefixPos_eq_groupPos_tb2 ring (eraseCfgV3 C) i
    (R2Coherence.raw ((eraseCfgV3 C) i)).label.val (Nat.le_refl _)]
  apply Fin.ext
  simp only [R2Coherence.prefixPos, R2Coherence.back,
    Nat.sub_self, Nat.zero_mod, Nat.sub_zero]
  rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_self,
    Nat.add_zero, Nat.mod_eq_of_lt i.isLt]



private theorem branch_commit_tb2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .commit) :
    l.ctl.tok ≠ .sweep ∧ r.ctl.tok = .commit := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind


private theorem commit_step_left_tb2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    stepV3 hψ h2 ring C e e =
      (commitStageV3 (C e) (C (ring.rightNeighbor e))).1 := by
  rcases branch_commit_tb2 hψ h2 (C e) (C (ring.rightNeighbor e)) hb with ⟨hs, hc⟩
  have hr : rowV3 hψ (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e)) =
      commitStageV3 (C e) (C (ring.rightNeighbor e)) := by
    simp [rowV3, hs, hc]
  simp [stepV3, protocolV3, PopulationProtocol.step, hr]


private theorem commit_step_right_tb2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (hne : ring.rightNeighbor e ≠ e) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      setControl (clearMain (C (ring.rightNeighbor e))) .sealed .none := by
  rcases branch_commit_tb2 hψ h2 (C e) (C (ring.rightNeighbor e)) hb with ⟨hs, hc⟩
  have hr : rowV3 hψ (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e)) =
      commitStageV3 (C e) (C (ring.rightNeighbor e)) := by
    simp [rowV3, hs, hc]
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hr, hne, commitStageV3]


private theorem commit_step_eq_of_post_token_tb2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    {t : TokenV3} (hn : t ≠ .none) (hc : t ≠ .commit)
    (ht : (stepV3 hψ h2 ring C e i).ctl.tok = t) :
    stepV3 hψ h2 ring C e i = C i := by
  by_cases hie : i = e
  · subst i
    rw [commit_step_left_tb2 hψ h2 ring C e hb] at ht ⊢
    cases hr : atRootB (C (ring.rightNeighbor e)) with
    | true =>
        simp [commitStageV3, hr]
    | false =>
        cases hl : atRootB (C e) with
        | true =>
            exfalso
            apply hn
            simpa [commitStageV3, hr, hl, setControl] using ht.symm
        | false =>
            exfalso
            apply hc
            simpa [commitStageV3, hr, hl, setControl] using ht.symm
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      rw [commit_step_right_tb2 hψ h2 ring C e hb hie] at ht
      exfalso
      apply hn
      simpa [setControl] using ht.symm
    · exact stepV3_other hψ h2 ring C e i hie hir


private theorem commit_served_mainClear_tb2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    MainClearV3 (C (ring.rightNeighbor e)) ∧
      (atRootB (C (ring.rightNeighbor e)) = false → MainClearV3 (C e)) := by
  have hFacts : ReachablePhaseFactsV31 ring C := hPlus.1.1.1.1
  have hP2 := hFacts.2.1
  have hc := branch_commit_tb2 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  have hGroupR := hP2 (ring.rightNeighbor e) hc.2
  have hAtR := hGroupR (raw (C (ring.rightNeighbor e))).label
  dsimp only at hAtR
  rw [groupPos_label_self_tb2 ring C (ring.rightNeighbor e)] at hAtR
  refine ⟨hAtR.1, ?_⟩
  intro hr0
  have hGeom : ElectionGeometryV31 ring C :=
    R2CoherenceV31ReachableSweep.electionGeometry_of_quarantineTrace
      hψ h2 ring C hTrace
  have hEdge := hGeom e
  have hs : successorB (C e) (C (ring.rightNeighbor e)) = true := by
    unfold passiveEdgeOKV3 at hEdge
    simp [hr0] at hEdge
    exact hEdge
  have hStart :
      R2Coherence.groupStart ring (eraseCfgV3 C) (ring.rightNeighbor e) =
        R2Coherence.groupStart ring (eraseCfgV3 C) e := by
    unfold R2Coherence.groupStart
    change R2Coherence.back ring (ring.rightNeighbor e)
        (raw (C (ring.rightNeighbor e))).label.val =
      R2Coherence.back ring e (raw (C e)).label.val
    have hv : (raw (C (ring.rightNeighbor e))).label.val =
        (raw (C e)).label.val + 1 := by simpa [successorB] using hs
    rw [hv]
    exact R2CoherenceV31ReachableOpenNoHazard.back_rightNeighbor_succ_reach
      ring e (raw (C e)).label.val
  have hAtE := hGroupR (raw (C e)).label
  dsimp only at hAtE
  have hp : R2Coherence.groupPos ring (eraseCfgV3 C)
      (ring.rightNeighbor e) (raw (C e)).label.val = e := by
    have hself := groupPos_label_self_tb2 ring C e
    unfold R2Coherence.groupPos at hself ⊢
    rw [hStart]
    exact hself
  rw [hp] at hAtE
  exact hAtE.1


private theorem commit_same_or_mainClear_tb2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    stepV3 hψ h2 ring C e p = C p ∨ MainClearV3 (C p) := by
  have hClear := commit_served_mainClear_tb2 hψ h2 ring C e hTrace hPlus hb
  by_cases hpe : p = e
  · subst p
    cases hr : atRootB (C (ring.rightNeighbor e)) with
    | false => exact Or.inr (hClear.2 hr)
    | true =>
        left
        rw [commit_step_left_tb2 hψ h2 ring C e hb]
        simp [commitStageV3, hr]
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      exact Or.inr hClear.1
    · left
      exact stepV3_other hψ h2 ring C e p hpe hpr


private theorem commit_post_equal_same_tb2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (heq : (raw (stepV3 hψ h2 ring C e p)).state = .equal) :
    stepV3 hψ h2 ring C e p = C p := by
  by_cases hpe : p = e
  · subst p
    cases hr : atRootB (C (ring.rightNeighbor e)) with
    | true =>
        rw [commit_step_left_tb2 hψ h2 ring C e hb]
        simp [commitStageV3, hr]
    | false =>
        exfalso
        rw [commit_step_left_tb2 hψ h2 ring C e hb] at heq
        cases hl : atRootB (C e) <;>
          simp [commitStageV3, hr, hl, setControl, clearMain, raw] at heq
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      exfalso
      rw [commit_step_right_tb2 hψ h2 ring C e hb hpe] at heq
      simp [setControl, clearMain, raw] at heq
    · exact stepV3_other hψ h2 ring C e p hpe hpr



private theorem groupPos_eq_of_labels_tb2
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring
      (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [hLab i]


private theorem prefixPos_eq_of_labels_tb2
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [hLab i]


private theorem freshComponent_false_of_mainClear_tb2
    (u : Cell ψ κ τ) (k : Nat) (hm : MainClearV3 u)
    (hf : R2Coherence.freshComponent (eraseCellV3 u) k) : False := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at hm
  unfold R2Coherence.freshComponent at hf
  change (raw u).label.val = k ∧
    (match (raw u).path with
     | .bot => False
     | .some lab b => lab.val = k ∧
         b.val = (if (raw u).bit then 1 else 0)) at hf
  have hPath : (raw u).path = .bot := hm.2.1
  rw [hPath] at hf
  exact hf.2


private theorem ownerFresh_deletion_tb2
    (ring : DirectedRing n) {C D : FC n ψ κ τ} (owner : Fin n)
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (hFront : ∀ p : Fin n,
      (raw (D p)).state = .equal → D p = C p)
    (hCell : ∀ p : Fin n, D p = C p ∨ MainClearV3 (C p))
    (hFresh : OpenROwnerFreshV3 ring C owner) :
    OpenROwnerFreshV3 ring D owner := by
  unfold OpenROwnerFreshV3 at hFresh ⊢
  intro j ko hHitD
  have hGPko := groupPos_eq_of_labels_tb2 ring hLab j ko.val
  rw [hGPko] at hHitD
  have hOldGroup := hFresh j ko hHitD
  unfold GroupIntrinsicFreshV3 at hOldGroup ⊢
  intro q
  have hGPq := groupPos_eq_of_labels_tb2 ring hLab j q.val
  rw [hGPq]
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  change IntrinsicFreshAtV3 ring D front
  have hOldFront : IntrinsicFreshAtV3 ring C front := by
    simpa [front] using hOldGroup q
  unfold IntrinsicFreshAtV3 at hOldFront ⊢
  intro hEqD
  have hSameFront := hFront front hEqD
  have hEqC : (raw (C front)).state = .equal := by
    simpa [hSameFront] using hEqD
  have hOldAt := hOldFront hEqC
  intro kD
  have hLabelVal : (raw (D front)).label.val =
      (raw (C front)).label.val :=
    congrArg (fun x : Fin ψ => x.val) (hLab front)
  have hkC : kD.val < (raw (C front)).label.val + 1 := by
    let m : Nat := kD.val
    have hm : m < (raw (D front)).label.val + 1 := kD.isLt
    simpa only [hLabelVal] using hm
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
  have hOldK := hOldAt kC
  have hPP := prefixPos_eq_of_labels_tb2 ring hLab front kD.val
  rw [hPP]
  let p := R2Coherence.prefixPos ring (eraseCfgV3 C) front kD.val
  change R2Coherence.freshComponent (eraseCellV3 (D p)) kD.val
  have hOldK' : R2Coherence.freshComponent (eraseCellV3 (C p)) kD.val := by
    simpa [p, kC] using hOldK
  rcases hCell p with hSame | hClear
  · simpa [hSame, p] using hOldK'
  · exact (freshComponent_false_of_mainClear_tb2
      (C p) kD.val hClear hOldK').elim


private theorem ownerFresh_commit_tb2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (hFresh : OpenROwnerFreshV3 ring C owner) :
    OpenROwnerFreshV3 ring (stepV3 hψ h2 ring C e) owner := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label := by
    intro p
    simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  have hFront : ∀ p : Fin n,
      (raw (D p)).state = .equal → D p = C p := by
    intro p hp
    change (raw (stepV3 hψ h2 ring C e p)).state = .equal at hp
    change stepV3 hψ h2 ring C e p = C p
    exact commit_post_equal_same_tb2 hψ h2 ring C e p hb hp
  have hCell : ∀ p : Fin n, D p = C p ∨ MainClearV3 (C p) := by
    intro p
    change stepV3 hψ h2 ring C e p = C p ∨ MainClearV3 (C p)
    exact commit_same_or_mainClear_tb2 hψ h2 ring C e p hTrace hPlus hb
  exact ownerFresh_deletion_tb2 ring owner hLab hFront hCell hFresh


/-- Commit P6: the commit group debt makes every actually-cleared served cell
main-clear before deletion, so an old intrinsic-fresh component can never sit
on a changed cell. -/
theorem commitP6OpenRFreshPreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    CommitP6OpenRFreshPreservationV31 (κ := κ) (τ := τ) hψ h2 ring := by
  unfold CommitP6OpenRFreshPreservationV31
  intro C e hTrace hPlus hb owner hOpenD
  have hFacts : ReachablePhaseFactsV31 ring C := hPlus.1.1.1.1
  have hP6 := hFacts.2.2.2.2.2
  have hSame := commit_step_eq_of_post_token_tb2 hψ h2 ring C e owner hb
    (t := .openR) (by decide) (by decide) hOpenD
  have hOpenC := hOpenD
  rw [hSame] at hOpenC
  rcases hP6 owner hOpenC with ⟨hm, hFresh⟩
  constructor
  · rw [hSame]
    exact hm
  · exact ownerFresh_commit_tb2
      hψ h2 ring C e owner hTrace hPlus hb hFresh


end R2CoherenceV31ReachableThreeBranches2
