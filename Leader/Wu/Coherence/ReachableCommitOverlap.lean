import Leader.Wu.Coherence.ReachableCommitHandoff
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
namespace R2CoherenceV31ReachableThreeBranches4
open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard3 R2CoherenceV31ReachableOpenNoHazard4
open R2CoherenceV31ReachableFourBranches
open R2CoherenceV31ReachableThreeBranches R2CoherenceV31ReachableThreeBranches2
open R2CoherenceV31ReachableThreeBranches3
variable {n ψ κ τ : Nat}


private theorem bc (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .commit) :
    l.ctl.tok ≠ .sweep ∧ r.ctl.tok = .commit := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind


private theorem rowC (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .commit) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = commitStageV3 l r := by
  rcases bc hψ h2 l r hb with ⟨hs, hc⟩
  simp [rowV3, hs, hc]


private theorem leftC (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    stepV3 hψ h2 ring C e e = (commitStageV3 (C e) (C (ring.rightNeighbor e))).1 := by
  have h := rowC hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, h]


private theorem rightC (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (hne : ring.rightNeighbor e ≠ e) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      setControl (clearMain (C (ring.rightNeighbor e))) .sealed .none := by
  have h := rowC hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, h, hne, commitStageV3]


private theorem oldTok (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    {t : TokenV3} (hn : t ≠ .none) (hc : t ≠ .commit)
    (ht : (stepV3 hψ h2 ring C e i).ctl.tok = t) :
    stepV3 hψ h2 ring C e i = C i := by
  by_cases hie : i = e
  · subst i; rw [leftC hψ h2 ring C e hb] at ht ⊢
    cases hr : atRootB (C (ring.rightNeighbor e)) with
    | true => simp [commitStageV3, hr]
    | false =>
      cases hl : atRootB (C e) with
      | true =>
        exfalso; apply hn
        simpa [commitStageV3, hr, hl, setControl] using ht.symm
      | false =>
        exfalso; apply hc
        simpa [commitStageV3, hr, hl, setControl] using ht.symm
  · by_cases hir : i = ring.rightNeighbor e
    · subst i; rw [rightC hψ h2 ring C e hb hie] at ht
      exfalso; apply hn; simpa [setControl] using ht.symm
    · exact stepV3_other hψ h2 ring C e i hie hir


private theorem clr (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    MainClearV3 (setControl (clearMain u) m t) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [eraseCellV3, setControl, clearMain, R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier, R2Coherence.raw]


private theorem frame (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    stepV3 hψ h2 ring C e p = C p ∨
      (MainClearV3 (stepV3 hψ h2 ring C e p) ∧ PhaseOwnedV31 (stepV3 hψ h2 ring C e p)) := by
  by_cases hp : p = e
  · subst p; rw [leftC hψ h2 ring C e hb]
    unfold commitStageV3; dsimp only; split
    · exact Or.inl rfl
    · split
      · exact Or.inr ⟨clr _ .sealed .none, by simp [PhaseOwnedV31, setControl]⟩
      · exact Or.inr ⟨clr _ .closing .commit, by simp [PhaseOwnedV31, setControl]⟩
  · by_cases hr : p = ring.rightNeighbor e
    · subst p; rw [rightC hψ h2 ring C e hb hp]
      exact Or.inr ⟨clr _ .sealed .none, by simp [PhaseOwnedV31, setControl]⟩
    · exact Or.inl (stepV3_other hψ h2 ring C e p hp hr)


private theorem mc (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (h : MainClearV3 (C p)) : MainClearV3 (stepV3 hψ h2 ring C e p) := by
  rcases frame hψ h2 ring C e p hb with hs | hc
  · simpa [hs] using h
  · exact hc.1


private theorem po (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (h : PhaseOwnedV31 (C p)) : PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
  rcases frame hψ h2 ring C e p hb with hs | hc
  · simpa [hs] using h
  · exact hc.2

private theorem gp (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label) (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k = R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [h i]


private theorem pp (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label) (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k = R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [h i]


private theorem foot (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label) (o p : Fin n)
    (h : InOpenRFreshFootprintV31 ring D o p) : InOpenRFreshFootprintV31 ring C o p := by
  rcases h with ⟨j, ko, q, ho, kD, hp⟩
  rw [gp ring hL j ko.val] at ho
  let f := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hf : R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = f := by
    simpa [f] using gp ring hL j q.val
  have hv : (raw (D (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val))).label.val =
      (raw (C f)).label.val := by rw [hf]; exact congrArg Fin.val (hL f)
  have hk : kD.val < (raw (C f)).label.val + 1 := by simpa only [hv] using kD.isLt
  let kC : Fin ((raw (C f)).label.val + 1) := ⟨kD.val, hk⟩
  refine ⟨j, ko, q, ho, kC, ?_⟩
  have h0 : R2Coherence.prefixPos ring (eraseCfgV3 D) f kD.val = p := by
    simpa only [hf] using hp
  simpa [kC] using (pp ring hL f kD.val).symm.trans h0


private theorem sfoot (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label) (o p : Fin n)
    (h : InSweptOwnedFootprintV31 ring D o p) : InSweptOwnedFootprintV31 ring C o p := by
  rcases h with ⟨kD, hp⟩
  have hv := congrArg Fin.val (hL o)
  have hk : kD.val < (raw (C o)).label.val := by simpa only [hv] using kD.isLt
  let kC : Fin (raw (C o)).label.val := ⟨kD.val, hk⟩
  refine ⟨kC, ?_⟩
  simpa [kC] using (gp ring hL o kD.val).symm.trans hp


private theorem gfoot (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label) (o p : Fin n)
    (h : InGroupOwnedFootprintV31 ring D o p) : InGroupOwnedFootprintV31 ring C o p := by
  rcases h with ⟨k, hp⟩
  exact ⟨k, (gp ring hL o k.val).symm.trans hp⟩


private theorem readBack (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label) (s p : Fin n)
    (h : InSweepWideReadV31 ring D s p) : InSweepWideReadV31 ring C s p := by
  rcases h with h | ⟨d, hp⟩
  · exact Or.inl h
  · right
    have hv := congrArg Fin.val (hL s)
    have hd : d.val < ψ - (raw (C s)).label.val := by simpa only [hv] using d.isLt
    exact ⟨⟨d.val, hd⟩, hp⟩


private theorem rootEq {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label) (p : Fin n) :
    atRootB (D p) = atRootB (C p) := by unfold atRootB; rw [hL p]


private theorem termEq {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label) (p : Fin n) :
    atTerminalB (D p) = atTerminalB (C p) := by unfold atTerminalB; rw [hL p]


private theorem succEq (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label) (p : Fin n) :
    successorB (D p) (D (ring.rightNeighbor p)) = successorB (C p) (C (ring.rightNeighbor p)) := by
  unfold successorB; rw [hL p, hL (ring.rightNeighbor p)]


private theorem pending (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e o : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (h : PendingOpenROwnerV31 ring (stepV3 hψ h2 ring C e) o) : PendingOpenROwnerV31 ring C o := by
  rcases h with ⟨hs, hu, hr⟩
  have hL := stepV3_labels_eq_or_held hψ h2 ring C e
  have heq := oldTok hψ h2 ring C e (ring.rightNeighbor o) hb
    (t := .scrubL) (by decide) (by decide) hs
  refine ⟨?_, ?_, ?_⟩
  · rw [← heq]; exact hs
  · rw [← succEq ring hL o]; exact hu
  · rw [← rootEq hL o]; exact hr


private theorem safe (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e o p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (h : SweepOpenRSafeAtV31 ring C o p) :
    SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) o p := by
  have hL := stepV3_labels_eq_or_held hψ h2 ring C e
  rcases h with hm | hf
  · exact Or.inl (mc hψ h2 ring C e p hb hm)
  · exact Or.inr (fun hd => hf (foot ring hL o p hd))


private theorem window (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e f o : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (h : SweepOpenRSafeAtV31 ring C o (ring.rightNeighbor f) ∧
      ∀ d : Fin (ψ - (raw (C f)).label.val), SweepOpenRSafeAtV31 ring C o (R2Coherence.fwd ring f d.val)) :
    SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) o (ring.rightNeighbor f) ∧
      ∀ d : Fin (ψ - (raw (stepV3 hψ h2 ring C e f)).label.val),
        SweepOpenRSafeAtV31 ring (stepV3 hψ h2 ring C e) o (R2Coherence.fwd ring f d.val) := by
  constructor
  · exact safe hψ h2 ring C e o (ring.rightNeighbor f) hb h.1
  · intro dD
    have hv := congrArg Fin.val (stepV3_labels_eq_or_held hψ h2 ring C e f)
    have hd : dD.val < ψ - (raw (C f)).label.val := by simpa only [hv] using dD.isLt
    let dC : Fin (ψ - (raw (C f)).label.val) := ⟨dD.val, hd⟩
    exact safe hψ h2 ring C e o (R2Coherence.fwd ring f dD.val) hb
      (by simpa [dC] using h.2 dC)

theorem sweepOpenROverlapClearWide_commit_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hWide : SweepOpenROverlapClearWideV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    SweepOpenROverlapClearWideV31 ring (stepV3 hψ h2 ring C e) := by
  intro s o hs hp
  have heq := oldTok hψ h2 ring C e s hb (t := .sweep) (by decide) (by decide) hs
  have hsC : (C s).ctl.tok = .sweep := by rw [← heq]; exact hs
  exact window hψ h2 ring C e s o hb (hWide s o hsC (pending hψ h2 ring C e o hb hp))


theorem sweepOpenROverlapClear_commit_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hWide : SweepOpenROverlapClearWideV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    SweepOpenROverlapClearV31 ring (stepV3 hψ h2 ring C e) := by
  exact sweepOpenROverlapClearWide_implies_pointwise ring _
    (sweepOpenROverlapClearWide_commit_step hψ h2 ring C e hWide hb)


theorem seekIncomingSweepOpenROverlapClearWide_commit_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hS : SeekIncomingSweepOpenROverlapClearWideV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    SeekIncomingSweepOpenROverlapClearWideV31 ring (stepV3 hψ h2 ring C e) := by
  have hL := stepV3_labels_eq_or_held hψ h2 ring C e
  intro pred o hs hp
  have heq := oldTok hψ h2 ring C e (ring.rightNeighbor pred) hb
    (t := .seek) (by decide) (by decide) hs
  have hsC : (C (ring.rightNeighbor pred)).ctl.tok = .seek := by rw [← heq]; exact hs
  have h := hS pred o hsC (pending hψ h2 ring C e o hb hp)
  constructor
  · intro hrD
    have hrC : atRootB (C (ring.rightNeighbor pred)) = true := by
      rw [← rootEq hL _]; exact hrD
    exact window hψ h2 ring C e (ring.rightNeighbor pred) o hb (h.1 hrC)
  · intro hnD hrD
    have hnC : atRootB (C (ring.rightNeighbor pred)) = false := by
      rw [← rootEq hL _]; exact hnD
    have hrC : atRootB (C pred) = true := by rw [← rootEq hL pred]; exact hrD
    exact window hψ h2 ring C e pred o hb (h.2 hnC hrC)


theorem openRForwardMainClear_commit_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hR1 : OpenRForwardMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    OpenRForwardMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  intro o ho dD
  have heq := oldTok hψ h2 ring C e o hb (t := .openR) (by decide) (by decide) ho
  have hoC : (C o).ctl.tok = .openR := by rw [← heq]; exact ho
  have hv := congrArg Fin.val (stepV3_labels_eq_or_held hψ h2 ring C e o)
  have hd : dD.val < ψ - (raw (C o)).label.val := by simpa only [hv] using dD.isLt
  let dC : Fin (ψ - (raw (C o)).label.val) := ⟨dD.val, hd⟩
  exact mc hψ h2 ring C e (R2Coherence.fwd ring o dD.val) hb
    (by simpa [dC] using hR1 o hoC dC)


private theorem rnInj (ring : DirectedRing n) : Function.Injective ring.rightNeighbor := by
  intro a b hab; apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv; dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv; omega
    · have hbe : b.val + 1 = n := by omega
      rw [hbe, Nat.mod_self] at hv; omega
  · have hae : a.val + 1 = n := by omega
    rw [hae, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv; omega
    · have hbe : b.val + 1 = n := by omega
      omega


private theorem startSucc (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    R2Coherence.groupStart ring (eraseCfgV3 C) (ring.rightNeighbor e) =
      R2Coherence.groupStart ring (eraseCfgV3 C) e := by
  unfold R2Coherence.groupStart
  change R2Coherence.back ring (ring.rightNeighbor e) (raw (C (ring.rightNeighbor e))).label.val =
    R2Coherence.back ring e (raw (C e)).label.val
  have hv : (raw (C (ring.rightNeighbor e))).label.val = (raw (C e)).label.val + 1 := by
    simpa [successorB] using hs
  rw [hv]
  exact R2CoherenceV31ReachableOpenNoHazard.back_rightNeighbor_succ_reach ring e (raw (C e)).label.val


private theorem gfReidx (ring : DirectedRing n) (C : FC n ψ κ τ) (a b p : Fin n)
    (hs : R2Coherence.groupStart ring (eraseCfgV3 C) a = R2Coherence.groupStart ring (eraseCfgV3 C) b)
    (h : InGroupOwnedFootprintV31 ring C a p) : InGroupOwnedFootprintV31 ring C b p := by
  rcases h with ⟨k, hp⟩
  refine ⟨k, ?_⟩
  have hg : R2Coherence.groupPos ring (eraseCfgV3 C) a k.val =
      R2Coherence.groupPos ring (eraseCfgV3 C) b k.val := by
    unfold R2Coherence.groupPos; rw [hs]
  exact hg.symm.trans hp

private theorem carryBack (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e a o p : Fin n) (hGeom : ElectionGeometryV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (hOpen : (stepV3 hψ h2 ring C e a).ctl.tok = .openR)
    (hne : o ≠ ring.rightNeighbor a)
    (hcary : CarriesGroupOwnedPhaseV31 (stepV3 hψ h2 ring C e) o)
    (hf : InGroupOwnedFootprintV31 ring (stepV3 hψ h2 ring C e) o p) :
    ∃ q, q ≠ ring.rightNeighbor a ∧ CarriesGroupOwnedPhaseV31 C q ∧ InGroupOwnedFootprintV31 ring C q p := by
  have hL := stepV3_labels_eq_or_held hψ h2 ring C e
  have hfC := gfoot ring hL o p hf
  have hc := bc hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  by_cases hoe : o = e
  · subst o
    cases hr : atRootB (C (ring.rightNeighbor e)) with
    | true =>
      refine ⟨e, hne, ?_, hfC⟩
      have heq : stepV3 hψ h2 ring C e e = C e := by
        rw [leftC hψ h2 ring C e hb]
        simp [commitStageV3, hr]
      have hctl :
          (stepV3 hψ h2 ring C e e).ctl = (C e).ctl :=
        congrArg Cell.ctl heq
      unfold CarriesGroupOwnedPhaseV31 at hcary ⊢
      rw [hctl] at hcary
      exact hcary
    | false =>
      have hae : a ≠ e := by
        intro h
        subst a
        rw [leftC hψ h2 ring C e hb] at hOpen
        cases hl : atRootB (C e) <;>
          simp [commitStageV3, hr, hl, setControl] at hOpen
      have hne' : ring.rightNeighbor e ≠ ring.rightNeighbor a := by
        intro h
        exact hae (rnInj ring h).symm
      have hs : successorB (C e) (C (ring.rightNeighbor e)) = true := by
        have hg := hGeom e
        unfold passiveEdgeOKV3 at hg
        simp [hr] at hg
        exact hg
      refine ⟨ring.rightNeighbor e, hne', Or.inl hc.2, ?_⟩
      exact gfReidx ring C e (ring.rightNeighbor e) p
        (startSucc ring C e hs).symm hfC
  · by_cases hor : o = ring.rightNeighbor e
    · subst o
      exact ⟨ring.rightNeighbor e, hne, Or.inl hc.2, hfC⟩
    · have heq := stepV3_other hψ h2 ring C e o hoe hor
      have hctl :
          (stepV3 hψ h2 ring C e o).ctl = (C o).ctl :=
        congrArg Cell.ctl heq
      have hcaryC : CarriesGroupOwnedPhaseV31 C o := by
        unfold CarriesGroupOwnedPhaseV31 at hcary ⊢
        rw [hctl] at hcary
        exact hcary
      exact ⟨o, hne, hcaryC, hfC⟩


theorem openRPhaseOwnershipDisjointStrong_commit_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hStrong : OpenRPhaseOwnershipDisjointStrongV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    OpenRPhaseOwnershipDisjointStrongV31 ring (stepV3 hψ h2 ring C e) := by
  have hL := stepV3_labels_eq_or_held hψ h2 ring C e
  constructor
  · intro a o ho hs hne
    have heq := oldTok hψ h2 ring C e a hb (t := .openR) (by decide) (by decide) ho
    have hoC : (C a).ctl.tok = .openR := by rw [← heq]; exact ho
    have hsC : successorB (C a) (C (ring.rightNeighbor a)) = true := by
      rw [← succEq ring hL a]; exact hs
    have hOld := hStrong.1 a o hoC hsC hne
    refine ⟨?_, ?_, ?_⟩
    · intro hsw hf
      have hse := oldTok hψ h2 ring C e o hb (t := .sweep) (by decide) (by decide) hsw
      exact hOld.1 (by rw [← hse]; exact hsw) (sfoot ring hL o a hf)
    · intro hcary hf
      rcases carryBack hψ h2 ring C e a o a hGeom hb ho hne hcary hf with ⟨q, hq, hqC, hfC⟩
      exact (hStrong.1 a q hoC hsC hq).2.1 hqC hfC
    · intro ht
      have htC : atTerminalB (C (ring.rightNeighbor a)) = true := by
        rw [← termEq hL _]; exact ht
      constructor
      · intro hsw hf
        have hse := oldTok hψ h2 ring C e o hb (t := .sweep) (by decide) (by decide) hsw
        exact (hOld.2.2 htC).1 (by rw [← hse]; exact hsw)
          (sfoot ring hL o (ring.rightNeighbor a) hf)
      · intro hcary hf
        rcases carryBack hψ h2 ring C e a o (ring.rightNeighbor a) hGeom hb ho hne hcary hf with
          ⟨q, hq, hqC, hfC⟩
        exact ((hStrong.1 a q hoC hsC hq).2.2 htC).2 hqC hfC
  · intro s o p hsw hp hr hf
    have hse := oldTok hψ h2 ring C e s hb (t := .sweep) (by decide) (by decide) hsw
    have hswC : (C s).ctl.tok = .sweep := by rw [← hse]; exact hsw
    exact po hψ h2 ring C e p hb (hStrong.2 s o p hswC
      (pending hψ h2 ring C e o hb hp) (readBack ring hL s p hr) (foot ring hL o p hf))


theorem commitStep_reachable_full
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    ReachablePhaseFactsPlus4StrongR2V31 ring (stepV3 hψ h2 ring C e) := by
  have hPlain : ReachablePhaseFactsPlus4V31 ring C :=
    ⟨hPlus.1, hPlus.2.1, hPlus.2.2.1, hPlus.2.2.2.1⟩
  have p1 := commitStep_reachable_P1 hψ h2 ring C e hPlain hb
  have p2 := commitP2OwnerReindexV31 (κ := κ) (τ := τ) hψ h2 ring C e hTrace hPlain hb
  have p345 := commitStep_reachable_P3_P5 hψ h2 ring C e hTrace hPlus hb
  have p6 := commitP6OpenRFreshPreservationV31 (κ := κ) (τ := τ) hψ h2 ring C e hTrace hPlus hb
  have p7 := scrubLIncomingOpenRFresh_commit_step hψ h2 ring C e hTrace hPlus hb
  have p9 := sweepOpenROverlapClearWide_commit_step hψ h2 ring C e hPlus.1.2 hb
  have p8 := sweepOpenROverlapClear_commit_step hψ h2 ring C e hPlus.1.2 hb
  have hs := seekIncomingSweepOpenROverlapClearWide_commit_step hψ h2 ring C e hPlus.2.1 hb
  have r1 := openRForwardMainClear_commit_step hψ h2 ring C e hPlus.2.2.1 hb
  have r2 := openRPhaseOwnershipDisjointStrong_commit_step hψ h2 ring C e hGeom hPlus.2.2.2 hb
  have hFacts : ReachablePhaseFactsV31 ring (stepV3 hψ h2 ring C e) :=
    ⟨p1, p2, p345.1, p345.2.1, p345.2.2, p6⟩
  have hP3 : ReachablePhaseFactsPlus3V31 ring (stepV3 hψ h2 ring C e) :=
    ⟨⟨⟨hFacts, p7⟩, p8⟩, p9⟩
  exact ⟨hP3, hs, r1, r2⟩


end R2CoherenceV31ReachableThreeBranches4
