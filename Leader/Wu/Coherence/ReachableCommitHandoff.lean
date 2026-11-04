import Leader.Wu.Coherence.ReachableCommitOwnerFresh

set_option autoImplicit false

namespace R2CoherenceV31ReachableThreeBranches3

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31PhaseMainClear R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableThreeBranches2
open R2CoherenceV31Closure2 R2CoherenceV31ReachableOpenNoHazard4

variable {n ψ κ τ : Nat}

private theorem modL3 (a b n : Nat) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem modR3 (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

private theorem prefixGroup3
    (ring : DirectedRing n) (C : R2Coherence.FC n ψ κ τ)
    (i : Fin n) (k : Nat) (hk : k ≤ (R2Coherence.raw (C i)).label.val) :
    R2Coherence.prefixPos ring C i k = R2Coherence.groupPos ring C i k := by
  let L := (R2Coherence.raw (C i)).label.val
  let A := i.val + n
  let a := (L - k) % n
  let b := k % n
  have hkL : k ≤ L := by simpa [L] using hk
  have hn : 0 < n := ring.hn
  have ha : a < n := by dsimp [a]; exact Nat.mod_lt _ hn
  have hb : b < n := by dsimp [b]; exact Nat.mod_lt _ hn
  have hA : n ≤ A := by dsimp [A]; omega
  have hmod : L % n = (a + b) % n := by
    calc
      L % n = (L - k + k) % n := by rw [Nat.sub_add_cancel hkL]
      _ = ((L - k) % n + k % n) % n := Nat.add_mod _ _ _
      _ = (a + b) % n := rfl
  apply Fin.ext
  change (A - a) % n = (((A - (L % n)) % n + k) % n)
  symm
  by_cases hs : a + b < n
  · have hm : L % n = a + b := hmod.trans (Nat.mod_eq_of_lt hs)
    calc
      (((A - (L % n)) % n + k) % n) = (A - (L % n) + k) % n :=
        modL3 (A - (L % n)) k n
      _ = (A - (L % n) + b) % n := by
        simpa [b] using (modR3 (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hm]
        have : A - (a + b) + b = A - a := by omega
        rw [this]
  · have hge : n ≤ a + b := by omega
    have hlt : a + b - n < n := by omega
    have hm : L % n = a + b - n := by
      calc
        L % n = (a + b) % n := hmod
        _ = (a + b - n) % n := Nat.mod_eq_sub_mod hge
        _ = a + b - n := Nat.mod_eq_of_lt hlt
    calc
      (((A - (L % n)) % n + k) % n) = (A - (L % n) + k) % n :=
        modL3 (A - (L % n)) k n
      _ = (A - (L % n) + b) % n := by
        simpa [b] using (modR3 (A - (L % n)) k n).symm
      _ = (A - a) % n := by
        rw [hm]
        have : A - (a + b - n) + b = n + (A - a) := by omega
        rw [this, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]

private theorem groupSelf3
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    R2Coherence.groupPos ring (eraseCfgV3 C) i (raw (C i)).label.val = i := by
  change R2Coherence.groupPos ring (eraseCfgV3 C) i
      (R2Coherence.raw ((eraseCfgV3 C) i)).label.val = i
  rw [← prefixGroup3 ring (eraseCfgV3 C) i
    (R2Coherence.raw ((eraseCfgV3 C) i)).label.val (Nat.le_refl _)]
  apply Fin.ext
  simp only [R2Coherence.prefixPos, R2Coherence.back,
    Nat.sub_self, Nat.zero_mod, Nat.sub_zero]
  rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_self,
    Nat.add_zero, Nat.mod_eq_of_lt i.isLt]

private theorem branchCommit3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .commit) :
    l.ctl.tok ≠ .sweep ∧ r.ctl.tok = .commit := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowCommit3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .commit) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = commitStageV3 l r := by
  rcases branchCommit3 hψ h2 l r hb with ⟨hs, hc⟩
  simp [rowV3, hs, hc]

private theorem left3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    stepV3 hψ h2 ring C e e =
      (commitStageV3 (C e) (C (ring.rightNeighbor e))).1 := by
  have hr := rowCommit3 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr]

private theorem right3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (hne : ring.rightNeighbor e ≠ e) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      setControl (clearMain (C (ring.rightNeighbor e))) .sealed .none := by
  have hr := rowCommit3 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr, hne, commitStageV3]


private theorem oldToken3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e i : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    {t : TokenV3} (hn : t ≠ .none) (hc : t ≠ .commit)
    (ht : (stepV3 hψ h2 ring C e i).ctl.tok = t) :
    stepV3 hψ h2 ring C e i = C i := by
  by_cases hie : i = e
  · subst i
    rw [left3 hψ h2 ring C e hb] at ht ⊢
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
    · subst i
      rw [right3 hψ h2 ring C e hb hie] at ht
      exfalso; apply hn
      simpa [setControl] using ht.symm
    · exact stepV3_other hψ h2 ring C e i hie hir

private theorem servedClear3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    MainClearV3 (C (ring.rightNeighbor e)) ∧
      (atRootB (C (ring.rightNeighbor e)) = false → MainClearV3 (C e)) := by
  have hFacts : ReachablePhaseFactsV31 ring C := hPlus.1.1.1.1
  have hc := branchCommit3 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  have hg := hFacts.2.1 (ring.rightNeighbor e) hc.2
  have hr := hg (raw (C (ring.rightNeighbor e))).label
  dsimp only at hr
  rw [groupSelf3 ring C (ring.rightNeighbor e)] at hr
  refine ⟨hr.1, ?_⟩
  intro hroot
  have hGeom := R2CoherenceV31ReachableSweep.electionGeometry_of_quarantineTrace
    hψ h2 ring C hTrace
  have he := hGeom e
  have hs : successorB (C e) (C (ring.rightNeighbor e)) = true := by
    unfold passiveEdgeOKV3 at he
    simp [hroot] at he
    exact he
  have hstart : R2Coherence.groupStart ring (eraseCfgV3 C) (ring.rightNeighbor e) =
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
  have hl := hg (raw (C e)).label
  dsimp only at hl
  have hp : R2Coherence.groupPos ring (eraseCfgV3 C)
      (ring.rightNeighbor e) (raw (C e)).label.val = e := by
    have hself := groupSelf3 ring C e
    unfold R2Coherence.groupPos at hself ⊢
    rw [hstart]
    exact hself
  rw [hp] at hl
  exact hl.1

private theorem sameOrClear3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    stepV3 hψ h2 ring C e p = C p ∨ MainClearV3 (C p) := by
  have hc := servedClear3 hψ h2 ring C e hTrace hPlus hb
  by_cases hpe : p = e
  · subst p
    cases hr : atRootB (C (ring.rightNeighbor e)) with
    | false => exact Or.inr (hc.2 hr)
    | true =>
      left
      rw [left3 hψ h2 ring C e hb]
      simp [commitStageV3, hr]
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p; exact Or.inr hc.1
    · exact Or.inl (stepV3_other hψ h2 ring C e p hpe hpr)

private theorem equalSame3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (heq : (raw (stepV3 hψ h2 ring C e p)).state = .equal) :
    stepV3 hψ h2 ring C e p = C p := by
  by_cases hpe : p = e
  · subst p
    cases hr : atRootB (C (ring.rightNeighbor e)) with
    | true => rw [left3 hψ h2 ring C e hb]; simp [commitStageV3, hr]
    | false =>
      exfalso
      rw [left3 hψ h2 ring C e hb] at heq
      cases hl : atRootB (C e) <;>
        simp [commitStageV3, hr, hl, setControl, clearMain, raw] at heq
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      exfalso
      rw [right3 hψ h2 ring C e hb hpe] at heq
      simp [setControl, clearMain, raw] at heq
    · exact stepV3_other hψ h2 ring C e p hpe hpr


private theorem gp3
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

private theorem pp3
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [hLab i]

private theorem freshFalse3 (u : Cell ψ κ τ) (k : Nat)
    (hm : MainClearV3 u)
    (hf : R2Coherence.freshComponent (eraseCellV3 u) k) : False := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at hm
  unfold R2Coherence.freshComponent at hf
  change (raw u).label.val = k ∧
    (match (raw u).path with
     | .bot => False
     | .some lab b => lab.val = k ∧ b.val = (if (raw u).bit then 1 else 0)) at hf
  have hp : (raw u).path = .bot := hm.2.1
  rw [hp] at hf
  exact hf.2

private theorem freshDeletion3
    (ring : DirectedRing n) {C D : FC n ψ κ τ} (owner : Fin n)
    (hLab : ∀ p : Fin n, (raw (D p)).label = (raw (C p)).label)
    (hFront : ∀ p : Fin n, (raw (D p)).state = .equal → D p = C p)
    (hCell : ∀ p : Fin n, D p = C p ∨ MainClearV3 (C p))
    (hFresh : OpenROwnerFreshV3 ring C owner) : OpenROwnerFreshV3 ring D owner := by
  unfold OpenROwnerFreshV3 at hFresh ⊢
  intro j ko hHitD
  rw [gp3 ring hLab j ko.val] at hHitD
  have hg := hFresh j ko hHitD
  unfold GroupIntrinsicFreshV3 at hg ⊢
  intro q
  rw [gp3 ring hLab j q.val]
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  change IntrinsicFreshAtV3 ring D front
  have hf : IntrinsicFreshAtV3 ring C front := by simpa [front] using hg q
  unfold IntrinsicFreshAtV3 at hf ⊢
  intro heqD
  have hsame := hFront front heqD
  have heqC : (raw (C front)).state = .equal := by simpa [hsame] using heqD
  have hold := hf heqC
  intro kD
  have hv := congrArg (fun x : Fin ψ => x.val) (hLab front)
  have hk : kD.val < (raw (C front)).label.val + 1 := by
    let m := kD.val
    have hm : m < (raw (D front)).label.val + 1 := kD.isLt
    simpa only [hv] using hm
  let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hk⟩
  have ho := hold kC
  rw [pp3 ring hLab front kD.val]
  let p := R2Coherence.prefixPos ring (eraseCfgV3 C) front kD.val
  change R2Coherence.freshComponent (eraseCellV3 (D p)) kD.val
  have ho' : R2Coherence.freshComponent (eraseCellV3 (C p)) kD.val := by
    simpa [p, kC] using ho
  rcases hCell p with hsame | hclear
  · simpa [hsame, p] using ho'
  · exact (freshFalse3 (C p) kD.val hclear ho').elim

private theorem freshCommit3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit)
    (hFresh : OpenROwnerFreshV3 ring C owner) :
    OpenROwnerFreshV3 ring (stepV3 hψ h2 ring C e) owner := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label := by
    intro p; simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  apply freshDeletion3 ring owner hLab
  · intro p hp
    change stepV3 hψ h2 ring C e p = C p
    exact equalSame3 hψ h2 ring C e p hb (by simpa [D] using hp)
  · intro p
    change stepV3 hψ h2 ring C e p = C p ∨ MainClearV3 (C p)
    exact sameOrClear3 hψ h2 ring C e p hTrace hPlus hb
  · exact hFresh

theorem scrubLIncomingOpenRFresh_commit_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .commit) :
    ScrubLIncomingOpenRFreshV31 ring (stepV3 hψ h2 ring C e) := by
  have hOld : ScrubLIncomingOpenRFreshV31 ring C := hPlus.1.1.1.2
  have hLab := stepV3_labels_eq_or_held hψ h2 ring C e
  intro owner hScrubD hSuccD hRootD
  have hSame := oldToken3 hψ h2 ring C e (ring.rightNeighbor owner) hb
    (t := .scrubL) (by decide) (by decide) hScrubD
  have hScrubC := hScrubD
  rw [hSame] at hScrubC
  have hSuccC : successorB (C owner) (C (ring.rightNeighbor owner)) = true := by
    unfold successorB at hSuccD ⊢
    rw [hLab owner, hLab (ring.rightNeighbor owner)] at hSuccD
    exact hSuccD
  have hRootC : atRootB (C owner) = true := by
    unfold atRootB at hRootD ⊢
    rw [hLab owner] at hRootD
    exact hRootD
  exact freshCommit3 hψ h2 ring C e owner hTrace hPlus hb
    (hOld owner hScrubC hSuccC hRootC)

end R2CoherenceV31ReachableThreeBranches3
