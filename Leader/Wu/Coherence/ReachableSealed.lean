import Leader.Wu.Coherence.ReachableStrongOwnership
import Leader.Wu.Coherence.ReachableCommitOwnerFresh

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableSealed

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard3
open R2CoherenceV31ReachableOpenNoHazard4

variable {n ψ κ τ : Nat}

private theorem bc
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sealed) :
    l.ctl.tok = .none ∧ r.ctl.tok = .none ∧
      l.ctl.mark = .sealed ∧ r.ctl.mark = .sealed := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowS
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sealed) :
    rowV3 hψ (by decide : 0 < 2) h2 l r =
      sealedStageV3 hψ (by decide : 0 < 2) h2 l r := by
  rcases bc hψ h2 l r hb with ⟨hl, hr, hsl, hsr⟩
  simp [rowV3, ordinaryStageV3, hl, hr, hsl, hsr]

private theorem leftS
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sealed) :
    stepV3 hψ h2 ring C e e =
      (sealedStageV3 hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).1 := by
  have h := rowS hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, h]

private theorem rightS
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sealed)
    (hne : ring.rightNeighbor e ≠ e) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      (sealedStageV3 hψ (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).2 := by
  have h := rowS hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, h, hne]

private theorem mcSet (u : Cell ψ κ τ) (m : R2Coherence.Mark) (t : TokenV3) :
    MainClearV3 (setControl u m t) ↔ MainClearV3 u := by
  simp [MainClearV3, R2CoherenceBranches.MainClear,
    eraseCellV3, setControl, R2Coherence.raw]

private theorem mcI (u : Cell ψ κ τ) (q : R2.Cell ψ κ τ) :
    MainClearV3 (install u (R2Coherence.clearMainPhys q)) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [install, eraseCellV3, R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier, R2Coherence.raw]

private theorem gp
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

private theorem pp
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [h i]

private theorem gt
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (hm : ∀ p, MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
      MainClearV3 (D p) ∧ PhaseOwnedV31 (D p))
    (i : Fin n) (h : GroupOwnedClearV31 ring C i) :
    GroupOwnedClearV31 ring D i := by
  intro k
  rw [gp ring hL i k.val]
  exact hm _ (h k)

private theorem st
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (hm : ∀ p, MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
      MainClearV3 (D p) ∧ PhaseOwnedV31 (D p))
    (i : Fin n) (h : SweptPrefixOwnedClearV31 ring C i) :
    SweptPrefixOwnedClearV31 ring D i := by
  intro kD
  have hv := congrArg Fin.val (hL i)
  have hk : kD.val < (raw (C i)).label.val := by
    simpa only [hv] using kD.isLt
  let kC : Fin (raw (C i)).label.val := ⟨kD.val, hk⟩
  rw [gp ring hL i kD.val]
  exact hm _ (by simpa [kC] using h kC)

private theorem mcState (u : Cell ψ κ τ) (h : MainClearV3 u) :
    (raw u).state = .none := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at h
  simpa [raw, eraseCellV3, R2Coherence.raw] using h.1

private theorem freshFalse (u : Cell ψ κ τ) (k : Nat)
    (hm : MainClearV3 u)
    (hf : R2Coherence.freshComponent (eraseCellV3 u) k) : False := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at hm
  unfold R2Coherence.freshComponent at hf
  change (raw u).label.val = k ∧
    (match (raw u).path with
     | .bot => False
     | .some lab b => lab.val = k ∧
       b.val = (if (raw u).bit then 1 else 0)) at hf
  have hp : (raw u).path = .bot := by
    simpa [raw, eraseCellV3, R2Coherence.raw] using hm.2.1
  rw [hp] at hf
  exact hf.2

private theorem freshDel
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (hCell : ∀ p, D p = C p ∨ MainClearV3 (C p))
    (hMC : ∀ p, MainClearV3 (C p) → MainClearV3 (D p))
    (owner : Fin n) (hf : OpenROwnerFreshV3 ring C owner) :
    OpenROwnerFreshV3 ring D owner := by
  unfold OpenROwnerFreshV3 at hf ⊢
  intro j ko hHit
  rw [gp ring hL j ko.val] at hHit
  have hg := hf j ko hHit
  unfold GroupIntrinsicFreshV3 at hg ⊢
  intro q
  rw [gp ring hL j q.val]
  let f := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  change IntrinsicFreshAtV3 ring D f
  have ho : IntrinsicFreshAtV3 ring C f := by simpa [f] using hg q
  unfold IntrinsicFreshAtV3 at ho ⊢
  intro heq
  rcases hCell f with hs | hc
  · have heqC : (raw (C f)).state = .equal := by simpa [hs] using heq
    have ha := ho heqC
    intro kD
    have hv := congrArg Fin.val (hL f)
    have hk : kD.val < (raw (C f)).label.val + 1 := by
      simpa only [hv] using kD.isLt
    let kC : Fin ((raw (C f)).label.val + 1) := ⟨kD.val, hk⟩
    have hOld := ha kC
    rw [pp ring hL f kD.val]
    let p := R2Coherence.prefixPos ring (eraseCfgV3 C) f kD.val
    change R2Coherence.freshComponent (eraseCellV3 (D p)) kD.val
    have hOld' : R2Coherence.freshComponent (eraseCellV3 (C p)) kD.val := by
      simpa [p, kC] using hOld
    rcases hCell p with hp | hp
    · simpa [hp, p] using hOld'
    · exact (freshFalse (C p) kD.val hp hOld').elim
  · have hn := mcState (D f) (hMC f hc)
    rw [hn] at heq
    cases heq

private theorem footBack
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (owner p : Fin n) (h : InOpenRFreshFootprintV31 ring D owner p) :
    InOpenRFreshFootprintV31 ring C owner p := by
  rcases h with ⟨j, ko, q, ho, kD, hp⟩
  rw [gp ring hL j ko.val] at ho
  have hq := gp ring hL j q.val
  let f := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hq' : R2Coherence.groupPos ring (eraseCfgV3 D) j q.val = f := by
    simpa [f] using hq
  have hv : (raw (D (R2Coherence.groupPos ring (eraseCfgV3 D) j q.val))).label.val =
      (raw (C f)).label.val := by
    rw [hq']; exact congrArg Fin.val (hL f)
  have hk : kD.val < (raw (C f)).label.val + 1 := by
    simpa only [hv] using kD.isLt
  let kC : Fin ((raw (C f)).label.val + 1) := ⟨kD.val, hk⟩
  refine ⟨j, ko, q, ho, kC, ?_⟩
  have hpp := pp ring hL f kD.val
  have hp' : R2Coherence.prefixPos ring (eraseCfgV3 D) f kD.val = p := by
    simpa only [hq'] using hp
  exact hpp.symm.trans hp'

private theorem sfBack
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (o p : Fin n) (h : InSweptOwnedFootprintV31 ring D o p) :
    InSweptOwnedFootprintV31 ring C o p := by
  rcases h with ⟨kD, hp⟩
  have hv := congrArg Fin.val (hL o)
  have hk : kD.val < (raw (C o)).label.val := by
    simpa only [hv] using kD.isLt
  let kC : Fin (raw (C o)).label.val := ⟨kD.val, hk⟩
  refine ⟨kC, ?_⟩
  exact (gp ring hL o kD.val).symm.trans hp

private theorem gfBack
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hL : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (o p : Fin n) (h : InGroupOwnedFootprintV31 ring D o p) :
    InGroupOwnedFootprintV31 ring C o p := by
  rcases h with ⟨k, hp⟩
  exact ⟨k, (gp ring hL o k.val).symm.trans hp⟩

theorem sealedStep_reachable_full
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sealed) :
    ReachablePhaseFactsPlus4StrongR2V31 ring
      (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  have hFacts : ReachablePhaseFactsV31 ring C := hPlus.1.1.1.1
  have hc := bc hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  have modLeft (a b : Nat) : (a % n + b) % n = (a + b) % n := by
    rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
    exact (Nat.add_mod a b n).symm
  have modRight (a b : Nat) : (a + b % n) % n = (a + b) % n := by
    rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
    exact (Nat.add_mod a b n).symm
  have groupSelf (i : Fin n) :
      R2Coherence.groupPos ring (eraseCfgV3 C) i (raw (C i)).label.val = i := by
    let L := (raw (C i)).label.val
    apply Fin.ext
    change ((((i.val + n - (L % n)) % n) + L) % n) = i.val
    rw [modLeft (i.val + n - (L % n)) L]
    rw [← modRight (i.val + n - (L % n)) L]
    have hmod : L % n ≤ i.val + n := by
      have : L % n < n := Nat.mod_lt _ ring.hn
      omega
    rw [Nat.sub_add_cancel hmod]
    rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_self,
      Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
  have hce : MainClearV3 (C e) := by
    have hAt := hFacts.2.2.1 e hc.2.2.1 (raw (C e)).label
    dsimp only at hAt
    rw [groupSelf e] at hAt
    exact hAt.1
  have hcr : MainClearV3 (C (ring.rightNeighbor e)) := by
    have hAt := hFacts.2.2.1 (ring.rightNeighbor e) hc.2.2.2
      (raw (C (ring.rightNeighbor e))).label
    dsimp only at hAt
    rw [groupSelf (ring.rightNeighbor e)] at hAt
    exact hAt.1
  have hL : ∀ p, (raw (D p)).label = (raw (C p)).label := by
    intro p; simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  have hCtl : ∀ p : Fin n, (D p).ctl = (C p).ctl ∨
      (p = e ∧ (D p).ctl = ⟨.releasing, .release⟩) := by
    intro p
    by_cases hp : p = e
    · subst p; rw [show D e = stepV3 hψ h2 ring C e e by rfl, leftS hψ h2 ring C e hb]
      unfold sealedStageV3
      split
      · right; simp [setControl]
      · left; dsimp only; split <;> simp [install]
    · by_cases hr : p = ring.rightNeighbor e
      · subst p; left
        rw [show D (ring.rightNeighbor e) = stepV3 hψ h2 ring C e (ring.rightNeighbor e) by rfl,
          rightS hψ h2 ring C e hb hp]
        unfold sealedStageV3
        split
        · rfl
        · dsimp only; split <;> simp [install]
      · left; exact congrArg Cell.ctl (by
          simpa [D] using stepV3_other hψ h2 ring C e p hp hr)
  have hMC : ∀ p, MainClearV3 (C p) → MainClearV3 (D p) := by
    intro p hm
    by_cases hp : p = e
    · subst p; rw [show D e = stepV3 hψ h2 ring C e e by rfl, leftS hψ h2 ring C e hb]
      unfold sealedStageV3
      split
      · exact (mcSet _ _ _).2 hce
      · dsimp only; split
        · exact hce
        · exact mcI _ _
    · by_cases hr : p = ring.rightNeighbor e
      · subst p
        rw [show D (ring.rightNeighbor e) = stepV3 hψ h2 ring C e (ring.rightNeighbor e) by rfl,
          rightS hψ h2 ring C e hb hp]
        unfold sealedStageV3
        split
        · exact hcr
        · dsimp only; split
          · exact hcr
          · exact mcI _ _
      · simpa [D] using hm
        |> (fun x => by simpa [stepV3_other hψ h2 ring C e p hp hr] using x)
  have hPO : ∀ p, PhaseOwnedV31 (C p) → PhaseOwnedV31 (D p) := by
    intro p ho
    rcases hCtl p with hs | ⟨_, hs⟩
    · unfold PhaseOwnedV31 at ho ⊢
      rw [hs]
      exact ho
    · unfold PhaseOwnedV31
      right
      intro hnone
      rw [hs] at hnone
      cases hnone
  have hMono : ∀ p, MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
      MainClearV3 (D p) ∧ PhaseOwnedV31 (D p) := by
    intro p h; exact ⟨hMC p h.1, hPO p h.2⟩
  have hCell : ∀ p, D p = C p ∨ MainClearV3 (C p) := by
    intro p; by_cases hp : p = e
    · exact Or.inr (by simpa [hp] using hce)
    · by_cases hr : p = ring.rightNeighbor e
      · exact Or.inr (by simpa [hr] using hcr)
      · exact Or.inl (by simpa [D] using stepV3_other hψ h2 ring C e p hp hr)
  have tokBack : ∀ p t, t ≠ .release → (D p).ctl.tok = t → (C p).ctl.tok = t := by
    intro p t hnr ht
    rcases hCtl p with hs | ⟨_, hs⟩
    · rw [hs] at ht; exact ht
    · rw [hs] at ht; simp at ht; exact (hnr ht.symm).elim
  have markBack : ∀ p, (D p).ctl.mark = .sealed → (C p).ctl.mark = .sealed := by
    intro p hm; rcases hCtl p with hs | ⟨_, hs⟩
    · rw [hs] at hm; exact hm
    · rw [hs] at hm; cases hm
  have hFresh : ∀ o, OpenROwnerFreshV3 ring C o → OpenROwnerFreshV3 ring D o :=
    fun o h => freshDel ring hL hCell hMC o h
  have succBack : ∀ p, successorB (D p) (D (ring.rightNeighbor p)) = true →
      successorB (C p) (C (ring.rightNeighbor p)) = true := by
    intro p hs
    have hl := congrArg Fin.val (hL p)
    have hr := congrArg Fin.val (hL (ring.rightNeighbor p))
    unfold successorB at hs ⊢; rw [hl, hr] at hs; exact hs
  have rootBack : ∀ p, atRootB (D p) = true → atRootB (C p) = true := by
    intro p hr; have hl := congrArg Fin.val (hL p)
    unfold atRootB at hr ⊢; rw [hl] at hr; exact hr

  have termBack : ∀ p, atTerminalB (D p) = true → atTerminalB (C p) = true := by
    intro p ht; have hl := congrArg Fin.val (hL p)
    unfold atTerminalB at ht ⊢; rw [hl] at ht; exact ht
  have pendingBack : ∀ o, PendingOpenROwnerV31 ring D o →
      PendingOpenROwnerV31 ring C o := by
    intro o h
    exact ⟨tokBack _ .scrubL (by decide) h.1,
      succBack o h.2.1, rootBack o h.2.2⟩
  have safe : ∀ o p, SweepOpenRSafeAtV31 ring C o p →
      SweepOpenRSafeAtV31 ring D o p := by
    intro o p h; unfold SweepOpenRSafeAtV31 at h ⊢
    rcases h with hm | hf
    · exact Or.inl (hMC p hm)
    · right; intro hd; exact hf (footBack ring hL o p hd)
  have readBack : ∀ s p, InSweepWideReadV31 ring D s p →
      InSweepWideReadV31 ring C s p := by
    intro s p h; rcases h with h | ⟨dD, hp⟩
    · exact Or.inl h
    · right
      have hv := congrArg Fin.val (hL s)
      have hd : dD.val < ψ - (raw (C s)).label.val := by
        simpa only [hv] using dD.isLt
      exact ⟨⟨dD.val, hd⟩, hp⟩
  have carryBack : ∀ o, CarriesGroupOwnedPhaseV31 D o →
      CarriesGroupOwnedPhaseV31 C o := by
    intro o h
    rcases hCtl o with hs | ⟨hoe, _⟩
    · unfold CarriesGroupOwnedPhaseV31 at h ⊢; rw [hs] at h; exact h
    · subst o; exact Or.inr (Or.inl hc.2.2.1)

  rcases hFacts with ⟨hSw, hCo, hSe, hRe, hSc, hOp⟩
  have hFactsD : ReachablePhaseFactsV31 ring D := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      exact st ring hL hMono i (hSw i (tokBack i .sweep (by decide) hi))
    · intro i hi
      exact gt ring hL hMono i (hCo i (tokBack i .commit (by decide) hi))
    · intro i hi
      exact gt ring hL hMono i (hSe i (markBack i hi))
    · intro i hi
      rcases hCtl i with hs | ⟨hie, hs⟩
      · have hiC : (C i).ctl.tok = .release := by
          rw [hs] at hi
          exact hi
        rcases hRe i hiC with ⟨hm, hg⟩
        exact ⟨by rw [hs]; exact hm, gt ring hL hMono i hg⟩
      · subst i
        exact ⟨by rw [hs], gt ring hL hMono e (hSe e hc.2.2.1)⟩
    · intro i hi
      have hiC := tokBack i .scrubL (by decide) hi
      rcases hSc i hiC with ⟨hm, hz, hg⟩
      refine ⟨?_, ?_, gt ring hL hMono i hg⟩
      · rcases hCtl i with hs | ⟨_, hs⟩
        · rw [hs]
          exact hm
        · rw [hs] at hi
          cases hi
      · intro hzD
        apply hz
        exact (congrArg Fin.val (hL i)).symm.trans hzD
    · intro i hi
      have hiC := tokBack i .openR (by decide) hi
      rcases hOp i hiC with ⟨hm, hf⟩
      refine ⟨?_, hFresh i hf⟩
      rcases hCtl i with hs | ⟨_, hs⟩
      · rw [hs]
        exact hm
      · rw [hs] at hi
        cases hi

  have hP7D : ScrubLIncomingOpenRFreshV31 ring D := by
    intro o hs hr ht
    exact hFresh o (hPlus.1.1.1.2 o
      (tokBack _ .scrubL (by decide) hs) (succBack o hr) (rootBack o ht))
  have hWideD : SweepOpenROverlapClearWideV31 ring D := by
    intro s o hsw hp
    have hswC := tokBack s .sweep (by decide) hsw
    have hpC := pendingBack o hp
    have h := hPlus.1.2 s o hswC hpC
    constructor
    · exact safe o (ring.rightNeighbor s) h.1
    · intro dD
      have hv := congrArg Fin.val (hL s)
      have hd : dD.val < ψ - (raw (C s)).label.val := by
        simpa only [hv] using dD.isLt
      let dC : Fin (ψ - (raw (C s)).label.val) := ⟨dD.val, hd⟩
      exact safe o (R2Coherence.fwd ring s dD.val)
        (by simpa [dC] using h.2 dC)
  have hP8D := sweepOpenROverlapClearWide_implies_pointwise ring D hWideD

  have hSD : SeekIncomingSweepOpenROverlapClearWideV31 ring D := by
    intro a o hseek hp
    have hseekC := tokBack _ .seek (by decide) hseek
    have hpC := pendingBack o hp
    have h := hPlus.2.1 a o hseekC hpC
    constructor
    · intro hrD
      have hrC := rootBack (ring.rightNeighbor a) hrD
      rcases h.1 hrC with ⟨h0, hw⟩
      constructor
      · exact safe o (ring.rightNeighbor (ring.rightNeighbor a)) h0
      · intro dD
        have hv := congrArg Fin.val (hL (ring.rightNeighbor a))
        have hd : dD.val < ψ - (raw (C (ring.rightNeighbor a))).label.val := by
          simpa only [hv] using dD.isLt
        let dC : Fin (ψ - (raw (C (ring.rightNeighbor a))).label.val) := ⟨dD.val, hd⟩
        exact safe o (R2Coherence.fwd ring (ring.rightNeighbor a) dD.val)
          (by simpa [dC] using hw dC)
    · intro hrD haD
      have hrC : atRootB (C (ring.rightNeighbor a)) = false := by
        cases h0 : atRootB (C (ring.rightNeighbor a))
        · rfl
        · have : atRootB (D (ring.rightNeighbor a)) = true := by
            have hv := congrArg Fin.val (hL (ring.rightNeighbor a))
            unfold atRootB at h0 ⊢; rw [hv]; exact h0
          rw [hrD] at this; cases this

      have haC := rootBack a haD
      rcases h.2 hrC haC with ⟨h0, hw⟩
      constructor
      · exact safe o (ring.rightNeighbor a) h0
      · intro dD
        have hv := congrArg Fin.val (hL a)
        have hd : dD.val < ψ - (raw (C a)).label.val := by
          simpa only [hv] using dD.isLt
        let dC : Fin (ψ - (raw (C a)).label.val) := ⟨dD.val, hd⟩
        exact safe o (R2Coherence.fwd ring a dD.val)
          (by simpa [dC] using hw dC)

  have hR1D : OpenRForwardMainClearV31 ring D := by
    intro a ho dD
    have hoC := tokBack a .openR (by decide) ho
    have hv := congrArg Fin.val (hL a)
    have hd : dD.val < ψ - (raw (C a)).label.val := by
      simpa only [hv] using dD.isLt
    let dC : Fin (ψ - (raw (C a)).label.val) := ⟨dD.val, hd⟩
    exact hMC _ (by simpa [dC] using hPlus.2.2.1 a hoC dC)

  have hR2D : OpenRPhaseOwnershipDisjointStrongV31 ring D := by
    constructor
    · intro a o ho hs hne
      have hoC := tokBack a .openR (by decide) ho
      have hsC := succBack a hs
      have h := hPlus.2.2.2.1 a o hoC hsC hne
      refine ⟨?_, ?_, ?_⟩
      · intro hsw hf
        exact h.1 (tokBack o .sweep (by decide) hsw)
          (sfBack ring hL o a hf)
      · intro hcarry hf
        exact h.2.1 (carryBack o hcarry) (gfBack ring hL o a hf)
      · intro ht
        have hT := h.2.2 (termBack (ring.rightNeighbor a) ht)
        constructor
        · intro hsw hf
          exact hT.1 (tokBack o .sweep (by decide) hsw)
            (sfBack ring hL o (ring.rightNeighbor a) hf)
        · intro hcarry hf
          exact hT.2 (carryBack o hcarry)
            (gfBack ring hL o (ring.rightNeighbor a) hf)
    · intro s o p hsw hp hr hf
      have hOld := hPlus.2.2.2.2 s o p
        (tokBack s .sweep (by decide) hsw)
        (pendingBack o hp) (readBack s p hr) (footBack ring hL o p hf)
      exact hPO p hOld

  have hP3D : ReachablePhaseFactsPlus3V31 ring D :=
    ⟨⟨⟨hFactsD, hP7D⟩, hP8D⟩, hWideD⟩
  exact ⟨hP3D, hSD, hR1D, hR2D⟩

end R2CoherenceV31ReachableSealed
