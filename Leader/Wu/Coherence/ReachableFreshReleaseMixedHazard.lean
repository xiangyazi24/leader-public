import Leader.Wu.Coherence.ReachableSoundFresh
import Leader.Wu.Coherence.ReachableReleaseWide
import Leader.Wu.Coherence.ReachableOpenHazardPrepaid
import Leader.Wu.Coherence.ReachableMixed

set_option autoImplicit false
set_option Elab.async false

namespace R2CoherenceV31ReachableFreshBranches2

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus2 R2CoherenceV31ReachablePlus4
open R2CoherenceV31MainClearTruth R2CoherenceV31MainClearTruth.WeakFreshnessLayer
open R2CoherenceV31FreshnessClear R2CoherenceV31ReachableSoundFresh

variable {n ψ κ τ : Nat}

private def FrameF (C D : FC n ψ κ τ) : Prop :=
  ∀ p, (D p).phys = (C p).phys ∧
    ((D p).ctl = (C p).ctl ∨ (D p).ctl = ⟨.closing, .seek⟩)

private theorem rawF {C D : FC n ψ κ τ} (h : FrameF C D) (p : Fin n) :
    raw (D p) = raw (C p) :=
  congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core) (h p).1

private theorem labF {C D : FC n ψ κ τ} (h : FrameF C D) (p : Fin n) :
    (raw (D p)).label = (raw (C p)).label :=
  congrArg (fun x : BoundedAgentState ψ κ => x.label) (rawF h p)

private theorem gpF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FrameF C D) (i : Fin n) (k : Nat) :
    R2Coherence.groupPos r (eraseCfgV3 D) i k =
      R2Coherence.groupPos r (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd r (R2Coherence.back r i (raw (D i)).label.val) k =
    R2Coherence.fwd r (R2Coherence.back r i (raw (C i)).label.val) k
  rw [labF h i]

private theorem ppF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FrameF C D) (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos r (eraseCfgV3 D) i k =
      R2Coherence.prefixPos r (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back r i ((raw (D i)).label.val - k) =
    R2Coherence.back r i ((raw (C i)).label.val - k)
  rw [labF h i]

private theorem ctlF {C D : FC n ψ κ τ} (h : FrameF C D) (p : Fin n)
    {t : TokenV3} (ht : (D p).ctl.tok = t) (hne : t ≠ .seek) :
    (D p).ctl = (C p).ctl := by
  rcases (h p).2 with hc | hn
  · exact hc
  · rw [hn] at ht
    exact (hne ht.symm).elim

private theorem sealCtlF {C D : FC n ψ κ τ} (h : FrameF C D) (p : Fin n)
    (hm : (D p).ctl.mark = .sealed) : (D p).ctl = (C p).ctl := by
  rcases (h p).2 with hc | hn
  · exact hc
  · rw [hn] at hm
    cases hm

private theorem mainF {C D : FC n ψ κ τ} (h : FrameF C D) (p : Fin n)
    (hm : MainClearV3 (C p)) : MainClearV3 (D p) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at hm ⊢
  simpa [eraseCellV3, R2Coherence.raw, (h p).1] using hm

private theorem freshF {C D : FC n ψ κ τ} (h : FrameF C D) (p : Fin n)
    (hf : FreshnessClearV31 (C p)) : FreshnessClearV31 (D p) := by
  unfold FreshnessClearV31 at hf ⊢
  rw [rawF h p]
  exact hf

private theorem ownedF {C D : FC n ψ κ τ} (h : FrameF C D) (p : Fin n)
    (ho : MainClearV3 (C p) ∧ PhaseOwnedV31 (C p)) :
    MainClearV3 (D p) ∧ PhaseOwnedV31 (D p) := by
  refine ⟨mainF h p ho.1, ?_⟩
  rcases (h p).2 with hc | hn
  · unfold PhaseOwnedV31 at ho ⊢
    rw [hc]
    exact ho.2
  · unfold PhaseOwnedV31
    rw [hn]
    simp

private theorem sweptF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FrameF C D) (i : Fin n) (ho : SweptPrefixOwnedClearV31 r C i) :
    SweptPrefixOwnedClearV31 r D i := by
  unfold SweptPrefixOwnedClearV31 at ho ⊢
  intro k
  have hv := congrArg Fin.val (labF h i)
  have hk : k.val < (raw (C i)).label.val := by simpa only [hv] using k.isLt
  let kc : Fin (raw (C i)).label.val := ⟨k.val, hk⟩
  rw [gpF r h i k.val]
  exact ownedF h _ (by simpa [kc] using ho kc)

private theorem groupF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FrameF C D) (i : Fin n) (ho : GroupOwnedClearV31 r C i) :
    GroupOwnedClearV31 r D i := by
  unfold GroupOwnedClearV31 at ho ⊢
  intro k
  rw [gpF r h i k.val]
  exact ownedF h _ (ho k)

private theorem ownerF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FrameF C D) (o : Fin n) (hf : OpenROwnerFreshV3 r C o) :
    OpenROwnerFreshV3 r D o := by
  unfold OpenROwnerFreshV3 at hf ⊢
  intro j ko hit
  have hko := gpF r h j ko.val
  rw [hko] at hit
  have hg := hf j ko hit
  unfold GroupIntrinsicFreshV3 at hg ⊢
  intro q
  have hq := gpF r h j q.val
  rw [hq]
  let f := R2Coherence.groupPos r (eraseCfgV3 C) j q.val
  change IntrinsicFreshAtV3 r D f
  have old : IntrinsicFreshAtV3 r C f := by simpa [f] using hg q
  unfold IntrinsicFreshAtV3 at old ⊢
  intro heqD
  have heqC : (raw (C f)).state = .equal := by
    rw [← rawF h f]
    exact heqD
  have ha := old heqC
  intro kD
  have hv : (raw (D f)).label.val = (raw (C f)).label.val :=
    congrArg (fun x : BoundedAgentState ψ κ => x.label.val) (rawF h f)
  let m : Nat := kD.val
  have hkD : m < (raw (D f)).label.val + 1 := by exact kD.isLt
  have hkC : m < (raw (C f)).label.val + 1 := by
    simpa only [hv] using hkD
  let kC : Fin ((raw (C f)).label.val + 1) := ⟨m, hkC⟩
  have hz := ha kC
  have hpp := ppF r h f m
  change R2Coherence.freshComponent
    (eraseCellV3 (D (R2Coherence.prefixPos r (eraseCfgV3 D) f m))) m
  rw [hpp]
  let p := R2Coherence.prefixPos r (eraseCfgV3 C) f m
  change R2Coherence.freshComponent (eraseCellV3 (D p)) m
  have hz' : R2Coherence.freshComponent (eraseCellV3 (C p)) m := by
    simpa [p, kC] using hz
  unfold R2Coherence.freshComponent at hz' ⊢
  change (raw (D p)).label.val = m ∧
    (match (raw (D p)).path with
     | .bot => False
     | .some a b => a.val = m ∧ b.val = (if (raw (D p)).bit then 1 else 0))
  change (raw (C p)).label.val = m ∧
    (match (raw (C p)).path with
     | .bot => False
     | .some a b => a.val = m ∧ b.val = (if (raw (C p)).bit then 1 else 0)) at hz'
  rw [rawF h p]
  exact hz'

private theorem footBackF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FrameF C D) (o p : Fin n)
    (hf : InOpenRFreshFootprintV31 r D o p) : InOpenRFreshFootprintV31 r C o p := by
  rcases hf with ⟨j, ko, q, ho, k, hp⟩
  rw [gpF r h j ko.val] at ho
  have hq := gpF r h j q.val
  let f := R2Coherence.groupPos r (eraseCfgV3 C) j q.val
  have hfD : R2Coherence.groupPos r (eraseCfgV3 D) j q.val = f := by
    simpa [f] using hq
  have hv :
      (raw (D (R2Coherence.groupPos r (eraseCfgV3 D) j q.val))).label.val =
        (raw (C f)).label.val := by
    rw [hfD]
    exact congrArg (fun x : BoundedAgentState ψ κ => x.label.val) (rawF h f)
  let kc : Fin ((raw (C f)).label.val + 1) :=
    ⟨k.val, by simpa only [hv] using k.isLt⟩
  refine ⟨j, ko, q, ho, kc, ?_⟩
  have hp' : R2Coherence.prefixPos r (eraseCfgV3 D) f k.val = p := by
    simpa only [hfD] using hp
  simpa [f, kc] using (ppF r h f k.val).symm.trans hp'

private theorem pendingBackF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FrameF C D) (o : Fin n) (hp : PendingOpenROwnerV31 r D o) :
    PendingOpenROwnerV31 r C o := by
  rcases hp with ⟨hs, hu, hr⟩
  have hc := ctlF h (r.rightNeighbor o) hs (by decide)
  refine ⟨by simpa [hc] using hs, ?_, ?_⟩
  · unfold successorB at hu ⊢
    simpa only [rawF h o, rawF h (r.rightNeighbor o)] using hu
  · unfold atRootB at hr ⊢
    simpa only [rawF h o] using hr

private theorem safeF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FrameF C D) (o p : Fin n) (hs : SweepOpenRSafeFreshV31 r C o p) :
    SweepOpenRSafeFreshV31 r D o p := by
  rcases hs with hc | hout
  · exact Or.inl (freshF h p hc)
  · exact Or.inr (fun hf => hout (footBackF r h o p hf))

private theorem tailF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FrameF C D) (o f : Fin n)
    (ht : ∀ d : Fin (ψ - (raw (C f)).label.val),
      SweepOpenRSafeFreshV31 r C o (R2Coherence.fwd r f d.val)) :
    ∀ d : Fin (ψ - (raw (D f)).label.val),
      SweepOpenRSafeFreshV31 r D o (R2Coherence.fwd r f d.val) := by
  intro d
  have hv := congrArg (fun x : BoundedAgentState ψ κ => x.label.val) (rawF h f)
  have hd : d.val < ψ - (raw (C f)).label.val := by simpa only [hv] using d.isLt
  let dc : Fin (ψ - (raw (C f)).label.val) := ⟨d.val, hd⟩
  exact safeF r h o _ (by simpa [dc] using ht dc)

private theorem factsF (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FrameF C D) (hf : ReachablePhaseFactsV31 r C) : ReachablePhaseFactsV31 r D := by
  rcases hf with ⟨a,b,c,d,e,f⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    have hc := ctlF h i hi (by decide)
    exact sweptF r h i (a i (by simpa [hc] using hi))
  · intro i hi
    have hc := ctlF h i hi (by decide)
    exact groupF r h i (b i (by simpa [hc] using hi))
  · intro i hi
    have hc := sealCtlF h i hi
    exact groupF r h i (c i (by simpa [hc] using hi))
  · intro i hi
    have hc := ctlF h i hi (by decide)
    rcases d i (by simpa [hc] using hi) with ⟨hm,hg⟩
    exact ⟨by simpa [hc] using hm, groupF r h i hg⟩
  · intro i hi
    have hc := ctlF h i hi (by decide)
    rcases e i (by simpa [hc] using hi) with ⟨hm,hz,hg⟩
    refine ⟨by simpa [hc] using hm, ?_, groupF r h i hg⟩
    rw [rawF h i]
    exact hz
  · intro i hi
    have hc := ctlF h i hi (by decide)
    rcases f i (by simpa [hc] using hi) with ⟨hm,ho⟩
    exact ⟨by simpa [hc] using hm, ownerF r h i ho⟩

private theorem p7F (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FrameF C D) (hp : ScrubLIncomingOpenRFreshV31 r C) :
    ScrubLIncomingOpenRFreshV31 r D := by
  intro o hs hu hr
  have hb := pendingBackF r h o ⟨hs,hu,hr⟩
  exact ownerF r h o (hp o hb.1 hb.2.1 hb.2.2)

private theorem p8F (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FrameF C D) (hp : SweepOpenROverlapFreshV31 r C) :
    SweepOpenROverlapFreshV31 r D := by
  intro s o hs ho
  have hc := ctlF h s hs (by decide)
  have hsC : (C s).ctl.tok = .sweep := by simpa [hc] using hs
  have hoC := pendingBackF r h o ho
  rcases hp s o hsC hoC with ⟨x,y⟩
  exact ⟨safeF r h o s x, safeF r h o (r.rightNeighbor s) y⟩

private theorem p9F (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FrameF C D) (hp : SweepOpenROverlapFreshWideV31 r C) :
    SweepOpenROverlapFreshWideV31 r D := by
  intro s o hs ho
  have hc := ctlF h s hs (by decide)
  have hsC : (C s).ctl.tok = .sweep := by simpa [hc] using hs
  have hoC := pendingBackF r h o ho
  rcases hp s o hsC hoC with ⟨x,y⟩
  exact ⟨safeF r h o (r.rightNeighbor s) x, tailF r h o s y⟩

private theorem r1F (r : DirectedRing n) {C D : FC n ψ κ τ}
    (h : FrameF C D) (hr : OpenRForwardFreshnessClearV31 r C) :
    OpenRForwardFreshnessClearV31 r D := by
  intro o ho d
  have hc := ctlF h o ho (by decide)
  have hoC : (C o).ctl.tok = .openR := by simpa [hc] using ho
  have hv := congrArg (fun x : BoundedAgentState ψ κ => x.label.val) (rawF h o)
  have hd : d.val < ψ - (raw (C o)).label.val := by simpa only [hv] using d.isLt
  let dc : Fin (ψ - (raw (C o)).label.val) := ⟨d.val, hd⟩
  exact freshF h _ (by simpa [dc] using hr o hoC dc)

private theorem stepFrame_of_row
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hr : rowV3 hψ (by decide : 0 < 2) h2 (C e) (C (r.rightNeighbor e)) =
        (C e, C (r.rightNeighbor e)) ∨
      rowV3 hψ (by decide : 0 < 2) h2 (C e) (C (r.rightNeighbor e)) =
        (C e, startClosing (C (r.rightNeighbor e))) ∨
      rowV3 hψ (by decide : 0 < 2) h2 (C e) (C (r.rightNeighbor e)) =
        (startClosing (C e), C (r.rightNeighbor e))) :
    FrameF C (stepV3 hψ h2 r C e) := by
  unfold FrameF
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

private theorem rowOH
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
  rcases hc with ⟨hln,hrn,hlo,hro,hh⟩
  let q := proposalV3 hψ (by decide : 0 < 2) h2 l r
  by_cases he : endpointHazardV3 r.phys q.2
  · left; simp [rowV3, ordinaryStageV3, openStageV3, hln, hrn, hlo, hro, hh, q, he]
  · right; simp [rowV3, ordinaryStageV3, openStageV3, hln, hrn, hlo, hro, hh, q, he]

private theorem frameOH
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .openHazard) :
    FrameF C (stepV3 hψ h2 r C e) := by
  rcases rowOH hψ h2 (C e) (C (r.rightNeighbor e)) hb with h | h
  · exact stepFrame_of_row hψ h2 r C e (Or.inr (Or.inl h))
  · exact stepFrame_of_row hψ h2 r C e (Or.inr (Or.inr h))

private theorem rowMix
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

private theorem frameMix
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hg : ElectionGeometryV31 r C)
    (hb : branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .mixed) :
    FrameF C (stepV3 hψ h2 r C e) := by
  rcases rowMix hψ h2 (C e) (C (r.rightNeighbor e)) (hg e) hb with h | h
  · exact stepFrame_of_row hψ h2 r C e (Or.inl h)
  · exact stepFrame_of_row hψ h2 r C e (Or.inr (Or.inl h))

private theorem relPhys
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .release) :
    ∀ p, (stepV3 hψ h2 r C e p).phys = (C p).phys := by
  have hc : (C (r.rightNeighbor e)).ctl.tok ≠ .seek ∧
      (C e).ctl.tok ≠ .sweep ∧
      (C (r.rightNeighbor e)).ctl.tok ≠ .commit ∧
      (C e).ctl.tok = .release := by
    unfold branchAtV3 at hb
    repeat' split at hb
    all_goals simp_all
    all_goals grind
  have hrow : rowV3 hψ (by decide : 0 < 2) h2
      (C e) (C (r.rightNeighbor e)) =
      releaseStageV3 (C e) (C (r.rightNeighbor e)) := by
    rcases hc with ⟨a,b,c,d⟩
    simp [rowV3,a,b,c,d]
  have hp :
      (releaseStageV3 (C e) (C (r.rightNeighbor e))).1.phys = (C e).phys ∧
      (releaseStageV3 (C e) (C (r.rightNeighbor e))).2.phys =
        (C (r.rightNeighbor e)).phys := by
    unfold releaseStageV3
    repeat' split <;> simp [setControl, startClosing]
  intro p
  by_cases pe : p = e
  · subst p
    simpa [stepV3, protocolV3, PopulationProtocol.step, hrow] using hp.1
  · by_cases pq : p = r.rightNeighbor e
    · subst p
      simpa [stepV3, protocolV3, PopulationProtocol.step, hrow, pe] using hp.2
    · exact congrArg Cell.phys (stepV3_other hψ h2 r C e p pe pq)

private theorem relR1
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hr : OpenRForwardFreshnessClearV31 r C)
    (hb : branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .release) :
    OpenRForwardFreshnessClearV31 r (stepV3 hψ h2 r C e) := by
  intro o ho d
  have hbc : (C (r.rightNeighbor e)).ctl.tok ≠ .seek ∧
      (C e).ctl.tok ≠ .sweep ∧
      (C (r.rightNeighbor e)).ctl.tok ≠ .commit ∧
      (C e).ctl.tok = .release := by
    unfold branchAtV3 at hb
    repeat' split at hb
    all_goals simp_all
    all_goals grind
  have hrow : rowV3 hψ (by decide : 0 < 2) h2
      (C e) (C (r.rightNeighbor e)) =
      releaseStageV3 (C e) (C (r.rightNeighbor e)) := by
    rcases hbc with ⟨a,b,c,z⟩
    simp [rowV3,a,b,c,z]
  have hoC : (C o).ctl.tok = .openR := by
    by_cases pe : o = e
    · subst o
      have heq : stepV3 hψ h2 r C e e =
          (releaseStageV3 (C e) (C (r.rightNeighbor e))).1 := by
        simp [stepV3, protocolV3, PopulationProtocol.step, hrow]
      rw [heq] at ho
      unfold releaseStageV3 at ho
      repeat' split at ho <;> simp_all [setControl, startClosing]
    · by_cases pq : o = r.rightNeighbor e
      · subst o
        have heq : stepV3 hψ h2 r C e (r.rightNeighbor e) =
            (releaseStageV3 (C e) (C (r.rightNeighbor e))).2 := by
          simp [stepV3, protocolV3, PopulationProtocol.step, hrow, pe]
        rw [heq] at ho
        unfold releaseStageV3 at ho
        repeat' split at ho <;> simp_all [setControl, startClosing]
      · rw [stepV3_other hψ h2 r C e o pe pq] at ho
        exact ho
  have hphys := relPhys hψ h2 r C e hb
  have hraw : ∀ p, raw (stepV3 hψ h2 r C e p) = raw (C p) := fun p =>
    congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core) (hphys p)
  have hv := congrArg (fun x : BoundedAgentState ψ κ => x.label.val) (hraw o)
  have hd : d.val < ψ - (raw (C o)).label.val := by
    simpa only [hv] using d.isLt
  let dc : Fin (ψ - (raw (C o)).label.val) := ⟨d.val, hd⟩
  have hold := hr o hoC dc
  unfold FreshnessClearV31 at hold ⊢
  rw [hraw (R2Coherence.fwd r o d.val)]
  simpa [dc] using hold

def FreshPostResidualV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) (b : BranchV3)
    (P : FC n ψ κ τ → Prop) : Prop :=
  ∀ C e, ElectionGeometryV31 r C → ReachableFromQuarantineV31 hψ h2 r C →
    ReachablePhaseFactsFreshV31 r C →
    branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = b → P (stepV3 hψ h2 r C e)

abbrev ReleaseP7FreshV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  FreshPostResidualV31 (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
    hψ h2 r .release (ScrubLIncomingOpenRFreshV31 r)
abbrev ReleaseP8FreshV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  FreshPostResidualV31 (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
    hψ h2 r .release (SweepOpenROverlapFreshV31 r)
abbrev ReleaseP9FreshV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  FreshPostResidualV31 (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
    hψ h2 r .release (SweepOpenROverlapFreshWideV31 r)
abbrev ReleaseSFreshV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  FreshPostResidualV31 (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
    hψ h2 r .release (SeekIncomingSweepOpenROverlapFreshWideV31 r)
abbrev ReleaseR2FreshV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  FreshPostResidualV31 (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ) hψ h2 r .release
    (R2CoherenceV31FreshnessClear.SweepPendingOpenRFootprintOwnedV31F r)

abbrev MixedSFreshV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  FreshPostResidualV31 (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
    hψ h2 r .mixed (SeekIncomingSweepOpenROverlapFreshWideV31 r)
abbrev MixedR1FreshV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  FreshPostResidualV31 (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ)
    hψ h2 r .mixed (OpenRForwardFreshnessClearV31 r)
abbrev MixedR2FreshV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  FreshPostResidualV31 (n:=n) (ψ:=ψ) (κ:=κ) (τ:=τ) hψ h2 r .mixed
    (R2CoherenceV31FreshnessClear.SweepPendingOpenRFootprintOwnedV31F r)

def OpenHazardFreshSeekPrepaidFreshV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e pred owner : Fin n),
    ReachableFromQuarantineV31 hψ h2 r C → ElectionGeometryV31 r C →
    ReachablePhaseFactsFreshV31 r C →
    branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .openHazard →
    let D : FC n ψ κ τ := stepV3 hψ h2 r C e
    (D (r.rightNeighbor pred)).ctl.tok = .seek →
    (C (r.rightNeighbor pred)).ctl.tok ≠ .seek →
    PendingOpenROwnerV31 r D owner →
      (atRootB (D (r.rightNeighbor pred)) = true →
        SweepOpenRSafeFreshV31 r D owner
          (r.rightNeighbor (r.rightNeighbor pred)) ∧
        ∀ d : Fin (ψ - (raw (D (r.rightNeighbor pred))).label.val),
          SweepOpenRSafeFreshV31 r D owner
            (R2Coherence.fwd r (r.rightNeighbor pred) d.val)) ∧
      (atRootB (D (r.rightNeighbor pred)) = false →
        atRootB (D pred) = true →
        SweepOpenRSafeFreshV31 r D owner (r.rightNeighbor pred) ∧
        ∀ d : Fin (ψ - (raw (D pred)).label.val),
          SweepOpenRSafeFreshV31 r D owner (R2Coherence.fwd r pred d.val))

private theorem ohS
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hn : OpenHazardFreshSeekPrepaidFreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (C : FC n ψ κ τ) (e : Fin n) (ht : ReachableFromQuarantineV31 hψ h2 r C)
    (hg : ElectionGeometryV31 r C) (hf : ReachablePhaseFactsFreshV31 r C)
    (hs : SeekIncomingSweepOpenROverlapFreshWideV31 r C)
    (hb : branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .openHazard) :
    SeekIncomingSweepOpenROverlapFreshWideV31 r (stepV3 hψ h2 r C e) := by
  let D := stepV3 hψ h2 r C e
  have fr : FrameF C D := by simpa [D] using frameOH hψ h2 r C e hb
  intro p o hseek hp
  by_cases hc : (C (r.rightNeighbor p)).ctl.tok = .seek
  · have old := hs p o hc (pendingBackF r fr o hp)
    constructor
    · intro hr
      have hrC : atRootB (C (r.rightNeighbor p)) = true := by
        change atRootB (D (r.rightNeighbor p)) = true at hr
        unfold atRootB at hr ⊢
        rw [rawF fr (r.rightNeighbor p)] at hr
        exact hr
      rcases old.1 hrC with ⟨x,y⟩
      exact ⟨safeF r fr o _ x, tailF r fr o (r.rightNeighbor p) y⟩
    · intro hnroot hroot
      have hnC : atRootB (C (r.rightNeighbor p)) = false := by
        change atRootB (D (r.rightNeighbor p)) = false at hnroot
        unfold atRootB at hnroot ⊢
        rw [rawF fr (r.rightNeighbor p)] at hnroot
        exact hnroot
      have hrC : atRootB (C p) = true := by
        change atRootB (D p) = true at hroot
        unfold atRootB at hroot ⊢
        rw [rawF fr p] at hroot
        exact hroot
      rcases old.2 hnC hrC with ⟨x,y⟩
      exact ⟨safeF r fr o _ x, tailF r fr o p y⟩
  · exact hn C e p o ht hg hf hb hseek hc hp


theorem releaseStep_reachable_fresh_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (p7 : ReleaseP7FreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (p8 : ReleaseP8FreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (p9 : ReleaseP9FreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (s : ReleaseSFreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (r2 : ReleaseR2FreshV31 (κ:=κ) (τ:=τ) hψ h2 r) :
    StepPreservesV31_release_fresh (κ:=κ) (τ:=τ) hψ h2 r := by
  intro C e hg ht hf hb
  have a := p7 C e hg ht hf hb; have b := p8 C e hg ht hf hb
  have c := p9 C e hg ht hf hb; have d := s C e hg ht hf hb
  have g := r2 C e hg ht hf hb
  rcases hf with ⟨f,p7o,p8o,p9o,so,r1o,r2o⟩
  have fD := R2CoherenceV31ReachableRelease.reachablePhaseFacts_release_step hψ h2 r C e f hb
  exact ⟨fD,a,b,c,d,relR1 hψ h2 r C e r1o hb,g⟩


theorem mixedStep_reachable_fresh_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (s : MixedSFreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (r1 : MixedR1FreshV31 (κ:=κ) (τ:=τ) hψ h2 r)
    (r2 : MixedR2FreshV31 (κ:=κ) (τ:=τ) hψ h2 r) :
    StepPreservesV31_mixed_fresh (κ:=κ) (τ:=τ) hψ h2 r := by
  intro C e hg ht hf hb
  have fr := frameMix hψ h2 r C e hg hb
  have sd := s C e hg ht hf hb; have r1d := r1 C e hg ht hf hb
  have r2d := r2 C e hg ht hf hb
  rcases hf with ⟨f,p7,p8,p9,so,r1o,r2o⟩
  exact ⟨factsF r fr f, p7F r fr p7, p8F r fr p8, p9F r fr p9, sd, r1d, r2d⟩

theorem openHazardStep_reachable_fresh_of_residuals
   (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
   (hn : OpenHazardFreshSeekPrepaidFreshV31 (κ:=κ) (τ:=τ) hψ h2 r) :
   StepPreservesV31_openHazard_fresh (κ:=κ) (τ:=τ) hψ h2 r := by
  intro C e hg ht hf hb
  have fr := frameOH hψ h2 r C e hb
  have hsOld : SeekIncomingSweepOpenROverlapFreshWideV31 r C :=
    hf.2.2.2.2.1
  have sd := ohS hψ h2 r hn C e ht hg hf hsOld hb
  rcases hf with ⟨f,p7,p8,p9,s,r1,r2⟩
  have r2d : SweepPendingOpenRFootprintOwnedV31F r
      (stepV3 hψ h2 r C e) := by
    intro sw o p hsw hp hr hfoot
    have hc := ctlF fr sw hsw (by decide)
    have hswC : (C sw).ctl.tok = .sweep := by
      rw [hc] at hsw
      exact hsw
    have hpC := pendingBackF r fr o hp
    have hrC :
        R2CoherenceV31ReachableOpenNoHazard3.InSweepWideReadV31
          r C sw p := by
      rcases hr with h | ⟨d,hd⟩
      · exact Or.inl h
      · right
        have hv := congrArg Fin.val (labF fr sw)
        exact ⟨⟨d.val, by simpa only [hv] using d.isLt⟩, hd⟩
    have hfC := footBackF r fr o p hfoot
    rcases r2 sw o p hswC hpC hrC hfC with ho | hc
    · left
      rcases (fr p).2 with heq | hseek
      · unfold PhaseOwnedV31 at ho ⊢
        rw [heq]
        exact ho
      · simp [PhaseOwnedV31,hseek]
    · exact Or.inr (freshF fr p hc)
  exact ⟨factsF r fr f,p7F r fr p7,p8F r fr p8,p9F r fr p9,
    sd,r1F r fr r1,r2d⟩

end R2CoherenceV31ReachableFreshBranches2
