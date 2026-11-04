import Leader.Wu.Coherence.ReachableStrongOwnership
import Leader.Wu.Coherence.ReachablePrepaid

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableScrubL

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4

variable {n ψ κ τ : Nat}

private theorem scrubCond12
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .scrubL) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok ≠ .release ∧
      r.ctl.tok = .scrubL := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowScrub12
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .scrubL) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = scrubLStageV3 l r := by
  rcases scrubCond12 hψ h2 l r hb with ⟨hs, hw, hc, hr, hsl⟩
  simp [rowV3, hs, hw, hc, hr, hsl]

/-- Reachability removes the two malformed scrub arms.  The active responder
is nonroot by the old scrub clause, while ElectionGeometry makes the edge a
successor. -/
private theorem scrubGood12
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hFacts : ReachablePhaseFactsV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL) :
    successorB (C e) (C (ring.rightNeighbor e)) = true ∧
      atRootB (C (ring.rightNeighbor e)) = false ∧
      GroupOwnedClearV31 ring C (ring.rightNeighbor e) := by
  have ht := (scrubCond12 hψ h2 (C e) (C (ring.rightNeighbor e)) hb).2.2.2.2
  have hh := hFacts.2.2.2.2.1 (ring.rightNeighbor e) ht
  have hr : atRootB (C (ring.rightNeighbor e)) = false := by
    cases h : atRootB (C (ring.rightNeighbor e)) with
    | false => rfl
    | true =>
        have hz : (raw (C (ring.rightNeighbor e))).label.val = 0 := by
          simpa [atRootB] using h
        exact (hh.2.1 hz).elim
  have hs : successorB (C e) (C (ring.rightNeighbor e)) = true := by
    simpa [ElectionGeometryV31, passiveEdgeOKV3, hr] using hGeom e
  exact ⟨hs, hr, hh.2.2⟩

private theorem edgeNe12 (C : FC n ψ κ τ) (ring : DirectedRing n) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro h
  have heq := congrArg (fun p : Fin n => (raw (C p)).label.val) h
  have hv : (raw (C (ring.rightNeighbor e))).label.val =
      (raw (C e)).label.val + 1 := by simpa [successorB] using hs
  omega

/-- `scrubLStageV3`, `R2CoherenceV31.lean:165-179`: on the reachable arm
both served cells are cleared; the left becomes openR at root, otherwise the
scrub debt moves left.  Off the pair we use `stepV3_other`, lines 329-334. -/
private theorem left12
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e e =
      if atRootB (C e) then
        setControl (clearMain (C e)) .releasing .openR
      else setControl (clearMain (C e)) .releasing .scrubL := by
  have hrow := rowScrub12 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, scrubLStageV3, hs, hr]

private theorem right12
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      setControl (clearMain (C (ring.rightNeighbor e))) .releasing .none := by
  have hrow := rowScrub12 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  have hne := Ne.symm (edgeNe12 C ring e hs)
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, scrubLStageV3, hs, hr, hne]

private theorem clearOwned12 (u : Cell ψ κ τ) (t : TokenV3) :
    MainClearV3 (setControl (clearMain u) .releasing t) ∧
      PhaseOwnedV31 (setControl (clearMain u) .releasing t) := by
  constructor
  · unfold MainClearV3 R2CoherenceBranches.MainClear
    simp [eraseCellV3, setControl, clearMain, R2Coherence.clearMainPhys,
      PPLLExpiringComparisonRepair.clearComparisonCarrier, R2Coherence.raw]
  · simp [PhaseOwnedV31, setControl]

private theorem gp12
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

private theorem pp12
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [hLab i]

private theorem groupStartSucc12
    (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    R2Coherence.groupStart ring (eraseCfgV3 C) e =
      R2Coherence.groupStart ring (eraseCfgV3 C) (ring.rightNeighbor e) := by
  unfold R2Coherence.groupStart
  change R2Coherence.back ring e (raw (C e)).label.val =
    R2Coherence.back ring (ring.rightNeighbor e)
      (raw (C (ring.rightNeighbor e))).label.val
  have hv : (raw (C (ring.rightNeighbor e))).label.val =
      (raw (C e)).label.val + 1 := by simpa [successorB] using hs
  rw [hv]
  exact (R2CoherenceV31ReachableOpenNoHazard.back_rightNeighbor_succ_reach
    ring e (raw (C e)).label.val).symm

private theorem reindexGroup12
    (ring : DirectedRing n) (C : FC n ψ κ τ) (a b : Fin n)
    (hs : R2Coherence.groupStart ring (eraseCfgV3 C) a =
      R2Coherence.groupStart ring (eraseCfgV3 C) b)
    (h : GroupOwnedClearV31 ring C b) : GroupOwnedClearV31 ring C a := by
  intro k
  have hk := h k
  change MainClearV3 (C (R2Coherence.groupPos ring (eraseCfgV3 C) a k.val)) ∧
    PhaseOwnedV31 (C (R2Coherence.groupPos ring (eraseCfgV3 C) a k.val))
  change MainClearV3 (C (R2Coherence.groupPos ring (eraseCfgV3 C) b k.val)) ∧
    PhaseOwnedV31 (C (R2Coherence.groupPos ring (eraseCfgV3 C) b k.val)) at hk
  unfold R2Coherence.groupPos at hk ⊢
  rw [hs]
  exact hk

private theorem mono12
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false)
    (h : MainClearV3 (C p) ∧ PhaseOwnedV31 (C p)) :
    MainClearV3 (stepV3 hψ h2 ring C e p) ∧
      PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
  by_cases hp : p = e
  · subst p
    rw [left12 hψ h2 ring C e hb hs hr]
    cases hroot : atRootB (C e) <;> simp [hroot]
    · exact clearOwned12 (C e) .scrubL
    · exact clearOwned12 (C e) .openR
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      rw [right12 hψ h2 ring C e hb hs hr]
      exact clearOwned12 _ .none
    · rw [stepV3_other hψ h2 ring C e p hp hpr]
      exact h

private theorem groupTransport12
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (hMono : ∀ p, MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
      MainClearV3 (D p) ∧ PhaseOwnedV31 (D p))
    (i : Fin n) (h : GroupOwnedClearV31 ring C i) :
    GroupOwnedClearV31 ring D i := by
  intro k
  have hk := h k
  change MainClearV3 (D (R2Coherence.groupPos ring (eraseCfgV3 D) i k.val)) ∧
    PhaseOwnedV31 (D (R2Coherence.groupPos ring (eraseCfgV3 D) i k.val))
  rw [gp12 ring hLab i k.val]
  exact hMono _ hk

private theorem sweptTransport12
    (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (hLab : ∀ p, (raw (D p)).label = (raw (C p)).label)
    (hMono : ∀ p, MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
      MainClearV3 (D p) ∧ PhaseOwnedV31 (D p))
    (i : Fin n) (h : SweptPrefixOwnedClearV31 ring C i) :
    SweptPrefixOwnedClearV31 ring D i := by
  intro kD
  have hv := congrArg Fin.val (hLab i)
  have hk : kD.val < (raw (C i)).label.val := by simpa only [hv] using kD.isLt
  let kC : Fin (raw (C i)).label.val := ⟨kD.val, hk⟩
  have hOld := h kC
  change MainClearV3 (D (R2Coherence.groupPos ring (eraseCfgV3 D) i kD.val)) ∧
    PhaseOwnedV31 (D (R2Coherence.groupPos ring (eraseCfgV3 D) i kD.val))
  rw [gp12 ring hLab i kD.val]
  exact hMono _ (by simpa [kC] using hOld)

private theorem oldToken12
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n) (t : TokenV3)
    (ho : t ≠ .openR) (hsl : t ≠ .scrubL) (hn : t ≠ .none)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false)
    (ht : (stepV3 hψ h2 ring C e p).ctl.tok = t) :
    stepV3 hψ h2 ring C e p = C p := by
  by_cases hp : p = e
  · subst p
    rw [left12 hψ h2 ring C e hb hs hr] at ht
    cases hroot : atRootB (C e) <;> simp_all [hroot, setControl]
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      rw [right12 hψ h2 ring C e hb hs hr] at ht
      simp_all [setControl]
    · exact stepV3_other hψ h2 ring C e p hp hpr

private theorem sealedSource12
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false)
    (hm : (stepV3 hψ h2 ring C e p).ctl.mark = .sealed) :
    stepV3 hψ h2 ring C e p = C p := by
  by_cases hp : p = e
  · subst p
    rw [left12 hψ h2 ring C e hb hs hr] at hm
    cases hroot : atRootB (C e) <;> simp_all [hroot, setControl]
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      rw [right12 hψ h2 ring C e hb hs hr] at hm
      simp_all [setControl]
    · exact stepV3_other hψ h2 ring C e p hp hpr

private theorem freshFalse12 (u : Cell ψ κ τ) (k : Nat)
    (hm : MainClearV3 u)
    (hf : R2Coherence.freshComponent (eraseCellV3 u) k) : False := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at hm
  unfold R2Coherence.freshComponent at hf
  change (raw u).label.val = k ∧
    (match (raw u).path with
     | .bot => False
     | .some lab b => lab.val = k ∧ b.val = (if (raw u).bit then 1 else 0)) at hf
  have hPath : (raw u).path = .bot := by
    simpa [raw, eraseCellV3, R2Coherence.raw] using hm.2.1
  rw [hPath] at hf
  exact hf.2


private theorem ownerFresh12
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false)
    (hce : MainClearV3 (C e))
    (hcr : MainClearV3 (C (ring.rightNeighbor e)))
    (hf : OpenROwnerFreshV3 ring C owner) :
    OpenROwnerFreshV3 ring (stepV3 hψ h2 ring C e) owner := by
  let D := stepV3 hψ h2 ring C e
  have hLab : ∀ p, (raw (D p)).label = (raw (C p)).label := by
    intro p; simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  have hSE : (raw (D e)).state = .none := by
    dsimp [D]; rw [left12 hψ h2 ring C e hb hs hr]
    cases hroot : atRootB (C e) <;> simp [hroot, setControl, clearMain, raw]
  have hSR : (raw (D (ring.rightNeighbor e))).state = .none := by
    dsimp [D]; rw [right12 hψ h2 ring C e hb hs hr]
    simp [setControl, clearMain, raw]
  unfold OpenROwnerFreshV3 at hf ⊢
  intro j ko hHitD
  have hgp := gp12 ring hLab j ko.val
  rw [hgp] at hHitD
  have hg := hf j ko hHitD
  unfold GroupIntrinsicFreshV3 at hg ⊢
  intro q
  have hgpq := gp12 ring hLab j q.val
  rw [hgpq]
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  change IntrinsicFreshAtV3 ring D front
  have hOld : IntrinsicFreshAtV3 ring C front := by simpa [front] using hg q
  unfold IntrinsicFreshAtV3 at hOld ⊢
  intro hEqD
  by_cases hfe : front = e
  · rw [hfe, hSE] at hEqD; cases hEqD
  · by_cases hfr : front = ring.rightNeighbor e
    · rw [hfr, hSR] at hEqD; cases hEqD
    · have hFront : D front = C front := by
        dsimp [D]; exact stepV3_other hψ h2 ring C e front hfe hfr
      have hEqC : (raw (C front)).state = .equal := by simpa [hFront] using hEqD
      have hOldAt := hOld hEqC
      intro kD
      have hv := congrArg Fin.val (hLab front)
      have hkC : kD.val < (raw (C front)).label.val + 1 := by
        simpa only [hv] using kD.isLt
      let kC : Fin ((raw (C front)).label.val + 1) := ⟨kD.val, hkC⟩
      have hOldK := hOldAt kC
      have hpp := pp12 ring hLab front kD.val
      rw [hpp]
      let p := R2Coherence.prefixPos ring (eraseCfgV3 C) front kD.val
      change R2Coherence.freshComponent (eraseCellV3 (D p)) kD.val
      have hOldK' : R2Coherence.freshComponent (eraseCellV3 (C p)) kD.val := by
        simpa [p, kC] using hOldK
      by_cases hpe : p = e
      · exact (freshFalse12 (C p) kD.val (by simpa [hpe] using hce) hOldK').elim
      · by_cases hpr : p = ring.rightNeighbor e
        · exact (freshFalse12 (C p) kD.val (by simpa [hpr] using hcr) hOldK').elim
        · have hp : D p = C p := by
            dsimp [D]; exact stepV3_other hψ h2 ring C e p hpe hpr
          simpa [hp, p] using hOldK'

/-- The six original reachable facts close under the reachable scrub arm.
The root handoff gets its new openR freshness exactly from
`ScrubLIncomingOpenRFreshV31`. -/
theorem reachablePhaseFacts_scrubL_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (_hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL) :
    ReachablePhaseFactsV31 ring (stepV3 hψ h2 ring C e) := by
  have hFacts := hPlus.1.1.1.1
  have hIncoming := hPlus.1.1.1.2
  have hg := scrubGood12 hψ h2 ring C e hGeom hFacts hb
  have hs := hg.1
  have hr := hg.2.1
  have hGR := hg.2.2
  have hGE := reindexGroup12 ring C e (ring.rightNeighbor e)
    (groupStartSucc12 ring C e hs) hGR

  have modLeft (a b n : Nat) : (a % n + b) % n = (a + b) % n := by
    rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
    exact (Nat.add_mod a b n).symm
  have modRight (a b n : Nat) : (a + b % n) % n = (a + b) % n := by
    rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
    exact (Nat.add_mod a b n).symm
  have prefixGroup
      (CR : R2Coherence.FC n ψ κ τ) (i : Fin n) (k : Nat)
      (hk : k ≤ (R2Coherence.raw (CR i)).label.val) :
      R2Coherence.prefixPos ring CR i k =
        R2Coherence.groupPos ring CR i k := by
    let L := (R2Coherence.raw (CR i)).label.val
    let A := i.val + n
    let a := (L - k) % n
    let b := k % n
    have hkL : k ≤ L := by simpa [L] using hk
    have hn : 0 < n := ring.hn
    have ha : a < n := by
      dsimp [a]
      exact Nat.mod_lt _ hn
    have hb' : b < n := by
      dsimp [b]
      exact Nat.mod_lt _ hn
    have hA : n ≤ A := by
      dsimp [A]
      omega
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
            (A - (L % n) + k) % n := modLeft (A - (L % n)) k n
        _ = (A - (L % n) + b) % n := by
          simpa [b] using (modRight (A - (L % n)) k n).symm
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
            (A - (L % n) + k) % n := modLeft (A - (L % n)) k n
        _ = (A - (L % n) + b) % n := by
          simpa [b] using (modRight (A - (L % n)) k n).symm
        _ = (A - a) % n := by
          rw [hLm]
          have hnum : A - (a + b - n) + b = n + (A - a) := by omega
          rw [hnum, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  have groupSelf (i : Fin n) :
      R2Coherence.groupPos ring (eraseCfgV3 C) i
          (raw (C i)).label.val = i := by
    rw [← prefixGroup (eraseCfgV3 C) i (raw (C i)).label.val
      (Nat.le_refl _)]
    apply Fin.ext
    change (i.val + n -
      ((raw (C i)).label.val - (raw (C i)).label.val) % n) % n = i.val
    simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  have hce : MainClearV3 (C e) := by
    have h := (hGE (raw (C e)).label).1
    change MainClearV3
      (C (R2Coherence.groupPos ring (eraseCfgV3 C) e
        (raw (C e)).label.val)) at h
    rw [groupSelf e] at h
    exact h
  have hcr : MainClearV3 (C (ring.rightNeighbor e)) := by
    have h := (hGR (raw (C (ring.rightNeighbor e))).label).1
    change MainClearV3
      (C (R2Coherence.groupPos ring (eraseCfgV3 C) (ring.rightNeighbor e)
        (raw (C (ring.rightNeighbor e))).label.val)) at h
    rw [groupSelf (ring.rightNeighbor e)] at h
    exact h

  have hLab := stepV3_labels_eq_or_held hψ h2 ring C e
  have hMono : ∀ p : Fin n,
      MainClearV3 (C p) ∧ PhaseOwnedV31 (C p) →
      MainClearV3 (stepV3 hψ h2 ring C e p) ∧
        PhaseOwnedV31 (stepV3 hψ h2 ring C e p) := by
    intro p hp
    exact mono12 hψ h2 ring C e p hb hs hr hp
  rcases hFacts with ⟨hSweep, hCommit, hSealed, hRelease, hScrub, hOpenR⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have heq := oldToken12 hψ h2 ring C e i .sweep (by decide) (by decide)
      (by decide) hb hs hr hi
    have hiC := hi
    rw [heq] at hiC
    exact sweptTransport12 ring hLab hMono i (hSweep i hiC)
  · intro i hi
    have heq := oldToken12 hψ h2 ring C e i .commit (by decide) (by decide)
      (by decide) hb hs hr hi
    have hiC := hi
    rw [heq] at hiC
    exact groupTransport12 ring hLab hMono i (hCommit i hiC)
  · intro i hi
    have heq := sealedSource12 hψ h2 ring C e i hb hs hr hi
    have hiC := hi
    rw [heq] at hiC
    exact groupTransport12 ring hLab hMono i (hSealed i hiC)
  · intro i hi
    have heq := oldToken12 hψ h2 ring C e i .release (by decide) (by decide)
      (by decide) hb hs hr hi
    have hiC := hi
    rw [heq] at hiC
    rcases hRelease i hiC with ⟨hm, hgroup⟩
    exact ⟨by simpa [heq] using hm,
      groupTransport12 ring hLab hMono i hgroup⟩
  · intro i hi
    by_cases hie : i = e
    · subst i
      cases hroot : atRootB (C e) with
      | true =>
          have hx := hi
          rw [left12 hψ h2 ring C e hb hs hr] at hx
          simp [hroot, setControl] at hx
      | false =>
          have hzC : (raw (C e)).label.val ≠ 0 := by
            intro hz
            have ht : atRootB (C e) = true := by simp [atRootB, hz]
            rw [hroot] at ht
            cases ht
          refine ⟨?_, ?_, groupTransport12 ring hLab hMono e hGE⟩
          · rw [left12 hψ h2 ring C e hb hs hr]
            simp [hroot, setControl]
          · have hv := congrArg Fin.val (hLab e)
            intro hzD
            apply hzC
            rw [← hv]
            exact hzD
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        have hx := hi
        rw [right12 hψ h2 ring C e hb hs hr] at hx
        simp [setControl] at hx
      · have heq := stepV3_other hψ h2 ring C e i hie hir
        have hiC := hi
        rw [heq] at hiC
        rcases hScrub i hiC with ⟨hm, hz, hgroup⟩
        refine ⟨by simpa [heq] using hm, ?_,
          groupTransport12 ring hLab hMono i hgroup⟩
        have hv := congrArg Fin.val (hLab i)
        simpa only [hv] using hz
  · intro i hi
    by_cases hie : i = e
    · subst i
      cases hroot : atRootB (C e) with
      | false =>
          have hx := hi
          rw [left12 hψ h2 ring C e hb hs hr] at hx
          simp [hroot, setControl] at hx
      | true =>
          have ht := (scrubCond12 hψ h2 (C e) (C (ring.rightNeighbor e)) hb).2.2.2.2
          have hf := hIncoming e ht hs hroot
          refine ⟨?_, ownerFresh12 hψ h2 ring C e e hb hs hr hce hcr hf⟩
          rw [left12 hψ h2 ring C e hb hs hr]
          simp [hroot, setControl]
    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        have hx := hi
        rw [right12 hψ h2 ring C e hb hs hr] at hx
        simp [setControl] at hx
      · have heq := stepV3_other hψ h2 ring C e i hie hir
        have hiC := hi
        rw [heq] at hiC
        rcases hOpenR i hiC with ⟨hm, hf⟩
        exact ⟨by simpa [heq] using hm,
          ownerFresh12 hψ h2 ring C e i hb hs hr hce hcr hf⟩


/-- STOP: first clause after the six base facts which is not prepaid.

On the nonroot continuation, `scrubLStageV3` moves `.scrubL` from the responder
to the initiator.  If that initiator is label 1, its root predecessor becomes
a new pending openR owner.  Pre-state `ScrubLIncomingOpenRFreshV31` did not
apply to this predecessor unless the initiator already carried `.scrubL`.
The current scrub owner's `GroupOwnedClearV31` is insufficient for arbitrary
overlapping freshness windows (the obstruction isolated earlier), while S,
R1 and strong R2 are guarded respectively by seek, current openR, and
live-sweep/pending-owner hypotheses.  Thus the exact missing prepayment is: -/
def ScrubLContinuationIncomingFreshPrepayV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e owner : Fin n),
    ReachableFromQuarantineV31 hψ h2 ring C →
    ElectionGeometryV31 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL →
    ring.rightNeighbor owner = e →
    atRootB (C owner) = true →
    successorB (C owner) (C e) = true →
    atRootB (C e) = false →
    (C e).ctl.tok ≠ .scrubL →
      OpenROwnerFreshV3 ring C owner

/- `scrubLStep_reachable_full` intentionally stops here.  This is the next
payload field `ScrubLIncomingOpenRFreshV31`; pointwise/wide overlap, S, R1 and
strong R2 are not attempted after the first unclosed obligation. -/

end R2CoherenceV31ReachableScrubL
