import Leader.Wu.Coherence.ReachableScrubL
import Leader.Wu.Coherence.ReachableSound
import Leader.Wu.Coherence.ReachableSealed
import Leader.Wu.Coherence.ReachableOpenHazardPrepaid
import Leader.Wu.Coherence.ReachableMixed
import Leader.Wu.Coherence.ReachableCommitOverlap
import Leader.Wu.Coherence.ReachableRelease

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableScrubL2

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
open R2CoherenceV31ReachableScrubL R2CoherenceV31ReachableSound

variable {n ψ κ τ : Nat}

private theorem row2 (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ) (hb : branchAtV3 hψ h2 l r = .scrubL) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = scrubLStageV3 l r := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all [rowV3]
  all_goals grind

private theorem edgeNe2 (C : FC n ψ κ τ) (ring : DirectedRing n) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    e ≠ ring.rightNeighbor e := by
  intro h
  have he := congrArg (fun p : Fin n => (raw (C p)).label.val) h
  have hv : (raw (C (ring.rightNeighbor e))).label.val =
      (raw (C e)).label.val + 1 := by simpa [successorB] using hs
  omega

private theorem left2 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e e =
      if atRootB (C e) then setControl (clearMain (C e)) .releasing .openR
      else setControl (clearMain (C e)) .releasing .scrubL := by
  have hrow := row2 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, scrubLStageV3, hs, hr]

private theorem right2 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      setControl (clearMain (C (ring.rightNeighbor e))) .releasing .none := by
  have hrow := row2 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  have hne := Ne.symm (edgeNe2 C ring e hs)
  simp [stepV3, protocolV3, PopulationProtocol.step,
    hrow, scrubLStageV3, hs, hr, hne]

private theorem mc2 (u : Cell ψ κ τ) (t : TokenV3) :
    MainClearV3 (setControl (clearMain u) .releasing t) := by
  unfold MainClearV3 R2CoherenceBranches.MainClear
  simp [eraseCellV3, setControl, clearMain, R2Coherence.clearMainPhys,
    PPLLExpiringComparisonRepair.clearComparisonCarrier, R2Coherence.raw]

private theorem gp2 (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label) (i : Fin n) (k : Nat) :
    R2Coherence.groupPos ring (eraseCfgV3 D) i k =
      R2Coherence.groupPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.groupPos R2Coherence.groupStart
  change R2Coherence.fwd ring (R2Coherence.back ring i (raw (D i)).label.val) k =
    R2Coherence.fwd ring (R2Coherence.back ring i (raw (C i)).label.val) k
  rw [h i]

private theorem pp2 (ring : DirectedRing n) {C D : FC n ψ κ τ}
    (h : ∀ p, (raw (D p)).label = (raw (C p)).label) (i : Fin n) (k : Nat) :
    R2Coherence.prefixPos ring (eraseCfgV3 D) i k =
      R2Coherence.prefixPos ring (eraseCfgV3 C) i k := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i ((raw (D i)).label.val - k) =
    R2Coherence.back ring i ((raw (C i)).label.val - k)
  rw [h i]

private theorem freshFalse2 (u : Cell ψ κ τ) (k : Nat)
    (hm : MainClearV3 u)
    (hf : R2Coherence.freshComponent (eraseCellV3 u) k) : False := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at hm
  unfold R2Coherence.freshComponent at hf
  change (raw u).label.val = k ∧
    (match (raw u).path with
     | .bot => False
     | .some lab b =>
         lab.val = k ∧ b.val = (if (raw u).bit then 1 else 0)) at hf
  have hp : (raw u).path = .bot := by
    simpa [raw, eraseCellV3, R2Coherence.raw] using hm.2.1
  rw [hp] at hf
  exact hf.2

private theorem ownerFresh2 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false)
    (hce : MainClearV3 (C e)) (hcr : MainClearV3 (C (ring.rightNeighbor e)))
    (hf : OpenROwnerFreshV3 ring C owner) :
    OpenROwnerFreshV3 ring (stepV3 hψ h2 ring C e) owner := by
  let D := stepV3 hψ h2 ring C e
  have hL : ∀ p, (raw (D p)).label = (raw (C p)).label := by
    intro p; simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  have hSE : (raw (D e)).state = .none := by
    dsimp [D]; rw [left2 hψ h2 ring C e hb hs hr]
    cases h : atRootB (C e) <;> simp [h, setControl, clearMain, raw]
  have hSR : (raw (D (ring.rightNeighbor e))).state = .none := by
    dsimp [D]; rw [right2 hψ h2 ring C e hb hs hr]
    simp [setControl, clearMain, raw]
  unfold OpenROwnerFreshV3 at hf ⊢
  intro j ko hHit
  rw [gp2 ring hL j ko.val] at hHit
  have hg := hf j ko hHit
  unfold GroupIntrinsicFreshV3 at hg ⊢
  intro q
  rw [gp2 ring hL j q.val]
  let f := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  change IntrinsicFreshAtV3 ring D f
  have ho : IntrinsicFreshAtV3 ring C f := by simpa [f] using hg q
  unfold IntrinsicFreshAtV3 at ho ⊢
  intro heq
  by_cases hfe : f = e
  · rw [hfe, hSE] at heq; cases heq
  · by_cases hfr : f = ring.rightNeighbor e
    · rw [hfr, hSR] at heq; cases heq
    · have hFC : D f = C f := by
        dsimp [D]; exact stepV3_other hψ h2 ring C e f hfe hfr
      have heqC : (raw (C f)).state = .equal := by simpa [hFC] using heq
      intro kD
      have hv := congrArg Fin.val (hL f)
      have hk : kD.val < (raw (C f)).label.val + 1 := by
        simpa only [hv] using kD.isLt
      let kC : Fin ((raw (C f)).label.val + 1) := ⟨kD.val, hk⟩
      have hOld := ho heqC kC
      rw [pp2 ring hL f kD.val]
      let p := R2Coherence.prefixPos ring (eraseCfgV3 C) f kD.val
      change R2Coherence.freshComponent (eraseCellV3 (D p)) kD.val
      have hOld' : R2Coherence.freshComponent (eraseCellV3 (C p)) kD.val := by
        simpa [p, kC] using hOld
      by_cases hpe : p = e
      · exact (freshFalse2 (C p) kD.val (by simpa [hpe] using hce) hOld').elim
      · by_cases hpr : p = ring.rightNeighbor e
        · exact (freshFalse2 (C p) kD.val (by simpa [hpr] using hcr) hOld').elim
        · have hp : D p = C p := by
            dsimp [D]; exact stepV3_other hψ h2 ring C e p hpe hpr
          simpa [hp, p] using hOld'

private theorem groupSelf2
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    R2Coherence.groupPos ring (eraseCfgV3 C) i (raw (C i)).label.val = i := by
  let L := (raw (C i)).label.val
  have modLeft (a b : Nat) :
      (a % n + b) % n = (a + b) % n := by
    rw [Nat.add_mod (a % n) b n, Nat.mod_mod]
    exact (Nat.add_mod a b n).symm
  have modRight (a b : Nat) :
      (a + b % n) % n = (a + b) % n := by
    rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
    exact (Nat.add_mod a b n).symm
  apply Fin.ext
  change ((((i.val + n - (L % n)) % n) + L) % n) = i.val
  rw [modLeft (i.val + n - (L % n)) L]
  rw [← modRight (i.val + n - (L % n)) L]
  have hm : L % n ≤ i.val + n := by
    have hlt := Nat.mod_lt L ring.hn
    omega
  rw [Nat.sub_add_cancel hm]
  rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_self,
    Nat.add_zero, Nat.mod_eq_of_lt i.isLt]

private theorem startSucc2 (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true) :
    R2Coherence.groupStart ring (eraseCfgV3 C) e =
      R2Coherence.groupStart ring (eraseCfgV3 C) (ring.rightNeighbor e) := by
  unfold R2Coherence.groupStart
  change R2Coherence.back ring e (raw (C e)).label.val =
    R2Coherence.back ring (ring.rightNeighbor e)
      (raw (C (ring.rightNeighbor e))).label.val
  have hv : (raw (C (ring.rightNeighbor e))).label.val =
      (raw (C e)).label.val + 1 := by
    simpa [successorB] using hs
  rw [hv]
  exact (R2CoherenceV31ReachableOpenNoHazard.back_rightNeighbor_succ_reach
    ring e (raw (C e)).label.val).symm

private theorem reindex2 (ring : DirectedRing n) (C : FC n ψ κ τ) (a b : Fin n)
    (hs : R2Coherence.groupStart ring (eraseCfgV3 C) a =
      R2Coherence.groupStart ring (eraseCfgV3 C) b)
    (h : GroupOwnedClearV31 ring C b) : GroupOwnedClearV31 ring C a := by
  intro k
  have hk := h k
  unfold R2Coherence.groupPos at hk ⊢
  rw [hs]
  exact hk

private theorem prep2 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (hGeom : ElectionGeometryV31 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL) :
    successorB (C e) (C (ring.rightNeighbor e)) = true ∧
    atRootB (C (ring.rightNeighbor e)) = false ∧ GroupOwnedClearV31 ring C e ∧
    MainClearV3 (C e) ∧ MainClearV3 (C (ring.rightNeighbor e)) := by
  have hg := scrubL_guard_prepays_current_owner hψ h2 ring C e hPlus.1.1.1.1 hb
  have hr : atRootB (C (ring.rightNeighbor e)) = false := by
    cases h : atRootB (C (ring.rightNeighbor e)) with
    | false => rfl
    | true =>
      have hz : (raw (C (ring.rightNeighbor e))).label.val = 0 := by
        simpa [atRootB] using h
      exact (hg.2.1 hz).elim
  have hs : successorB (C e) (C (ring.rightNeighbor e)) = true := by
    simpa [ElectionGeometryV31, passiveEdgeOKV3, hr] using hGeom e
  have hGE := reindex2 ring C e (ring.rightNeighbor e)
    (startSucc2 ring C e hs) hg.2.2
  have he := (hGE (raw (C e)).label).1
  have hrm := (hg.2.2 (raw (C (ring.rightNeighbor e))).label).1
  try dsimp only at he hrm
  rw [groupSelf2 ring C e] at he
  rw [groupSelf2 ring C (ring.rightNeighbor e)] at hrm
  exact ⟨hs, hr, hGE, he, hrm⟩

private theorem mcStep2 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false)
    (h : MainClearV3 (C p)) : MainClearV3 (stepV3 hψ h2 ring C e p) := by
  by_cases hp : p = e
  · subst p; rw [left2 hψ h2 ring C e hb hs hr]
    cases h0 : atRootB (C e)
    · simpa [h0] using mc2 (C e) .scrubL
    · simpa [h0] using mc2 (C e) .openR
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p; rw [right2 hψ h2 ring C e hb hs hr]
      exact mc2 _ .none
    · rw [stepV3_other hψ h2 ring C e p hp hpr]
      exact h

private theorem scrubSource2 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false)
    (ht : (stepV3 hψ h2 ring C e p).ctl.tok = .scrubL) :
    p = e ∨ stepV3 hψ h2 ring C e p = C p := by
  by_cases hp : p = e
  · exact Or.inl hp
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p; rw [right2 hψ h2 ring C e hb hs hr] at ht
      simp [setControl] at ht
    · exact Or.inr (stepV3_other hψ h2 ring C e p hp hpr)

private theorem openSource2 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hs : successorB (C e) (C (ring.rightNeighbor e)) = true)
    (hr : atRootB (C (ring.rightNeighbor e)) = false)
    (ht : (stepV3 hψ h2 ring C e p).ctl.tok = .openR) :
    p = e ∨ stepV3 hψ h2 ring C e p = C p := by
  by_cases hp : p = e
  · exact Or.inl hp
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p; rw [right2 hψ h2 ring C e hb hs hr] at ht
      simp [setControl] at ht
    · exact Or.inr (stepV3_other hψ h2 ring C e p hp hpr)

theorem scrubLIncomingOpenRFresh_scrubL_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hPre : ScrubLContinuationIncomingFreshPrepayV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n) (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL) :
    ScrubLIncomingOpenRFreshV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  rcases prep2 hψ h2 ring C e hGeom hPlus hb with ⟨hs, hr, _, hce, hcr⟩
  have hL : ∀ p, (raw (D p)).label = (raw (C p)).label := by
    intro p; simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  intro owner hScrubD hSuccD hRootD
  have hSuccC : successorB (C owner) (C (ring.rightNeighbor owner)) = true := by
    unfold successorB at hSuccD ⊢
    rw [hL owner, hL (ring.rightNeighbor owner)] at hSuccD
    exact hSuccD
  have hRootC : atRootB (C owner) = true := by
    unfold atRootB at hRootD ⊢
    rw [hL owner] at hRootD
    exact hRootD
  rcases scrubSource2 hψ h2 ring C e (ring.rightNeighbor owner) hb hs hr hScrubD with hnew | heq
  · have hRootE : atRootB (C e) = false := by
      cases h0 : atRootB (C e) with
      | false => rfl
      | true =>
        have hx := hScrubD
        rw [hnew] at hx
        change (stepV3 hψ h2 ring C e e).ctl.tok = .scrubL at hx
        rw [left2 hψ h2 ring C e hb hs hr] at hx
        simp [h0, setControl] at hx
    by_cases hold : (C e).ctl.tok = .scrubL
    · have hf := hPlus.1.1.1.2 owner (by simpa [hnew] using hold) hSuccC hRootC
      exact ownerFresh2 hψ h2 ring C e owner hb hs hr hce hcr hf
    · have hf := hPre C e owner hTrace hGeom hPlus hb hnew hRootC
        (by simpa [hnew] using hSuccC) hRootE hold
      exact ownerFresh2 hψ h2 ring C e owner hb hs hr hce hcr hf
  · have hOld : (C (ring.rightNeighbor owner)).ctl.tok = .scrubL := by
      rw [← heq]; exact hScrubD
    exact ownerFresh2 hψ h2 ring C e owner hb hs hr hce hcr
      (hPlus.1.1.1.2 owner hOld hSuccC hRootC)

/-- First still-semantic gap: a continued scrub can create a new pending owner. -/
def ScrubLP8PreservationV31 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n), ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C → ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL →
    ScrubLIncomingOpenRFreshV31 ring (stepV3 hψ h2 ring C e) →
    SweepOpenROverlapClearV31 ring (stepV3 hψ h2 ring C e)

def ScrubLP9PreservationV31 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n), ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C → ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL →
    ScrubLIncomingOpenRFreshV31 ring (stepV3 hψ h2 ring C e) →
    SweepOpenROverlapClearV31 ring (stepV3 hψ h2 ring C e) →
    SweepOpenROverlapClearWideV31 ring (stepV3 hψ h2 ring C e)

def ScrubLSPreservationV31 (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n), ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C → ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL →
    ReachablePhaseFactsPlus3V31 ring (stepV3 hψ h2 ring C e) →
    SeekIncomingSweepOpenROverlapClearWideV31 ring (stepV3 hψ h2 ring C e)

def ScrubLStrongR2PreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n), ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C → ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL →
    ReachablePhaseFactsPlus3V31 ring (stepV3 hψ h2 ring C e) →
    SeekIncomingSweepOpenROverlapClearWideV31 ring (stepV3 hψ h2 ring C e) →
    OpenRPhaseOwnershipDisjointStrongV31 ring (stepV3 hψ h2 ring C e)

theorem openRForwardMainClear_scrubL_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n) (hGeom : ElectionGeometryV31 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL) :
    OpenRForwardMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  let D := stepV3 hψ h2 ring C e
  rcases prep2 hψ h2 ring C e hGeom hPlus hb with ⟨hs, hr, hGE, _, _⟩
  have hL : ∀ p, (raw (D p)).label = (raw (C p)).label := by
    intro p
    simpa [D] using stepV3_labels_eq_or_held hψ h2 ring C e p
  intro owner hOpenD dD
  rcases openSource2 hψ h2 ring C e owner hb hs hr hOpenD with hnew | heq
  · subst owner
    cases h0 : atRootB (C e) with
    | false =>
      have hx := hOpenD
      change (stepV3 hψ h2 ring C e e).ctl.tok = .openR at hx
      rw [left2 hψ h2 ring C e hb hs hr] at hx
      simp [h0, setControl] at hx
    | true =>
      have hz : (raw (C e)).label.val = 0 := by
        simpa [atRootB] using h0
      have hv :
          (raw (stepV3 hψ h2 ring C e e)).label.val =
            (raw (C e)).label.val := by
        simpa [D] using congrArg Fin.val (hL e)
      have hdC : dD.val < ψ - (raw (C e)).label.val := by
        simpa only [hv] using dD.isLt
      have hk : dD.val < ψ := by
        rw [hz] at hdC
        simpa using hdC
      let k : Fin ψ := ⟨dD.val, hk⟩
      have hm := (hGE k).1
      have hStart : R2Coherence.groupStart ring (eraseCfgV3 C) e = e := by
        unfold R2Coherence.groupStart
        change R2Coherence.back ring e (raw (C e)).label.val = e
        rw [hz]
        apply Fin.ext
        simp [R2Coherence.back, Nat.add_mod, Nat.mod_eq_of_lt e.isLt]
      have hp : R2Coherence.groupPos ring (eraseCfgV3 C) e k.val =
          R2Coherence.fwd ring e dD.val := by
        simp [R2Coherence.groupPos, hStart, k]
      rw [hp] at hm
      exact mcStep2 hψ h2 ring C e _ hb hs hr hm
  · have hOpenC : (C owner).ctl.tok = .openR := by
      rw [← heq]
      exact hOpenD
    have hv :
        (raw (stepV3 hψ h2 ring C e owner)).label.val =
          (raw (C owner)).label.val := by
      simpa [D] using congrArg Fin.val (hL owner)
    have hd : dD.val < ψ - (raw (C owner)).label.val := by
      simpa only [hv] using dD.isLt
    let dC : Fin (ψ - (raw (C owner)).label.val) := ⟨dD.val, hd⟩
    exact mcStep2 hψ h2 ring C e _ hb hs hr
      (by simpa [dC] using hPlus.2.2.1 owner hOpenC dC)

theorem scrubLStep_reachable_full
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hPre : ScrubLContinuationIncomingFreshPrepayV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hP8 : ScrubLP8PreservationV31 (κ := κ) (τ := τ) hψ h2 ring)
    (hP9 : ScrubLP9PreservationV31 (κ := κ) (τ := τ) hψ h2 ring)
    (hS : ScrubLSPreservationV31 (κ := κ) (τ := τ) hψ h2 ring)
    (hR2 : ScrubLStrongR2PreservationV31 (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n) (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL) :
    ReachablePhaseFactsPlus4StrongR2V31 ring (stepV3 hψ h2 ring C e) := by
  have hFacts := reachablePhaseFacts_scrubL_step hψ h2 ring C e hGeom hTrace hPlus hb
  have h7 := scrubLIncomingOpenRFresh_scrubL_step hψ h2 ring hPre C e hGeom hTrace hPlus hb
  have h8 := hP8 C e hGeom hTrace hPlus hb h7
  have h9 := hP9 C e hGeom hTrace hPlus hb h7 h8
  have hP3 : ReachablePhaseFactsPlus3V31 ring (stepV3 hψ h2 ring C e) :=
    ⟨⟨⟨hFacts, h7⟩, h8⟩, h9⟩
  have hSD := hS C e hGeom hTrace hPlus hb hP3
  have hR1D := openRForwardMainClear_scrubL_step hψ h2 ring C e hGeom hPlus hb
  have hR2D := hR2 C e hGeom hTrace hPlus hb hP3 hSD
  exact ⟨hP3, hSD, hR1D, hR2D⟩

theorem stepPreservesV31_scrubL_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hPre : ScrubLContinuationIncomingFreshPrepayV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hP8 : ScrubLP8PreservationV31 (κ := κ) (τ := τ) hψ h2 ring)
    (hP9 : ScrubLP9PreservationV31 (κ := κ) (τ := τ) hψ h2 ring)
    (hS : ScrubLSPreservationV31 (κ := κ) (τ := τ) hψ h2 ring)
    (hR2 : ScrubLStrongR2PreservationV31 (κ := κ) (τ := τ) hψ h2 ring) :
    StepPreservesV31_scrubL (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace hPlus hb
  exact scrubLStep_reachable_full hψ h2 ring hPre hP8 hP9 hS hR2
    C e hGeom hTrace hPlus hb

theorem scrubLReplay_oldOwnerFresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e owner : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL)
    (hf : OpenROwnerFreshV3 ring C owner) :
    OpenROwnerFreshV3 ring (stepV3 hψ h2 ring C e) owner := by
  rcases prep2 hψ h2 ring C e hGeom hPlus hb with
    ⟨hs, hr, _, hce, hcr⟩
  exact ownerFresh2 hψ h2 ring C e owner hb hs hr hce hcr hf

end R2CoherenceV31ReachableScrubL2
