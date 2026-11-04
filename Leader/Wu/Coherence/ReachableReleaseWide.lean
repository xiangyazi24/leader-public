import Leader.Wu.Coherence.ReachableReleaseHandoff


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31ReachableRelease3


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
open R2CoherenceV31ReachableRelease R2CoherenceV31ReachableRelease2


variable {n ψ κ τ : Nat}


private theorem branchReleaseConditions3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .release) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok ≠ .sweep ∧
      r.ctl.tok ≠ .commit ∧ l.ctl.tok = .release := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind


private theorem rowRelease3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .release) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = releaseStageV3 l r := by
  rcases branchReleaseConditions3 hψ h2 l r hb with
    ⟨hs, hw, hc, hr⟩
  simp [rowV3, hs, hw, hc, hr]


private theorem releaseStagePhys3 (l r : Cell ψ κ τ) :
    (releaseStageV3 l r).1.phys = l.phys ∧
      (releaseStageV3 l r).2.phys = r.phys := by
  unfold releaseStageV3
  repeat' split <;> simp [setControl, startClosing]


private theorem releasePhys3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    ∀ p, (stepV3 hψ h2 ring C e p).phys = (C p).phys := by
  intro p
  have hr := rowRelease3 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  have hp := releaseStagePhys3 (C e) (C (ring.rightNeighbor e))
  by_cases hpe : p = e
  · subst p
    simpa [stepV3, protocolV3, PopulationProtocol.step, hr] using hp.1
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      simpa [stepV3, protocolV3, PopulationProtocol.step, hr, hpe] using hp.2
    · rw [stepV3_other hψ h2 ring C e p hpe hpr]


private theorem releasePostOpenROld3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release)
    (ho : (stepV3 hψ h2 ring C e p).ctl.tok = .openR) :
    (C p).ctl.tok = .openR := by
  have hr := rowRelease3 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  by_cases hpe : p = e
  · subst p
    have heq : stepV3 hψ h2 ring C e e =
        (releaseStageV3 (C e) (C (ring.rightNeighbor e))).1 := by
      simp [stepV3, protocolV3, PopulationProtocol.step, hr]
    rw [heq] at ho
    unfold releaseStageV3 at ho
    repeat' split at ho <;> simp_all [setControl, startClosing]
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      have heq : stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
          (releaseStageV3 (C e) (C (ring.rightNeighbor e))).2 := by
        simp [stepV3, protocolV3, PopulationProtocol.step, hr, hpe]
      rw [heq] at ho
      unfold releaseStageV3 at ho
      repeat' split at ho <;> simp_all [setControl, startClosing]
    · rw [stepV3_other hψ h2 ring C e p hpe hpr] at ho
      exact ho


private theorem mainClearPhys3
    {u v : Cell ψ κ τ} (hp : u.phys = v.phys)
    (hm : MainClearV3 v) : MainClearV3 u := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at hm ⊢
  simpa [eraseCellV3, R2Coherence.raw, hp] using hm


/-- R1: RELEASE creates no openR token and changes no physical field. -/
theorem openRForwardMainClear_release_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hR1 : OpenRForwardMainClearV31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    OpenRForwardMainClearV31 ring (stepV3 hψ h2 ring C e) := by
  intro owner hOpenD dD
  have hOpenC := releasePostOpenROld3 hψ h2 ring C e owner hb hOpenD
  have hRaw : raw (stepV3 hψ h2 ring C e owner) = raw (C owner) :=
    congrArg (fun x : R2.Cell ψ κ τ => x.base.core.core)
      (releasePhys3 hψ h2 ring C e hb owner)
  have hv : (raw (stepV3 hψ h2 ring C e owner)).label.val =
      (raw (C owner)).label.val :=
    congrArg (fun x : BoundedAgentState ψ κ => x.label.val) hRaw
  have hdC : dD.val < ψ - (raw (C owner)).label.val := by
    simpa only [hv] using dD.isLt
  let dC : Fin (ψ - (raw (C owner)).label.val) := ⟨dD.val, hdC⟩
  have hm := hR1 owner hOpenC dC
  exact mainClearPhys3
    (releasePhys3 hψ h2 ring C e hb (R2Coherence.fwd ring owner dD.val))
    (by simpa [dC] using hm)



/-- Proposed payload prepayment for the root+terminal RELEASE handoff.
It is exactly P9-wide safety for the owner which will become pending. -/
def ReleaseIncomingSweepOpenROverlapClearWideV31
    (ring : DirectedRing n) (C : FC n ψ κ τ) : Prop :=
  ∀ (e sweep : Fin n),
    (C e).ctl.tok = .release →
    atRootB (C e) = true →
    successorB (C e) (C (ring.rightNeighbor e)) = true →
    writerQuiet (C (ring.rightNeighbor e)) = true →
    atTerminalB (C (ring.rightNeighbor e)) = true →
    (C sweep).ctl.tok = .sweep →
      SweepOpenRSafeAtV31 ring C e (ring.rightNeighbor sweep) ∧
      ∀ d : Fin (ψ - (raw (C sweep)).label.val),
        SweepOpenRSafeAtV31 ring C e
          (R2Coherence.fwd ring sweep d.val)


/-- Conditional P9 continuation after the named P8 assumption. -/
def ReleaseSweepOpenROverlapClearWidePreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release →
    ScrubLIncomingOpenRFreshV31 ring (stepV3 hψ h2 ring C e) →
    SweepOpenROverlapClearV31 ring (stepV3 hψ h2 ring C e) →
      SweepOpenROverlapClearWideV31 ring (stepV3 hψ h2 ring C e)


/-- RELEASE can create a seek on its bad edge, so S is kept as an exact
conditional preservation obligation rather than assumed to be a frame. -/
def ReleaseSeekIncomingSweepOpenROverlapClearWidePreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release →
    ReachablePhaseFactsPlus3V31 ring (stepV3 hψ h2 ring C e) →
      SeekIncomingSweepOpenROverlapClearWideV31 ring
        (stepV3 hψ h2 ring C e)


/-- The strong-R2 new-pending-owner sentence is also kept explicit: old R2
is a frame for surviving openR, but the added pending-owner/sweep sentence has
a genuinely new owner on the terminal root handoff. -/
def ReleaseStrongR2PreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release →
    ReachablePhaseFactsPlus3V31 ring (stepV3 hψ h2 ring C e) →
    SeekIncomingSweepOpenROverlapClearWideV31 ring
      (stepV3 hψ h2 ring C e) →
      OpenRPhaseOwnershipDisjointStrongV31 ring
        (stepV3 hψ h2 ring C e)


theorem reachablePhaseFactsPlus2_release_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hP7 : ReleaseScrubLIncomingOpenRFreshPreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hP8 : ReleaseSweepOpenROverlapClearPreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    ReachablePhaseFactsPlus2V31 ring (stepV3 hψ h2 ring C e) := by
  have hP := reachablePhaseFactsPlus_release_step
    hψ h2 ring hP7 C e hGeom hTrace hPlus hb
  have hPoint := hP8 C e hGeom hTrace hPlus hb hP.2
  exact ⟨hP, hPoint⟩


theorem reachablePhaseFactsPlus3_release_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hP7 : ReleaseScrubLIncomingOpenRFreshPreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hP8 : ReleaseSweepOpenROverlapClearPreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hP9 : ReleaseSweepOpenROverlapClearWidePreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    ReachablePhaseFactsPlus3V31 ring (stepV3 hψ h2 ring C e) := by
  have hP2 := reachablePhaseFactsPlus2_release_step
    hψ h2 ring hP7 hP8 C e hGeom hTrace hPlus hb
  have hWide := hP9 C e hGeom hTrace hPlus hb hP2.1.2 hP2.2
  exact ⟨hP2, hWide⟩


theorem releaseStep_reachable_full
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hP7 : ReleaseScrubLIncomingOpenRFreshPreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hP8 : ReleaseSweepOpenROverlapClearPreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hP9 : ReleaseSweepOpenROverlapClearWidePreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hS : ReleaseSeekIncomingSweepOpenROverlapClearWidePreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (hR2 : ReleaseStrongR2PreservationV31
      (n := n) (ψ := ψ) (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .release) :
    ReachablePhaseFactsPlus4StrongR2V31 ring (stepV3 hψ h2 ring C e) := by
  have hP3 := reachablePhaseFactsPlus3_release_step
    hψ h2 ring hP7 hP8 hP9 C e hGeom hTrace hPlus hb
  have hSD := hS C e hGeom hTrace hPlus hb hP3
  have hR1D := openRForwardMainClear_release_step
    hψ h2 ring C e hPlus.2.2.1 hb
  have hR2D := hR2 C e hGeom hTrace hPlus hb hP3 hSD
  exact ⟨hP3, hSD, hR1D, hR2D⟩


end R2CoherenceV31ReachableRelease3
