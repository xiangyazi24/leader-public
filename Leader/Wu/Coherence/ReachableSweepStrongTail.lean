import Leader.Wu.Coherence.ReachableSound

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReachableSweep2

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31QuarantineReach R2CoherenceV31ReachableFacts
open R2CoherenceV31ReachableSweep
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4

variable {n ψ κ τ : Nat}

/-- Missing global bridge: current strong-R2 fields do not imply this by
projection/definition. -/
def StrongR2ReachableOpenRBarrierV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
      OpenRImpliesNoSweepInGroupV31 ring C ∧ OpenRSeekAheadV31 ring C

/-- First missing Facts clause for SWEEP: P6's mark is framed; only the
current openR owner's intrinsic freshness needs new causal information. -/
def SweepCurrentOpenRFreshPreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e owner : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep →
    (stepV3 hψ h2 ring C e owner).ctl.tok = .openR →
      OpenROwnerFreshV3 ring (stepV3 hψ h2 ring C e) owner

/-- No sweep preservation theorem for these three Plus4 tail fields is
currently exported; keep that API debt explicit. -/
def SweepStrongTailPreservationV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    ElectionGeometryV31 ring C →
    ReachableFromQuarantineV31 hψ h2 ring C →
    ReachablePhaseFactsPlus4StrongR2V31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep →
      SeekIncomingSweepOpenROverlapClearWideV31 ring
          (stepV3 hψ h2 ring C e) ∧
      OpenRForwardMainClearV31 ring (stepV3 hψ h2 ring C e) ∧
      OpenRPhaseOwnershipDisjointStrongV31 ring
          (stepV3 hψ h2 ring C e)

private theorem sweepCond_s2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sweep) :
    r.ctl.tok ≠ .seek ∧ l.ctl.tok = .sweep := by
  unfold branchAtV3 at hb
  repeat' split at hb
  all_goals simp_all
  all_goals grind

private theorem rowSweep_s2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : Cell ψ κ τ)
    (hb : branchAtV3 hψ h2 l r = .sweep) :
    rowV3 hψ (by decide : 0 < 2) h2 l r = sweepStageV3 l r := by
  rcases sweepCond_s2 hψ h2 l r hb with ⟨hs, hw⟩
  simp [rowV3, hs, hw]

private theorem leftSweep_s2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    stepV3 hψ h2 ring C e e =
      (sweepStageV3 (C e) (C (ring.rightNeighbor e))).1 := by
  have hr := rowSweep_s2 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr]

private theorem rightSweep_s2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    (hne : ring.rightNeighbor e ≠ e) :
    stepV3 hψ h2 ring C e (ring.rightNeighbor e) =
      (sweepStageV3 (C e) (C (ring.rightNeighbor e))).2 := by
  have hr := rowSweep_s2 hψ h2 (C e) (C (ring.rightNeighbor e)) hb
  simp [stepV3, protocolV3, PopulationProtocol.step, hr, hne]


private theorem postOld_s2
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (e p : Fin n)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep)
    {t : TokenV3} (h0 : t ≠ .none) (hk : t ≠ .seek)
    (hw : t ≠ .sweep) (hc : t ≠ .commit)
    (ht : (stepV3 hψ h2 ring C e p).ctl.tok = t) :
    stepV3 hψ h2 ring C e p = C p := by
  by_cases hpe : p = e
  · subst p
    rw [leftSweep_s2 hψ h2 ring C e hb] at ht ⊢
    unfold sweepStageV3 at ht ⊢
    split <;> simp_all [setControl, startClosing]
  · by_cases hpr : p = ring.rightNeighbor e
    · subst p
      rw [rightSweep_s2 hψ h2 ring C e hb hpe] at ht ⊢
      unfold sweepStageV3 at ht ⊢
      split
      · cases hh : atTerminalB (C (ring.rightNeighbor e)) <;>
          simp_all [setControl, hh]
      · rfl
    · exact stepV3_other hψ h2 ring C e p hpe hpr

private theorem reachablePhaseFacts_sweep_step_of_openRFresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hP6 : SweepCurrentOpenRFreshPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    ReachablePhaseFactsV31 ring (stepV3 hψ h2 ring C e) := by
  have hFacts : ReachablePhaseFactsV31 ring C := hPlus.1.1.1.1
  have hPhase := sweepStep_reachable_phase hψ h2 ring C e hTrace hFacts hb
  refine ⟨hPhase.1, hPhase.2.1, hPhase.2.2.1, ?_, ?_, ?_⟩
  · intro i hi
    have heq := postOld_s2 hψ h2 ring C e i hb
      (t := .release) (by decide) (by decide) (by decide) (by decide) hi
    have hiC : (C i).ctl.tok = .release := by simpa [heq] using hi
    have hOld := hFacts.2.2.2.1 i hiC
    exact ⟨by simpa [heq] using hOld.1, hPhase.2.2.2.1 i hi⟩
  · intro i hi
    have heq := postOld_s2 hψ h2 ring C e i hb
      (t := .scrubL) (by decide) (by decide) (by decide) (by decide) hi
    have hiC : (C i).ctl.tok = .scrubL := by simpa [heq] using hi
    have hOld := hFacts.2.2.2.2.1 i hiC
    exact ⟨by simpa [heq] using hOld.1,
      by simpa [heq] using hOld.2.1, hPhase.2.2.2.2 i hi⟩
  · intro i hi
    have heq := postOld_s2 hψ h2 ring C e i hb
      (t := .openR) (by decide) (by decide) (by decide) (by decide) hi
    have hiC : (C i).ctl.tok = .openR := by simpa [heq] using hi
    have hOld := hFacts.2.2.2.2.2 i hiC
    exact ⟨by simpa [heq] using hOld.1,
      hP6 C e i hGeom hTrace hPlus hb hi⟩

private theorem plus3_sweep_step_of_openRFresh
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hP6 : SweepCurrentOpenRFreshPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    ReachablePhaseFactsPlus3V31 ring (stepV3 hψ h2 ring C e) := by
  have hFactsD := reachablePhaseFacts_sweep_step_of_openRFresh
    hψ h2 ring hP6 C e hGeom hTrace hPlus hb
  have hIncomingD :=
    R2CoherenceV31ReachablePlus2.sweepStep_preserves_scrubLIncoming_plus2
      hψ h2 ring C e hPlus.1.1 hTrace hb
  have hWideD :=
    R2CoherenceV31ReachablePlus3.sweepOpenROverlapClearWide_sweep_step_full
      hψ h2 ring C e hPlus.1.2 hb
  have hPointD := sweepOpenROverlapClearWide_implies_pointwise
    ring (stepV3 hψ h2 ring C e) hWideD
  exact ⟨⟨⟨hFactsD, hIncomingD⟩, hPointD⟩, hWideD⟩

theorem sweepStep_reachable_full
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hP6 : SweepCurrentOpenRFreshPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hTail : SweepStrongTailPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (C : FC n ψ κ τ) (e : Fin n)
    (hGeom : ElectionGeometryV31 ring C)
    (hTrace : ReachableFromQuarantineV31 hψ h2 ring C)
    (hPlus : ReachablePhaseFactsPlus4StrongR2V31 ring C)
    (hb : branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .sweep) :
    ReachablePhaseFactsPlus4StrongR2V31 ring (stepV3 hψ h2 ring C e) := by
  have hP3D := plus3_sweep_step_of_openRFresh
    hψ h2 ring hP6 C e hGeom hTrace hPlus hb
  have hT := hTail C e hGeom hTrace hPlus hb
  exact ⟨hP3D, hT.1, hT.2.1, hT.2.2⟩

theorem stepPreservesV31_sweep_of_residuals
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hP6 : SweepCurrentOpenRFreshPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hTail : SweepStrongTailPreservationV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    R2CoherenceV31ReachableSound.StepPreservesV31_sweep
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hGeom hTrace hPlus hb
  exact sweepStep_reachable_full
    hψ h2 ring hP6 hTail C e hGeom hTrace hPlus hb

end R2CoherenceV31ReachableSweep2
