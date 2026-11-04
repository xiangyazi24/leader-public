import Leader.Wu.Coherence.ReachableSoundParametric
import Leader.Wu.Coherence.ReachableSoundInstances

set_option autoImplicit false
set_option Elab.async false

namespace R2CoherenceV31ReachableSoundInstancesParametric

open R2CoherenceV31 R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31ReachableOpenNoHazard4 R2CoherenceV31ReachableSound
open R2CoherenceV31ReachableSoundParametric
open R2CoherenceV31FinalSimulation4 R2CoherenceV31FinalSimulation5

variable {n ψ κ τ : Nat}

abbrev ReachP (E : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) (C : FC n ψ κ τ) :=
  ReachableFromV31 E hψ h2 r C

def SeekSPreservationV31P (E : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ∀ C e, ReachP E hψ h2 r C → ElectionGeometryV31 r C →
    ReachablePhaseFactsPlus4StrongR2V31 r C →
    branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .seek →
      SeekIncomingSweepOpenROverlapClearWideV31 r (stepV3 hψ h2 r C e)

def SweepP6V31P (E : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ∀ C e owner, ElectionGeometryV31 r C → ReachP E hψ h2 r C →
    ReachablePhaseFactsPlus4StrongR2V31 r C →
    branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .sweep →
    (stepV3 hψ h2 r C e owner).ctl.tok = .openR →
      OpenROwnerFreshV3 r (stepV3 hψ h2 r C e) owner

def SweepTailV31P (E : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 r C → ReachP E hψ h2 r C →
    ReachablePhaseFactsPlus4StrongR2V31 r C →
    branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .sweep →
      SeekIncomingSweepOpenROverlapClearWideV31 r (stepV3 hψ h2 r C e) ∧
      OpenRForwardMainClearV31 r (stepV3 hψ h2 r C e) ∧
      OpenRPhaseOwnershipDisjointStrongV31 r (stepV3 hψ h2 r C e)

def OpenHazardFreshV31P (E : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ∀ C e pred owner, ReachP E hψ h2 r C → ElectionGeometryV31 r C →
    ReachablePhaseFactsPlus4StrongR2V31 r C →
    branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .openHazard →
    let D := stepV3 hψ h2 r C e
    (D (r.rightNeighbor pred)).ctl.tok = .seek →
    (C (r.rightNeighbor pred)).ctl.tok ≠ .seek →
    PendingOpenROwnerV31 r D owner →
      (atRootB (D (r.rightNeighbor pred)) = true →
        SweepOpenRSafeAtV31 r D owner (r.rightNeighbor (r.rightNeighbor pred)) ∧
        ∀ d : Fin (ψ - (raw (D (r.rightNeighbor pred))).label.val),
          SweepOpenRSafeAtV31 r D owner (R2Coherence.fwd r (r.rightNeighbor pred) d.val)) ∧
      (atRootB (D (r.rightNeighbor pred)) = false → atRootB (D pred) = true →
        SweepOpenRSafeAtV31 r D owner (r.rightNeighbor pred) ∧
        ∀ d : Fin (ψ - (raw (D pred)).label.val),
          SweepOpenRSafeAtV31 r D owner (R2Coherence.fwd r pred d.val))

def MixedSV31P (E : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 r C → ReachP E hψ h2 r C →
    ReachablePhaseFactsPlus4StrongR2V31 r C →
    branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .mixed →
      SeekIncomingSweepOpenROverlapClearWideV31 r (stepV3 hψ h2 r C e)

def MixedR1V31P (E : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 r C → ReachP E hψ h2 r C →
    ReachablePhaseFactsPlus4StrongR2V31 r C →
    branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .mixed →
      OpenRForwardMainClearV31 r (stepV3 hψ h2 r C e)

def MixedR2V31P (E : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 r C → ReachP E hψ h2 r C →
    ReachablePhaseFactsPlus4StrongR2V31 r C →
    branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .mixed →
      OpenRPhaseOwnershipDisjointStrongV31 r (stepV3 hψ h2 r C e)

def ReleaseP7V31P (E : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 r C → ReachP E hψ h2 r C →
    ReachablePhaseFactsPlus4StrongR2V31 r C →
    branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .release →
      ScrubLIncomingOpenRFreshV31 r (stepV3 hψ h2 r C e)

def ReleaseP8V31P (E : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 r C → ReachP E hψ h2 r C →
    ReachablePhaseFactsPlus4StrongR2V31 r C →
    branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .release →
    ScrubLIncomingOpenRFreshV31 r (stepV3 hψ h2 r C e) →
      SweepOpenROverlapClearV31 r (stepV3 hψ h2 r C e)

def ReleaseP9V31P (E : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 r C → ReachP E hψ h2 r C →
    ReachablePhaseFactsPlus4StrongR2V31 r C →
    branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .release →
    ScrubLIncomingOpenRFreshV31 r (stepV3 hψ h2 r C e) →
    SweepOpenROverlapClearV31 r (stepV3 hψ h2 r C e) →
      SweepOpenROverlapClearWideV31 r (stepV3 hψ h2 r C e)

def ReleaseSV31P (E : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 r C → ReachP E hψ h2 r C →
    ReachablePhaseFactsPlus4StrongR2V31 r C →
    branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .release →
    ReachablePhaseFactsPlus3V31 r (stepV3 hψ h2 r C e) →
      SeekIncomingSweepOpenROverlapClearWideV31 r (stepV3 hψ h2 r C e)

def ReleaseR2V31P (E : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 r C → ReachP E hψ h2 r C →
    ReachablePhaseFactsPlus4StrongR2V31 r C →
    branchAtV3 hψ h2 (C e) (C (r.rightNeighbor e)) = .release →
    ReachablePhaseFactsPlus3V31 r (stepV3 hψ h2 r C e) →
    SeekIncomingSweepOpenROverlapClearWideV31 r (stepV3 hψ h2 r C e) →
      OpenRPhaseOwnershipDisjointStrongV31 r (stepV3 hψ h2 r C e)

abbrev ScrubLStepV31P := @StepPreservesV31_scrubL_parametric n ψ κ τ
abbrev OpenRStepV31P := @StepPreservesV31_openR_parametric n ψ κ τ
abbrev OpenNoHazardStepV31P := @StepPreservesV31_openNoHazard_parametric n ψ κ τ

private abbrev BirthE (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) :=
  BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r

theorem seekS_to_old (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (h : SeekSPreservationV31P (BirthE (κ := κ) (τ := τ) hψ h2 r) hψ h2 r) :
    R2CoherenceV31ReachableSeek2.SeekSPreservationV31
      (κ := κ) (τ := τ) hψ h2 r := by
  intro C e hq hg hp hb
  exact h C e hq hg hp hb

-- The other eleven custom twins are definitionally equal to their old Props
-- (`ReachableFromV31` at `BirthE` unfolds to `ReachableFromQuarantineV31`), so
-- each is the same `intro`/`exact` after matching the binder order.
-- The three full-step twins need only:
theorem scrubL_to_old (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (h : ScrubLStepV31P (BirthE (κ := κ) (τ := τ) hψ h2 r) hψ h2 r) :
    R2CoherenceV31ReachableSound.StepPreservesV31_scrubL
      (κ := κ) (τ := τ) hψ h2 r := by
  intro C e hg hq hp hb
  exact h C e hg hq hp hb

-- same proof for `openR_to_old` and `openNoHazard_to_old`.

theorem stepReleaseP
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (r : DirectedRing n)
    (p7 : ReleaseP7V31P E hψ h2 r) (p8 : ReleaseP8V31P E hψ h2 r)
    (p9 : ReleaseP9V31P E hψ h2 r) (s : ReleaseSV31P E hψ h2 r)
    (r2 : ReleaseR2V31P E hψ h2 r) :
    StepPreservesV31_release_parametric E hψ h2 r := by
  intro C e hg ht hp hb
  have f := R2CoherenceV31ReachableRelease.reachablePhaseFacts_release_step
    hψ h2 r C e hp.1.1.1.1 hb
  have q7 := p7 C e hg ht hp hb
  have q8 := p8 C e hg ht hp hb q7
  have q9 := p9 C e hg ht hp hb q7 q8
  have p3 : ReachablePhaseFactsPlus3V31 r (stepV3 hψ h2 r C e) :=
    ⟨⟨⟨f, q7⟩, q8⟩, q9⟩
  have qs := s C e hg ht hp hb p3
  have qr1 := R2CoherenceV31ReachableRelease3.openRForwardMainClear_release_step
    hψ h2 r C e hp.2.2.1 hb
  exact ⟨p3, qs, qr1, r2 C e hg ht hp hb p3 qs⟩

end R2CoherenceV31ReachableSoundInstancesParametric
