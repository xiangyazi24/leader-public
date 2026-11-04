import Leader.Wu.Coherence.ReachableFreshSeekScrubLOpenR

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ReplayExport

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31Closure R2CoherenceV31Closure2
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableFacts R2CoherenceV31ReachablePrepaid
open R2CoherenceV31ReachablePlus R2CoherenceV31ReachablePlus2
open R2CoherenceV31ReachablePlus3 R2CoherenceV31ReachablePlus4
open R2CoherenceV31FreshnessClear
open R2CoherenceV31ReachableSoundParametric
open R2CoherenceV31ReachableFreshBranches3
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31ReachableSoundFresh

variable {n ψ κ τ : Nat}

/-- Smallest SCRUBL shadow-export target.  Prove downstream by replaying the
legacy P1/P7/R1 bodies; do not assume it in the final ledger. -/
def ScrubLReplayCoreFreshExportP
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ C e, ElectionGeometryV31 ring C →
    ReachableFromV31 E hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .scrubL →
    let D := stepV3 hψ h2 ring C e
    ReachablePhaseFactsV31 ring D ∧
    ScrubLIncomingOpenRFreshV31 ring D ∧
    OpenRForwardFreshnessClearV31 ring D

/-- Smallest OPEN-R shadow-export target.  `hS` is the already-installed
source for only the bad/new-seek arm. -/
def OpenRReplayCoreFreshExportP
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  OpenRSFreshSourceV31P E hψ h2 ring →
  ∀ C e, ElectionGeometryV31 ring C →
    ReachableFromV31 E hψ h2 ring C →
    ReachablePhaseFactsFreshV31 ring C →
    branchAtV3 hψ h2 (C e) (C (ring.rightNeighbor e)) = .openR →
    let D := stepV3 hψ h2 ring C e
    ReachablePhaseFactsFreshP3V31 ring D ∧
    SeekIncomingSweepOpenROverlapFreshWideV31 ring D

-- The actual downstream theorem statements to prove are:
-- theorem scrubLReplayCoreFresh_export (E) hψ h2 ring :
--   ScrubLReplayCoreFreshExportP E hψ h2 ring := by ...
-- theorem openRReplayCoreFresh_export (E) hψ h2 ring :
--   OpenRReplayCoreFreshExportP E hψ h2 ring := by ...


theorem scrubLReplayFresh_of_core
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hCore : ScrubLReplayCoreFreshExportP E hψ h2 ring) :
    ScrubLFreshPrivateReplayV31P E hψ h2 ring := by
  intro hP8 hP9 hS hR2 C e hg ht hf hb
  rcases hCore C e hg ht hf hb with ⟨h1, h7, hR1⟩
  have h8 := hP8 C e hg ht hf hb h7
  have h9 := hP9 C e hg ht hf hb h7 h8
  have hP3 : ReachablePhaseFactsFreshP3V31 ring
      (stepV3 hψ h2 ring C e) := ⟨h1, h7, h8, h9⟩
  have hSD := hS C e hg ht hf hb hP3
  have hR2D := hR2 C e hg ht hf hb hP3 hSD
  exact ⟨h1, h7, h8, h9, hSD, hR1, hR2D⟩

theorem openRReplayFresh_of_core
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hCore : OpenRReplayCoreFreshExportP E hψ h2 ring) :
    OpenRFreshPrivateReplayV31P E hψ h2 ring := by
  intro hS hR1 hR2 C e hg ht hf hb
  rcases hCore hS C e hg ht hf hb with ⟨hP3, hSD⟩
  rcases hP3 with ⟨h1, h7, h8, h9⟩
  have hR1D := hR1 C e hg ht hf hb
  have hR2D := hR2 C e hg ht hf hb
  exact ⟨h1, h7, h8, h9, hSD, hR1D, hR2D⟩

/-- Final wrappers after the two shadow-export cores above are proved. -/
theorem scrubLReplayFresh_of_export
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hCore : ScrubLReplayCoreFreshExportP E hψ h2 ring) :
    ScrubLFreshPrivateReplayV31P E hψ h2 ring :=
  scrubLReplayFresh_of_core E hψ h2 ring hCore

theorem openRReplayFresh_of_export
    (E : FC n ψ κ τ → Prop) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hCore : OpenRReplayCoreFreshExportP E hψ h2 ring) :
    OpenRFreshPrivateReplayV31P E hψ h2 ring :=
  openRReplayFresh_of_core E hψ h2 ring hCore


end R2CoherenceV31ReplayExport
