import Leader.Wu.Coherence.FreshResidualLedger
import Leader.Wu.Coherence.CarrierSimulationComponents

set_option autoImplicit false
set_option Elab.async false

namespace R2CoherenceV31EntranceTransport

open R2CoherenceV31 R2CoherenceBranches
open R2CoherenceV31BirthQuarantine R2CoherenceV31QuarantineReach
open R2CoherenceV31ReachableSoundParametric
open R2CoherenceV31FinalSimulation R2CoherenceV31FinalSimulation4
open R2CoherenceV31FinalSimulation5
open R2CoherenceV31ReachableAdjacentRoot
open R2CoherenceV31ReachableFreshBranches1
open R2CoherenceV31ReachableFreshBranches2
open R2CoherenceV31ReachableFreshBranches3
open R2CoherenceV31ReachableSoundFreshInstances
open R2CoherenceV31ReachableSweepFresh
open R2CoherenceV31ReachableSweepFresh2
open R2CoherenceV31FreshnessClear
open R2CoherenceV31OpenNoHazardClose
open R2CoherenceV31PhaseMainClear
open R2CoherenceV31ReachableSoundFresh

variable {n ψ κ τ : Nat}

/-- Old producer-facing entrance: an R1 birth handoff, re-controlled to
all-closing/token-none quarantine, plus election geometry. -/
abbrev BirthQuarantineEntranceV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) :
    FC n ψ κ τ → Prop :=
  BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r

/-- C1 entrance: the open/token-none lift image of an admitted, leaderless,
all-open final configuration.  It carries no birth-preimage witness. -/
abbrev AdmittedFinalEntranceV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) :
    FC n ψ κ τ → Prop :=
  C1FinalV31AdmittedEntrance (kappa := κ) (tau := τ) hψ h2 r

/-- The two entrance predicates are disjoint on the admitted source class:
BirthEntranceV1 has a physical leader, whereas the admitted lift is physically
leaderless.  So zero-word transport is impossible. -/
theorem admittedEntrance_not_quarantineEntrance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (Q : FC n ψ κ τ)
    (hA : AdmittedFinalEntranceV31 hψ h2 r Q) :
    ¬ BirthQuarantineEntranceV31 hψ h2 r Q := by
  rcases hA with ⟨C, _hAdm, hL, _hOpen, rfl⟩
  exact
    R2CoherenceV31FinalSimulation4.liftFinalV31_not_birthEntranceV1_of_finalLeaderless
        hψ h2 r C hL

/-- Exact extra historical fact needed to reuse the old 22-slot ledger.Every admitted entrance need only be *reachable* from some quarantine entrance;
it need not itself satisfy BirthEntranceV1.  A real producer belongs with the
C-final phase-renewal provenance, e.g. CFinalPhaseRenewal3. -/
def C1FinalV31AdmittedQuarantineProvenance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n) : Prop :=
  ∀ Q : FC n ψ κ τ,
    AdmittedFinalEntranceV31 hψ h2 r Q →
      ReachableFromQuarantineV31 hψ h2 r Q

/-- Entrance provenance is enough for full reachable-set containment: append
the admitted future word to the quarantine word witnessing the entrance. -/
theorem admittedReachable_subset_quarantine_of_provenance
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hProv : C1FinalV31AdmittedQuarantineProvenance
      (κ := κ) (τ := τ) hψ h2 r)
    (Q : FC n ψ κ τ)
    (hReach : ReachableFromV31
      (AdmittedFinalEntranceV31 hψ h2 r) hψ h2 r Q) :
    ReachableFromQuarantineV31 hψ h2 r Q := by
  rcases hReach with ⟨A0, w, hA0, rfl⟩
  rcases hProv A0 hA0 with ⟨B0, pre, hB0, hEq⟩
  refine ⟨B0, pre ++ w, hB0, ?_⟩
  rw [List.foldl_append, ← hEq]


/-- Conditional seam closure.  The hypotheses after `hProv` are exactly the
22 open slots of `reachableSoundFresh_of_ledger`.  No slot is strengthened or
re-stated.  Once entrance provenance is supplied, that ledger directly yields
the admitted C1 Fresh residual. -/
theorem reachableSoundFreshAdmitted_of_ledger
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (hProv : C1FinalV31AdmittedQuarantineProvenance
      (κ := κ) (τ := τ) hψ h2 r)
    (hCover : PendingFootprintCoveredReachableV31
      (kappa := κ) (tau := τ) hψ h2 r)
    (hCurrent : ReachableCurrentOpenRSweepFootprintFreshV31
      (κ := κ) (τ := τ) hψ h2 r)
    (seekS : SeekSFreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (seekR2 : SeekStrongR2FreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (seekReplay : SeekFreshPrivateReplayV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (rel7 : ReleaseP7FreshV31 (κ := κ) (τ := τ) hψ h2 r)
    (rel8 : ReleaseP8FreshV31 (κ := κ) (τ := τ) hψ h2 r)
    (rel9 : ReleaseP9FreshV31 (κ := κ) (τ := τ) hψ h2 r)
    (relS : ReleaseSFreshV31 (κ := κ) (τ := τ) hψ h2 r)
    (relR2 : ReleaseR2FreshV31 (κ := κ) (τ := τ) hψ h2 r)
    (scr8 : ScrubLP8FreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (scr9 : ScrubLP9FreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (scrS : ScrubLSFreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (scrR2 : ScrubLStrongR2FreshPreservationV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (scrReplay : ScrubLFreshPrivateReplayV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (orS : OpenRSFreshSourceV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (orReplay : OpenRFreshPrivateReplayV31P
      (BirthEntranceV1 (κ := κ) (τ := τ) hψ h2 r) hψ h2 r)
    (haz : OpenHazardFreshSeekPrepaidFreshV31
      (κ := κ) (τ := τ) hψ h2 r)
    (onh : SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ (by decide : 0 < 2) h2)
    (mixS : MixedSFreshV31 (κ := κ) (τ := τ) hψ h2 r)
    (mixR1 : MixedR1FreshV31 (κ := κ) (τ := τ) hψ h2 r)
    (mixR2 : MixedR2FreshV31 (κ := κ) (τ := τ) hψ h2 r) :
    C1FinalV31AdmittedReachableFreshResidual
      (κ := κ) (τ := τ) hψ h2 r := by
  have hOld :=
    R2CoherenceV31FreshResidualLedger.reachableSoundFresh_of_ledger
      (κ := κ) (τ := τ) hψ h2 r hCover hCurrent
      seekS seekR2 seekReplay rel7 rel8 rel9 relS relR2
      scr8 scr9 scrS scrR2 scrReplay orS orReplay haz onh
      mixS mixR1 mixR2
  intro Q hReach
  exact hOld Q
    (admittedReachable_subset_quarantine_of_provenance
      (κ := κ) (τ := τ) hψ h2 r hProv Q hReach)

end R2CoherenceV31EntranceTransport
