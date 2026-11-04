import Leader.Wu.Entrance.CoreHostLaws
import Leader.Wu.Birth.CheckPermitRepairNoBirth
import Leader.Wu.Birth.CheckPermitRepairBirth

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B6EntranceV2K2R1

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
open PPLLWallSweepPreCheckResetContracts PPLLWallSweepNormalResetContract
  PPLLCompleteMultiLeaderCleanup PPLLPpsiLeaderCreationSchedule
open BirthGenerationControlRepair BirthGenerationDone BirthShortWait
  BirthShortWaitTerminalEntryRepair BirthShortDoneCuts
  BirthShortDoneTerminalEntryCut BirthShortDoneTerminalHost
  BirthSigMoveDisposalRepair BirthStationaryWrite
open K2BirthDispatcher K2BirthDispatcherDone K2BirthLeaderNormalize
  ExpiringK2Projection LDSinkKernelC
open B6EntranceV2 B6EntranceV2K2 B6LocalReverseFill

variable {n psi width kappa tau : Nat}

/-- The R1-only permit repair changes only `path0Crossed`, hence is invisible
through the four-field K2 observation. -/
private theorem permitFix_pair_signal
    (c : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authSignalPair (BirthCheckPermitRepair.permitFix c.1, c.2) =
      authSignalPair c := by
  change signalPair
      ((BirthCheckPermitRepair.permitFix c.1).core, c.2.core) =
    signalPair (c.1.core, c.2.core)
  rw [BirthCheckPermitRepair.permitFix_core]

/-- R1's repaired ordinary branch has exactly the CHECK-cut K2 observation,
including the exceptional equal/permit branch. -/
private theorem r1_ordinary_signal_from_check
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (cap : Nat) (l r : AuthorizedAgentState psi) :
    authSignalPair
        (BirthCheckPermitRepair.ordinary
          hpsi hwidth hle cap l r) =
      authSignalPair
        (doneThroughCheckEntryWidth hpsi hwidth hle cap l r) := by
  unfold BirthCheckPermitRepair.ordinary
  dsimp only
  generalize doneThroughCheckEntryWidth hpsi hwidth hle cap l r = c
  let f := BirthCheckPermitRepair.permitFix c.1
  let q := afterCheckMetadataWidth hpsi hwidth hle f c.2
  have hf : authSignalPair (f, c.2) = authSignalPair c := by
    simpa only [f] using permitFix_pair_signal c
  have hq := afterCheckMetadataWidth_signal hpsi hwidth hle f c.2
  have hm := markBirth_signal (authBirth l r q) q
  change authSignalPair (markLeaderBirth (authBirth l r q) q) =
    authSignalPair c
  exact hm.trans (hq.trans hf)

/-- The accepted terminal consumer's ordinary branch has the same CHECK-cut
K2 observation. -/
private theorem host_ordinary_signal_from_check
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (cap : Nat) (l r : AuthorizedAgentState psi) :
    authSignalPair
        (BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
          hpsi hwidth hle cap l r) =
      authSignalPair
        (doneThroughCheckEntryWidth hpsi hwidth hle cap l r) := by
  unfold BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
  dsimp only
  generalize doneThroughCheckEntryWidth hpsi hwidth hle cap l r = c
  have hq := afterCheckMetadataWidth_signal hpsi hwidth hle c.1 c.2
  generalize afterCheckMetadataWidth hpsi hwidth hle c.1 c.2 = q at hq ⊢
  exact (markBirth_signal (authBirth l r q) q).trans hq

theorem r1_ordinary_observation_eq_host
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (cap : Nat) (l r : AuthorizedAgentState psi) :
    authSignalPair
        (BirthCheckPermitRepair.ordinary
          hpsi hwidth hle cap l r) =
      authSignalPair
        (BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
          hpsi hwidth hle cap l r) :=
  (r1_ordinary_signal_from_check hpsi hwidth hle cap l r).trans
    (host_ordinary_signal_from_check hpsi hwidth hle cap l r).symm

/-- The deletion-priority wrapper is literally the same on both sides; only
its ordinary branch needed the preceding bridge. -/
theorem r1_authorized_observation_eq_host
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (cap : Nat) (l r : AuthorizedAgentState psi) :
    authSignalPair
        (BirthCheckPermitRepair.authorized
          hpsi hwidth hle cap l r) =
      authSignalPair
        (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
          hpsi hwidth hle cap l r) := by
  unfold BirthCheckPermitRepair.authorized
    BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
  dsimp only
  split
  · rfl
  · split
    · rfl
    · exact r1_ordinary_observation_eq_host
        hpsi hwidth hle cap _ _

/-- Bounded reification and expiry are observation-transparent on both paths. -/
theorem r1_expiring_observation_eq_host
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) :
    (observeCell
        (BirthCheckPermitRepair.expiring
          hpsi (by decide : 0 < 2) h2 l r).1,
      observeCell
        (BirthCheckPermitRepair.expiring
          hpsi (by decide : 0 < 2) h2 l r).2) =
    (observeCell
        (BirthShortDoneTerminalHost.doneMetadataEntryWidth
          hpsi (by decide : 0 < 2) h2 l r).1,
      observeCell
        (BirthShortDoneTerminalHost.doneMetadataEntryWidth
          hpsi (by decide : 0 < 2) h2 l r).2) := by
  calc
    _ = authSignalPair
        (BirthCheckPermitRepair.authorized
          hpsi (by decide : 0 < 2) h2 kappa
          (prepareExpiringDisposal hpsi l).core.erase
          (prepareExpiringDisposal hpsi r).core.erase) :=
      BirthCheckPermitRepairBirth.r1_expiring_observation
        hpsi h2 l r
    _ = authSignalPair
        (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
          hpsi (by decide : 0 < 2) h2 kappa
          (prepareExpiringDisposal hpsi l).core.erase
          (prepareExpiringDisposal hpsi r).core.erase) :=
      r1_authorized_observation_eq_host
        hpsi (by decide : 0 < 2) h2 kappa _ _
    _ = _ :=
      (BirthShortDoneTerminalConsumer.doneMetadataEntryWidth_observation
        hpsi (by decide : 0 < 2) h2 l r).symm

/-- Exact normalized pre-tail R1 observation equals the accepted consumer's
normalized pre-tail observation on the same physical input. -/
theorem r1Metadata_observation_eq_host
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) :
    (observeCell (B10NoBirthR1.metadataR1 hpsi h2 l r).1,
      observeCell (B10NoBirthR1.metadataR1 hpsi h2 l r).2) =
    (observeCell
        (BirthShortDoneTerminalHost.metadata
          hpsi (by decide : 0 < 2) h2 l r).1,
      observeCell
        (BirthShortDoneTerminalHost.metadata
          hpsi (by decide : 0 < 2) h2 l r).2) := by
  unfold B10NoBirthR1.metadataR1
  dsimp only
  rw [normalizeLeader_observation, normalizeLeader_observation]
  exact (r1_expiring_observation_eq_host hpsi h2 l r).trans
    (BirthShortDoneTerminalConsumer.metadata_observation_raw
      hpsi (by decide : 0 < 2) h2 l r).symm

/-- Consequently the R1 metadata birth bit is the accepted consumer birth bit. -/
theorem birthEventR1_eq_host
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) :
    B10NoBirthR1.birthEventR1 hpsi h2 l r =
      BirthShortDoneTerminalObserver.birthEvent
        hpsi (by decide : 0 < 2) h2 l r := by
  have ho := r1Metadata_observation_eq_host hpsi h2 l r
  have hL := congrArg
    (fun z : AgentState 1 × AgentState 1 => z.1.leader) ho
  have hR := congrArg
    (fun z : AgentState 1 × AgentState 1 => z.2.leader) ho
  change
    (B10NoBirthR1.metadataR1 hpsi h2 l r).1.core.core.leader =
      (BirthShortDoneTerminalHost.metadata
        hpsi (by decide : 0 < 2) h2 l r).1.core.core.leader at hL
  change
    (B10NoBirthR1.metadataR1 hpsi h2 l r).2.core.core.leader =
      (BirthShortDoneTerminalHost.metadata
        hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader at hR
  unfold B10NoBirthR1.birthEventR1 B10NoBirthR1.birthEventR1Cut
    BirthShortDoneTerminalObserver.birthEvent
  dsimp only
  unfold K2BirthDispatcher.newborn
  rw [hL, hR]

/-- If both completed R1 endpoints are followers, neither exact normalized
metadata endpoint can be a newborn. -/
theorem birthEventR1_false_of_final_followers
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hqL : (BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r).1.core.core.leader = false)
    (hqR : (BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader = false) :
    B10NoBirthR1.birthEventR1 hpsi h2 l r = false := by
  cases hb : B10NoBirthR1.birthEventR1 hpsi h2 l r with
  | false => rfl
  | true =>
      have hborn :
          newborn l (B10NoBirthR1.metadataR1 hpsi h2 l r).1 = true ∨
          newborn r (B10NoBirthR1.metadataR1 hpsi h2 l r).2 = true := by
        unfold B10NoBirthR1.birthEventR1
          B10NoBirthR1.birthEventR1Cut at hb
        dsimp only at hb
        simpa only [Bool.or_eq_true] using hb
      have hs :=
        BirthCheckPermitRepairBirth.r1_finalPhysical_birth_has_leader
          hpsi l r
          (B10NoBirthR1.metadataR1 hpsi h2 l r).1
          (B10NoBirthR1.metadataR1 hpsi h2 l r).2 hborn
      rw [B10NoBirthR1.row_eq_finalPhysical_metadataR1
        hpsi h2 l r] at hqL hqR
      dsimp only at hqL hqR
      rcases hs with hs | hs
      · have hbad : false = true := hqL.symm.trans hs
        cases hbad
      · have hbad : false = true := hqR.symm.trans hs
        cases hbad

/-- No R1 metadata birth gives the exact frozen collision/K2 observation. -/
theorem r1_observe_row_of_no_birth
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hn : B10NoBirthR1.birthEventR1 hpsi h2 l r = false) :
    (observeCell
        (BirthCheckPermitRepair.row
          hpsi (by decide : 0 < 2) h2 l r).1,
      observeCell
        (BirthCheckPermitRepair.row
          hpsi (by decide : 0 < 2) h2 l r).2) =
      shadowRow (observeCell l) (observeCell r) := by
  have hnb :
      newborn l (B10NoBirthR1.metadataR1 hpsi h2 l r).1 = false ∧
      newborn r (B10NoBirthR1.metadataR1 hpsi h2 l r).2 = false := by
    simpa only [B10NoBirthR1.birthEventR1,
      B10NoBirthR1.birthEventR1Cut, Bool.or_eq_false_iff] using hn
  have hnHost :
      BirthShortDoneTerminalObserver.birthEvent
        hpsi (by decide : 0 < 2) h2 l r = false := by
    rw [← birthEventR1_eq_host hpsi h2 l r]
    exact hn
  have hmeta :
      (observeCell (B10NoBirthR1.metadataR1 hpsi h2 l r).1,
        observeCell (B10NoBirthR1.metadataR1 hpsi h2 l r).2) =
      (observeCell l, observeCell r) :=
    (r1Metadata_observation_eq_host hpsi h2 l r).trans
      (BirthShortDoneTerminalObserver.metadata_signal_of_no_birth
        hpsi (by decide : 0 < 2) h2 l r hnHost)
  rw [B10NoBirthR1.row_eq_finalPhysical_metadataR1 hpsi h2 l r]
  dsimp only
  rw [K2BirthDispatcher.finalPhysical_of_no_birth
    hpsi l r _ _ hnb.1 hnb.2]
  exact (K2BirthDispatcher.observe_collisionRow hpsi _ _).trans
    (congrArg
      (fun z : AgentState 1 × AgentState 1 =>
        shadowRow z.1 z.2) hmeta)

/-- Discharge the row-level seam requested by `B6EntranceV2K2`. -/
theorem r1LeaderlessK2Agreement
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) :
    B6EntranceV2K2.R1LeaderlessK2Agreement hpsi h2 := by
  unfold B6EntranceV2K2.R1LeaderlessK2Agreement
  intro l r _ _
  dsimp only [B9Host.r1Host, B9Host.r1HostWidth]
  intro hqL hqR
  change (BirthCheckPermitRepair.row
    hpsi (by decide : 0 < 2) h2 l r).1.core.core.leader = false at hqL
  change (BirthCheckPermitRepair.row
    hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader = false at hqR
  exact r1_observe_row_of_no_birth hpsi h2 l r
    (birthEventR1_false_of_final_followers hpsi h2 l r hqL hqR)

/-! `R1K2DrainFrame` contains an arbitrary `WriterProtected` predicate, so it
cannot be a consequence of K2 observation mechanics alone.  These are the
three exact one-service frame leaves whose conjunction is definitionally the
requested `ExpiryAt` preservation. -/

def R1WriterAtSingleServiceFrame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (WP : WriterProtected ring psi (Phys psi psi (16 * psi))) : Prop :=
  ∀ (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi))) (e : Fin n),
    HostLeaderless (fun q => q) C →
    ExpiryAt (fun q => q) WP X C →
    internal X.env.I e →
    let D := B9Host.hostStep
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) ring C e
    HostLeaderless (fun q => q) D →
      WriterAt WP X D

def R1ResetEchoSingleServiceFrame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (WP : WriterProtected ring psi (Phys psi psi (16 * psi))) : Prop :=
  ∀ (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi))) (e : Fin n),
    HostLeaderless (fun q => q) C →
    ExpiryAt (fun q => q) WP X C →
    internal X.env.I e →
    let D := B9Host.hostStep
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) ring C e
    HostLeaderless (fun q => q) D →
      CoreAll (fun q => q) X ResetEchoClearCell D

def R1ComparisonCleanSingleServiceFrame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (WP : WriterProtected ring psi (Phys psi psi (16 * psi))) : Prop :=
  ∀ (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi))) (e : Fin n),
    HostLeaderless (fun q => q) C →
    ExpiryAt (fun q => q) WP X C →
    internal X.env.I e →
    let D := B9Host.hostStep
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) ring C e
    HostLeaderless (fun q => q) D →
      CoreAll (fun q => q) X ComparisonCleanCell D

theorem r1K2DrainFrame_of_single_service_frames
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (WP : WriterProtected ring psi (Phys psi psi (16 * psi)))
    (hWriter : R1WriterAtSingleServiceFrame hpsi h2 ring WP)
    (hReset : R1ResetEchoSingleServiceFrame hpsi h2 ring WP)
    (hCompare : R1ComparisonCleanSingleServiceFrame hpsi h2 ring WP) :
    B6EntranceV2K2.R1K2DrainFrame hpsi h2 ring WP := by
  unfold B6EntranceV2K2.R1K2DrainFrame
  intro X C e hLead hExpiry hInt
  dsimp only
  intro hLeadD
  exact
    ⟨⟨hWriter X C e hLead hExpiry hInt hLeadD,
        hReset X C e hLead hExpiry hInt hLeadD⟩,
      hCompare X C e hLead hExpiry hInt hLeadD⟩

theorem r1K2ProofSeams_of_single_service_frames
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (WP : WriterProtected ring psi (Phys psi psi (16 * psi)))
    (hWriter : R1WriterAtSingleServiceFrame hpsi h2 ring WP)
    (hReset : R1ResetEchoSingleServiceFrame hpsi h2 ring WP)
    (hCompare : R1ComparisonCleanSingleServiceFrame hpsi h2 ring WP) :
    B6EntranceV2K2.R1K2ProofSeams hpsi h2 ring WP := by
  exact
    ⟨r1K2DrainFrame_of_single_service_frames
        hpsi h2 ring WP hWriter hReset hCompare,
      r1LeaderlessK2Agreement hpsi h2⟩

end B6EntranceV2K2R1
