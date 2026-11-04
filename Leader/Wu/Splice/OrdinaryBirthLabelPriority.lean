import Leader.Wu.Splice.OrdinaryBirthLabelCheck
import Leader.Wu.WallSweep.Repair
import Leader.Wu.WallSweep.PreCheckResetContractsCore
import Leader.Wu.WallSweep.FiniteIntegration

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV8BirthCaseAdapterLabelProjection

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open PPLLCompleteMultiLeaderCleanup PPLLPpsiLeaderCreationSchedule
open BirthShortDoneCuts BirthShortDoneTerminalEntryCut BirthShortDoneTerminalHost
  BirthSigMoveDisposalRepair K2BirthDispatcher K2BirthLeaderNormalize
  ExpiringK2Projection BirthStationaryWrite
open B9SpliceV8LeftLeaderOpaqueBridge
  B9SpliceV8BirthCaseAdapterLabelGen B9SpliceV8BirthCaseAdapterLabelCheck

variable {psi width kappa tau : Nat}

attribute [local irreducible] BirthStationaryWrite.stationaryPersistentAuthorizedRow

private theorem stationary_labels (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) :
    authLabels (stationaryPersistentAuthorizedRow hpsi l r) = authLabels (l, r) := by
  have hf := stationaryPersistentAuthorizedRow_frame hpsi l r
  have hl0 := congrArg (fun q => q.1.2.1) hf
  have hr0 := congrArg (fun q => q.2.2.1) hf
  have hl : (stationaryPersistentAuthorizedRow hpsi l r).1.core.label =
      l.core.label := by
    simpa only [swPair, swView] using hl0
  have hr : (stationaryPersistentAuthorizedRow hpsi l r).2.core.label =
      r.core.label := by
    simpa only [swPair, swView] using hr0
  exact Prod.ext hl hr

private theorem afterCheck_stage (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (l r : AuthorizedAgentState psi) :
    let b := beforeWriteWidth hpsi hwidth hle l r
    afterCheckMetadataWidth hpsi hwidth hle l r =
      stationaryPersistentAuthorizedRow hpsi b.1 b.2 := by
  rfl

private theorem afterCheck_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (l r : AuthorizedAgentState psi) :
    authLabels (afterCheckMetadataWidth hpsi hwidth hle l r) = authLabels (l, r) := by
  let b := beforeWriteWidth hpsi hwidth hle l r
  have hb := beforeWrite_labels hpsi hwidth hle l r
  have hw := stationary_labels hpsi b.1 b.2
  have hstage : afterCheckMetadataWidth hpsi hwidth hle l r =
      stationaryPersistentAuthorizedRow hpsi b.1 b.2 :=
    afterCheck_stage hpsi hwidth hle l r
  exact (congrArg authLabels hstage).trans (hw.trans hb)

private theorem markBirth_labels (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authLabels (markLeaderBirth born q) = authLabels q := by
  have h := PPLLWallSweepPreCheckResetContracts.markLeaderBirth_labels_eq born q
  exact Prod.ext h.1 h.2

attribute [local irreducible]
  BirthShortDoneCuts.beforeWriteWidth BirthShortDoneCuts.afterCheckMetadataWidth
  BirthShortDoneTerminalEntryCut.doneBeforeCheckEntryWidth
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth

private theorem ordinary_labels (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width <= psi) (cap : Nat) (l r : AuthorizedAgentState psi) :
    authLabels (doneOrdinaryMetadataEntryWidth hpsi hwidth hle cap l r) =
      authLabels (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hpsi l r) := by
  let c := doneThroughCheckEntryWidth hpsi hwidth hle cap l r
  let q := afterCheckMetadataWidth hpsi hwidth hle c.1 c.2
  have hc := throughCheck_labels hpsi hwidth hle cap l r
  have hq := afterCheck_labels hpsi hwidth hle c.1 c.2
  have hm := markBirth_labels (authBirth l r q) q
  have hs : doneOrdinaryMetadataEntryWidth hpsi hwidth hle cap l r =
      markLeaderBirth (authBirth l r q) q :=
    ordinary_eq_stages hpsi hwidth hle cap l r
  exact (congrArg authLabels hs).trans (hm.trans (hq.trans hc))

theorem normalizeDeletion_label_local (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.label = u.core.label := by
  unfold normalizeDeletion; split <;> rfl

theorem prepared_label_local (hpsi : 0 < psi)
    (u : ExpiringAgentState psi kappa tau) :
    (prepareExpiringDisposal hpsi u).core.erase.core.label = u.core.core.label := by
  change (prepareBoundedDisposal hpsi u.core).erase.core.label = u.core.core.label
  rw [erase_prepareBoundedDisposal]
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion; split <;> rfl
  · rfl

private theorem pprime_left_label (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) :
    (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hpsi l r).1.core.label = l.core.label := by
  have hc := PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall_core hpsi l r
  have h := congrArg (fun q : AgentState psi × AgentState psi => q.1.label) hc
  change (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hpsi l r).1.core.label =
    (PPLLWallSweepRepair.pPsiLeaderResetProbeWall hpsi l.core r.core).1.label at h
  apply h.trans
  unfold PPLLWallSweepRepair.pPsiLeaderResetProbeWall
  dsimp only
  exact (PPLLVerify.pPsi_initiator_label_eq hpsi _ _).trans (by split <;> rfl)

/-- Opaque ordinary-priority left-label transport. -/
theorem ordinary_left_label
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi) :
    (doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa l r).1.core.label =
      l.core.label := by
  have ho := congrArg Prod.fst (ordinary_labels hpsi hwidth hle kappa l r)
  change (doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa l r).1.core.label =
    (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hpsi l r).1.core.label at ho
  exact ho.trans (pprime_left_label hpsi l r)

end B9SpliceV8BirthCaseAdapterLabelProjection

#print axioms B9SpliceV8BirthCaseAdapterLabelProjection.ordinary_left_label
