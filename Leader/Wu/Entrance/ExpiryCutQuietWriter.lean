import Leader.Wu.WriteSeq.StationaryWritePersistent
import Leader.Wu.WallSweep.NormalResetContract
import Leader.Wu.Entrance.ExpiryCutQuietInput


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B6EntranceExpiryWord


open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepNormalResetContract PPLLComparisonHistory
open PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair
open BirthSigMoveDisposalRepair BirthShortDoneCuts BirthStationaryWrite
open R1CandidateKernel
open B6EntranceV2


variable {n psi kappa tau : Nat}


attribute [local irreducible]
  writeSeqPrepareTransport writeActionPreservingComparison moveWsigStopAligned


/-- Cleanup-aux frame of the stationary persistent row.  Expose the row once,
then use only the seven accepted public substage frames. -/
theorem stationaryPersistentRaw_cleanupAux_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    cleanupAuxPair (stationaryPersistentRaw hpsi l r) =
      cleanupAuxPair (l, r) := by
  unfold stationaryPersistentRaw
  dsimp only
  unfold writeSeqAfterPrepareComparisonTransport
  dsimp only
  rw [moveWsigStopAligned_cleanupAux_frame]
  rw [writeActionPreservingComparison_cleanupAux_frame]
  rw [gatePreparedIncrementPair_cleanupAux_frame]
  unfold swPersistentThroughPrepare
  dsimp only
  rw [writeSeqPrepareTransport_cleanupAux_frame]
  rw [writeSeqGenerate_cleanupAux_frame]
  rw [groupInfo_cleanupAux_frame]
  rw [clearInputIncrementPair_cleanupAux_frame]


private theorem neutral_of_views {old out : AgentState psi}
    (ht : ComparisonTrackedView.ofState out =
      ComparisonTrackedView.ofState old)
    (ha : CleanupAuxView.ofState out = CleanupAuxView.ofState old)
    (ho : ComparisonNeutral old) : ComparisonNeutral out := by
  have hs := congrArg ComparisonTrackedView.state ht
  have hp := congrArg ComparisonTrackedView.path ht
  have hp2 := congrArg ComparisonTrackedView.path2 ht
  have hpc := congrArg ComparisonTrackedView.pCarry ht
  have hp4 := congrArg CleanupAuxView.path4 ha
  have hp5 := congrArg CleanupAuxView.path5 ha
  have hlot := congrArg CleanupAuxView.p ha
  change out.state = old.state at hs
  change out.path = old.path at hp
  change out.path2 = old.path2 at hp2
  change out.p_carry = old.p_carry at hpc
  change out.path4 = old.path4 at hp4
  change out.path5 = old.path5 at hp5
  change out.p = old.p at hlot
  exact ⟨hs.trans ho.1, hp.trans ho.2.1, hp2.trans ho.2.2.1,
    hp4.trans ho.2.2.2.1, hp5.trans ho.2.2.2.2.1,
    hlot.trans ho.2.2.2.2.2.1, hpc.trans ho.2.2.2.2.2.2⟩


/-- The stationary writer preserves `AuthQuiet`. -/
theorem stationaryPersistentAuthorizedRow_authQuiet
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi)
    (hl : AuthQuiet l) (hr : AuthQuiet r) :
    let z := stationaryPersistentAuthorizedRow hpsi l r
    AuthQuiet z.1 ∧ AuthQuiet z.2 := by
  let z := stationaryPersistentAuthorizedRow hpsi l r
  have hc := stationaryPersistentAuthorizedRow_core hpsi l r
  have htRaw := stationaryPersistentRaw_comparison hpsi l.core r.core
  have haRaw := stationaryPersistentRaw_cleanupAux_frame hpsi l.core r.core
  have ht : comparisonTrackedPair (z.1.core, z.2.core) =
      comparisonTrackedPair (l.core, r.core) :=
    (congrArg comparisonTrackedPair hc).trans htRaw
  have ha : cleanupAuxPair (z.1.core, z.2.core) =
      cleanupAuxPair (l.core, r.core) :=
    (congrArg cleanupAuxPair hc).trans haRaw
  have hnL : ComparisonNeutral l.core := by
    simpa only [RawQuiet, ComparisonNeutral] using hl.1
  have hnR : ComparisonNeutral r.core := by
    simpa only [RawQuiet, ComparisonNeutral] using hr.1
  have hzL := neutral_of_views (congrArg Prod.fst ht)
    (congrArg Prod.fst ha) hnL
  have hzR := neutral_of_views (congrArg Prod.snd ht)
    (congrArg Prod.snd ha) hnR
  have hp := stationaryPersistentAuthorizedRow_permits hpsi l r
  have hpL : z.1.path0Crossed = false := by
    calc
      z.1.path0Crossed = normalizePermit l.core l.path0Crossed := hp.1
      _ = false := by simp [normalizePermit, hl.1.2.1]
  have hpR : z.2.path0Crossed = false := by
    calc
      z.2.path0Crossed = normalizePermit r.core r.path0Crossed := hp.2
      _ = false := by simp [normalizePermit, hr.1.2.1]
  exact ⟨⟨by simpa only [RawQuiet, ComparisonNeutral] using hzL, hpL⟩,
    ⟨by simpa only [RawQuiet, ComparisonNeutral] using hzR, hpR⟩⟩


private theorem checkedSuffix_authQuiet
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Phys psi kappa tau)
    (hq : AuthQuiet (checkInput hpsi h2 l r).1 ∧
      AuthQuiet (checkInput hpsi h2 l r).2) :
    AuthQuiet (checkedSuffix hpsi h2 l r).1 ∧
      AuthQuiet (checkedSuffix hpsi h2 l r).2 := by
  have hw := writerInput_authQuiet_of_quiet_inputs hpsi h2 l r hq
  let w := writerInput hpsi h2 l r
  change AuthQuiet (stationaryPersistentAuthorizedRow hpsi w.1 w.2).1 ∧
    AuthQuiet (stationaryPersistentAuthorizedRow hpsi w.1 w.2).2
  exact stationaryPersistentAuthorizedRow_authQuiet hpsi w.1 w.2 hw.1 hw.2


end B6EntranceExpiryWord

namespace B6EntranceExpiryWord


open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
open BirthSigMoveDisposalRepair BirthShortDoneCuts BirthStationaryWrite
open R1CandidateKernel
open B6EntranceV2


variable {n psi kappa tau : Nat}


private theorem markLeaderBirth_authQuiet
    (born : Bool) (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hq : AuthQuiet q.1 ∧ AuthQuiet q.2) :
    AuthQuiet (markLeaderBirth born q).1 ∧
      AuthQuiet (markLeaderBirth born q).2 := by
  cases born <;>
    simp [markLeaderBirth, markComparisonForDeletion,
      hq.1.1.2.1, hq.2.1.2.1, hq]


/-- Local copy of the private helper in `B6ExpiryCutQuietLocal`. -/
private theorem prepareExpiringDisposal_eq_of_authQuiet
    (hpsi : 0 < psi) (u : Phys psi kappa tau)
    (hu : AuthQuiet u.core.erase) :
    prepareExpiringDisposal hpsi u = u := by
  have hp2 : u.core.erase.core.path2 = none := hu.1.2.2.1
  have hc : pendingTerminalDisposal hpsi u.core.erase.core = false := by
    simp [pendingTerminalDisposal, hp2]
  unfold prepareExpiringDisposal
  rw [prepareBoundedDisposal_eq_of_clear hpsi u.core hc]


private theorem normalizeDeletion_eq_of_authQuiet
    (u : AuthorizedAgentState psi) (hu : AuthQuiet u) :
    normalizeDeletion u = u := by
  unfold normalizeDeletion
  simp [hu.1.1]


private theorem deletionActive_false_of_authQuiet
    (u : AuthorizedAgentState psi) (hu : AuthQuiet u) :
    deletionActive u = false := by
  simp [deletionActive, pathPresent, hu.1.1, hu.1.2.1]


private theorem prepared_eq_of_authQuiet2
    (hpsi : 0 < psi) (u : Phys psi kappa tau)
    (hu : AuthQuiet u.core.erase) :
    prepared hpsi u = u.core.erase := by
  unfold prepared
  rw [prepareExpiringDisposal_eq_of_authQuiet hpsi u hu]
  exact normalizeDeletion_eq_of_authQuiet u.core.erase hu


private theorem deletionPriorityExpireOne_authQuiet
    (old out : Phys psi kappa tau)
    (hout : AuthQuiet out.core.erase) :
    AuthQuiet (deletionPriorityExpireOne tau old out).core.erase := by
  have hn : ComparisonNeutral out.core.erase.core := by
    simpa only [RawQuiet, ComparisonNeutral] using hout.1
  have hf :
      ComparisonNeutral
        (deletionPriorityExpireOne tau old out).core.erase.core := by
    unfold deletionPriorityExpireOne
    split
    · exact hn
    · unfold PPLLPathStallComparisonRepair.pathExpireOne
      split
      · exact hn
      · split
        · simp [ComparisonNeutral, clearComparisonCarrier,
            AuthorizedBoundedAgentState.erase, BoundedAgentState.erase] <;> rfl
        · exact hn
  have hp :
      (deletionPriorityExpireOne tau old out).core.erase.path0Crossed = false := by
    unfold deletionPriorityExpireOne
    split
    · exact hout.2
    · unfold PPLLPathStallComparisonRepair.pathExpireOne
      split
      · exact hout.2
      · split
        · rfl
        · exact hout.2
  exact ⟨by simpa only [RawQuiet, ComparisonNeutral] using hf, hp⟩


/-- Full local bridge. -/
theorem r1ExpiryCutQuiet_of_quiet_inputs
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Phys psi kappa tau)
    (hl : AuthQuiet l.core.erase)
    (hr : AuthQuiet r.core.erase)
    (hq : AuthQuiet (checkInput hpsi h2 l r).1 ∧
      AuthQuiet (checkInput hpsi h2 l r).2) :
    R1ExpiryCutQuiet hpsi h2 l r := by
  have hprepL := prepareExpiringDisposal_eq_of_authQuiet hpsi l hl
  have hprepR := prepareExpiringDisposal_eq_of_authQuiet hpsi r hr
  have hnormL := normalizeDeletion_eq_of_authQuiet l.core.erase hl
  have hnormR := normalizeDeletion_eq_of_authQuiet r.core.erase hr
  have hdelL := deletionActive_false_of_authQuiet l.core.erase hl
  have hdelR := deletionActive_false_of_authQuiet r.core.erase hr
  have hpl := prepared_eq_of_authQuiet2 hpsi l hl
  have hpr := prepared_eq_of_authQuiet2 hpsi r hr
  have hz := checkedSuffix_authQuiet hpsi h2 l r hq
  let z := checkedSuffix hpsi h2 l r
  have hzEq : z = afterCheckMetadataWidth
      hpsi (by decide : 0 < 2) h2
      (BirthCheckPermitRepair.permitFix
        (BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
          hpsi (by decide : 0 < 2) h2 kappa
          l.core.erase r.core.erase).1)
      (BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
        hpsi (by decide : 0 < 2) h2 kappa
        l.core.erase r.core.erase).2 := by
    unfold z checkedSuffix checkOutput
    rw [hpl, hpr]
  have hm := markLeaderBirth_authQuiet
    (K2BirthDispatcher.authBirth l.core.erase r.core.erase z) z hz
  have hord :
      AuthQuiet
          (BirthCheckPermitRepair.ordinary hpsi (by decide : 0 < 2) h2
            kappa l.core.erase r.core.erase).1 ∧
        AuthQuiet
          (BirthCheckPermitRepair.ordinary hpsi (by decide : 0 < 2) h2
            kappa l.core.erase r.core.erase).2 := by
    unfold BirthCheckPermitRepair.ordinary
    dsimp only
    rw [← hzEq]
    exact hm
  have hauth :
      AuthQuiet
          (BirthCheckPermitRepair.authorized hpsi (by decide : 0 < 2) h2
            kappa l.core.erase r.core.erase).1 ∧
        AuthQuiet
          (BirthCheckPermitRepair.authorized hpsi (by decide : 0 < 2) h2
            kappa l.core.erase r.core.erase).2 := by
    unfold BirthCheckPermitRepair.authorized
    rw [hnormL, hnormR]
    simp only [hdelR, Bool.false_eq_true, if_false, hdelL]
    exact hord
  let b := BirthCheckPermitRepair.bounded
    hpsi (by decide : 0 < 2) h2 l.core r.core
  have hb : AuthQuiet b.1.erase ∧ AuthQuiet b.2.erase := by
    unfold b BirthCheckPermitRepair.bounded
    dsimp only
    simpa only [AuthorizedBoundedAgentState.erase,
      BoundedAgentState.erase_ofDomain] using hauth
  let lBase : Phys psi kappa tau := ⟨b.1, l.stall⟩
  let rBase : Phys psi kappa tau := ⟨b.2, r.stall⟩
  have hbaseL : AuthQuiet lBase.core.erase := by
    simpa only [lBase] using hb.1
  have hbaseR : AuthQuiet rBase.core.erase := by
    simpa only [rBase] using hb.2
  unfold R1ExpiryCutQuiet BirthCheckPermitRepair.expiring
  rw [hprepL, hprepR]
  dsimp only
  change
    AuthQuiet (deletionPriorityExpireOne tau l lBase).core.erase ∧
      AuthQuiet (deletionPriorityExpireOne tau r rBase).core.erase
  exact ⟨deletionPriorityExpireOne_authQuiet l lBase hbaseL,
    deletionPriorityExpireOne_authQuiet r rBase hbaseR⟩


end B6EntranceExpiryWord
