import Leader.Wu.Birth.ShortDoneTerminalPassiveThroughCheck


namespace BirthShortDoneTerminalPassiveR3


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
  PPLLCompleteMultiLeaderCleanup PPLLWriteSeqPersistenceRepair
  BirthGenerationDone BirthTossCheckPreservationRepair
  BirthCheckCongestGuardRepair BirthStationaryWrite
  BirthWaitPassive BirthShortWait BirthShortDoneCuts
  BirthShortWaitTerminalEntryRepair BirthShortDoneTerminalEntryCut
  BirthShortDoneTerminalPassiveR1 BirthShortDoneTerminalPassiveR2
  BirthShortDoneTerminalHost K2BirthDispatcher K2BirthLeaderNormalize
  ExpiringK2Projection LDSinkKernelC K2OutputSafety


open BirthGenerationControlRepair BirthArrivalCaptureRepair
  BirthSingleUseReleaseRepair BirthSigMoveDisposalRepair PPLLWriteIncrementGate


set_option autoImplicit false
set_option pp.structureInstances false


variable {psi kappa tau : Nat}


def wr (hpsi : 0 < psi) (a b : Registers psi) :
    Registers psi × Registers psi :=
  ({a with writer := .none},
   {b with writer := if a.label < b.label ∨ b.label = ⟨0,hpsi⟩
     then .depart else .none})


private theorem bw_cell (hpsi : 0 < psi) (h2 : 2 <= psi)
    (a b : Registers psi) :
    beforeWriteWidth hpsi (by decide : 0 < 2) h2
      ⟨cell a,false⟩ ⟨cell b,false⟩ =
      (⟨cell a,false⟩,⟨cell b,false⟩) := by
  simp [beforeWriteWidth, authorizedDisappear, disappear,
    authorizedCompareSigActionOne, compareSigInit, authorizedCmpUpdate,
    freshComparisonStart, cmpUpdateReturnPriority, cmpUpdateSetPath2,
    compareSigDispatchActionOne, compareBitActionOne,
    authorizedSuppressWidth, suppressSigResetKillWidth, suppressPrefix,
    suppressSigStart, resetKillComparison, suppressSigMoveReset,
    shortCountReset, suppressSigTerminal, suppressSigEcho, suppressSigFinish,
    authorizedReconcile, reconcilePermit, normalizePermit, cell]


private theorem st_cell (hpsi : 0 < psi) (a b : Registers psi) :
    stationaryPersistentAuthorizedRow hpsi ⟨cell a,false⟩ ⟨cell b,false⟩ =
      (⟨cell (wr hpsi a b).1,false⟩,⟨cell (wr hpsi a b).2,false⟩) := by
  simp [stationaryPersistentAuthorizedRow, stationaryPersistentRaw,
    swPersistentThroughPrepare, clearInputIncrementPair, clearIncrementAction,
    groupInfo, writeSeqGenerate, writeSeqPrepareTransport,
    writeSeqReadyTransport, writeSeqSetWriteReadyTransport,
    writeSeqCompare, writeSeqCommands, writeSeqSetWriteAct,
    gatePreparedIncrement, writeSeqAfterPrepareComparisonTransport,
    writeActionPreservingComparison, writeActionActivateNonempty,
    writeActionExecutePreservingComparison, writeActionExecutePreservingDepart,
    writeActionToState, writeActionApplyOverwrite, writeActionApplyMoveFlip,
    writeActionApplyIncrementAndFlip, writeActionPropagateState,
    moveWsigStopAligned, moveWsigStart, moveWsigCheckLast,
    moveWsigTransferStopAligned, moveWsigFinishPreservingCommand,
    moveWsigMoveWritePreservingNonempty, moveWsigLeaderSignal,
    moveWsigSignalMove, moveWsigEchoMove, authorizedReconcile,
    reconcilePermit, normalizePermit, wr, cell]
  split <;> rfl


private theorem aft_cell (hpsi : 0 < psi) (h2 : 2 <= psi)
    (a b : Registers psi) :
    afterCheckMetadataWidth hpsi (by decide : 0 < 2) h2
      ⟨cell a,false⟩ ⟨cell b,false⟩ =
      (⟨cell (wr hpsi a b).1,false⟩,⟨cell (wr hpsi a b).2,false⟩) := by
  unfold afterCheckMetadataWidth
  rw [bw_cell hpsi h2 a b]
  exact st_cell hpsi a b


private theorem auth_cell2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (a b : Registers psi) (pa pb : Bool)
    (hab : b.label = ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (ha : a.wait = true) (hb : b.wait = true)
    (hc : PreCapEntry2 hpsi h2 kappa (cell a) (cell b)) :
    let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
    let d := wr hpsi (registers w.1) (registers w.2)
    doneMetadataAuthorizedEntryWidth hpsi (by decide : 0 < 2) h2 kappa
      ⟨cell a,pa⟩ ⟨cell b,pb⟩ = (⟨cell d.1,false⟩,⟨cell d.2,false⟩) := by
  let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
  let d := wr hpsi (registers w.1) (registers w.2)
  have ht : doneThroughCheckEntryWidth hpsi (by decide : 0 < 2) h2 kappa
      ⟨cell a,pa⟩ ⟨cell b,pb⟩ =
      (⟨cell (registers w.1),false⟩,⟨cell (registers w.2),false⟩) :=
    through_entry_cell2 hpsi h2 kappa a b pa pb hab ha hb hc
  unfold doneMetadataAuthorizedEntryWidth
  dsimp only
  simp only [normalize_cell, active_cell, Bool.false_eq_true, if_false]
  unfold doneOrdinaryMetadataEntryWidth
  rw [ht]
  dsimp only
  rw [aft_cell hpsi h2 (registers w.1) (registers w.2)]
  have hborn : authBirth ⟨cell a,pa⟩ ⟨cell b,pb⟩
      (⟨cell d.1,false⟩,⟨cell d.2,false⟩) = false := by rfl
  rw [hborn]
  rfl


private theorem meta_cells2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : ExpiringAgentState psi kappa tau) (a b : Registers psi)
    (hl : raw l = cell a) (hr : raw r = cell b)
    (hab : b.label = ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (ha : a.wait = true) (hb : b.wait = true)
    (hc : PreCapEntry2 hpsi h2 kappa (cell a) (cell b)) :
    let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
    let d := wr hpsi (registers w.1) (registers w.2)
    (BirthShortDoneTerminalHost.metadata hpsi (by decide : 0 < 2) h2 l r).1.core.erase =
      ⟨cell d.1,false⟩ ∧
    (BirthShortDoneTerminalHost.metadata hpsi (by decide : 0 < 2) h2 l r).2.core.erase =
      ⟨cell d.2,false⟩ := by
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let bnd := doneMetadataBoundedEntryWidth hpsi (by decide : 0 < 2) h2 l0.core r0.core
  let lo : ExpiringAgentState psi kappa tau := ⟨bnd.1,l0.stall⟩
  let ro : ExpiringAgentState psi kappa tau := ⟨bnd.2,r0.stall⟩
  let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
  let d := wr hpsi (registers w.1) (registers w.2)
  have hauth : doneMetadataAuthorizedEntryWidth hpsi (by decide : 0 < 2) h2 kappa
      l0.core.erase r0.core.erase = (⟨cell d.1,false⟩,⟨cell d.2,false⟩) := by
    rw [prepared_erasure hpsi l a hl, prepared_erasure hpsi r b hr]
    exact auth_cell2 hpsi h2 kappa a b _ _ hab ha hb hc
  have he := doneMetadataBoundedEntryWidth_erase hpsi (by decide : 0 < 2) h2
    l0.core r0.core
  have hbnd := he.trans hauth
  have el := expiry_cell l0 lo d.1 (congrArg Prod.fst hbnd)
  have er := expiry_cell r0 ro d.2 (congrArg Prod.snd hbnd)
  have hraw :
      (doneMetadataEntryWidth hpsi (by decide : 0 < 2) h2 l r).1.core.erase =
        ⟨cell d.1,false⟩ ∧
      (doneMetadataEntryWidth hpsi (by decide : 0 < 2) h2 l r).2.core.erase =
        ⟨cell d.2,false⟩ := by
    unfold doneMetadataEntryWidth
    exact ⟨el,er⟩
  have hL := congrArg (fun s : AuthorizedAgentState psi => s.core.leader) hraw.1
  have hR := congrArg (fun s : AuthorizedAgentState psi => s.core.leader) hraw.2
  change (doneMetadataEntryWidth hpsi (by decide : 0 < 2) h2 l r).1.core.core.leader =
    false at hL
  change (doneMetadataEntryWidth hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader =
    false at hR
  change
    (normalizeLeader hpsi (doneMetadataEntryWidth hpsi (by decide : 0 < 2) h2 l r).1).core.erase =
      ⟨cell d.1,false⟩ ∧
    (normalizeLeader hpsi (doneMetadataEntryWidth hpsi (by decide : 0 < 2) h2 l r).2).core.erase =
      ⟨cell d.2,false⟩
  simpa only [normalizeLeader, hL, hR, Bool.false_eq_true, if_false] using hraw


private def quiet : AgentState 1 :=
  PPLLNoCheckBirthConditionTwoProtocol.PeaceView.toState ⟨false,0,false,0,0⟩


private theorem obs_cell (u : ExpiringAgentState psi kappa tau)
    (d : Registers psi) (h : u.core.erase = ⟨cell d,false⟩) :
    observeCell u = quiet := by
  have hc := congrArg (fun s : AuthorizedAgentState psi => s.core) h
  change u.core.core.erase = cell d at hc
  unfold observeCell quiet
  rw [hc]
  rfl


private theorem fin_cells (hpsi : 0 < psi)
    (oldL oldR metaL metaR : ExpiringAgentState psi kappa tau)
    (a b : Registers psi) (hl : metaL.core.erase = ⟨cell a,false⟩)
    (hr : metaR.core.erase = ⟨cell b,false⟩) :
    finalPhysical hpsi oldL oldR metaL metaR = (metaL,metaR) := by
  have ol := obs_cell metaL a hl
  have or := obs_cell metaR b hr
  have ll := congrArg (fun s : AuthorizedAgentState psi => s.core.leader) hl
  have lr := congrArg (fun s : AuthorizedAgentState psi => s.core.leader) hr
  change metaL.core.core.leader = false at ll
  change metaR.core.core.leader = false at lr
  have hnl : newborn oldL metaL = false := by simp [newborn, ll]
  have hnr : newborn oldR metaR = false := by simp [newborn, lr]
  rw [finalPhysical_of_no_birth hpsi oldL oldR metaL metaR hnl hnr]
  rw [collisionRow_of_not_both hpsi metaL metaR (by simp [ll,lr])]
  unfold ExpiringK2Projection.row
  rw [ol,or]
  have hk : sinkKernelC (by decide : 0 < 1) quiet quiet = (quiet,quiet) := by decide
  rw [hk]
  exact Prod.ext (by simpa [ol] using putSignals_self metaL)
    (by simpa [or] using putSignals_self metaR)


theorem full_terminal_row2_preCap (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa tau : Nat) (l r : ExpiringAgentState psi kappa tau)
    (a b : Registers psi) (hl : raw l = cell a) (hr : raw r = cell b)
    (ha : a.wait = true) (hb : b.wait = true)
    (hab : b.label = ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hc : PreCapEntry2 hpsi h2 kappa (cell a) (cell b)) :
    let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
    let q := BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2 l r
    clock (raw q.1) = clock w.1 ∧ clock (raw q.2) = clock w.2 ∧
      Passive (raw q.1) ∧ Passive (raw q.2) := by
  let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
  let d := wr hpsi (registers w.1) (registers w.2)
  let q := BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2 l r
  let m := BirthShortDoneTerminalHost.metadata
    (κ := kappa) (τ := tau) hpsi (by decide : 0 < 2) h2 l r
  change clock (raw q.1) = clock w.1 ∧ clock (raw q.2) = clock w.2 ∧
    Passive (raw q.1) ∧ Passive (raw q.2)
  have hm : m.1.core.erase = ⟨cell d.1,false⟩ ∧
      m.2.core.erase = ⟨cell d.2,false⟩ :=
    meta_cells2 hpsi h2 l r a b hl hr hab ha hb hc
  have hf : finalPhysical hpsi l r m.1 m.2 = (m.1,m.2) :=
    fin_cells hpsi l r m.1 m.2 d.1 d.2 hm.1 hm.2
  have hq : q.1.core.erase = ⟨cell d.1,false⟩ ∧
      q.2.core.erase = ⟨cell d.2,false⟩ := by
    change (finalPhysical hpsi l r m.1 m.2).1.core.erase = ⟨cell d.1,false⟩ ∧
      (finalPhysical hpsi l r m.1 m.2).2.core.erase = ⟨cell d.2,false⟩
    rw [hf]
    exact hm
  have hw : w.1.wait = true ∧ w.2.wait = true :=
    waitWidthEntry2_armed_of_preCap hpsi h2 kappa (cell a) (cell b)
      (by change a.wait = true; exact ha) (by change b.wait = true; exact hb) hc
  have ql : raw q.1 = cell d.1 :=
    congrArg (fun s : AuthorizedAgentState psi => s.core) hq.1
  have qr : raw q.2 = cell d.2 :=
    congrArg (fun s : AuthorizedAgentState psi => s.core) hq.2
  rw [ql,qr]
  constructor
  · simp [clock,d,wr,registers,cell]
  constructor
  · simp [clock,d,wr,registers,cell]
  constructor
  · refine ⟨metadata_cell _, ?_, ?_⟩
    · simpa [d,wr,registers,cell] using hw.1
    · simp [InertWriter,d,wr,cell]
  · refine ⟨metadata_cell _, ?_, ?_⟩
    · simpa [d,wr,registers,cell] using hw.2
    · by_cases hwr : (registers w.1).label < (registers w.2).label ∨
          (registers w.2).label = ⟨0,hpsi⟩
      · simp [InertWriter,d,wr,cell,hwr]
      · simp [InertWriter,d,wr,cell,hwr]


#print axioms BirthShortDoneTerminalPassiveR3.full_terminal_row2_preCap


end BirthShortDoneTerminalPassiveR3

