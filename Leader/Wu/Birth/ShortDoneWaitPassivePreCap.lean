import Leader.Wu.Birth.ShortDoneCuts
import Leader.Wu.Birth.ShortDoneDispatcher
import Leader.Wu.Birth.WaitPassiveStopped
import Leader.Wu.Elimination.BirthDispatcherLeaderNormalize

namespace BirthShortDoneWaitPassiveR1

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
  PPLLCompleteMultiLeaderCleanup PPLLWriteSeqPersistenceRepair
  BirthGenerationDone BirthTossCheckPreservationRepair
  BirthCheckCongestGuardRepair BirthStationaryWrite
  BirthWaitPassive BirthShortWait BirthShortDoneCuts
  K2BirthDispatcher K2BirthLeaderNormalize ExpiringK2Projection
  LDSinkKernelC K2OutputSafety

open BirthGenerationControlRepair BirthArrivalCaptureRepair
  BirthSingleUseReleaseRepair BirthSigMoveDisposalRepair PPLLWriteIncrementGate

set_option autoImplicit false
set_option pp.structureInstances false

variable {psi kappa tau : Nat}

/-- Actual short-width state immediately before Finish. -/
def preFinish2 (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (l r : AgentState psi) : AgentState psi × AgentState psi :=
  let p := waitSaturatedPrepare hpsi l r
  let c := waitWidthCarry (by decide : 0 < 2) h2 kappa p.1 p.2
  waitWidthReset (by decide : 0 < 2) h2 c.1 c.2

/-- Minimal current-state exclusion of the real width-two cap branch. -/
def PreCap2 (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (l r : AgentState psi) : Prop :=
  let s := preFinish2 hpsi h2 kappa l r
  ¬ (s.2.label = widthTerminal (by decide : 0 < 2) h2 ∧ s.2.count = kappa)

private theorem prepare2_wait_frame (hpsi : 0 < psi)
    (l r : AgentState psi) :
    let q := waitSaturatedPrepare hpsi l r
    q.1.wait = l.wait ∧ q.2.wait = r.wait := by
  unfold waitSaturatedPrepare
  split <;> try dsimp only
  all_goals split <;> try dsimp only
  all_goals first
    | exact ⟨rfl, rfl⟩
    | (split <;> exact ⟨rfl, rfl⟩)

private theorem carry2_wait_frame (h2 : 2 <= psi) (kappa : Nat)
    (l r : AgentState psi) :
    let q := waitWidthCarry (by decide : 0 < 2) h2 kappa l r
    q.1.wait = l.wait ∧ q.2.wait = r.wait := by
  unfold waitWidthCarry
  split <;> try dsimp only
  · split <;> try dsimp only
    · split <;> try dsimp only
      · split <;> exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem reset2_wait_frame (h2 : 2 <= psi)
    (l r : AgentState psi) :
    let q := waitWidthReset (by decide : 0 < 2) h2 l r
    q.1.wait = l.wait ∧ q.2.wait = r.wait := by
  unfold waitWidthReset
  split <;> try dsimp only
  · split <;> try dsimp only
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem prepare2_metadata (hpsi : 0 < psi)
    (a b : Registers psi) :
    let q := waitSaturatedPrepare hpsi (cell a) (cell b)
    Metadata q.1 ∧ Metadata q.2 := by
  unfold waitSaturatedPrepare
  split <;> try dsimp only
  all_goals split <;> try dsimp only
  all_goals first
    | exact ⟨rfl, rfl⟩
    | (split <;> exact ⟨rfl, rfl⟩)

private theorem carry2_metadata (h2 : 2 <= psi) (kappa : Nat)
    (a b : Registers psi) :
    let q := waitWidthCarry (by decide : 0 < 2) h2 kappa (cell a) (cell b)
    Metadata q.1 ∧ Metadata q.2 := by
  unfold waitWidthCarry
  split <;> try dsimp only
  · split <;> try dsimp only
    · split <;> try dsimp only
      · split <;> exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem reset2_metadata (h2 : 2 <= psi)
    (a b : Registers psi) :
    let q := waitWidthReset (by decide : 0 < 2) h2 (cell a) (cell b)
    Metadata q.1 ∧ Metadata q.2 := by
  unfold waitWidthReset
  split <;> try dsimp only
  · split <;> try dsimp only
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem finish2_metadata (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (a b : Registers psi) :
    let q := waitWidthFinish hpsi (by decide : 0 < 2) h2 kappa
      (cell a) (cell b)
    Metadata q.1 ∧ Metadata q.2 := by
  unfold waitWidthFinish
  split <;> try dsimp only
  · split <;> exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

private theorem preFinish2_wait (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (l r : AgentState psi) :
    let s := preFinish2 hpsi h2 kappa l r
    s.1.wait = l.wait ∧ s.2.wait = r.wait := by
  let p := waitSaturatedPrepare hpsi l r
  have hp : p.1.wait = l.wait ∧ p.2.wait = r.wait :=
    prepare2_wait_frame hpsi l r
  let c := waitWidthCarry (by decide : 0 < 2) h2 kappa p.1 p.2
  have hc : c.1.wait = p.1.wait ∧ c.2.wait = p.2.wait :=
    carry2_wait_frame h2 kappa p.1 p.2
  let s := waitWidthReset (by decide : 0 < 2) h2 c.1 c.2
  have hs : s.1.wait = c.1.wait ∧ s.2.wait = c.2.wait :=
    reset2_wait_frame h2 c.1 c.2
  change s.1.wait = l.wait ∧ s.2.wait = r.wait
  exact ⟨hs.1.trans (hc.1.trans hp.1),
    hs.2.trans (hc.2.trans hp.2)⟩

private theorem waitWidth2_metadata (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (a b : Registers psi) :
    let w := waitWidth hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
    w.1 = cell (registers w.1) ∧ w.2 = cell (registers w.2) := by
  let p := waitSaturatedPrepare hpsi (cell a) (cell b)
  have hp : Metadata p.1 ∧ Metadata p.2 := prepare2_metadata hpsi a b
  let c := waitWidthCarry (by decide : 0 < 2) h2 kappa p.1 p.2
  have hc : Metadata c.1 ∧ Metadata c.2 := by
    unfold c
    rw [hp.1, hp.2]
    exact carry2_metadata h2 kappa (registers p.1) (registers p.2)
  let s := waitWidthReset (by decide : 0 < 2) h2 c.1 c.2
  have hs : Metadata s.1 ∧ Metadata s.2 := by
    unfold s
    rw [hc.1, hc.2]
    exact reset2_metadata h2 (registers c.1) (registers c.2)
  change let w := waitWidthFinish hpsi (by decide : 0 < 2) h2 kappa s.1 s.2
    Metadata w.1 ∧ Metadata w.2
  rw [hs.1, hs.2]
  exact finish2_metadata hpsi h2 kappa (registers s.1) (registers s.2)

/-- Pre-cap is exactly enough to keep both physical WAIT bits armed. -/
theorem waitWidth2_armed_of_preCap (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (l r : AgentState psi)
    (hl : l.wait = true) (hr : r.wait = true)
    (hc : PreCap2 hpsi h2 kappa l r) :
    let w := waitWidth hpsi (by decide : 0 < 2) h2 kappa l r
    w.1.wait = true ∧ w.2.wait = true := by
  let s := preFinish2 hpsi h2 kappa l r
  have hs : s.1.wait = l.wait ∧ s.2.wait = r.wait :=
    preFinish2_wait hpsi h2 kappa l r
  have hsl : s.1.wait = true := hs.1.trans hl
  have hsr : s.2.wait = true := hs.2.trans hr
  change ¬ (s.2.label = widthTerminal (by decide : 0 < 2) h2 ∧
    s.2.count = kappa) at hc
  unfold waitWidth
  change
    (waitWidthFinish hpsi (by decide : 0 < 2) h2 kappa s.1 s.2).1.wait = true ∧
    (waitWidthFinish hpsi (by decide : 0 < 2) h2 kappa s.1 s.2).2.wait = true
  simp [waitWidthFinish, hc, hsl, hsr]

private theorem genWidth2_cell (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (a b : Registers psi)
    (ha : a.wait = true) (hb : b.wait = true)
    (hc : PreCap2 hpsi h2 kappa (cell a) (cell b)) :
    let w := waitWidth hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
    genCleanWidth hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b) =
      (cell (registers w.1), cell (registers w.2)) := by
  let w := waitWidth hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
  have hm : w.1 = cell (registers w.1) ∧ w.2 = cell (registers w.2) :=
    waitWidth2_metadata hpsi h2 kappa a b
  have hw : w.1.wait = true ∧ w.2.wait = true :=
    waitWidth2_armed_of_preCap hpsi h2 kappa (cell a) (cell b)
      (by change a.wait = true; exact ha)
      (by change b.wait = true; exact hb) hc
  unfold genCleanWidth
  dsimp only
  change genCleanAfterWait hpsi w.1 w.2 =
    (cell (registers w.1), cell (registers w.2))
  conv => lhs; rw [hm.1, hm.2]
  exact gen_after_wait_cell hpsi (registers w.1) (registers w.2) (by
    intro _
    change w.1.wait = true
    exact hw.1)


private theorem generation_cell2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (a b : Registers psi) (pa pb : Bool)
    (hab : b.label = ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (ha : a.wait = true) (hb : b.wait = true)
    (hc : PreCap2 hpsi h2 kappa (cell a) (cell b)) :
    let w := waitWidth hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
    generationBeforeMoveWidth hpsi (by decide : 0 < 2) h2 kappa
      ⟨cell a,pa⟩ ⟨cell b,pb⟩ =
      (⟨cell (registers w.1),false⟩, ⟨cell (registers w.2),false⟩) := by
  let w := waitWidth hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
  have hg : genCleanWidth hpsi (by decide : 0 < 2) h2 kappa
      (cell a) (cell b) =
      (cell (registers w.1), cell (registers w.2)) :=
    genWidth2_cell hpsi h2 kappa a b ha hb hc
  unfold generationBeforeMoveWidth
  rw [wall_cell hpsi a b pa pb hab]
  simp only [authorizedGenCleanWidth, authorizedReconcile, hg]
  simp only [reconcile_cell]
  simp only [authorizedCleanSig, authorizedReconcile]
  rw [clean_cell hpsi (registers w.1) (registers w.2)]
  simp only [reconcile_cell]
  simp only [authorizedEliminateSig, authorizedReconcile]
  have he : eliminateSig hpsi
      (cell (registers w.1)) (cell (registers w.2)) =
      (cell (registers w.1), cell (registers w.2)) := by
    simp [eliminateSig, cell]
  rw [he]
  simp only [reconcile_cell]
  rfl

private theorem done_move_cell (hpsi : 0 < psi) (a b : Registers psi) :
    authorizedDoneMove hpsi ⟨cell a,false⟩ ⟨cell b,false⟩ =
      (⟨cell a,false⟩,⟨cell b,false⟩) := by
  have hp :
      (sigMoveLeaderPreclear hpsi (cell a) (cell b)).1.state ≠ .done := by
    simp [sigMoveLeaderPreclear, incompleteLeftLeaderBoundary,
      clearIfLeader, cell]
  rw [authorizedDoneMove_eq_singleUse hpsi _ _ hp]
  have hcap : authorizedCaptureSigMove hpsi
      ⟨cell a,false⟩ ⟨cell b,false⟩ =
        (⟨cell a,false⟩,⟨cell b,false⟩) := by
    unfold authorizedCaptureSigMove
    rw [capture_cell hpsi a b]
    simp [pathMovedRight, reconcilePermit, normalizePermit, cell]
  unfold authorizedSingleUseReleaseMove
  rw [hcap]
  simp [clearTerminalRelease, cell]

private theorem done_tail_cell (hpsi : 0 < psi) (a b : Registers psi) :
    let m := authorizedDoneMove hpsi ⟨cell a,false⟩ ⟨cell b,false⟩
    let p := PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair hpsi
      (preCheckResetWall m.1 m.2)
    preserveDoneCheck hpsi p.1 p.2 = (⟨cell a,false⟩,⟨cell b,false⟩) := by
  dsimp only
  rw [done_move_cell hpsi a b]
  rw [preCheckResetWall_eq_of_inactive _ _ rfl rfl rfl]
  have hs (d : Registers psi) :
      sanitizeAuthorizedTerminalEqual hpsi ⟨cell d,false⟩ =
        ⟨cell d,false⟩ := by
    simp [sanitizeAuthorizedTerminalEqual, unsupportedTerminalEqual, cell]
  simp only [PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair, hs]
  rw [preserveDoneCheck_of_no_done hpsi _ _
    (by simp [cell]) (by simp [cell])]
  rw [preserveTossCheck_of_no_toss hpsi _ _
    (by simp [cell]) (by simp [cell])]
  exact guarded_check_cell hpsi a b

private theorem through_cell2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (a b : Registers psi) (pa pb : Bool)
    (hab : b.label = ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (ha : a.wait = true) (hb : b.wait = true)
    (hc : PreCap2 hpsi h2 kappa (cell a) (cell b)) :
    let w := waitWidth hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
    doneThroughCheckWidth hpsi (by decide : 0 < 2) h2 kappa
      ⟨cell a,pa⟩ ⟨cell b,pb⟩ =
      (⟨cell (registers w.1),false⟩,⟨cell (registers w.2),false⟩) := by
  unfold doneThroughCheckWidth doneBeforeCheckWidth
  rw [generation_cell2 hpsi h2 kappa a b pa pb hab ha hb hc]
  exact done_tail_cell hpsi _ _


/-- Exact passive WRITE image; `.depart` is retained physically. -/
def writerRegs (hpsi : 0 < psi) (a b : Registers psi) :
    Registers psi × Registers psi :=
  ({a with writer := .none},
    {b with writer := if a.label < b.label ∨ b.label = ⟨0,hpsi⟩
      then .depart else .none})

private theorem beforeWrite_cell (hpsi : 0 < psi) (h2 : 2 <= psi)
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

private theorem stationary_cell (hpsi : 0 < psi) (a b : Registers psi) :
    stationaryPersistentAuthorizedRow hpsi ⟨cell a,false⟩ ⟨cell b,false⟩ =
      (⟨cell (writerRegs hpsi a b).1,false⟩,
       ⟨cell (writerRegs hpsi a b).2,false⟩) := by
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
    reconcilePermit, normalizePermit, writerRegs, cell]
  split <;> rfl

private theorem after_cell (hpsi : 0 < psi) (h2 : 2 <= psi)
    (a b : Registers psi) :
    afterCheckMetadataWidth hpsi (by decide : 0 < 2) h2
      ⟨cell a,false⟩ ⟨cell b,false⟩ =
      (⟨cell (writerRegs hpsi a b).1,false⟩,
       ⟨cell (writerRegs hpsi a b).2,false⟩) := by
  unfold afterCheckMetadataWidth
  rw [beforeWrite_cell hpsi h2 a b]
  exact stationary_cell hpsi a b

private theorem authorized_cell2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (a b : Registers psi) (pa pb : Bool)
    (hab : b.label = ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (ha : a.wait = true) (hb : b.wait = true)
    (hc : PreCap2 hpsi h2 kappa (cell a) (cell b)) :
    let w := waitWidth hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
    let d := writerRegs hpsi (registers w.1) (registers w.2)
    doneMetadataAuthorizedWidth hpsi (by decide : 0 < 2) h2 kappa
      ⟨cell a,pa⟩ ⟨cell b,pb⟩ = (⟨cell d.1,false⟩,⟨cell d.2,false⟩) := by
  let w := waitWidth hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
  let d := writerRegs hpsi (registers w.1) (registers w.2)
  change doneMetadataAuthorizedWidth hpsi (by decide : 0 < 2) h2 kappa
      ⟨cell a,pa⟩ ⟨cell b,pb⟩ =
    (⟨cell d.1,false⟩,⟨cell d.2,false⟩)
  have ht :
      doneThroughCheckWidth hpsi (by decide : 0 < 2) h2 kappa
        ⟨cell a,pa⟩ ⟨cell b,pb⟩ =
      (⟨cell (registers w.1),false⟩,
       ⟨cell (registers w.2),false⟩) :=
    through_cell2 hpsi h2 kappa a b pa pb hab ha hb hc
  unfold doneMetadataAuthorizedWidth
  simp only [normalize_cell, active_cell, Bool.false_eq_true, if_false]
  unfold doneOrdinaryMetadataWidth
  rw [ht]
  dsimp only
  rw [after_cell hpsi h2 (registers w.1) (registers w.2)]
  have hborn :
      authBirth ⟨cell a,pa⟩ ⟨cell b,pb⟩
        (⟨cell d.1,false⟩,⟨cell d.2,false⟩) = false := by
    rfl
  rw [hborn]
  rfl

/-- Local source-identical copy of the unaccepted endpoint composition,
specialized only to width two; it does not import the original. -/
def metadata2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : ExpiringAgentState psi kappa tau) :=
  let q := doneMetadataWidth hpsi (by decide : 0 < 2) h2 l r
  (normalizeLeader hpsi q.1, normalizeLeader hpsi q.2)

def row2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : ExpiringAgentState psi kappa tau) :=
  let q := metadata2 hpsi h2 l r
  finalPhysical hpsi l r q.1 q.2

private theorem metadata_cells2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : ExpiringAgentState psi kappa tau) (a b : Registers psi)
    (hl : raw l = cell a) (hr : raw r = cell b)
    (hab : b.label = ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (ha : a.wait = true) (hb : b.wait = true)
    (hc : PreCap2 hpsi h2 kappa (cell a) (cell b)) :
    let w := waitWidth hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
    let d := writerRegs hpsi (registers w.1) (registers w.2)
    (metadata2 hpsi h2 l r).1.core.erase = ⟨cell d.1,false⟩ ∧
    (metadata2 hpsi h2 l r).2.core.erase = ⟨cell d.2,false⟩ := by
  let l0 := prepareExpiringDisposal hpsi l
  let r0 := prepareExpiringDisposal hpsi r
  let bnd := doneMetadataBoundedWidth hpsi (by decide : 0 < 2) h2 l0.core r0.core
  let lo : ExpiringAgentState psi kappa tau := ⟨bnd.1,l0.stall⟩
  let ro : ExpiringAgentState psi kappa tau := ⟨bnd.2,r0.stall⟩
  let w := waitWidth hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
  let d := writerRegs hpsi (registers w.1) (registers w.2)
  have hauth : doneMetadataAuthorizedWidth hpsi (by decide : 0 < 2) h2 kappa
      l0.core.erase r0.core.erase = (⟨cell d.1,false⟩,⟨cell d.2,false⟩) := by
    rw [prepared_erasure hpsi l a hl, prepared_erasure hpsi r b hr]
    exact authorized_cell2 hpsi h2 kappa a b _ _ hab ha hb hc
  have he := doneMetadataBoundedWidth_erase hpsi (by decide : 0 < 2) h2
    l0.core r0.core
  have hbnd := he.trans hauth
  have el := expiry_cell l0 lo d.1 (congrArg Prod.fst hbnd)
  have er := expiry_cell r0 ro d.2 (congrArg Prod.snd hbnd)
  have hraw :
      (doneMetadataWidth hpsi (by decide : 0 < 2) h2 l r).1.core.erase =
          ⟨cell d.1,false⟩ ∧
      (doneMetadataWidth hpsi (by decide : 0 < 2) h2 l r).2.core.erase =
          ⟨cell d.2,false⟩ := by
    unfold doneMetadataWidth
    exact ⟨el,er⟩
  have hleadL :=
    congrArg (fun s : AuthorizedAgentState psi => s.core.leader) hraw.1
  change
    (doneMetadataWidth hpsi (by decide : 0 < 2) h2 l r).1.core.core.leader =
      false at hleadL
  have hleadR :=
    congrArg (fun s : AuthorizedAgentState psi => s.core.leader) hraw.2
  change
    (doneMetadataWidth hpsi (by decide : 0 < 2) h2 l r).2.core.core.leader =
      false at hleadR
  change
    (normalizeLeader hpsi
      (doneMetadataWidth hpsi (by decide : 0 < 2) h2 l r).1).core.erase =
        ⟨cell d.1,false⟩ ∧
    (normalizeLeader hpsi
      (doneMetadataWidth hpsi (by decide : 0 < 2) h2 l r).2).core.erase =
        ⟨cell d.2,false⟩
  simpa only [normalizeLeader, hleadL, hleadR, Bool.false_eq_true, if_false]
    using hraw

private def quiet : AgentState 1 :=
  PPLLNoCheckBirthConditionTwoProtocol.PeaceView.toState ⟨false,0,false,0,0⟩

private theorem observe_cell (u : ExpiringAgentState psi kappa tau)
    (d : Registers psi) (h : u.core.erase = ⟨cell d,false⟩) :
    observeCell u = quiet := by
  have hc := congrArg (fun s : AuthorizedAgentState psi => s.core) h
  change u.core.core.erase = cell d at hc
  unfold observeCell quiet
  rw [hc]
  rfl

private theorem final_cells (hpsi : 0 < psi)
    (oldL oldR metaL metaR : ExpiringAgentState psi kappa tau)
    (a b : Registers psi)
    (hl : metaL.core.erase = ⟨cell a,false⟩)
    (hr : metaR.core.erase = ⟨cell b,false⟩) :
    finalPhysical hpsi oldL oldR metaL metaR = (metaL,metaR) := by
  have ol := observe_cell metaL a hl
  have or := observe_cell metaR b hr
  have ll := congrArg (fun s : AuthorizedAgentState psi => s.core.leader) hl
  change metaL.core.core.leader = false at ll
  have lr := congrArg (fun s : AuthorizedAgentState psi => s.core.leader) hr
  change metaR.core.core.leader = false at lr
  have hnl : newborn oldL metaL = false := by
    simp [newborn, ll]
  have hnr : newborn oldR metaR = false := by
    simp [newborn, lr]
  rw [finalPhysical_of_no_birth hpsi oldL oldR metaL metaR hnl hnr]
  rw [collisionRow_of_not_both hpsi metaL metaR (by simp [ll,lr])]
  unfold ExpiringK2Projection.row
  rw [ol,or]
  have hk : sinkKernelC (by decide : 0 < 1) quiet quiet = (quiet,quiet) := by
    decide
  rw [hk]
  exact Prod.ext (by simpa [ol] using putSignals_self metaL)
    (by simpa [or] using putSignals_self metaR)

/-- Requested bounded one-row producer. The first two premises are literal
physical source identities; together with the two WAIT and two writer clauses
they are exactly passive inputs, with no hidden safety premise. -/
theorem full_row2_preCap (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa tau : Nat) (l r : ExpiringAgentState psi kappa tau)
    (a b : Registers psi)
    (hl : raw l = cell a) (hr : raw r = cell b)
    (ha : a.wait = true) (hb : b.wait = true)
    (hia : a.writer = .none ∨ a.writer = .depart)
    (hib : b.writer = .none ∨ b.writer = .depart)
    (hab : b.label = ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hc : PreCap2 hpsi h2 kappa (cell a) (cell b)) :
    let w := waitWidth hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
    let q := row2 (kappa := kappa) (tau := tau) hpsi h2 l r
    clock (raw q.1) = clock w.1 ∧ clock (raw q.2) = clock w.2 ∧
      Passive (raw q.1) ∧ Passive (raw q.2) := by
  let w := waitWidth hpsi (by decide : 0 < 2) h2 kappa (cell a) (cell b)
  let d := writerRegs hpsi (registers w.1) (registers w.2)
  let m := metadata2 (kappa := kappa) (tau := tau) hpsi h2 l r
  change
    clock (raw (row2 (kappa := kappa) (tau := tau) hpsi h2 l r).1) =
        clock w.1 ∧
    clock (raw (row2 (kappa := kappa) (tau := tau) hpsi h2 l r).2) =
        clock w.2 ∧
    Passive (raw (row2 (kappa := kappa) (tau := tau) hpsi h2 l r).1) ∧
    Passive (raw (row2 (kappa := kappa) (tau := tau) hpsi h2 l r).2)
  have hm :
      m.1.core.erase = ⟨cell d.1,false⟩ ∧
      m.2.core.erase = ⟨cell d.2,false⟩ :=
    metadata_cells2 hpsi h2 l r a b hl hr hab ha hb hc
  have hf : finalPhysical hpsi l r m.1 m.2 = (m.1,m.2) :=
    final_cells hpsi l r m.1 m.2 d.1 d.2 hm.1 hm.2
  have hq :
      (row2 (kappa := kappa) (tau := tau) hpsi h2 l r).1.core.erase =
          ⟨cell d.1,false⟩ ∧
      (row2 (kappa := kappa) (tau := tau) hpsi h2 l r).2.core.erase =
          ⟨cell d.2,false⟩ := by
    change
      (finalPhysical hpsi l r m.1 m.2).1.core.erase = ⟨cell d.1,false⟩ ∧
      (finalPhysical hpsi l r m.1 m.2).2.core.erase = ⟨cell d.2,false⟩
    rw [hf]
    exact hm
  have hw : w.1.wait = true ∧ w.2.wait = true :=
    waitWidth2_armed_of_preCap hpsi h2 kappa (cell a) (cell b)
      (by simpa [cell] using ha) (by simpa [cell] using hb) hc
  have ql :
      raw (row2 (kappa := kappa) (tau := tau) hpsi h2 l r).1 = cell d.1 :=
    congrArg (fun s : AuthorizedAgentState psi => s.core) hq.1
  have qr :
      raw (row2 (kappa := kappa) (tau := tau) hpsi h2 l r).2 = cell d.2 :=
    congrArg (fun s : AuthorizedAgentState psi => s.core) hq.2
  rw [ql,qr]
  constructor
  · simp [clock, d, writerRegs, registers, cell]
  constructor
  · simp [clock, d, writerRegs, registers, cell]
  constructor
  · refine ⟨metadata_cell _, ?_, ?_⟩
    · simpa [d,writerRegs,registers,cell] using hw.1
    · simp [InertWriter,d,writerRegs,cell]
  · refine ⟨metadata_cell _, ?_, ?_⟩
    · simpa [d,writerRegs,registers,cell] using hw.2
    · by_cases hwr : (registers w.1).label < (registers w.2).label ∨
          (registers w.2).label = ⟨0,hpsi⟩
      · simp [InertWriter,d,writerRegs,cell,hwr]
      · simp [InertWriter,d,writerRegs,cell,hwr]

/-- The raw metadata domain proof is still the frozen source-derived proof. -/
theorem metadata2_raw_domain (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    (doneMetadataWidth hpsi (by decide : 0 < 2) h2 l r).1.core.core.erase.inProtocolDomain kappa ∧
    (doneMetadataWidth hpsi (by decide : 0 < 2) h2 l r).2.core.core.erase.inProtocolDomain kappa :=
  doneMetadataWidth_domain hpsi (by decide : 0 < 2) h2 l r

/-! Exact finite cap witness: psi=3,width=2,kappa=tau=0. -/
def capA : Registers 3 := ⟨0,false,false,false,0,true,false,false,.none⟩
def capB : Registers 3 := ⟨1,false,false,false,0,true,false,false,.none⟩

theorem capA_domain : (cell capA).inProtocolDomain 0 := by
  simp [cell, capA, AgentState.inProtocolDomain]
theorem capB_domain : (cell capB).inProtocolDomain 0 := by
  simp [cell, capB, AgentState.inProtocolDomain]

def capL : ExpiringAgentState 3 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain (cell capA) capA_domain,false⟩,0⟩
def capR : ExpiringAgentState 3 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain (cell capB) capB_domain,false⟩,0⟩

theorem width2_cap_first_change :
    let w := waitWidth (psi := 3) (width := 2) (by decide) (by decide) (by decide)
      0 (raw capL) (raw capR)
    w.1.wait = false ∧ w.2.wait = true ∧
      (genCleanAfterWait (by decide : 0 < 3) w.1 w.2).1.state = .produce := by
  decide

#print axioms BirthShortDoneWaitPassiveR1.waitWidth2_armed_of_preCap
#print axioms BirthShortDoneWaitPassiveR1.full_row2_preCap
#print axioms BirthShortDoneWaitPassiveR1.metadata2_raw_domain
#print axioms BirthShortDoneWaitPassiveR1.width2_cap_first_change

/-- Executable identity to the current dispatcher, not a protocol-renaming premise. -/
theorem row2_eq_actual (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    row2 hpsi h2 l r = BirthShortDoneDispatcher.row
      (width := 2) hpsi (by decide) h2 l r := rfl

#print axioms row2_eq_actual

end BirthShortDoneWaitPassiveR1
