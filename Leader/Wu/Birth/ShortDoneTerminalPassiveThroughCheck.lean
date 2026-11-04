import Leader.Wu.Birth.ShortDoneTerminalPassivePreCap

namespace BirthShortDoneTerminalPassiveR2

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
  PPLLCompleteMultiLeaderCleanup PPLLWriteSeqPersistenceRepair
  BirthGenerationDone BirthTossCheckPreservationRepair
  BirthCheckCongestGuardRepair BirthStationaryWrite
  BirthWaitPassive BirthShortWait BirthShortDoneCuts
  BirthShortWaitTerminalEntryRepair BirthShortDoneTerminalEntryCut
  BirthShortDoneTerminalPassiveR1
  K2BirthDispatcher K2BirthLeaderNormalize ExpiringK2Projection
  LDSinkKernelC K2OutputSafety

open BirthGenerationControlRepair BirthArrivalCaptureRepair
  BirthSingleUseReleaseRepair BirthSigMoveDisposalRepair PPLLWriteIncrementGate

set_option autoImplicit false
set_option pp.structureInstances false

variable {psi kappa tau : Nat}

/-- Ruler + repaired terminal-entry GEN + unchanged CLEAN/ELIMINATE. -/
theorem generation_entry_cell2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (a b : Registers psi) (pa pb : Bool)
    (hab : b.label = ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (ha : a.wait = true) (hb : b.wait = true)
    (hc : PreCapEntry2 hpsi h2 kappa (cell a) (cell b)) :
    let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa
      (cell a) (cell b)
    generationBeforeMoveEntryWidth hpsi (by decide : 0 < 2) h2 kappa
      ⟨cell a,pa⟩ ⟨cell b,pb⟩ =
      (⟨cell (registers w.1),false⟩,
       ⟨cell (registers w.2),false⟩) := by
  let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa
    (cell a) (cell b)
  have hg : genCleanEntryWidth hpsi (by decide : 0 < 2) h2 kappa
      (cell a) (cell b) =
      (cell (registers w.1), cell (registers w.2)) := by
    change genCleanAfterWait hpsi w.1 w.2 =
      (cell (registers w.1), cell (registers w.2))
    exact genAfterEntry2_cell hpsi h2 kappa a b ha hb hc
  unfold generationBeforeMoveEntryWidth
  rw [wall_cell hpsi a b pa pb hab]
  simp only [authorizedGenCleanEntryWidth, authorizedReconcile, hg]
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

private theorem done_move_entry_cell (hpsi : 0 < psi)
    (a b : Registers psi) :
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

private theorem done_tail_entry_cell (hpsi : 0 < psi)
    (a b : Registers psi) :
    let m := authorizedDoneMove hpsi ⟨cell a,false⟩ ⟨cell b,false⟩
    let p := PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair hpsi
      (preCheckResetWall m.1 m.2)
    preserveDoneCheck hpsi p.1 p.2 =
      (⟨cell a,false⟩,⟨cell b,false⟩) := by
  dsimp only
  rw [done_move_entry_cell hpsi a b]
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

/-- Exact repaired through-CHECK bridge. Authorization bits are unrestricted. -/
theorem through_entry_cell2 (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (a b : Registers psi) (pa pb : Bool)
    (hab : b.label = ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (ha : a.wait = true) (hb : b.wait = true)
    (hc : PreCapEntry2 hpsi h2 kappa (cell a) (cell b)) :
    let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa
      (cell a) (cell b)
    doneThroughCheckEntryWidth hpsi (by decide : 0 < 2) h2 kappa
      ⟨cell a,pa⟩ ⟨cell b,pb⟩ =
      (⟨cell (registers w.1),false⟩,
       ⟨cell (registers w.2),false⟩) := by
  unfold doneThroughCheckEntryWidth doneBeforeCheckEntryWidth
  rw [generation_entry_cell2 hpsi h2 kappa a b pa pb hab ha hb hc]
  exact done_tail_entry_cell hpsi _ _

#print axioms BirthShortDoneTerminalPassiveR2.generation_entry_cell2
#print axioms BirthShortDoneTerminalPassiveR2.through_entry_cell2

end BirthShortDoneTerminalPassiveR2
