import Leader.Wu.Birth.InnerFieldFrames
import Leader.Wu.Birth.CountStepReduction

set_option autoImplicit false

namespace BirthB1InnerCountMono

open PPLLWallSweepFinite PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  BirthCheckCongestGuardRepair PPLLCompleteMultiLeaderCleanup BirthShortDoneCuts
  BirthArrivalCaptureRepair BirthGenerationControlRepair BirthGenerationDone BirthShortWait
  BirthShortWaitTerminalEntryRepair BirthSingleUseReleaseRepair BirthStationaryWrite
  BirthTossCheckPreservationRepair PPLL PPLLLeaderCreationCleanupRepair PPLLRepair
  PPLLTerminalEqualSupportRepair PPLLWallSweepPreCheckResetRepair PPLLWallSweepRepair
  PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair
  BirthShortDoneTerminalHost BirthShortDoneTerminalEntryCut
open BirthB1InnerCountFrames BirthB1InnerFieldFrames

variable {ψ psi κ kappa width : Nat}

/-! ## The increment stage: saturating carry never decreases a count `<= kappa`. -/

theorem satCountSucc_ge (kappa c : Nat) (hc : c <= kappa) : c <= satCountSucc kappa c := by
  unfold satCountSucc
  omega

theorem waitWidthCarry_count_le (hwidth : 0 < width) (hle : width <= psi) (kappa : Nat)
    (l r : AgentState psi) (hr : r.count <= kappa) :
    l.count <= (waitWidthCarry hwidth hle kappa l r).1.count ∧
      r.count <= (waitWidthCarry hwidth hle kappa l r).2.count := by
  unfold waitWidthCarry
  repeat' split
  all_goals first
    | exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    | exact ⟨Nat.le_refl _, satCountSucc_ge kappa r.count hr⟩

theorem waitWidthEntry_count_le (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AgentState psi) (hr : r.count <= kappa) :
    l.count <= (waitWidthEntry hpsi hwidth hle kappa l r).1.count ∧
      r.count <= (waitWidthEntry hpsi hwidth hle kappa l r).2.count := by
  unfold waitWidthEntry
  simp only []
  have h0 := waitSaturatedPrepare_count hpsi l r
  have h1 := terminalInactiveClear_count hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2
  have ha1 : (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).1.count = l.count := by rw [h1.1, h0.1]
  have ha2 : (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).2.count = r.count := by rw [h1.2, h0.2]
  have h2 := waitWidthCarry_count_le hwidth hle kappa (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).1 (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).2 (by rw [ha2]; exact hr)
  have h3 := waitWidthReset_count hwidth hle (waitWidthCarry hwidth hle kappa (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).1 (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).2).1 (waitWidthCarry hwidth hle kappa (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).1 (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).2).2
  have h4 := waitWidthFinish_count hpsi hwidth hle kappa (waitWidthReset hwidth hle (waitWidthCarry hwidth hle kappa (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).1 (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).2).1 (waitWidthCarry hwidth hle kappa (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).1 (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).2).2).1 (waitWidthReset hwidth hle (waitWidthCarry hwidth hle kappa (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).1 (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).2).1 (waitWidthCarry hwidth hle kappa (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).1 (terminalInactiveClear hwidth hle (waitSaturatedPrepare hpsi l r).1 (waitSaturatedPrepare hpsi l r).2).2).2).2
  rw [h4.1, h4.2, h3.1, h3.2]
  rw [ha1, ha2] at h2
  exact h2

/-! ## Field frames for the carry chain (it writes count/carry/h_field only). -/

theorem waitWidthCarry_reset_cmd (hwidth : 0 < width) (hle : width <= psi) (kappa : Nat)
    (l r : AgentState psi) :
    (waitWidthCarry hwidth hle kappa l r).1.reset_cmd = l.reset_cmd ∧
      (waitWidthCarry hwidth hle kappa l r).2.reset_cmd = r.reset_cmd := by
  unfold waitWidthCarry
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem waitWidthCarry_leader (hwidth : 0 < width) (hle : width <= psi) (kappa : Nat)
    (l r : AgentState psi) :
    (waitWidthCarry hwidth hle kappa l r).1.leader = l.leader ∧
      (waitWidthCarry hwidth hle kappa l r).2.leader = r.leader := by
  unfold waitWidthCarry
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem waitWidthEntry_reset_cmd (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AgentState psi) :
    (waitWidthEntry hpsi hwidth hle kappa l r).1.reset_cmd = l.reset_cmd ∧
      (waitWidthEntry hpsi hwidth hle kappa l r).2.reset_cmd = r.reset_cmd := by
  unfold waitWidthEntry
  dsimp only
  rw [(waitWidthFinish_reset_cmd _ _ _ _ _ _).1, (waitWidthFinish_reset_cmd _ _ _ _ _ _).2,
    (waitWidthReset_reset_cmd _ _ _ _).1, (waitWidthReset_reset_cmd _ _ _ _).2,
    (waitWidthCarry_reset_cmd _ _ _ _ _).1, (waitWidthCarry_reset_cmd _ _ _ _ _).2,
    (terminalInactiveClear_reset_cmd _ _ _ _).1, (terminalInactiveClear_reset_cmd _ _ _ _).2,
    (waitSaturatedPrepare_reset_cmd _ _ _).1, (waitSaturatedPrepare_reset_cmd _ _ _).2]
  exact ⟨rfl, rfl⟩

theorem waitWidthEntry_leader (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AgentState psi) :
    (waitWidthEntry hpsi hwidth hle kappa l r).1.leader = l.leader ∧
      (waitWidthEntry hpsi hwidth hle kappa l r).2.leader = r.leader := by
  unfold waitWidthEntry
  dsimp only
  rw [(waitWidthFinish_leader _ _ _ _ _ _).1, (waitWidthFinish_leader _ _ _ _ _ _).2,
    (waitWidthReset_leader _ _ _ _).1, (waitWidthReset_leader _ _ _ _).2,
    (waitWidthCarry_leader _ _ _ _ _).1, (waitWidthCarry_leader _ _ _ _ _).2,
    (terminalInactiveClear_leader _ _ _ _).1, (terminalInactiveClear_leader _ _ _ _).2,
    (waitSaturatedPrepare_leader _ _ _).1, (waitSaturatedPrepare_leader _ _ _).2]
  exact ⟨rfl, rfl⟩

/-! ## The generation/WAIT entry: count nondecreasing, reset_cmd and leader framed. -/

theorem genCleanEntryWidth_count_le (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (κ : Nat) (l r : AgentState ψ) (hr : r.count <= κ) :
    l.count <= (genCleanEntryWidth hψ hwidth hle κ l r).1.count ∧
      r.count <= (genCleanEntryWidth hψ hwidth hle κ l r).2.count := by
  unfold genCleanEntryWidth
  dsimp only
  have hw := waitWidthEntry_count_le hψ hwidth hle κ l r hr
  have hg := genCleanAfterWait_count hψ (waitWidthEntry hψ hwidth hle κ l r).1 (waitWidthEntry hψ hwidth hle κ l r).2
  rw [hg.1, hg.2]
  exact hw

theorem genCleanEntryWidth_reset_cmd (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (κ : Nat) (l r : AgentState ψ) :
    (genCleanEntryWidth hψ hwidth hle κ l r).1.reset_cmd = l.reset_cmd ∧
      (genCleanEntryWidth hψ hwidth hle κ l r).2.reset_cmd = r.reset_cmd := by
  unfold genCleanEntryWidth
  dsimp only
  have hg := genCleanAfterWait_reset_cmd hψ (waitWidthEntry hψ hwidth hle κ l r).1 (waitWidthEntry hψ hwidth hle κ l r).2
  rw [hg.1, hg.2]
  exact waitWidthEntry_reset_cmd hψ hwidth hle κ l r

theorem genCleanEntryWidth_leader (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (κ : Nat) (l r : AgentState ψ) :
    (genCleanEntryWidth hψ hwidth hle κ l r).1.leader = l.leader ∧
      (genCleanEntryWidth hψ hwidth hle κ l r).2.leader = r.leader := by
  unfold genCleanEntryWidth
  dsimp only
  have hg := genCleanAfterWait_leader hψ (waitWidthEntry hψ hwidth hle κ l r).1 (waitWidthEntry hψ hwidth hle κ l r).2
  rw [hg.1, hg.2]
  exact waitWidthEntry_leader hψ hwidth hle κ l r

theorem authorizedGenCleanEntryWidth_count_le (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ) (hr : r.core.count <= κ) :
    l.core.count <= (authorizedGenCleanEntryWidth hψ hwidth hle κ l r).1.core.count ∧
      r.core.count <= (authorizedGenCleanEntryWidth hψ hwidth hle κ l r).2.core.count := by
  unfold authorizedGenCleanEntryWidth
  rw [(BirthB1InnerCountFrames.authorizedReconcile_core (genCleanEntryWidth hψ hwidth hle κ) l r).1, (BirthB1InnerCountFrames.authorizedReconcile_core (genCleanEntryWidth hψ hwidth hle κ) l r).2]
  exact genCleanEntryWidth_count_le hψ hwidth hle κ l.core r.core hr

theorem authorizedGenCleanEntryWidth_reset_cmd (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ) :
    (authorizedGenCleanEntryWidth hψ hwidth hle κ l r).1.core.reset_cmd = l.core.reset_cmd ∧
      (authorizedGenCleanEntryWidth hψ hwidth hle κ l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold authorizedGenCleanEntryWidth
  rw [(BirthB1InnerCountFrames.authorizedReconcile_core (genCleanEntryWidth hψ hwidth hle κ) l r).1, (BirthB1InnerCountFrames.authorizedReconcile_core (genCleanEntryWidth hψ hwidth hle κ) l r).2]
  exact genCleanEntryWidth_reset_cmd hψ hwidth hle κ l.core r.core

/-! ## Compare-signal action one (the one authorized stage without a generated frame). -/

theorem authorizedCompareSigActionOne_count (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedCompareSigActionOne hpsi l r).1.core.count = l.core.count ∧
      (authorizedCompareSigActionOne hpsi l r).2.core.count = r.core.count := by
  unfold authorizedCompareSigActionOne
  dsimp only
  repeat' split
  all_goals simp_all [compareSigInit_count, authorizedCmpUpdate_count, compareSigDispatchActionOne_count]

theorem authorizedCompareSigActionOne_reset_cmd (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedCompareSigActionOne hpsi l r).1.core.reset_cmd = l.core.reset_cmd ∧
      (authorizedCompareSigActionOne hpsi l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold authorizedCompareSigActionOne
  dsimp only
  repeat' split
  all_goals simp_all [compareSigInit_reset_cmd, authorizedCmpUpdate_reset_cmd, compareSigDispatchActionOne_reset_cmd]

theorem authorizedCompareSigActionOne_leader (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedCompareSigActionOne hpsi l r).1.core.leader = l.core.leader ∧
      (authorizedCompareSigActionOne hpsi l r).2.core.leader = r.core.leader := by
  unfold authorizedCompareSigActionOne
  dsimp only
  repeat' split
  all_goals simp_all [compareSigInit_leader, authorizedCmpUpdate_leader, compareSigDispatchActionOne_leader]

/-! ## The SUPPRESS stage under leaderless / reset-free inputs. -/

theorem authorizedSuppressWidth_count_of_reset_free (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (l r : AuthorizedAgentState ψ) (hleader : l.core.leader = false)
    (hl : l.core.reset_cmd = false) (hr : r.core.reset_cmd = false) :
    (authorizedSuppressWidth hψ hwidth hle l r).1.core.count = l.core.count ∧
      (authorizedSuppressWidth hψ hwidth hle l r).2.core.count = r.core.count := by
  unfold authorizedSuppressWidth
  rw [(BirthB1InnerCountFrames.authorizedReconcile_core (suppressSigResetKillWidth hψ hwidth hle) l r).1, (BirthB1InnerCountFrames.authorizedReconcile_core (suppressSigResetKillWidth hψ hwidth hle) l r).2]
  exact BirthB1ResetFreeControlled.suppressSigResetKillWidth_count_frame_of_reset_free hψ hwidth hle l.core r.core hleader hl hr


/-! ## Through CHECK: count nondecreasing, reset_cmd framed. -/

theorem doneThroughCheckEntryWidth_count_le (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ) (hr : r.core.count <= κ) :
    l.core.count <= (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1.core.count ∧
      r.core.count <= (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2.core.count := by
  unfold doneThroughCheckEntryWidth doneBeforeCheckEntryWidth generationBeforeMoveEntryWidth
  dsimp only
  have h0 := authorizedPPsiLeaderResetProbeWall_count hψ l r
  have h1 := authorizedGenCleanEntryWidth_count_le hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2 (by rw [h0.2]; exact hr)
  have h2 := authorizedCleanSig_count hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2
  have h3 := authorizedEliminateSig_count hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2
  have h4 := authorizedDoneMove_count hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2
  have h5 := preCheckResetWall_count (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).1 (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).2
  have h6 := sanitizeAuthorizedPair_count hψ (preCheckResetWall (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).1 (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).2)
  have h7 := preserveDoneCheck_count hψ (sanitizeAuthorizedPair hψ (preCheckResetWall (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).1 (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).2)).1 (sanitizeAuthorizedPair hψ (preCheckResetWall (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).1 (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).2)).2
  rw [h7.1, h7.2, h6.1, h6.2, h5.1, h5.2, h4.1, h4.2, h3.1, h3.2, h2.1, h2.2]
  rw [h0.1, h0.2] at h1
  exact h1

theorem doneThroughCheckEntryWidth_reset_cmd (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ) :
    (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1.core.reset_cmd = l.core.reset_cmd ∧
      (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2.core.reset_cmd = r.core.reset_cmd := by
  unfold doneThroughCheckEntryWidth doneBeforeCheckEntryWidth generationBeforeMoveEntryWidth
  dsimp only
  have h0 := authorizedPPsiLeaderResetProbeWall_reset_cmd hψ l r
  have h1 := authorizedGenCleanEntryWidth_reset_cmd hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2
  have h2 := authorizedCleanSig_reset_cmd hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2
  have h3 := authorizedEliminateSig_reset_cmd hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2
  have h4 := authorizedDoneMove_reset_cmd hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2
  have h5 := preCheckResetWall_reset_cmd (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).1 (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).2
  have h6 := sanitizeAuthorizedPair_reset_cmd hψ (preCheckResetWall (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).1 (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).2)
  have h7 := preserveDoneCheck_reset_cmd hψ (sanitizeAuthorizedPair hψ (preCheckResetWall (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).1 (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).2)).1 (sanitizeAuthorizedPair hψ (preCheckResetWall (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).1 (authorizedDoneMove hψ (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).1 (authorizedEliminateSig hψ (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1 (authorizedCleanSig hψ (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).1 (authorizedGenCleanEntryWidth hψ hwidth hle κ (authorizedPPsiLeaderResetProbeWall hψ l r).1 (authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2).2).2)).2
  rw [h7.1, h7.2, h6.1, h6.2, h5.1, h5.2, h4.1, h4.2, h3.1, h3.2, h2.1, h2.2, h1.1, h1.2, h0.1, h0.2]
  exact ⟨rfl, rfl⟩

/-! ## After CHECK: with reset-free inputs and no leader at the output, counts are framed. -/

theorem afterCheckMetadataWidth_count_of (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (l r : AuthorizedAgentState ψ)
    (hl : l.core.reset_cmd = false) (hr : r.core.reset_cmd = false)
    (hlead : (afterCheckMetadataWidth hψ hwidth hle l r).1.core.leader = false) :
    (afterCheckMetadataWidth hψ hwidth hle l r).1.core.count = l.core.count ∧
      (afterCheckMetadataWidth hψ hwidth hle l r).2.core.count = r.core.count := by
  unfold afterCheckMetadataWidth beforeWriteWidth at hlead ⊢
  dsimp only at hlead ⊢
  have d0 := authorizedDisappear_count hψ l r
  have d0r := authorizedDisappear_reset_cmd hψ l r
  have c1 := authorizedCompareSigActionOne_count hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2
  have c1r := authorizedCompareSigActionOne_reset_cmd hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2
  have hlead1 : (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1.core.leader = false := by
    rw [(stationaryPersistentAuthorizedRow_leader hψ (authorizedSuppressWidth hψ hwidth hle (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1 (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).2).1 (authorizedSuppressWidth hψ hwidth hle (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1 (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).2).2).1,
      (authorizedSuppressWidth_leader hψ hwidth hle (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1 (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).2).1] at hlead
    exact hlead
  have hr1 : (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1.core.reset_cmd = false := by rw [c1r.1, d0r.1]; exact hl
  have hr2 : (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).2.core.reset_cmd = false := by rw [c1r.2, d0r.2]; exact hr
  have s2 := authorizedSuppressWidth_count_of_reset_free hψ hwidth hle (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1 (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).2 hlead1 hr1 hr2
  have s3 := stationaryPersistentAuthorizedRow_count hψ (authorizedSuppressWidth hψ hwidth hle (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1 (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).2).1 (authorizedSuppressWidth hψ hwidth hle (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).1 (authorizedCompareSigActionOne hψ (authorizedDisappear hψ l r).1 (authorizedDisappear hψ l r).2).2).2
  rw [s3.1, s3.2, s2.1, s2.2, c1.1, c1.2, d0.1, d0.2]
  exact ⟨rfl, rfl⟩

/-! ## The ordinary metadata row and the full authorized entry. -/

theorem doneOrdinaryMetadataEntryWidth_count_le (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ) (hrc : r.core.count <= κ)
    (hl : l.core.reset_cmd = false) (hr : r.core.reset_cmd = false)
    (hlead : (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r).1.core.leader = false) :
    l.core.count <= (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r).1.core.count ∧
      r.core.count <= (doneOrdinaryMetadataEntryWidth hψ hwidth hle κ l r).2.core.count := by
  unfold doneOrdinaryMetadataEntryWidth at hlead ⊢
  dsimp only at hlead ⊢
  have hm := markLeaderBirth_count (K2BirthDispatcher.authBirth l r (afterCheckMetadataWidth hψ hwidth hle (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1 (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2)) (afterCheckMetadataWidth hψ hwidth hle (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1 (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2)
  have hml := markLeaderBirth_leader (K2BirthDispatcher.authBirth l r (afterCheckMetadataWidth hψ hwidth hle (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1 (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2)) (afterCheckMetadataWidth hψ hwidth hle (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1 (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2)
  rw [hml.1] at hlead
  have hcr := doneThroughCheckEntryWidth_reset_cmd hψ hwidth hle κ l r
  have ha := afterCheckMetadataWidth_count_of hψ hwidth hle (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1 (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2
    (by rw [hcr.1]; exact hl) (by rw [hcr.2]; exact hr) hlead
  have hc := doneThroughCheckEntryWidth_count_le hψ hwidth hle κ l r hrc
  rw [hm.1, hm.2, ha.1, ha.2]
  exact hc

theorem doneMetadataAuthorizedEntryWidth_count_le (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width <= ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ) (hrc : r.core.count <= κ)
    (hl : l.core.reset_cmd = false) (hr : r.core.reset_cmd = false)
    (hlead : (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l r).1.core.leader = false) :
    l.core.count <= (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l r).1.core.count ∧
      r.core.count <= (doneMetadataAuthorizedEntryWidth hψ hwidth hle κ l r).2.core.count := by
  unfold doneMetadataAuthorizedEntryWidth at hlead ⊢
  dsimp only at hlead ⊢
  have nl := normalizeDeletion_count l
  have nr := normalizeDeletion_count r
  have nlr := normalizeDeletion_reset_cmd l
  have nrr := normalizeDeletion_reset_cmd r
  by_cases hA : deletionActive (normalizeDeletion r) = true
  · rw [if_pos hA] at hlead ⊢
    have he := authorizedEliminateSig_count hψ (normalizeDeletion l) (normalizeDeletion r)
    rw [he.1, he.2, nl, nr]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · rw [if_neg hA] at hlead ⊢
    by_cases hB : deletionActive (normalizeDeletion l) = true
    · rw [if_pos hB] at hlead ⊢
      rw [nl, nr]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · rw [if_neg hB] at hlead ⊢
      have ho := doneOrdinaryMetadataEntryWidth_count_le hψ hwidth hle κ (normalizeDeletion l) (normalizeDeletion r)
        (by rw [nr]; exact hrc) (by rw [nlr]; exact hl) (by rw [nrr]; exact hr) hlead
      rw [nl, nr] at ho
      exact ho

/-- The inner one-letter obligation of B7's hcount, discharged. -/
theorem innerCountMono (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat) :
    BirthB1CountStepReduction.InnerCountMono hpsi h2 kappa :=
  ⟨fun l r hlc hrc hl hr hout1 _ =>
    doneMetadataAuthorizedEntryWidth_count_le hpsi (by decide : 0 < 2) h2 kappa l r hrc hl hr hout1⟩

/-- B7's count step, fully discharged: leaderless, reset-free, and no birth in this letter. -/
theorem count_step_noBirth {n tau : Nat} (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau) (e : Fin n)
    (hL : BirthB1LeaderlessResetFree.Leaderless C)
    (hR : BirthB1LeaderlessResetFree.ResetFree C)
    (hNB : BirthB1CountStepReduction.NoInnerBirth hpsi h2 ring C e) :
    BirthB1ResetFreeCountMono.CountMonoStep C
      (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) :=
  BirthB1CountStepReduction.count_step_of_inner hpsi h2 ring (innerCountMono hpsi h2 kappa) C e hL hR hNB

end BirthB1InnerCountMono
