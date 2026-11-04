import Leader.Wu.Birth.ControlledWrapAligned

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthB1ScarPrefixCollision

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
  PPLLCompleteMultiLeaderCleanup
open BirthWaitPassive BirthGenerationControlRepair BirthGenerationDone
  BirthArrivalCaptureRepair BirthSingleUseReleaseRepair
  BirthShortWait BirthShortWaitTerminalEntryRepair
  BirthShortDoneTerminalPassiveR1 BirthShortDoneTerminalEntryCut

variable {ψ κ width : Nat}

/-- Everything left by `clearComparisonSignal` except the mutable WAIT/register
coordinates.  In particular this records both collision scars, probe/leader,
`path3`, the writer action, and all K2/final-physical fields. -/
structure ScarView where
  leader : Bool
  probe : Bool
  path3 : Option Path3Info
  resetCmd : Bool
  echo : Bool
  signalB : Fin 2
  bullet : Fin 3
  shield : Bool
  write : WriteAction
  last : Bool
  lastSet : Bool
  lastUnset : Bool
  bCarry : Bool
  genWs : Bool
  wsEcho : Bool
  signalWs : Bool


def scarView (u : AgentState ψ) : ScarView where
  leader := u.leader
  probe := u.probe
  path3 := u.path3
  resetCmd := u.reset_cmd
  echo := u.echo
  signalB := u.signal_B
  bullet := u.bullet
  shield := u.shield
  write := u.write
  last := u.last
  lastSet := u.last_set
  lastUnset := u.last_unset
  bCarry := u.b_carry
  genWs := u.gen_ws
  wsEcho := u.ws_echo
  signalWs := u.signal_ws


def scarFrame (q : AgentState ψ × AgentState ψ) : ScarView × ScarView :=
  (scarView q.1, scarView q.2)


def resetScarCell (a : Registers ψ) : AgentState ψ :=
  { cell a with reset_cmd := true }


def echoScarCell (b : Registers ψ) : AgentState ψ :=
  { cell b with echo := true }


def CollisionScarNormal
    (a b : Registers ψ) (q : AgentState ψ × AgentState ψ) : Prop :=
  scarFrame q = scarFrame (resetScarCell a, echoScarCell b)


def ClearedCollisionScar
    (a b : Registers ψ)
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) : Prop :=
  CollisionScarNormal a b (q.1.core, q.2.core) ∧
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
    q.1.path0Crossed = false ∧ q.2.path0Crossed = false


private theorem authorizedReconcile_scar_frame
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ l r, scarFrame (f l r) = scarFrame (l, r))
    (l r : AuthorizedAgentState ψ) :
    scarFrame ((authorizedReconcile f l r).1.core,
      (authorizedReconcile f l r).2.core) = scarFrame (l.core, r.core) := by
  unfold authorizedReconcile
  dsimp only
  exact hf l.core r.core


private theorem waitPrepare_scar_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    scarFrame (waitSaturatedPrepare hψ l r) = scarFrame (l, r) := by
  unfold scarFrame scarView waitSaturatedPrepare
  dsimp only
  repeat (first | rfl | split)


private theorem waitClear_scar_frame
    (hwidth : 0 < width) (hle : width ≤ ψ) (l r : AgentState ψ) :
    scarFrame (terminalInactiveClear hwidth hle l r) = scarFrame (l, r) := by
  unfold scarFrame scarView terminalInactiveClear
  repeat (first | rfl | split)


private theorem waitCarry_scar_frame
    (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AgentState ψ) :
    scarFrame (waitWidthCarry hwidth hle κ l r) = scarFrame (l, r) := by
  unfold scarFrame scarView waitWidthCarry
  repeat (first | rfl | split)


private theorem waitReset_scar_frame
    (hwidth : 0 < width) (hle : width ≤ ψ) (l r : AgentState ψ) :
    scarFrame (waitWidthReset hwidth hle l r) = scarFrame (l, r) := by
  unfold scarFrame scarView waitWidthReset
  repeat (first | rfl | split)


private theorem waitFinish_scar_frame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AgentState ψ) :
    scarFrame (waitWidthFinish hψ hwidth hle κ l r) = scarFrame (l, r) := by
  unfold scarFrame scarView waitWidthFinish
  dsimp only
  repeat (first | rfl | split)


private theorem waitEntry_scar_frame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AgentState ψ) :
    scarFrame (waitWidthEntry hψ hwidth hle κ l r) = scarFrame (l, r) := by
  let p := waitSaturatedPrepare hψ l r
  let e := terminalInactiveClear hwidth hle p.1 p.2
  let c := waitWidthCarry hwidth hle κ e.1 e.2
  let t := waitWidthReset hwidth hle c.1 c.2
  change scarFrame (waitWidthFinish hψ hwidth hle κ t.1 t.2) = _
  exact (waitFinish_scar_frame hψ hwidth hle κ t.1 t.2).trans
    ((waitReset_scar_frame hwidth hle c.1 c.2).trans
      ((waitCarry_scar_frame hwidth hle κ e.1 e.2).trans
        ((waitClear_scar_frame hwidth hle p.1 p.2).trans
          (waitPrepare_scar_frame hψ l r))))


private theorem genStart_scar_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    scarFrame (genSigSaturatedStart hψ l r) = scarFrame (l, r) := by
  unfold scarFrame scarView genSigSaturatedStart
  dsimp only
  repeat (first | rfl | split)


private theorem genEmit_scar_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    scarFrame (genCleanEmit hψ l r) = scarFrame (l, r) := by
  unfold scarFrame scarView genCleanEmit
  dsimp only
  repeat (first | rfl | split)


private theorem genPropagate_scar_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    scarFrame (genCleanPropagate hψ l r) = scarFrame (l, r) := by
  unfold scarFrame scarView genCleanPropagate
  repeat (first | rfl | split)


private theorem genFinish_scar_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    scarFrame (genSigSaturatedFinish hψ l r) = scarFrame (l, r) := by
  unfold scarFrame scarView genSigSaturatedFinish
  dsimp only
  repeat (first | rfl | split)


private theorem genAfterWait_scar_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    scarFrame (genCleanAfterWait hψ l r) = scarFrame (l, r) := by
  let s := genSigSaturatedStart hψ l r
  let e := genCleanEmit hψ s.1 s.2
  let p := genCleanPropagate hψ e.1 e.2
  change scarFrame (genSigSaturatedFinish hψ p.1 p.2) = _
  exact (genFinish_scar_frame hψ p.1 p.2).trans
    ((genPropagate_scar_frame hψ e.1 e.2).trans
      ((genEmit_scar_frame hψ s.1 s.2).trans
        (genStart_scar_frame hψ l r)))


private theorem genEntryRaw_scar_frame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AgentState ψ) :
    scarFrame (genCleanEntryWidth hψ hwidth hle κ l r) = scarFrame (l, r) := by
  let w := waitWidthEntry hψ hwidth hle κ l r
  change scarFrame (genCleanAfterWait hψ w.1 w.2) = _
  exact (genAfterWait_scar_frame hψ w.1 w.2).trans
    (waitEntry_scar_frame hψ hwidth hle κ l r)


theorem genEntry_scar_frame
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    scarFrame ((authorizedGenCleanEntryWidth hψ hwidth hle κ l r).1.core,
      (authorizedGenCleanEntryWidth hψ hwidth hle κ l r).2.core) =
      scarFrame (l.core, r.core) := by
  unfold authorizedGenCleanEntryWidth
  exact authorizedReconcile_scar_frame _
    (genEntryRaw_scar_frame hψ hwidth hle κ) l r


private theorem cleanConnect_scar_frame (l r : AgentState ψ) :
    scarFrame (cleanSigGenConnect l, cleanSigGenConnect r) =
      scarFrame (l, r) := by
  unfold scarFrame scarView cleanSigGenConnect
  dsimp only
  repeat (first | rfl | split)


private theorem clean3_scar_frame (l r : AgentState ψ) :
    scarFrame (cleanSigStep3 l r) = scarFrame (l, r) := by
  unfold scarFrame scarView cleanSigStep3
  repeat (first | rfl | split)


private theorem clean4_scar_frame (l r : AgentState ψ) :
    scarFrame (cleanSigStep4 l r) = scarFrame (l, r) := by
  unfold scarFrame scarView cleanSigStep4
  repeat (first | rfl | split)


private theorem clean5_scar_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    scarFrame (cleanSigStep5 hψ l r) = scarFrame (l, r) := by
  unfold scarFrame scarView cleanSigStep5
  repeat (first | rfl | split)


private theorem clean6_scar_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    scarFrame (cleanSigStep6 hψ l r) = scarFrame (l, r) := by
  unfold scarFrame scarView cleanSigStep6
  repeat (first | rfl | split)


private theorem cleanApply_left_scar_frame (l r : AgentState ψ) :
    scarFrame (cleanSigCleanApply l, r) = scarFrame (l, r) := by
  unfold scarFrame scarView cleanSigCleanApply
  dsimp only
  repeat (first | rfl | split)


private theorem cleanApply_right_scar_frame (l r : AgentState ψ) :
    scarFrame (l, cleanSigCleanApply r) = scarFrame (l, r) := by
  unfold scarFrame scarView cleanSigCleanApply
  dsimp only
  repeat (first | rfl | split)


private theorem cleanApply_scar_frame (l r : AgentState ψ) :
    scarFrame (cleanSigCleanApply l, cleanSigCleanApply r) =
      scarFrame (l, r) :=
  (cleanApply_left_scar_frame l (cleanSigCleanApply r)).trans
    (cleanApply_right_scar_frame l r)


private theorem cleanRaw_scar_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    scarFrame (cleanSig hψ l r) = scarFrame (l, r) := by
  unfold cleanSig
  dsimp only
  rw [cleanApply_scar_frame, clean6_scar_frame, clean5_scar_frame,
    clean4_scar_frame, clean3_scar_frame, cleanConnect_scar_frame]


theorem clean_scar_frame (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    scarFrame ((authorizedCleanSig hψ l r).1.core,
      (authorizedCleanSig hψ l r).2.core) = scarFrame (l.core, r.core) := by
  unfold authorizedCleanSig
  exact authorizedReconcile_scar_frame _ (cleanRaw_scar_frame hψ) l r


private theorem eliminateRaw_scar_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    scarFrame (eliminateSig hψ l r) = scarFrame (l, r) := by
  unfold eliminateSig scarFrame scarView
  repeat (first | rfl | split)


theorem eliminate_scar_frame (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    scarFrame ((authorizedEliminateSig hψ l r).1.core,
      (authorizedEliminateSig hψ l r).2.core) = scarFrame (l.core, r.core) := by
  unfold authorizedEliminateSig
  exact authorizedReconcile_scar_frame _ (eliminateRaw_scar_frame hψ) l r


private theorem clearLeft_scar_frame (l r : AgentState ψ) :
    scarFrame (clearComparisonSignal l, r) = scarFrame (l, r) := by
  unfold scarFrame scarView clearComparisonSignal
  rfl


private theorem clearRight_scar_frame (l r : AgentState ψ) :
    scarFrame (l, clearComparisonSignal r) = scarFrame (l, r) := by
  unfold scarFrame scarView clearComparisonSignal
  rfl


private theorem clearIfLeader_right_scar_frame (l r : AgentState ψ) :
    scarFrame (l, clearIfLeader r) = scarFrame (l, r) := by
  unfold clearIfLeader
  split
  · exact clearRight_scar_frame l r
  · rfl


private theorem preclear_scar_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    scarFrame (sigMoveLeaderPreclear hψ l r) = scarFrame (l, r) := by
  unfold sigMoveLeaderPreclear
  dsimp only
  split
  · exact (clearLeft_scar_frame l (clearIfLeader r)).trans
      (clearIfLeader_right_scar_frame l r)
  · exact clearIfLeader_right_scar_frame l r


private theorem capture_scar_frame (l r : AgentState ψ) :
    scarFrame (captureStep1 l r) = scarFrame (l, r) := by
  unfold scarFrame scarView captureStep1
  dsimp only
  repeat (first | rfl | split)


private theorem step2_scar_frame (l r : AgentState ψ) :
    scarFrame (sigMoveStep2 l r) = scarFrame (l, r) := by
  unfold scarFrame scarView sigMoveStep2
  repeat (first | rfl | split)


private theorem step3_scar_frame (l r : AgentState ψ) :
    scarFrame (sigMoveStep3 l r) = scarFrame (l, r) := by
  unfold scarFrame scarView sigMoveStep3
  repeat (first | rfl | split)


private theorem step4_scar_frame (l r : AgentState ψ) :
    scarFrame (sigMoveStep4 l r) = scarFrame (l, r) := by
  unfold scarFrame scarView sigMoveStep4
  repeat (first | rfl | split)


private theorem step5_scar_frame (l r : AgentState ψ) :
    scarFrame (sigMoveStep5 l r) = scarFrame (l, r) := by
  unfold scarFrame scarView sigMoveStep5
  repeat (first | rfl | split)


private theorem holdDone_scar_frame (l r : AgentState ψ) :
    scarFrame (holdDoneStep1 l r) = scarFrame (l, r) := by
  unfold holdDoneStep1
  split
  · rfl
  · exact capture_scar_frame l r


private theorem controlTransfers_scar_frame (l r : AgentState ψ) :
    scarFrame (controlTransfers l r) = scarFrame (l, r) := by
  unfold controlTransfers
  dsimp only
  rw [step5_scar_frame, step4_scar_frame, step3_scar_frame,
    step2_scar_frame]


private theorem doneTransfers_scar_frame (l r : AgentState ψ) :
    scarFrame (doneTransfers l r) = scarFrame (l, r) := by
  unfold doneTransfers
  dsimp only
  rw [controlTransfers_scar_frame, holdDone_scar_frame]


private theorem leaderWall_scar_frame (l r : AgentState ψ) :
    scarFrame (comparisonLeaderWall l r) = scarFrame (l, r) := by
  unfold comparisonLeaderWall
  dsimp only
  split
  · split
    · exact (clearLeft_scar_frame l (clearComparisonSignal r)).trans
        (clearRight_scar_frame l r)
    · exact clearLeft_scar_frame l r
  · split
    · exact clearRight_scar_frame l r
    · rfl


private theorem applyControl_scar_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    scarFrame
        (singleUseApplyControl hψ l, singleUseApplyControl hψ r) =
      scarFrame (l, r) := by
  unfold scarFrame scarView singleUseApplyControl
  dsimp only
  repeat (first | rfl | split)


private theorem controlTail_scar_frame
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    scarFrame (singleUseControlTail hψ l r) = scarFrame (l, r) := by
  unfold singleUseControlTail
  dsimp only
  split
  · split
    · simpa [scarFrame, scarView] using applyControl_scar_frame hψ l r
    · exact applyControl_scar_frame hψ l r
  · exact applyControl_scar_frame hψ l r


private theorem doneRaw_scar_frame (hψ : 0 < ψ) (l r : AgentState ψ) :
    scarFrame (doneCaptureSigMove hψ l r) = scarFrame (l, r) := by
  unfold doneCaptureSigMove
  dsimp only
  rw [controlTail_scar_frame, leaderWall_scar_frame,
    doneTransfers_scar_frame, preclear_scar_frame]


theorem doneMove_scar_frame (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) :
    scarFrame ((authorizedDoneMove hψ l r).1.core,
      (authorizedDoneMove hψ l r).2.core) = scarFrame (l.core, r.core) := by
  exact (congrArg scarFrame (authorizedDoneMove_core hψ l r)).trans
    (doneRaw_scar_frame hψ l.core r.core)


private theorem pprimeRaw_collision_eq
    (hψ : 0 < ψ) (a b : Registers ψ)
    (hab : b.label = ⟨(a.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) :
    pPsiLeaderResetProbeWall hψ (resetScarCell a) (echoScarCell b) =
      (resetScarCell a, echoScarCell b) := by
  simp [pPsiLeaderResetProbeWall, pPsi, resetScarCell, echoScarCell,
    cell, hab]


theorem pprime_collision_normal
    (hψ : 0 < ψ) (a b : Registers ψ) (pa pb : Bool)
    (hab : b.label = ⟨(a.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) :
    CollisionScarNormal a b
      ((authorizedPPsiLeaderResetProbeWall hψ
          ⟨resetScarCell a, pa⟩ ⟨echoScarCell b, pb⟩).1.core,
       (authorizedPPsiLeaderResetProbeWall hψ
          ⟨resetScarCell a, pa⟩ ⟨echoScarCell b, pb⟩).2.core) := by
  unfold CollisionScarNormal
  calc
    scarFrame
        ((authorizedPPsiLeaderResetProbeWall hψ
            ⟨resetScarCell a, pa⟩ ⟨echoScarCell b, pb⟩).1.core,
         (authorizedPPsiLeaderResetProbeWall hψ
            ⟨resetScarCell a, pa⟩ ⟨echoScarCell b, pb⟩).2.core) =
      scarFrame (pPsiLeaderResetProbeWall hψ
        (resetScarCell a) (echoScarCell b)) :=
      congrArg scarFrame
        (authorizedPPsiLeaderResetProbeWall_core hψ
          ⟨resetScarCell a, pa⟩ ⟨echoScarCell b, pb⟩)
    _ = scarFrame (resetScarCell a, echoScarCell b) := by
      rw [pprimeRaw_collision_eq hψ a b hab]


theorem genEntry_preserves_collision
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (κ : Nat)
    (a b : Registers ψ) (l r : AuthorizedAgentState ψ)
    (h : CollisionScarNormal a b (l.core, r.core)) :
    CollisionScarNormal a b
      ((authorizedGenCleanEntryWidth hψ hwidth hle κ l r).1.core,
       (authorizedGenCleanEntryWidth hψ hwidth hle κ l r).2.core) := by
  unfold CollisionScarNormal at h ⊢
  exact (genEntry_scar_frame hψ hwidth hle κ l r).trans h


theorem clean_preserves_collision
    (hψ : 0 < ψ) (a b : Registers ψ) (l r : AuthorizedAgentState ψ)
    (h : CollisionScarNormal a b (l.core, r.core)) :
    CollisionScarNormal a b
      ((authorizedCleanSig hψ l r).1.core,
       (authorizedCleanSig hψ l r).2.core) := by
  unfold CollisionScarNormal at h ⊢
  exact (clean_scar_frame hψ l r).trans h


theorem eliminate_preserves_collision
    (hψ : 0 < ψ) (a b : Registers ψ) (l r : AuthorizedAgentState ψ)
    (h : CollisionScarNormal a b (l.core, r.core)) :
    CollisionScarNormal a b
      ((authorizedEliminateSig hψ l r).1.core,
       (authorizedEliminateSig hψ l r).2.core) := by
  unfold CollisionScarNormal at h ⊢
  exact (eliminate_scar_frame hψ l r).trans h


theorem doneMove_preserves_collision
    (hψ : 0 < ψ) (a b : Registers ψ) (l r : AuthorizedAgentState ψ)
    (h : CollisionScarNormal a b (l.core, r.core)) :
    CollisionScarNormal a b
      ((authorizedDoneMove hψ l r).1.core,
       (authorizedDoneMove hψ l r).2.core) := by
  unfold CollisionScarNormal at h ⊢
  exact (doneMove_scar_frame hψ l r).trans h


private theorem preCheckResetWall_scar_frame
    (l r : AuthorizedAgentState ψ) :
    scarFrame ((preCheckResetWall l r).1.core,
      (preCheckResetWall l r).2.core) = scarFrame (l.core, r.core) := by
  unfold preCheckResetWall clearAuthorizedComparison clearComparisonSignal
    scarFrame scarView
  dsimp only
  repeat (first | rfl | split)


/-- The collision wall is the decisive cut: the left reset scar makes
`sendRight` true, so both comparison carriers and both permits are cleared;
`scarFrame` proves that reset/echo and every other scar-side field survive. -/
theorem preCheckResetWall_clears_collision
    (a b : Registers ψ) (l r : AuthorizedAgentState ψ)
    (h : CollisionScarNormal a b (l.core, r.core)) :
    ClearedCollisionScar a b (preCheckResetWall l r) := by
  have hframe : scarFrame (l.core, r.core) =
      scarFrame (resetScarCell a, echoScarCell b) := h
  have hreset : l.core.reset_cmd = true := by
    have hx := congrArg (fun z : ScarView × ScarView => z.1.resetCmd) hframe
    simpa [scarFrame, scarView, resetScarCell, cell] using hx
  have hn := preCheckResetWall_both_neutral_of_send
    l r (Or.inr hreset)
  have hs : CollisionScarNormal a b
      ((preCheckResetWall l r).1.core,
       (preCheckResetWall l r).2.core) := by
    unfold CollisionScarNormal
    exact (preCheckResetWall_scar_frame l r).trans hframe
  exact ⟨hs, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2⟩


/-- Exact remainder after this micro-round: from the scarred literal pair,
through the shortened width-two CHECK cut, DISAPPEAR, and action-one COMPARE,
the pair is still the same scar normal form and comparison-neutral. -/
def CollisionPreSuppressCutStatement : Prop :=
  ∀ (ψ κ : Nat) (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
      (a b : Registers ψ) (pa pb : Bool),
    b.label = ⟨(a.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ →
    PreCapEntry2 hψ h2 κ (resetScarCell a) (echoScarCell b) →
    let q := doneThroughCheckEntryWidth
      hψ (by decide : 0 < 2) h2 κ
      ⟨resetScarCell a, pa⟩ ⟨echoScarCell b, pb⟩
    let q := authorizedDisappear hψ q.1 q.2
    let q := authorizedCompareSigActionOne hψ q.1 q.2
    ClearedCollisionScar a b q


#print axioms genEntry_scar_frame
#print axioms clean_scar_frame
#print axioms eliminate_scar_frame
#print axioms doneMove_scar_frame
#print axioms pprime_collision_normal
#print axioms genEntry_preserves_collision
#print axioms clean_preserves_collision
#print axioms eliminate_preserves_collision
#print axioms doneMove_preserves_collision
#print axioms preCheckResetWall_clears_collision

end BirthB1ScarPrefixCollision
