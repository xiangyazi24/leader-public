import Leader.Wu.Birth.ShortWaitDomainWitness
import Leader.Wu.Elimination.BirthDispatcherDone

/-!
# Short-clock cuts in the actual DONE stationary-WRITE metadata host

Only two calls change: GEN uses `genCleanWidth`, and post-CHECK SUPPRESS uses
`suppressSigResetKillWidth`.  The full-psi P'psi/ruler and GEN writers, DONE
movement/CHECK, stationary persistent WRITE, disposal priority, bounded carrier
and one expiry call per endpoint retain their existing implementations.
-/

namespace BirthShortDoneCuts

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepNormalResetContract PPLLWallSweepPreCheckResetRepair
  PPLLNoCheckBirthConditionTwoFrames PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol PPLLNoCheckBirthLeaderFrames
  BirthGenerationControlRepair BirthGenerationDone BirthShortWait
  BirthShortWaitDomainWitness BirthStationaryWrite K2OutputSafety
  PPLLTerminalEqualSupportRepair BirthSigMoveDisposalRepair

open K2BirthDispatcher K2BirthDispatcherDone ExpiringK2Projection

set_option autoImplicit false
set_option pp.structureInstances false

variable {ψ width κ τ : Nat}

/-! ## Cut 1: shortened WAIT inside the otherwise full-psi GEN prefix -/

private theorem waitPrepare_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (waitSaturatedPrepare hψ l r) = signalPair (l, r) := by
  unfold waitSaturatedPrepare
  repeat (first | rfl | split)

private theorem waitCarryWidth_signal (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AgentState ψ) :
    signalPair (waitWidthCarry hwidth hle κ l r) = signalPair (l, r) := by
  unfold waitWidthCarry
  repeat (first | rfl | split)

private theorem waitResetWidth_signal (hwidth : 0 < width)
    (hle : width <= ψ) (l r : AgentState ψ) :
    signalPair (waitWidthReset hwidth hle l r) = signalPair (l, r) := by
  unfold waitWidthReset
  repeat (first | rfl | split)

private theorem waitFinishWidth_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AgentState ψ) :
    signalPair (waitWidthFinish hψ hwidth hle κ l r) = signalPair (l, r) := by
  unfold waitWidthFinish
  split <;> dsimp only <;> split <;> rfl

private theorem waitWidth_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AgentState ψ) :
    signalPair (waitWidth hψ hwidth hle κ l r) = signalPair (l, r) := by
  unfold waitWidth
  dsimp only
  rw [waitFinishWidth_signal, waitResetWidth_signal,
    waitCarryWidth_signal, waitPrepare_signal]

private theorem genStart_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (genSigSaturatedStart hψ l r) = signalPair (l, r) := by
  unfold genSigSaturatedStart
  split <;> dsimp only <;> split <;> rfl

private theorem genEmit_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (genCleanEmit hψ l r) = signalPair (l, r) := by
  unfold genCleanEmit
  repeat (first | rfl | split)

private theorem genPropagate_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (genCleanPropagate hψ l r) = signalPair (l, r) := by
  unfold genCleanPropagate
  repeat (first | rfl | split)

private theorem genFinish_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (genSigSaturatedFinish hψ l r) = signalPair (l, r) := by
  unfold genSigSaturatedFinish
  repeat (first | rfl | split)

private theorem genAfterWait_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (genCleanAfterWait hψ l r) = signalPair (l, r) := by
  unfold genCleanAfterWait
  dsimp only
  rw [genFinish_signal, genPropagate_signal, genEmit_signal, genStart_signal]

/-- Source-derived four-field frame for the changed GEN row. -/
theorem genCleanWidth_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AgentState ψ) :
    signalPair (genCleanWidth hψ hwidth hle κ l r) = signalPair (l, r) := by
  unfold genCleanWidth
  dsimp only
  rw [genAfterWait_signal, waitWidth_signal]

/-- Actual authorization adapter at the old `authorizedGenClean` cut. -/
def authorizedGenCleanWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  authorizedReconcile (genCleanWidth hψ hwidth hle κ) l r

theorem authorizedGenCleanWidth_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authSignalPair (authorizedGenCleanWidth hψ hwidth hle κ l r) =
      authSignalPair (l, r) := by
  change signalPair (genCleanWidth hψ hwidth hle κ l.core r.core) =
    signalPair (l.core, r.core)
  exact genCleanWidth_signal hψ hwidth hle κ l.core r.core

theorem authorizedGenCleanWidth_domain (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (authorizedGenCleanWidth hψ hwidth hle κ l r).1.core.inProtocolDomain κ ∧
      (authorizedGenCleanWidth hψ hwidth hle κ l r).2.core.inProtocolDomain κ := by
  exact authorizedReconcile_inProtocolDomain (genCleanWidth hψ hwidth hle κ) l r
    (genCleanWidth_inProtocolDomain hψ hwidth hle l.core r.core hl hr)

theorem authorizedGenCleanWidth_full (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authorizedGenCleanWidth hψ hψ (Nat.le_refl ψ) κ l r =
      authorizedGenClean hψ κ l r := by
  unfold authorizedGenCleanWidth authorizedGenClean
  have hfun :
      genCleanWidth (psi := ψ) (width := ψ)
          hψ hψ (Nat.le_refl ψ) κ =
        genClean hψ κ := by
    funext a b
    exact genCleanWidth_full hψ κ a b
  exact congrArg (fun f => authorizedReconcile f l r) hfun

/-- Full-psi probe/ruler, short WAIT inside GEN, then the unchanged CLEAN and
ELIMINATE stages. -/
def generationBeforeMoveWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q0 := authorizedPPsiLeaderResetProbeWall hψ l r
  let q1 := authorizedGenCleanWidth hψ hwidth hle κ q0.1 q0.2
  let q2 := authorizedCleanSig hψ q1.1 q1.2
  authorizedEliminateSig hψ q2.1 q2.2

theorem generationBeforeMoveWidth_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authSignalPair (generationBeforeMoveWidth hψ hwidth hle κ l r) =
      authSignalPair (authorizedPPsiLeaderResetProbeWall hψ l r) := by
  let q0 := authorizedPPsiLeaderResetProbeWall hψ l r
  let q1 := authorizedGenCleanWidth hψ hwidth hle κ q0.1 q0.2
  let q2 := authorizedCleanSig hψ q1.1 q1.2
  unfold generationBeforeMoveWidth
  exact (eliminate_signal hψ q2.1 q2.2).trans
    ((clean_signal hψ q1.1 q1.2).trans
      (authorizedGenCleanWidth_signal hψ hwidth hle κ q0.1 q0.2))

theorem generationBeforeMoveWidth_domain (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (generationBeforeMoveWidth hψ hwidth hle κ l r).1.core.inProtocolDomain κ ∧
      (generationBeforeMoveWidth hψ hwidth hle κ l r).2.core.inProtocolDomain κ := by
  let q0 := authorizedPPsiLeaderResetProbeWall hψ l r
  have h0 := authorizedPPsiLeaderResetProbeWall_inProtocolDomain hψ l r hl hr
  let q1 := authorizedGenCleanWidth hψ hwidth hle κ q0.1 q0.2
  have h1 := authorizedGenCleanWidth_domain hψ hwidth hle κ q0.1 q0.2 h0.1 h0.2
  let q2 := authorizedCleanSig hψ q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain (cleanSig hψ) q1.1 q1.2
    (cleanSig_inProtocolDomain hψ q1.1.core q1.2.core h1.1 h1.2)
  exact authorizedReconcile_inProtocolDomain (eliminateSig hψ) q2.1 q2.2
    (eliminateSig_inProtocolDomain hψ q2.1.core q2.2.core h2.1 h2.2)

theorem generationBeforeMoveWidth_full (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    generationBeforeMoveWidth hψ hψ (Nat.le_refl ψ) κ l r =
      generationBeforeMove hψ κ l r := by
  let q0 := authorizedPPsiLeaderResetProbeWall hψ l r
  let tail :
      (AuthorizedAgentState ψ × AuthorizedAgentState ψ) →
        (AuthorizedAgentState ψ × AuthorizedAgentState ψ) := fun q1 =>
    let q2 := authorizedCleanSig hψ q1.1 q1.2
    authorizedEliminateSig hψ q2.1 q2.2
  change
    tail (authorizedGenCleanWidth hψ hψ (Nat.le_refl ψ) κ q0.1 q0.2) =
      tail (authorizedGenClean hψ κ q0.1 q0.2)
  exact congrArg tail
    (authorizedGenCleanWidth_full hψ κ q0.1 q0.2)

attribute [local irreducible]
  generationBeforeMoveWidth authorizedDoneMove authorizedPPsiLeaderResetProbeWall

/-- DONE movement and pre-CHECK reset/sanitization are unchanged; only their
GEN input is the short-width prefix above. -/
def doneBeforeCheckWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let b := generationBeforeMoveWidth hψ hwidth hle κ l r
  let q := authorizedDoneMove hψ b.1 b.2
  sanitizeAuthorizedPair hψ (preCheckResetWall q.1 q.2)

theorem doneBeforeCheckWidth_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authSignalPair (doneBeforeCheckWidth hψ hwidth hle κ l r) =
      authSignalPair (authorizedPPsiLeaderResetProbeWall hψ l r) := by
  let b := generationBeforeMoveWidth hψ hwidth hle κ l r
  let q := authorizedDoneMove hψ b.1 b.2
  unfold doneBeforeCheckWidth
  have hs :
      authSignalPair
        (PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair hψ
          (preCheckResetWall q.1 q.2)) = authSignalPair q :=
    authSignalPair_of_peace
      (sanitizePreCheckResetWall_peaceViewPair hψ q)
  have hm : authSignalPair q = authSignalPair b :=
    K2BirthDispatcherDone.authorizedDoneMove_signal hψ b.1 b.2
  exact hs.trans
    (hm.trans (generationBeforeMoveWidth_signal hψ hwidth hle κ l r))

theorem doneBeforeCheckWidth_bullets (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (doneBeforeCheckWidth hψ hwidth hle κ l r) =
      authorizedBulletFieldPair (l, r) := by
  have hs := authBullets_of_signal
    (doneBeforeCheckWidth_signal hψ hwidth hle κ l r)
  have hp :
      authorizedBulletFieldPair (authorizedPPsiLeaderResetProbeWall hψ l r) =
        authorizedBulletFieldPair (l, r) := by
    unfold authorizedPPsiLeaderResetProbeWall
    exact pPsiLeaderResetProbeWall_bulletFieldPair hψ l.core r.core
  exact hs.trans hp

theorem doneBeforeCheckWidth_leaders (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true →
      (doneBeforeCheckWidth hψ hwidth hle κ l r).1.core.leader = true) ∧
    (r.core.leader = true →
      (doneBeforeCheckWidth hψ hwidth hle κ l r).2.core.leader = true) := by
  let l0 := if l.core.leader = true then { l.core with probe := false } else l.core
  let r0 := if r.core.leader = true ∨ l.core.leader = true ∨ l.core.reset_cmd = true then
    { r.core with probe := false } else r.core
  have hl0 : l0.leader = l.core.leader := by unfold l0; split <;> rfl
  have hr0 : r0.leader = r.core.leader := by unfold r0; split <;> rfl
  have hs := doneBeforeCheckWidth_signal hψ hwidth hle κ l r
  have hL := congrArg (fun q : AgentState 1 × AgentState 1 => q.1.leader) hs
  have hR := congrArg (fun q : AgentState 1 × AgentState 1 => q.2.leader) hs
  unfold authorizedPPsiLeaderResetProbeWall at hL hR
  change (doneBeforeCheckWidth hψ hwidth hle κ l r).1.core.leader =
    (pPsi hψ l0 r0).1.leader at hL
  change (doneBeforeCheckWidth hψ hwidth hle κ l r).2.core.leader =
    (pPsi hψ l0 r0).2.leader at hR
  exact ⟨fun h => hL.trans
      ((PPLLVerify.pPsi_initiator_leader_eq hψ l0 r0).trans (hl0.trans h)),
    fun h => hR.trans
      (PPLLVerify.pPsi_responder_leader_of_true hψ l0 r0 (hr0.trans h))⟩

theorem doneBeforeCheckWidth_domain (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (doneBeforeCheckWidth hψ hwidth hle κ l r).1.core.inProtocolDomain κ ∧
      (doneBeforeCheckWidth hψ hwidth hle κ l r).2.core.inProtocolDomain κ := by
  let b := generationBeforeMoveWidth hψ hwidth hle κ l r
  have hb := generationBeforeMoveWidth_domain hψ hwidth hle κ l r hl hr
  have hm := authorizedDoneMove_inProtocolDomain hψ b.1 b.2 hb.1 hb.2
  let m := authorizedDoneMove hψ b.1 b.2
  have hw := preCheckResetWall_inProtocolDomain m.1 m.2 hm.1 hm.2
  exact ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain hψ _ hw.1,
    sanitizeAuthorizedTerminalEqual_inProtocolDomain hψ _ hw.2⟩

theorem doneBeforeCheckWidth_full (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    doneBeforeCheckWidth hψ hψ (Nat.le_refl ψ) κ l r =
      BirthGenerationDone.doneBeforeCheck hψ κ l r := by
  let tail :
      (AuthorizedAgentState ψ × AuthorizedAgentState ψ) →
        (AuthorizedAgentState ψ × AuthorizedAgentState ψ) := fun b =>
    let q := authorizedDoneMove hψ b.1 b.2
    PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair hψ
      (preCheckResetWall q.1 q.2)
  change
    tail (generationBeforeMoveWidth hψ hψ (Nat.le_refl ψ) κ l r) =
      tail (generationBeforeMove hψ κ l r)
  exact congrArg tail
    (generationBeforeMoveWidth_full hψ κ l r)

/-! ## Cut 2: shortened SUPPRESS before the unchanged stationary WRITE -/

private theorem suppressStart_signal (l r : AgentState ψ) :
    signalPair (suppressSigStart l r) = signalPair (l, r) := by
  unfold suppressSigStart
  repeat (first | rfl | split)

private theorem resetKill_signal (u : AgentState ψ) :
    signalView (resetKillComparison u) = signalView u := by
  unfold resetKillComparison
  repeat (first | rfl | split)

private theorem resetKillPair_signal (l r : AgentState ψ) :
    signalPair (resetKillComparison l, resetKillComparison r) = signalPair (l, r) :=
  Prod.ext (resetKill_signal l) (resetKill_signal r)

private theorem suppressMove_signal (l r : AgentState ψ) :
    signalPair (suppressSigMoveReset l r) = signalPair (l, r) := by
  unfold suppressSigMoveReset
  repeat (first | rfl | split)

private theorem shortCountReset_signal (hwidth : 0 < width) (hle : width <= ψ)
    (l r : AgentState ψ) :
    signalPair (shortCountReset hwidth hle l r) = signalPair (l, r) := by
  unfold shortCountReset
  repeat (first | rfl | split)

private theorem suppressTerminal_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (suppressSigTerminal hψ l r) = signalPair (l, r) := by
  unfold suppressSigTerminal
  repeat (first | rfl | split)

private theorem suppressEcho_signal (l r : AgentState ψ) :
    signalPair (suppressSigEcho l r) = signalPair (l, r) := by
  unfold suppressSigEcho
  repeat (first | rfl | split)

private theorem suppressFinish_signal (l r : AgentState ψ) :
    signalPair (suppressSigFinish l r) = signalPair (l, r) := by
  unfold suppressSigFinish
  repeat (first | rfl | split)

private theorem suppressPrefix_signal (l r : AgentState ψ) :
    signalPair (suppressPrefix l r) = signalPair (l, r) := by
  unfold suppressPrefix
  dsimp only
  rw [resetKillPair_signal, suppressMove_signal,
    resetKillPair_signal, suppressStart_signal]

/-- Source-derived four-field frame for the changed SUPPRESS row. -/
theorem suppressWidth_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : AgentState ψ) :
    signalPair (suppressSigResetKillWidth hψ hwidth hle l r) =
      signalPair (l, r) := by
  unfold suppressSigResetKillWidth
  dsimp only
  rw [suppressFinish_signal, suppressEcho_signal, suppressTerminal_signal,
    shortCountReset_signal, suppressPrefix_signal]

/-- Actual authorization adapter at the old SUPPRESS call in `beforeWrite`. -/
def authorizedSuppressWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  authorizedReconcile (suppressSigResetKillWidth hψ hwidth hle) l r

theorem authorizedSuppressWidth_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : AuthorizedAgentState ψ) :
    authSignalPair (authorizedSuppressWidth hψ hwidth hle l r) =
      authSignalPair (l, r) := by
  change signalPair (suppressSigResetKillWidth hψ hwidth hle l.core r.core) =
    signalPair (l.core, r.core)
  exact suppressWidth_signal hψ hwidth hle l.core r.core

theorem authorizedSuppressWidth_domain (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (authorizedSuppressWidth hψ hwidth hle l r).1.core.inProtocolDomain κ ∧
      (authorizedSuppressWidth hψ hwidth hle l r).2.core.inProtocolDomain κ := by
  exact authorizedReconcile_inProtocolDomain
    (suppressSigResetKillWidth hψ hwidth hle) l r
    (suppressSigResetKillWidth_inProtocolDomain hψ hwidth hle
      l.core r.core hl hr)

theorem authorizedSuppressWidth_full (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) :
    authorizedSuppressWidth hψ hψ (Nat.le_refl ψ) l r =
      authorizedReconcile (suppressSigResetKill hψ) l r := by
  unfold authorizedSuppressWidth
  have hfun :
      suppressSigResetKillWidth (psi := ψ) (width := ψ)
          hψ hψ (Nat.le_refl ψ) =
        suppressSigResetKill hψ := by
    funext a b
    exact suppressWidth_full hψ a b
  exact congrArg (fun f => authorizedReconcile f l r) hfun

/-- DISAPPEAR and action-one COMPARE are unchanged; only SUPPRESS is short. -/
def beforeWriteWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q0 := authorizedDisappear hψ l r
  let q1 := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ q0.1 q0.2
  authorizedSuppressWidth hψ hwidth hle q1.1 q1.2

theorem beforeWriteWidth_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : AuthorizedAgentState ψ) :
    authSignalPair (beforeWriteWidth hψ hwidth hle l r) = authSignalPair (l, r) := by
  let q0 := authorizedDisappear hψ l r
  let q1 := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ q0.1 q0.2
  unfold beforeWriteWidth
  exact (authorizedSuppressWidth_signal hψ hwidth hle q1.1 q1.2).trans
    ((compare_signal hψ q0.1 q0.2).trans (disappear_signal hψ l r))

theorem beforeWriteWidth_domain (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (beforeWriteWidth hψ hwidth hle l r).1.core.inProtocolDomain κ ∧
      (beforeWriteWidth hψ hwidth hle l r).2.core.inProtocolDomain κ := by
  let q0 := authorizedDisappear hψ l r
  have h0 := authorizedReconcile_inProtocolDomain (disappear hψ) l r
    (disappear_inProtocolDomain hψ l.core r.core hl hr)
  let q1 := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ q0.1 q0.2
  have h1 := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne_inProtocolDomain
    hψ q0.1 q0.2 h0.1 h0.2
  exact authorizedSuppressWidth_domain hψ hwidth hle q1.1 q1.2 h1.1 h1.2

theorem beforeWriteWidth_full (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    beforeWriteWidth hψ hψ (Nat.le_refl ψ) l r = beforeWrite hψ l r := by
  unfold beforeWriteWidth beforeWrite
  rw [authorizedSuppressWidth_full hψ]

/-- Same stationary persistent writer, fed by the changed SUPPRESS output. -/
def afterCheckMetadataWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := beforeWriteWidth hψ hwidth hle l r
  stationaryPersistentAuthorizedRow hψ q.1 q.2

theorem afterCheckMetadataWidth_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : AuthorizedAgentState ψ) :
    authSignalPair (afterCheckMetadataWidth hψ hwidth hle l r) =
      authSignalPair (l, r) := by
  let q := beforeWriteWidth hψ hwidth hle l r
  exact (stationaryWriter_signal hψ q.1 q.2).trans
    (beforeWriteWidth_signal hψ hwidth hle l r)

theorem afterCheckMetadataWidth_domain (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (afterCheckMetadataWidth hψ hwidth hle l r).1.core.inProtocolDomain κ ∧
      (afterCheckMetadataWidth hψ hwidth hle l r).2.core.inProtocolDomain κ := by
  have h := beforeWriteWidth_domain hψ hwidth hle l r hl hr
  unfold afterCheckMetadataWidth
  exact stationaryPersistentAuthorizedRow_domain hψ _ _ h.1 h.2

theorem afterCheckMetadataWidth_full (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) :
    afterCheckMetadataWidth hψ hψ (Nat.le_refl ψ) l r =
      afterCheckMetadata hψ l r := by
  unfold afterCheckMetadataWidth afterCheckMetadata
  rw [beforeWriteWidth_full hψ]

/-! ## Smallest actual DONE metadata host using both changed cuts -/

def doneThroughCheckWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let b := doneBeforeCheckWidth hψ hwidth hle κ l r
  preserveDoneCheck hψ b.1 b.2

theorem doneThroughCheckWidth_bullets (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (doneThroughCheckWidth hψ hwidth hle κ l r) =
      authorizedBulletFieldPair (l, r) := by
  unfold doneThroughCheckWidth
  dsimp only
  exact (preserveDoneCheck_bullets hψ _ _).trans
    (doneBeforeCheckWidth_bullets hψ hwidth hle κ l r)

theorem doneThroughCheckWidth_leaders (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true →
      (doneThroughCheckWidth hψ hwidth hle κ l r).1.core.leader = true) ∧
    (r.core.leader = true →
      (doneThroughCheckWidth hψ hwidth hle κ l r).2.core.leader = true) := by
  let b := doneBeforeCheckWidth hψ hwidth hle κ l r
  have hb := doneBeforeCheckWidth_leaders hψ hwidth hle κ l r
  have hc := preserveDoneCheck_leaders hψ b.1 b.2
  exact ⟨hc.1 ∘ hb.1, hc.2 ∘ hb.2⟩

theorem doneThroughCheckWidth_domain (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (doneThroughCheckWidth hψ hwidth hle κ l r).1.core.inProtocolDomain κ ∧
      (doneThroughCheckWidth hψ hwidth hle κ l r).2.core.inProtocolDomain κ := by
  let b := doneBeforeCheckWidth hψ hwidth hle κ l r
  have hb := doneBeforeCheckWidth_domain hψ hwidth hle κ l r hl hr
  exact preserveDoneCheck_inProtocolDomain hψ b.1 b.2 hb.1 hb.2

theorem doneThroughCheckWidth_full (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    doneThroughCheckWidth hψ hψ (Nat.le_refl ψ) κ l r =
      K2BirthDispatcherDone.doneThroughCheck hψ κ l r := by
  unfold doneThroughCheckWidth K2BirthDispatcherDone.doneThroughCheck
  rw [doneBeforeCheckWidth_full hψ]

def doneOrdinaryMetadataWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let c := doneThroughCheckWidth hψ hwidth hle κ l r
  let q := afterCheckMetadataWidth hψ hwidth hle c.1 c.2
  markLeaderBirth (authBirth l r q) q

theorem doneOrdinaryMetadataWidth_signal (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authSignalPair (doneOrdinaryMetadataWidth hψ hwidth hle κ l r) =
      authSignalPair (doneThroughCheckWidth hψ hwidth hle κ l r) := by
  let c := doneThroughCheckWidth hψ hwidth hle κ l r
  let q := afterCheckMetadataWidth hψ hwidth hle c.1 c.2
  unfold doneOrdinaryMetadataWidth
  exact (markBirth_signal (authBirth l r q) q).trans
    (afterCheckMetadataWidth_signal hψ hwidth hle c.1 c.2)

theorem doneOrdinaryMetadataWidth_bullets (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (doneOrdinaryMetadataWidth hψ hwidth hle κ l r) =
      authorizedBulletFieldPair (l, r) :=
  (authBullets_of_signal
    (doneOrdinaryMetadataWidth_signal hψ hwidth hle κ l r)).trans
      (doneThroughCheckWidth_bullets hψ hwidth hle κ l r)

theorem doneOrdinaryMetadataWidth_leaders (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true →
      (doneOrdinaryMetadataWidth hψ hwidth hle κ l r).1.core.leader = true) ∧
    (r.core.leader = true →
      (doneOrdinaryMetadataWidth hψ hwidth hle κ l r).2.core.leader = true) := by
  have hs := doneOrdinaryMetadataWidth_signal hψ hwidth hle κ l r
  have hc := doneThroughCheckWidth_leaders hψ hwidth hle κ l r
  exact ⟨fun hl => (congrArg (fun q => q.1.leader) hs).trans (hc.1 hl),
    fun hr => (congrArg (fun q => q.2.leader) hs).trans (hc.2 hr)⟩

theorem doneOrdinaryMetadataWidth_domain (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (doneOrdinaryMetadataWidth hψ hwidth hle κ l r).1.core.inProtocolDomain κ ∧
      (doneOrdinaryMetadataWidth hψ hwidth hle κ l r).2.core.inProtocolDomain κ := by
  let c := doneThroughCheckWidth hψ hwidth hle κ l r
  have hc := doneThroughCheckWidth_domain hψ hwidth hle l r hl hr
  have hw := afterCheckMetadataWidth_domain hψ hwidth hle c.1 c.2 hc.1 hc.2
  unfold doneOrdinaryMetadataWidth
  exact markLeaderBirth_inProtocolDomain _ _ hw

theorem doneOrdinaryMetadataWidth_full (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    doneOrdinaryMetadataWidth hψ hψ (Nat.le_refl ψ) κ l r =
      K2BirthDispatcherDone.doneOrdinaryMetadata hψ κ l r := by
  let cS := doneThroughCheckWidth hψ hψ (Nat.le_refl ψ) κ l r
  let cO := K2BirthDispatcherDone.doneThroughCheck hψ κ l r
  have hc : cS = cO :=
    doneThroughCheckWidth_full hψ κ l r
  have hq :
      afterCheckMetadataWidth hψ hψ (Nat.le_refl ψ) cS.1 cS.2 =
        afterCheckMetadata hψ cO.1 cO.2 := by
    calc
      afterCheckMetadataWidth hψ hψ (Nat.le_refl ψ) cS.1 cS.2 =
          afterCheckMetadata hψ cS.1 cS.2 :=
        afterCheckMetadataWidth_full hψ cS.1 cS.2
      _ = afterCheckMetadata hψ cO.1 cO.2 :=
        congrArg
          (fun c : AuthorizedAgentState ψ × AuthorizedAgentState ψ =>
            afterCheckMetadata hψ c.1 c.2) hc
  let finish :
      (AuthorizedAgentState ψ × AuthorizedAgentState ψ) →
        (AuthorizedAgentState ψ × AuthorizedAgentState ψ) := fun q =>
    markLeaderBirth (authBirth l r q) q
  change
    finish (afterCheckMetadataWidth hψ hψ (Nat.le_refl ψ) cS.1 cS.2) =
      finish (afterCheckMetadata hψ cO.1 cO.2)
  exact congrArg finish hq

/-- Same deletion priority as the accepted DONE metadata row. -/
def doneMetadataAuthorizedWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then authorizedEliminateSig hψ l0 r0
  else if deletionActive l0 then (l0, r0)
  else doneOrdinaryMetadataWidth hψ hwidth hle κ l0 r0

attribute [local irreducible]
  doneBeforeCheckWidth beforeWriteWidth
  afterCheckMetadataWidth doneThroughCheckWidth doneOrdinaryMetadataWidth
  doneMetadataAuthorizedWidth

theorem doneMetadataAuthorizedWidth_bullets (hψ : 0 < ψ)
    (hwidth : 0 < width) (hle : width <= ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (doneMetadataAuthorizedWidth hψ hwidth hle κ l r) =
      authorizedBulletFieldPair (l, r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have h0 := authBullets_of_signal (normalize_pair_signal l r)
  unfold doneMetadataAuthorizedWidth
  dsimp only
  split
  · exact (authBullets_of_signal (eliminate_signal hψ l0 r0)).trans h0
  · split
    · exact h0
    · exact (doneOrdinaryMetadataWidth_bullets hψ hwidth hle κ l0 r0).trans h0

theorem doneMetadataAuthorizedWidth_leaders (hψ : 0 < ψ)
    (hwidth : 0 < width) (hle : width <= ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true →
      (doneMetadataAuthorizedWidth hψ hwidth hle κ l r).1.core.leader = true) ∧
    (r.core.leader = true →
      (doneMetadataAuthorizedWidth hψ hwidth hle κ l r).2.core.leader = true) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 : l0.core.leader = l.core.leader :=
    congrArg (fun u : AgentState 1 => u.leader) (normalize_signal l)
  have hr0 : r0.core.leader = r.core.leader :=
    congrArg (fun u : AgentState 1 => u.leader) (normalize_signal r)
  unfold doneMetadataAuthorizedWidth
  dsimp only
  split
  · have he := eliminate_signal hψ l0 r0
    exact ⟨fun hl => (congrArg (fun q => q.1.leader) he).trans (hl0.trans hl),
      fun hr => (congrArg (fun q => q.2.leader) he).trans (hr0.trans hr)⟩
  · split
    · exact ⟨fun hl => hl0.trans hl, fun hr => hr0.trans hr⟩
    · have he := doneOrdinaryMetadataWidth_leaders hψ hwidth hle κ l0 r0
      exact ⟨fun hl => he.1 (hl0.trans hl), fun hr => he.2 (hr0.trans hr)⟩

theorem doneMetadataAuthorizedWidth_domain (hψ : 0 < ψ)
    (hwidth : 0 < width) (hle : width <= ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (doneMetadataAuthorizedWidth hψ hwidth hle κ l r).1.core.inProtocolDomain κ ∧
      (doneMetadataAuthorizedWidth hψ hwidth hle κ l r).2.core.inProtocolDomain κ := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  unfold doneMetadataAuthorizedWidth
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain (eliminateSig hψ) l0 r0
      (eliminateSig_inProtocolDomain hψ l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · exact doneOrdinaryMetadataWidth_domain hψ hwidth hle l0 r0 hl0 hr0

theorem doneMetadataAuthorizedWidth_full (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    doneMetadataAuthorizedWidth hψ hψ (Nat.le_refl ψ) κ l r =
      K2BirthDispatcherDone.doneMetadataAuthorized hψ κ l r := by
  unfold doneMetadataAuthorizedWidth K2BirthDispatcherDone.doneMetadataAuthorized
  dsimp only
  split
  · rfl
  · split
    · rfl
    · exact doneOrdinaryMetadataWidth_full hψ κ _ _

/-- Reify on the unchanged finite carrier. -/
def doneMetadataBoundedWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q := doneMetadataAuthorizedWidth hψ hwidth hle κ l.erase r.erase
  let hq := doneMetadataAuthorizedWidth_domain hψ hwidth hle l.erase r.erase
    l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

attribute [local irreducible] doneMetadataBoundedWidth

theorem doneMetadataBoundedWidth_erase (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : AuthorizedBoundedAgentState ψ κ) :
    ((doneMetadataBoundedWidth hψ hwidth hle l r).1.erase,
      (doneMetadataBoundedWidth hψ hwidth hle l r).2.erase) =
      doneMetadataAuthorizedWidth hψ hwidth hle κ l.erase r.erase := by
  unfold doneMetadataBoundedWidth
  simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]

/-- Same entry-disposal preparation and exactly one existing expiry call per
endpoint.  No newborn/K2 call is added here. -/
def doneMetadataWidth (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let q := doneMetadataBoundedWidth hψ hwidth hle l0.core r0.core
  (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩,
    deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩)

attribute [local irreducible] doneMetadataWidth

/-- Exact finite observation through reification and the two unchanged expiry
calls. -/
theorem doneMetadataWidth_observation (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ) :
    (observeCell (doneMetadataWidth hψ hwidth hle l r).1,
      observeCell (doneMetadataWidth hψ hwidth hle l r).2) =
      authSignalPair (doneMetadataAuthorizedWidth hψ hwidth hle κ
        (prepareExpiringDisposal hψ l).core.erase
        (prepareExpiringDisposal hψ r).core.erase) := by
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let q := doneMetadataBoundedWidth hψ hwidth hle l0.core r0.core
  have he := congrArg authSignalPair
    (doneMetadataBoundedWidth_erase hψ hwidth hle l0.core r0.core)
  have hx :
      (observeCell (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩),
        observeCell (deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩)) =
      (observeCell (⟨q.1, l0.stall⟩ : ExpiringAgentState ψ κ τ),
        observeCell (⟨q.2, r0.stall⟩ : ExpiringAgentState ψ κ τ)) :=
    Prod.ext (priority_expiry_observation l0 (⟨q.1, l0.stall⟩))
      (priority_expiry_observation r0 (⟨q.2, r0.stall⟩))
  unfold doneMetadataWidth
  exact hx.trans he

theorem doneMetadataWidth_domain (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width <= ψ) (l r : ExpiringAgentState ψ κ τ) :
    (doneMetadataWidth hψ hwidth hle l r).1.core.core.erase.inProtocolDomain κ ∧
      (doneMetadataWidth hψ hwidth hle l r).2.core.core.erase.inProtocolDomain κ :=
  ⟨(doneMetadataWidth hψ hwidth hle l r).1.core.core.erase_inProtocolDomain,
    (doneMetadataWidth hψ hwidth hle l r).2.core.core.erase_inProtocolDomain⟩

#print axioms BirthShortDoneCuts.genCleanWidth_signal
#print axioms BirthShortDoneCuts.authorizedGenCleanWidth_signal
#print axioms BirthShortDoneCuts.authorizedGenCleanWidth_domain
#print axioms BirthShortDoneCuts.generationBeforeMoveWidth_signal
#print axioms BirthShortDoneCuts.generationBeforeMoveWidth_domain
#print axioms BirthShortDoneCuts.generationBeforeMoveWidth_full
#print axioms BirthShortDoneCuts.doneBeforeCheckWidth_bullets
#print axioms BirthShortDoneCuts.doneBeforeCheckWidth_leaders
#print axioms BirthShortDoneCuts.doneBeforeCheckWidth_domain
#print axioms BirthShortDoneCuts.doneBeforeCheckWidth_full
#print axioms BirthShortDoneCuts.suppressWidth_signal
#print axioms BirthShortDoneCuts.authorizedSuppressWidth_signal
#print axioms BirthShortDoneCuts.authorizedSuppressWidth_domain
#print axioms BirthShortDoneCuts.beforeWriteWidth_signal
#print axioms BirthShortDoneCuts.beforeWriteWidth_domain
#print axioms BirthShortDoneCuts.beforeWriteWidth_full
#print axioms BirthShortDoneCuts.afterCheckMetadataWidth_signal
#print axioms BirthShortDoneCuts.afterCheckMetadataWidth_domain
#print axioms BirthShortDoneCuts.afterCheckMetadataWidth_full
#print axioms BirthShortDoneCuts.doneMetadataAuthorizedWidth_bullets
#print axioms BirthShortDoneCuts.doneMetadataAuthorizedWidth_leaders
#print axioms BirthShortDoneCuts.doneMetadataAuthorizedWidth_domain
#print axioms BirthShortDoneCuts.doneMetadataAuthorizedWidth_full
#print axioms BirthShortDoneCuts.doneMetadataBoundedWidth_erase
#print axioms BirthShortDoneCuts.doneMetadataWidth_observation
#print axioms BirthShortDoneCuts.doneMetadataWidth_domain

end BirthShortDoneCuts
