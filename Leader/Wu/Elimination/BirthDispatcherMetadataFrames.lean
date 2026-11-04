import Leader.Wu.Birth.SingleUseReleaseRepair
import Leader.Wu.Comparison.ExpiringK2ProjectionHostBoundary

/-! Source-derived physical frames of the concrete metadata prefix.
The view below is data only; no transition or probability law is assumed. -/

namespace K2BirthDispatcher

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepNormalResetContract PPLLWallSweepPreCheckResetRepair
  PPLLNoCheckBirthConditionTwoFrames PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol PPLLNoCheckBirthLeaderFrames
  BirthArrivalCaptureRepair BirthGenerationControlRepair
  BirthSingleUseReleaseRepair BirthTossCheckPreservationRepair
  BirthCheckCongestGuardRepair BirthSigMoveDisposalRepair K2OutputSafety

set_option autoImplicit false
set_option pp.structureInstances false

variable {ψ κ : Nat}

def signalPair (q : AgentState ψ × AgentState ψ) : AgentState 1 × AgentState 1 :=
  (signalView q.1, signalView q.2)

def authSignalPair (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    AgentState 1 × AgentState 1 := signalPair (q.1.core, q.2.core)

theorem signal_of_peace {u v : AgentState ψ}
    (h : PeaceView.ofState u = PeaceView.ofState v) : signalView u = signalView v :=
  congrArg (fun p : PeaceView ψ => PeaceView.toState
    (ψ := 1) ⟨p.leader, 0, p.shield, p.bullet, p.signal_B⟩) h

theorem signalPair_of_peace {q p : AgentState ψ × AgentState ψ}
    (h : peaceViewPair q = peaceViewPair p) : signalPair q = signalPair p :=
  Prod.ext (signal_of_peace (congrArg Prod.fst h))
    (signal_of_peace (congrArg Prod.snd h))

theorem authSignalPair_of_peace
    {q p : AuthorizedAgentState ψ × AuthorizedAgentState ψ}
    (h : authorizedPeaceViewPair q = authorizedPeaceViewPair p) :
    authSignalPair q = authSignalPair p := signalPair_of_peace h

theorem authBullets_of_signal
    {q p : AuthorizedAgentState ψ × AuthorizedAgentState ψ}
    (h : authSignalPair q = authSignalPair p) :
    authorizedBulletFieldPair q = authorizedBulletFieldPair p := by
  apply Prod.ext <;> apply BulletFields.ext
  · exact congrArg (fun q => q.1.shield) h
  · exact congrArg (fun q => q.1.bullet) h
  · exact congrArg (fun q => q.1.signal_B) h
  · exact congrArg (fun q => q.2.shield) h
  · exact congrArg (fun q => q.2.bullet) h
  · exact congrArg (fun q => q.2.signal_B) h

theorem signalPair_of_fields {q p : AgentState ψ × AgentState ψ}
    (hl : leaderPair q = leaderPair p)
    (hb : bulletFieldPair q = bulletFieldPair p) : signalPair q = signalPair p := by
  have h : ∀ (a b : AgentState ψ), a.leader = b.leader →
      BulletFields.ofState a = BulletFields.ofState b → signalView a = signalView b := by
    intro a b hleader hfields
    have hs := congrArg BulletFields.shield hfields
    have hb := congrArg BulletFields.bullet hfields
    have hz := congrArg BulletFields.signal_B hfields
    change a.shield = b.shield at hs
    change a.bullet = b.bullet at hb
    change a.signal_B = b.signal_B at hz
    simp only [signalView, hleader, hs, hb, hz]
  exact Prod.ext (h _ _ (congrArg Prod.fst hl) (congrArg Prod.fst hb))
    (h _ _ (congrArg Prod.snd hl) (congrArg Prod.snd hb))

private theorem clearRelease_signal (hψ : 0 < ψ) (u : AgentState ψ) :
    signalView (clearTerminalRelease hψ u) = signalView u := by
  unfold clearTerminalRelease
  repeat (first | rfl | split)

theorem captureStep1_signal (l r : AgentState ψ) :
    signalPair (captureStep1 l r) = signalPair (l, r) := by
  unfold captureStep1
  repeat (first | rfl | split)

private theorem step2_signal (l r : AgentState ψ) :
    signalPair (sigMoveStep2 l r) = signalPair (l, r) := by
  unfold sigMoveStep2
  repeat (first | rfl | split)

private theorem step3_signal (l r : AgentState ψ) :
    signalPair (sigMoveStep3 l r) = signalPair (l, r) := by
  unfold sigMoveStep3
  repeat (first | rfl | split)

private theorem step4_signal (l r : AgentState ψ) :
    signalPair (sigMoveStep4 l r) = signalPair (l, r) := by
  unfold sigMoveStep4
  repeat (first | rfl | split)

private theorem step5_signal (l r : AgentState ψ) :
    signalPair (sigMoveStep5 l r) = signalPair (l, r) := by
  unfold sigMoveStep5
  repeat (first | rfl | split)

theorem captureTransfers_signal (l r : AgentState ψ) :
    signalPair (captureTransfers l r) = signalPair (l, r) := by
  unfold captureTransfers
  dsimp only
  rw [step5_signal, step4_signal, step3_signal, step2_signal, captureStep1_signal]

private theorem preclear_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (sigMoveLeaderPreclear hψ l r) = signalPair (l, r) := by
  unfold sigMoveLeaderPreclear clearIfLeader
  repeat (first | rfl | split)

private theorem leaderWall_signal (l r : AgentState ψ) :
    signalPair (comparisonLeaderWall l r) = signalPair (l, r) := by
  unfold comparisonLeaderWall
  repeat (first | rfl | split)

private theorem applyControl_signal (hψ : 0 < ψ) (u : AgentState ψ) :
    signalView (sigMoveApplyControl hψ u) = signalView u := by
  cases hp : u.path2 with
  | none => simp only [sigMoveApplyControl, hp]
  | some p =>
    by_cases h1 : u.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧ (p.action = 3 ∨ p.action = 4)
    <;> by_cases h2 : u.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧ p.action = 5
    <;> by_cases h3 : u.label = (⟨0, hψ⟩ : Fin ψ) ∧ p.action = 6
    <;> simp [sigMoveApplyControl, hp, h1, h2, h3, signalView]

private theorem controlTail_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (sigMoveControlTail hψ l r) = signalPair (l, r) := by
  unfold sigMoveControlTail
  dsimp only
  split
  · split <;> exact Prod.ext (applyControl_signal hψ l) (applyControl_signal hψ r)
  · exact Prod.ext (applyControl_signal hψ l) (applyControl_signal hψ r)

theorem captureSigMove_signal (hψ : 0 < ψ) (l r : AgentState ψ) :
    signalPair (captureSigMoveLeaderWall hψ l r) = signalPair (l, r) := by
  unfold captureSigMoveLeaderWall
  dsimp only
  rw [controlTail_signal, leaderWall_signal, captureTransfers_signal, preclear_signal]

theorem singleUseMove_signal (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    authSignalPair (authorizedSingleUseReleaseMove hψ l r) = authSignalPair (l, r) := by
  unfold authSignalPair
  rw [authorizedSingleUseReleaseMove_core, singleUseCaptureSigMove_eq_clear]
  change (signalView (clearTerminalRelease hψ _), signalView (clearTerminalRelease hψ _)) = _
  rw [clearRelease_signal, clearRelease_signal]
  exact captureSigMove_signal hψ l.core r.core

theorem clean_signal (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    authSignalPair (authorizedCleanSig hψ l r) = authSignalPair (l, r) :=
  signalPair_of_fields
    (Prod.ext (PPLLVerify.cleanSig_leaders_eq hψ l.core r.core).1
      (PPLLVerify.cleanSig_leaders_eq hψ l.core r.core).2)
    (cleanSig_bulletFieldPair hψ l.core r.core)

theorem eliminate_signal (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    authSignalPair (authorizedEliminateSig hψ l r) = authSignalPair (l, r) :=
  signalPair_of_fields
    (Prod.ext (PPLLVerify.eliminateSig_leaders_eq hψ l.core r.core).1
      (PPLLVerify.eliminateSig_leaders_eq hψ l.core r.core).2)
    (eliminateSig_bulletFieldPair hψ l.core r.core)

attribute [local irreducible] singleUseBeforeCheck generationBeforeMove
  authorizedSingleUseReleaseMove authorizedGenClean authorizedCleanSig
  authorizedEliminateSig authorizedPPsiLeaderResetProbeWall

theorem generationBeforeMove_signal (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authSignalPair (generationBeforeMove hψ κ l r) =
      authSignalPair (authorizedPPsiLeaderResetProbeWall hψ l r) := by
  let q0 := authorizedPPsiLeaderResetProbeWall hψ l r
  let q1 := authorizedGenClean hψ κ q0.1 q0.2
  let q2 := authorizedCleanSig hψ q1.1 q1.2
  have hg : authSignalPair q1 = authSignalPair q0 := by
    unfold q1 authorizedGenClean
    exact ExpiringK2Projection.generation_observation hψ κ _ _
  unfold generationBeforeMove
  exact (eliminate_signal hψ q2.1 q2.2).trans
    ((clean_signal hψ q1.1 q1.2).trans hg)

/-- All changes after the actual probe/label prefix and before CHECK are
invisible to the four physical K2 fields, including capture and single-use release. -/
theorem beforeCheck_signal (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authSignalPair (singleUseBeforeCheck hψ κ l r) =
      authSignalPair (authorizedPPsiLeaderResetProbeWall hψ l r) := by
  let b := generationBeforeMove hψ κ l r
  let q := authorizedSingleUseReleaseMove hψ b.1 b.2
  unfold singleUseBeforeCheck
  exact (authSignalPair_of_peace (sanitizePreCheckResetWall_peaceViewPair hψ q)).trans
    ((singleUseMove_signal hψ b.1 b.2).trans (generationBeforeMove_signal hψ κ l r))

theorem beforeCheck_bullets (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (singleUseBeforeCheck hψ κ l r) =
      authorizedBulletFieldPair (l, r) := by
  have h := authBullets_of_signal (beforeCheck_signal hψ κ l r)
  have hg : authorizedBulletFieldPair (authorizedPPsiLeaderResetProbeWall hψ l r) =
      authorizedBulletFieldPair (l, r) := by
    unfold authorizedPPsiLeaderResetProbeWall
    exact pPsiLeaderResetProbeWall_bulletFieldPair hψ l.core r.core
  exact h.trans hg

theorem beforeCheck_leaders (hψ : 0 < ψ) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true → (singleUseBeforeCheck hψ κ l r).1.core.leader = true) ∧
    (r.core.leader = true → (singleUseBeforeCheck hψ κ l r).2.core.leader = true) := by
  let l0 := if l.core.leader = true then { l.core with probe := false } else l.core
  let r0 := if r.core.leader = true ∨ l.core.leader = true ∨ l.core.reset_cmd = true then
    { r.core with probe := false } else r.core
  have hl0 : l0.leader = l.core.leader := by unfold l0; split <;> rfl
  have hr0 : r0.leader = r.core.leader := by unfold r0; split <;> rfl
  have hl := congrArg (fun q : AgentState 1 × AgentState 1 => q.1.leader)
    (beforeCheck_signal hψ κ l r)
  have hr := congrArg (fun q : AgentState 1 × AgentState 1 => q.2.leader)
    (beforeCheck_signal hψ κ l r)
  unfold authorizedPPsiLeaderResetProbeWall at hl hr
  change (singleUseBeforeCheck hψ κ l r).1.core.leader = (pPsi hψ l0 r0).1.leader at hl
  change (singleUseBeforeCheck hψ κ l r).2.core.leader = (pPsi hψ l0 r0).2.leader at hr
  exact ⟨fun h => hl.trans ((PPLLVerify.pPsi_initiator_leader_eq hψ l0 r0).trans (hl0.trans h)),
    fun h => hr.trans (PPLLVerify.pPsi_responder_leader_of_true hψ l0 r0 (hr0.trans h))⟩

theorem preserveCheck_bullets (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (preserveTossCheck hψ l r) =
      authorizedBulletFieldPair (l, r) := by
  unfold preserveTossCheck congestGuardCheck
  split
  · rfl
  · split
    · rfl
    · exact checkSig_bulletFieldPair hψ l.core r.core

theorem preserveCheck_leaders (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true → (preserveTossCheck hψ l r).1.core.leader = true) ∧
    (r.core.leader = true → (preserveTossCheck hψ l r).2.core.leader = true) := by
  unfold preserveTossCheck congestGuardCheck
  split
  · exact ⟨id, id⟩
  · split
    · exact ⟨id, id⟩
    · exact ⟨fun h => (PPLLVerify.checkSig_initiator_leader_eq hψ l.core r.core).trans h,
        PPLLVerify.checkSig_responder_leader_of_true hψ l.core r.core⟩

/-- The concrete ordinary prefix includes actual GEN/WAIT, single-use
transport and the toss-preserving guarded CHECK, in that order. -/
def throughCheck (hψ : 0 < ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let b := singleUseBeforeCheck hψ κ l r
  preserveTossCheck hψ b.1 b.2

theorem throughCheck_bullets (hψ : 0 < ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    authorizedBulletFieldPair (throughCheck hψ κ l r) =
      authorizedBulletFieldPair (l, r) := by
  let b := singleUseBeforeCheck hψ κ l r
  exact (preserveCheck_bullets hψ b.1 b.2).trans (beforeCheck_bullets hψ κ l r)

theorem throughCheck_leaders (hψ : 0 < ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) :
    (l.core.leader = true → (throughCheck hψ κ l r).1.core.leader = true) ∧
    (r.core.leader = true → (throughCheck hψ κ l r).2.core.leader = true) := by
  let b := singleUseBeforeCheck hψ κ l r
  have hb := beforeCheck_leaders hψ κ l r
  have hc := preserveCheck_leaders hψ b.1 b.2
  exact ⟨hc.1 ∘ hb.1, hc.2 ∘ hb.2⟩

theorem throughCheck_domain (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    (throughCheck hψ κ l r).1.core.inProtocolDomain κ ∧
      (throughCheck hψ κ l r).2.core.inProtocolDomain κ := by
  have h := singleUseBeforeCheck_inProtocolDomain hψ κ l r hl hr
  exact preserveTossCheck_inProtocolDomain hψ _ _ h.1 h.2

theorem normalize_signal (u : AuthorizedAgentState ψ) :
    signalView (normalizeDeletion u).core = signalView u.core :=
  signal_of_peace (normalizeDeletion_peaceView u)

theorem markComparison_signal (u : AuthorizedAgentState ψ) :
    signalView (markComparisonForDeletion u).core = signalView u.core := by
  unfold markComparisonForDeletion
  split <;> rfl

theorem markBirth_signal (b : Bool) (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    authSignalPair (markLeaderBirth b q) = authSignalPair q := by
  cases b
  · rfl
  · exact Prod.ext (markComparison_signal q.1) (markComparison_signal q.2)

theorem prepare_signal (hψ : 0 < ψ) (u : AuthorizedAgentState ψ) :
    signalView (prepareDisposal hψ u).core = signalView u.core := by
  unfold prepareDisposal
  split
  · exact markComparison_signal u
  · rfl

theorem prepareExpiring_signal {τ : Nat} (hψ : 0 < ψ)
    (u : ExpiringAgentState ψ κ τ) :
    ExpiringK2Projection.observeCell (prepareExpiringDisposal hψ u) =
      ExpiringK2Projection.observeCell u := by
  change signalView (prepareBoundedDisposal hψ u.core).erase.core = _
  rw [erase_prepareBoundedDisposal]
  exact prepare_signal hψ u.core.erase

#print axioms beforeCheck_signal
#print axioms beforeCheck_leaders
#print axioms preserveCheck_leaders

end K2BirthDispatcher
