import Leader.Wu.WallSweep.ShieldCircuit

/-!
# Pre-CHECK reset deletion repair

The suppression prose says that a reset command eliminates every comparison
signal it encounters and therefore prevents another leader from being created.
Printed Algorithm 1, however, calls CHECK before SUPPRESS_SIG.  This repair
applies only the deletion effect of an already-present or leader-generated
reset immediately before CHECK; reset movement, echo generation, and every
other Algorithm-14 assignment remain at their original later boundary.

The construction is separately named and belongs to the repair lane.  It adds
no executable field and leaves the source `Leader.Wu.Protocol.Algorithm` transition
unchanged.
-/

namespace PPLLWallSweepPreCheckResetRepair

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLTerminalEqualSupportRepair PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepNormalResetContract
  PPLLWallSweepShieldCircuit
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol
  PPLLWriteIncrementGate

variable {psi kappa tau : Nat}

/-- Clear one authorized comparison carrier and consume any moved-carrier
permission attached to it.  All non-comparison fields are retained. -/
def clearAuthorizedComparison
    (u : AuthorizedAgentState psi) : AuthorizedAgentState psi :=
  ⟨clearComparisonSignal u.core, false⟩

/-- Pre-CHECK deletion effect of suppression.  A leader or left reset token
will send reset to the responder later in the same interaction, so both
endpoints are cleared; a reset already at the responder clears that endpoint. -/
def preCheckResetWall
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let sendRight : Prop :=
    l.core.leader = true ∨ l.core.reset_cmd = true
  let l' := if sendRight then clearAuthorizedComparison l else l
  let r' := if sendRight ∨ r.core.reset_cmd = true then
    clearAuthorizedComparison r else r
  (l', r')

/-- With no leader or reset at the pre-CHECK boundary, the added wall is
definitionally inert and leaves the unchanged CHECK-birth mechanism available. -/
theorem preCheckResetWall_eq_of_inactive
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = false)
    (hlReset : l.core.reset_cmd = false)
    (hrReset : r.core.reset_cmd = false) :
    preCheckResetWall l r = (l, r) := by
  simp [preCheckResetWall, hlLeader, hlReset, hrReset]

/-- A leader or outgoing reset clears both comparison endpoints before CHECK. -/
theorem preCheckResetWall_both_neutral_of_send
    (l r : AuthorizedAgentState psi)
    (hsend : l.core.leader = true ∨ l.core.reset_cmd = true) :
    let q := preCheckResetWall l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.path0Crossed = false ∧ q.2.path0Crossed = false := by
  simp [preCheckResetWall, hsend, clearAuthorizedComparison,
    clearComparisonSignal_neutral]

/-- A responder-resident reset clears at least the responder comparison
carrier before CHECK, even when the initiator sends no reset. -/
theorem preCheckResetWall_responder_neutral_of_reset
    (l r : AuthorizedAgentState psi)
    (hrReset : r.core.reset_cmd = true) :
    ComparisonNeutral (preCheckResetWall l r).2.core ∧
      (preCheckResetWall l r).2.path0Crossed = false := by
  simp [preCheckResetWall, hrReset, clearAuthorizedComparison,
    clearComparisonSignal_neutral]

/-- A comparison-neutral authorized pair remains neutral through the reset
wall, including both movement-permission bits. -/
theorem preCheckResetWall_neutral_of_neutral
    (l r : AuthorizedAgentState psi)
    (hL : ComparisonNeutral l.core)
    (hR : ComparisonNeutral r.core)
    (hpL : l.path0Crossed = false)
    (hpR : r.path0Crossed = false) :
    let q := preCheckResetWall l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.path0Crossed = false ∧ q.2.path0Crossed = false := by
  by_cases hsend : l.core.leader = true ∨ l.core.reset_cmd = true
  · simp [preCheckResetWall, hsend, clearAuthorizedComparison,
      clearComparisonSignal_neutral]
  · by_cases hrReset : r.core.reset_cmd = true
    · simp [preCheckResetWall, hsend, hrReset,
        clearAuthorizedComparison, clearComparisonSignal_neutral,
        hL, hpL]
    · simp [preCheckResetWall, hsend, hrReset, hL, hR, hpL, hpR]

/-- Repaired Algorithm 14 preserves comparison neutrality while moving or
consuming reset/echo controls. -/
theorem suppressSigResetKill_neutral_of_neutral
    (hpsi : psi > 0) (l r : AgentState psi)
    (hL : ComparisonNeutral l) (hR : ComparisonNeutral r) :
    let q := suppressSigResetKill hpsi l r
    ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 := by
  rcases hL with ⟨hLs, hLp, hLp2, hLp4, hLp5, hLP, hLCarry⟩
  rcases hR with ⟨hRs, hRp, hRp2, hRp4, hRp5, hRP, hRCarry⟩
  simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
    resetKillComparison, clearComparisonSignal, ComparisonNeutral,
    suppressSigTerminal, suppressSigEcho, suppressSigFinish,
    hLs, hLp, hLp2, hLp4, hLp5, hLP, hLCarry,
    hRs, hRp, hRp2, hRp4, hRp5, hRP, hRCarry]

/-- The pre-CHECK wall frames the complete Algorithm-15 `PeaceView`. -/
theorem preCheckResetWall_peaceViewPair
    (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (preCheckResetWall l r) =
      authorizedPeaceViewPair (l, r) := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold preCheckResetWall clearAuthorizedComparison
      authorizedPeaceViewPair peaceViewPair PeaceView.ofState
      clearComparisonSignal
    try dsimp only []
    repeat (first | rfl | split)

/-- Applying the reset wall and then terminal-equality sanitation is a single
physical-view frame on any authorized pair. -/
theorem sanitizePreCheckResetWall_peaceViewPair
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedPeaceViewPair
        (sanitizeAuthorizedPair hpsi
          (preCheckResetWall (psi := psi) q.1 q.2)) =
      authorizedPeaceViewPair q :=
  (sanitizeAuthorizedPair_peaceViewPair hpsi
      (preCheckResetWall (psi := psi) q.1 q.2)).trans
    (preCheckResetWall_peaceViewPair q.1 q.2)

/-- The same combined boundary frames the responder leader bit. -/
theorem sanitizePreCheckResetWall_responder_leader_eq
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (sanitizeAuthorizedPair hpsi
        (preCheckResetWall (psi := psi) q.1 q.2)).2.core.leader =
      q.2.core.leader := by
  have h := sanitizePreCheckResetWall_peaceViewPair hpsi q
  exact congrArg
    (fun v : PeaceView psi × PeaceView psi => v.2.leader) h

/-- Field-local consumer for a complete authorized `PeaceView` frame.  The
generic pair arguments keep downstream wall terms opaque while extracting the
responder leader and both labels. -/
theorem responderLeaderAndLabels_of_authorizedPeaceViewPair_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    a.2.core.leader = b.2.core.leader ∧
      a.1.core.label = b.1.core.label ∧
      a.2.core.label = b.2.core.label :=
  ⟨congrArg
      (fun v : PeaceView psi × PeaceView psi => v.2.leader) h,
    congrArg (fun v : PeaceView psi × PeaceView psi => v.1.label) h,
    congrArg (fun v : PeaceView psi × PeaceView psi => v.2.label) h⟩

/-- In particular, the pre-CHECK deletion wall never creates, removes, or
moves a leader. -/
theorem preCheckResetWall_leaders_eq
    (l r : AuthorizedAgentState psi) :
    (preCheckResetWall l r).1.core.leader = l.core.leader ∧
      (preCheckResetWall l r).2.core.leader = r.core.leader := by
  have h := preCheckResetWall_peaceViewPair l r
  have hL := congrArg Prod.fst h
  have hR := congrArg Prod.snd h
  exact ⟨congrArg PeaceView.leader hL, congrArg PeaceView.leader hR⟩

/-- The earlier deletion boundary does not move reset or echo tokens. -/
theorem preCheckResetWall_resetEchoPair
    (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair (preCheckResetWall l r) =
      authorizedResetEchoPair (l, r) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    unfold preCheckResetWall clearAuthorizedComparison
      authorizedResetEchoPair resetEchoPair resetEchoView
      clearComparisonSignal
    try dsimp only []
    repeat (first | rfl | split)

private theorem sanitizeAuthorizedPair_eq_of_neutral
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hL : ComparisonNeutral q.1.core)
    (hR : ComparisonNeutral q.2.core) :
    sanitizeAuthorizedPair hpsi q = q := by
  apply Prod.ext
  · simp [sanitizeAuthorizedPair, sanitizeAuthorizedTerminalEqual,
      unsupportedTerminalEqual, hL.1]
  · simp [sanitizeAuthorizedPair, sanitizeAuthorizedTerminalEqual,
      unsupportedTerminalEqual, hR.1]

/-- **Reset suppresses same-interaction CHECK birth.**  If the initiator is a
leader or carries reset, the wall clears both comparison endpoints, terminal
sanitation is inert, and the subsequent real CHECK frames both leader bits. -/
theorem preCheckResetWall_check_leaders_eq_of_send
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hsend : l.core.leader = true ∨ l.core.reset_cmd = true) :
    let q := preCheckResetWall l r
    let beforeCheck := sanitizeAuthorizedPair hpsi q
    let afterCheck := authorizedCheckSig hpsi
      beforeCheck.1 beforeCheck.2
    afterCheck.1.core.leader = l.core.leader ∧
      afterCheck.2.core.leader = r.core.leader := by
  let q := preCheckResetWall l r
  have hneutral := preCheckResetWall_both_neutral_of_send l r hsend
  change ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
    q.1.path0Crossed = false ∧ q.2.path0Crossed = false at hneutral
  have hsanitize := sanitizeAuthorizedPair_eq_of_neutral
    hpsi q hneutral.1 hneutral.2.1
  have hqLeaders := preCheckResetWall_leaders_eq l r
  change
    (authorizedCheckSig hpsi
      (sanitizeAuthorizedPair hpsi q).1
      (sanitizeAuthorizedPair hpsi q).2).1.core.leader = l.core.leader ∧
    (authorizedCheckSig hpsi
      (sanitizeAuthorizedPair hpsi q).1
      (sanitizeAuthorizedPair hpsi q).2).2.core.leader = r.core.leader
  rw [hsanitize]
  constructor
  · exact (PPLLVerify.checkSig_initiator_leader_eq
      hpsi q.1.core q.2.core).trans hqLeaders.1
  · have hsafe : CheckResponderSafe hpsi q.2.core := by
      right
      right
      left
      refine ⟨hneutral.2.1.2.1, ?_⟩
      intro heq
      rw [hneutral.2.1.1] at heq
      contradiction
    exact (checkSig_responder_leader_eq_of_safe
      hpsi q.1.core q.2.core hsafe).trans hqLeaders.2

private theorem authorizedCheckSig_eq_of_neutral
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hL : ComparisonNeutral l.core) (hR : ComparisonNeutral r.core)
    (hpL : l.path0Crossed = false) (hpR : r.path0Crossed = false) :
    authorizedCheckSig hpsi l r = (l, r) := by
  rcases hL with ⟨hLs, hLp, _, _, _, _, _⟩
  rcases hR with ⟨hRs, hRp, _, _, _, _, _⟩
  simp [authorizedCheckSig, authorizedReconcile, checkSig,
    checkSigSetReady, checkSigCheckL, checkSigCheckR,
    checkSigSetResult, reconcilePermit, normalizePermit,
    hLs, hLp, hRs, hRp]
  constructor
  · cases l
    simp_all
  · cases r
    simp_all

private theorem authorizedDisappear_eq_of_neutral
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hL : ComparisonNeutral l.core) (hR : ComparisonNeutral r.core)
    (hpL : l.path0Crossed = false) (hpR : r.path0Crossed = false) :
    authorizedDisappear hpsi l r = (l, r) := by
  rcases hL with ⟨hLs, hLp, _, _, _, hLP, hLCarry⟩
  rcases hR with ⟨hRs, hRp, _, _, _, hRP, hRCarry⟩
  simp [authorizedDisappear, authorizedReconcile, disappear,
    reconcilePermit, normalizePermit, hLs, hLp, hLCarry,
    hRs, hRp]
  constructor
  · cases l
    simp_all
  · cases r
    simp_all

private theorem authorizedCompareSig_eq_of_neutral
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hL : ComparisonNeutral l.core) (_hR : ComparisonNeutral r.core)
    (hpL : l.path0Crossed = false) (_hpR : r.path0Crossed = false) :
    authorizedCompareSig hpsi l r = (l, r) := by
  rcases hL with ⟨hLs, hLp, hLp2, hLp4, hLp5, hLP, hLCarry⟩
  simp [authorizedCompareSig, compareSigInit, normalizePermit,
    hLp, hLp2, hLp4, hLp5, hLP, hLCarry]
  cases l with
  | mk core permit =>
      cases core
      simp_all

/-- Exact sanitized input boundary of the real CHECK stage.  Naming this
boundary prevents downstream provenance proofs from unfolding the entire
P-prime/GENSIG/CLEAN/ELIMINATE/SIGMOVE prefix merely to project one field. -/
def wallSweepPreCheckResetBeforeCheck
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l r
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  sanitizeAuthorizedPair hpsi beforeReset

/-- Exact output boundary of the real CHECK stage. -/
def wallSweepPreCheckResetAfterCheck
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let beforeCheck := wallSweepPreCheckResetBeforeCheck hpsi kappa l r
  authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2

/- Named one-step facts at variables.  The proofs below rewrite with these and
generalize the stage outputs instead of letting the elaborator unify a
stage-output fact against the composed prefix (LP-0157). -/
private theorem authorizedPPsiLeaderProbeWall_right_core
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedPPsiLeaderProbeWall hpsi l r).2.core =
      (pPsiLeaderProbeWall hpsi l.core r.core).2 :=
  rfl

private theorem wallSweepPreCheckResetBeforeCheck_eq
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    wallSweepPreCheckResetBeforeCheck hpsi kappa l r =
      sanitizeAuthorizedPair hpsi
        (preCheckResetWall (wallSweepAuthorizedBeforeCheck hpsi kappa l r).1
          (wallSweepAuthorizedBeforeCheck hpsi kappa l r).2) :=
  rfl

private theorem wallSweepPreCheckResetAfterCheck_eq
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    wallSweepPreCheckResetAfterCheck hpsi kappa l r =
      authorizedCheckSig hpsi
        (wallSweepPreCheckResetBeforeCheck hpsi kappa l r).1
        (wallSweepPreCheckResetBeforeCheck hpsi kappa l r).2 :=
  rfl

/-- The P-prime responder frame of an existing responder leader, stated on
the authorized stage output. -/
private theorem authorizedPPsiLeaderProbeWall_responder_frame_of_responder_leader
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    (authorizedPPsiLeaderProbeWall hpsi l r).2.core.leader = r.core.leader ∧
      (authorizedPPsiLeaderProbeWall hpsi l r).2.core.label = r.core.label := by
  have hppsi := pPsiLeaderProbeWall_responder_frame_of_responder_leader
    hpsi l.core r.core hrLeader
  rw [authorizedPPsiLeaderProbeWall_right_core]
  exact hppsi

/-- The saturated pre-CHECK prefix cannot remove an already-present responder
leader.  This field-local form deliberately avoids projecting the complete
`PeaceView` equality, which would force Lean to normalize the whole prefix
while inferring the projection type. -/
theorem wallSweepAuthorizedBeforeCheck_responder_leader_of_true
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    let out := wallSweepAuthorizedBeforeCheck hpsi kappa l r
    out.2.core.leader = true := by
  have hppsi := authorizedPPsiLeaderProbeWall_responder_frame_of_responder_leader
    hpsi l r hrLeader
  have hview := wallSweepAuthorizedBeforeCheck_peaceView_of_ppsi_frame
    hpsi kappa l r hppsi.1 hppsi.2
  show (wallSweepAuthorizedBeforeCheck hpsi kappa l r).2.core.leader = true
  revert hview
  generalize wallSweepAuthorizedBeforeCheck hpsi kappa l r = q
  intro hview
  exact (responderLeaderAndLabels_of_authorizedPeaceViewPair_eq
    hview).1.trans hrLeader

/-- An existing responder leader reaches SIGMOVE intact; the responder-leader
wall then clears both comparison carriers and both authorization permits. -/
theorem wallSweepAuthorizedBeforeCheck_neutral_of_responder_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    let q := wallSweepAuthorizedBeforeCheck hpsi kappa l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.path0Crossed = false ∧ q.2.path0Crossed = false := by
  rw [PPLLWallSweepStageFrames.wallSweepAuthorizedBeforeCheck_stages]
  have h0 : (authorizedPPsiLeaderProbeWall hpsi l r).2.core.leader = true :=
    (authorizedPPsiLeaderProbeWall_responder_frame_of_responder_leader
      hpsi l r hrLeader).1.trans hrLeader
  revert h0
  generalize authorizedPPsiLeaderProbeWall hpsi l r = q0
  intro h0
  have h1 : (authorizedGenSig hpsi kappa q0.1 q0.2).2.core.leader = true :=
    (congrArg (fun p : AgentState psi × AgentState psi => p.2.leader)
      (PPLLWallSweepStageFrames.authorizedReconcile_core_pair
        (genSigSaturated hpsi kappa) q0.1 q0.2)).trans
      ((congrArg Prod.snd (PPLLNoCheckBirthLeaderFrames.genSigSaturated_leaders
        hpsi kappa q0.1.core q0.2.core)).trans h0)
  revert h1
  generalize authorizedGenSig hpsi kappa q0.1 q0.2 = q1
  intro h1
  have h2 : (authorizedCleanSig hpsi q1.1 q1.2).2.core.leader = true :=
    (congrArg (fun p : AgentState psi × AgentState psi => p.2.leader)
      (PPLLWallSweepStageFrames.authorizedReconcile_core_pair
        (cleanSig hpsi) q1.1 q1.2)).trans
      ((PPLLVerify.cleanSig_leaders_eq hpsi q1.1.core q1.2.core).2.trans h1)
  revert h2
  generalize authorizedCleanSig hpsi q1.1 q1.2 = q2
  intro h2
  have h3 : (authorizedEliminateSig hpsi q2.1 q2.2).2.core.leader = true :=
    (congrArg (fun p : AgentState psi × AgentState psi => p.2.leader)
      (PPLLWallSweepStageFrames.authorizedReconcile_core_pair
        (eliminateSig hpsi) q2.1 q2.2)).trans
      ((PPLLVerify.eliminateSig_leaders_eq hpsi q2.1.core q2.2.core).2.trans h2)
  revert h3
  generalize authorizedEliminateSig hpsi q2.1 q2.2 = q3
  intro h3
  exact authorizedSigMoveLeaderWall_right_leader_kills
    hpsi q3.1 q3.2 h3

/-- The reset wall and terminal-equality sanitizer preserve the complete
physical view of the saturated pre-CHECK prefix around an existing responder
leader. -/
theorem wallSweepPreCheckResetBeforeCheck_peaceView_of_responder_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    authorizedPeaceViewPair
        (wallSweepPreCheckResetBeforeCheck hpsi kappa l r) =
      authorizedPeaceViewPair (l, r) := by
  have hppsi := authorizedPPsiLeaderProbeWall_responder_frame_of_responder_leader
    hpsi l r hrLeader
  have hview := wallSweepAuthorizedBeforeCheck_peaceView_of_ppsi_frame
    hpsi kappa l r hppsi.1 hppsi.2
  rw [wallSweepPreCheckResetBeforeCheck_eq]
  revert hview
  generalize wallSweepAuthorizedBeforeCheck hpsi kappa l r = q
  intro hview
  exact (sanitizePreCheckResetWall_peaceViewPair hpsi q).trans hview

/-- The same sanitized boundary retains the existing responder leader bit. -/
theorem wallSweepPreCheckResetBeforeCheck_responder_leader_of_true
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    let out := wallSweepPreCheckResetBeforeCheck hpsi kappa l r
    out.2.core.leader = true := by
  have h : (wallSweepAuthorizedBeforeCheck hpsi kappa l r).2.core.leader =
      true :=
    wallSweepAuthorizedBeforeCheck_responder_leader_of_true
      hpsi kappa l r hrLeader
  show (wallSweepPreCheckResetBeforeCheck hpsi kappa l r).2.core.leader = true
  rw [wallSweepPreCheckResetBeforeCheck_eq]
  revert h
  generalize wallSweepAuthorizedBeforeCheck hpsi kappa l r = q
  intro h
  exact (sanitizePreCheckResetWall_responder_leader_eq hpsi q).trans h

/-- Real CHECK frames the complete physical view of any authorized pair whose
responder is already a leader. -/
theorem authorizedCheckSig_peaceViewPair_of_responder_leader_true
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hrLeader : q.2.core.leader = true) :
    authorizedPeaceViewPair
        (authorizedCheckSig hpsi q.1 q.2) =
      authorizedPeaceViewPair q := by
  have hframe :
      (authorizedCheckSig hpsi q.1 q.2).2.core.leader =
        q.2.core.leader :=
    (PPLLVerify.checkSig_responder_leader_of_true
      hpsi q.1.core q.2.core hrLeader).trans hrLeader.symm
  exact authorizedCheckSig_peaceViewPair_of_responder_frame
    hpsi q.1 q.2 hframe

/-- If the input responder is already a leader, the complete repaired prefix
through real CHECK frames the five physical `PeaceView` fields at both
endpoints.  Naming the intermediate boundary keeps downstream migration
proofs from unfolding the saturated P-prime/GENSIG/CLEAN/ELIMINATE prefix. -/
theorem wallSweepPreCheckResetAfterCheck_peaceView_of_responder_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    authorizedPeaceViewPair
        (wallSweepPreCheckResetAfterCheck hpsi kappa l r) =
      authorizedPeaceViewPair (l, r) := by
  have hbefore := wallSweepPreCheckResetBeforeCheck_peaceView_of_responder_leader
      hpsi kappa l r hrLeader
  have hbeforeLeader :
      (wallSweepPreCheckResetBeforeCheck hpsi kappa l r).2.core.leader = true :=
    wallSweepPreCheckResetBeforeCheck_responder_leader_of_true
      hpsi kappa l r hrLeader
  rw [wallSweepPreCheckResetAfterCheck_eq]
  revert hbefore hbeforeLeader
  generalize wallSweepPreCheckResetBeforeCheck hpsi kappa l r = before
  intro hbefore hbeforeLeader
  exact (authorizedCheckSig_peaceViewPair_of_responder_leader_true
    hpsi before hbeforeLeader).trans hbefore

/-- The stages after the new deletion boundary through COMPARE. -/
def preCheckResetCheckTail
    (hpsi : psi > 0)
    (q0 : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let qR := preCheckResetWall q0.1 q0.2
  let q1 := sanitizeAuthorizedPair hpsi qR
  let q2 := authorizedCheckSig hpsi q1.1 q1.2
  let q3 := authorizedDisappear hpsi q2.1 q2.2
  authorizedCompareSig hpsi q3.1 q3.2

/-- Named ordinary prefix with the reset deletion inserted at the exact new
boundary immediately before terminal sanitation and real CHECK. -/
def wallSweepPreCheckResetBeforeSuppress
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let afterCheck := wallSweepPreCheckResetAfterCheck hpsi kappa l r
  let afterDisappear := authorizedDisappear hpsi
    afterCheck.1 afterCheck.2
  authorizedCompareSig hpsi afterDisappear.1 afterDisappear.2

/-- Named expansion of the corrected prefix.  Keeping this equality opaque to
downstream clients avoids unfolding the complete wall merely to project one
output field. -/
theorem wallSweepPreCheckResetBeforeSuppress_eq_checkTail
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    wallSweepPreCheckResetBeforeSuppress hpsi kappa l r =
      preCheckResetCheckTail hpsi
        (wallSweepAuthorizedBeforeCheck hpsi kappa l r) := by
  rfl

/-- The new prefix still frames reset and echo exactly. -/
theorem wallSweepPreCheckResetBeforeSuppress_resetEchoPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedResetEchoPair
      (wallSweepPreCheckResetBeforeSuppress hpsi kappa l r) =
      authorizedResetEchoPair (l, r) := by
  let q0 := wallSweepAuthorizedBeforeCheck hpsi kappa l r
  let qR := preCheckResetWall q0.1 q0.2
  let q1 := sanitizeAuthorizedPair hpsi qR
  let q2 := authorizedCheckSig hpsi q1.1 q1.2
  let q3 := authorizedDisappear hpsi q2.1 q2.2
  let q4 := authorizedCompareSig hpsi q3.1 q3.2
  have h0 := wallSweepAuthorizedBeforeCheck_resetEchoPair hpsi kappa l r
  have hR := preCheckResetWall_resetEchoPair q0.1 q0.2
  have h1 := sanitizeAuthorizedPair_resetEchoPair hpsi qR
  have h2 := authorizedCheckSig_resetEchoPair hpsi q1.1 q1.2
  have h3 := authorizedDisappear_resetEchoPair hpsi q2.1 q2.2
  have h4 := authorizedCompareSig_resetEchoPair hpsi q3.1 q3.2
  change authorizedResetEchoPair
    q4 = authorizedResetEchoPair (l, r)
  have h4' : authorizedResetEchoPair q4 = authorizedResetEchoPair q3 :=
    authorizedResetEchoPair_eq_trans h4 (authorizedResetEchoPair_eta q3)
  have h3' : authorizedResetEchoPair q3 = authorizedResetEchoPair q2 :=
    authorizedResetEchoPair_eq_trans h3 (authorizedResetEchoPair_eta q2)
  have h2' : authorizedResetEchoPair q2 = authorizedResetEchoPair q1 :=
    authorizedResetEchoPair_eq_trans h2 (authorizedResetEchoPair_eta q1)
  have h1' : authorizedResetEchoPair q1 = authorizedResetEchoPair qR := h1
  have hR' : authorizedResetEchoPair qR = authorizedResetEchoPair q0 :=
    authorizedResetEchoPair_eq_trans hR (authorizedResetEchoPair_eta q0)
  exact authorizedResetEchoPair_eq_trans h4'
    (authorizedResetEchoPair_eq_trans h3'
      (authorizedResetEchoPair_eq_trans h2'
        (authorizedResetEchoPair_eq_trans h1'
          (authorizedResetEchoPair_eq_trans hR' h0))))

private theorem initiator_reset_true_of_resetEchoPair_eq
    {before after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedResetEchoPair after = authorizedResetEchoPair before)
    (hreset : before.1.core.reset_cmd = true) :
    after.1.core.reset_cmd = true := by
  have hL := congrArg Prod.fst h
  have heq := congrArg Prod.fst hL
  change after.1.core.reset_cmd = before.1.core.reset_cmd at heq
  exact heq.trans hreset

private theorem neutral_check_disappear_compare_eq
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hL : ComparisonNeutral q.1.core)
    (hR : ComparisonNeutral q.2.core)
    (hpL : q.1.path0Crossed = false)
    (hpR : q.2.path0Crossed = false) :
    let q1 := sanitizeAuthorizedPair hpsi q
    let q2 := authorizedCheckSig hpsi q1.1 q1.2
    let q3 := authorizedDisappear hpsi q2.1 q2.2
    authorizedCompareSig hpsi q3.1 q3.2 = q := by
  have h1 := sanitizeAuthorizedPair_eq_of_neutral hpsi q hL hR
  have h2 := authorizedCheckSig_eq_of_neutral
    hpsi q.1 q.2 hL hR hpL hpR
  have h3 := authorizedDisappear_eq_of_neutral
    hpsi q.1 q.2 hL hR hpL hpR
  have h4 := authorizedCompareSig_eq_of_neutral
    hpsi q.1 q.2 hL hR hpL hpR
  simp [h1, h2, h3, h4]

/-- A neutral authorized pair remains neutral through the complete repaired
reset-wall/CHECK/DISAPPEAR/COMPARE tail. -/
theorem preCheckResetCheckTail_neutral_of_neutral
    (hpsi : psi > 0)
    (q0 : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hL : ComparisonNeutral q0.1.core)
    (hR : ComparisonNeutral q0.2.core)
    (hpL : q0.1.path0Crossed = false)
    (hpR : q0.2.path0Crossed = false) :
    let q := preCheckResetCheckTail hpsi q0
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.path0Crossed = false ∧ q.2.path0Crossed = false := by
  let qR := preCheckResetWall q0.1 q0.2
  have hreset := preCheckResetWall_neutral_of_neutral
    q0.1 q0.2 hL hR hpL hpR
  change ComparisonNeutral qR.1.core ∧ ComparisonNeutral qR.2.core ∧
    qR.1.path0Crossed = false ∧ qR.2.path0Crossed = false at hreset
  have htail := neutral_check_disappear_compare_eq hpsi qR
    hreset.1 hreset.2.1 hreset.2.2.1 hreset.2.2.2
  have heq : preCheckResetCheckTail hpsi q0 = qR := by
    change
      (let q1 := sanitizeAuthorizedPair hpsi qR
       let q2 := authorizedCheckSig hpsi q1.1 q1.2
       let q3 := authorizedDisappear hpsi q2.1 q2.2
       authorizedCompareSig hpsi q3.1 q3.2) = qR
    exact htail
  rw [heq]
  exact hreset

/-- An existing responder leader makes the complete repaired prefix through
COMPARE comparison-neutral at both endpoints. -/
theorem wallSweepPreCheckResetBeforeSuppress_neutral_of_responder_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    let q := wallSweepPreCheckResetBeforeSuppress hpsi kappa l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.path0Crossed = false ∧ q.2.path0Crossed = false := by
  rw [wallSweepPreCheckResetBeforeSuppress_eq_checkTail]
  have hraw := wallSweepAuthorizedBeforeCheck_neutral_of_responder_leader
    hpsi kappa l r hrLeader
  exact preCheckResetCheckTail_neutral_of_neutral hpsi
    (wallSweepAuthorizedBeforeCheck hpsi kappa l r)
    hraw.1 hraw.2.1 hraw.2.2.1 hraw.2.2.2

/-- Opaque two-field projection of the responder-leader pre-suppression
contract for consumers that do not need movement-permission fields. -/
theorem
    wallSweepPreCheckResetBeforeSuppress_both_neutral_of_responder_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    authorizedBothNeutral
      (wallSweepPreCheckResetBeforeSuppress hpsi kappa l r) := by
  have h :=
    wallSweepPreCheckResetBeforeSuppress_neutral_of_responder_leader
      hpsi kappa l r hrLeader
  exact ⟨h.1, h.2.1⟩

theorem preCheckResetCheckTail_eq_of_send
    (hpsi : psi > 0)
    (q0 : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hsend : q0.1.core.leader = true ∨ q0.1.core.reset_cmd = true) :
    preCheckResetCheckTail hpsi q0 = preCheckResetWall q0.1 q0.2 := by
  let qR := preCheckResetWall q0.1 q0.2
  have hR := preCheckResetWall_both_neutral_of_send q0.1 q0.2 hsend
  change ComparisonNeutral qR.1.core ∧ ComparisonNeutral qR.2.core ∧
    qR.1.path0Crossed = false ∧ qR.2.path0Crossed = false at hR
  change
    (let q1 := sanitizeAuthorizedPair hpsi qR
      let q2 := authorizedCheckSig hpsi q1.1 q1.2
      let q3 := authorizedDisappear hpsi q2.1 q2.2
      authorizedCompareSig hpsi q3.1 q3.2) = qR
  exact neutral_check_disappear_compare_eq hpsi qR
    hR.1 hR.2.1 hR.2.2.1 hR.2.2.2

private theorem neutralPermitPair_of_eq
    {before after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : after = before)
    (hbefore : ComparisonNeutral before.1.core ∧
      ComparisonNeutral before.2.core ∧
      before.1.path0Crossed = false ∧
      before.2.path0Crossed = false) :
    ComparisonNeutral after.1.core ∧ ComparisonNeutral after.2.core ∧
      after.1.path0Crossed = false ∧ after.2.path0Crossed = false := by
  rw [h]
  exact hbefore

/-- An existing initiator reset clears the two comparison endpoints before
CHECK; sanitation and the CHECK/DISAPPEAR/COMPARE prefix are then inert. -/
theorem wallSweepPreCheckResetBeforeSuppress_neutral_of_left_reset
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = true) :
    let q := wallSweepPreCheckResetBeforeSuppress hpsi kappa l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.path0Crossed = false ∧ q.2.path0Crossed = false := by
  let q0 := wallSweepAuthorizedBeforeCheck hpsi kappa l r
  have h0 := wallSweepAuthorizedBeforeCheck_resetEchoPair
    hpsi kappa l r
  have hq0Reset : q0.1.core.reset_cmd = true :=
    initiator_reset_true_of_resetEchoPair_eq h0 hlReset
  let qR := preCheckResetWall q0.1 q0.2
  have hR := preCheckResetWall_both_neutral_of_send
    q0.1 q0.2 (.inr hq0Reset)
  change ComparisonNeutral qR.1.core ∧ ComparisonNeutral qR.2.core ∧
    qR.1.path0Crossed = false ∧ qR.2.path0Crossed = false at hR
  have hout := preCheckResetCheckTail_eq_of_send
    hpsi q0 (.inr hq0Reset)
  have hnamed : wallSweepPreCheckResetBeforeSuppress hpsi kappa l r = qR :=
    (show wallSweepPreCheckResetBeforeSuppress hpsi kappa l r =
      preCheckResetCheckTail hpsi q0 from rfl).trans hout
  exact neutralPermitPair_of_eq hnamed hR

/-- Clearing comparison material preserves every declared numeric range. -/
theorem clearAuthorizedComparison_inProtocolDomain
    (u : AuthorizedAgentState psi) (hu : u.core.inProtocolDomain kappa) :
    (clearAuthorizedComparison u).core.inProtocolDomain kappa :=
  clearComparisonSignal_inProtocolDomain u.core hu

/-- The pair wall is numeric-domain closed. -/
theorem preCheckResetWall_inProtocolDomain
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := preCheckResetWall l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  unfold preCheckResetWall
  dsimp only
  split
  · constructor
    · exact clearAuthorizedComparison_inProtocolDomain l hl
    · split
      · exact clearAuthorizedComparison_inProtocolDomain r hr
      · exact hr
  · constructor
    · exact hl
    · split
      · exact clearAuthorizedComparison_inProtocolDomain r hr
      · exact hr

/-- Complete authorized wall transition with the source-prose reset deletion
inserted after SIGMOVE and immediately before terminal sanitation and CHECK. -/
def wallSweepPreCheckResetAuthorizedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then
    authorizedEliminateSig hpsi l0 r0
  else if deletionActive l0 then
    (l0, r0)
  else
    let beforeCheck := wallSweepPreCheckResetBeforeCheck
      hpsi kappa l0 r0
    let afterCheck := wallSweepPreCheckResetAfterCheck
      hpsi kappa l0 r0
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    markLeaderBirth born
      (wallSweepAuthorizedAfterCheckSuffix hpsi afterCheck.1 afterCheck.2)

/-- The active-responder priority branch, exposed without unfolding the
ordinary transition suffix in downstream proofs. -/
theorem wallSweepPreCheckResetAuthorizedTransition_eq_eliminate_of_active
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hr : deletionActive (normalizeDeletion r) = true) :
    wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
      authorizedEliminateSig hpsi (normalizeDeletion l)
        (normalizeDeletion r) := by
  simp [wallSweepPreCheckResetAuthorizedTransition, hr]

/-- The active-initiator priority branch, exposed without unfolding the
ordinary transition suffix in downstream proofs. -/
theorem wallSweepPreCheckResetAuthorizedTransition_eq_pair_of_left_active
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hr : deletionActive (normalizeDeletion r) = false)
    (hl : deletionActive (normalizeDeletion l) = true) :
    wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
      (normalizeDeletion l, normalizeDeletion r) := by
  simp [wallSweepPreCheckResetAuthorizedTransition, hr, hl]

/-- The sanitized real-CHECK output of the ordinary prefix is in the numeric
domain.  Stage outputs are generalized one at a time (LP-0157). -/
private theorem wallSweepPreCheckResetAfterCheck_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    (wallSweepPreCheckResetAfterCheck hpsi kappa l r).1.core.inProtocolDomain
        kappa ∧
      (wallSweepPreCheckResetAfterCheck hpsi kappa l r).2.core.inProtocolDomain
        kappa := by
  have h0 := wallSweepAuthorizedBeforeCheck_inProtocolDomain hpsi kappa l r hl hr
  rw [wallSweepPreCheckResetAfterCheck_eq, wallSweepPreCheckResetBeforeCheck_eq]
  revert h0
  generalize wallSweepAuthorizedBeforeCheck hpsi kappa l r = q0
  intro h0
  have hR := preCheckResetWall_inProtocolDomain q0.1 q0.2 h0.1 h0.2
  revert hR
  generalize preCheckResetWall q0.1 q0.2 = qR
  intro hR
  have h1 : (sanitizeAuthorizedPair hpsi qR).1.core.inProtocolDomain kappa ∧
      (sanitizeAuthorizedPair hpsi qR).2.core.inProtocolDomain kappa :=
    ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi qR.1 hR.1,
      sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi qR.2 hR.2⟩
  revert h1
  generalize sanitizeAuthorizedPair hpsi qR = q1
  intro h1
  exact authorizedReconcile_inProtocolDomain (checkSig hpsi) q1.1 q1.2
    (checkSig_inProtocolDomain hpsi q1.1.core q1.2.core h1.1 h1.2)

attribute [local irreducible]
  wallSweepAuthorizedBeforeCheck wallSweepAuthorizedAfterCheckSuffix

/-- The pre-CHECK reset repair preserves the finite numeric domain without
adding a state component. -/
theorem wallSweepPreCheckResetAuthorizedTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧ q.2.core.inProtocolDomain kappa := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain kappa at hl0
  change r0.core.inProtocolDomain kappa at hr0
  unfold wallSweepPreCheckResetAuthorizedTransition
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain
      (eliminateSig hpsi) l0 r0
      (eliminateSig_inProtocolDomain hpsi l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · have h2 := wallSweepPreCheckResetAfterCheck_inProtocolDomain
        hpsi kappa l0 r0 hl0 hr0
      exact markLeaderBirth_inProtocolDomain _ _
        (wallSweepAuthorizedAfterCheckSuffix_inProtocolDomain hpsi _ _ h2.1 h2.2)

attribute [local semireducible]
  wallSweepAuthorizedBeforeCheck wallSweepAuthorizedAfterCheckSuffix

/-! ## Exact finite carrier -/

/-- Finite reification on the unchanged authorization carrier. -/
def wallSweepPreCheckResetBoundedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa :=
  let q := wallSweepPreCheckResetAuthorizedTransition
    hpsi kappa l.erase r.erase
  let hq := wallSweepPreCheckResetAuthorizedTransition_inProtocolDomain
    hpsi kappa l.erase r.erase
      l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

/-- Bounded erasure is exact. -/
theorem erase_wallSweepPreCheckResetBoundedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := wallSweepPreCheckResetBoundedTransition hpsi kappa l r
    (q.1.erase, q.2.erase) =
      wallSweepPreCheckResetAuthorizedTransition
        hpsi kappa l.erase r.erase := by
  let q := wallSweepPreCheckResetAuthorizedTransition
    hpsi kappa l.erase r.erase
  let hq := wallSweepPreCheckResetAuthorizedTransition_inProtocolDomain
    hpsi kappa l.erase r.erase
      l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  change (⟨(BoundedAgentState.ofDomain q.1.core hq.1).erase,
      q.1.path0Crossed⟩,
    ⟨(BoundedAgentState.ofDomain q.2.core hq.2).erase,
      q.2.path0Crossed⟩) = (q.1, q.2)
  rw [BoundedAgentState.erase_ofDomain, BoundedAgentState.erase_ofDomain]

/-- Path-stall/deletion expiry on the existing finite state type. -/
def wallSweepPreCheckResetPathStallTransition
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
  let q := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r.stall⟩
  (deletionPriorityExpireOne tau l lOut,
    deletionPriorityExpireOne tau r rOut)

/-! ## Rooted leader-entry signal-sink repair -/

/-- Existing post-CHECK stages with only Algorithm 15 replaced by the
separately named responder-leader signal sink. -/
def wallSweepLeaderSinkAfterCheckSuffix
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSig hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  authorizedPostSuppressLeaderSink hpsi q2.1 q2.2

/-- The leader-sink post-CHECK suffix is closed on the existing numeric
carrier. -/
theorem wallSweepLeaderSinkAfterCheckSuffix_inProtocolDomain
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := wallSweepLeaderSinkAfterCheckSuffix hpsi l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  let q0 := authorizedDisappear hpsi l r
  have h0 := authorizedReconcile_inProtocolDomain
    (disappear hpsi) l r
    (disappear_inProtocolDomain hpsi l.core r.core hl hr)
  let q1 := authorizedCompareSig hpsi q0.1 q0.2
  have h1 := authorizedCompareSig_inProtocolDomain
    hpsi q0.1 q0.2 h0.1 h0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain
    (suppressSigResetKill hpsi) q1.1 q1.2
    (suppressSigResetKill_inProtocolDomain
      hpsi q1.1.core q1.2.core h1.1 h1.2)
  exact authorizedPostSuppressLeaderSink_inProtocolDomain
    hpsi q2.1 q2.2 h2.1 h2.2

/-- Complete pre-CHECK reset transition with the rooted leader-entry signal
sink in its ordinary Algorithm-15 suffix.  Deletion priority, CHECK birth,
and every other stage are unchanged. -/
def wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then
    authorizedEliminateSig hpsi l0 r0
  else if deletionActive l0 then
    (l0, r0)
  else
    let beforeCheck := wallSweepPreCheckResetBeforeCheck
      hpsi kappa l0 r0
    let afterCheck := wallSweepPreCheckResetAfterCheck
      hpsi kappa l0 r0
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    markLeaderBirth born
      (wallSweepLeaderSinkAfterCheckSuffix
        hpsi afterCheck.1 afterCheck.2)

/-- The complete rooted leader-sink transition remains in the unchanged
finite numeric domain. -/
theorem wallSweepPreCheckResetLeaderSinkAuthorizedTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain kappa at hl0
  change r0.core.inProtocolDomain kappa at hr0
  unfold wallSweepPreCheckResetLeaderSinkAuthorizedTransition
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain
      (eliminateSig hpsi) l0 r0
      (eliminateSig_inProtocolDomain hpsi l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · have h2 := wallSweepPreCheckResetAfterCheck_inProtocolDomain
        hpsi kappa l0 r0 hl0 hr0
      exact markLeaderBirth_inProtocolDomain _ _
        (wallSweepLeaderSinkAfterCheckSuffix_inProtocolDomain hpsi _ _ h2.1 h2.2)

/-- Finite reification of the rooted leader-sink transition on the unchanged
authorization carrier. -/
def wallSweepPreCheckResetLeaderSinkBoundedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa :=
  let q := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l.erase r.erase
  let hq :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_inProtocolDomain
      hpsi kappa l.erase r.erase
        l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

/-- Bounded erasure is exact for the rooted leader-sink transition. -/
theorem erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := wallSweepPreCheckResetLeaderSinkBoundedTransition
      hpsi kappa l r
    (q.1.erase, q.2.erase) =
      wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l.erase r.erase := by
  let q := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l.erase r.erase
  let hq :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_inProtocolDomain
      hpsi kappa l.erase r.erase
        l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  change (⟨(BoundedAgentState.ofDomain q.1.core hq.1).erase,
      q.1.path0Crossed⟩,
    ⟨(BoundedAgentState.ofDomain q.2.core hq.2).erase,
      q.2.path0Crossed⟩) = (q.1, q.2)
  rw [BoundedAgentState.erase_ofDomain, BoundedAgentState.erase_ofDomain]

/-- Path-stall/deletion expiry for the rooted leader-sink transition. -/
def wallSweepPreCheckResetLeaderSinkPathStallTransition
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
  let q := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r.stall⟩
  (deletionPriorityExpireOne tau l lOut,
    deletionPriorityExpireOne tau r rOut)

/-- The rooted leader-sink path-stall transition is bounded reification
followed by the same two pointwise expiry stages as the established repair. -/
theorem wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
      hpsi kappa l.core r.core
    let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
    let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
    wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r =
      (deletionPriorityExpireOne tau l lBase,
        deletionPriorityExpireOne tau r rBase) := by
  rfl

/-! ## Reset-aware P-prime integration -/

/-- Exact sanitized CHECK input when the reset-aware P-prime probe guard is
used at the first ordinary-branch stage.  The existing pre-CHECK deletion wall
and every later stage are unchanged. -/
def wallSweepResetProbePreCheckResetBeforeCheck
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let beforeRaw := wallSweepResetProbeAuthorizedBeforeCheck
    hpsi kappa l r
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  sanitizeAuthorizedPair hpsi beforeReset

/-- Exact real-CHECK output of the reset-aware ordinary prefix. -/
def wallSweepResetProbePreCheckResetAfterCheck
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let beforeCheck := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l r
  authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2

private theorem wallSweepResetProbePreCheckResetBeforeCheck_eq
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r =
      sanitizeAuthorizedPair hpsi
        (preCheckResetWall
          (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r).1
          (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r).2) :=
  rfl

private theorem wallSweepResetProbePreCheckResetAfterCheck_eq
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi) :
    wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r =
      authorizedCheckSig hpsi
        (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r).1
        (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r).2 :=
  rfl

private theorem wallSweepResetProbePreCheckResetAfterCheck_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa) (hr : r.core.inProtocolDomain kappa) :
    (wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r).1.core.inProtocolDomain
        kappa ∧
      (wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r).2.core.inProtocolDomain
        kappa := by
  have h0 := wallSweepResetProbeAuthorizedBeforeCheck_inProtocolDomain
    hpsi kappa l r hl hr
  rw [wallSweepResetProbePreCheckResetAfterCheck_eq,
    wallSweepResetProbePreCheckResetBeforeCheck_eq]
  revert h0
  generalize wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r = q0
  intro h0
  have hR := preCheckResetWall_inProtocolDomain q0.1 q0.2 h0.1 h0.2
  revert hR
  generalize preCheckResetWall q0.1 q0.2 = qR
  intro hR
  have h1 : (sanitizeAuthorizedPair hpsi qR).1.core.inProtocolDomain kappa ∧
      (sanitizeAuthorizedPair hpsi qR).2.core.inProtocolDomain kappa :=
    ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi qR.1 hR.1,
      sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi qR.2 hR.2⟩
  revert h1
  generalize sanitizeAuthorizedPair hpsi qR = q1
  intro h1
  exact authorizedReconcile_inProtocolDomain (checkSig hpsi) q1.1 q1.2
    (checkSig_inProtocolDomain hpsi q1.1.core q1.2.core h1.1 h1.2)

/-- Complete finite-stage repair with the reset-aware P-prime guard, the
pre-CHECK reset deletion, and the rooted Algorithm-15 leader sink in one
ordinary branch.  Deletion-priority branches remain exactly the established
ones. -/
def wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then
    authorizedEliminateSig hpsi l0 r0
  else if deletionActive l0 then
    (l0, r0)
  else
    let beforeCheck := wallSweepResetProbePreCheckResetBeforeCheck
      hpsi kappa l0 r0
    let afterCheck := wallSweepResetProbePreCheckResetAfterCheck
      hpsi kappa l0 r0
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    markLeaderBirth born
      (wallSweepLeaderSinkAfterCheckSuffix
        hpsi afterCheck.1 afterCheck.2)

/-- The integrated reset-aware transition is closed on the unchanged finite
numeric domain. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain kappa at hl0
  change r0.core.inProtocolDomain kappa at hr0
  unfold wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain
      (eliminateSig hpsi) l0 r0
      (eliminateSig_inProtocolDomain hpsi l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · have h2 := wallSweepResetProbePreCheckResetAfterCheck_inProtocolDomain
        hpsi kappa l0 r0 hl0 hr0
      exact markLeaderBirth_inProtocolDomain _ _
        (wallSweepLeaderSinkAfterCheckSuffix_inProtocolDomain hpsi _ _ h2.1 h2.2)

/-- Finite reification of the integrated reset-aware transition. -/
def wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa :=
  let q := wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l.erase r.erase
  let hq :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition_inProtocolDomain
      hpsi kappa l.erase r.erase
        l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

/-- Bounded erasure is exact for the integrated reset-aware transition. -/
theorem erase_wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
      hpsi kappa l r
    (q.1.erase, q.2.erase) =
      wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l.erase r.erase := by
  let q := wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l.erase r.erase
  let hq :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition_inProtocolDomain
      hpsi kappa l.erase r.erase
        l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  change (⟨(BoundedAgentState.ofDomain q.1.core hq.1).erase,
      q.1.path0Crossed⟩,
    ⟨(BoundedAgentState.ofDomain q.2.core hq.2).erase,
      q.2.path0Crossed⟩) = (q.1, q.2)
  rw [BoundedAgentState.erase_ofDomain, BoundedAgentState.erase_ofDomain]

/-- Path-stall/deletion expiry wrapper for the integrated reset-aware
transition. -/
def wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
  let q := wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lOut : ExpiringAgentState psi kappa tau := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState psi kappa tau := ⟨q.2, r.stall⟩
  (deletionPriorityExpireOne tau l lOut,
    deletionPriorityExpireOne tau r rOut)

/-- The integrated reset-aware path-stall transition is the same bounded
reification followed by the established pointwise expiry stages. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_expiryStages
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    let bounded := wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
      hpsi kappa l.core r.core
    let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
    let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r =
      (deletionPriorityExpireOne tau l lBase,
        deletionPriorityExpireOne tau r rBase) := by
  rfl

/-! ## Complete reset handoff -/

/-- The exact boundary after repaired Algorithm 14 in the pre-CHECK-reset
variant.  Naming this boundary keeps the subsequent handoff proof aligned with
the source stage decomposition. -/
def wallSweepPreCheckResetNormalAfterSuppress
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  authorizedReconcile (suppressSigResetKill hpsi) pre.1 pre.2

/-- Exact input boundary of the final gated WRITE in the rooted leader-sink
tail.  The boundary is named so provenance statements do not unfold repaired
Algorithm 14 or Algorithm 15 merely to inspect one endpoint. -/
def wallSweepPreCheckResetLeaderSinkBeforeWrite
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let afterSuppress :=
    wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi)
    afterSuppress.1 afterSuppress.2

/-- Complete ordinary branch after the new pre-CHECK prefix: repaired
Algorithm 14 is followed by no-collision Algorithm 15 and gated WRITE. -/
def wallSweepPreCheckResetNormalTail
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  authorizedPostSuppress hpsi after.1 after.2

/-- Ordinary pre-CHECK-reset tail with only Algorithm 15 replaced by the
rooted responder-leader signal sink. -/
def wallSweepPreCheckResetLeaderSinkNormalTail
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  authorizedPostSuppressLeaderSink hpsi after.1 after.2

private theorem normalizeDeletion_reset_eq
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.reset_cmd = u.core.reset_cmd := by
  unfold normalizeDeletion
  split <;> rfl

/-- With no initiator reset, the integrated reset-aware CHECK input is
exactly the established pre-CHECK-reset boundary. -/
theorem wallSweepResetProbePreCheckResetBeforeCheck_eq_of_no_reset
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = false) :
    wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r =
      wallSweepPreCheckResetBeforeCheck hpsi kappa l r := by
  unfold wallSweepResetProbePreCheckResetBeforeCheck
    wallSweepPreCheckResetBeforeCheck
  rw [wallSweepResetProbeAuthorizedBeforeCheck_eq_of_no_reset
    hpsi kappa l r hlReset]

/-- The real CHECK output is likewise exactly unchanged on reset-free
initiator edges. -/
theorem wallSweepResetProbePreCheckResetAfterCheck_eq_of_no_reset
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = false) :
    wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r =
      wallSweepPreCheckResetAfterCheck hpsi kappa l r := by
  unfold wallSweepResetProbePreCheckResetAfterCheck
    wallSweepPreCheckResetAfterCheck
  rw [wallSweepResetProbePreCheckResetBeforeCheck_eq_of_no_reset
    hpsi kappa l r hlReset]

/-- The reset-aware and rooted sanitized CHECK inputs agree exactly when the
input responder is already a leader.  Both P-prime walls clear that leader's
probe before the common prefix continues. -/
theorem wallSweepResetProbePreCheckResetBeforeCheck_eq_of_right_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r =
      wallSweepPreCheckResetBeforeCheck hpsi kappa l r := by
  unfold wallSweepResetProbePreCheckResetBeforeCheck
    wallSweepPreCheckResetBeforeCheck
  rw [wallSweepResetProbeAuthorizedBeforeCheck_eq_of_right_leader
    hpsi kappa l r hrLeader]

/-- Real CHECK likewise sees identical inputs in the responder-leader case. -/
theorem wallSweepResetProbePreCheckResetAfterCheck_eq_of_right_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r =
      wallSweepPreCheckResetAfterCheck hpsi kappa l r := by
  unfold wallSweepResetProbePreCheckResetAfterCheck
    wallSweepPreCheckResetAfterCheck
  rw [wallSweepResetProbePreCheckResetBeforeCheck_eq_of_right_leader
    hpsi kappa l r hrLeader]

/-- The reset-aware and rooted sanitized CHECK inputs agree exactly when the
input initiator is already a leader. -/
theorem wallSweepResetProbePreCheckResetBeforeCheck_eq_of_left_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true) :
    wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r =
      wallSweepPreCheckResetBeforeCheck hpsi kappa l r := by
  unfold wallSweepResetProbePreCheckResetBeforeCheck
    wallSweepPreCheckResetBeforeCheck
  rw [wallSweepResetProbeAuthorizedBeforeCheck_eq_of_left_leader
    hpsi kappa l r hlLeader]

/-- Real CHECK likewise sees identical inputs in the initiator-leader case. -/
theorem wallSweepResetProbePreCheckResetAfterCheck_eq_of_left_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true) :
    wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r =
      wallSweepPreCheckResetAfterCheck hpsi kappa l r := by
  unfold wallSweepResetProbePreCheckResetAfterCheck
    wallSweepPreCheckResetAfterCheck
  rw [wallSweepResetProbePreCheckResetBeforeCheck_eq_of_left_leader
    hpsi kappa l r hlLeader]

/-- On every edge whose input initiator carries no reset, the complete
integrated transition is exactly the established rooted leader-sink
transition.  Thus the first-birth simulation is retained without a second
semantic model. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition_eq_of_no_reset
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = false) :
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r =
      wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0Reset : l0.core.reset_cmd = false :=
    (normalizeDeletion_reset_eq l).trans hlReset
  unfold wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
  dsimp only
  rw [wallSweepResetProbePreCheckResetBeforeCheck_eq_of_no_reset
      hpsi kappa l0 r0 hl0Reset,
    wallSweepResetProbePreCheckResetAfterCheck_eq_of_no_reset
      hpsi kappa l0 r0 hl0Reset]

/-- On a closing edge whose responder is the existing leader, the integrated
reset-aware transition is exactly the established rooted leader-sink
transition, even though the follower initiator still carries reset. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition_eq_of_right_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r =
      wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hr0Leader : r0.core.leader = true := by
    change (normalizeDeletion r).core.leader = true
    unfold normalizeDeletion
    split <;> exact hrLeader
  unfold wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
  dsimp only
  rw [wallSweepResetProbePreCheckResetBeforeCheck_eq_of_right_leader
      hpsi kappa l0 r0 hr0Leader,
    wallSweepResetProbePreCheckResetAfterCheck_eq_of_right_leader
      hpsi kappa l0 r0 hr0Leader]

/-- On an edge initiated by the existing leader, the integrated reset-aware
transition is exactly the rooted leader-sink transition, independently of the
leader's reset bit. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition_eq_of_left_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true) :
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r =
      wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0Leader : l0.core.leader = true := by
    change (normalizeDeletion l).core.leader = true
    unfold normalizeDeletion
    split <;> exact hlLeader
  unfold wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
  dsimp only
  rw [wallSweepResetProbePreCheckResetBeforeCheck_eq_of_left_leader
      hpsi kappa l0 r0 hl0Leader,
    wallSweepResetProbePreCheckResetAfterCheck_eq_of_left_leader
      hpsi kappa l0 r0 hl0Leader]

private theorem normalizeDeletion_echo_eq
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.echo = u.core.echo := by
  unfold normalizeDeletion
  split <;> rfl

private theorem responder_echo_false_of_resetEchoPair_eq
    {before after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedResetEchoPair after = authorizedResetEchoPair before)
    (hecho : before.2.core.echo = false) :
    after.2.core.echo = false := by
  have hR := congrArg Prod.snd h
  have heq := congrArg Prod.snd hR
  change after.2.core.echo = before.2.core.echo at heq
  exact heq.trans hecho

private theorem markComparisonForDeletion_eq_of_neutral
    (u : AuthorizedAgentState psi) (h : ComparisonNeutral u.core) :
    markComparisonForDeletion u = u := by
  simp [markComparisonForDeletion, h.2.1]

theorem markLeaderBirth_eq_of_neutral
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hL : ComparisonNeutral q.1.core)
    (hR : ComparisonNeutral q.2.core) :
    markLeaderBirth born q = q := by
  unfold markLeaderBirth
  split
  · rw [markComparisonForDeletion_eq_of_neutral q.1 hL,
      markComparisonForDeletion_eq_of_neutral q.2 hR]
  · rfl

/-- The comparison-neutral reset-token state passed from one clockwise edge to
the next. -/
def ResetHandoff (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    Prop :=
  ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
    q.1.core.reset_cmd = false ∧ q.2.core.reset_cmd = true

private theorem authorizedReconcile_resetHandoff_of_raw
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hraw :
      let q := f l.core r.core
      ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 ∧
        q.1.reset_cmd = false ∧ q.2.reset_cmd = true) :
    ResetHandoff (authorizedReconcile f l r) := by
  exact hraw

/-- The named post-suppression boundary exposes exactly the repaired
Algorithm-14 reconciliation. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
    wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r =
      authorizedReconcile (suppressSigResetKill hpsi) pre.1 pre.2 := by
  rfl

private theorem authorizedReconcile_both_neutral_of_raw
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hraw : ComparisonNeutral (f l.core r.core).1 ∧
      ComparisonNeutral (f l.core r.core).2) :
    authorizedBothNeutral (authorizedReconcile f l r) := by
  exact hraw

private theorem normalizeDeletion_leader_eq
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion
  split <;> rfl

theorem afterSuppress_neutral_of_eq
    (hpsi : psi > 0)
    {pre out : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hpre : authorizedBothNeutral pre)
    (hout : out = authorizedReconcile
      (suppressSigResetKill hpsi) pre.1 pre.2) :
    authorizedBothNeutral out := by
  have hraw := suppressSigResetKill_neutral_of_neutral
    hpsi pre.1.core pre.2.core hpre.1 hpre.2
  exact bothNeutral_of_authorizedPair_eq hout
    (authorizedReconcile_both_neutral_of_raw
      (suppressSigResetKill hpsi) pre.1 pre.2 hraw)

/-- An existing responder leader makes the saturated pre-CHECK prefix neutral;
repaired suppression therefore leaves both authorized endpoints comparison
neutral. -/
theorem
    wallSweepPreCheckResetNormalAfterSuppress_neutral_of_responder_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    authorizedBothNeutral
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  have hr0Leader : r0.core.leader = true :=
    (normalizeDeletion_leader_eq r).trans hrLeader
  have hpre :=
    wallSweepPreCheckResetBeforeSuppress_both_neutral_of_responder_leader
      hpsi kappa l0 r0 hr0Leader
  exact afterSuppress_neutral_of_eq hpsi
    (pre := pre)
    (out := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r)
    hpre
    (wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
      hpsi kappa l r)

/-- The rooted Algorithm-15/WRITE suffix preserves the responder-leader
neutrality established by the repaired pre-CHECK prefix. -/
theorem
    wallSweepPreCheckResetLeaderSinkNormalTail_neutral_of_responder_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    authorizedBothNeutral
      (wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r) := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hafter :=
    wallSweepPreCheckResetNormalAfterSuppress_neutral_of_responder_leader
      hpsi kappa l r hrLeader
  change authorizedBothNeutral
    (authorizedPostSuppressLeaderSink hpsi after.1 after.2)
  exact authorizedPostSuppressLeaderSink_neutral
    hpsi after.1 after.2 hafter.1 hafter.2

/-- Repaired Algorithm 14 moves an existing initiator reset after the earlier
comparison deletion has made CHECK harmless. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_reset_handoff
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = true)
    (hrEcho : r.core.echo = false) :
    ResetHandoff
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0Reset : l0.core.reset_cmd = true :=
    (normalizeDeletion_reset_eq l).trans hlReset
  have hr0Echo : r0.core.echo = false :=
    (normalizeDeletion_echo_eq r).trans hrEcho
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  have hpreFrame := wallSweepPreCheckResetBeforeSuppress_resetEchoPair
    hpsi kappa l0 r0
  have hpreReset : pre.1.core.reset_cmd = true :=
    initiator_reset_true_of_resetEchoPair_eq hpreFrame hl0Reset
  have hpreEcho : pre.2.core.echo = false :=
    responder_echo_false_of_resetEchoPair_eq hpreFrame hr0Echo
  have hraw := suppressSigResetKill_handoff
    hpsi pre.1.core pre.2.core hpreReset hpreEcho
  have hauth := authorizedReconcile_resetHandoff_of_raw
    (suppressSigResetKill hpsi) pre.1 pre.2 hraw
  rw [wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile]
  exact hauth

/-- The named normal tail preserves the complete repaired reset handoff through
Algorithm 15 and the gated WRITE stage. -/
theorem wallSweepPreCheckResetNormalTail_reset_handoff
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = true)
    (hrEcho : r.core.echo = false) :
    let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
    ComparisonNeutral tail.1.core ∧ ComparisonNeutral tail.2.core ∧
      tail.1.core.reset_cmd = false ∧
      tail.2.core.reset_cmd = true := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hafter := wallSweepPreCheckResetNormalAfterSuppress_reset_handoff
    hpsi kappa l r hlReset hrEcho
  change ComparisonNeutral after.1.core ∧ ComparisonNeutral after.2.core ∧
    after.1.core.reset_cmd = false ∧ after.2.core.reset_cmd = true at hafter
  have hpost := postSuppress_normalReset_handoff
    hpsi after.1 after.2 hafter.1 hafter.2.1
  let tail := authorizedPostSuppress hpsi after.1 after.2
  change ComparisonNeutral tail.1.core ∧ ComparisonNeutral tail.2.core ∧
    tail.1.core.reset_cmd = false ∧ tail.2.core.reset_cmd = true
  exact ⟨hpost.1, hpost.2.1,
    hpost.2.2.1.trans hafter.2.2.1,
    hpost.2.2.2.1.trans hafter.2.2.2⟩

/-- The named normal tail is definitionally the existing post-CHECK suffix on
the actual CHECK output of the new pre-CHECK reset wall. -/
theorem wallSweepPreCheckResetNormalTail_eq_afterCheckSuffix
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let afterCheck := wallSweepPreCheckResetAfterCheck hpsi kappa l0 r0
    wallSweepPreCheckResetNormalTail hpsi kappa l r =
      wallSweepAuthorizedAfterCheckSuffix hpsi afterCheck.1 afterCheck.2 := by
  rfl

/-- The rooted leader-sink normal tail is definitionally the corresponding
post-CHECK suffix on the actual pre-CHECK-reset output. -/
theorem wallSweepPreCheckResetLeaderSinkNormalTail_eq_afterCheckSuffix
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let afterCheck := wallSweepPreCheckResetAfterCheck hpsi kappa l0 r0
    wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r =
      wallSweepLeaderSinkAfterCheckSuffix
        hpsi afterCheck.1 afterCheck.2 := by
  rfl

/-- Priority openness exposes the ordinary branch with the actual repaired
CHECK output, without unfolding its internal algorithms. -/
theorem wallSweepPreCheckResetAuthorizedTransition_eq_normal_of_priority_open
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let beforeCheck := wallSweepPreCheckResetBeforeCheck hpsi kappa l0 r0
    let afterCheck := wallSweepPreCheckResetAfterCheck hpsi kappa l0 r0
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
      markLeaderBirth born
        (wallSweepAuthorizedAfterCheckSuffix hpsi afterCheck.1 afterCheck.2) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  change deletionActive l0 = false ∧ deletionActive r0 = false at hopen
  unfold wallSweepPreCheckResetAuthorizedTransition
  dsimp only
  split
  · rename_i hdel
    rw [hopen.2] at hdel
    contradiction
  · split
    · rename_i hdel
      rw [hopen.1] at hdel
      contradiction
    · rfl

/-- Priority openness selects exactly the marked new normal tail. -/
theorem wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let beforeCheck := wallSweepPreCheckResetBeforeCheck hpsi kappa l0 r0
    let afterCheck := wallSweepPreCheckResetAfterCheck hpsi kappa l0 r0
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
      markLeaderBirth born
        (wallSweepPreCheckResetNormalTail hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeCheck := wallSweepPreCheckResetBeforeCheck hpsi kappa l0 r0
  let afterCheck := wallSweepPreCheckResetAfterCheck hpsi kappa l0 r0
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have hnormal :=
    wallSweepPreCheckResetAuthorizedTransition_eq_normal_of_priority_open
      hpsi kappa l r hopen
  have htail := wallSweepPreCheckResetNormalTail_eq_afterCheckSuffix
    hpsi kappa l r
  change wallSweepPreCheckResetNormalTail hpsi kappa l r =
    wallSweepAuthorizedAfterCheckSuffix hpsi afterCheck.1 afterCheck.2 at htail
  exact hnormal.trans (congrArg (markLeaderBirth born) htail.symm)

/-- Priority openness selects exactly the marked rooted leader-sink normal
tail. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let beforeCheck := wallSweepPreCheckResetBeforeCheck hpsi kappa l0 r0
    let afterCheck := wallSweepPreCheckResetAfterCheck hpsi kappa l0 r0
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r =
      markLeaderBirth born
        (wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeCheck := wallSweepPreCheckResetBeforeCheck hpsi kappa l0 r0
  let afterCheck := wallSweepPreCheckResetAfterCheck hpsi kappa l0 r0
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  change deletionActive l0 = false ∧ deletionActive r0 = false at hopen
  have htail :=
    wallSweepPreCheckResetLeaderSinkNormalTail_eq_afterCheckSuffix
      hpsi kappa l r
  change wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r =
    wallSweepLeaderSinkAfterCheckSuffix
      hpsi afterCheck.1 afterCheck.2 at htail
  have hrInactive : ¬deletionActive r0 = true := by
    rw [hopen.2]
    decide
  have hlInactive : ¬deletionActive l0 = true := by
    rw [hopen.1]
    decide
  unfold wallSweepPreCheckResetLeaderSinkAuthorizedTransition
  dsimp only
  rw [if_neg hrInactive, if_neg hlInactive]
  exact congrArg (markLeaderBirth born) htail.symm

/-- The complete priority-open authorized repair realizes the handoff; birth
marking is inert because the normal-tail output is comparison-neutral. -/
theorem wallSweepPreCheckResetAuthorized_reset_handoff
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlReset : l.core.reset_cmd = true)
    (hrEcho : r.core.echo = false) :
    let q := wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.core.reset_cmd = false ∧ q.2.core.reset_cmd = true := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  have htail := wallSweepPreCheckResetNormalTail_reset_handoff
    hpsi kappa l r hlReset hrEcho
  change ComparisonNeutral tail.1.core ∧ ComparisonNeutral tail.2.core ∧
    tail.1.core.reset_cmd = false ∧ tail.2.core.reset_cmd = true at htail
  have hmark := markLeaderBirth_eq_of_neutral born tail htail.1 htail.2.1
  have heq := wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
    hpsi kappa l r hopen
  change wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at heq
  rw [heq, hmark]
  exact htail

/-- Path-stall expiry either frames a neutral repaired output or clears its
remaining comparison carrier; in both cases the reset field is unchanged. -/
private theorem deletionPriorityExpireOne_neutral_reset
    (old out : ExpiringAgentState psi kappa tau)
    (hneutral : ComparisonNeutral out.core.erase.core) :
    ComparisonNeutral
        (deletionPriorityExpireOne tau old out).core.erase.core ∧
      (deletionPriorityExpireOne tau old out).core.erase.core.reset_cmd =
        out.core.erase.core.reset_cmd := by
  have hframe := deletionPriorityExpireOne_path_frame old out
  refine ⟨?_, hframe.2.2.2.1⟩
  unfold deletionPriorityExpireOne
  split
  · exact hneutral
  · unfold pathExpireOne
    split
    · exact hneutral
    · split
      · simp [ComparisonNeutral, clearComparisonCarrier,
          AuthorizedBoundedAgentState.erase, BoundedAgentState.erase]
        rfl
      · exact hneutral

/-- Full finite/path-stall handoff on the unchanged carrier. -/
theorem wallSweepPreCheckResetPathStall_reset_handoff
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hrEcho : r.core.erase.core.echo = false) :
    let q := wallSweepPreCheckResetPathStallTransition
      hpsi kappa tau l r
    ComparisonNeutral q.1.core.erase.core ∧
      ComparisonNeutral q.2.core.erase.core ∧
      q.1.core.erase.core.reset_cmd = false ∧
      q.2.core.erase.core.reset_cmd = true := by
  let bounded := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have hauth := wallSweepPreCheckResetAuthorized_reset_handoff
    hpsi kappa l.core.erase r.core.erase hopen hlReset hrEcho
  have herase := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst herase
  have hR := congrArg Prod.snd herase
  change bounded.1.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  change bounded.2.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hLNeutral : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hL]
    exact hauth.1
  have hRNeutral : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hR]
    exact hauth.2.1
  have hLReset : lBase.core.erase.core.reset_cmd = false := by
    change bounded.1.erase.core.reset_cmd = false
    rw [hL]
    exact hauth.2.2.1
  have hRReset : rBase.core.erase.core.reset_cmd = true := by
    change bounded.2.erase.core.reset_cmd = true
    rw [hR]
    exact hauth.2.2.2
  have hLf := deletionPriorityExpireOne_neutral_reset l lBase hLNeutral
  have hRf := deletionPriorityExpireOne_neutral_reset r rBase hRNeutral
  change ComparisonNeutral
      (deletionPriorityExpireOne tau l lBase).core.erase.core ∧
    ComparisonNeutral
      (deletionPriorityExpireOne tau r rBase).core.erase.core ∧
    (deletionPriorityExpireOne tau l lBase).core.erase.core.reset_cmd = false ∧
    (deletionPriorityExpireOne tau r rBase).core.erase.core.reset_cmd = true
  exact ⟨hLf.1, hRf.1, hLf.2.trans hLReset, hRf.2.trans hRReset⟩

/-! ## Follower-pair birth signal initialization

The literal Algorithm-2/CHECK stack can create a leader from two followers
while retaining an arbitrary old absence signal at the endpoint that finally
holds that leader.  The repair below changes only that genuine birth case.  It
is deliberately a wrapper around the complete integrated transition: an edge
with any input leader, and a follower/follower edge whose output is still two
followers, is definitionally unchanged. -/

/-- Clear the absence signal exactly when the supplied finite endpoint is a
leader.  Every other physical and proof-only field is retained. -/
def clearExpiringLeaderSignal
    (u : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau :=
  if u.core.core.leader = true then
    { u with core :=
        { u.core with core :=
            { u.core.core with signal_B := ⟨0, by omega⟩ } } }
  else u

@[simp] theorem clearExpiringLeaderSignal_eq_of_follower
    (u : ExpiringAgentState psi kappa tau)
    (h : u.core.erase.core.leader = false) :
    clearExpiringLeaderSignal u = u := by
  change u.core.core.leader = false at h
  simp [clearExpiringLeaderSignal, h]

@[simp] theorem clearExpiringLeaderSignal_leader
    (u : ExpiringAgentState psi kappa tau) :
    (clearExpiringLeaderSignal u).core.erase.core.leader =
      u.core.erase.core.leader := by
  unfold clearExpiringLeaderSignal
  split <;> rfl

@[simp] theorem clearExpiringLeaderSignal_signal_zero_of_leader
    (u : ExpiringAgentState psi kappa tau)
    (h : u.core.erase.core.leader = true) :
    (clearExpiringLeaderSignal u).core.erase.core.signal_B =
      ⟨0, by omega⟩ := by
  change u.core.core.leader = true at h
  simp [clearExpiringLeaderSignal, h,
    AuthorizedBoundedAgentState.erase, BoundedAgentState.erase]

@[simp] theorem clearExpiringLeaderSignal_label
    (u : ExpiringAgentState psi kappa tau) :
    (clearExpiringLeaderSignal u).core.erase.core.label =
      u.core.erase.core.label := by
  unfold clearExpiringLeaderSignal
  split <;> rfl

@[simp] theorem clearExpiringLeaderSignal_shield
    (u : ExpiringAgentState psi kappa tau) :
    (clearExpiringLeaderSignal u).core.erase.core.shield =
      u.core.erase.core.shield := by
  unfold clearExpiringLeaderSignal
  split <;> rfl

@[simp] theorem clearExpiringLeaderSignal_bullet
    (u : ExpiringAgentState psi kappa tau) :
    (clearExpiringLeaderSignal u).core.erase.core.bullet =
      u.core.erase.core.bullet := by
  unfold clearExpiringLeaderSignal
  split <;> rfl

@[simp] theorem clearExpiringLeaderSignal_probe
    (u : ExpiringAgentState psi kappa tau) :
    (clearExpiringLeaderSignal u).core.erase.core.probe =
      u.core.erase.core.probe := by
  unfold clearExpiringLeaderSignal
  split <;> rfl

@[simp] theorem clearExpiringLeaderSignal_phase
    (u : ExpiringAgentState psi kappa tau) :
    (clearExpiringLeaderSignal u).core.erase.core.phase =
      u.core.erase.core.phase := by
  unfold clearExpiringLeaderSignal
  split <;> rfl

@[simp] theorem clearExpiringLeaderSignal_reset_cmd
    (u : ExpiringAgentState psi kappa tau) :
    (clearExpiringLeaderSignal u).core.erase.core.reset_cmd =
      u.core.erase.core.reset_cmd := by
  unfold clearExpiringLeaderSignal
  split <;> rfl

@[simp] theorem clearExpiringLeaderSignal_echo
    (u : ExpiringAgentState psi kappa tau) :
    (clearExpiringLeaderSignal u).core.erase.core.echo =
      u.core.erase.core.echo := by
  unfold clearExpiringLeaderSignal
  split <;> rfl

@[simp] theorem clearExpiringLeaderSignal_deletionActive
    (u : ExpiringAgentState psi kappa tau) :
    deletionActive (clearExpiringLeaderSignal u).core.erase =
      deletionActive u.core.erase := by
  unfold clearExpiringLeaderSignal
  split <;> rfl

@[simp] theorem clearExpiringLeaderSignal_stall
    (u : ExpiringAgentState psi kappa tau) :
    (clearExpiringLeaderSignal u).stall = u.stall := by
  unfold clearExpiringLeaderSignal
  split <;> rfl

/-- Exact frame of the birth-signal postprocessor.  It names every field used
by the current first-leader, reset-drain, live-rank, and protected-anchor
interfaces; only `signal_B` is intentionally absent. -/
structure BirthSignalFrame
    (before after : ExpiringAgentState psi kappa tau) : Prop where
  leader : after.core.erase.core.leader = before.core.erase.core.leader
  label : after.core.erase.core.label = before.core.erase.core.label
  shield : after.core.erase.core.shield = before.core.erase.core.shield
  bullet : after.core.erase.core.bullet = before.core.erase.core.bullet
  probe : after.core.erase.core.probe = before.core.erase.core.probe
  phase : after.core.erase.core.phase = before.core.erase.core.phase
  reset_cmd :
    after.core.erase.core.reset_cmd = before.core.erase.core.reset_cmd
  echo : after.core.erase.core.echo = before.core.erase.core.echo
  deletion_active :
    deletionActive after.core.erase = deletionActive before.core.erase
  stall : after.stall = before.stall

/-- Pointwise lift of `BirthSignalFrame` to a finite configuration. -/
def BirthSignalConfigFrame
    (before after : Fin n → ExpiringAgentState psi kappa tau) : Prop :=
  ∀ i, BirthSignalFrame (before i) (after i)

theorem BirthSignalFrame.refl
    (u : ExpiringAgentState psi kappa tau) : BirthSignalFrame u u := by
  exact {
    leader := rfl
    label := rfl
    shield := rfl
    bullet := rfl
    probe := rfl
    phase := rfl
    reset_cmd := rfl
    echo := rfl
    deletion_active := rfl
    stall := rfl }

theorem BirthSignalConfigFrame.refl
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    BirthSignalConfigFrame C C := fun i => BirthSignalFrame.refl (C i)

theorem clearExpiringLeaderSignal_frame
    (u : ExpiringAgentState psi kappa tau) :
    BirthSignalFrame u (clearExpiringLeaderSignal u) := by
  exact {
    leader := clearExpiringLeaderSignal_leader u
    label := clearExpiringLeaderSignal_label u
    shield := clearExpiringLeaderSignal_shield u
    bullet := clearExpiringLeaderSignal_bullet u
    probe := clearExpiringLeaderSignal_probe u
    phase := clearExpiringLeaderSignal_phase u
    reset_cmd := clearExpiringLeaderSignal_reset_cmd u
    echo := clearExpiringLeaderSignal_echo u
    deletion_active := clearExpiringLeaderSignal_deletionActive u
    stall := clearExpiringLeaderSignal_stall u }

/-- Postprocess a complete local output only when both input endpoints were
followers.  In that case every output leader is a genuine same-interaction
birth, including a CHECK-born responder migrated to the initiator by WRITE. -/
def initializeFollowerPairBirthSignals
    (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
  if l.core.core.leader = false ∧ r.core.core.leader = false then
    (clearExpiringLeaderSignal q.1, clearExpiringLeaderSignal q.2)
  else q

theorem initializeFollowerPairBirthSignals_frame
    (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) :
    BirthSignalFrame q.1 (initializeFollowerPairBirthSignals l r q).1 ∧
      BirthSignalFrame q.2
        (initializeFollowerPairBirthSignals l r q).2 := by
  unfold initializeFollowerPairBirthSignals
  split
  · exact ⟨clearExpiringLeaderSignal_frame q.1,
      clearExpiringLeaderSignal_frame q.2⟩
  · exact ⟨{
      leader := rfl
      label := rfl
      shield := rfl
      bullet := rfl
      probe := rfl
      phase := rfl
      reset_cmd := rfl
      echo := rfl
      deletion_active := rfl
      stall := rfl }, {
      leader := rfl
      label := rfl
      shield := rfl
      bullet := rfl
      probe := rfl
      phase := rfl
      reset_cmd := rfl
      echo := rfl
      deletion_active := rfl
      stall := rfl }⟩

/-- Minimal finite repair of the birth-signal boundary.  The source lane and
all previously named repair transitions remain unchanged. -/
def wallSweepBirthSignalZeroPathStallTransition
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
  initializeFollowerPairBirthSignals l r
    (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r)

theorem initializeFollowerPairBirthSignals_eq_of_left_leader
    (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau)
    (h : l.core.erase.core.leader = true) :
    initializeFollowerPairBirthSignals l r q = q := by
  change l.core.core.leader = true at h
  simp [initializeFollowerPairBirthSignals, h]

theorem initializeFollowerPairBirthSignals_eq_of_right_leader
    (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau)
    (h : r.core.erase.core.leader = true) :
    initializeFollowerPairBirthSignals l r q = q := by
  change r.core.core.leader = true at h
  simp [initializeFollowerPairBirthSignals, h]

theorem initializeFollowerPairBirthSignals_eq_of_output_followers
    (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau)
    (hl : q.1.core.erase.core.leader = false)
    (hr : q.2.core.erase.core.leader = false) :
    initializeFollowerPairBirthSignals l r q = q := by
  unfold initializeFollowerPairBirthSignals
  split
  · rw [clearExpiringLeaderSignal_eq_of_follower q.1 hl,
      clearExpiringLeaderSignal_eq_of_follower q.2 hr]
  · rfl

theorem initializeFollowerPairBirthSignals_left_signal_zero
    (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau)
    (hl : l.core.erase.core.leader = false)
    (hr : r.core.erase.core.leader = false)
    (hout : q.1.core.erase.core.leader = true) :
    (initializeFollowerPairBirthSignals l r q).1.core.erase.core.signal_B =
      ⟨0, by omega⟩ := by
  change l.core.core.leader = false at hl
  change r.core.core.leader = false at hr
  simp [initializeFollowerPairBirthSignals, hl, hr,
    clearExpiringLeaderSignal_signal_zero_of_leader q.1 hout]

theorem initializeFollowerPairBirthSignals_right_signal_zero
    (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau)
    (hl : l.core.erase.core.leader = false)
    (hr : r.core.erase.core.leader = false)
    (hout : q.2.core.erase.core.leader = true) :
    (initializeFollowerPairBirthSignals l r q).2.core.erase.core.signal_B =
      ⟨0, by omega⟩ := by
  change l.core.core.leader = false at hl
  change r.core.core.leader = false at hr
  simp [initializeFollowerPairBirthSignals, hl, hr,
    clearExpiringLeaderSignal_signal_zero_of_leader q.2 hout]

theorem wallSweepBirthSignalZeroPathStall_eq_of_left_leader
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (h : l.core.erase.core.leader = true) :
    wallSweepBirthSignalZeroPathStallTransition hpsi kappa tau l r =
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r := by
  exact initializeFollowerPairBirthSignals_eq_of_left_leader l r _ h

theorem wallSweepBirthSignalZeroPathStall_eq_of_right_leader
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (h : r.core.erase.core.leader = true) :
    wallSweepBirthSignalZeroPathStallTransition hpsi kappa tau l r =
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r := by
  exact initializeFollowerPairBirthSignals_eq_of_right_leader l r _ h

theorem wallSweepBirthSignalZeroPathStall_eq_of_output_followers
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hl :
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r).1.core.erase.core.leader = false)
    (hr :
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r).2.core.erase.core.leader = false) :
    wallSweepBirthSignalZeroPathStallTransition hpsi kappa tau l r =
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r := by
  exact initializeFollowerPairBirthSignals_eq_of_output_followers l r _ hl hr

theorem wallSweepBirthSignalZeroPathStall_left_birth_signal_zero
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.erase.core.leader = false)
    (hr : r.core.erase.core.leader = false)
    (hout :
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r).1.core.erase.core.leader = true) :
    (wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau l r).1.core.erase.core.signal_B =
        ⟨0, by omega⟩ := by
  exact initializeFollowerPairBirthSignals_left_signal_zero l r _ hl hr hout

theorem wallSweepBirthSignalZeroPathStall_right_birth_signal_zero
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.erase.core.leader = false)
    (hr : r.core.erase.core.leader = false)
    (hout :
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r).2.core.erase.core.leader = true) :
    (wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau l r).2.core.erase.core.signal_B =
        ⟨0, by omega⟩ := by
  exact initializeFollowerPairBirthSignals_right_signal_zero l r _ hl hr hout

end PPLLWallSweepPreCheckResetRepair
