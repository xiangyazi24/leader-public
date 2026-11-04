import Leader.Wu.WallSweep.PreCheckResetContractsExpiring

/-!
# Pre-CHECK reset contracts: FirstBirth

This module is one dependency-ordered part of the former contract monolith.
-/

namespace PPLLWallSweepPreCheckResetContracts

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLRepair PPLLWriteIncrementGate
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLTerminalEqualSupportRepair
  PPLLWallSweepNormalResetContract PPLLWallSweepEchoDrain
  PPLLWallSweepPreCheckResetRepair
  PPLLNoCheckBirthLeaderFrames
  PPLLNoCheckBirthConditionTwoFrames
  PPLLNoCheckBirthConditionTwoKernel
  PPLLNoCheckBirthConditionTwoPhysical

variable {psi kappa tau : Nat}

/-! ## First-birth uniqueness -/

/-- The new pre-CHECK tail cannot create or move an initiator leader. -/
theorem preCheckResetCheckTail_initiator_leader_eq
    (hpsi : psi > 0)
    (q0 : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (preCheckResetCheckTail hpsi q0).1.core.leader =
      q0.1.core.leader := by
  let qR := preCheckResetWall q0.1 q0.2
  let q1 := sanitizeAuthorizedPair hpsi qR
  let q2 := authorizedCheckSig hpsi q1.1 q1.2
  let q3 := authorizedDisappear hpsi q2.1 q2.2
  have hR : qR.1.core.leader = q0.1.core.leader :=
    (preCheckResetWall_leaders_eq q0.1 q0.2).1
  have h1 : q1.1.core.leader = qR.1.core.leader := by
    change (sanitizeAuthorizedTerminalEqual hpsi qR.1).core.leader =
      qR.1.core.leader
    exact sanitizeAuthorizedTerminalEqual_leader_eq hpsi qR.1
  have h2 : q2.1.core.leader = q1.1.core.leader := by
    change (checkSig hpsi q1.1.core q1.2.core).1.leader =
      q1.1.core.leader
    exact PPLLVerify.checkSig_initiator_leader_eq
      hpsi q1.1.core q1.2.core
  have h3 : q3.1.core.leader = q2.1.core.leader := by
    change (disappear hpsi q2.1.core q2.2.core).1.leader =
      q2.1.core.leader
    exact (PPLLVerify.disappear_leaders_eq
      hpsi q2.1.core q2.2.core).1
  have h4 :
      (authorizedCompareSig hpsi q3.1 q3.2).1.core.leader =
        q3.1.core.leader :=
    (authorizedCompareSig_leaders_eq hpsi q3.1 q3.2).1
  have hout :
      (preCheckResetCheckTail hpsi q0).1.core.leader =
        (authorizedCompareSig hpsi q3.1 q3.2).1.core.leader :=
    congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.1.core.leader)
      (by rfl)
  exact hout.trans (h4.trans (h3.trans (h2.trans (h1.trans hR))))

/-- The complete wall-aware prefix through COMPARE frames the initiator leader
unconditionally. -/
theorem wallSweepPreCheckResetBeforeSuppress_initiator_leader_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    (wallSweepPreCheckResetBeforeSuppress hpsi kappa l r).1.core.leader =
      l.core.leader := by
  have h0 := wallSweepAuthorizedBeforeCheck_initiator_leader_eq
    hpsi kappa l r
  have htail := preCheckResetCheckTail_initiator_leader_eq hpsi
    (wallSweepAuthorizedBeforeCheck hpsi kappa l r)
  have heq := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.1.core.leader)
    (wallSweepPreCheckResetBeforeSuppress_eq_checkTail
      hpsi kappa l r)
  exact heq.trans (htail.trans h0)

/-- The ordinary branch through repaired Algorithm 14 frames the initiator
leader. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_initiator_leader_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r).1.core.leader =
      l.core.leader := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  have hpre : pre.1.core.leader = l0.core.leader := by
    simpa only [pre] using
      wallSweepPreCheckResetBeforeSuppress_initiator_leader_eq
        hpsi kappa l0 r0
  have hs :
      (suppressSigResetKill hpsi pre.1.core pre.2.core).1.leader =
        pre.1.core.leader :=
    (suppressSigResetKill_leaders_eq hpsi pre.1.core pre.2.core).1
  have hreconcile :
      (authorizedReconcile (suppressSigResetKill hpsi)
        pre.1 pre.2).1.core.leader =
        (suppressSigResetKill hpsi pre.1.core pre.2.core).1.leader :=
    (authorizedReconcile_leaders_eq
      (suppressSigResetKill hpsi) pre.1 pre.2).1
  have heq :
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r).1.core.leader =
        (authorizedReconcile (suppressSigResetKill hpsi)
          pre.1 pre.2).1.core.leader := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.1.core.leader)
    (wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
      hpsi kappa l r)
  exact heq.trans (hreconcile.trans
    (hs.trans (hpre.trans (normalizeDeletion_leader_eq l))))

private theorem pPsiLeaderProbeWall_responder_leader_eq_of_initiator_leader
    (hpsi : psi > 0) (l r : AgentState psi)
    (hlLeader : l.leader = true) :
    (pPsiLeaderProbeWall hpsi l r).2.leader = r.leader := by
  unfold pPsiLeaderProbeWall
  dsimp only
  simp [hlLeader, pPsi]

set_option maxHeartbeats 1000000 in
private theorem
    wallSweepAuthorizedBeforeCheck_responder_leader_eq_of_initiator_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true) :
    (wallSweepAuthorizedBeforeCheck hpsi kappa l r).2.core.leader =
      r.core.leader := by
  let q0 := authorizedPPsiLeaderProbeWall hpsi l r
  let q1 := authorizedGenSig hpsi kappa q0.1 q0.2
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  let q3 := authorizedEliminateSig hpsi q2.1 q2.2
  have h0 : q0.2.core.leader = r.core.leader :=
    pPsiLeaderProbeWall_responder_leader_eq_of_initiator_leader
      hpsi l.core r.core hlLeader
  have h1 : q1.2.core.leader = q0.2.core.leader :=
    congrArg Prod.snd
      (genSigSaturated_leaders hpsi kappa q0.1.core q0.2.core)
  have h2 : q2.2.core.leader = q1.2.core.leader :=
    (PPLLVerify.cleanSig_leaders_eq hpsi q1.1.core q1.2.core).2
  have h3 : q3.2.core.leader = q2.2.core.leader :=
    (PPLLVerify.eliminateSig_leaders_eq hpsi q2.1.core q2.2.core).2
  have hcore := authorizedSigMoveLeaderWall_core hpsi q3.1 q3.2
  have h4 :
      (authorizedSigMoveLeaderWall hpsi q3.1 q3.2).2.core.leader =
        q3.2.core.leader := by
    have hR := congrArg Prod.snd hcore
    exact (congrArg AgentState.leader hR).trans
      (sigMoveLeaderWall_leaders_eq hpsi q3.1.core q3.2.core).2
  exact h4.trans (h3.trans (h2.trans (h1.trans h0)))

set_option maxHeartbeats 1000000 in
private theorem
    wallSweepPreCheckResetBeforeSuppress_responder_leader_eq_of_initiator_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true) :
    (wallSweepPreCheckResetBeforeSuppress hpsi kappa l r).2.core.leader =
      r.core.leader := by
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l r
  have hrawLeft : beforeRaw.1.core.leader = true :=
    (wallSweepAuthorizedBeforeCheck_initiator_leader_eq
      hpsi kappa l r).trans hlLeader
  have hrawRight : beforeRaw.2.core.leader = r.core.leader :=
    wallSweepAuthorizedBeforeCheck_responder_leader_eq_of_initiator_leader
      hpsi kappa l r hlLeader
  have htail := preCheckResetCheckTail_eq_of_send
    hpsi beforeRaw (.inl hrawLeft)
  change wallSweepPreCheckResetBeforeSuppress hpsi kappa l r =
    preCheckResetWall beforeRaw.1 beforeRaw.2 at htail
  rw [htail]
  exact (preCheckResetWall_leaders_eq beforeRaw.1 beforeRaw.2).2.trans
    hrawRight

/-- When the initiator is already a leader, the complete pre-Algorithm-15
prefix frames the responder leader bit.  In particular, CHECK cannot create a
second leader on that source-covered edge. -/
theorem
    wallSweepPreCheckResetNormalAfterSuppress_responder_leader_eq_of_initiator_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true) :
    (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r).2.core.leader =
      r.core.leader := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  have hl0 : l0.core.leader = true :=
    (normalizeDeletion_leader_eq l).trans hlLeader
  have hpreRight : pre.2.core.leader = r0.core.leader := by
    simpa only [pre] using
      wallSweepPreCheckResetBeforeSuppress_responder_leader_eq_of_initiator_leader
        hpsi kappa l0 r0 hl0
  have hsuppress := suppressSigResetKill_leaders_eq
    hpsi pre.1.core pre.2.core
  have hreconcile := authorizedReconcile_leaders_eq
    (suppressSigResetKill hpsi) pre.1 pre.2
  have hstage := wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
    hpsi kappa l r
  have hout :
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r).2.core.leader =
        (authorizedReconcile (suppressSigResetKill hpsi)
          pre.1 pre.2).2.core.leader := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.leader) hstage
  calc
    (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r).2.core.leader =
        (authorizedReconcile (suppressSigResetKill hpsi)
          pre.1 pre.2).2.core.leader := hout
    _ = (suppressSigResetKill hpsi pre.1.core pre.2.core).2.leader :=
      hreconcile.2
    _ = pre.2.core.leader := hsuppress.2
    _ = r0.core.leader := hpreRight
    _ = r.core.leader := normalizeDeletion_leader_eq r

/-- An existing initiating leader receives the exact repaired-Algorithm-14
comparison/reset/echo cleanup contract without any shield premise. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_leader_source_cleanup
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true) :
    AuthorizedLeaderSourceCleanup (l, r)
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  have hl0 : l0.core.leader = true :=
    (normalizeDeletion_leader_eq l).trans hlLeader
  have hpreLeader : pre.1.core.leader = true := by
    simpa only [pre] using
      beforeSuppress_initiator_leader_true_of_left_leader
        hpsi kappa l0 r0 hl0
  have hbase := afterSuppress_leader_source_cleanup_of_eq hpsi
    (input := (l0, r0)) (pre := pre)
    (out := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r)
    hpreLeader
    (wallSweepPreCheckResetBeforeSuppress_resetEchoPair
      hpsi kappa l0 r0)
    (wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
      hpsi kappa l r)
  have hr0Echo : r0.core.echo = r.core.echo := by
    unfold r0 normalizeDeletion
    split <;> rfl
  rcases hbase with ⟨hleftNeutral, hrightNeutral,
    hleftReset, hrightReset, hleftEcho, hrightEcho⟩
  rw [hr0Echo] at hrightReset
  exact ⟨hleftNeutral, hrightNeutral, hleftReset,
    hrightReset, hleftEcho, hrightEcho⟩

private theorem authorizedBulletFieldPair_eq_of_peaceViewPair_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    authorizedBulletFieldPair a = authorizedBulletFieldPair b := by
  have hL := congrArg Prod.fst h
  have hR := congrArg Prod.snd h
  apply Prod.ext
  · apply BulletFields.ext
    · exact congrArg PeaceView.shield hL
    · exact congrArg PeaceView.bullet hL
    · exact congrArg PeaceView.signal_B hL
  · apply BulletFields.ext
    · exact congrArg PeaceView.shield hR
    · exact congrArg PeaceView.bullet hR
    · exact congrArg PeaceView.signal_B hR

private theorem sanitizeAuthorizedPair_bulletFieldPair
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedBulletFieldPair (sanitizeAuthorizedPair hpsi q) =
      authorizedBulletFieldPair q := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold sanitizeAuthorizedPair sanitizeAuthorizedTerminalEqual
      authorizedBulletFieldPair bulletFieldPair BulletFields.ofState
    try dsimp only []
    repeat (first | rfl | split)

/-- The inserted pre-CHECK deletion and the real CHECK/DISAPPEAR/COMPARE
tail frame both endpoint bullet fields. -/
theorem preCheckResetCheckTail_bulletFieldPair
    (hpsi : psi > 0)
    (q0 : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedBulletFieldPair (preCheckResetCheckTail hpsi q0) =
      authorizedBulletFieldPair q0 := by
  let qR := preCheckResetWall q0.1 q0.2
  let q1 := sanitizeAuthorizedPair hpsi qR
  let q2 := authorizedCheckSig hpsi q1.1 q1.2
  let q3 := authorizedDisappear hpsi q2.1 q2.2
  have hR : authorizedBulletFieldPair qR =
      authorizedBulletFieldPair q0 :=
    authorizedBulletFieldPair_eq_of_peaceViewPair_eq
      (preCheckResetWall_peaceViewPair q0.1 q0.2)
  have h1 : authorizedBulletFieldPair q1 =
      authorizedBulletFieldPair qR :=
    sanitizeAuthorizedPair_bulletFieldPair hpsi qR
  have h2 : authorizedBulletFieldPair q2 =
      authorizedBulletFieldPair q1 := by
    exact checkSig_bulletFieldPair hpsi q1.1.core q1.2.core
  have h3 : authorizedBulletFieldPair q3 =
      authorizedBulletFieldPair q2 := by
    exact disappear_bulletFieldPair hpsi q2.1.core q2.2.core
  have h4 : authorizedBulletFieldPair
      (authorizedCompareSig hpsi q3.1 q3.2) =
      authorizedBulletFieldPair q3 :=
    authorizedCompareSig_bulletFieldPair hpsi q3.1 q3.2
  exact h4.trans (h3.trans (h2.trans (h1.trans hR)))

theorem authorizedSuppressSigResetKill_bulletFieldPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair
        (authorizedReconcile (suppressSigResetKill hpsi) l r) =
      authorizedBulletFieldPair (l, r) :=
  authorizedBulletFieldPair_eq_of_peaceViewPair_eq
    (authorizedSuppressSigResetKill_peaceViewPair hpsi l r)

set_option maxHeartbeats 2000000 in
/-- The reset-aware P-prime prefix and the inserted pre-CHECK deletion wall
frame both endpoint bullet fields up to the sanitized CHECK input. -/
theorem wallSweepResetProbePreCheckResetBeforeCheck_bulletFieldPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair
        (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r) =
      authorizedBulletFieldPair (l, r) := by
  let beforeRaw := wallSweepResetProbeAuthorizedBeforeCheck
    hpsi kappa l r
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  have hraw : authorizedBulletFieldPair beforeRaw =
      authorizedBulletFieldPair (l, r) :=
    wallSweepResetProbeAuthorizedBeforeCheck_bulletFieldPair
      hpsi kappa l r
  have hreset : authorizedBulletFieldPair beforeReset =
      authorizedBulletFieldPair beforeRaw :=
    authorizedBulletFieldPair_eq_of_peaceViewPair_eq
      (preCheckResetWall_peaceViewPair beforeRaw.1 beforeRaw.2)
  have hsanitize : authorizedBulletFieldPair
        (sanitizeAuthorizedPair hpsi beforeReset) =
      authorizedBulletFieldPair beforeReset :=
    sanitizeAuthorizedPair_bulletFieldPair hpsi beforeReset
  change authorizedBulletFieldPair
      (sanitizeAuthorizedPair hpsi beforeReset) =
    authorizedBulletFieldPair (l, r)
  exact hsanitize.trans (hreset.trans hraw)

/-- Real CHECK also frames the bullet fields, so the complete reset-aware
pre-CHECK prefix presents Algorithm 15 with the input pair's bullets. -/
theorem wallSweepResetProbePreCheckResetAfterCheck_bulletFieldPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair
        (wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r) =
      authorizedBulletFieldPair (l, r) := by
  let beforeCheck := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l r
  have hcheck : authorizedBulletFieldPair
        (authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2) =
      authorizedBulletFieldPair (beforeCheck.1, beforeCheck.2) :=
    authorizedCheckSig_bulletFieldPair hpsi beforeCheck.1 beforeCheck.2
  have heta : authorizedBulletFieldPair (beforeCheck.1, beforeCheck.2) =
      authorizedBulletFieldPair beforeCheck :=
    congrArg authorizedBulletFieldPair (Prod.eta beforeCheck)
  change authorizedBulletFieldPair
      (authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2) =
    authorizedBulletFieldPair (l, r)
  exact hcheck.trans (heta.trans
    (wallSweepResetProbePreCheckResetBeforeCheck_bulletFieldPair
      hpsi kappa l r))

/-- The complete corrected prefix through repaired Algorithm 14 frames both
endpoint bullet fields, even when P-prime or CHECK creates a first leader. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_bulletFieldPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair
        (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) =
      authorizedBulletFieldPair (l, r) := by
  let after : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let l0 : AuthorizedAgentState psi := normalizeDeletion l
  let r0 : AuthorizedAgentState psi := normalizeDeletion r
  let beforeRaw : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let pre : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  have hraw := wallSweepAuthorizedBeforeCheck_bulletFieldPair
    hpsi kappa l0 r0
  have htail := preCheckResetCheckTail_bulletFieldPair hpsi beforeRaw
  have hpreStage := congrArg authorizedBulletFieldPair
    (wallSweepPreCheckResetBeforeSuppress_eq_checkTail
      hpsi kappa l0 r0)
  have hpre : authorizedBulletFieldPair pre =
      authorizedBulletFieldPair (l0, r0) :=
    hpreStage.trans (htail.trans hraw)
  have hnormalize : authorizedBulletFieldPair (l0, r0) =
      authorizedBulletFieldPair (l, r) :=
    Prod.ext (normalizeDeletion_bulletFields l)
      (normalizeDeletion_bulletFields r)
  let suppressed : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    authorizedReconcile (suppressSigResetKill hpsi) pre.1 pre.2
  have hsuppress0 : authorizedBulletFieldPair suppressed =
      authorizedBulletFieldPair (pre.1, pre.2) :=
    authorizedSuppressSigResetKill_bulletFieldPair
      hpsi pre.1 pre.2
  have hpreEta : authorizedBulletFieldPair (pre.1, pre.2) =
      authorizedBulletFieldPair pre :=
    congrArg authorizedBulletFieldPair (Prod.eta pre)
  have hsuppress : authorizedBulletFieldPair suppressed =
      authorizedBulletFieldPair pre := hsuppress0.trans hpreEta
  have hafterStage : after = suppressed :=
    wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
      hpsi kappa l r
  have hout : authorizedBulletFieldPair after =
      authorizedBulletFieldPair suppressed :=
    congrArg authorizedBulletFieldPair hafterStage
  change authorizedBulletFieldPair after = authorizedBulletFieldPair (l, r)
  calc
    _ = authorizedBulletFieldPair suppressed := hout
    _ = authorizedBulletFieldPair pre := hsuppress
    _ = authorizedBulletFieldPair (l0, r0) := hpre
    _ = authorizedBulletFieldPair (l, r) := hnormalize

theorem markLeaderBirth_bulletFieldPair
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedBulletFieldPair (markLeaderBirth born q) =
      authorizedBulletFieldPair q := by
  apply Prod.ext <;> apply BulletFields.ext
  all_goals
    unfold markLeaderBirth markComparisonForDeletion
      authorizedBulletFieldPair bulletFieldPair BulletFields.ofState
    try dsimp only []
    repeat (first | rfl | split)

/-- If an initiating leader disappears in the rooted ordinary tail, the staged
Algorithm-15/WRITE certificate identifies the live responder bullet that killed
it and the resulting dummy bullet. -/
theorem wallSweepPreCheckResetLeaderSinkNormalTail_live_hit_of_initiator_killed
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true)
    (hrFollower : r.core.leader = false)
    (houtFollower :
      (wallSweepPreCheckResetLeaderSinkNormalTail
        hpsi kappa l r).1.core.leader = false) :
    let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
    let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
    AuthorizedInitiatorLeaderLiveHit after.1 after.2 tail := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let beforeWrite := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) after.1 after.2
  let out := authorizedReconcile (writeSeqIncrementGate hpsi)
    beforeWrite.1 beforeWrite.2
  have houtEq : wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r =
      out := by
    rfl
  have hafterLeft : after.1.core.leader = true :=
    (wallSweepPreCheckResetNormalAfterSuppress_initiator_leader_eq
      hpsi kappa l r).trans hlLeader
  have hafterRight : after.2.core.leader = false :=
    (wallSweepPreCheckResetNormalAfterSuppress_responder_leader_eq_of_initiator_leader
      hpsi kappa l r hlLeader).trans hrFollower
  have houtFollower' : out.1.core.leader = false := by
    exact (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.1.core.leader) houtEq).symm.trans houtFollower
  have hbeforeLeaders := authorizedReconcile_leaders_eq
    (eliminateLeadersNoCollisionLeaderSink hpsi) after.1 after.2
  have hbeforeFields := authorizedReconcile_bulletFieldPair
    (eliminateLeadersNoCollisionLeaderSink hpsi) after.1 after.2
  have hbeforeLeftBullet := congrArg (fun q => q.1.bullet) hbeforeFields
  have hbeforeRightBullet := congrArg (fun q => q.2.bullet) hbeforeFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hbeforeLeftBullet
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hbeforeRightBullet
  dsimp only at hbeforeLeftBullet hbeforeRightBullet
  have houtLeaders := authorizedReconcile_leaders_eq
    (writeSeqIncrementGate hpsi) beforeWrite.1 beforeWrite.2
  have houtFields := authorizedReconcile_bulletFieldPair
    (writeSeqIncrementGate hpsi) beforeWrite.1 beforeWrite.2
  have houtLeftBullet := congrArg (fun q => q.1.bullet) houtFields
  have houtRightBullet := congrArg (fun q => q.2.bullet) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at houtLeftBullet
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at houtRightBullet
  dsimp only at houtLeftBullet houtRightBullet
  rw [houtEq]
  exact authorizedLeaderSinkPostSuppress_live_hit_of_stages
    hpsi after.1 after.2 beforeWrite out
    hbeforeLeaders.1 hbeforeLeaders.2
    hbeforeLeftBullet hbeforeRightBullet
    houtLeaders.1 houtLeaders.2 houtLeftBullet houtRightBullet
    hafterLeft hafterRight houtFollower'

/-- A source-covered leader edge cannot create a second leader at its
responder.  The pre-Algorithm-15 prefix frames the follower responder;
Algorithm 15 never creates a responder leader, and gated WRITE can only retain
a responder leader that was already present. -/
theorem
    wallSweepPreCheckResetLeaderSinkNormalTail_responder_follower_of_initiator_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true)
    (hrFollower : r.core.leader = false) :
    (wallSweepPreCheckResetLeaderSinkNormalTail
      hpsi kappa l r).2.core.leader = false := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let beforeWrite := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) after.1 after.2
  let out := authorizedReconcile (writeSeqIncrementGate hpsi)
    beforeWrite.1 beforeWrite.2
  have houtEq : wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r =
      out := by
    rfl
  have hafterRight : after.2.core.leader = false :=
    (wallSweepPreCheckResetNormalAfterSuppress_responder_leader_eq_of_initiator_leader
      hpsi kappa l r hlLeader).trans hrFollower
  have hrawRight :
      (eliminateLeadersNoCollisionLeaderSink
        hpsi after.1.core after.2.core).2.leader = false :=
    (eliminateLeadersNoCollisionLeaderSink_leaders_eq
      hpsi after.1.core after.2.core).2.trans
        ((eliminateLeadersNoCollision_responder_leader_eq
          hpsi after.1.core after.2.core).trans hafterRight)
  have hbeforeRight : beforeWrite.2.core.leader = false :=
    (authorizedReconcile_leaders_eq
      (eliminateLeadersNoCollisionLeaderSink hpsi)
      after.1 after.2).2.trans hrawRight
  have hwriteRight :
      (writeSeqIncrementGate hpsi
        beforeWrite.1.core beforeWrite.2.core).2.leader = false := by
    cases hout : (writeSeqIncrementGate hpsi
      beforeWrite.1.core beforeWrite.2.core).2.leader
    · rfl
    · have horigin := writeSeqIncrementGate_responder_origin
        hpsi beforeWrite.1.core beforeWrite.2.core hout
      have hbad : (false : Bool) = true :=
        hbeforeRight.symm.trans horigin
      simp at hbad
  have houtRight :
      out.2.core.leader = false :=
    (authorizedReconcile_leaders_eq
      (writeSeqIncrementGate hpsi) beforeWrite.1 beforeWrite.2).2.trans
        hwriteRight
  exact (congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.leader) houtEq).trans houtRight


end PPLLWallSweepPreCheckResetContracts
