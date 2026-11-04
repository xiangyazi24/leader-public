import Leader.Wu.WallSweep.PreCheckResetContractsResetControl

/-!
# Pre-CHECK reset contracts: Normalized

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

/-- Single physical contract consumed by the reset-normalizing clockwise
induction: no leader is born, the edge becomes successor-aligned, comparison
is neutral, and reset/echo behavior is exact. -/
structure ExpiringResetFollowerNormalizedOutput
    (hpsi : psi > 0)
    (input output : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop where
  control : ExpiringResetFollowerControlOutput hpsi input output
  left_follower : output.1.core.erase.core.leader = false
  right_follower : output.2.core.erase.core.leader = false
  left_label : output.1.core.erase.core.label =
    input.1.core.erase.core.label
  right_successor : output.2.core.erase.core.label =
    ⟨(input.1.core.erase.core.label.val + 1) % psi,
      Nat.mod_lt _ hpsi⟩

/-- Complete path-stall reset-normalization result, with no input alignment
premise. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_exists_reset_follower_normalization
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlFollower : l.core.erase.core.leader = false)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hrFollower : r.core.erase.core.leader = false) :
    ∃ output, output =
        wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau l r ∧
      ExpiringResetFollowerNormalizedOutput hpsi (l, r) output := by
  rcases
      wallSweepResetProbePreCheckResetLeaderSinkPathStall_exists_reset_follower_control
      hpsi l r hopen hlFollower hlReset hrFollower
      with ⟨output, houtput, hcontrol⟩
  have hfollowers :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_followers_of_reset_source
      hpsi l r hopen hlFollower hlReset hrFollower
  have hlabels :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_source_follower_labels
      hpsi l r hopen (.inr hlReset) hrFollower
  have hleftFollower : output.1.core.erase.core.leader = false :=
    (congrArg
      (fun q : ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau =>
          q.1.core.erase.core.leader) houtput).trans hfollowers.1
  have hrightFollower : output.2.core.erase.core.leader = false :=
    (congrArg
      (fun q : ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau =>
          q.2.core.erase.core.leader) houtput).trans hfollowers.2
  have hleftLabel : output.1.core.erase.core.label =
      l.core.erase.core.label :=
    (congrArg
      (fun q : ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau =>
          q.1.core.erase.core.label) houtput).trans hlabels.1
  have hrightLabel : output.2.core.erase.core.label =
      ⟨(l.core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ :=
    (congrArg
      (fun q : ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau =>
          q.2.core.erase.core.label) houtput).trans hlabels.2
  exact ⟨output, houtput, {
    control := hcontrol
    left_follower := hleftFollower
    right_follower := hrightFollower
    left_label := hleftLabel
    right_successor := hrightLabel }⟩

/-- On a follower/follower barrier, a resident responder probe is returned as
a label-zero leader by the physical P-prime stage.  Authorization reconciliation
does not alter either physical field. -/
theorem authorizedPPsiLeaderProbeWall_barrier_probe_birth
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hprobe : r.core.probe = true)
    (hbarrier : isBarrier hpsi l.core r.core) :
    ResponderZeroAnchor hpsi
      (authorizedPPsiLeaderProbeWall hpsi l r).2.core := by
  change ResponderZeroAnchor hpsi
    (pPsiLeaderProbeWall hpsi l.core r.core).2
  rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders
    hpsi l.core r.core hl hr]
  unfold isBarrier at hbarrier
  unfold ResponderZeroAnchor
  simp [pPsi, hbarrier, hprobe]

/-- The saturated repair prefix through SIGMOVE preserves the label-zero
leader born when a responder probe returns across a barrier. -/
theorem wallSweepAuthorizedBeforeCheck_barrier_probe_birth
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hprobe : r.core.probe = true)
    (hbarrier : isBarrier hpsi l.core r.core) :
    ResponderZeroAnchor hpsi
      (wallSweepAuthorizedBeforeCheck hpsi kappa l r).2.core := by
  -- Stage by stage through `Leader.Wu.WallSweep.StageFrames`: chaining the stage
  -- facts through `let`-bound stage outputs made the elaborator reduce the
  -- composed prefix (191 s).
  have h0 : ResponderZeroAnchor hpsi
      (authorizedPPsiLeaderProbeWall hpsi l r).2.core :=
    authorizedPPsiLeaderProbeWall_barrier_probe_birth
      hpsi l r hl hr hprobe hbarrier
  rw [PPLLWallSweepStageFrames.wallSweepAuthorizedBeforeCheck_stages]
  revert h0
  generalize authorizedPPsiLeaderProbeWall hpsi l r = q0
  intro h0
  have h1 := PPLLWallSweepStageFrames.authorizedGenSig_leaders_eq
    hpsi kappa q0.1 q0.2
  have h1' := PPLLWallSweepStageFrames.authorizedGenSig_labels_eq
    hpsi kappa q0.1 q0.2
  revert h1 h1'
  generalize authorizedGenSig hpsi kappa q0.1 q0.2 = q1
  intro h1 h1'
  have h2 := PPLLWallSweepStageFrames.authorizedCleanSig_leaders_eq
    hpsi q1.1 q1.2
  have h2' := PPLLWallSweepStageFrames.authorizedCleanSig_labels_eq
    hpsi q1.1 q1.2
  revert h2 h2'
  generalize authorizedCleanSig hpsi q1.1 q1.2 = q2
  intro h2 h2'
  have h3 := PPLLWallSweepStageFrames.authorizedEliminateSig_leaders_eq
    hpsi q2.1 q2.2
  have h3' := PPLLWallSweepStageFrames.authorizedEliminateSig_labels_eq
    hpsi q2.1 q2.2
  revert h3 h3'
  generalize authorizedEliminateSig hpsi q2.1 q2.2 = q3
  intro h3 h3'
  have h4 := PPLLWallSweepStageFrames.authorizedSigMoveLeaderWall_leaders_eq
    hpsi q3.1 q3.2
  have h4' := PPLLWallSweepStageFrames.authorizedSigMoveLeaderWall_labels_eq
    hpsi q3.1 q3.2
  exact ⟨h4.2.trans (h3.2.trans (h2.2.trans (h1.2.trans h0.1))),
    h4'.2.trans (h3'.2.trans (h2'.2.trans (h1'.2.trans h0.2)))⟩

structure AuthorizedResponderLeaderWitness
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  leader_eq : q.2.core.leader = true

structure AuthorizedResponderZeroWitness
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  leader_eq : q.2.core.leader = true
  label_eq : q.2.core.label = ⟨0, hpsi⟩

structure AuthorizedResponderLeaderLabelFrame
    (before after :
      AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  leader_eq : after.2.core.leader = before.2.core.leader
  label_eq : after.2.core.label = before.2.core.label

private theorem responderFrame_through_reset_sanitize
    (hpsi : psi > 0)
    (raw reset check :
      AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hreset : reset = preCheckResetWall raw.1 raw.2)
    (hcheck : check = sanitizeAuthorizedPair hpsi reset) :
    AuthorizedResponderLeaderLabelFrame raw check := by
  have hcheckLeader : check.2.core.leader = reset.2.core.leader :=
    (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.2.core.leader) hcheck).trans
      (sanitizeAuthorizedPair_leaders_eq hpsi reset).2
  have hcheckLabel : check.2.core.label = reset.2.core.label :=
    (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.2.core.label) hcheck).trans
      (sanitizeAuthorizedPair_labels_eq hpsi reset).2
  have hresetView := congrArg Prod.snd
    (preCheckResetWall_peaceViewPair raw.1 raw.2)
  have hresetLeader : reset.2.core.leader = raw.2.core.leader :=
    (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.2.core.leader) hreset).trans
      (congrArg PeaceView.leader hresetView)
  have hresetLabel : reset.2.core.label = raw.2.core.label :=
    (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.2.core.label) hreset).trans
      (congrArg PeaceView.label hresetView)
  exact {
    leader_eq := hcheckLeader.trans hresetLeader
    label_eq := hcheckLabel.trans hresetLabel }

/-- With two follower inputs, every responder leader present at the end of the
saturated pre-CHECK prefix is the zero-labelled P-prime barrier/probe birth.
The later prefix stages frame the leader bit, so no other creation route is
available before CHECK. -/
theorem wallSweepAuthorizedBeforeCheck_new_responder_zero
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hout : AuthorizedResponderLeaderWitness
      (wallSweepAuthorizedBeforeCheck hpsi kappa l r)) :
    AuthorizedResponderZeroWitness hpsi
      (wallSweepAuthorizedBeforeCheck hpsi kappa l r) := by
  -- Backwards through the stages, as in the previous theorem.
  have hout4 := hout.leader_eq
  rw [PPLLWallSweepStageFrames.wallSweepAuthorizedBeforeCheck_stages] at hout4
  revert hout4
  generalize hq0 : authorizedPPsiLeaderProbeWall hpsi l r = q0
  intro hout4
  have h1 := PPLLWallSweepStageFrames.authorizedGenSig_leaders_eq
    hpsi kappa q0.1 q0.2
  revert h1 hout4
  generalize authorizedGenSig hpsi kappa q0.1 q0.2 = q1
  intro hout4 h1
  have h2 := PPLLWallSweepStageFrames.authorizedCleanSig_leaders_eq
    hpsi q1.1 q1.2
  revert h2 hout4
  generalize authorizedCleanSig hpsi q1.1 q1.2 = q2
  intro hout4 h2
  have h3 := PPLLWallSweepStageFrames.authorizedEliminateSig_leaders_eq
    hpsi q2.1 q2.2
  revert h3 hout4
  generalize authorizedEliminateSig hpsi q2.1 q2.2 = q3
  intro hout4 h3
  have h4 := PPLLWallSweepStageFrames.authorizedSigMoveLeaderWall_leaders_eq
    hpsi q3.1 q3.2
  have h0' : q0.2.core.leader = true :=
    h1.2.symm.trans (h2.2.symm.trans (h3.2.symm.trans (h4.2.symm.trans hout4)))
  have h0 : (authorizedPPsiLeaderProbeWall hpsi l r).2.core.leader = true := by
    rw [hq0]
    exact h0'
  have hq0Core : (authorizedPPsiLeaderProbeWall hpsi l r).2.core =
      (pPsiLeaderProbeWall hpsi l.core r.core).2 := by
    rfl
  have hrawWall :
      (pPsiLeaderProbeWall hpsi l.core r.core).2.leader = true :=
    (congrArg AgentState.leader hq0Core).symm.trans h0
  have hraw0 : (pPsi hpsi l.core r.core).2.leader = true := by
    rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders
      hpsi l.core r.core hl hr] at hrawWall
    exact hrawWall
  have horigin := PPLLVerify.pPsi_new_responder_leader_requires_probe_barrier
    hpsi l.core r.core hraw0 hr
  have hzero := wallSweepAuthorizedBeforeCheck_barrier_probe_birth
    hpsi kappa l r hl hr horigin.1 horigin.2
  exact { leader_eq := hzero.1, label_eq := hzero.2 }

/-- An existing responder leader, unlike a fresh follower/follower birth, is
framed by the complete saturated pre-CHECK prefix at its physical host.  This
is the entry contract needed by the reverse WRITE migration schedule: the
prefix neither removes the leader nor relabels the host before real CHECK. -/
theorem wallSweepAuthorizedBeforeCheck_responder_frame_of_responder_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    let out := wallSweepAuthorizedBeforeCheck hpsi kappa l r
    out.2.core.leader = true ∧
      out.1.core.label = l.core.label ∧
      out.2.core.label = r.core.label := by
  have hppsi := pPsiLeaderProbeWall_responder_frame_of_responder_leader
    hpsi l.core r.core hrLeader
  have hview := wallSweepAuthorizedBeforeCheck_peaceView_of_ppsi_frame
    hpsi kappa l r hppsi.1 hppsi.2
  have hfields :=
    responderLeaderAndLabels_of_authorizedPeaceViewPair_eq hview
  exact ⟨hfields.1.trans hrLeader, hfields.2.1, hfields.2.2⟩

/-- The reset wall, sanitizer, and real CHECK preserve an existing responder
leader and its host label after the saturated prefix. -/
theorem wallSweepPreCheckResetAfterCheck_responder_frame_of_responder_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrLeader : r.core.leader = true) :
    let out := wallSweepPreCheckResetAfterCheck hpsi kappa l r
    out.2.core.leader = true ∧
      out.1.core.label = l.core.label ∧
      out.2.core.label = r.core.label := by
  have hview :=
    wallSweepPreCheckResetAfterCheck_peaceView_of_responder_leader
      hpsi kappa l r hrLeader
  have hfields :=
    responderLeaderAndLabels_of_authorizedPeaceViewPair_eq hview
  exact ⟨hfields.1.trans hrLeader, hfields.2.1, hfields.2.2⟩

/-- If the repaired interaction starts with two followers, a responder leader
already present at the sanitized CHECK input is necessarily the label-zero
P-prime barrier/probe birth.  The reset wall and sanitizer frame both fields. -/
theorem wallSweepPreCheckReset_beforeCheck_new_responder_zero
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hnew : AuthorizedResponderLeaderWitness
      (wallSweepPreCheckResetBeforeCheck hpsi kappa l r)) :
    AuthorizedResponderZeroWitness hpsi
      (wallSweepPreCheckResetBeforeCheck hpsi kappa l r) := by
  have hframe := responderFrame_through_reset_sanitize hpsi
    (wallSweepAuthorizedBeforeCheck hpsi kappa l r)
    (preCheckResetWall (wallSweepAuthorizedBeforeCheck hpsi kappa l r).1
      (wallSweepAuthorizedBeforeCheck hpsi kappa l r).2)
    (wallSweepPreCheckResetBeforeCheck hpsi kappa l r) rfl rfl
  have hrawZero := wallSweepAuthorizedBeforeCheck_new_responder_zero
    hpsi kappa l r hl hr
    { leader_eq := hframe.leader_eq.symm.trans hnew.leader_eq }
  exact {
    leader_eq := hnew.leader_eq
    label_eq := hframe.label_eq.trans hrawZero.label_eq }

private theorem responderFrame_to_leaderSinkBeforeWrite
    (hpsi : psi > 0)
    (afterCheck beforeSuppress afterSuppress beforeWrite :
      AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hpre : beforeSuppress =
      let afterDisappear := authorizedDisappear hpsi
        afterCheck.1 afterCheck.2
      authorizedCompareSig hpsi afterDisappear.1 afterDisappear.2)
    (hsuppress : afterSuppress = authorizedReconcile
      (suppressSigResetKill hpsi) beforeSuppress.1 beforeSuppress.2)
    (hsink : beforeWrite = authorizedReconcile
      (eliminateLeadersNoCollisionLeaderSink hpsi)
      afterSuppress.1 afterSuppress.2) :
    AuthorizedResponderLeaderLabelFrame afterCheck beforeWrite := by
  let afterDisappear := authorizedDisappear hpsi
    afterCheck.1 afterCheck.2
  let afterCompare := authorizedCompareSig hpsi
    afterDisappear.1 afterDisappear.2
  change beforeSuppress = afterCompare at hpre
  have hdisappearLeader : afterDisappear.2.core.leader =
      afterCheck.2.core.leader :=
    (authorizedDisappear_leaders_eq
      hpsi afterCheck.1 afterCheck.2).2
  have hdisappearLabel : afterDisappear.2.core.label =
      afterCheck.2.core.label :=
    (authorizedDisappear_labels_eq
      hpsi afterCheck.1 afterCheck.2).2
  have hcompareLeader : afterCompare.2.core.leader =
      afterDisappear.2.core.leader :=
    (authorizedCompareSig_leaders_eq
      hpsi afterDisappear.1 afterDisappear.2).2
  have hcompareLabels :=
    PPLLNoCheckBirthConditionTwoFrames.authorizedCompareSig_labels
      hpsi afterDisappear.1 afterDisappear.2
  have hcompareLabel : afterCompare.2.core.label =
      afterDisappear.2.core.label := congrArg Prod.snd hcompareLabels
  have hpreLeader : beforeSuppress.2.core.leader =
      afterCompare.2.core.leader := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.leader) hpre
  have hpreLabel : beforeSuppress.2.core.label =
      afterCompare.2.core.label := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.label) hpre
  have hsuppressLeader : afterSuppress.2.core.leader =
      beforeSuppress.2.core.leader := by
    rw [hsuppress]
    change (suppressSigResetKill hpsi
      beforeSuppress.1.core beforeSuppress.2.core).2.leader =
        beforeSuppress.2.core.leader
    exact (suppressSigResetKill_leaders_eq hpsi
      beforeSuppress.1.core beforeSuppress.2.core).2
  have hsuppressLabel : afterSuppress.2.core.label =
      beforeSuppress.2.core.label := by
    rw [hsuppress]
    change (suppressSigResetKill hpsi
      beforeSuppress.1.core beforeSuppress.2.core).2.label =
        beforeSuppress.2.core.label
    exact suppressSigResetKill_right_label_eq hpsi
      beforeSuppress.1.core beforeSuppress.2.core
  have hsinkLeader : beforeWrite.2.core.leader =
      afterSuppress.2.core.leader := by
    rw [hsink]
    change (eliminateLeadersNoCollisionLeaderSink hpsi
      afterSuppress.1.core afterSuppress.2.core).2.leader =
        afterSuppress.2.core.leader
    exact (eliminateLeadersNoCollisionLeaderSink_leaders_eq
      hpsi afterSuppress.1.core afterSuppress.2.core).2.trans
        (eliminateLeadersNoCollision_responder_leader_eq
          hpsi afterSuppress.1.core afterSuppress.2.core)
  have hsinkLabel : beforeWrite.2.core.label =
      afterSuppress.2.core.label := by
    rw [hsink]
    change (eliminateLeadersNoCollisionLeaderSink hpsi
      afterSuppress.1.core afterSuppress.2.core).2.label =
        afterSuppress.2.core.label
    exact (eliminateLeadersNoCollisionLeaderSink_labels_eq
      hpsi afterSuppress.1.core afterSuppress.2.core).2.trans
        (PPLLNoCheckBirthConditionTwoKernel.noCollision_labels hpsi
          afterSuppress.1.core afterSuppress.2.core).2
  exact {
    leader_eq := hsinkLeader.trans (hsuppressLeader.trans
      (hpreLeader.trans (hcompareLeader.trans hdisappearLeader)))
    label_eq := hsinkLabel.trans (hsuppressLabel.trans
      (hpreLabel.trans (hcompareLabel.trans hdisappearLabel))) }

/-- From the real CHECK output through DISAPPEAR, COMPARE, repaired
Algorithm 14, and the leader-sink part of Algorithm 15, the responder's leader
and label are framed.  This stops the final WRITE migration certificate from
being mistaken for a later leader birth. -/
theorem
    wallSweepPreCheckResetLeaderSink_beforeWrite_responder_frame_afterCheck
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedResponderLeaderLabelFrame
      (wallSweepPreCheckResetAfterCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))
      (wallSweepPreCheckResetLeaderSinkBeforeWrite hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  let afterCheck := wallSweepPreCheckResetAfterCheck hpsi kappa l0 r0
  let beforeSuppress :=
    wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  let afterSuppress :=
    wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let beforeWrite :=
    wallSweepPreCheckResetLeaderSinkBeforeWrite hpsi kappa l r
  exact responderFrame_to_leaderSinkBeforeWrite hpsi
    afterCheck beforeSuppress afterSuppress beforeWrite
    (by rfl)
    (wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
      hpsi kappa l r)
    (by rfl)

theorem preCheckResetCheckTail_responder_zero_anchor
    (hpsi : psi > 0)
    (q0 : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (h0 : ResponderZeroAnchor hpsi q0.2.core) :
    authorizedResponderZeroAnchor hpsi (preCheckResetCheckTail hpsi q0) := by
  let qR := preCheckResetWall q0.1 q0.2
  let q1 := sanitizeAuthorizedPair hpsi qR
  let q2 := authorizedCheckSig hpsi q1.1 q1.2
  let q3 := authorizedDisappear hpsi q2.1 q2.2
  have hR : ResponderZeroAnchor hpsi qR.2.core :=
    preCheckResetWall_responder_zero_anchor hpsi q0.1 q0.2 h0
  have h1 : ResponderZeroAnchor hpsi q1.2.core := by
    change ResponderZeroAnchor hpsi
      (sanitizeAuthorizedTerminalEqual hpsi qR.2).core
    unfold sanitizeAuthorizedTerminalEqual
    split <;> exact hR
  have h2 : ResponderZeroAnchor hpsi q2.2.core := by
    change ResponderZeroAnchor hpsi (checkSig hpsi q1.1.core q1.2.core).2
    exact ⟨PPLLVerify.checkSig_responder_leader_of_true
        hpsi q1.1.core q1.2.core h1.1,
      (PPLLVerify.checkSig_labels_eq hpsi q1.1.core q1.2.core).2.trans h1.2⟩
  have h3 : ResponderZeroAnchor hpsi q3.2.core := by
    change ResponderZeroAnchor hpsi (disappear hpsi q2.1.core q2.2.core).2
    exact ⟨(PPLLVerify.disappear_leaders_eq hpsi q2.1.core q2.2.core).2.trans h2.1,
      (PPLLVerify.disappear_labels_eq hpsi q2.1.core q2.2.core).2.trans h2.2⟩
  change ResponderZeroAnchor hpsi
    (authorizedCompareSig hpsi q3.1 q3.2).2.core
  have hleaders := authorizedCompareSig_leaders_eq hpsi q3.1 q3.2
  have hlabels :=
    PPLLNoCheckBirthConditionTwoFrames.authorizedCompareSig_labels
      hpsi q3.1 q3.2
  exact ⟨hleaders.2.trans h3.1,
    (congrArg Prod.snd hlabels).trans h3.2⟩

/-- A barrier-return P-prime birth reaches repaired Algorithm 14 as a
label-zero responder leader, even though the initiator did not previously
carry a leader or reset token. -/
theorem wallSweepPreCheckResetBeforeSuppress_barrier_probe_birth
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hprobe : r.core.probe = true)
    (hbarrier : isBarrier hpsi l.core r.core) :
    authorizedResponderZeroAnchor hpsi
      (wallSweepPreCheckResetBeforeSuppress hpsi kappa l r) := by
  exact preCheckResetCheckTail_responder_zero_anchor hpsi
    (wallSweepAuthorizedBeforeCheck hpsi kappa l r)
    (wallSweepAuthorizedBeforeCheck_barrier_probe_birth
      hpsi kappa l r hl hr hprobe hbarrier)

/-- The complete wall-aware prefix through SIGMOVE frames the initiator leader
bit without requiring its shield. -/
theorem wallSweepAuthorizedBeforeCheck_initiator_leader_eq
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    (wallSweepAuthorizedBeforeCheck hpsi kappa l r).1.core.leader =
      l.core.leader := by
  rw [PPLLWallSweepStageFrames.wallSweepAuthorizedBeforeCheck_stages]
  exact (PPLLWallSweepStageFrames.authorizedSigMoveLeaderWall_leaders_eq
      hpsi _ _).1.trans
    ((PPLLWallSweepStageFrames.authorizedEliminateSig_leaders_eq
        hpsi _ _).1.trans
      ((PPLLWallSweepStageFrames.authorizedCleanSig_leaders_eq
          hpsi _ _).1.trans
        ((PPLLWallSweepStageFrames.authorizedGenSig_leaders_eq
            hpsi kappa _ _).1.trans
          (authorizedPPsiLeaderProbeWall_initiator_leader_eq hpsi l r))))

/-- A shielded initiating leader reaches repaired Algorithm 14 unchanged in
its leader/shield anchor; its comparison carrier has already been cleared. -/
theorem wallSweepPreCheckResetBeforeSuppress_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor
      (wallSweepPreCheckResetBeforeSuppress hpsi kappa l r) := by
  have hraw := wallSweepAuthorizedBeforeCheck_initiator_anchor
    hpsi kappa l r h
  rw [wallSweepPreCheckResetBeforeSuppress_eq_checkTail]
  revert hraw
  generalize wallSweepAuthorizedBeforeCheck hpsi kappa l r = beforeRaw
  intro hraw
  rw [preCheckResetCheckTail_eq_of_send hpsi beforeRaw (.inl hraw.1)]
  exact preCheckResetWall_initiator_anchor beforeRaw.1 beforeRaw.2 hraw

/-- An initiating leader clears both comparison endpoints before CHECK, even
when it is not yet shielded. -/
theorem wallSweepPreCheckResetBeforeSuppress_neutral_of_left_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true) :
    let q := wallSweepPreCheckResetBeforeSuppress hpsi kappa l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.path0Crossed = false ∧ q.2.path0Crossed = false := by
  have hrawLeader :
      (wallSweepAuthorizedBeforeCheck hpsi kappa l r).1.core.leader = true :=
    (wallSweepAuthorizedBeforeCheck_initiator_leader_eq
      hpsi kappa l r).trans hlLeader
  rw [wallSweepPreCheckResetBeforeSuppress_eq_checkTail]
  revert hrawLeader
  generalize wallSweepAuthorizedBeforeCheck hpsi kappa l r = beforeRaw
  intro hrawLeader
  rw [preCheckResetCheckTail_eq_of_send hpsi beforeRaw (.inl hrawLeader)]
  exact preCheckResetWall_both_neutral_of_send
    beforeRaw.1 beforeRaw.2 (.inl hrawLeader)

/-- A leader or an existing reset source makes the actual prefix neutral. -/
theorem wallSweepPreCheckResetBeforeSuppress_neutral_of_source
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true) :
    let q := wallSweepPreCheckResetBeforeSuppress hpsi kappa l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.path0Crossed = false ∧ q.2.path0Crossed = false := by
  rcases hsource with hleader | hreset
  · exact wallSweepPreCheckResetBeforeSuppress_neutral_of_left_leader
      hpsi kappa l r hleader
  · exact wallSweepPreCheckResetBeforeSuppress_neutral_of_left_reset
      hpsi kappa l r hreset

/-- Certificate form of a PeaceView frame that avoids unfolding a complete
transition merely to elaborate its output projection. -/
inductive AuthorizedPeaceFrame
    (input output : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop
    where
  | intro (witness : AuthorizedAgentState psi × AuthorizedAgentState psi)
      (middle1 middle2 : AuthorizedAgentState psi × AuthorizedAgentState psi)
      (witness_eq : witness = output)
      (witness_view_eq : authorizedPeaceViewPair witness =
        authorizedPeaceViewPair middle1)
      (middle_view_eq : authorizedPeaceViewPair middle1 =
        authorizedPeaceViewPair middle2)
      (last_view_eq : authorizedPeaceViewPair middle2 =
        authorizedPeaceViewPair input)

/-- Extract the actual PeaceView equality from a frame certificate. -/
theorem AuthorizedPeaceFrame.exact_eq
    {input output : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : AuthorizedPeaceFrame input output) :
    authorizedPeaceViewPair output = authorizedPeaceViewPair input := by
  rcases h with ⟨witness, middle1, middle2, hwitness,
    hfirst, hsecond, hthird⟩
  rw [← hwitness]
  exact hfirst.trans (hsecond.trans hthird)

/-- Eta for the PeaceView projection, at a variable pair (so callers need not
unfold a concrete pair to compare `(q.1, q.2)` with `q`). -/
private theorem authorizedPeaceViewPair_pair_eta
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedPeaceViewPair (q.1, q.2) = authorizedPeaceViewPair q :=
  rfl

/-- If the wall-aware P-prime stage frames the responder's physical fields,
then any leader/reset-covered edge frames the complete Algorithm-15 PeaceView
through the corrected prefix while deleting comparison material.  This is the
common seam for an aligned follower edge and for a barrier already covered by
its responder leader. -/
theorem wallSweepPreCheckResetBeforeSuppress_peaceFrame_of_ppsi_source
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrespLeader :
      (authorizedPPsiLeaderProbeWall hpsi l r).2.core.leader = r.core.leader)
    (hrespLabel :
      (authorizedPPsiLeaderProbeWall hpsi l r).2.core.label = r.core.label)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true) :
    AuthorizedPeaceFrame (l, r)
      (wallSweepPreCheckResetBeforeSuppress hpsi kappa l r) := by
  have hbefore := wallSweepAuthorizedBeforeCheck_peaceView_of_ppsi_frame
    hpsi kappa l r hrespLeader hrespLabel
  have hsend :
      (wallSweepAuthorizedBeforeCheck hpsi kappa l r).1.core.leader = true ∨
        (wallSweepAuthorizedBeforeCheck hpsi kappa l r).1.core.reset_cmd =
          true := by
    rcases hsource with hleader | hreset
    · exact .inl ((wallSweepAuthorizedBeforeCheck_initiator_leader_eq
        hpsi kappa l r).trans hleader)
    · exact .inr ((resetEcho_fields_of_pair_eq
        (wallSweepAuthorizedBeforeCheck_resetEchoPair hpsi kappa l r)).1.trans
          hreset)
  rw [wallSweepPreCheckResetBeforeSuppress_eq_checkTail]
  revert hbefore hsend
  generalize wallSweepAuthorizedBeforeCheck hpsi kappa l r = beforeRaw
  intro hbefore hsend
  exact ⟨preCheckResetCheckTail hpsi beforeRaw,
    preCheckResetWall beforeRaw.1 beforeRaw.2, beforeRaw, rfl,
    congrArg authorizedPeaceViewPair
      (preCheckResetCheckTail_eq_of_send hpsi beforeRaw hsend),
    (preCheckResetWall_peaceViewPair beforeRaw.1 beforeRaw.2).trans
      (authorizedPeaceViewPair_pair_eta beforeRaw),
    hbefore⟩

/-- Aligned-edge specialization of the generic source-covered prefix frame. -/
theorem wallSweepPreCheckResetBeforeSuppress_peaceFrame_of_aligned_source
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true) :
    AuthorizedPeaceFrame (l, r)
      (wallSweepPreCheckResetBeforeSuppress hpsi kappa l r) := by
  have hppsi := pPsiLeaderProbeWall_responder_frame_of_aligned
    hpsi l.core r.core halign
  exact wallSweepPreCheckResetBeforeSuppress_peaceFrame_of_ppsi_source
    hpsi kappa l r hppsi.1 hppsi.2 hsource

theorem beforeRaw_left_reset_true
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = true) :
    (wallSweepAuthorizedBeforeCheck hpsi kappa
      l r).1.core.reset_cmd = true := by
  exact (resetEcho_fields_of_pair_eq
    (wallSweepAuthorizedBeforeCheck_resetEchoPair hpsi kappa l r)).1.trans
      hlReset

/-- A responder label-zero leader reaches repaired Algorithm 14 whenever an
initiator reset covers the edge. -/
theorem wallSweepPreCheckResetBeforeSuppress_responder_zero_of_left_reset
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = true)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderZeroAnchor hpsi
      (wallSweepPreCheckResetBeforeSuppress hpsi kappa l r) := by
  have hraw := wallSweepAuthorizedBeforeCheck_responder_zero_anchor
    hpsi kappa l r h
  have hreset := beforeRaw_left_reset_true hpsi kappa l r hlReset
  rw [wallSweepPreCheckResetBeforeSuppress_eq_checkTail]
  revert hraw hreset
  generalize wallSweepAuthorizedBeforeCheck hpsi kappa l r = beforeRaw
  intro hraw hreset
  rw [preCheckResetCheckTail_eq_of_send hpsi beforeRaw (.inr hreset)]
  exact preCheckResetWall_responder_zero_anchor
    hpsi beforeRaw.1 beforeRaw.2 hraw

theorem wallSweepPreCheckResetBeforeSuppress_label_of_send
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hsend :
      let q := wallSweepAuthorizedBeforeCheck hpsi kappa l r
      q.1.core.leader = true ∨ q.1.core.reset_cmd = true) :
    (wallSweepPreCheckResetBeforeSuppress hpsi kappa l r).1.core.label =
      l.core.label := by
  have hrawLabel := wallSweepAuthorizedBeforeCheck_initiator_label_eq
    hpsi kappa l r
  rw [wallSweepPreCheckResetBeforeSuppress_eq_checkTail]
  revert hsend hrawLabel
  generalize wallSweepAuthorizedBeforeCheck hpsi kappa l r = beforeRaw
  intro hsend hrawLabel
  rw [preCheckResetCheckTail_eq_of_send hpsi beforeRaw hsend,
    preCheckResetWall_initiator_label_eq]
  exact hrawLabel


end PPLLWallSweepPreCheckResetContracts
