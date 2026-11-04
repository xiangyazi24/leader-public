import Leader.Wu.WallSweep.PreCheckResetContractsLeaderCleanup

/-!
# Pre-CHECK reset contracts: Output

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

/-- If the Algorithm-15/WRITE suffix starts with a follower initiator, its
final endpoints are not both leaders. -/
theorem authorizedPostSuppress_left_follower_not_both
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) :
    let q := authorizedPostSuppress hpsi l r
    ¬ (q.1.core.leader = true ∧ q.2.core.leader = true) := by
  dsimp only
  let q0 := authorizedReconcile
    (eliminateLeadersNoCollision hpsi) l r
  let q1 := authorizedReconcile
    (writeSeqIncrementGate hpsi) q0.1 q0.2
  have hq0Left : q0.1.core.leader = false := by
    cases hout : q0.1.core.leader
    · rfl
    · have hraw :
          (eliminateLeadersNoCollision hpsi l.core r.core).1.leader =
            true := by
        have hcore : q0.1.core =
            (eliminateLeadersNoCollision hpsi l.core r.core).1 := rfl
        exact (congrArg AgentState.leader hcore).symm.trans hout
      have horigin := eliminateLeadersNoCollision_initiator_origin
        hpsi l.core r.core hraw
      rw [hl] at horigin
      contradiction
  have hraw := writeSeqIncrementGate_left_follower_not_both
    hpsi q0.1.core q0.2.core hq0Left
  have hq1Leaders := authorizedReconcile_leaders_eq
    (writeSeqIncrementGate hpsi) q0.1 q0.2
  have hq1 : ¬ (q1.1.core.leader = true ∧
      q1.2.core.leader = true) := by
    rintro ⟨hleft, hright⟩
    apply hraw
    exact ⟨hq1Leaders.1.symm.trans hleft,
      hq1Leaders.2.symm.trans hright⟩
  have hstage : authorizedPostSuppress hpsi l r = q1 :=
    authorizedPostSuppress_eq_staged hpsi l r
  have hleft := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.1.core.leader) hstage
  have hright := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.leader) hstage
  rintro ⟨houtLeft, houtRight⟩
  apply hq1
  exact ⟨hleft.symm.trans houtLeft,
    hright.symm.trans houtRight⟩

/-- Replacing only the final Algorithm-15 signal guard cannot make the
post-suppression suffix duplicate a follower initiator into two leaders. -/
theorem authorizedPostSuppressLeaderSink_left_follower_not_both
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) :
    let q := authorizedPostSuppressLeaderSink hpsi l r
    ¬ (q.1.core.leader = true ∧ q.2.core.leader = true) := by
  dsimp only
  let q0 := authorizedReconcile
    (eliminateLeadersNoCollisionLeaderSink hpsi) l r
  let q1 := authorizedReconcile
    (writeSeqIncrementGate hpsi) q0.1 q0.2
  have hq0Left : q0.1.core.leader = false := by
    cases hout : q0.1.core.leader
    · rfl
    · have hrawNew :
          (eliminateLeadersNoCollisionLeaderSink
            hpsi l.core r.core).1.leader = true := by
        have hcore : q0.1.core =
            (eliminateLeadersNoCollisionLeaderSink
              hpsi l.core r.core).1 := rfl
        exact (congrArg AgentState.leader hcore).symm.trans hout
      have hleaderEq :=
        (eliminateLeadersNoCollisionLeaderSink_leaders_eq
          hpsi l.core r.core).1
      have hrawOld :
          (eliminateLeadersNoCollision hpsi l.core r.core).1.leader =
            true := hleaderEq.symm.trans hrawNew
      have horigin := eliminateLeadersNoCollision_initiator_origin
        hpsi l.core r.core hrawOld
      rw [hl] at horigin
      contradiction
  have hraw := writeSeqIncrementGate_left_follower_not_both
    hpsi q0.1.core q0.2.core hq0Left
  have hq1Leaders := authorizedReconcile_leaders_eq
    (writeSeqIncrementGate hpsi) q0.1 q0.2
  have hq1 : ¬ (q1.1.core.leader = true ∧
      q1.2.core.leader = true) := by
    rintro ⟨hleft, hright⟩
    apply hraw
    exact ⟨hq1Leaders.1.symm.trans hleft,
      hq1Leaders.2.symm.trans hright⟩
  change ¬ (q1.1.core.leader = true ∧ q1.2.core.leader = true)
  exact hq1

/-- The complete ordinary normal tail cannot return two leaders when its input
initiator is a follower. -/
theorem wallSweepPreCheckResetNormalTail_left_follower_not_both
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) :
    let q := wallSweepPreCheckResetNormalTail hpsi kappa l r
    ¬ (q.1.core.leader = true ∧ q.2.core.leader = true) := by
  dsimp only
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hafter :=
    wallSweepPreCheckResetNormalAfterSuppress_initiator_leader_eq
      hpsi kappa l r
  have hafterFalse : after.1.core.leader = false := hafter.trans hl
  have hpost : ¬ ((authorizedPostSuppress hpsi after.1 after.2).1.core.leader =
      true ∧
    (authorizedPostSuppress hpsi after.1 after.2).2.core.leader = true) :=
    authorizedPostSuppress_left_follower_not_both
      hpsi after.1 after.2 hafterFalse
  have heq : wallSweepPreCheckResetNormalTail hpsi kappa l r =
      authorizedPostSuppress hpsi after.1 after.2 :=
    normalTail_eq_postSuppress hpsi kappa l r
  have hleft := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.1.core.leader) heq
  have hright := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.leader) heq
  rintro ⟨houtLeft, houtRight⟩
  apply hpost
  exact ⟨hleft.symm.trans houtLeft,
    hright.symm.trans houtRight⟩

/-- The rooted leader-sink normal tail also cannot return two leaders from a
follower initiator. -/
theorem wallSweepPreCheckResetLeaderSinkNormalTail_left_follower_not_both
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) :
    let q := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
    ¬ (q.1.core.leader = true ∧ q.2.core.leader = true) := by
  dsimp only
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hafter :=
    wallSweepPreCheckResetNormalAfterSuppress_initiator_leader_eq
      hpsi kappa l r
  have hafterFalse : after.1.core.leader = false := hafter.trans hl
  have hpost : ¬ ((authorizedPostSuppressLeaderSink
        hpsi after.1 after.2).1.core.leader = true ∧
      (authorizedPostSuppressLeaderSink
        hpsi after.1 after.2).2.core.leader = true) :=
    authorizedPostSuppressLeaderSink_left_follower_not_both
      hpsi after.1 after.2 hafterFalse
  have heq : wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r =
      authorizedPostSuppressLeaderSink hpsi after.1 after.2 := rfl
  have hleft := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.1.core.leader) heq
  have hright := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.leader) heq
  rintro ⟨houtLeft, houtRight⟩
  apply hpost
  exact ⟨hleft.symm.trans houtLeft,
    hright.symm.trans houtRight⟩

structure AuthorizedInitiatorCheckMigration
    (hpsi : psi > 0)
    (beforeCheck afterCheck beforeWrite out :
      AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  beforeCheckFollower : beforeCheck.2.core.leader = false
  afterCheckBirth :
    afterCheck.2.core.leader = true ∧
      afterCheck.2.core.label = ⟨psi - 1, by omega⟩ ∧
      afterCheck.2.core.state = .equal
  beforeWriteSource :
    beforeWrite.1.core.leader = false ∧
      beforeWrite.2.core.leader = true ∧
      beforeWrite.2.core.label = ⟨psi - 1, by omega⟩ ∧
      beforeWrite.2.core.label ≠ ⟨0, hpsi⟩
  outputResponder :
    out.2.core.leader = false ∧
      out.2.core.label = ⟨psi - 1, by omega⟩

/-- Exact source of a new initiator leader on the repaired priority-open
leader-sink branch.  It was born at CHECK on the responder in terminal
`.equal` at label `psi - 1`, survives unchanged to WRITE, and is then migrated
to the initiator while the responder becomes a follower at the same label. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_new_initiator_check_migration
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hout : (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r).1.core.leader = true) :
    AuthorizedInitiatorCheckMigration hpsi
      (wallSweepPreCheckResetBeforeCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))
      (wallSweepPreCheckResetAfterCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))
      (wallSweepPreCheckResetLeaderSinkBeforeWrite hpsi kappa l r)
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeCheck := wallSweepPreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let afterCheck := wallSweepPreCheckResetAfterCheck
    hpsi kappa l0 r0
  let born := leaderBirthBeforeOrAtCheck
    l0 r0 beforeCheck afterCheck
  let afterSuppress :=
    wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let beforeWrite :=
    wallSweepPreCheckResetLeaderSinkBeforeWrite hpsi kappa l r
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  have heq :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change out = markLeaderBirth born tail at heq
  have hmarkLeaders := markLeaderBirth_leaders_eq born tail
  have hmarkLabels := markLeaderBirth_labels_eq born tail
  have heqLeft := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.1.core.leader) heq
  have heqRightLeader := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.leader) heq
  have heqRightLabel := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.label) heq
  have htailLeft : tail.1.core.leader = true :=
    hmarkLeaders.1.symm.trans (heqLeft.symm.trans hout)
  have hafterLeft : afterSuppress.1.core.leader = false :=
    (wallSweepPreCheckResetNormalAfterSuppress_initiator_leader_eq
      hpsi kappa l r).trans hl
  have hmigration := authorizedPostSuppressLeaderSink_new_initiator_migration
    hpsi afterSuppress.1 afterSuppress.2 hafterLeft htailLeft
  change beforeWrite.1.core.leader = false ∧
    beforeWrite.2.core.leader = true ∧
    beforeWrite.2.core.label ≠ ⟨0, hpsi⟩ ∧
    tail.2.core.leader = false ∧
    tail.2.core.label = beforeWrite.2.core.label at hmigration
  have hframe :=
    wallSweepPreCheckResetLeaderSink_beforeWrite_responder_frame_afterCheck
      hpsi kappa l r
  have hafterCheckLeader : afterCheck.2.core.leader = true :=
    hframe.leader_eq.symm.trans hmigration.2.1
  have hafterCheckStage : afterCheck = authorizedCheckSig hpsi
      beforeCheck.1 beforeCheck.2 := by
    rfl
  have hafterCheckStageLeader := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.leader) hafterCheckStage
  have hafterCheckStageLabel := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.label) hafterCheckStage
  have hafterCheckStageState := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.state) hafterCheckStage
  have hbeforeCheckFollower : beforeCheck.2.core.leader = false := by
    cases hbc : beforeCheck.2.core.leader
    · rfl
    · exfalso
      have hl0 : l0.core.leader = false :=
        (normalizeDeletion_leader_eq l).trans hl
      have hr0 : r0.core.leader = false :=
        (normalizeDeletion_leader_eq r).trans hr
      have hbcDirect :
          (wallSweepPreCheckResetBeforeCheck hpsi kappa
            l0 r0).2.core.leader = true := by
        simpa only [beforeCheck] using hbc
      have hzero := wallSweepPreCheckReset_beforeCheck_new_responder_zero
        hpsi kappa l0 r0 hl0 hr0 { leader_eq := hbcDirect }
      have hzeroLabel : beforeCheck.2.core.label = ⟨0, hpsi⟩ := by
        simpa only [beforeCheck] using hzero.label_eq
      have hcheckLabel : afterCheck.2.core.label =
          beforeCheck.2.core.label :=
        hafterCheckStageLabel.trans (PPLLVerify.checkSig_labels_eq
          hpsi beforeCheck.1.core beforeCheck.2.core).2
      exact hmigration.2.2.1
        (hframe.label_eq.trans (hcheckLabel.trans hzeroLabel))
  have hrawAfterCheck :
      (checkSig hpsi
        beforeCheck.1.core beforeCheck.2.core).2.leader = true :=
    hafterCheckStageLeader.symm.trans hafterCheckLeader
  have hterminal :=
    PPLLVerify.checkSig_new_responder_leader_requires_terminal_equal
      hpsi beforeCheck.1.core beforeCheck.2.core
        hrawAfterCheck hbeforeCheckFollower
  have hafterCheckLabel : afterCheck.2.core.label =
      ⟨psi - 1, by omega⟩ :=
    hafterCheckStageLabel.trans hterminal.1
  have hafterCheckState : afterCheck.2.core.state = .equal :=
    hafterCheckStageState.trans hterminal.2
  have hbeforeWriteLabel : beforeWrite.2.core.label =
      ⟨psi - 1, by omega⟩ := hframe.label_eq.trans hafterCheckLabel
  have houtRightFollower : out.2.core.leader = false :=
    heqRightLeader.trans
      (hmarkLeaders.2.trans hmigration.2.2.2.1)
  have houtRightLabel : out.2.core.label =
      ⟨psi - 1, by omega⟩ :=
    heqRightLabel.trans (hmarkLabels.2.trans
      (hmigration.2.2.2.2.trans hbeforeWriteLabel))
  have hcertificate : AuthorizedInitiatorCheckMigration hpsi
      beforeCheck afterCheck beforeWrite out := {
    beforeCheckFollower := hbeforeCheckFollower
    afterCheckBirth :=
      ⟨hafterCheckLeader, hafterCheckLabel, hafterCheckState⟩
    beforeWriteSource :=
      ⟨hmigration.1, hmigration.2.1, hbeforeWriteLabel,
        hmigration.2.2.1⟩
    outputResponder := ⟨houtRightFollower, houtRightLabel⟩ }
  simpa only [beforeCheck, afterCheck, beforeWrite, out, l0, r0]
    using hcertificate

structure ExpiringInitiatorCheckMigration
    (hpsi : psi > 0)
    (beforeCheck afterCheck beforeWrite authorizedOut :
      AuthorizedAgentState psi × AuthorizedAgentState psi)
    (out : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop where
  authorized : AuthorizedInitiatorCheckMigration hpsi
    beforeCheck afterCheck beforeWrite authorizedOut
  outputResponder :
    out.2.core.erase.core.leader = false ∧
      out.2.core.erase.core.label = ⟨psi - 1, by omega⟩

/-- Bounded reification and the two expiry stages preserve the complete CHECK
migration certificate and its final responder follower/label fields. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_new_initiator_check_migration
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hl : l.core.erase.core.leader = false)
    (hr : r.core.erase.core.leader = false)
    (hout : (wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r).1.core.erase.core.leader = true) :
    ExpiringInitiatorCheckMigration hpsi
      (wallSweepPreCheckResetBeforeCheck hpsi kappa
        (normalizeDeletion l.core.erase)
        (normalizeDeletion r.core.erase))
      (wallSweepPreCheckResetAfterCheck hpsi kappa
        (normalizeDeletion l.core.erase)
        (normalizeDeletion r.core.erase))
      (wallSweepPreCheckResetLeaderSinkBeforeWrite hpsi kappa
        l.core.erase r.core.erase)
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l.core.erase r.core.erase)
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  let authorizedOut :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let pathOut := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau l r
  have hstages :=
    wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages
      hpsi kappa tau l r
  change pathOut =
    (deletionPriorityExpireOne tau l lBase,
      deletionPriorityExpireOne tau r rBase) at hstages
  have hpathLeft := congrArg
    (fun q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau => q.1.core.erase.core.leader)
    hstages
  have hpathRightLeader := congrArg
    (fun q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau => q.2.core.erase.core.leader)
    hstages
  have hpathRightLabel := congrArg
    (fun q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau => q.2.core.erase.core.label)
    hstages
  have hLf := deletionPriorityExpireOne_path_frame l lBase
  have hRf := deletionPriorityExpireOne_path_frame r rBase
  have herase := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst herase
  have hR := congrArg Prod.snd herase
  change bounded.1.erase = authorizedOut.1 at hL
  change bounded.2.erase = authorizedOut.2 at hR
  have hfinalLeft :
      (deletionPriorityExpireOne tau l lBase).core.erase.core.leader = true :=
    hpathLeft.symm.trans hout
  have hbaseLeft : bounded.1.erase.core.leader = true :=
    hLf.2.1.symm.trans hfinalLeft
  have haLeft : authorizedOut.1.core.leader = true :=
    (congrArg
      (fun u : AuthorizedAgentState psi => u.core.leader) hL).symm.trans
        hbaseLeft
  have ha :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_new_initiator_check_migration
      hpsi kappa l.core.erase r.core.erase hopen hl hr haLeft
  have hfinalRightLeader : pathOut.2.core.erase.core.leader = false :=
    hpathRightLeader.trans (hRf.2.1.trans ((congrArg
      (fun u : AuthorizedAgentState psi => u.core.leader) hR).trans
        ha.outputResponder.1))
  have hfinalRightLabel : pathOut.2.core.erase.core.label =
      ⟨psi - 1, by omega⟩ :=
    hpathRightLabel.trans (hRf.2.2.1.trans ((congrArg
      (fun u : AuthorizedAgentState psi => u.core.label) hR).trans
        ha.outputResponder.2))
  have hcertificate : ExpiringInitiatorCheckMigration hpsi
      (wallSweepPreCheckResetBeforeCheck hpsi kappa
        (normalizeDeletion l.core.erase)
        (normalizeDeletion r.core.erase))
      (wallSweepPreCheckResetAfterCheck hpsi kappa
        (normalizeDeletion l.core.erase)
        (normalizeDeletion r.core.erase))
      (wallSweepPreCheckResetLeaderSinkBeforeWrite hpsi kappa
        l.core.erase r.core.erase)
      authorizedOut pathOut := {
    authorized := ha
    outputResponder := ⟨hfinalRightLeader, hfinalRightLabel⟩ }
  simpa only [authorizedOut, pathOut] using hcertificate

/-- On a priority-open edge with a follower initiator, the rooted leader-sink
transition cannot finish with two leaders.  The responder may already be a
leader: the only suffix operation that can move it to the initiator clears the
responder in the same atomic WRITE step. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_left_follower_not_both
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hl : l.core.leader = false) :
    let q := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    ¬ (q.1.core.leader = true ∧ q.2.core.leader = true) := by
  dsimp only
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  have heq :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r = markLeaderBirth born tail at heq
  have htail :=
    wallSweepPreCheckResetLeaderSinkNormalTail_left_follower_not_both
      hpsi kappa l r hl
  have hmark := markLeaderBirth_leaders_eq born tail
  have heqLeft := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.1.core.leader) heq
  have heqRight := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.leader) heq
  rintro ⟨hleft, hright⟩
  apply htail
  exact ⟨hmark.1.symm.trans (heqLeft.symm.trans hleft),
    hmark.2.symm.trans (heqRight.symm.trans hright)⟩

/-- Follower/follower specialization of the stronger follower-initiator
contract retained for existing consumers. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_followers_not_both
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hl : l.core.leader = false)
    (_hr : r.core.leader = false) :
    let q := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    ¬ (q.1.core.leader = true ∧ q.2.core.leader = true) := by
  exact
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_left_follower_not_both
      hpsi kappa l r hopen hl


end PPLLWallSweepPreCheckResetContracts
