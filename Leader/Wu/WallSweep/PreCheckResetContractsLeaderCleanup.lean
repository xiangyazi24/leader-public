import Leader.Wu.WallSweep.PreCheckResetContractsAuthorizedBullet

/-!
# Pre-CHECK reset contracts: LeaderCleanup

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

/-- The rooted leader-sink Algorithm-15/WRITE suffix preserves the exact
cleanup produced by an existing leader at repaired Algorithm 14. -/
theorem wallSweepPreCheckResetLeaderSinkNormalTail_leader_source_cleanup
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true) :
    AuthorizedLeaderSourceCleanup (l, r)
      (wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r) := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  change AuthorizedLeaderSourceCleanup (l, r)
    (authorizedPostSuppressLeaderSink hpsi after.1 after.2)
  exact authorizedPostSuppressLeaderSink_leader_source_cleanup
    hpsi (l, r) after
      (wallSweepPreCheckResetNormalAfterSuppress_leader_source_cleanup
        hpsi kappa l r hlLeader)

/-- A priority-open complete rooted leader-sink edge sourced by an existing
leader clears both endpoint comparisons and echoes.  Reset reaches the
responder exactly when its input echo was absent. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_leader_source_cleanup
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlLeader : l.core.leader = true) :
    AuthorizedLeaderSourceCleanup (l, r)
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r) := by
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  have htail :=
    wallSweepPreCheckResetLeaderSinkNormalTail_leader_source_cleanup
      hpsi kappa l r hlLeader
  have hmark := markLeaderBirth_eq_of_neutral
    (leaderBirthBeforeOrAtCheck
      (normalizeDeletion l) (normalizeDeletion r)
      (wallSweepPreCheckResetBeforeCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))
      (wallSweepPreCheckResetAfterCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r)))
    tail htail.1 htail.2.1
  have hstage :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  exact AuthorizedLeaderSourceCleanup.of_pair_eq
    (hstage.trans hmark) htail

/-- A surviving initiating leader leaves the complete priority-open output
collision-safe for replay of the same outgoing edge. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_survivor_safe
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlLeader : l.core.leader = true)
    (hrFollower : r.core.leader = false)
    (houtLeader :
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r).1.core.leader = true) :
    (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r).2.core.bullet = ⟨2, by omega⟩ →
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r).1.core.shield = true := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  have hstage :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  let born := leaderBirthBeforeOrAtCheck
    (normalizeDeletion l) (normalizeDeletion r)
    (wallSweepPreCheckResetBeforeCheck hpsi kappa
      (normalizeDeletion l) (normalizeDeletion r))
    (wallSweepPreCheckResetAfterCheck hpsi kappa
      (normalizeDeletion l) (normalizeDeletion r))
  change out = markLeaderBirth born tail at hstage
  have hmarkLeaders := markLeaderBirth_leaders_eq born tail
  have hstageLeader := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.1.core.leader) hstage
  have htailLeader : tail.1.core.leader = true :=
    hmarkLeaders.1.symm.trans (hstageLeader.symm.trans houtLeader)
  have hafterLeader : after.1.core.leader = true :=
    (wallSweepPreCheckResetNormalAfterSuppress_initiator_leader_eq
      hpsi kappa l r).trans hlLeader
  have hafterFollower : after.2.core.leader = false :=
    (wallSweepPreCheckResetNormalAfterSuppress_responder_leader_eq_of_initiator_leader
      hpsi kappa l r hlLeader).trans hrFollower
  have htailSafe := authorizedPostSuppressLeaderSink_survivor_safe
    hpsi after.1 after.2 hafterLeader hafterFollower htailLeader
  have houtFields : authorizedBulletFieldPair out =
      authorizedBulletFieldPair tail :=
    (congrArg authorizedBulletFieldPair hstage).trans
      (markLeaderBirth_bulletFieldPair born tail)
  have hleftShield := congrArg (fun q => q.1.shield) houtFields
  have hrightBullet := congrArg (fun q => q.2.bullet) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair
    BulletFields.ofState at hleftShield hrightBullet
  dsimp only at hleftShield hrightBullet
  intro houtBullet
  have htailBullet : tail.2.core.bullet = ⟨2, by omega⟩ :=
    hrightBullet.symm.trans houtBullet
  exact hleftShield.trans (htailSafe htailBullet)

/-- A live follower responder remains live through the complete priority-open
rooted transition whenever the initiating leader survives. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_survivor_preserves_responder_live
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlLeader : l.core.leader = true)
    (hrFollower : r.core.leader = false)
    (hrLive : r.core.bullet = ⟨2, by omega⟩)
    (houtLeader :
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r).1.core.leader = true) :
    (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r).2.core.bullet = ⟨2, by omega⟩ := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  have hstage :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  let born := leaderBirthBeforeOrAtCheck
    (normalizeDeletion l) (normalizeDeletion r)
    (wallSweepPreCheckResetBeforeCheck hpsi kappa
      (normalizeDeletion l) (normalizeDeletion r))
    (wallSweepPreCheckResetAfterCheck hpsi kappa
      (normalizeDeletion l) (normalizeDeletion r))
  change out = markLeaderBirth born tail at hstage
  have hmarkLeaders := markLeaderBirth_leaders_eq born tail
  have hstageLeader := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.1.core.leader) hstage
  have htailLeader : tail.1.core.leader = true :=
    hmarkLeaders.1.symm.trans (hstageLeader.symm.trans houtLeader)
  have hafterLeader : after.1.core.leader = true :=
    (wallSweepPreCheckResetNormalAfterSuppress_initiator_leader_eq
      hpsi kappa l r).trans hlLeader
  have hafterFollower : after.2.core.leader = false :=
    (wallSweepPreCheckResetNormalAfterSuppress_responder_leader_eq_of_initiator_leader
      hpsi kappa l r hlLeader).trans hrFollower
  have hafterFields : authorizedBulletFieldPair after =
      authorizedBulletFieldPair (l, r) :=
    wallSweepPreCheckResetNormalAfterSuppress_bulletFieldPair
      hpsi kappa l r
  have hafterRightBullet := congrArg (fun q => q.2.bullet) hafterFields
  unfold authorizedBulletFieldPair bulletFieldPair
    BulletFields.ofState at hafterRightBullet
  dsimp only at hafterRightBullet
  have hafterLive : after.2.core.bullet = ⟨2, by omega⟩ :=
    hafterRightBullet.trans hrLive
  have htailLive :=
    authorizedPostSuppressLeaderSink_survivor_preserves_responder_live
      hpsi after.1 after.2 hafterLeader hafterFollower
        hafterLive htailLeader
  have houtFields : authorizedBulletFieldPair out =
      authorizedBulletFieldPair tail :=
    (congrArg authorizedBulletFieldPair hstage).trans
      (markLeaderBirth_bulletFieldPair born tail)
  have hrightBullet := congrArg (fun q => q.2.bullet) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair
    BulletFields.ofState at hrightBullet
  dsimp only at hrightBullet
  exact hrightBullet.trans htailLive

/-- If an initiating leader is killed on a priority-open edge with a follower
responder, the complete authorized transition strictly consumes one live
bullet. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_initiator_killed_bulletTwoPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlLeader : l.core.leader = true)
    (hrFollower : r.core.leader = false)
    (houtFollower :
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r).1.core.leader = false) :
    let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    AuthorizedBulletTwoPairDecrease (l, r) out := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  have hstage :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  have hstageLeader := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.1.core.leader) hstage
  have hstageRightLeader := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.leader) hstage
  have hmarkLeaders := markLeaderBirth_leaders_eq
    (leaderBirthBeforeOrAtCheck
      (normalizeDeletion l) (normalizeDeletion r)
      (wallSweepPreCheckResetBeforeCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))
      (wallSweepPreCheckResetAfterCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))) tail
  have htailFollower : tail.1.core.leader = false :=
    hmarkLeaders.1.symm.trans (hstageLeader.symm.trans houtFollower)
  have hhit :=
    wallSweepPreCheckResetLeaderSinkNormalTail_live_hit_of_initiator_killed
      hpsi kappa l r hlLeader hrFollower htailFollower
  have hstageFields := congrArg authorizedBulletFieldPair hstage
  have houtFields : authorizedBulletFieldPair out =
      authorizedBulletFieldPair tail :=
    hstageFields.trans (markLeaderBirth_bulletFieldPair _ tail)
  have houtLeft := congrArg (fun q => q.1.bullet) houtFields
  have houtRight := congrArg (fun q => q.2.bullet) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at houtLeft
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at houtRight
  dsimp only at houtLeft houtRight
  have hafterFields : authorizedBulletFieldPair after =
      authorizedBulletFieldPair (l, r) :=
    wallSweepPreCheckResetNormalAfterSuppress_bulletFieldPair
      hpsi kappa l r
  have hafterLeft := congrArg (fun q => q.1.bullet) hafterFields
  have hafterRight := congrArg (fun q => q.2.bullet) hafterFields
  have hafterLeftShield := congrArg (fun q => q.1.shield) hafterFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hafterLeft
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hafterRight
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hafterLeftShield
  dsimp only at hafterLeft hafterRight hafterLeftShield
  have houtLeftInput : out.1.core.bullet = l.core.bullet :=
    houtLeft.trans (hhit.outputInitiatorBullet.trans hafterLeft)
  have houtRightDummy : out.2.core.bullet = ⟨1, by omega⟩ :=
    houtRight.trans hhit.outputResponderDummy
  have hinputRightLive : r.core.bullet = ⟨2, by omega⟩ :=
    hafterRight.symm.trans hhit.responderLive
  have hinputLeftUnshielded : l.core.shield = false :=
    hafterLeftShield.symm.trans hhit.sourceUnshielded
  refine {
    lt := ?_
    inputInitiatorUnshielded := hinputLeftUnshielded
    inputResponderLive := hinputRightLive
    outputInitiatorFollower := houtFollower
    outputResponderFollower :=
      hstageRightLeader.trans
        (hmarkLeaders.2.trans hhit.outputResponderFollower) }
  · unfold bulletTwoPairMass bulletTwoMass
    rw [houtLeftInput, houtRightDummy, hinputRightLive]
    simp

/-- Before and through rooted Algorithm 15, a follower initiator cannot gain
live-bullet mass. -/
theorem
    wallSweepPreCheckResetLeaderSink_left_follower_raw_bulletTwoPair_le
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false) :
    let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
    let raw := eliminateLeadersNoCollisionLeaderSink
      hpsi after.1.core after.2.core
    bulletTwoPairMass raw.1 raw.2 ≤
      bulletTwoPairMass l.core r.core := by
  let after : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let raw : AgentState psi × AgentState psi :=
    eliminateLeadersNoCollisionLeaderSink
      hpsi after.1.core after.2.core
  have hafterFollower : after.1.core.leader = false :=
    (wallSweepPreCheckResetNormalAfterSuppress_initiator_leader_eq
      hpsi kappa l r).trans hlFollower
  have hkernel :=
    eliminateLeadersNoCollisionLeaderSink_left_follower_bulletTwoPair_le
      hpsi after.1.core after.2.core hafterFollower
  change bulletTwoPairMass raw.1 raw.2 ≤
    bulletTwoPairMass after.1.core after.2.core at hkernel
  have hafterFields : authorizedBulletFieldPair after =
      authorizedBulletFieldPair (l, r) :=
    wallSweepPreCheckResetNormalAfterSuppress_bulletFieldPair
      hpsi kappa l r
  have hafterL := congrArg (fun q => q.1.bullet) hafterFields
  have hafterR := congrArg (fun q => q.2.bullet) hafterFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hafterL hafterR
  dsimp only at hafterL hafterR
  have hmass : bulletTwoPairMass after.1.core after.2.core =
      bulletTwoPairMass l.core r.core :=
    bulletTwoPairMass_eq_of_bullets_eq hafterL hafterR
  calc
    bulletTwoPairMass raw.1 raw.2 ≤
        bulletTwoPairMass after.1.core after.2.core := hkernel
    _ = bulletTwoPairMass l.core r.core := hmass

/-- Before and through rooted Algorithm 15, a leader initiator whose absence
signal is already zero cannot gain live-bullet mass.  The pre-CHECK prefix
frames the leader bit, absence signal, and both bullets. -/
theorem
    wallSweepPreCheckResetLeaderSink_left_leader_signal_zero_raw_bulletTwoPair_le
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true)
    (hlSignalZero : l.core.signal_B = ⟨0, by omega⟩) :
    let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
    let raw := eliminateLeadersNoCollisionLeaderSink
      hpsi after.1.core after.2.core
    bulletTwoPairMass raw.1 raw.2 ≤
      bulletTwoPairMass l.core r.core := by
  let after : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let raw : AgentState psi × AgentState psi :=
    eliminateLeadersNoCollisionLeaderSink
      hpsi after.1.core after.2.core
  have hafterLeader : after.1.core.leader = true :=
    (wallSweepPreCheckResetNormalAfterSuppress_initiator_leader_eq
      hpsi kappa l r).trans hlLeader
  have hafterFields : authorizedBulletFieldPair after =
      authorizedBulletFieldPair (l, r) :=
    wallSweepPreCheckResetNormalAfterSuppress_bulletFieldPair
      hpsi kappa l r
  have hafterSignal := congrArg (fun q => q.1.signal_B) hafterFields
  have hafterL := congrArg (fun q => q.1.bullet) hafterFields
  have hafterR := congrArg (fun q => q.2.bullet) hafterFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hafterSignal hafterL hafterR
  dsimp only at hafterSignal hafterL hafterR
  have hkernel :=
    eliminateLeadersNoCollisionLeaderSink_left_leader_signal_zero_bulletTwoPair_le
      hpsi after.1.core after.2.core hafterLeader
        (hafterSignal.trans hlSignalZero)
  change bulletTwoPairMass raw.1 raw.2 ≤
    bulletTwoPairMass after.1.core after.2.core at hkernel
  have hmass : bulletTwoPairMass after.1.core after.2.core =
      bulletTwoPairMass l.core r.core :=
    bulletTwoPairMass_eq_of_bullets_eq hafterL hafterR
  calc
    bulletTwoPairMass raw.1 raw.2 ≤
        bulletTwoPairMass after.1.core after.2.core := hkernel
    _ = bulletTwoPairMass l.core r.core := hmass

/-- On a priority-open edge with a follower initiator, one complete rooted
pre-CHECK-reset interaction cannot increase the number of live bullets on
the active pair. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_left_follower_bulletTwoPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlFollower : l.core.leader = false) :
    let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    AuthorizedBulletTwoPairNonincrease (l, r) out := by
  let after : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let raw : AgentState psi × AgentState psi :=
    eliminateLeadersNoCollisionLeaderSink
      hpsi after.1.core after.2.core
  let out : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition hpsi kappa l r
  refine { le := ?_ }
  change bulletTwoPairMass out.1.core out.2.core ≤
    bulletTwoPairMass l.core r.core
  have hfields : authorizedBulletFieldPair out =
      bulletFieldPair raw :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_bulletFieldPair
      hpsi kappa l r hopen
  have hrawLe : bulletTwoPairMass raw.1 raw.2 ≤
      bulletTwoPairMass l.core r.core :=
    wallSweepPreCheckResetLeaderSink_left_follower_raw_bulletTwoPair_le
      hpsi kappa l r hlFollower
  have houtL := congrArg (fun q => q.1.bullet) hfields
  have houtR := congrArg (fun q => q.2.bullet) hfields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at houtL houtR
  dsimp only at houtL houtR
  have hmass : bulletTwoPairMass out.1.core out.2.core =
      bulletTwoPairMass raw.1 raw.2 :=
    bulletTwoPairMass_eq_of_bullets_eq houtL houtR
  calc
    bulletTwoPairMass out.1.core out.2.core =
        bulletTwoPairMass raw.1 raw.2 := hmass
    _ ≤ bulletTwoPairMass l.core r.core := hrawLe

/-- On a priority-open edge with a zero-signal leader initiator, one complete
rooted pre-CHECK-reset interaction cannot increase live-bullet mass on the
active pair. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_left_leader_signal_zero_bulletTwoPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlLeader : l.core.leader = true)
    (hlSignalZero : l.core.signal_B = ⟨0, by omega⟩) :
    let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    AuthorizedBulletTwoPairNonincrease (l, r) out := by
  let after : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let raw : AgentState psi × AgentState psi :=
    eliminateLeadersNoCollisionLeaderSink
      hpsi after.1.core after.2.core
  let out : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition hpsi kappa l r
  refine { le := ?_ }
  change bulletTwoPairMass out.1.core out.2.core ≤
    bulletTwoPairMass l.core r.core
  have hfields : authorizedBulletFieldPair out =
      bulletFieldPair raw :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_bulletFieldPair
      hpsi kappa l r hopen
  have hrawLe : bulletTwoPairMass raw.1 raw.2 ≤
      bulletTwoPairMass l.core r.core :=
    wallSweepPreCheckResetLeaderSink_left_leader_signal_zero_raw_bulletTwoPair_le
      hpsi kappa l r hlLeader hlSignalZero
  have houtL := congrArg (fun q => q.1.bullet) hfields
  have houtR := congrArg (fun q => q.2.bullet) hfields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at houtL houtR
  dsimp only at houtL houtR
  have hmass : bulletTwoPairMass out.1.core out.2.core =
      bulletTwoPairMass raw.1 raw.2 :=
    bulletTwoPairMass_eq_of_bullets_eq houtL houtR
  calc
    bulletTwoPairMass out.1.core out.2.core =
        bulletTwoPairMass raw.1 raw.2 := hmass
    _ ≤ bulletTwoPairMass l.core r.core := hrawLe

/-- On the reset-aware follower/reset/follower edge used by a clockwise
normalization pass, one complete priority-open interaction cannot increase
the active pair's live-bullet mass. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_priority_open_reset_follower_bulletTwoPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false) :
    let out := wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    AuthorizedBulletTwoPairNonincrease (l, r) out := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeCheck := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let afterCheck := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  let tail := wallSweepLeaderSinkAfterCheckSuffix
    hpsi afterCheck.1 afterCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let out := wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  have hl0Follower : l0.core.leader = false :=
    (normalizeDeletion_leader_eq l).trans hlFollower
  have hr0Follower : r0.core.leader = false :=
    (normalizeDeletion_leader_eq r).trans hrFollower
  have hnormalizeReset := normalizeDeletionPair_resetEcho l r
  have hl0Reset : l0.core.reset_cmd = true :=
    (resetEcho_fields_of_pair_eq hnormalizeReset).1.trans hlReset
  have hafterFollowers : afterCheck.1.core.leader = false ∧
      afterCheck.2.core.leader = false :=
    wallSweepResetProbePreCheckResetAfterCheck_followers_of_reset_source
      hpsi kappa l0 r0 hl0Follower hl0Reset hr0Follower
  have htailLe : bulletTwoPairMass tail.1.core tail.2.core ≤
      bulletTwoPairMass afterCheck.1.core afterCheck.2.core :=
    wallSweepLeaderSinkAfterCheckSuffix_left_follower_bulletTwoPair_le
      hpsi afterCheck.1 afterCheck.2 hafterFollowers.1
  have hafter0 : authorizedBulletFieldPair afterCheck =
      authorizedBulletFieldPair (l0, r0) :=
    wallSweepResetProbePreCheckResetAfterCheck_bulletFieldPair
      hpsi kappa l0 r0
  have hnormalizeFields : authorizedBulletFieldPair (l0, r0) =
      authorizedBulletFieldPair (l, r) :=
    Prod.ext (normalizeDeletion_bulletFields l)
      (normalizeDeletion_bulletFields r)
  have hafterFields : authorizedBulletFieldPair afterCheck =
      authorizedBulletFieldPair (l, r) :=
    hafter0.trans hnormalizeFields
  have hafterL := congrArg (fun q => q.1.bullet) hafterFields
  have hafterR := congrArg (fun q => q.2.bullet) hafterFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hafterL hafterR
  dsimp only at hafterL hafterR
  have hafterMass : bulletTwoPairMass afterCheck.1.core afterCheck.2.core =
      bulletTwoPairMass l.core r.core :=
    bulletTwoPairMass_eq_of_bullets_eq hafterL hafterR
  have hstage :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_marked_suffix_of_priority_open
      hpsi kappa l r hopen
  change out = markLeaderBirth born tail at hstage
  have houtFields : authorizedBulletFieldPair out =
      authorizedBulletFieldPair tail :=
    (congrArg authorizedBulletFieldPair hstage).trans
      (markLeaderBirth_bulletFieldPair born tail)
  have houtL := congrArg (fun q => q.1.bullet) houtFields
  have houtR := congrArg (fun q => q.2.bullet) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at houtL houtR
  dsimp only at houtL houtR
  have houtMass : bulletTwoPairMass out.1.core out.2.core =
      bulletTwoPairMass tail.1.core tail.2.core :=
    bulletTwoPairMass_eq_of_bullets_eq houtL houtR
  refine { le := ?_ }
  calc
    bulletTwoPairMass out.1.core out.2.core =
        bulletTwoPairMass tail.1.core tail.2.core := houtMass
    _ ≤ bulletTwoPairMass afterCheck.1.core afterCheck.2.core := htailLe
    _ = bulletTwoPairMass l.core r.core := hafterMass

/-- The complete priority-open reset-aware follower step either advances a
positive absence signal or moves the unique local obstruction, a dummy
bullet, one edge counterclockwise.  The reset-aware prefix supplies alignment
without assuming it at the input edge. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_priority_open_signal_or_dummy_moves
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false)
    (hlSignal : l.core.signal_B = ⟨1, by omega⟩)
    (hrNotLive : r.core.bullet ≠ ⟨2, by omega⟩) :
    let out :=
      wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r
    out.2.core.signal_B = ⟨1, by omega⟩ ∨
      (r.core.bullet = ⟨1, by omega⟩ ∧
        out.1.core.bullet = ⟨1, by omega⟩ ∧
        out.2.core.bullet = ⟨0, by omega⟩) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let afterCheck := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  let tail := wallSweepLeaderSinkAfterCheckSuffix
    hpsi afterCheck.1 afterCheck.2
  let out :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
  have hl0Follower : l0.core.leader = false :=
    (normalizeDeletion_leader_eq l).trans hlFollower
  have hr0Follower : r0.core.leader = false :=
    (normalizeDeletion_leader_eq r).trans hrFollower
  have hnormalizeReset := normalizeDeletionPair_resetEcho l r
  have hl0Reset : l0.core.reset_cmd = true :=
    (resetEcho_fields_of_pair_eq hnormalizeReset).1.trans hlReset
  have hafterFollowers : afterCheck.1.core.leader = false ∧
      afterCheck.2.core.leader = false :=
    wallSweepResetProbePreCheckResetAfterCheck_followers_of_reset_source
      hpsi kappa l0 r0 hl0Follower hl0Reset hr0Follower
  have hafterLabels :=
    wallSweepResetProbePreCheckResetAfterCheck_source_follower_labels
      hpsi kappa l0 r0 (.inr hl0Reset) hr0Follower
  have hafterAlign : afterCheck.2.core.label =
      ⟨(afterCheck.1.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ := by
    rw [hafterLabels.1]
    exact hafterLabels.2
  have hafter0 : authorizedBulletFieldPair afterCheck =
      authorizedBulletFieldPair (l0, r0) :=
    wallSweepResetProbePreCheckResetAfterCheck_bulletFieldPair
      hpsi kappa l0 r0
  have hnormalizeFields : authorizedBulletFieldPair (l0, r0) =
      authorizedBulletFieldPair (l, r) :=
    Prod.ext (normalizeDeletion_bulletFields l)
      (normalizeDeletion_bulletFields r)
  have hafterFields : authorizedBulletFieldPair afterCheck =
      authorizedBulletFieldPair (l, r) :=
    hafter0.trans hnormalizeFields
  have hafterLeftSignal :=
    congrArg (fun q => q.1.signal_B) hafterFields
  have hafterRightBullet :=
    congrArg (fun q => q.2.bullet) hafterFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hafterLeftSignal hafterRightBullet
  dsimp only at hafterLeftSignal hafterRightBullet
  have hafterNotLive :
      afterCheck.2.core.bullet ≠ ⟨2, by omega⟩ := by
    intro hlive
    apply hrNotLive
    exact hafterRightBullet.symm.trans hlive
  have htail := wallSweepLeaderSinkAfterCheckSuffix_signal_or_dummy_moves
    hpsi afterCheck.1 afterCheck.2 hafterFollowers.1 hafterFollowers.2
      hafterAlign (hafterLeftSignal.trans hlSignal) hafterNotLive
  change tail.2.core.signal_B = ⟨1, by omega⟩ ∨
      (afterCheck.2.core.bullet = ⟨1, by omega⟩ ∧
        tail.1.core.bullet = ⟨1, by omega⟩ ∧
        tail.2.core.bullet = ⟨0, by omega⟩) at htail
  have hout :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_tail_of_reset_follower
      hpsi kappa l r hopen hlFollower hlReset hrFollower
  change out = tail at hout
  change out.2.core.signal_B = ⟨1, by omega⟩ ∨
    (r.core.bullet = ⟨1, by omega⟩ ∧
      out.1.core.bullet = ⟨1, by omega⟩ ∧
      out.2.core.bullet = ⟨0, by omega⟩)
  rw [hout]
  rcases htail with hsignal | hdummy
  · exact .inl hsignal
  · exact .inr ⟨hafterRightBullet.symm.trans hdummy.1,
      hdummy.2.1, hdummy.2.2⟩

/-- Exact dummy-bullet transport through the complete priority-open
reset-aware follower step.  The reset-aware prefix installs the alignment
needed by the rooted suffix, while normalization, birth bookkeeping, bounded
metadata, and authorization leave the physical bullet equation unchanged. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_priority_open_follower_bullets
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false)
    (hrNotLive : r.core.bullet ≠ ⟨2, by omega⟩) :
    let out :=
      wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r
    out.1.core.bullet =
        (if r.core.bullet = ⟨1, by omega⟩ then ⟨1, by omega⟩
          else l.core.bullet) ∧
      out.2.core.bullet = ⟨0, by omega⟩ := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let afterCheck := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  let tail := wallSweepLeaderSinkAfterCheckSuffix
    hpsi afterCheck.1 afterCheck.2
  let out :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
  have hl0Follower : l0.core.leader = false :=
    (normalizeDeletion_leader_eq l).trans hlFollower
  have hr0Follower : r0.core.leader = false :=
    (normalizeDeletion_leader_eq r).trans hrFollower
  have hnormalizeReset := normalizeDeletionPair_resetEcho l r
  have hl0Reset : l0.core.reset_cmd = true :=
    (resetEcho_fields_of_pair_eq hnormalizeReset).1.trans hlReset
  have hafterFollowers : afterCheck.1.core.leader = false ∧
      afterCheck.2.core.leader = false :=
    wallSweepResetProbePreCheckResetAfterCheck_followers_of_reset_source
      hpsi kappa l0 r0 hl0Follower hl0Reset hr0Follower
  have hafterLabels :=
    wallSweepResetProbePreCheckResetAfterCheck_source_follower_labels
      hpsi kappa l0 r0 (.inr hl0Reset) hr0Follower
  have hafterAlign : afterCheck.2.core.label =
      ⟨(afterCheck.1.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ := by
    rw [hafterLabels.1]
    exact hafterLabels.2
  have hafter0 : authorizedBulletFieldPair afterCheck =
      authorizedBulletFieldPair (l0, r0) :=
    wallSweepResetProbePreCheckResetAfterCheck_bulletFieldPair
      hpsi kappa l0 r0
  have hnormalizeFields : authorizedBulletFieldPair (l0, r0) =
      authorizedBulletFieldPair (l, r) :=
    Prod.ext (normalizeDeletion_bulletFields l)
      (normalizeDeletion_bulletFields r)
  have hafterFields : authorizedBulletFieldPair afterCheck =
      authorizedBulletFieldPair (l, r) :=
    hafter0.trans hnormalizeFields
  have hafterLeftBullet :=
    congrArg (fun q => q.1.bullet) hafterFields
  have hafterRightBullet :=
    congrArg (fun q => q.2.bullet) hafterFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hafterLeftBullet hafterRightBullet
  dsimp only at hafterLeftBullet hafterRightBullet
  have hafterNotLive :
      afterCheck.2.core.bullet ≠ ⟨2, by omega⟩ := by
    intro hlive
    apply hrNotLive
    exact hafterRightBullet.symm.trans hlive
  have htail :=
    wallSweepLeaderSinkAfterCheckSuffix_aligned_follower_bullets
      hpsi afterCheck.1 afterCheck.2 hafterFollowers.1 hafterFollowers.2
        hafterAlign hafterNotLive
  change tail.1.core.bullet =
        (if afterCheck.2.core.bullet = ⟨1, by omega⟩ then
          ⟨1, by omega⟩ else afterCheck.1.core.bullet) ∧
      tail.2.core.bullet = ⟨0, by omega⟩ at htail
  have hout :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_tail_of_reset_follower
      hpsi kappa l r hopen hlFollower hlReset hrFollower
  change out = tail at hout
  change out.1.core.bullet =
      (if r.core.bullet = ⟨1, by omega⟩ then ⟨1, by omega⟩
        else l.core.bullet) ∧
    out.2.core.bullet = ⟨0, by omega⟩
  rw [hout]
  constructor
  · rw [htail.1, hafterLeftBullet, hafterRightBullet]
  · exact htail.2

/-- Exact directional live-bullet transport through a complete reset-aware
follower step.  The reset prefix first installs successor alignment; the
rooted suffix then moves the live responder bullet to the initiator and clears
the responder. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_priority_open_follower_live_bullets
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false)
    (hrLive : r.core.bullet = ⟨2, by omega⟩) :
    let out :=
      wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r
    out.1.core.bullet = ⟨2, by omega⟩ ∧
      out.2.core.bullet = ⟨0, by omega⟩ := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let afterCheck := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  let tail := wallSweepLeaderSinkAfterCheckSuffix
    hpsi afterCheck.1 afterCheck.2
  let out :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
  have hl0Follower : l0.core.leader = false :=
    (normalizeDeletion_leader_eq l).trans hlFollower
  have hr0Follower : r0.core.leader = false :=
    (normalizeDeletion_leader_eq r).trans hrFollower
  have hnormalizeReset := normalizeDeletionPair_resetEcho l r
  have hl0Reset : l0.core.reset_cmd = true :=
    (resetEcho_fields_of_pair_eq hnormalizeReset).1.trans hlReset
  have hafterFollowers : afterCheck.1.core.leader = false ∧
      afterCheck.2.core.leader = false :=
    wallSweepResetProbePreCheckResetAfterCheck_followers_of_reset_source
      hpsi kappa l0 r0 hl0Follower hl0Reset hr0Follower
  have hafterLabels :=
    wallSweepResetProbePreCheckResetAfterCheck_source_follower_labels
      hpsi kappa l0 r0 (.inr hl0Reset) hr0Follower
  have hafterAlign : afterCheck.2.core.label =
      ⟨(afterCheck.1.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ := by
    rw [hafterLabels.1]
    exact hafterLabels.2
  have hafter0 : authorizedBulletFieldPair afterCheck =
      authorizedBulletFieldPair (l0, r0) :=
    wallSweepResetProbePreCheckResetAfterCheck_bulletFieldPair
      hpsi kappa l0 r0
  have hnormalizeFields : authorizedBulletFieldPair (l0, r0) =
      authorizedBulletFieldPair (l, r) :=
    Prod.ext (normalizeDeletion_bulletFields l)
      (normalizeDeletion_bulletFields r)
  have hafterFields : authorizedBulletFieldPair afterCheck =
      authorizedBulletFieldPair (l, r) :=
    hafter0.trans hnormalizeFields
  have hafterRightBullet :=
    congrArg (fun q => q.2.bullet) hafterFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hafterRightBullet
  dsimp only at hafterRightBullet
  have hafterLive : afterCheck.2.core.bullet = ⟨2, by omega⟩ :=
    hafterRightBullet.trans hrLive
  have htail :=
    wallSweepLeaderSinkAfterCheckSuffix_aligned_follower_live_bullets
      hpsi afterCheck.1 afterCheck.2 hafterFollowers.1 hafterFollowers.2
        hafterAlign hafterLive
  change tail.1.core.bullet = ⟨2, by omega⟩ ∧
      tail.2.core.bullet = ⟨0, by omega⟩ at htail
  have hout :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_tail_of_reset_follower
      hpsi kappa l r hopen hlFollower hlReset hrFollower
  change out = tail at hout
  change out.1.core.bullet = ⟨2, by omega⟩ ∧
    out.2.core.bullet = ⟨0, by omega⟩
  rw [hout]
  exact htail


end PPLLWallSweepPreCheckResetContracts
