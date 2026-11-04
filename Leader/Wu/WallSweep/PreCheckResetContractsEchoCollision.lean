import Leader.Wu.WallSweep.PreCheckResetContractsAuthorized

/-!
# Pre-CHECK reset contracts: EchoCollision

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

/-! ## Echo drain and leader reseed -/

private theorem authorizedReconcile_responder_echo_false_of_raw
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hraw : (f l.core r.core).2.echo = false) :
    authorizedResponderEchoFalse (authorizedReconcile f l r) := by
  exact hraw

/-- Repaired Algorithm 14 clears the responder echo at the named
post-suppression boundary, independently of comparison history. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_responder_echo_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedResponderEchoFalse
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  have heq := wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
    hpsi kappa l r
  exact responderEchoFalse_of_authorizedPair_eq heq
    (authorizedReconcile_responder_echo_false_of_raw
      (suppressSigResetKill hpsi) pre.1 pre.2
      (suppressSigResetKill_responder_echo_false
        hpsi pre.1.core pre.2.core))

/-- A shielded initiating leader consumes its echo at repaired Algorithm 14. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_initiator_echo_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hanchor : InitiatorAnchor l.core) :
    authorizedInitiatorEchoFalse
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  exact afterSuppress_initiator_echo_false_of_eq hpsi
    (pre := pre)
    (out := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r)
    (wallSweepPreCheckResetBeforeSuppress_initiator_anchor
      hpsi kappa l0 r0 (normalizeDeletion_initiator_anchor l hanchor))
    (wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
      hpsi kappa l r)

/-- An echo-free leader edge writes reset to the responder and clears both
echoes at the post-Algorithm-14 boundary. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_leader_reseed
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hanchor : InitiatorAnchor l.core)
    (hrEcho : r.core.echo = false) :
    authorizedLeaderReseedResult
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  have hr0Echo : r0.core.echo = false := by
    unfold r0 normalizeDeletion
    split <;> exact hrEcho
  exact afterSuppress_leader_reseed_of_eq hpsi
    (input := (l0, r0)) (pre := pre)
    (out := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r)
    (wallSweepPreCheckResetBeforeSuppress_initiator_anchor
      hpsi kappa l0 r0 (normalizeDeletion_initiator_anchor l hanchor))
    (wallSweepPreCheckResetBeforeSuppress_resetEchoPair
      hpsi kappa l0 r0)
    (wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
      hpsi kappa l r)
    hr0Echo

/-- The same echo-free leader seed leaves both comparison endpoints neutral. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_leader_reseed_neutral
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hanchor : InitiatorAnchor l.core)
    (hrEcho : r.core.echo = false) :
    authorizedBothNeutral
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  have hr0Echo : r0.core.echo = false := by
    unfold r0 normalizeDeletion
    split <;> exact hrEcho
  exact afterSuppress_leader_reseed_neutral_of_eq hpsi
    (input := (l0, r0)) (pre := pre)
    (out := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r)
    (wallSweepPreCheckResetBeforeSuppress_initiator_anchor
      hpsi kappa l0 r0 (normalizeDeletion_initiator_anchor l hanchor))
    (wallSweepPreCheckResetBeforeSuppress_resetEchoPair
      hpsi kappa l0 r0)
    (wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
      hpsi kappa l r)
    hr0Echo


/-- The ordinary tail frames the responder echo after Algorithm 14. -/
theorem wallSweepPreCheckResetNormalTail_responder_echo_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedResponderEchoFalse
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  exact responderEchoFalse_of_authorizedPair_eq
    (normalTail_eq_postSuppress hpsi kappa l r)
    (authorizedPostSuppress_responder_echo_false hpsi after.1 after.2
      (wallSweepPreCheckResetNormalAfterSuppress_responder_echo_false
        hpsi kappa l r))

/-- The ordinary tail frames the consumed initiator echo. -/
theorem wallSweepPreCheckResetNormalTail_initiator_echo_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hanchor : InitiatorAnchor l.core) :
    authorizedInitiatorEchoFalse
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  exact initiatorEchoFalse_of_authorizedPair_eq
    (normalTail_eq_postSuppress hpsi kappa l r)
    (authorizedPostSuppress_initiator_echo_false hpsi after.1 after.2
      (wallSweepPreCheckResetNormalAfterSuppress_initiator_echo_false
        hpsi kappa l r hanchor))

/-- The ordinary tail preserves the leader reseed control fields. -/
theorem wallSweepPreCheckResetNormalTail_leader_reseed
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hanchor : InitiatorAnchor l.core)
    (hrEcho : r.core.echo = false) :
    authorizedLeaderReseedResult
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  exact leaderReseedResult_of_authorizedPair_eq
    (normalTail_eq_postSuppress hpsi kappa l r)
    (authorizedPostSuppress_leader_reseed hpsi after.1 after.2
      (wallSweepPreCheckResetNormalAfterSuppress_leader_reseed
        hpsi kappa l r hanchor hrEcho))

/-- Algorithm 15 and gated WRITE preserve the two neutral seed endpoints. -/
theorem wallSweepPreCheckResetNormalTail_leader_reseed_neutral
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hanchor : InitiatorAnchor l.core)
    (hrEcho : r.core.echo = false) :
    authorizedBothNeutral
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  exact bothNeutral_of_authorizedPair_eq
    (normalTail_eq_postSuppress hpsi kappa l r)
    (authorizedPostSuppress_both_neutral hpsi after.1 after.2
      (wallSweepPreCheckResetNormalAfterSuppress_leader_reseed_neutral
        hpsi kappa l r hanchor hrEcho))

/-- Every priority-open corrected edge clears its responder echo. -/
theorem wallSweepPreCheckResetAuthorized_priority_open_responder_echo_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    authorizedResponderEchoFalse
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  exact responderEchoFalse_of_authorizedPair_eq
    (wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen)
    (markLeaderBirth_responder_echo_false born
      (wallSweepPreCheckResetNormalTail hpsi kappa l r)
      (wallSweepPreCheckResetNormalTail_responder_echo_false
        hpsi kappa l r))

/-- A priority-open shielded initiator consumes its echo. -/
theorem wallSweepPreCheckResetAuthorized_priority_open_initiator_echo_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core) :
    authorizedInitiatorEchoFalse
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  exact initiatorEchoFalse_of_authorizedPair_eq
    (wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen)
    (markLeaderBirth_initiator_echo_false born
      (wallSweepPreCheckResetNormalTail hpsi kappa l r)
      (wallSweepPreCheckResetNormalTail_initiator_echo_false
        hpsi kappa l r hanchor))

/-- A priority-open echo-free leader edge reseeds reset and clears both echoes. -/
theorem wallSweepPreCheckResetAuthorized_priority_open_leader_reseed
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core)
    (hrEcho : r.core.echo = false) :
    authorizedLeaderReseedResult
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  exact leaderReseedResult_of_authorizedPair_eq
    (wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen)
    (markLeaderBirth_leader_reseed born
      (wallSweepPreCheckResetNormalTail hpsi kappa l r)
      (wallSweepPreCheckResetNormalTail_leader_reseed
        hpsi kappa l r hanchor hrEcho))

/-- The same priority-open leader edge leaves both endpoints neutral. -/
theorem wallSweepPreCheckResetAuthorized_priority_open_leader_reseed_neutral
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core)
    (hrEcho : r.core.echo = false) :
    authorizedBothNeutral
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) := by
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  have htail := wallSweepPreCheckResetNormalTail_leader_reseed_neutral
    hpsi kappa l r hanchor hrEcho
  have heq :=
    wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have hmark := markLeaderBirth_eq_of_neutral born tail htail.1 htail.2
  exact bothNeutral_of_authorizedPair_eq (heq.trans hmark) htail

/-! ## Reset/echo collision -/

/-- Neutral endpoint state after a blocking echo consumes the moving token. -/
def AuthorizedResetCollision
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop :=
  ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
    q.1.core.reset_cmd = false ∧ q.2.core.reset_cmd = false ∧
    q.2.core.echo = false

theorem AuthorizedResetCollision.of_pair_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hab : a = b) (hb : AuthorizedResetCollision b) :
    AuthorizedResetCollision a := by
  rw [hab]
  exact hb

private theorem authorizedReconcile_collision_of_raw
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi)
    (hraw :
      let q := f l.core r.core
      ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 ∧
        q.1.reset_cmd = false ∧ q.2.reset_cmd = false ∧
        q.2.echo = false) :
    AuthorizedResetCollision (authorizedReconcile f l r) := by
  exact hraw

private theorem responder_echo_true_of_resetEchoPair_eq
    {before after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedResetEchoPair after = authorizedResetEchoPair before)
    (hecho : before.2.core.echo = true) :
    after.2.core.echo = true := by
  have hright := congrArg Prod.snd h
  exact (congrArg Prod.snd hright).trans hecho

private theorem initiator_reset_true_of_resetEchoPair_eq
    {before after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedResetEchoPair after = authorizedResetEchoPair before)
    (hreset : before.1.core.reset_cmd = true) :
    after.1.core.reset_cmd = true := by
  have hleft := congrArg Prod.fst h
  exact (congrArg Prod.fst hleft).trans hreset

set_option maxHeartbeats 1000000 in
theorem beforeSuppress_initiator_leader_true_of_left_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true) :
    (wallSweepPreCheckResetBeforeSuppress hpsi kappa l r).1.core.leader =
      true := by
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l r
  have hrawLeader : beforeRaw.1.core.leader = true :=
    (wallSweepAuthorizedBeforeCheck_initiator_leader_eq
      hpsi kappa l r).trans hlLeader
  have htail := preCheckResetCheckTail_eq_of_send
    hpsi beforeRaw (.inl hrawLeader)
  have hwall := preCheckResetWall_leaders_eq beforeRaw.1 beforeRaw.2
  change wallSweepPreCheckResetBeforeSuppress hpsi kappa l r =
    preCheckResetWall beforeRaw.1 beforeRaw.2 at htail
  rw [htail]
  exact hwall.1.trans hrawLeader

/-- Repaired Algorithm 14 has an exact cleanup contract for every existing
initiator leader, without assuming that the leader is shielded. -/
theorem afterSuppress_leader_source_cleanup_of_eq
    (hpsi : psi > 0)
    {input pre out : AuthorizedAgentState psi ×
      AuthorizedAgentState psi}
    (hpreLeader : pre.1.core.leader = true)
    (hpreFrame : authorizedResetEchoPair pre =
      authorizedResetEchoPair input)
    (hout : out = authorizedReconcile
      (suppressSigResetKill hpsi) pre.1 pre.2) :
    AuthorizedLeaderSourceCleanup input out := by
  have hfields := resetEcho_fields_of_pair_eq hpreFrame
  have hpreEcho : pre.2.core.echo = input.2.core.echo :=
    hfields.2.2.2
  let raw := suppressSigResetKill hpsi pre.1.core pre.2.core
  have hneutral : ComparisonNeutral raw.1 ∧
      ComparisonNeutral raw.2 := by
    cases hinputEcho : input.2.core.echo with
    | false =>
        have hpreEchoFalse : pre.2.core.echo = false :=
          hpreEcho.trans hinputEcho
        exact suppressSigResetKill_leader_reseed_neutral
          hpsi pre.1.core pre.2.core hpreLeader hpreEchoFalse
    | true =>
        have hpreEchoTrue : pre.2.core.echo = true :=
          hpreEcho.trans hinputEcho
        have hcollision := suppressSigResetKill_source_echo_collision
          hpsi pre.1.core pre.2.core (.inl hpreLeader)
            hpreEchoTrue
        exact ⟨hcollision.1, hcollision.2.1⟩
  have hexact := suppressSigResetKill_source_reset_echo_exact
    hpsi pre.1.core pre.2.core (.inl hpreLeader)
  have hexactRaw : raw.1.reset_cmd = false ∧
      raw.2.reset_cmd = !pre.2.core.echo ∧
      raw.2.echo = false ∧ raw.1.echo = false := by
    simpa only [raw, hpreLeader, if_true] using hexact
  rw [hout]
  change ComparisonNeutral raw.1 ∧
    ComparisonNeutral raw.2 ∧
    raw.1.reset_cmd = false ∧
    raw.2.reset_cmd = !input.2.core.echo ∧
    raw.1.echo = false ∧ raw.2.echo = false
  refine ⟨hneutral.1, hneutral.2, hexactRaw.1, ?_,
    hexactRaw.2.2.2, hexactRaw.2.2.1⟩
  exact hexactRaw.2.1.trans (congrArg Bool.not hpreEcho)

set_option maxHeartbeats 1000000 in
private theorem wallSweepPreCheckResetNormalAfterSuppress_left_leader_collision
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlLeader : l.core.leader = true)
    (hrEcho : r.core.echo = true) :
    AuthorizedResetCollision
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  have hframe := wallSweepPreCheckResetBeforeSuppress_resetEchoPair
    hpsi kappa l0 r0
  have hr0Echo : r0.core.echo = true := by
    unfold r0 normalizeDeletion
    split <;> exact hrEcho
  have hpreEcho : pre.2.core.echo = true :=
    responder_echo_true_of_resetEchoPair_eq hframe hr0Echo
  have hl0 : l0.core.leader = true := by
    unfold l0 normalizeDeletion
    split <;> exact hlLeader
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  have hrawLeader : beforeRaw.1.core.leader = true :=
    (wallSweepAuthorizedBeforeCheck_initiator_leader_eq
      hpsi kappa l0 r0).trans hl0
  let preWall := preCheckResetWall beforeRaw.1 beforeRaw.2
  have htail := preCheckResetCheckTail_eq_of_send
    hpsi beforeRaw (.inl hrawLeader)
  have hnamed : pre = preWall := by
    exact htail
  let cleared := (clearAuthorizedComparison beforeRaw.1,
    clearAuthorizedComparison beforeRaw.2)
  have hwallEq : preWall = cleared := by
    simp [preWall, cleared, preCheckResetWall, hrawLeader]
  have hpreEq : pre = cleared := hnamed.trans hwallEq
  have hclearedSource : cleared.1.core.leader = true ∨
      cleared.1.core.reset_cmd = true := by
    left
    simp [cleared, clearAuthorizedComparison, clearComparisonSignal,
      hrawLeader]
  have hclearedEcho : cleared.2.core.echo = true := by
    rw [← hpreEq]
    exact hpreEcho
  have hrawWall := suppressSigResetKill_source_echo_collision
    hpsi cleared.1.core cleared.2.core hclearedSource hclearedEcho
  have hraw :
      let q := suppressSigResetKill hpsi pre.1.core pre.2.core
      ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 ∧
        q.1.reset_cmd = false ∧ q.2.reset_cmd = false ∧
        q.2.echo = false := by
    rw [hpreEq]
    exact hrawWall
  have hauth := authorizedReconcile_collision_of_raw
    (suppressSigResetKill hpsi) pre.1 pre.2 hraw
  rw [wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile]
  exact hauth

private theorem wallSweepPreCheckResetNormalAfterSuppress_left_reset_collision
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = true)
    (hrEcho : r.core.echo = true) :
    AuthorizedResetCollision
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  have hframe := wallSweepPreCheckResetBeforeSuppress_resetEchoPair
    hpsi kappa l0 r0
  have hr0Echo : r0.core.echo = true := by
    unfold r0 normalizeDeletion
    split <;> exact hrEcho
  have hpreEcho : pre.2.core.echo = true :=
    responder_echo_true_of_resetEchoPair_eq hframe hr0Echo
  have hl0 : l0.core.reset_cmd = true := by
    unfold l0 normalizeDeletion
    split <;> exact hlReset
  have hpreSource : pre.1.core.leader = true ∨
      pre.1.core.reset_cmd = true := .inr
    (initiator_reset_true_of_resetEchoPair_eq hframe hl0)
  have hraw := suppressSigResetKill_source_echo_collision
    hpsi pre.1.core pre.2.core hpreSource hpreEcho
  have hauth := authorizedReconcile_collision_of_raw
    (suppressSigResetKill hpsi) pre.1 pre.2 hraw
  rw [wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile]
  exact hauth

/-- At repaired Algorithm 14, a blocking responder echo consumes a leader- or
reset-generated token and leaves both endpoints neutral. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_source_echo_collision
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hrEcho : r.core.echo = true) :
    AuthorizedResetCollision
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  rcases hsource with hleader | hreset
  · exact wallSweepPreCheckResetNormalAfterSuppress_left_leader_collision
      hpsi kappa l r hleader hrEcho
  · exact wallSweepPreCheckResetNormalAfterSuppress_left_reset_collision
      hpsi kappa l r hreset hrEcho

private theorem postSuppress_collision
    (hpsi : psi > 0)
    (before : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hbefore : AuthorizedResetCollision before) :
    AuthorizedResetCollision
      (authorizedPostSuppress hpsi before.1 before.2) := by
  have hpost := postSuppress_normalReset_handoff
    hpsi before.1 before.2 hbefore.1 hbefore.2.1
  exact ⟨hpost.1, hpost.2.1,
    hpost.2.2.1.trans hbefore.2.2.1,
    hpost.2.2.2.1.trans hbefore.2.2.2.1,
    hpost.2.2.2.2.2.trans hbefore.2.2.2.2⟩

/-- Algorithm 15 and gated WRITE preserve a reset/echo collision endpoint. -/
theorem wallSweepPreCheckResetNormalTail_source_echo_collision
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hrEcho : r.core.echo = true) :
    AuthorizedResetCollision
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hafter :=
    wallSweepPreCheckResetNormalAfterSuppress_source_echo_collision
      hpsi kappa l r hsource hrEcho
  exact AuthorizedResetCollision.of_pair_eq
    (normalTail_eq_postSuppress hpsi kappa l r)
    (postSuppress_collision hpsi after hafter)

/-- The complete priority-open transition records the same neutral collision;
birth marking is inert on its pathless output. -/
theorem wallSweepPreCheckResetAuthorized_priority_open_source_echo_collision
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hrEcho : r.core.echo = true) :
    AuthorizedResetCollision
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  have htail := wallSweepPreCheckResetNormalTail_source_echo_collision
    hpsi kappa l r hsource hrEcho
  change ComparisonNeutral tail.1.core ∧ ComparisonNeutral tail.2.core ∧
    tail.1.core.reset_cmd = false ∧ tail.2.core.reset_cmd = false ∧
    tail.2.core.echo = false at htail
  have hmark := markLeaderBirth_eq_of_neutral born tail htail.1 htail.2.1
  have heq :=
    wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at heq
  rw [heq, hmark]
  exact htail


end PPLLWallSweepPreCheckResetContracts
