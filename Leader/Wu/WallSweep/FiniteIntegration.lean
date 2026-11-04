import Leader.Wu.WallSweep.Repair

/-!
# Finite integration of the source-backed wall sweep

This module inserts the probe, leader, and reset walls into the existing
authorized/bounded/path-stall carrier without nesting any complete transition.
Every Algorithm-1 stage executes once.  The source lane remains unchanged.
-/

namespace PPLLWallSweepFinite

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLTerminalEqualSupportRepair PPLLWriteIncrementGate
  PPLLCombinedLocalRepair PPLLWallSweepRepair

/-! ## Authorized wall stages -/

/-- Preserve Algorithm 2's label-sensitive authorization discipline while
using the source-backed leader/probe wall as its physical core. -/
def authorizedPPsiLeaderProbeWall (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := pPsiLeaderProbeWall hψ l.core r.core
  let lp := if q.1.label = l.core.label then
    reconcilePermit l q.1
  else false
  let rp := if q.2.label = r.core.label then
    reconcilePermit r q.2
  else false
  (⟨q.1, lp⟩, ⟨q.2, rp⟩)

/-- Authorization-preserving lift of the reset-aware pre-P-prime probe wall.
The physical change is only the additional trusted reset-source guard; label
changes retain the same fail-closed permit discipline as the maintained wall. -/
def authorizedPPsiLeaderResetProbeWall (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := pPsiLeaderResetProbeWall hψ l.core r.core
  let lp := if q.1.label = l.core.label then
    reconcilePermit l q.1
  else false
  let rp := if q.2.label = r.core.label then
    reconcilePermit r q.2
  else false
  (⟨q.1, lp⟩, ⟨q.2, rp⟩)

/-- The authorized reset-aware wall exposes exactly its raw physical core. -/
theorem authorizedPPsiLeaderResetProbeWall_core
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    let q := authorizedPPsiLeaderResetProbeWall hψ l r
    (q.1.core, q.2.core) =
      pPsiLeaderResetProbeWall hψ l.core r.core := by
  rfl

/-- Reset-free edges remain exactly the established authorized probe wall. -/
theorem authorizedPPsiLeaderResetProbeWall_eq_of_no_reset
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hlReset : l.core.reset_cmd = false) :
    authorizedPPsiLeaderResetProbeWall hψ l r =
      authorizedPPsiLeaderProbeWall hψ l r := by
  unfold authorizedPPsiLeaderResetProbeWall
    authorizedPPsiLeaderProbeWall
  rw [pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_no_reset
    hψ l.core r.core hlReset]

/-- The authorized reset-aware wall is also exactly the rooted wall when the
responder is already a leader: both raw stages clear the same probe and hence
run the same fail-closed permit reconciliation. -/
theorem authorizedPPsiLeaderResetProbeWall_eq_of_right_leader
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hrLeader : r.core.leader = true) :
    authorizedPPsiLeaderResetProbeWall hψ l r =
      authorizedPPsiLeaderProbeWall hψ l r := by
  unfold authorizedPPsiLeaderResetProbeWall
    authorizedPPsiLeaderProbeWall
  rw [pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_right_leader
    hψ l.core r.core hrLeader]

/-- The authorized reset-aware wall is exactly the rooted wall on every edge
initiated by an existing leader. -/
theorem authorizedPPsiLeaderResetProbeWall_eq_of_left_leader
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hlLeader : l.core.leader = true) :
    authorizedPPsiLeaderResetProbeWall hψ l r =
      authorizedPPsiLeaderProbeWall hψ l r := by
  unfold authorizedPPsiLeaderResetProbeWall
    authorizedPPsiLeaderProbeWall
  rw [pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_left_leader
    hψ l.core r.core hlLeader]

theorem authorizedPPsiLeaderProbeWall_inProtocolDomain
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := authorizedPPsiLeaderProbeWall hψ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  exact pPsiLeaderProbeWall_inProtocolDomain hψ l.core r.core hl hr

theorem authorizedPPsiLeaderResetProbeWall_inProtocolDomain
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := authorizedPPsiLeaderResetProbeWall hψ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  exact pPsiLeaderResetProbeWall_inProtocolDomain
    hψ l.core r.core hl hr

/-- Carry T9's one-shot authorization through the wall-aware Algorithm 10.
The only authorization-creation event remains a real stable payload-zero move. -/
def authorizedSigMoveLeaderWall (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q := sigMoveLeaderWall hψ l.core r.core
  if _hmoved : pathMovedRight l.core r.core q.1 q.2 = true then
    let receiverPermit := match l.core.path with
      | .some 0 _ =>
          if stableSuccessor hψ l.core r.core then
            l.path0Crossed || stableWrap hψ l.core r.core
          else false
      | _ => false
    (⟨q.1, false⟩, ⟨q.2, normalizePermit q.2 receiverPermit⟩)
  else
    (⟨q.1, reconcilePermit l q.1⟩,
      ⟨q.2, reconcilePermit r q.2⟩)

/-- The authorized lift has exactly the corrected raw wall as its physical
core, with no extra physical rewrite. -/
theorem authorizedSigMoveLeaderWall_core (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    let q := authorizedSigMoveLeaderWall hψ l r
    (q.1.core, q.2.core) = sigMoveLeaderWall hψ l.core r.core := by
  unfold authorizedSigMoveLeaderWall
  dsimp only
  split <;> rfl

/-- The authorization wrapper changes only the movement permit; the raw
leader wall frames the responder's physical leader bit.  Keeping this as a
field-local API prevents downstream saturated prefixes from unfolding the
whole authorized pair merely to project one Boolean. -/
theorem authorizedSigMoveLeaderWall_responder_leader_eq
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) :
    (authorizedSigMoveLeaderWall hψ l r).2.core.leader =
      r.core.leader := by
  have hcore := authorizedSigMoveLeaderWall_core hψ l r
  have hR := congrArg Prod.snd hcore
  exact (congrArg AgentState.leader hR).trans
    (sigMoveLeaderWall_leaders_eq hψ l.core r.core).2

/-- On a leaderless edge the wall lift is exactly the established T9 SIGMOVE
adapter, so the stable-wrap permission event is preserved definitionally. -/
theorem authorizedSigMoveLeaderWall_eq_authorizedSigMove_of_no_leaders
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hl : l.core.leader = false) (hr : r.core.leader = false) :
    authorizedSigMoveLeaderWall hψ l r = authorizedSigMove hψ l r := by
  unfold authorizedSigMoveLeaderWall authorizedSigMove
  rw [sigMoveLeaderWall_eq_sigMove_of_no_leaders hψ l.core r.core hl hr]
  rfl

/-- A right leader kills both physical carriers and both existing T9 permits
before later control/CHECK/COMPARE stages. -/
theorem authorizedSigMoveLeaderWall_right_leader_kills
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hr : r.core.leader = true) :
    let q := authorizedSigMoveLeaderWall hψ l r
    ComparisonNeutral q.1.core ∧ ComparisonNeutral q.2.core ∧
      q.1.path0Crossed = false ∧ q.2.path0Crossed = false := by
  let core := sigMoveLeaderWall hψ l.core r.core
  have hneutral := sigMoveLeaderWall_right_leader_neutral
    hψ l.core r.core hr
  change ComparisonNeutral core.1 ∧ ComparisonNeutral core.2 at hneutral
  have hlPath : (sigMoveLeaderWall hψ l.core r.core).1.path = .bot := by
    exact hneutral.1.2.1
  have hrPath : (sigMoveLeaderWall hψ l.core r.core).2.path = .bot := by
    exact hneutral.2.2.1
  unfold authorizedSigMoveLeaderWall
  dsimp only
  split
  · refine ⟨hneutral.1, hneutral.2, rfl, ?_⟩
    simp [normalizePermit, hrPath]
  · refine ⟨hneutral.1, hneutral.2, ?_, ?_⟩
    · simp [reconcilePermit, normalizePermit, hlPath]
    · simp [reconcilePermit, normalizePermit, hrPath]

theorem authorizedSigMoveLeaderWall_inProtocolDomain
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := authorizedSigMoveLeaderWall hψ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  have hcore := sigMoveLeaderWall_inProtocolDomain
    hψ l.core r.core hl hr
  unfold authorizedSigMoveLeaderWall
  dsimp only
  split <;> exact hcore

/-- Authorized Algorithm-1 prefix through the repaired SIGMOVE wall. -/
def wallSweepAuthorizedBeforeCheck (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q0 := authorizedPPsiLeaderProbeWall hψ l r
  let q1 := authorizedGenSig hψ κ q0.1 q0.2
  let q2 := authorizedCleanSig hψ q1.1 q1.2
  let q3 := authorizedEliminateSig hψ q2.1 q2.2
  authorizedSigMoveLeaderWall hψ q3.1 q3.2

/-- Algorithm-1 prefix with the reset-aware probe guard applied at the exact
P-prime boundary and every later pre-CHECK stage unchanged. -/
def wallSweepResetProbeAuthorizedBeforeCheck
    (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q0 := authorizedPPsiLeaderResetProbeWall hψ l r
  let q1 := authorizedGenSig hψ κ q0.1 q0.2
  let q2 := authorizedCleanSig hψ q1.1 q1.2
  let q3 := authorizedEliminateSig hψ q2.1 q2.2
  authorizedSigMoveLeaderWall hψ q3.1 q3.2

/-- When the initiator carries no reset, the new prefix is exactly the
maintained prefix rather than merely field-equivalent to it. -/
theorem wallSweepResetProbeAuthorizedBeforeCheck_eq_of_no_reset
    (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hlReset : l.core.reset_cmd = false) :
    wallSweepResetProbeAuthorizedBeforeCheck hψ κ l r =
      wallSweepAuthorizedBeforeCheck hψ κ l r := by
  unfold wallSweepResetProbeAuthorizedBeforeCheck
    wallSweepAuthorizedBeforeCheck
  rw [authorizedPPsiLeaderResetProbeWall_eq_of_no_reset
    hψ l r hlReset]

/-- A responder leader makes the reset-source extension redundant throughout
the complete authorized prefix through the leader-aware SIGMOVE wall. -/
theorem wallSweepResetProbeAuthorizedBeforeCheck_eq_of_right_leader
    (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hrLeader : r.core.leader = true) :
    wallSweepResetProbeAuthorizedBeforeCheck hψ κ l r =
      wallSweepAuthorizedBeforeCheck hψ κ l r := by
  unfold wallSweepResetProbeAuthorizedBeforeCheck
    wallSweepAuthorizedBeforeCheck
  rw [authorizedPPsiLeaderResetProbeWall_eq_of_right_leader
    hψ l r hrLeader]

/-- A leader initiator makes the reset-source extension redundant throughout
the complete authorized prefix through the leader-aware SIGMOVE wall. -/
theorem wallSweepResetProbeAuthorizedBeforeCheck_eq_of_left_leader
    (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ)
    (hlLeader : l.core.leader = true) :
    wallSweepResetProbeAuthorizedBeforeCheck hψ κ l r =
      wallSweepAuthorizedBeforeCheck hψ κ l r := by
  unfold wallSweepResetProbeAuthorizedBeforeCheck
    wallSweepAuthorizedBeforeCheck
  rw [authorizedPPsiLeaderResetProbeWall_eq_of_left_leader
    hψ l r hlLeader]

set_option maxHeartbeats 2000000 in
theorem wallSweepResetProbeAuthorizedBeforeCheck_inProtocolDomain
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := wallSweepResetProbeAuthorizedBeforeCheck hψ κ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  let q0 := authorizedPPsiLeaderResetProbeWall hψ l r
  have h0 := authorizedPPsiLeaderResetProbeWall_inProtocolDomain
    hψ l r hl hr
  change q0.1.core.inProtocolDomain κ ∧
    q0.2.core.inProtocolDomain κ at h0
  let q1 := authorizedGenSig hψ κ q0.1 q0.2
  have h1 := authorizedReconcile_inProtocolDomain
    (genSigSaturated hψ κ) q0.1 q0.2
    (genSigSaturated_inProtocolDomain hψ q0.1.core q0.2.core h0.1 h0.2)
  change q1.1.core.inProtocolDomain κ ∧
    q1.2.core.inProtocolDomain κ at h1
  let q2 := authorizedCleanSig hψ q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain
    (cleanSig hψ) q1.1 q1.2
    (cleanSig_inProtocolDomain hψ q1.1.core q1.2.core h1.1 h1.2)
  change q2.1.core.inProtocolDomain κ ∧
    q2.2.core.inProtocolDomain κ at h2
  let q3 := authorizedEliminateSig hψ q2.1 q2.2
  have h3 := authorizedReconcile_inProtocolDomain
    (eliminateSig hψ) q2.1 q2.2
    (eliminateSig_inProtocolDomain hψ q2.1.core q2.2.core h2.1 h2.2)
  change q3.1.core.inProtocolDomain κ ∧
    q3.2.core.inProtocolDomain κ at h3
  exact authorizedSigMoveLeaderWall_inProtocolDomain
    hψ q3.1 q3.2 h3.1 h3.2

set_option maxHeartbeats 2000000 in
theorem wallSweepAuthorizedBeforeCheck_inProtocolDomain
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := wallSweepAuthorizedBeforeCheck hψ κ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  let q0 := authorizedPPsiLeaderProbeWall hψ l r
  have h0 := authorizedPPsiLeaderProbeWall_inProtocolDomain hψ l r hl hr
  change q0.1.core.inProtocolDomain κ ∧ q0.2.core.inProtocolDomain κ at h0
  let q1 := authorizedGenSig hψ κ q0.1 q0.2
  have h1 := authorizedReconcile_inProtocolDomain
    (genSigSaturated hψ κ) q0.1 q0.2
    (genSigSaturated_inProtocolDomain hψ q0.1.core q0.2.core h0.1 h0.2)
  change q1.1.core.inProtocolDomain κ ∧ q1.2.core.inProtocolDomain κ at h1
  let q2 := authorizedCleanSig hψ q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain
    (cleanSig hψ) q1.1 q1.2
    (cleanSig_inProtocolDomain hψ q1.1.core q1.2.core h1.1 h1.2)
  change q2.1.core.inProtocolDomain κ ∧ q2.2.core.inProtocolDomain κ at h2
  let q3 := authorizedEliminateSig hψ q2.1 q2.2
  have h3 := authorizedReconcile_inProtocolDomain
    (eliminateSig hψ) q2.1 q2.2
    (eliminateSig_inProtocolDomain hψ q2.1.core q2.2.core h2.1 h2.2)
  change q3.1.core.inProtocolDomain κ ∧ q3.2.core.inProtocolDomain κ at h3
  exact authorizedSigMoveLeaderWall_inProtocolDomain
    hψ q3.1 q3.2 h3.1 h3.2

/-! ## One repaired suffix and one complete authorized transition -/

/-- Existing T9/T19/T8 suffix with only Algorithm 14 replaced by the
source-backed reset deletion stage. -/
def wallSweepAuthorizedAfterCheckSuffix (hψ : ψ > 0)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let q0 := authorizedDisappear hψ l r
  let q1 := authorizedCompareSig hψ q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hψ) q1.1 q1.2
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollision hψ) q2.1 q2.2
  authorizedReconcile (writeSeqIncrementGate hψ) q3.1 q3.2

theorem wallSweepAuthorizedAfterCheckSuffix_inProtocolDomain
    (hψ : ψ > 0) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := wallSweepAuthorizedAfterCheckSuffix hψ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  let q0 := authorizedDisappear hψ l r
  have h0 := authorizedReconcile_inProtocolDomain
    (disappear hψ) l r
    (disappear_inProtocolDomain hψ l.core r.core hl hr)
  let q1 := authorizedCompareSig hψ q0.1 q0.2
  have h1 := authorizedCompareSig_inProtocolDomain
    hψ q0.1 q0.2 h0.1 h0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hψ) q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain
    (suppressSigResetKill hψ) q1.1 q1.2
    (suppressSigResetKill_inProtocolDomain
      hψ q1.1.core q1.2.core h1.1 h1.2)
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollision hψ) q2.1 q2.2
  have h3 := authorizedReconcile_inProtocolDomain
    (eliminateLeadersNoCollision hψ) q2.1 q2.2
    (eliminateLeadersNoCollision_inProtocolDomain
      hψ q2.1.core q2.2.core h2.1 h2.2)
  exact authorizedReconcile_inProtocolDomain
    (writeSeqIncrementGate hψ) q3.1 q3.2
    (writeSeqIncrementGate_inProtocolDomain
      hψ q3.1.core q3.2.core h3.1 h3.2)

/-- One nonduplicating Algorithm-1 execution.  Active T19 deletion retains
priority; T20 sanitation remains immediately before unchanged CHECK birth. -/
def wallSweepAuthorizedTransition (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  if deletionActive r0 then
    authorizedEliminateSig hψ l0 r0
  else if deletionActive l0 then
    (l0, r0)
  else
    let beforeRaw := wallSweepAuthorizedBeforeCheck hψ κ l0 r0
    let beforeCheck := sanitizeAuthorizedPair hψ beforeRaw
    let afterCheck := authorizedCheckSig hψ beforeCheck.1 beforeCheck.2
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    markLeaderBirth born
      (wallSweepAuthorizedAfterCheckSuffix hψ afterCheck.1 afterCheck.2)

attribute [local irreducible]
  wallSweepAuthorizedBeforeCheck wallSweepAuthorizedAfterCheckSuffix

set_option maxHeartbeats 2000000 in
theorem wallSweepAuthorizedTransition_inProtocolDomain
    (hψ : ψ > 0) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.inProtocolDomain κ) (hr : r.core.inProtocolDomain κ) :
    let q := wallSweepAuthorizedTransition hψ κ l r
    q.1.core.inProtocolDomain κ ∧ q.2.core.inProtocolDomain κ := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain κ at hl0
  change r0.core.inProtocolDomain κ at hr0
  unfold wallSweepAuthorizedTransition
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain
      (eliminateSig hψ) l0 r0
      (eliminateSig_inProtocolDomain hψ l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · let q0 := wallSweepAuthorizedBeforeCheck hψ κ l0 r0
      have h0 := wallSweepAuthorizedBeforeCheck_inProtocolDomain
        hψ κ l0 r0 hl0 hr0
      let q1 := sanitizeAuthorizedPair hψ q0
      have h1 : q1.1.core.inProtocolDomain κ ∧
          q1.2.core.inProtocolDomain κ :=
        ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain hψ q0.1 h0.1,
          sanitizeAuthorizedTerminalEqual_inProtocolDomain hψ q0.2 h0.2⟩
      let q2 := authorizedCheckSig hψ q1.1 q1.2
      have h2 := authorizedReconcile_inProtocolDomain
        (checkSig hψ) q1.1 q1.2
        (checkSig_inProtocolDomain hψ q1.1.core q1.2.core h1.1 h1.2)
      let tail := wallSweepAuthorizedAfterCheckSuffix hψ q2.1 q2.2
      have ht := wallSweepAuthorizedAfterCheckSuffix_inProtocolDomain
        hψ q2.1 q2.2 h2.1 h2.2
      let born := leaderBirthBeforeOrAtCheck l0 r0 q1 q2
      exact markLeaderBirth_inProtocolDomain born tail ht

/-! ## Exact bounded reification and existing stall carrier -/

/-- Reify once, after closure of the complete authorized transition. -/
def wallSweepBoundedTransition (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    AuthorizedBoundedAgentState ψ κ × AuthorizedBoundedAgentState ψ κ :=
  let q := wallSweepAuthorizedTransition hψ κ l.erase r.erase
  let hq := wallSweepAuthorizedTransition_inProtocolDomain hψ κ
    l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1, q.1.path0Crossed⟩,
    ⟨BoundedAgentState.ofDomain q.2.core hq.2, q.2.path0Crossed⟩)

theorem erase_wallSweepBoundedTransition
    (hψ : ψ > 0) (κ : Nat)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    let q := wallSweepBoundedTransition hψ κ l r
    (q.1.erase, q.2.erase) =
      wallSweepAuthorizedTransition hψ κ l.erase r.erase := by
  let q := wallSweepAuthorizedTransition hψ κ l.erase r.erase
  let hq := wallSweepAuthorizedTransition_inProtocolDomain hψ κ
    l.erase r.erase l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  change (⟨(BoundedAgentState.ofDomain q.1.core hq.1).erase,
      q.1.path0Crossed⟩,
    ⟨(BoundedAgentState.ofDomain q.2.core hq.2).erase,
      q.2.path0Crossed⟩) = q
  rw [BoundedAgentState.erase_ofDomain, BoundedAgentState.erase_ofDomain]

/-- One outer application of the established deletion-priority path-stall
accounting; no timer or wall stage is duplicated. -/
def wallSweepPathStallTransition (hψ : ψ > 0) (κ τ : Nat)
    (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := wallSweepBoundedTransition hψ κ l.core r.core
  let lOut : ExpiringAgentState ψ κ τ := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState ψ κ τ := ⟨q.2, r.stall⟩
  (deletionPriorityExpireOne τ l lOut,
    deletionPriorityExpireOne τ r rOut)

def wallSweepProtocol (hψ : ψ > 0) (κ τ : Nat) : PopulationProtocol where
  Q := ExpiringAgentState ψ κ τ
  Y := LeaderOutput
  transition := wallSweepPathStallTransition hψ κ τ
  output := fun s => if s.core.core.leader then .leader else .follower

/-! ## Exact factor-one finite certificate -/

def wallSweepStateCertificate (ψ κ τ : Nat) :
    ExhaustiveList (ExpiringAgentState ψ κ τ) :=
  combinedLocalStateCertificate ψ κ τ

theorem wallSweepStateCertificate_values_nodup (ψ κ τ : Nat) :
    (wallSweepStateCertificate ψ κ τ).values.Nodup :=
  combinedLocalStateCertificate_values_nodup ψ κ τ

theorem wallSweepStateCertificate_values_length (ψ κ τ : Nat) :
    (wallSweepStateCertificate ψ κ τ).values.length =
      (2 * (PPLLFinite.boundedAgentState ψ κ).values.length) * (τ + 1) :=
  combinedLocalStateCertificate_values_length ψ κ τ

/-- The three wall rules add no local-state factor over the existing combined
authorized/path-stall carrier. -/
theorem wallSweepStateCertificate_factor_one (ψ κ τ : Nat) :
    (wallSweepStateCertificate ψ κ τ).values.length =
      (combinedLocalStateCertificate ψ κ τ).values.length := by
  rfl

end PPLLWallSweepFinite
