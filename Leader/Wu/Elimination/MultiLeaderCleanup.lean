import Leader.Wu.WallSweep.ClockwiseRetry
import Leader.Wu.WriteSeq.WriterResetBarrier

/-!
# Multi-leader cleanup transition

Composed authorized transition that replaces three internal stages in the
ordinary suffix for multi-leader cleanup:

1. Replace responder `compareBitUpdateR` in COMPARE by the action-1 guarded
   `compareBitUpdateRActionOne`, preserving CHECK directional codes.
2. Replace Algorithm-15 MOVE by `eliminateLeadersNoCollisionZeroLeaderEgressMove`,
   adding the label-zero responder-leader egress route.
3. Replace ordinary SIGNAL by the responder-leader sink, then run
   `dummyBulletSink` before gated WRITE.  The sink is required on the
   nonconsecutive edge entering a label-zero victim leader.

Deletion branches and the reset-aware pre-CHECK prefix remain unchanged.

The file contains the cleanup schedule and trace interface, the composed authorized
transition and finite wrappers, then the local
ordinary-SIGNAL counterexample and leader-sink correction proved below.
-/

namespace PPLLCompleteMultiLeaderCleanup

open PPLL PPLLRepair PPLLDomain
  PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWriteIncrementGate PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepPreCheckResetRepair
  PPLLPpsiLeaderCreationRepair PPLLWallSweepClockwiseAttempt
  PPLLNoCheckBirthConditionTwoGeometry
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol
  PPLLWallSweepClockwiseScheduler
  PPLLTerminalEqualSupportRepair
  PPLLWriterResetBarrier

variable {n psi kappa tau : Nat}

/-! ## Action-1 COMPARE dispatch

The standard `compareBitUpdateR` unconditionally processes any `path2` at
position 0, destroying CHECK directional action codes (4 and 6).  The
action-1 guard restricts processing to action-1 tokens only. -/

/-- Action-1 guarded COMPARE on one edge.  Uses `compareBitUpdateRActionOne`
(the action-1 restricted responder update) paired with the unchanged
initiator update `compareBitUpdateL`. -/
def compareBitActionOne
    (hpsi : psi > 0) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let r' := compareBitUpdateRActionOne hpsi r
  let l' := compareBitUpdateL hpsi l
  (l', r')

/-- Dispatch to the action-1 guarded COMPARE when either agent carries a
`path2` signal; identity otherwise. -/
def compareSigDispatchActionOne
    (hpsi : psi > 0) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  match l.path2, r.path2 with
  | some _, _ => compareBitActionOne hpsi l r
  | _, some _ => compareBitActionOne hpsi l r
  | _, _ => (l, r)

/-- Copy of `authorizedCompareSig`, changing only the final dispatch to
the action-1 guarded variant. -/
def authorizedCompareSigActionOne
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState psi :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  match l0.core.path with
  | .bot => (l0, r)
  | .some _ _ =>
      match r.core.path with
      | .bot => (l0, r)
      | .some _ _ =>
          let q := authorizedCmpUpdate hpsi l0 r
          let out := compareSigDispatchActionOne
            hpsi q.1.core q.2.core
          (⟨out.1, normalizePermit out.1 q.1.path0Crossed⟩,
           ⟨out.2, normalizePermit out.2 q.2.path0Crossed⟩)

/-! ## Algorithm 15: FIRE, repaired egress MOVE, leader-sink SIGNAL, then dummy sink

The raw kernel composes four stages: FIRE, the egress-extended MOVE,
the responder-leader signal sink, and the dummy bullet sink.  The leader-sink
guard is essential: on an arbitrary interleader arc, the last edge entering a
label-zero leader need not be label-consecutive, so ordinary SIGNAL cannot
deliver the returning absence signal. -/

/-- Raw Algorithm-15 kernel with egress MOVE, responder-leader signal delivery,
and a post-SIGNAL dummy sink. -/
def eliminateLeadersNoCollisionEgressSink
    (hpsi : psi > 0) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let nextLabel : Fin psi :=
    ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  let q0 := eliminateLeadersNoCollisionFire hpsi l r
  let q1 := eliminateLeadersNoCollisionZeroLeaderEgressMove
    hpsi nextLabel q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink
    nextLabel q1.1 q1.2
  dummyBulletSink q2

/-- With zero bullets and an inert FIRE guard, one enabled source edge is a
pure absence-signal propagation step.  This is the local induction rule for
both interleader arcs. -/
theorem eliminateLeadersNoCollisionEgressSink_idle_propagation
    (hpsi : psi > 0) (l r : AgentState psi)
    (hlBullet : l.bullet = ⟨0, by omega⟩)
    (hrBullet : r.bullet = ⟨0, by omega⟩)
    (hnoLeftFire : l.leader = false ∨
      l.signal_B = ⟨0, by omega⟩)
    (hnoRightFire : r.leader = false ∨
      r.signal_B = ⟨0, by omega⟩)
    (hsource : l.leader = true ∨
      l.signal_B = ⟨1, by omega⟩)
    (hdeliver : r.label =
        ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ ∨
      r.leader = true) :
    let q := eliminateLeadersNoCollisionEgressSink hpsi l r
    q.1.leader = l.leader ∧ q.2.leader = r.leader ∧
      q.1.label = l.label ∧ q.2.label = r.label ∧
      q.1.shield = l.shield ∧ q.2.shield = r.shield ∧
      q.1.bullet = ⟨0, by omega⟩ ∧
      q.2.bullet = ⟨0, by omega⟩ ∧
      q.1.signal_B = l.signal_B ∧
      q.2.signal_B = ⟨1, by omega⟩ := by
  let nextLabel : Fin psi :=
    ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  have hfire : eliminateLeadersNoCollisionFire hpsi l r = (l, r) := by
    rcases hnoLeftFire with hlFollower | hlSignalZero
    · rcases hnoRightFire with hrFollower | hrSignalZero
      · simp [eliminateLeadersNoCollisionFire, hlFollower, hrFollower]
      · simp [eliminateLeadersNoCollisionFire, hlFollower, hrSignalZero]
    · rcases hnoRightFire with hrFollower | hrSignalZero
      · simp [eliminateLeadersNoCollisionFire, hlSignalZero, hrFollower]
      · simp [eliminateLeadersNoCollisionFire, hlSignalZero, hrSignalZero]
  have hmove :
      eliminateLeadersNoCollisionZeroLeaderEgressMove
        hpsi nextLabel l r = (l, r) := by
    simp [eliminateLeadersNoCollisionZeroLeaderEgressMove, hrBullet]
  let q := eliminateLeadersNoCollisionSignalLeaderSink nextLabel l r
  have hqRight : q.2.signal_B = ⟨1, by omega⟩ := by
    rcases hdeliver with hrAligned | hrLeader
    · have hsinkEq :
          eliminateLeadersNoCollisionSignalLeaderSink nextLabel l r =
            eliminateLeadersNoCollisionSignal nextLabel l r := by
        simp only [eliminateLeadersNoCollisionSignalLeaderSink,
          eliminateLeadersNoCollisionSignal]
        rw [if_pos (Or.inl hrAligned), if_pos (Or.inl hrAligned)]
      rw [show q = eliminateLeadersNoCollisionSignal nextLabel l r by
        exact hsinkEq]
      exact eliminateLeadersNoCollisionSignal_right_one_of_not_live
        nextLabel l r hrAligned (by simp [hrBullet]) hsource
    · exact
        eliminateLeadersNoCollisionSignalLeaderSink_right_one_of_leader
          nextLabel l r hrLeader hrBullet hsource
  have hqBullet : q.2.bullet = ⟨0, by omega⟩ := by
    simp [q, eliminateLeadersNoCollisionSignalLeaderSink, hrBullet]
  have hsink : dummyBulletSink q = q :=
    dummyBulletSink_eq_of_responder_bullet_zero q hqBullet
  have hout : eliminateLeadersNoCollisionEgressSink hpsi l r = q := by
    unfold eliminateLeadersNoCollisionEgressSink
    change dummyBulletSink
      (eliminateLeadersNoCollisionSignalLeaderSink nextLabel
        (eliminateLeadersNoCollisionZeroLeaderEgressMove hpsi nextLabel
          (eliminateLeadersNoCollisionFire hpsi l r).1
          (eliminateLeadersNoCollisionFire hpsi l r).2).1
        (eliminateLeadersNoCollisionZeroLeaderEgressMove hpsi nextLabel
          (eliminateLeadersNoCollisionFire hpsi l r).1
          (eliminateLeadersNoCollisionFire hpsi l r).2).2) = q
    rw [hfire]
    dsimp only
    rw [hmove]
    exact hsink
  rw [hout]
  refine ⟨rfl, ?_, rfl, ?_, rfl, ?_, hlBullet, hqBullet, rfl, hqRight⟩ <;>
    simp [q, eliminateLeadersNoCollisionSignalLeaderSink]

private structure CleanupSignalStepOutput
    (l r : AgentState psi) (q : AgentState psi × AgentState psi) : Prop where
  leaderL : q.1.leader = l.leader
  leaderR : q.2.leader = r.leader
  labelL : q.1.label = l.label
  labelR : q.2.label = r.label
  shieldL : q.1.shield = l.shield
  shieldR : q.2.shield = r.shield
  bulletL : q.1.bullet = ⟨0, by omega⟩
  bulletR : q.2.bullet = ⟨0, by omega⟩
  signalL : q.1.signal_B = l.signal_B
  signalR : q.2.signal_B = ⟨1, by omega⟩

private theorem cleanupSignalStepOutput
    (hpsi : psi > 0) (l r : AgentState psi)
    (hlBullet : l.bullet = ⟨0, by omega⟩)
    (hrBullet : r.bullet = ⟨0, by omega⟩)
    (hnoLeftFire : l.leader = false ∨
      l.signal_B = ⟨0, by omega⟩)
    (hnoRightFire : r.leader = false ∨
      r.signal_B = ⟨0, by omega⟩)
    (hsource : l.leader = true ∨
      l.signal_B = ⟨1, by omega⟩)
    (hdeliver : r.label =
        ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ ∨
      r.leader = true) :
    CleanupSignalStepOutput l r
      (eliminateLeadersNoCollisionEgressSink hpsi l r) := by
  have h := eliminateLeadersNoCollisionEgressSink_idle_propagation
    hpsi l r hlBullet hrBullet hnoLeftFire hnoRightFire hsource hdeliver
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- When the returning absence signal reaches a shielded responder leader,
one repeated incoming-edge interaction fires that leader on the right and
uses the label-zero egress route to park its dummy bullet on the follower.
The victim is thereby unshielded without changing either leader bit. -/
theorem eliminateLeadersNoCollisionEgressSink_right_leader_fire_egress
    (hpsi : psi > 0) (l r : AgentState psi)
    (hlLeader : l.leader = false)
    (hlSignal : l.signal_B = ⟨1, by omega⟩)
    (hrLeader : r.leader = true)
    (hrLabel : r.label = ⟨0, hpsi⟩)
    (hrSignal : r.signal_B = ⟨1, by omega⟩) :
    let q := eliminateLeadersNoCollisionEgressSink hpsi l r
    q.1.leader = false ∧ q.2.leader = true ∧
      q.1.label = l.label ∧ q.2.label = r.label ∧
      q.1.shield = l.shield ∧ q.2.shield = false ∧
      q.1.bullet = ⟨1, by omega⟩ ∧
      q.2.bullet = ⟨0, by omega⟩ ∧
      q.1.signal_B = ⟨0, by omega⟩ ∧
      q.2.signal_B = ⟨0, by omega⟩ := by
  simp (config := { maxSteps := 20000 })
    [eliminateLeadersNoCollisionEgressSink,
      eliminateLeadersNoCollisionFire,
      eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink,
      dummyBulletSink, hlLeader, hlSignal,
      hrLeader, hrLabel, hrSignal] <;>
    decide

structure CleanupRightFireOutput
    (l r : AgentState psi) (q : AgentState psi × AgentState psi) : Prop where
  leaderL : q.1.leader = false
  leaderR : q.2.leader = true
  labelL : q.1.label = l.label
  labelR : q.2.label = r.label
  shieldL : q.1.shield = l.shield
  shieldR : q.2.shield = false
  bulletL : q.1.bullet = ⟨1, by omega⟩
  bulletR : q.2.bullet = ⟨0, by omega⟩
  signalL : q.1.signal_B = ⟨0, by omega⟩
  signalR : q.2.signal_B = ⟨0, by omega⟩

theorem cleanupRightFireOutput
    (hpsi : psi > 0) (l r : AgentState psi)
    (hlLeader : l.leader = false)
    (hlSignal : l.signal_B = ⟨1, by omega⟩)
    (hrLeader : r.leader = true)
    (hrLabel : r.label = ⟨0, hpsi⟩)
    (hrSignal : r.signal_B = ⟨1, by omega⟩) :
    CleanupRightFireOutput l r
      (eliminateLeadersNoCollisionEgressSink hpsi l r) := by
  have h := eliminateLeadersNoCollisionEgressSink_right_leader_fire_egress
    hpsi l r hlLeader hlSignal hrLeader hrLabel hrSignal
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- A signalled initiator leader fires a live bullet on its outgoing edge.
The follower responder cannot fire, and SIGNAL leaves a positive absence
signal on that responder for the already completed circuit. -/
theorem eliminateLeadersNoCollisionEgressSink_left_leader_fire_live
    (hpsi : psi > 0) (l r : AgentState psi)
    (hlLeader : l.leader = true)
    (hlSignal : l.signal_B = ⟨1, by omega⟩)
    (hrLeader : r.leader = false)
    (hrNotLive : r.bullet ≠ ⟨2, by omega⟩) :
    let q := eliminateLeadersNoCollisionEgressSink hpsi l r
    q.1.leader = true ∧ q.2.leader = false ∧
      q.1.label = l.label ∧ q.2.label = r.label ∧
      q.1.shield = true ∧ q.2.shield = r.shield ∧
      q.1.bullet = ⟨2, by omega⟩ ∧
      q.2.bullet = ⟨0, by omega⟩ ∧
      q.1.signal_B = ⟨0, by omega⟩ ∧
      q.2.signal_B = ⟨1, by omega⟩ := by
  have hcases : r.bullet = ⟨0, by omega⟩ ∨
      r.bullet = ⟨1, by omega⟩ ∨
      r.bullet = ⟨2, by omega⟩ := by
    have hv : r.bullet.val = 0 ∨ r.bullet.val = 1 ∨
        r.bullet.val = 2 := by omega
    rcases hv with hv | hv | hv
    · exact Or.inl (Fin.ext hv)
    · exact Or.inr (Or.inl (Fin.ext hv))
    · exact Or.inr (Or.inr (Fin.ext hv))
  have hsignalCases : r.signal_B = ⟨0, by omega⟩ ∨
      r.signal_B = ⟨1, by omega⟩ := by
    have hv : r.signal_B.val = 0 ∨ r.signal_B.val = 1 := by omega
    rcases hv with hv | hv
    · exact Or.inl (Fin.ext hv)
    · exact Or.inr (Fin.ext hv)
  rcases hcases with hrZero | hrDummy | hrLive
  · rcases hsignalCases with hrSignalZero | hrSignalOne <;>
      simp_all (config := { maxSteps := 20000 })
      [eliminateLeadersNoCollisionEgressSink,
        eliminateLeadersNoCollisionFire,
        eliminateLeadersNoCollisionZeroLeaderEgressMove,
        eliminateLeadersNoCollisionSignalLeaderSink,
        dummyBulletSink] <;>
      decide
  · rcases hsignalCases with hrSignalZero | hrSignalOne <;>
      simp_all (config := { maxSteps := 20000 })
      [eliminateLeadersNoCollisionEgressSink,
        eliminateLeadersNoCollisionFire,
        eliminateLeadersNoCollisionZeroLeaderEgressMove,
        eliminateLeadersNoCollisionSignalLeaderSink,
        dummyBulletSink] <;>
      decide
  · exact (hrNotLive hrLive).elim

structure CleanupLeftFireOutput
    (l r : AgentState psi) (q : AgentState psi × AgentState psi) : Prop where
  leaderL : q.1.leader = true
  leaderR : q.2.leader = false
  labelL : q.1.label = l.label
  labelR : q.2.label = r.label
  shieldL : q.1.shield = true
  shieldR : q.2.shield = r.shield
  bulletL : q.1.bullet = ⟨2, by omega⟩
  bulletR : q.2.bullet = ⟨0, by omega⟩
  signalL : q.1.signal_B = ⟨0, by omega⟩
  signalR : q.2.signal_B = ⟨1, by omega⟩

theorem cleanupLeftFireOutput
    (hpsi : psi > 0) (l r : AgentState psi)
    (hlLeader : l.leader = true)
    (hlSignal : l.signal_B = ⟨1, by omega⟩)
    (hrLeader : r.leader = false)
    (hrNotLive : r.bullet ≠ ⟨2, by omega⟩) :
    CleanupLeftFireOutput l r
      (eliminateLeadersNoCollisionEgressSink hpsi l r) := by
  have h := eliminateLeadersNoCollisionEgressSink_left_leader_fire_live
    hpsi l r hlLeader hlSignal hrLeader hrNotLive
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- A live responder bullet moves one edge counterclockwise through either
an aligned follower edge or the explicit label-zero responder-leader egress.
This is the local rule iterated by `reversePositiveEdgeSchedule`. -/
theorem eliminateLeadersNoCollisionEgressSink_live_bullet_move_left
    (hpsi : psi > 0) (l r : AgentState psi)
    (hlLeader : l.leader = false)
    (hrBullet : r.bullet = ⟨2, by omega⟩)
    (hnoRightFire : r.leader = false ∨
      r.signal_B = ⟨0, by omega⟩)
    (hroute : r.label =
        ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ ∨
      (r.leader = true ∧ r.label = ⟨0, hpsi⟩)) :
    let q := eliminateLeadersNoCollisionEgressSink hpsi l r
    q.1.leader = false ∧ q.2.leader = r.leader ∧
      q.1.label = l.label ∧ q.2.label = r.label ∧
      q.1.shield = l.shield ∧ q.2.shield = r.shield ∧
      q.1.bullet = ⟨2, by omega⟩ ∧
      q.2.bullet = ⟨0, by omega⟩ ∧
      q.1.signal_B = ⟨0, by omega⟩ := by
  rcases hnoRightFire with hrFollower | hrSignalZero <;>
    rcases hroute with hrAligned | ⟨hrLeader, hrZero⟩ <;>
    simp_all (config := { maxSteps := 30000 })
      [eliminateLeadersNoCollisionEgressSink,
        eliminateLeadersNoCollisionFire,
        eliminateLeadersNoCollisionZeroLeaderEgressMove,
        eliminateLeadersNoCollisionSignalLeaderSink,
        dummyBulletSink] <;>
    decide

private structure CleanupLiveMoveOutput
    (l r : AgentState psi) (q : AgentState psi × AgentState psi) : Prop where
  leaderL : q.1.leader = false
  leaderR : q.2.leader = r.leader
  labelL : q.1.label = l.label
  labelR : q.2.label = r.label
  shieldL : q.1.shield = l.shield
  shieldR : q.2.shield = r.shield
  bulletL : q.1.bullet = ⟨2, by omega⟩
  bulletR : q.2.bullet = ⟨0, by omega⟩
  signalL : q.1.signal_B = ⟨0, by omega⟩

private theorem cleanupLiveMoveOutput
    (hpsi : psi > 0) (l r : AgentState psi)
    (hlLeader : l.leader = false)
    (hrBullet : r.bullet = ⟨2, by omega⟩)
    (hnoRightFire : r.leader = false ∨
      r.signal_B = ⟨0, by omega⟩)
    (hroute : r.label =
        ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ ∨
      (r.leader = true ∧ r.label = ⟨0, hpsi⟩)) :
    CleanupLiveMoveOutput l r
      (eliminateLeadersNoCollisionEgressSink hpsi l r) := by
  have h := eliminateLeadersNoCollisionEgressSink_live_bullet_move_left
    hpsi l r hlLeader hrBullet hnoRightFire hroute
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- A live responder bullet deletes an unshielded initiator leader.  MOVE
demotes the live bullet to a dummy; the post-SIGNAL sink does not clear it
because the initiator is already a follower. -/
theorem eliminateLeadersNoCollisionEgressSink_live_bullet_kills_left
    (hpsi : psi > 0) (l r : AgentState psi)
    (hlLeader : l.leader = true)
    (hlShield : l.shield = false)
    (hlSignal : l.signal_B = ⟨0, by omega⟩)
    (hrLeader : r.leader = false)
    (hrBullet : r.bullet = ⟨2, by omega⟩) :
    let q := eliminateLeadersNoCollisionEgressSink hpsi l r
    q.1.leader = false ∧ q.2.leader = false ∧
      q.1.label = l.label ∧ q.2.label = r.label ∧
      q.1.shield = false ∧ q.2.shield = r.shield ∧
      q.1.bullet = l.bullet ∧
      q.2.bullet = ⟨1, by omega⟩ := by
  simp (config := { maxSteps := 20000 })
    [eliminateLeadersNoCollisionEgressSink,
      eliminateLeadersNoCollisionFire,
      eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink,
      dummyBulletSink, hlLeader, hlShield, hlSignal,
      hrLeader, hrBullet]

structure CleanupLiveKillOutput
    (l r : AgentState psi) (q : AgentState psi × AgentState psi) : Prop where
  leaderL : q.1.leader = false
  leaderR : q.2.leader = false
  labelL : q.1.label = l.label
  labelR : q.2.label = r.label
  shieldL : q.1.shield = false
  shieldR : q.2.shield = r.shield
  bulletL : q.1.bullet = l.bullet
  bulletR : q.2.bullet = ⟨1, by omega⟩

theorem cleanupLiveKillOutput
    (hpsi : psi > 0) (l r : AgentState psi)
    (hlLeader : l.leader = true)
    (hlShield : l.shield = false)
    (hlSignal : l.signal_B = ⟨0, by omega⟩)
    (hrLeader : r.leader = false)
    (hrBullet : r.bullet = ⟨2, by omega⟩) :
    CleanupLiveKillOutput l r
      (eliminateLeadersNoCollisionEgressSink hpsi l r) := by
  have h := eliminateLeadersNoCollisionEgressSink_live_bullet_kills_left
    hpsi l r hlLeader hlShield hlSignal hrLeader hrBullet
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## Custom post-CHECK suffix

The sink is inside the Algorithm-15 replacement, so WRITE observes the
already-cleared dummy.  The suffix structure mirrors the existing
`wallSweepLeaderSinkAfterCheckSuffix` but replaces COMPARE dispatch
and Algorithm 15 with the action-1 guarded and egress-sink variants. -/

/-- Post-CHECK suffix for the multi-leader cleanup wall.  Compared to the
existing `wallSweepLeaderSinkAfterCheckSuffix`, this replaces:
- `authorizedCompareSig` with `authorizedCompareSigActionOne`
- `eliminateLeadersNoCollisionLeaderSink` with `eliminateLeadersNoCollisionEgressSink` -/
def multiLeaderAfterCheckSuffix
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  authorizedReconcile
    (writeSeqIncrementGate hpsi) q3.1 q3.2

/-! ## Multi-leader cleanup authorized transition

Deletion branches and the reset-aware pre-CHECK prefix are exactly the
existing scheduler branches; only the ordinary suffix is replaced. -/

/-- Audit-level multi-leader wall.  The deletion-priority and reset-aware
prefix remain byte-for-byte the existing ones; only the ordinary suffix
uses the action-1 guarded COMPARE and egress-sink Algorithm 15. -/
def multiLeaderCleanupAuthorizedTransition
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
    let born := leaderBirthBeforeOrAtCheck
      l0 r0 beforeCheck afterCheck
    markLeaderBirth born
      (multiLeaderAfterCheckSuffix hpsi afterCheck.1 afterCheck.2)

/-! ## Domain closure

The finite wrapper requires domain closure through the new suffix.  The
deletion/reset proof is unchanged from the existing wall; only the tail
lemma differs. -/

/-! ### Local helpers: count/payload frame and path2-frame domain transfer -/

private theorem domain_of_count_payload_eq
    (input output : AgentState psi) (hin : input.inProtocolDomain kappa)
    (hcount : output.count = input.count)
    (hpayload : PayloadView.ofState output = PayloadView.ofState input) :
    output.inProtocolDomain kappa := by
  rw [inProtocolDomain_iff] at hin ⊢
  exact ⟨hcount ▸ hin.1, hpayload ▸ hin.2⟩

private theorem domain_of_path2_frame_eq
    (input output : AgentState psi) (hin : input.inProtocolDomain kappa)
    (hpath2 : PayloadView.Path2Valid psi output.path2)
    (hframe : Path2FrameView.ofState output = Path2FrameView.ofState input) :
    output.inProtocolDomain kappa := by
  rw [inProtocolDomain_iff_path2_frame] at hin ⊢
  exact ⟨hpath2, hframe ▸ hin.2⟩

/-! ### Action-1 COMPARE domain closure

Recover `compareBitUpdateL` domain closure from the public
`compareSigDispatch_inProtocolDomain`, then prove
`compareBitUpdateRActionOne` directly. -/

private theorem compareBitUpdateL_inProtocolDomain'
    (hpsi : psi > 0) (u : AgentState psi) (hu : u.inProtocolDomain kappa) :
    (compareBitUpdateL hpsi u).inProtocolDomain kappa := by
  cases hp : u.path2 with
  | none => simpa [compareBitUpdateL, hp] using hu
  | some _ =>
    have h := compareSigDispatch_inProtocolDomain hpsi u u hu hu
    simpa [compareSigDispatch, compareBit, hp] using h.1

private theorem compareBitUpdateRActionOne_inProtocolDomain
    (hpsi : psi > 0) (r : AgentState psi) (hr : r.inProtocolDomain kappa) :
    (compareBitUpdateRActionOne hpsi r).inProtocolDomain kappa := by
  cases hp : r.path2 with
  | none => simpa [compareBitUpdateRActionOne, hp] using hr
  | some p2 =>
    by_cases ha : p2.action = 1
    · rw [compareBitUpdateRActionOne_eq_of_action_one hpsi r hp ha]
      have h := compareSigDispatch_inProtocolDomain hpsi r r hr hr
      simpa [compareSigDispatch, compareBit, hp] using h.2
    · simp only [compareBitUpdateRActionOne, hp]
      split
      · next hguard => exact absurd hguard.2 ha
      · exact hr

private theorem compareBitActionOne_inProtocolDomain
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := compareBitActionOne hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa :=
  ⟨compareBitUpdateL_inProtocolDomain' hpsi l hl,
    compareBitUpdateRActionOne_inProtocolDomain hpsi r hr⟩

private theorem compareSigDispatchActionOne_inProtocolDomain
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := compareSigDispatchActionOne hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  cases hlp : l.path2 <;> cases hrp : r.path2 <;>
    simp only [compareSigDispatchActionOne, hlp, hrp]
  · exact ⟨hl, hr⟩
  · exact compareBitActionOne_inProtocolDomain hpsi l r hl hr
  · exact compareBitActionOne_inProtocolDomain hpsi l r hl hr
  · exact compareBitActionOne_inProtocolDomain hpsi l r hl hr

theorem authorizedCompareSigActionOne_inProtocolDomain
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := authorizedCompareSigActionOne hpsi l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  unfold authorizedCompareSigActionOne
  dsimp only
  let lCore := compareSigInit l.core
  have hlCore := compareSigInit_inProtocolDomain l.core hl
  let l0 : AuthorizedAgentState psi :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  change l0.core.inProtocolDomain kappa at hlCore
  cases hlpath : l0.core.path with
  | bot => exact ⟨hlCore, hr⟩
  | some leftLabel leftBit =>
      cases hrpath : r.core.path with
      | bot => exact ⟨hlCore, hr⟩
      | some rightLabel rightBit =>
          let q0 := authorizedCmpUpdate hpsi l0 r
          have hq0 := authorizedCmpUpdate_inProtocolDomain
            hpsi l0 r hlCore hr
          change q0.1.core.inProtocolDomain kappa ∧
            q0.2.core.inProtocolDomain kappa at hq0
          exact compareSigDispatchActionOne_inProtocolDomain hpsi
            q0.1.core q0.2.core hq0.1 hq0.2

/-! ### Egress-sink Algorithm 15 domain closure

All four sub-stages (FIRE, egress MOVE, SIGNAL, dummy sink) modify only
`leader`, `bullet`, `shield`, and `signal_B`; none of these appear in
`inProtocolDomain`.  Domain closure follows from count/payload framing. -/

private theorem elncFire_count_payload (hpsi : psi > 0)
    (l r : AgentState psi) :
    let q := eliminateLeadersNoCollisionFire hpsi l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧
        PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [eliminateLeadersNoCollisionFire, PayloadView.ofState]
  repeat (first | constructor | rfl | split)

private theorem elncEgressMove_count_payload (hpsi : psi > 0)
    (nextLabel : Fin psi) (l r : AgentState psi) :
    let q := eliminateLeadersNoCollisionZeroLeaderEgressMove
      hpsi nextLabel l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧
        PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [eliminateLeadersNoCollisionZeroLeaderEgressMove,
    PayloadView.ofState]
  repeat (first | constructor | rfl | split)

private theorem elncSignal_count_payload
    (nextLabel : Fin psi) (l r : AgentState psi) :
    let q := eliminateLeadersNoCollisionSignalLeaderSink nextLabel l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧
        PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [eliminateLeadersNoCollisionSignalLeaderSink,
    PayloadView.ofState]
  repeat (first | constructor | rfl | split)

private theorem dummyBulletSink_count_payload
    (q : AgentState psi × AgentState psi) :
    ((dummyBulletSink q).1.count = q.1.count ∧
      PayloadView.ofState (dummyBulletSink q).1 =
        PayloadView.ofState q.1) ∧
    ((dummyBulletSink q).2.count = q.2.count ∧
      PayloadView.ofState (dummyBulletSink q).2 =
        PayloadView.ofState q.2) := by
  simp only [dummyBulletSink, PayloadView.ofState]
  repeat (first | constructor | rfl | split)

theorem eliminateLeadersNoCollisionEgressSink_inProtocolDomain
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := eliminateLeadersNoCollisionEgressSink hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  let nextLabel : Fin psi :=
    ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  let q0 := eliminateLeadersNoCollisionFire hpsi l r
  have h0 := elncFire_count_payload hpsi l r
  have hd0 : q0.1.inProtocolDomain kappa ∧
      q0.2.inProtocolDomain kappa :=
    ⟨domain_of_count_payload_eq l q0.1 hl h0.1.1 h0.1.2,
      domain_of_count_payload_eq r q0.2 hr h0.2.1 h0.2.2⟩
  let q1 := eliminateLeadersNoCollisionZeroLeaderEgressMove
    hpsi nextLabel q0.1 q0.2
  have h1 := elncEgressMove_count_payload hpsi nextLabel q0.1 q0.2
  have hd1 : q1.1.inProtocolDomain kappa ∧
      q1.2.inProtocolDomain kappa :=
    ⟨domain_of_count_payload_eq q0.1 q1.1 hd0.1 h1.1.1 h1.1.2,
      domain_of_count_payload_eq q0.2 q1.2 hd0.2 h1.2.1 h1.2.2⟩
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink
    nextLabel q1.1 q1.2
  have h2 := elncSignal_count_payload nextLabel q1.1 q1.2
  have hd2 : q2.1.inProtocolDomain kappa ∧
      q2.2.inProtocolDomain kappa :=
    ⟨domain_of_count_payload_eq q1.1 q2.1 hd1.1 h2.1.1 h2.1.2,
      domain_of_count_payload_eq q1.2 q2.2 hd1.2 h2.2.1 h2.2.2⟩
  have h3 := dummyBulletSink_count_payload q2
  exact ⟨domain_of_count_payload_eq q2.1 _ hd2.1 h3.1.1 h3.1.2,
    domain_of_count_payload_eq q2.2 _ hd2.2 h3.2.1 h3.2.2⟩

/-! ### Suffix and full transition domain closure -/

set_option maxHeartbeats 2000000 in
/-- Domain closure of the custom after-CHECK suffix. -/
theorem multiLeaderAfterCheckSuffix_inProtocolDomain
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := multiLeaderAfterCheckSuffix hpsi l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  let q0 := authorizedDisappear hpsi l r
  have h0 := authorizedReconcile_inProtocolDomain
    (disappear hpsi) l r
    (disappear_inProtocolDomain hpsi l.core r.core hl hr)
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  have h1 := authorizedCompareSigActionOne_inProtocolDomain
    hpsi q0.1 q0.2 h0.1 h0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  have h2 := authorizedReconcile_inProtocolDomain
    (suppressSigResetKill hpsi) q1.1 q1.2
    (suppressSigResetKill_inProtocolDomain
      hpsi q1.1.core q1.2.core h1.1 h1.2)
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  have h3 := authorizedReconcile_inProtocolDomain
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
    (eliminateLeadersNoCollisionEgressSink_inProtocolDomain
      hpsi q2.1.core q2.2.core h2.1 h2.2)
  exact authorizedReconcile_inProtocolDomain
    (writeSeqIncrementGate hpsi) q3.1 q3.2
    (writeSeqIncrementGate_inProtocolDomain
      hpsi q3.1.core q3.2.core h3.1 h3.2)

set_option maxHeartbeats 2000000 in
/-- Domain closure of the full multi-leader cleanup authorized transition.
The deletion/reset prefix is unchanged from the existing wall. -/
theorem multiLeaderCleanupAuthorizedTransition_inProtocolDomain
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.inProtocolDomain kappa)
    (hr : r.core.inProtocolDomain kappa) :
    let q := multiLeaderCleanupAuthorizedTransition hpsi kappa l r
    q.1.core.inProtocolDomain kappa ∧
      q.2.core.inProtocolDomain kappa := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 := (cleanup_helpers_inProtocolDomain l hl).1
  have hr0 := (cleanup_helpers_inProtocolDomain r hr).1
  change l0.core.inProtocolDomain kappa at hl0
  change r0.core.inProtocolDomain kappa at hr0
  unfold multiLeaderCleanupAuthorizedTransition
  dsimp only
  split
  · exact authorizedReconcile_inProtocolDomain
      (eliminateSig hpsi) l0 r0
      (eliminateSig_inProtocolDomain hpsi l0.core r0.core hl0 hr0)
  · split
    · exact ⟨hl0, hr0⟩
    · let q0 := wallSweepResetProbeAuthorizedBeforeCheck
        hpsi kappa l0 r0
      have h0 := wallSweepResetProbeAuthorizedBeforeCheck_inProtocolDomain
        hpsi kappa l0 r0 hl0 hr0
      let qR := preCheckResetWall q0.1 q0.2
      have hR := preCheckResetWall_inProtocolDomain q0.1 q0.2 h0.1 h0.2
      let q1 := sanitizeAuthorizedPair hpsi qR
      have h1 : q1.1.core.inProtocolDomain kappa ∧
          q1.2.core.inProtocolDomain kappa :=
        ⟨sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi qR.1 hR.1,
          sanitizeAuthorizedTerminalEqual_inProtocolDomain hpsi qR.2 hR.2⟩
      let q2 := authorizedCheckSig hpsi q1.1 q1.2
      have h2 := authorizedReconcile_inProtocolDomain
        (checkSig hpsi) q1.1 q1.2
        (checkSig_inProtocolDomain hpsi q1.1.core q1.2.core h1.1 h1.2)
      let born := leaderBirthBeforeOrAtCheck l0 r0 q1 q2
      let tail := multiLeaderAfterCheckSuffix hpsi q2.1 q2.2
      have ht := multiLeaderAfterCheckSuffix_inProtocolDomain
        hpsi q2.1 q2.2 h2.1 h2.2
      exact markLeaderBirth_inProtocolDomain born tail ht

/-! ## Finite wrappers

The bounded and path-stall carriers mirror the existing wall's finite
reification exactly, substituting the multi-leader authorized transition. -/

/-- Finite reification of the multi-leader cleanup transition. -/
def multiLeaderCleanupBoundedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa ×
      AuthorizedBoundedAgentState psi kappa :=
  let q := multiLeaderCleanupAuthorizedTransition
    hpsi kappa l.erase r.erase
  let hq := multiLeaderCleanupAuthorizedTransition_inProtocolDomain
    hpsi kappa l.erase r.erase
      l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  (⟨BoundedAgentState.ofDomain q.1.core hq.1,
      q.1.path0Crossed⟩,
   ⟨BoundedAgentState.ofDomain q.2.core hq.2,
      q.2.path0Crossed⟩)

set_option maxHeartbeats 2000000 in
/-- Finite reification erases exactly to the custom authorized transition.
This discharges the first, purely representational part of the raw-to-expiring
bridge; timer behavior is handled separately at the expiring layer. -/
theorem erase_multiLeaderCleanupBoundedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := multiLeaderCleanupBoundedTransition hpsi kappa l r
    (q.1.erase, q.2.erase) =
      multiLeaderCleanupAuthorizedTransition hpsi kappa l.erase r.erase := by
  let q := multiLeaderCleanupAuthorizedTransition
    hpsi kappa l.erase r.erase
  let hq := multiLeaderCleanupAuthorizedTransition_inProtocolDomain
    hpsi kappa l.erase r.erase
      l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  change
    (⟨(BoundedAgentState.ofDomain q.1.core hq.1).erase,
        q.1.path0Crossed⟩,
      ⟨(BoundedAgentState.ofDomain q.2.core hq.2).erase,
        q.2.path0Crossed⟩) = (q.1, q.2)
  rw [BoundedAgentState.erase_ofDomain, BoundedAgentState.erase_ofDomain]

/-- The transition used by deletion drain, dummy sweeps and egress kills. -/
def multiLeaderCleanupTransition
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
  let q := multiLeaderCleanupBoundedTransition
    hpsi kappa l.core r.core
  let lOut : ExpiringAgentState psi kappa tau :=
    ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState psi kappa tau :=
    ⟨q.2, r.stall⟩
  (deletionPriorityExpireOne tau l lOut,
   deletionPriorityExpireOne tau r rOut)

/-- The physical fields used by the cleanup trace and leader-count argument.
Comparison-carrier expiration may clear path metadata, but it cannot change
this projection. -/
structure CleanupPhysicalView (psi : Nat) where
  leader : Bool
  label : Fin psi
  shield : Bool
  bullet : Fin 3
  signal_B : Fin 2
  deriving DecidableEq, Repr

def CleanupPhysicalView.ofState
    (u : AgentState psi) : CleanupPhysicalView psi :=
  ⟨u.leader, u.label, u.shield, u.bullet, u.signal_B⟩

/-- Deletion priority and path-stall expiration preserve every physical field
observed by the cleanup proof, including the leader bit. -/
theorem deletionPriorityExpireOne_cleanupPhysicalView
    (tau : Nat) (old out : ExpiringAgentState psi kappa tau) :
    CleanupPhysicalView.ofState
        (deletionPriorityExpireOne tau old out).core.erase.core =
      CleanupPhysicalView.ofState out.core.erase.core := by
  unfold deletionPriorityExpireOne
  split
  · rfl
  · unfold pathExpireOne
    split
    · rfl
    · split
      · simp [CleanupPhysicalView.ofState, clearComparisonCarrier,
          AuthorizedBoundedAgentState.erase, BoundedAgentState.erase]
      · rfl

/-- The expiring wrapper erases, on all cleanup-relevant physical fields,
to the exact custom authorized transition.  Thus finite reification and timer
accounting introduce no hidden leader, label, shield, bullet, or signal step. -/
theorem multiLeaderCleanupTransition_cleanupPhysicalView
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    let out := multiLeaderCleanupTransition hpsi kappa tau l r
    let raw := multiLeaderCleanupAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
    CleanupPhysicalView.ofState out.1.core.erase.core =
        CleanupPhysicalView.ofState raw.1.core ∧
      CleanupPhysicalView.ofState out.2.core.erase.core =
        CleanupPhysicalView.ofState raw.2.core := by
  let bounded := multiLeaderCleanupBoundedTransition
    hpsi kappa l.core r.core
  let raw := multiLeaderCleanupAuthorizedTransition
    hpsi kappa l.core.erase r.core.erase
  have herase : (bounded.1.erase, bounded.2.erase) = raw :=
    erase_multiLeaderCleanupBoundedTransition hpsi kappa l.core r.core
  have hleft := deletionPriorityExpireOne_cleanupPhysicalView
    tau l (⟨bounded.1, l.stall⟩ : ExpiringAgentState psi kappa tau)
  have hright := deletionPriorityExpireOne_cleanupPhysicalView
    tau r (⟨bounded.2, r.stall⟩ : ExpiringAgentState psi kappa tau)
  change
    CleanupPhysicalView.ofState
          ((deletionPriorityExpireOne tau l
            (⟨bounded.1, l.stall⟩ : ExpiringAgentState psi kappa tau))
            |>.core.erase.core) =
        CleanupPhysicalView.ofState raw.1.core ∧
      CleanupPhysicalView.ofState
          ((deletionPriorityExpireOne tau r
            (⟨bounded.2, r.stall⟩ : ExpiringAgentState psi kappa tau))
            |>.core.erase.core) =
        CleanupPhysicalView.ofState raw.2.core
  constructor
  · calc
      CleanupPhysicalView.ofState
          ((deletionPriorityExpireOne tau l
            (⟨bounded.1, l.stall⟩ : ExpiringAgentState psi kappa tau))
            |>.core.erase.core) =
          CleanupPhysicalView.ofState bounded.1.erase.core := hleft
      _ = CleanupPhysicalView.ofState raw.1.core := by
        exact congrArg (fun u => CleanupPhysicalView.ofState u.core)
          (congrArg Prod.fst herase)
  · calc
      CleanupPhysicalView.ofState
          ((deletionPriorityExpireOne tau r
            (⟨bounded.2, r.stall⟩ : ExpiringAgentState psi kappa tau))
            |>.core.erase.core) =
          CleanupPhysicalView.ofState bounded.2.erase.core := hright
      _ = CleanupPhysicalView.ofState raw.2.core := by
        exact congrArg (fun u => CleanupPhysicalView.ofState u.core)
          (congrArg Prod.snd herase)

/-- Pointwise relation used to transport the five cleanup fields between an
expiring execution and a raw Algorithm-15 execution. -/
def CleanupPhysicalConfigRefinesRaw
    (physical : EConfig n psi kappa tau)
    (raw : Fin n → AgentState psi) : Prop :=
  ∀ i,
    CleanupPhysicalView.ofState (physical i).core.erase.core =
      CleanupPhysicalView.ofState (raw i)

/-- A pair-local cleanup-view simulation lifts to one ring interaction.  The
premise is deliberately relational: expiry may change comparison metadata, so
full-state equality is neither required nor claimed. -/
theorem cleanupPhysicalConfigRefinesRaw_localStep
    (ring : DirectedRing n)
    (physicalT : ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau)
    (rawT : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (hpair : ∀ pl pr rl rr,
      CleanupPhysicalView.ofState pl.core.erase.core =
          CleanupPhysicalView.ofState rl →
        CleanupPhysicalView.ofState pr.core.erase.core =
          CleanupPhysicalView.ofState rr →
        let po := physicalT pl pr
        let ro := rawT rl rr
        CleanupPhysicalView.ofState po.1.core.erase.core =
            CleanupPhysicalView.ofState ro.1 ∧
          CleanupPhysicalView.ofState po.2.core.erase.core =
            CleanupPhysicalView.ofState ro.2)
    (physical : EConfig n psi kappa tau)
    (raw : Fin n → AgentState psi) (e : Fin n)
    (hrefine : CleanupPhysicalConfigRefinesRaw physical raw) :
    CleanupPhysicalConfigRefinesRaw
      (localStep ring physicalT physical e)
      (localStep ring rawT raw e) := by
  let j := ring.rightNeighbor e
  let po := physicalT (physical e) (physical j)
  let ro := rawT (raw e) (raw j)
  have hp := hpair (physical e) (physical j) (raw e) (raw j)
    (hrefine e) (hrefine j)
  change
    CleanupPhysicalView.ofState po.1.core.erase.core =
        CleanupPhysicalView.ofState ro.1 ∧
      CleanupPhysicalView.ofState po.2.core.erase.core =
        CleanupPhysicalView.ofState ro.2 at hp
  intro i
  by_cases hie : i = e
  · subst i
    simpa [localStep, po, ro, j] using hp.1
  · by_cases hij : i = j
    · have hje : j ≠ e := by
        intro h
        exact hie (hij.trans h)
      simpa [localStep, po, ro, j, hie, hij, hje] using hp.2
    · simpa [localStep, po, ro, j, hie, hij] using hrefine i

/-- The same pair-local premise transports cleanup fields through every word.
This is the schedule-level consumer for the still-missing authorized-prefix
edge theorem. -/
theorem cleanupPhysicalConfigRefinesRaw_runLocalSchedule
    (ring : DirectedRing n)
    (physicalT : ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau)
    (rawT : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (hpair : ∀ pl pr rl rr,
      CleanupPhysicalView.ofState pl.core.erase.core =
          CleanupPhysicalView.ofState rl →
        CleanupPhysicalView.ofState pr.core.erase.core =
          CleanupPhysicalView.ofState rr →
        let po := physicalT pl pr
        let ro := rawT rl rr
        CleanupPhysicalView.ofState po.1.core.erase.core =
            CleanupPhysicalView.ofState ro.1 ∧
          CleanupPhysicalView.ofState po.2.core.erase.core =
            CleanupPhysicalView.ofState ro.2)
    (physical : EConfig n psi kappa tau)
    (raw : Fin n → AgentState psi) (word : DetSchedule n)
    (hrefine : CleanupPhysicalConfigRefinesRaw physical raw) :
    CleanupPhysicalConfigRefinesRaw
      (runLocalSchedule ring physicalT physical word)
      (runLocalSchedule ring rawT raw word) := by
  induction word generalizing physical raw with
  | nil => exact hrefine
  | cons e rest ih =>
      simp only [runLocalSchedule]
      apply ih
      exact cleanupPhysicalConfigRefinesRaw_localStep
        ring physicalT rawT hpair physical raw e hrefine

/-! ## Physical leader count

Number of physical `leader = true` agents in a raw configuration.
Defined by List.ofFn summation
(Finset is unavailable without Mathlib). -/

/-- Whether a single agent is a physical leader, as a natural number. -/
def rawLeaderMass (u : AgentState psi) : Nat :=
  if u.leader then 1 else 0

/-- Number of physical leaders in a raw `AgentState` configuration. -/
def rawPhysicalLeaderCount (C : Fin n → AgentState psi) : Nat :=
  (List.ofFn (fun i : Fin n => rawLeaderMass (C i))).sum

/-! ### Count one is semantic uniqueness -/

private def rawLeaderBitsCount {m : Nat} (bits : Fin m → Bool) : Nat :=
  (List.ofFn (fun i => if bits i then 1 else 0)).sum

private theorem rawLeaderBitsCount_succ {m : Nat}
    (bits : Fin (m + 1) → Bool) :
    rawLeaderBitsCount bits =
      (if bits 0 then 1 else 0) +
        rawLeaderBitsCount (fun i : Fin m => bits i.succ) := by
  unfold rawLeaderBitsCount
  rw [List.ofFn_succ, List.sum_cons]

private theorem rawPhysicalLeaderCount_eq_rawLeaderBitsCount
    (C : Fin n → AgentState psi) :
    rawPhysicalLeaderCount C =
      rawLeaderBitsCount (fun i : Fin n => (C i).leader) := by
  rfl

private theorem rawLeaderBitsCount_eq_zero_iff {m : Nat}
    (bits : Fin m → Bool) :
    rawLeaderBitsCount bits = 0 ↔ ∀ i, bits i = false := by
  induction m with
  | zero => simp [rawLeaderBitsCount]
  | succ m ih =>
      rw [rawLeaderBitsCount_succ]
      constructor
      · intro hcount
        have hzero : bits 0 = false := by
          cases hbit : bits 0 <;> simp_all
        have htailCount :
            rawLeaderBitsCount (fun i : Fin m => bits i.succ) = 0 := by
          simp [hzero] at hcount
          omega
        have htail :=
          (ih (fun i : Fin m => bits i.succ)).mp htailCount
        intro i
        cases i using Fin.cases with
        | zero => exact hzero
        | succ i => exact htail i
      · intro hall
        have hzero : bits 0 = false := hall 0
        have htail : ∀ i : Fin m, bits i.succ = false :=
          fun i => hall i.succ
        rw [(ih (fun i : Fin m => bits i.succ)).mpr htail]
        simp [hzero]

private theorem exists_unique_true_of_rawLeaderBitsCount_eq_one
    {m : Nat} (bits : Fin m → Bool)
    (hcount : rawLeaderBitsCount bits = 1) :
    ∃ i : Fin m, bits i = true ∧
      ∀ j : Fin m, bits j = true → j = i := by
  induction m with
  | zero => simp [rawLeaderBitsCount] at hcount
  | succ m ih =>
      rw [rawLeaderBitsCount_succ] at hcount
      cases hzero : bits 0
      · have htailCount :
            rawLeaderBitsCount (fun i : Fin m => bits i.succ) = 1 := by
          simpa [hzero] using hcount
        obtain ⟨i, hi, honly⟩ :=
          ih (fun j : Fin m => bits j.succ) htailCount
        refine ⟨i.succ, hi, ?_⟩
        intro j hj
        cases j using Fin.cases with
        | zero => simp [hzero] at hj
        | succ j' =>
            exact congrArg Fin.succ (honly j' hj)
      · have hsum :
            1 + rawLeaderBitsCount
              (fun i : Fin m => bits i.succ) = 1 := by
          simpa [hzero] using hcount
        have htailCount :
            rawLeaderBitsCount (fun i : Fin m => bits i.succ) = 0 := by
          omega
        have htailFalse :=
          (rawLeaderBitsCount_eq_zero_iff
            (fun i : Fin m => bits i.succ)).mp htailCount
        refine ⟨0, hzero, ?_⟩
        intro j hj
        cases j using Fin.cases with
        | zero => rfl
        | succ j' => simp [htailFalse j'] at hj

/-- A raw physical leader count of one implies the repository's semantic
unique-leader predicate. -/
theorem hasUniqueLeader_of_rawPhysicalLeaderCount_eq_one
    (C : Fin n → AgentState psi)
    (hcount : rawPhysicalLeaderCount C = 1) :
    hasUniqueLeader n C := by
  have hbits :
      rawLeaderBitsCount (fun i : Fin n => (C i).leader) = 1 := by
    rw [← rawPhysicalLeaderCount_eq_rawLeaderBitsCount C]
    exact hcount
  obtain ⟨leader, hleader, honly⟩ :=
    exists_unique_true_of_rawLeaderBitsCount_eq_one
      (fun i : Fin n => (C i).leader) hbits
  refine ⟨leader, ?_, ?_⟩
  · change (C leader).leader = true
    exact hleader
  · intro i hi
    apply honly i
    change (C i).leader = true at hi
    exact hi

private theorem rawLeaderCount_ofFn_le
    (f g : Fin n → Nat) (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.sum_cons,
      List.ofFn_succ, List.sum_cons]
    exact Nat.add_le_add (hfg 0)
      (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hfg i.succ))

private theorem rawLeaderCount_ofFn_lt_of_single_lt
    (f g : Fin n → Nat) (j : Fin n)
    (hle : ∀ i, f i ≤ g i) (hlt : f j < g j) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    rw [List.ofFn_succ, List.sum_cons,
      List.ofFn_succ, List.sum_cons]
    by_cases hj0 : j = 0
    · subst j
      have htail := rawLeaderCount_ofFn_le
        (fun i : Fin n => f i.succ) (fun i : Fin n => g i.succ)
        (fun i => hle i.succ)
      omega
    · have hjpos : 0 < j.val := by
        have hjne : j.val ≠ 0 := fun h => hj0 (Fin.ext (by simpa using h))
        omega
      let j' : Fin n := ⟨j.val - 1, by omega⟩
      have hjsucc : j'.succ = j := Fin.ext (by simp [j']; omega)
      have htail := ih (fun i => f i.succ) (fun i => g i.succ) j'
        (fun i => hle i.succ) (hjsucc ▸ hlt)
      have hhead := hle 0
      omega

/-- Pointwise framing away from one true-to-false victim strictly lowers the
physical leader count. -/
theorem rawPhysicalLeaderCount_lt_of_single_drop
    {n psi : Nat}
    (C D : Fin n → AgentState psi) (victim : Fin n)
    (hbefore : (C victim).leader = true)
    (hafter : (D victim).leader = false)
    (hother : ∀ i, i ≠ victim →
      (D i).leader = (C i).leader) :
    rawPhysicalLeaderCount D < rawPhysicalLeaderCount C := by
  unfold rawPhysicalLeaderCount
  apply rawLeaderCount_ofFn_lt_of_single_lt _ _ victim
  · intro i
    by_cases hi : i = victim
    · subst hi; simp [rawLeaderMass, hbefore, hafter]
    · rw [rawLeaderMass, rawLeaderMass, hother i hi]
      exact Nat.le_refl _
  · simp [rawLeaderMass, hbefore, hafter]

/-! ## Two-leader cleanup schedule

Proof data and deterministic word for eliminating one of two nonadjacent
leaders. -/

/-- The first `steps` clockwise edge indices beginning at `start`. -/
def clockwiseEdgeSchedule (ring : DirectedRing n) (start : Fin n) :
    Nat → DetSchedule n
  | 0 => []
  | steps + 1 =>
      clockwiseEdgeSchedule ring start steps ++
        [cwPos ring start steps]

@[simp] theorem clockwiseEdgeSchedule_length
    (ring : DirectedRing n) (start : Fin n) (steps : Nat) :
    (clockwiseEdgeSchedule ring start steps).length = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [clockwiseEdgeSchedule, ih]

/-- Descending positive offsets `[count, ..., 1]`.  This is the edge order
that moves a responder bullet counterclockwise from a target back toward the
source leader. -/
def reversePositiveEdgeSchedule
    (ring : DirectedRing n) (start : Fin n) :
    Nat → DetSchedule n
  | 0 => []
  | count + 1 =>
      cwPos ring start (count + 1) ::
        reversePositiveEdgeSchedule ring start count

@[simp] theorem reversePositiveEdgeSchedule_length
    (ring : DirectedRing n) (start : Fin n) (count : Nat) :
    (reversePositiveEdgeSchedule ring start count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [reversePositiveEdgeSchedule, ih]

private theorem cwPos_ne_of_ne_below_cleanup
    (ring : DirectedRing n) (start : Fin n)
    {a b : Nat} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    cwPos ring start a ≠ cwPos ring start b := by
  intro hpos
  apply hab
  have ha' := cwPos_bounded_unique ring start
    (cwPos ring start a) a ha rfl
  have hb' := cwPos_bounded_unique ring start
    (cwPos ring start a) b hb hpos.symm
  exact ha'.trans hb'.symm

theorem applySchedule_append_cleanup
    (ring : DirectedRing n)
    (T : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (C : Fin n → AgentState psi) (first second : DetSchedule n) :
    applySchedule ring T C (first ++ second) =
      applySchedule ring T (applySchedule ring T C first) second := by
  induction first generalizing C with
  | nil => rfl
  | cons e rest ih => exact ih (stepConfig ring T C e)

theorem stepConfig_left_cleanup
    (ring : DirectedRing n)
    (T : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (C : Fin n → AgentState psi) (e : Fin n) :
    stepConfig ring T C e e =
      (T (C e) (C (ring.rightNeighbor e))).1 := by
  simp [stepConfig]

theorem stepConfig_right_cleanup
    (ring : DirectedRing n)
    (T : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (C : Fin n → AgentState psi) (e : Fin n)
    (hne : e ≠ ring.rightNeighbor e) :
    stepConfig ring T C e (ring.rightNeighbor e) =
      (T (C e) (C (ring.rightNeighbor e))).2 := by
  simp [stepConfig, Ne.symm hne]

theorem stepConfig_untouched_cleanup
    (ring : DirectedRing n)
    (T : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (C : Fin n → AgentState psi) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    stepConfig ring T C e i = C i := by
  simp [stepConfig, hi, hj]

theorem stepConfig_view_frame_cleanup
    {alpha : Type} (view : AgentState psi → alpha)
    (ring : DirectedRing n)
    (T : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (C : Fin n → AgentState psi) (e : Fin n)
    (hleft : view (T (C e) (C (ring.rightNeighbor e))).1 = view (C e))
    (hright : view (T (C e) (C (ring.rightNeighbor e))).2 =
      view (C (ring.rightNeighbor e))) :
    ∀ i, view (stepConfig ring T C e i) = view (C i) := by
  intro i
  by_cases hi : i = e
  · subst i
    simpa [stepConfig] using hleft
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simpa [stepConfig, hi] using hright
    · simp [stepConfig, hi, hj]

/-! ## Forward absence-signal circuit

The leader-sink delivery makes the final edge independent of its label.  The
state records a zero-bullet arc rather than global bullet freedom: after the
first circuit, the repeated victim edge deliberately parks one dummy bullet
on the complementary arc. -/

structure ForwardCleanupSignalState
    (hpsi : psi > 0) (ring : DirectedRing n)
    (start : Fin n) (limit : Nat)
    (initial current : Fin n → AgentState psi)
    (steps : Nat) : Prop where
  steps_le : steps ≤ limit
  limit_lt : limit < n
  leaders_frame : ∀ i, (current i).leader = (initial i).leader
  labels_frame : ∀ i, (current i).label = (initial i).label
  shields_frame : ∀ i, (current i).shield = (initial i).shield
  arc_bullets_zero : ∀ k, k ≤ limit →
    (current (cwPos ring start k)).bullet = ⟨0, by omega⟩
  outside_bullet_frame : ∀ k, limit < k → k < n →
    (current (cwPos ring start k)).bullet =
      (initial (cwPos ring start k)).bullet
  source_signal_zero : (current start).signal_B = ⟨0, by omega⟩
  visited_signal_one : ∀ k, 0 < k → k ≤ steps →
    (current (cwPos ring start k)).signal_B = ⟨1, by omega⟩
  ahead_signal_zero : ∀ k, steps < k → k ≤ limit →
    (current (cwPos ring start k)).signal_B = ⟨0, by omega⟩
  outside_signal_frame : ∀ k, limit < k → k < n →
    (current (cwPos ring start k)).signal_B =
      (initial (cwPos ring start k)).signal_B

theorem ForwardCleanupSignalState.bullets_zero_of_initial
    {n psi : Nat} {hpsi : psi > 0} {ring : DirectedRing n}
    {start : Fin n} {limit steps : Nat}
    {initial current : Fin n → AgentState psi}
    (hstate : ForwardCleanupSignalState hpsi ring start limit
      initial current steps)
    (hzero : ∀ i, (initial i).bullet = ⟨0, by omega⟩) :
    ∀ i, (current i).bullet = ⟨0, by omega⟩ := by
  intro i
  let k := cwDist ring start i
  have hk : k < n := cwDist_lt ring start i
  have hpos : cwPos ring start k = i := cwPos_cwDist ring start i
  rw [← hpos]
  by_cases hkle : k ≤ limit
  · exact hstate.arc_bullets_zero k hkle
  · rw [hstate.outside_bullet_frame k (by omega) hk]
    exact hzero _

private theorem forwardCleanupSignalState_zero
    (hpsi : psi > 0) (ring : DirectedRing n)
    (start : Fin n) (limit : Nat)
    (C : Fin n → AgentState psi)
    (hlimit : limit < n)
    (hbullets : ∀ k, k ≤ limit →
      (C (cwPos ring start k)).bullet = ⟨0, by omega⟩)
    (hsignals : ∀ k, k ≤ limit →
      (C (cwPos ring start k)).signal_B = ⟨0, by omega⟩) :
    ForwardCleanupSignalState hpsi ring start limit C C 0 := by
  refine
    { steps_le := Nat.zero_le _
      limit_lt := hlimit
      leaders_frame := fun _ => rfl
      labels_frame := fun _ => rfl
      shields_frame := fun _ => rfl
      arc_bullets_zero := hbullets
      outside_bullet_frame := by intro k hk hkn; rfl
      source_signal_zero := by simpa using hsignals 0 (Nat.zero_le _)
      visited_signal_one := by intro k hk hk'; omega
      ahead_signal_zero := by intro k hk0 hk; exact hsignals k hk
      outside_signal_frame := by intro k hk hkn; rfl }

private theorem forwardCleanupSignalState_step
    (hpsi : psi > 0) (ring : DirectedRing n)
    (start : Fin n) (limit steps : Nat)
    (initial current : Fin n → AgentState psi)
    (hstate : ForwardCleanupSignalState hpsi ring start limit
      initial current steps)
    (hsourceLeader : (initial start).leader = true)
    (hendLeader :
      (initial (cwPos ring start limit)).leader = true)
    (hfollowers : ∀ k, 0 < k → k < limit →
      (initial (cwPos ring start k)).leader = false)
    (halign : ∀ k, k + 1 < limit →
      (initial (cwPos ring start (k + 1))).label =
        ⟨((initial (cwPos ring start k)).label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩)
    (hnext : steps < limit) :
    ForwardCleanupSignalState hpsi ring start limit initial
      (stepConfig ring (eliminateLeadersNoCollisionEgressSink hpsi)
        current (cwPos ring start steps)) (steps + 1) := by
  let T := eliminateLeadersNoCollisionEgressSink hpsi
  let e := cwPos ring start steps
  let j := ring.rightNeighbor e
  let out := stepConfig ring T current e
  have heLt : steps < n :=
    Nat.lt_of_le_of_lt hstate.steps_le hstate.limit_lt
  have hjLt : steps + 1 < n :=
    Nat.lt_of_le_of_lt (by omega) hstate.limit_lt
  have hj : j = cwPos ring start (steps + 1) := by
    dsimp [j, e]
    simp
  have hene : e ≠ j := by
    rw [hj]
    simpa [e] using cwPos_ne_of_ne_below_cleanup ring start
      (a := steps) (b := steps + 1) heLt hjLt (by omega)
  have hleftBullet : (current e).bullet = ⟨0, by omega⟩ := by
    simpa [e] using hstate.arc_bullets_zero steps (by omega)
  have hrightBullet : (current j).bullet = ⟨0, by omega⟩ := by
    rw [hj]
    exact hstate.arc_bullets_zero (steps + 1) (by omega)
  have hrightSignal : (current j).signal_B = ⟨0, by omega⟩ := by
    rw [hj]
    exact hstate.ahead_signal_zero (steps + 1) (by omega) (by omega)
  have hnoLeftFire : (current e).leader = false ∨
      (current e).signal_B = ⟨0, by omega⟩ := by
    by_cases hs : steps = 0
    · right
      simpa [e, hs] using hstate.source_signal_zero
    · left
      rw [hstate.leaders_frame]
      exact hfollowers steps (by omega) hnext
  have hsource : (current e).leader = true ∨
      (current e).signal_B = ⟨1, by omega⟩ := by
    by_cases hs : steps = 0
    · left
      rw [hstate.leaders_frame]
      simpa [e, hs] using hsourceLeader
    · right
      simpa [e] using
        hstate.visited_signal_one steps (by omega) (Nat.le_refl _)
  have hdeliver : (current j).label =
        ⟨((current e).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ ∨
      (current j).leader = true := by
    by_cases hfinal : steps + 1 = limit
    · right
      rw [hstate.leaders_frame, hj, hfinal]
      exact hendLeader
    · left
      rw [hstate.labels_frame, hstate.labels_frame, hj]
      simpa [e] using halign steps (by omega)
  have hlocal := cleanupSignalStepOutput hpsi (current e) (current j)
    hleftBullet hrightBullet hnoLeftFire (Or.inr hrightSignal)
    hsource hdeliver
  have hleadersStep : ∀ i, (out i).leader = (current i).leader := by
    apply stepConfig_view_frame_cleanup (view := fun u => u.leader)
    · simpa [T, j] using hlocal.leaderL
    · simpa [T, j] using hlocal.leaderR
  have hlabelsStep : ∀ i, (out i).label = (current i).label := by
    apply stepConfig_view_frame_cleanup (view := fun u => u.label)
    · simpa [T, j] using hlocal.labelL
    · simpa [T, j] using hlocal.labelR
  have hshieldsStep : ∀ i, (out i).shield = (current i).shield := by
    apply stepConfig_view_frame_cleanup (view := fun u => u.shield)
    · simpa [T, j] using hlocal.shieldL
    · simpa [T, j] using hlocal.shieldR
  have hbulletLeft :
      (T (current e) (current (ring.rightNeighbor e))).1.bullet =
        (current e).bullet := by
    calc
      _ = ⟨0, by omega⟩ := by simpa [T, j] using hlocal.bulletL
      _ = (current e).bullet := hleftBullet.symm
  have hbulletRight :
      (T (current e) (current (ring.rightNeighbor e))).2.bullet =
        (current (ring.rightNeighbor e)).bullet := by
    calc
      _ = ⟨0, by omega⟩ := by simpa [T, j] using hlocal.bulletR
      _ = (current (ring.rightNeighbor e)).bullet := by
        simpa [j] using hrightBullet.symm
  have hbulletsStep : ∀ i, (out i).bullet = (current i).bullet :=
    stepConfig_view_frame_cleanup (view := fun u => u.bullet)
      ring T current e hbulletLeft hbulletRight
  have hleft : out e = (T (current e) (current j)).1 := by
    simpa [out, j] using stepConfig_left_cleanup ring T current e
  have hright : out j = (T (current e) (current j)).2 := by
    have : e ≠ ring.rightNeighbor e := by simpa [j] using hene
    simpa [out, j] using stepConfig_right_cleanup ring T current e this
  change ForwardCleanupSignalState hpsi ring start limit initial out (steps + 1)
  refine
    { steps_le := by omega
      limit_lt := hstate.limit_lt
      leaders_frame := fun i =>
        (hleadersStep i).trans (hstate.leaders_frame i)
      labels_frame := fun i =>
        (hlabelsStep i).trans (hstate.labels_frame i)
      shields_frame := fun i =>
        (hshieldsStep i).trans (hstate.shields_frame i)
      arc_bullets_zero := ?_
      outside_bullet_frame := ?_
      source_signal_zero := ?_
      visited_signal_one := ?_
      ahead_signal_zero := ?_
      outside_signal_frame := ?_ }
  · intro k hk
    rw [hbulletsStep]
    exact hstate.arc_bullets_zero k hk
  · intro k hk hkn
    rw [hbulletsStep]
    exact hstate.outside_bullet_frame k hk hkn
  · by_cases hs : steps = 0
    · have heq : e = start := by simp [e, hs]
      calc
        (out start).signal_B = (out e).signal_B := by rw [heq]
        _ = (T (current e) (current j)).1.signal_B :=
          congrArg (fun u => u.signal_B) hleft
        _ = (current e).signal_B := by simpa [T] using hlocal.signalL
        _ = (current start).signal_B := by rw [heq]
        _ = ⟨0, by omega⟩ := hstate.source_signal_zero
    · have hse : start ≠ e := by
        simpa [e] using cwPos_ne_of_ne_below_cleanup ring start
          (a := 0) (b := steps) ring.hn heLt (by omega)
      have hsj : start ≠ j := by
        rw [hj]
        simpa using cwPos_ne_of_ne_below_cleanup ring start
          (a := 0) (b := steps + 1) ring.hn hjLt (by omega)
      have hu : out start = current start := by
        apply stepConfig_untouched_cleanup ring T current e start hse
        simpa [j] using hsj
      rw [hu]
      exact hstate.source_signal_zero
  · intro k hk0 hkle
    by_cases hknew : k = steps + 1
    · subst k
      calc
        (out (cwPos ring start (steps + 1))).signal_B =
            (out j).signal_B := by rw [← hj]
        _ = (T (current e) (current j)).2.signal_B :=
          congrArg (fun u => u.signal_B) hright
        _ = ⟨1, by omega⟩ := by simpa [T] using hlocal.signalR
    · have hkold : k ≤ steps := by omega
      by_cases hkeq : k = steps
      · subst k
        calc
          (out (cwPos ring start steps)).signal_B = (out e).signal_B := by rfl
          _ = (T (current e) (current j)).1.signal_B :=
            congrArg (fun u => u.signal_B) hleft
          _ = (current e).signal_B := by simpa [T] using hlocal.signalL
          _ = ⟨1, by omega⟩ := by
            simpa [e] using
              hstate.visited_signal_one steps hk0 (Nat.le_refl _)
      · have hkLt : k < steps := by omega
        have hkN : k < n := by omega
        have hke : cwPos ring start k ≠ e := by
          simpa [e] using cwPos_ne_of_ne_below_cleanup ring start
            (a := k) (b := steps) hkN heLt (by omega)
        have hkj : cwPos ring start k ≠ j := by
          rw [hj]
          exact cwPos_ne_of_ne_below_cleanup ring start hkN hjLt (by omega)
        have hu : out (cwPos ring start k) = current (cwPos ring start k) := by
          apply stepConfig_untouched_cleanup ring T current e _ hke
          simpa [j] using hkj
        rw [hu]
        exact hstate.visited_signal_one k hk0 hkold
  · intro k hkstep hklimit
    have hkN : k < n := Nat.lt_of_le_of_lt hklimit hstate.limit_lt
    have hke : cwPos ring start k ≠ e := by
      simpa [e] using cwPos_ne_of_ne_below_cleanup ring start
        (a := k) (b := steps) hkN heLt (by omega)
    have hkj : cwPos ring start k ≠ j := by
      rw [hj]
      exact cwPos_ne_of_ne_below_cleanup ring start hkN hjLt (by omega)
    have hu : out (cwPos ring start k) = current (cwPos ring start k) := by
      apply stepConfig_untouched_cleanup ring T current e _ hke
      simpa [j] using hkj
    rw [hu]
    exact hstate.ahead_signal_zero k (by omega) hklimit
  · intro k hklimit hkn
    have hke : cwPos ring start k ≠ e := by
      simpa [e] using cwPos_ne_of_ne_below_cleanup ring start
        (a := k) (b := steps) hkn heLt (by omega)
    have hkj : cwPos ring start k ≠ j := by
      rw [hj]
      exact cwPos_ne_of_ne_below_cleanup ring start hkn hjLt (by omega)
    have hu : out (cwPos ring start k) = current (cwPos ring start k) := by
      apply stepConfig_untouched_cleanup ring T current e _ hke
      simpa [j] using hkj
    rw [hu]
    exact hstate.outside_signal_frame k hklimit hkn

theorem forwardCleanupSignalSchedule
    (hpsi : psi > 0) (ring : DirectedRing n)
    (start : Fin n) (limit steps : Nat)
    (C : Fin n → AgentState psi)
    (hsteps : steps ≤ limit) (hlimit : limit < n)
    (hbullets : ∀ k, k ≤ limit →
      (C (cwPos ring start k)).bullet = ⟨0, by omega⟩)
    (hsignals : ∀ k, k ≤ limit →
      (C (cwPos ring start k)).signal_B = ⟨0, by omega⟩)
    (hsourceLeader : (C start).leader = true)
    (hendLeader : (C (cwPos ring start limit)).leader = true)
    (hfollowers : ∀ k, 0 < k → k < limit →
      (C (cwPos ring start k)).leader = false)
    (halign : ∀ k, k + 1 < limit →
      (C (cwPos ring start (k + 1))).label =
        ⟨((C (cwPos ring start k)).label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩) :
    ForwardCleanupSignalState hpsi ring start limit C
      (applySchedule ring (eliminateLeadersNoCollisionEgressSink hpsi) C
        (clockwiseEdgeSchedule ring start steps)) steps := by
  induction steps with
  | zero =>
      simpa [clockwiseEdgeSchedule, applySchedule] using
        forwardCleanupSignalState_zero hpsi ring start limit C
          hlimit hbullets hsignals
  | succ s ih =>
      have hsle : s ≤ limit := by omega
      have hslt : s < limit := by omega
      have hprev := ih hsle hbullets hsignals
      have hnext := forwardCleanupSignalState_step hpsi ring start limit s
        C (applySchedule ring (eliminateLeadersNoCollisionEgressSink hpsi) C
          (clockwiseEdgeSchedule ring start s))
        hprev hsourceLeader hendLeader hfollowers halign hslt
      rw [show clockwiseEdgeSchedule ring start (s + 1) =
        clockwiseEdgeSchedule ring start s ++ [cwPos ring start s] from rfl]
      rw [applySchedule_append_cleanup]
      simpa [applySchedule] using hnext

/-! ## Reverse live-bullet transport -/

structure ReverseCleanupLiveOutput
    (ring : DirectedRing n) (start : Fin n)
    (before after : Fin n → AgentState psi) : Prop where
  live_at_one : (after (cwPos ring start 1)).bullet = ⟨2, by omega⟩
  live_signal_zero :
    (after (cwPos ring start 1)).signal_B = ⟨0, by omega⟩
  leaders_frame : ∀ i, (after i).leader = (before i).leader
  labels_frame : ∀ i, (after i).label = (before i).label
  start_unchanged : after start = before start

/-- Descending positive edges move one live bullet from offset `count+1` to
offset one.  `hroute` admits the first label-zero leader egress and ordinary
aligned follower edges thereafter. -/
theorem reversePositiveEdgeSchedule_moves_live_cleanup
    (hpsi : psi > 0) (ring : DirectedRing n)
    (start : Fin n) (count : Nat)
    (C : Fin n → AgentState psi)
    (hbound : count + 1 < n)
    (hlive : (C (cwPos ring start (count + 1))).bullet =
      ⟨2, by omega⟩)
    (hliveSignal :
      (C (cwPos ring start (count + 1))).signal_B = ⟨0, by omega⟩)
    (hfollowers : ∀ k, 0 < k → k ≤ count →
      (C (cwPos ring start k)).leader = false)
    (hroute : ∀ k, 0 < k → k ≤ count →
      (C (cwPos ring start (k + 1))).label =
          ⟨((C (cwPos ring start k)).label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩ ∨
        ((C (cwPos ring start (k + 1))).leader = true ∧
          (C (cwPos ring start (k + 1))).label = ⟨0, hpsi⟩)) :
    ReverseCleanupLiveOutput ring start C
      (applySchedule ring (eliminateLeadersNoCollisionEgressSink hpsi) C
        (reversePositiveEdgeSchedule ring start count)) := by
  induction count generalizing C with
  | zero =>
      refine
        { live_at_one := by
            simpa [reversePositiveEdgeSchedule, applySchedule] using hlive
          live_signal_zero := by
            simpa [reversePositiveEdgeSchedule, applySchedule] using hliveSignal
          leaders_frame := fun _ => rfl
          labels_frame := fun _ => rfl
          start_unchanged := rfl }
  | succ c ih =>
      let T := eliminateLeadersNoCollisionEgressSink hpsi
      let e := cwPos ring start (c + 1)
      let j := ring.rightNeighbor e
      let C1 := stepConfig ring T C e
      have hj : j = cwPos ring start (c + 2) := by
        dsimp [j, e]
        simp
      have heLt : c + 1 < n := by omega
      have hjLt : c + 2 < n := by omega
      have hene : e ≠ j := by
        rw [hj]
        simpa [e] using cwPos_ne_of_ne_below_cleanup ring start
          (a := c + 1) (b := c + 2) heLt hjLt (by omega)
      have heFollower : (C e).leader = false := by
        simpa [e] using
          hfollowers (c + 1) (by omega) (Nat.le_refl _)
      have hlocal := cleanupLiveMoveOutput hpsi (C e) (C j)
        heFollower
        (by simpa [hj] using hlive)
        (Or.inr (by simpa [hj] using hliveSignal))
        (by simpa [e, hj] using hroute (c + 1) (by omega) (Nat.le_refl _))
      have hlocal' : CleanupLiveMoveOutput
          (C e) (C (ring.rightNeighbor e))
          (T (C e) (C (ring.rightNeighbor e))) := by
        simpa [T, j] using hlocal
      have hleaders1 : ∀ i, (C1 i).leader = (C i).leader :=
        stepConfig_view_frame_cleanup (view := fun u => u.leader)
          ring T C e (hlocal'.leaderL.trans heFollower.symm) hlocal'.leaderR
      have hlabels1 : ∀ i, (C1 i).label = (C i).label :=
        stepConfig_view_frame_cleanup (view := fun u => u.label)
          ring T C e hlocal'.labelL hlocal'.labelR
      have hleft : C1 e = (T (C e) (C j)).1 := by
        simpa [C1, j] using stepConfig_left_cleanup ring T C e
      have hstartE : start ≠ e := by
        simpa [e] using cwPos_ne_of_ne_below_cleanup ring start
          (a := 0) (b := c + 1) ring.hn heLt (by omega)
      have hstartJ : start ≠ j := by
        rw [hj]
        simpa using cwPos_ne_of_ne_below_cleanup ring start
          (a := 0) (b := c + 2) ring.hn hjLt (by omega)
      have hstart1 : C1 start = C start := by
        apply stepConfig_untouched_cleanup ring T C e start hstartE
        simpa [j] using hstartJ
      have hlive1 : (C1 (cwPos ring start (c + 1))).bullet =
          ⟨2, by omega⟩ := by
        calc
          (C1 (cwPos ring start (c + 1))).bullet = (C1 e).bullet := by rfl
          _ = (T (C e) (C j)).1.bullet :=
            congrArg (fun u => u.bullet) hleft
          _ = ⟨2, by omega⟩ := hlocal.bulletL
      have hliveSignal1 :
          (C1 (cwPos ring start (c + 1))).signal_B =
            ⟨0, by omega⟩ := by
        calc
          (C1 (cwPos ring start (c + 1))).signal_B = (C1 e).signal_B := by rfl
          _ = (T (C e) (C j)).1.signal_B :=
            congrArg (fun u => u.signal_B) hleft
          _ = ⟨0, by omega⟩ := hlocal.signalL
      have hfollowers1 : ∀ k, 0 < k → k ≤ c →
          (C1 (cwPos ring start k)).leader = false := by
        intro k hk0 hkc
        rw [hleaders1]
        exact hfollowers k hk0 (by omega)
      have hroute1 : ∀ k, 0 < k → k ≤ c →
          (C1 (cwPos ring start (k + 1))).label =
              ⟨((C1 (cwPos ring start k)).label.val + 1) % psi,
                Nat.mod_lt _ hpsi⟩ ∨
            ((C1 (cwPos ring start (k + 1))).leader = true ∧
              (C1 (cwPos ring start (k + 1))).label = ⟨0, hpsi⟩) := by
        intro k hk0 hkc
        rw [hleaders1, hlabels1, hlabels1]
        exact hroute k hk0 (by omega)
      have hrec := ih C1 (by omega) hlive1 hliveSignal1
        hfollowers1 hroute1
      rw [show reversePositiveEdgeSchedule ring start (c + 1) =
        cwPos ring start (c + 1) ::
          reversePositiveEdgeSchedule ring start c from rfl]
      change ReverseCleanupLiveOutput ring start C
        (applySchedule ring T C1
          (reversePositiveEdgeSchedule ring start c))
      exact
        { live_at_one := hrec.live_at_one
          live_signal_zero := hrec.live_signal_zero
          leaders_frame := fun i =>
            (hrec.leaders_frame i).trans (hleaders1 i)
          labels_frame := fun i =>
            (hrec.labels_frame i).trans (hlabels1 i)
          start_unchanged := hrec.start_unchanged.trans hstart1 }

/-- Proof data choosing two nonadjacent leaders and the two clockwise arc
lengths between them. -/
structure TwoLeaderCleanupSchedule (ring : DirectedRing n) where
  L1 : Fin n
  L2 : Fin n
  leaders_ne : L1 ≠ L2
  d12 : Nat
  d21 : Nat
  d12_eq : d12 = cwDist ring L1 L2
  d21_eq : d21 = cwDist ring L2 L1
  d12_pos : 0 < d12
  d21_pos : 0 < d21
  d12_lt : d12 < n
  d21_lt : d21 < n
  d12_nonadjacent : 1 < d12
  d21_nonadjacent : 1 < d21
  partition : d12 + d21 = n

namespace TwoLeaderCleanupSchedule

variable {ring : DirectedRing n}

/-- The exact word:

1. `d12` clockwise edges deliver L1's signal to L2;
2. repeat L2's incoming edge, firing right and ejecting its dummy bullet;
3. `d21` clockwise edges deliver L2's signal to L1;
4. fire L1 on its outgoing edge;
5. descend the opposite arc, moving the live bullet to L2's successor;
6. fire `L2 -> successor L2` for the live hit. -/
def word (plan : TwoLeaderCleanupSchedule ring) : DetSchedule n :=
  clockwiseEdgeSchedule ring plan.L1 plan.d12 ++
    [cwPos ring plan.L1 (plan.d12 - 1)] ++
    clockwiseEdgeSchedule ring plan.L2 plan.d21 ++
    [plan.L1] ++
    reversePositiveEdgeSchedule ring plan.L2 (plan.d21 - 1) ++
    [plan.L2]

/-- Exact advertised length. -/
theorem word_length (plan : TwoLeaderCleanupSchedule ring) :
    plan.word.length = plan.d12 + 2 * plan.d21 + 2 := by
  have hd21 := plan.d21_pos
  simp [word]
  omega

/-- Execute the word under the egress-sink raw Algorithm-15 kernel. -/
def output (hpsi : psi > 0)
    (plan : TwoLeaderCleanupSchedule ring)
    (C : Fin n → AgentState psi) : Fin n → AgentState psi :=
  applySchedule ring
    (eliminateLeadersNoCollisionEgressSink hpsi)
    C plan.word

end TwoLeaderCleanupSchedule

private theorem cwPos_add_cleanup
    (ring : DirectedRing n) (start : Fin n) (a b : Nat) :
    cwPos ring (cwPos ring start a) b = cwPos ring start (a + b) := by
  apply Fin.ext
  unfold cwPos
  dsimp only
  rw [Nat.mod_add_mod]
  congr 1
  omega

private theorem rightNeighbor_eq_cwPos_one_cleanup
    (ring : DirectedRing n) (start : Fin n) :
    ring.rightNeighbor start = cwPos ring start 1 := by
  simp

private theorem cleanupPlan_target12
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring) :
    cwPos ring plan.L1 plan.d12 = plan.L2 := by
  rw [plan.d12_eq]
  exact cwPos_cwDist ring plan.L1 plan.L2

private theorem cleanupPlan_target21
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring) :
    cwPos ring plan.L2 plan.d21 = plan.L1 := by
  rw [plan.d21_eq]
  exact cwPos_cwDist ring plan.L2 plan.L1

private theorem cleanupPlan_predecessor12_right
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring) :
    ring.rightNeighbor (cwPos ring plan.L1 (plan.d12 - 1)) = plan.L2 := by
  have hdpos := plan.d12_pos
  calc
    ring.rightNeighbor (cwPos ring plan.L1 (plan.d12 - 1)) =
        cwPos ring plan.L1 ((plan.d12 - 1) + 1) :=
      (cwPos_succ ring plan.L1 (plan.d12 - 1)).symm
    _ = cwPos ring plan.L1 plan.d12 := by congr 2 <;> omega
    _ = plan.L2 := cleanupPlan_target12 ring plan

private theorem cleanupPlan_arc21_as_arc12
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring)
    (k : Nat) :
    cwPos ring plan.L2 k = cwPos ring plan.L1 (plan.d12 + k) := by
  calc
    cwPos ring plan.L2 k =
        cwPos ring (cwPos ring plan.L1 plan.d12) k := by
      rw [cleanupPlan_target12 ring plan]
    _ = cwPos ring plan.L1 (plan.d12 + k) :=
      cwPos_add_cleanup ring plan.L1 plan.d12 k

private theorem cleanupPlan_pred12_ne_L2
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring) :
    cwPos ring plan.L1 (plan.d12 - 1) ≠ plan.L2 := by
  have hdpos := plan.d12_pos
  have hdlt := plan.d12_lt
  rw [← cleanupPlan_target12 ring plan]
  exact cwPos_ne_of_ne_below_cleanup ring plan.L1
    (by omega) plan.d12_lt (by omega)

private theorem cleanupPlan_L1_ne_pred12
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring) :
    plan.L1 ≠ cwPos ring plan.L1 (plan.d12 - 1) := by
  have hdpos := plan.d12_pos
  have hdlt := plan.d12_lt
  have hdnon := plan.d12_nonadjacent
  simpa using cwPos_ne_of_ne_below_cleanup ring plan.L1
    (a := 0) (b := plan.d12 - 1) ring.hn (by omega) (by omega)

private theorem cleanupPlan_arc21_interior_ne_pred12
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring)
    (k : Nat) (hk0 : 0 < k) (hk : k < plan.d21) :
    cwPos ring plan.L2 k ≠ cwPos ring plan.L1 (plan.d12 - 1) := by
  have hpart := plan.partition
  have hdpos := plan.d12_pos
  have hdlt := plan.d12_lt
  rw [cleanupPlan_arc21_as_arc12 ring plan k]
  exact cwPos_ne_of_ne_below_cleanup ring plan.L1
    (by omega) (by omega) (by omega)

private theorem cleanupPlan_arc21_interior_ne_L2
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring)
    (k : Nat) (hk0 : 0 < k) (hk : k < plan.d21) :
    cwPos ring plan.L2 k ≠ plan.L2 := by
  have hdlt := plan.d21_lt
  intro h
  have hne := cwPos_ne_of_ne_below_cleanup ring plan.L2
    (a := k) (b := 0) (by omega) ring.hn (by omega)
  exact hne (by simpa using h)

private theorem cleanupPlan_arc21_interior_ne_L1
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring)
    (k : Nat) (_hk0 : 0 < k) (hk : k < plan.d21) :
    cwPos ring plan.L2 k ≠ plan.L1 := by
  have hdlt := plan.d21_lt
  rw [← cleanupPlan_target21 ring plan]
  exact cwPos_ne_of_ne_below_cleanup ring plan.L2
    (by omega) plan.d21_lt (by omega)

private theorem cleanupPlan_L2_ne_rightNeighbor_L1
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring) :
    plan.L2 ≠ ring.rightNeighbor plan.L1 := by
  have hdlt := plan.d12_lt
  have hdnon := plan.d12_nonadjacent
  rw [rightNeighbor_eq_cwPos_one_cleanup ring plan.L1,
    ← cleanupPlan_target12 ring plan]
  exact cwPos_ne_of_ne_below_cleanup ring plan.L1
    plan.d12_lt (by omega) (by omega)

private theorem cleanupPlan_L1_ne_rightNeighbor_L2
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring) :
    plan.L1 ≠ ring.rightNeighbor plan.L2 := by
  have hdlt := plan.d21_lt
  have hdnon := plan.d21_nonadjacent
  rw [rightNeighbor_eq_cwPos_one_cleanup ring plan.L2,
    ← cleanupPlan_target21 ring plan]
  exact cwPos_ne_of_ne_below_cleanup ring plan.L2
    plan.d21_lt (by omega) (by omega)

private theorem cleanupPlan_self_ne_rightNeighbor_L1
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring) :
    plan.L1 ≠ ring.rightNeighbor plan.L1 := by
  have hdlt := plan.d12_lt
  have hdnon := plan.d12_nonadjacent
  rw [rightNeighbor_eq_cwPos_one_cleanup ring plan.L1]
  simpa using cwPos_ne_of_ne_below_cleanup ring plan.L1
    (a := 0) (b := 1) ring.hn (by omega) (by omega)

private theorem cleanupPlan_self_ne_rightNeighbor_L2
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring) :
    plan.L2 ≠ ring.rightNeighbor plan.L2 := by
  have hdlt := plan.d21_lt
  have hdnon := plan.d21_nonadjacent
  rw [rightNeighbor_eq_cwPos_one_cleanup ring plan.L2]
  simpa using cwPos_ne_of_ne_below_cleanup ring plan.L2
    (a := 0) (b := 1) ring.hn (by omega) (by omega)

/-! ## Cleanup trace certificate

The exact physical facts required after executing the literal word. -/

/-- A trace certificate records that the word killed exactly one of the two
leaders while preserving the other and framing all non-victim leader bits. -/
structure TwoLeaderCleanupTrace (hpsi : psi > 0)
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring)
    (C : Fin n → AgentState psi) : Prop where
  victim_before : (C plan.L2).leader = true
  survivor_after : (plan.output hpsi C plan.L1).leader = true
  victim_after : (plan.output hpsi C plan.L2).leader = false
  other_leaders_frame : ∀ i, i ≠ plan.L2 →
    (plan.output hpsi C i).leader = (C i).leader

/-- Every executable two-leader trace strictly lowers the raw physical leader
count. -/
theorem TwoLeaderCleanupTrace.rawPhysicalLeaderCount_lt
    {hpsi : psi > 0} {ring : DirectedRing n}
    {plan : TwoLeaderCleanupSchedule ring}
    {C : Fin n → AgentState psi}
    (h : TwoLeaderCleanupTrace hpsi ring plan C) :
    rawPhysicalLeaderCount (plan.output hpsi C) <
      rawPhysicalLeaderCount C :=
  rawPhysicalLeaderCount_lt_of_single_drop
    C (plan.output hpsi C) plan.L2
    h.victim_before h.victim_after h.other_leaders_frame

/-! ## Clean-slice entry predicate

Natural entry predicate for the multi-leader cleanup phase induction.
Explicitly rules out the forged dummy-bullet counterexample. -/

/-- Clean configuration from which the two-leader cleanup word is guaranteed
to produce a valid trace certificate.  All bullets and signals are zero,
both leaders are shielded at label zero, and both arcs have consecutive
follower labels.  This predicate is strictly stronger than "two physical
leaders" and cannot be omitted. -/
structure TwoLeaderCleanupReady (hpsi : psi > 0)
    (ring : DirectedRing n) (plan : TwoLeaderCleanupSchedule ring)
    (C : Fin n → AgentState psi) : Prop where
  leaders_exact : ∀ i,
    (C i).leader = true ↔ i = plan.L1 ∨ i = plan.L2
  l1_zero : (C plan.L1).label = ⟨0, hpsi⟩
  l2_zero : (C plan.L2).label = ⟨0, hpsi⟩
  l1_shielded : (C plan.L1).shield = true
  l2_shielded : (C plan.L2).shield = true
  bullets_zero : ∀ i, (C i).bullet = ⟨0, by omega⟩
  signals_zero : ∀ i, (C i).signal_B = ⟨0, by omega⟩
  arc12_followers : ∀ k, 0 < k → k < plan.d12 →
    (C (cwPos ring plan.L1 k)).leader = false
  arc21_followers : ∀ k, 0 < k → k < plan.d21 →
    (C (cwPos ring plan.L2 k)).leader = false
  arc12_aligned : ∀ k, k + 1 < plan.d12 →
    (C (cwPos ring plan.L1 (k + 1))).label =
      ⟨((C (cwPos ring plan.L1 k)).label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩
  arc21_aligned : ∀ k, k + 1 < plan.d21 →
    (C (cwPos ring plan.L2 (k + 1))).label =
      ⟨((C (cwPos ring plan.L2 k)).label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩

/-- The literal two-leader cleanup word implements the advertised trace from
the clean-slice predicate.  Final signal delivery uses the responder-leader
sink, while the first reverse bullet step uses label-zero leader egress. -/
theorem TwoLeaderCleanupReady.trace
    {hpsi : psi > 0} {ring : DirectedRing n}
    {plan : TwoLeaderCleanupSchedule ring}
    {C : Fin n → AgentState psi}
    (hready : TwoLeaderCleanupReady hpsi ring plan C) :
    TwoLeaderCleanupTrace hpsi ring plan C := by
  let T := eliminateLeadersNoCollisionEgressSink hpsi
  have hL1Leader : (C plan.L1).leader = true :=
    (hready.leaders_exact plan.L1).2 (Or.inl rfl)
  have hL2Leader : (C plan.L2).leader = true :=
    (hready.leaders_exact plan.L2).2 (Or.inr rfl)

  let C1 := applySchedule ring T C
    (clockwiseEdgeSchedule ring plan.L1 plan.d12)
  have hC1 : ForwardCleanupSignalState hpsi ring plan.L1 plan.d12
      C C1 plan.d12 := by
    simpa [C1, T] using
      forwardCleanupSignalSchedule hpsi ring plan.L1 plan.d12 plan.d12 C
        (Nat.le_refl _) plan.d12_lt
        (fun k _ => hready.bullets_zero _)
        (fun k _ => hready.signals_zero _)
        hL1Leader
        (by rw [cleanupPlan_target12 ring plan]; exact hL2Leader)
        hready.arc12_followers hready.arc12_aligned
  have hC1Bullets : ∀ i, (C1 i).bullet = ⟨0, by omega⟩ :=
    hC1.bullets_zero_of_initial hready.bullets_zero
  let p12 := cwPos ring plan.L1 (plan.d12 - 1)
  have hp12Signal : (C1 p12).signal_B = ⟨1, by omega⟩ := by
    have hdnon := plan.d12_nonadjacent
    exact hC1.visited_signal_one (plan.d12 - 1) (by omega) (by omega)
  have hp12Follower : (C1 p12).leader = false := by
    have hdnon := plan.d12_nonadjacent
    rw [hC1.leaders_frame]
    exact hready.arc12_followers (plan.d12 - 1) (by omega) (by omega)
  have hC1L2Signal : (C1 plan.L2).signal_B = ⟨1, by omega⟩ := by
    rw [← cleanupPlan_target12 ring plan]
    exact hC1.visited_signal_one plan.d12 plan.d12_pos (Nat.le_refl _)
  have hC1L2Leader : (C1 plan.L2).leader = true := by
    rw [hC1.leaders_frame]
    exact hL2Leader
  have hC1L2Label : (C1 plan.L2).label = ⟨0, hpsi⟩ := by
    rw [hC1.labels_frame]
    exact hready.l2_zero
  have hrepeat := cleanupRightFireOutput hpsi (C1 p12) (C1 plan.L2)
    hp12Follower hp12Signal hC1L2Leader hC1L2Label hC1L2Signal

  let C2 := stepConfig ring T C1 p12
  have hpred : ring.rightNeighbor p12 = plan.L2 :=
    cleanupPlan_predecessor12_right ring plan
  have hpne : p12 ≠ ring.rightNeighbor p12 := by
    rw [hpred]
    exact cleanupPlan_pred12_ne_L2 ring plan
  have hrepeat' : CleanupRightFireOutput
      (C1 p12) (C1 (ring.rightNeighbor p12))
      (T (C1 p12) (C1 (ring.rightNeighbor p12))) := by
    simpa [T, hpred] using hrepeat
  have hC2LeadersC1 : ∀ i, (C2 i).leader = (C1 i).leader :=
    stepConfig_view_frame_cleanup (view := fun u => u.leader)
      ring T C1 p12
        (hrepeat'.leaderL.trans hp12Follower.symm)
        (hrepeat'.leaderR.trans (by simpa [hpred] using hC1L2Leader.symm))
  have hC2LabelsC1 : ∀ i, (C2 i).label = (C1 i).label :=
    stepConfig_view_frame_cleanup (view := fun u => u.label)
      ring T C1 p12 hrepeat'.labelL hrepeat'.labelR
  have hC2LeadersC : ∀ i, (C2 i).leader = (C i).leader := fun i =>
    (hC2LeadersC1 i).trans (hC1.leaders_frame i)
  have hC2LabelsC : ∀ i, (C2 i).label = (C i).label := fun i =>
    (hC2LabelsC1 i).trans (hC1.labels_frame i)
  have hC2L2 : C2 plan.L2 = (T (C1 p12) (C1 plan.L2)).2 := by
    have h := stepConfig_right_cleanup ring T C1 p12 hpne
    simpa [C2, hpred] using h
  have hC2P12 : C2 p12 = (T (C1 p12) (C1 plan.L2)).1 := by
    simpa [C2, hpred] using stepConfig_left_cleanup ring T C1 p12
  have hC2L2Leader : (C2 plan.L2).leader = true := by
    rw [hC2L2]
    exact hrepeat.leaderR
  have hC2L2Shield : (C2 plan.L2).shield = false := by
    rw [hC2L2]
    exact hrepeat.shieldR
  have hC2L2Bullet : (C2 plan.L2).bullet = ⟨0, by omega⟩ := by
    rw [hC2L2]
    exact hrepeat.bulletR
  have hC2L2Signal : (C2 plan.L2).signal_B = ⟨0, by omega⟩ := by
    rw [hC2L2]
    exact hrepeat.signalR
  have hC2P12Bullet : (C2 p12).bullet = ⟨1, by omega⟩ := by
    rw [hC2P12]
    exact hrepeat.bulletL
  have hC2P12Signal : (C2 p12).signal_B = ⟨0, by omega⟩ := by
    rw [hC2P12]
    exact hrepeat.signalL
  have hL1neP : plan.L1 ≠ p12 := cleanupPlan_L1_ne_pred12 ring plan
  have hC2L1Eq : C2 plan.L1 = C1 plan.L1 := by
    apply stepConfig_untouched_cleanup ring T C1 p12 plan.L1 hL1neP
    simpa [hpred] using plan.leaders_ne
  have hC2L1Signal : (C2 plan.L1).signal_B = ⟨0, by omega⟩ := by
    rw [hC2L1Eq]
    exact hC1.source_signal_zero
  have hC2L1Shield : (C2 plan.L1).shield = true := by
    rw [hC2L1Eq, hC1.shields_frame]
    exact hready.l1_shielded
  have hC2Arc21Bullets : ∀ k, k ≤ plan.d21 →
      (C2 (cwPos ring plan.L2 k)).bullet = ⟨0, by omega⟩ := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa using hC2L2Bullet
    by_cases hkend : k = plan.d21
    · subst k
      rw [cleanupPlan_target21 ring plan, hC2L1Eq]
      exact hC1Bullets plan.L1
    have hkpos : 0 < k := by omega
    have hklt : k < plan.d21 := by omega
    let i := cwPos ring plan.L2 k
    have hu : C2 i = C1 i := by
      apply stepConfig_untouched_cleanup ring T C1 p12 i
        (cleanupPlan_arc21_interior_ne_pred12 ring plan k hkpos hklt)
      simpa [hpred] using
        cleanupPlan_arc21_interior_ne_L2 ring plan k hkpos hklt
    rw [hu]
    exact hC1Bullets i
  have hC2Arc21Signals : ∀ k, k ≤ plan.d21 →
      (C2 (cwPos ring plan.L2 k)).signal_B = ⟨0, by omega⟩ := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa using hC2L2Signal
    by_cases hkend : k = plan.d21
    · subst k
      rw [cleanupPlan_target21 ring plan]
      exact hC2L1Signal
    have hkpos : 0 < k := by omega
    have hklt : k < plan.d21 := by omega
    let i := cwPos ring plan.L2 k
    have hu : C2 i = C1 i := by
      apply stepConfig_untouched_cleanup ring T C1 p12 i
        (cleanupPlan_arc21_interior_ne_pred12 ring plan k hkpos hklt)
      simpa [hpred] using
        cleanupPlan_arc21_interior_ne_L2 ring plan k hkpos hklt
    rw [hu]
    change (C1 (cwPos ring plan.L2 k)).signal_B = ⟨0, by omega⟩
    rw [cleanupPlan_arc21_as_arc12 ring plan k]
    have hpart := plan.partition
    rw [hC1.outside_signal_frame (plan.d12 + k) (by omega) (by omega)]
    exact hready.signals_zero _

  let C3 := applySchedule ring T C2
    (clockwiseEdgeSchedule ring plan.L2 plan.d21)
  have hC3 : ForwardCleanupSignalState hpsi ring plan.L2 plan.d21
      C2 C3 plan.d21 := by
    simpa [C3, T] using
      forwardCleanupSignalSchedule hpsi ring plan.L2 plan.d21 plan.d21 C2
        (Nat.le_refl _) plan.d21_lt hC2Arc21Bullets hC2Arc21Signals
        hC2L2Leader
        (by rw [cleanupPlan_target21 ring plan, hC2LeadersC]; exact hL1Leader)
        (fun k hk0 hk => by rw [hC2LeadersC]; exact hready.arc21_followers k hk0 hk)
        (fun k hk => by rw [hC2LabelsC, hC2LabelsC]; exact hready.arc21_aligned k hk)
  have hC3LeadersC : ∀ i, (C3 i).leader = (C i).leader := fun i =>
    (hC3.leaders_frame i).trans (hC2LeadersC i)
  have hC3LabelsC : ∀ i, (C3 i).label = (C i).label := fun i =>
    (hC3.labels_frame i).trans (hC2LabelsC i)
  have hC3L1Signal : (C3 plan.L1).signal_B = ⟨1, by omega⟩ := by
    rw [← cleanupPlan_target21 ring plan]
    exact hC3.visited_signal_one plan.d21 plan.d21_pos (Nat.le_refl _)
  have hC3L1Leader : (C3 plan.L1).leader = true := by
    rw [hC3LeadersC]
    exact hL1Leader
  have hC3L2Signal : (C3 plan.L2).signal_B = ⟨0, by omega⟩ :=
    hC3.source_signal_zero
  have hC3L2Shield : (C3 plan.L2).shield = false := by
    rw [hC3.shields_frame]
    exact hC2L2Shield

  let r1 := ring.rightNeighbor plan.L1
  have hr1pos : r1 = cwPos ring plan.L1 1 :=
    rightNeighbor_eq_cwPos_one_cleanup ring plan.L1
  have hC3R1Follower : (C3 r1).leader = false := by
    have hdnon := plan.d12_nonadjacent
    rw [hC3LeadersC, hr1pos]
    exact hready.arc12_followers 1 (by omega) (by omega)
  have hr1Offset : cwPos ring plan.L2 (plan.d21 + 1) = r1 := by
    rw [show plan.d21 + 1 = plan.d21 + 1 by rfl,
      cwPos_succ, cleanupPlan_target21 ring plan]
  have hC3R1BulletEq : (C3 r1).bullet = (C2 r1).bullet := by
    rw [← hr1Offset]
    exact hC3.outside_bullet_frame (plan.d21 + 1) (by omega) (by
      have hpart := plan.partition
      have hd12 := plan.d12_nonadjacent
      omega)
  have hC2R1NotLive : (C2 r1).bullet ≠ ⟨2, by omega⟩ := by
    by_cases hrp : r1 = p12
    · intro hlive
      have heq : (C2 p12).bullet = ⟨2, by omega⟩ := by
        rw [← hrp]
        exact hlive
      rw [hC2P12Bullet] at heq
      simp at heq
    · have hrL2 : r1 ≠ plan.L2 :=
        (cleanupPlan_L2_ne_rightNeighbor_L1 ring plan).symm
      have hu : C2 r1 = C1 r1 := by
        apply stepConfig_untouched_cleanup ring T C1 p12 r1 hrp
        simpa [hpred] using hrL2
      intro hlive
      rw [hu, hC1Bullets] at hlive
      simp at hlive
  have hC3R1NotLive : (C3 r1).bullet ≠ ⟨2, by omega⟩ := by
    rw [hC3R1BulletEq]
    exact hC2R1NotLive
  have hfire := cleanupLeftFireOutput hpsi (C3 plan.L1) (C3 r1)
    hC3L1Leader hC3L1Signal hC3R1Follower hC3R1NotLive

  let C4 := stepConfig ring T C3 plan.L1
  have hL1neR1 : plan.L1 ≠ r1 :=
    cleanupPlan_self_ne_rightNeighbor_L1 ring plan
  have hfire' : CleanupLeftFireOutput
      (C3 plan.L1) (C3 (ring.rightNeighbor plan.L1))
      (T (C3 plan.L1) (C3 (ring.rightNeighbor plan.L1))) := by
    simpa [T, r1] using hfire
  have hC4LeadersC3 : ∀ i, (C4 i).leader = (C3 i).leader :=
    stepConfig_view_frame_cleanup (view := fun u => u.leader)
      ring T C3 plan.L1
        (hfire'.leaderL.trans hC3L1Leader.symm)
        (hfire'.leaderR.trans (by simpa [r1] using hC3R1Follower.symm))
  have hC4LabelsC3 : ∀ i, (C4 i).label = (C3 i).label :=
    stepConfig_view_frame_cleanup (view := fun u => u.label)
      ring T C3 plan.L1 hfire'.labelL hfire'.labelR
  have hC4LeadersC : ∀ i, (C4 i).leader = (C i).leader := fun i =>
    (hC4LeadersC3 i).trans (hC3LeadersC i)
  have hC4LabelsC : ∀ i, (C4 i).label = (C i).label := fun i =>
    (hC4LabelsC3 i).trans (hC3LabelsC i)
  have hC4L1 : C4 plan.L1 = (T (C3 plan.L1) (C3 r1)).1 := by
    simpa [C4, r1] using stepConfig_left_cleanup ring T C3 plan.L1
  have hC4L1Bullet : (C4 plan.L1).bullet = ⟨2, by omega⟩ := by
    rw [hC4L1]
    exact hfire.bulletL
  have hC4L1Signal : (C4 plan.L1).signal_B = ⟨0, by omega⟩ := by
    rw [hC4L1]
    exact hfire.signalL
  have hC4L2Eq : C4 plan.L2 = C3 plan.L2 := by
    apply stepConfig_untouched_cleanup ring T C3 plan.L1 plan.L2
      plan.leaders_ne.symm
    exact cleanupPlan_L2_ne_rightNeighbor_L1 ring plan
  have hC4L2Leader : (C4 plan.L2).leader = true := by
    rw [hC4L2Eq, hC3LeadersC]
    exact hL2Leader
  have hC4L2Shield : (C4 plan.L2).shield = false := by
    rw [hC4L2Eq]
    exact hC3L2Shield
  have hC4L2Signal : (C4 plan.L2).signal_B = ⟨0, by omega⟩ := by
    rw [hC4L2Eq]
    exact hC3L2Signal

  let C5 := applySchedule ring T C4
    (reversePositiveEdgeSchedule ring plan.L2 (plan.d21 - 1))
  have hreverse : ReverseCleanupLiveOutput ring plan.L2 C4 C5 := by
    have hdpos := plan.d21_pos
    have hdlt := plan.d21_lt
    apply reversePositiveEdgeSchedule_moves_live_cleanup hpsi ring plan.L2
      (plan.d21 - 1) C4
    · omega
    · rw [show plan.d21 - 1 + 1 = plan.d21 by omega,
        cleanupPlan_target21 ring plan]
      exact hC4L1Bullet
    · rw [show plan.d21 - 1 + 1 = plan.d21 by omega,
        cleanupPlan_target21 ring plan]
      exact hC4L1Signal
    · intro k hk0 hkle
      rw [hC4LeadersC]
      exact hready.arc21_followers k hk0 (by omega)
    · intro k hk0 hkle
      by_cases htop : k = plan.d21 - 1
      · right
        have hk1 : k + 1 = plan.d21 := by omega
        rw [hk1, cleanupPlan_target21 ring plan, hC4LeadersC, hC4LabelsC]
        exact ⟨hL1Leader, hready.l1_zero⟩
      · left
        rw [hC4LabelsC, hC4LabelsC]
        exact hready.arc21_aligned k (by omega)

  let r2 := ring.rightNeighbor plan.L2
  have hr2pos : r2 = cwPos ring plan.L2 1 :=
    rightNeighbor_eq_cwPos_one_cleanup ring plan.L2
  have hC5R2Bullet : (C5 r2).bullet = ⟨2, by omega⟩ := by
    rw [hr2pos]
    exact hreverse.live_at_one
  have hC5R2Follower : (C5 r2).leader = false := by
    have hdnon := plan.d21_nonadjacent
    rw [hreverse.leaders_frame, hC4LeadersC, hr2pos]
    exact hready.arc21_followers 1 (by omega) (by omega)
  have hC5L2Eq : C5 plan.L2 = C4 plan.L2 := hreverse.start_unchanged
  have hC5L2Leader : (C5 plan.L2).leader = true := by
    rw [hC5L2Eq]
    exact hC4L2Leader
  have hC5L2Shield : (C5 plan.L2).shield = false := by
    rw [hC5L2Eq]
    exact hC4L2Shield
  have hC5L2Signal : (C5 plan.L2).signal_B = ⟨0, by omega⟩ := by
    rw [hC5L2Eq]
    exact hC4L2Signal
  have hhit := cleanupLiveKillOutput hpsi (C5 plan.L2) (C5 r2)
    hC5L2Leader hC5L2Shield hC5L2Signal hC5R2Follower hC5R2Bullet

  let C6 := stepConfig ring T C5 plan.L2
  have hL2neR2 : plan.L2 ≠ r2 :=
    cleanupPlan_self_ne_rightNeighbor_L2 ring plan
  have hC6L2 : C6 plan.L2 = (T (C5 plan.L2) (C5 r2)).1 := by
    simpa [C6, r2] using stepConfig_left_cleanup ring T C5 plan.L2
  have hC6R2 : C6 r2 = (T (C5 plan.L2) (C5 r2)).2 := by
    have h := stepConfig_right_cleanup ring T C5 plan.L2 hL2neR2
    simpa [C6, r2] using h
  have hC6Victim : (C6 plan.L2).leader = false := by
    rw [hC6L2]
    exact hhit.leaderL
  have hC5LeadersC : ∀ i, (C5 i).leader = (C i).leader := fun i =>
    (hreverse.leaders_frame i).trans (hC4LeadersC i)
  have hC6L1 : C6 plan.L1 = C5 plan.L1 := by
    apply stepConfig_untouched_cleanup ring T C5 plan.L2 plan.L1
      plan.leaders_ne
    exact cleanupPlan_L1_ne_rightNeighbor_L2 ring plan
  have hC6Survivor : (C6 plan.L1).leader = true := by
    rw [hC6L1, hC5LeadersC]
    exact hL1Leader
  have houtput : plan.output hpsi C = C6 := by
    have hsched : plan.word =
        clockwiseEdgeSchedule ring plan.L1 plan.d12 ++
          ([cwPos ring plan.L1 (plan.d12 - 1)] ++
            (clockwiseEdgeSchedule ring plan.L2 plan.d21 ++
              ([plan.L1] ++
                (reversePositiveEdgeSchedule ring plan.L2 (plan.d21 - 1) ++
                  [plan.L2])))) := by
      simp [TwoLeaderCleanupSchedule.word, List.append_assoc]
    rw [TwoLeaderCleanupSchedule.output, hsched]
    simp only [applySchedule_append_cleanup, applySchedule]
    rfl
  refine
    { victim_before := hL2Leader
      survivor_after := by rw [houtput]; exact hC6Survivor
      victim_after := by rw [houtput]; exact hC6Victim
      other_leaders_frame := ?_ }
  intro i hi
  rw [houtput]
  by_cases hir : i = r2
  · subst i
    calc
      (C6 r2).leader = (T (C5 plan.L2) (C5 r2)).2.leader :=
        congrArg (fun u => u.leader) hC6R2
      _ = false := hhit.leaderR
      _ = (C r2).leader := by
        have hdnon := plan.d21_nonadjacent
        rw [hr2pos]
        exact (hready.arc21_followers 1 (by omega) (by omega)).symm
  · have hu : C6 i = C5 i := by
      apply stepConfig_untouched_cleanup ring T C5 plan.L2 i hi
      simpa [r2] using hir
    rw [hu]
    exact hC5LeadersC i

/-- Every clean two-leader slice supplies a literal strict-count cleanup
round, rather than merely the finite regression instance. -/
theorem TwoLeaderCleanupReady.rawPhysicalLeaderCount_lt
    {hpsi : psi > 0} {ring : DirectedRing n}
    {plan : TwoLeaderCleanupSchedule ring}
    {C : Fin n → AgentState psi}
    (hready : TwoLeaderCleanupReady hpsi ring plan C) :
    rawPhysicalLeaderCount (plan.output hpsi C) <
      rawPhysicalLeaderCount C :=
  hready.trace.rawPhysicalLeaderCount_lt

/-- The arbitrary cleanup endpoint has exactly the surviving first leader. -/
theorem TwoLeaderCleanupReady.uniqueLeader
    {hpsi : psi > 0} {ring : DirectedRing n}
    {plan : TwoLeaderCleanupSchedule ring}
    {C : Fin n → AgentState psi}
    (hready : TwoLeaderCleanupReady hpsi ring plan C) :
    hasUniqueLeader n (plan.output hpsi C) := by
  have htrace := hready.trace
  refine ⟨plan.L1, by
    simpa [AgentState.isLeader] using htrace.survivor_after, ?_⟩
  intro i hi
  change (plan.output hpsi C i).leader = true at hi
  by_cases hivictim : i = plan.L2
  · subst i
    rw [htrace.victim_after] at hi
    simp at hi
  · have hiBefore : (C i).leader = true := by
      rw [← htrace.other_leaders_frame i hivictim]
      exact hi
    rcases (hready.leaders_exact i).1 hiBefore with hiL1 | hiL2
    · exact hiL1
    · exact (hivictim hiL2).elim

/-! ## Regression: ordinary SIGNAL cannot implement the cleanup word

The two arc predicates constrain only interior follower edges.  With width
three and two leaders two steps apart, both interior edges are aligned but
neither absence signal can cross the final `1 → 0` leader edge under the
ordinary signal kernel.  This exact regression is why the executable repair
above uses the responder-leader signal sink. -/

private def eliminateLeadersNoCollisionEgressSinkOrdinary
    (hpsi : psi > 0) (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let nextLabel : Fin psi :=
    ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  let q0 := eliminateLeadersNoCollisionFire hpsi l r
  let q1 := eliminateLeadersNoCollisionZeroLeaderEgressMove
    hpsi nextLabel q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignal nextLabel q1.1 q1.2
  dummyBulletSink q2

private theorem unalignedTwoLeaderRing : DirectedRing 4 := ⟨by omega⟩

private def unalignedTwoLeaderPlan :
    TwoLeaderCleanupSchedule unalignedTwoLeaderRing where
  L1 := ⟨0, by omega⟩
  L2 := ⟨2, by omega⟩
  leaders_ne := by decide
  d12 := 2
  d21 := 2
  d12_eq := by decide
  d21_eq := by decide
  d12_pos := by omega
  d21_pos := by omega
  d12_lt := by omega
  d21_lt := by omega
  d12_nonadjacent := by omega
  d21_nonadjacent := by omega
  partition := by omega

private def unalignedTwoLeaderView (i : Fin 4) : PeaceView 3 :=
  { leader := decide (i.val = 0 ∨ i.val = 2)
    label := if i.val % 2 = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩
    shield := decide (i.val = 0 ∨ i.val = 2)
    bullet := ⟨0, by omega⟩
    signal_B := ⟨0, by omega⟩ }

private def unalignedTwoLeaderConfig (i : Fin 4) : AgentState 3 :=
  PeaceView.toState (unalignedTwoLeaderView i)

private def unalignedTwoLeaderOrdinaryOutput : Fin 4 → AgentState 3 :=
  applySchedule unalignedTwoLeaderRing
    (eliminateLeadersNoCollisionEgressSinkOrdinary (by omega))
    unalignedTwoLeaderConfig unalignedTwoLeaderPlan.word

private theorem unalignedTwoLeaderReady :
    TwoLeaderCleanupReady (by omega : 0 < 3) unalignedTwoLeaderRing
      unalignedTwoLeaderPlan unalignedTwoLeaderConfig := by
  refine
    { leaders_exact := by decide
      l1_zero := by decide
      l2_zero := by decide
      l1_shielded := by decide
      l2_shielded := by decide
      bullets_zero := by decide
      signals_zero := by decide
      arc12_followers := ?_
      arc21_followers := ?_
      arc12_aligned := ?_
      arc21_aligned := ?_ }
  · intro k hk hlt
    change k < 2 at hlt
    have : k = 1 := by omega
    subst k
    decide
  · intro k hk hlt
    change k < 2 at hlt
    have : k = 1 := by omega
    subst k
    decide
  · intro k hlt
    change k + 1 < 2 at hlt
    have : k = 0 := by omega
    subst k
    decide
  · intro k hlt
    change k + 1 < 2 at hlt
    have : k = 0 := by omega
    subst k
    decide

/-- The word leaves the intended victim alive under ordinary
SIGNAL when the closing leader edge is nonconsecutive. -/
theorem twoLeaderCleanupReady_ordinary_signal_victim_survives :
    TwoLeaderCleanupReady (by omega : 0 < 3) unalignedTwoLeaderRing
        unalignedTwoLeaderPlan unalignedTwoLeaderConfig ∧
      (unalignedTwoLeaderOrdinaryOutput
        unalignedTwoLeaderPlan.L2).leader = true := by
  exact ⟨unalignedTwoLeaderReady, by decide⟩

/-- Replacing ordinary SIGNAL by the responder-leader sink repairs the exact
width-three regression: the same literal word preserves `L1`, removes `L2`,
and frames every other leader bit. -/
theorem twoLeaderCleanup_leaderSink_repairs_unaligned_regression :
    TwoLeaderCleanupTrace (by omega : 0 < 3) unalignedTwoLeaderRing
      unalignedTwoLeaderPlan unalignedTwoLeaderConfig := by
  constructor <;> decide

/-- The repaired finite trace is a genuine strict leader-count round. -/
theorem twoLeaderCleanup_leaderSink_regression_count_lt :
    rawPhysicalLeaderCount
        (unalignedTwoLeaderPlan.output (by omega)
          unalignedTwoLeaderConfig) <
      rawPhysicalLeaderCount unalignedTwoLeaderConfig :=
  twoLeaderCleanup_leaderSink_repairs_unaligned_regression
    |>.rawPhysicalLeaderCount_lt

/-- The repaired regression endpoint satisfies the repository's semantic
unique-leader predicate, not merely a strict-count inequality. -/
theorem twoLeaderCleanup_leaderSink_regression_uniqueLeader :
    hasUniqueLeader 4
      (unalignedTwoLeaderPlan.output (by omega)
        unalignedTwoLeaderConfig) :=
  hasUniqueLeader_of_rawPhysicalLeaderCount_eq_one _ (by decide)

/-! ### Full finite-wrapper regression

The canonical PeaceView representative is also a concrete input to the full
authorized, bounded, and expiring transition.  This executable test guards the
bridge against a raw-kernel-only success that is destroyed by another stage of
the complete interaction. -/

private theorem unalignedTwoLeaderConfig_inProtocolDomain (i : Fin 4) :
    (unalignedTwoLeaderConfig i).inProtocolDomain 0 := by
  simp [unalignedTwoLeaderConfig, unalignedTwoLeaderView,
    PeaceView.toState, AgentState.inProtocolDomain]

private def unalignedTwoLeaderExpiringConfig : EConfig 4 3 0 16 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain (unalignedTwoLeaderConfig i)
      (unalignedTwoLeaderConfig_inProtocolDomain i), false⟩,
    freshStall 16⟩

private def unalignedTwoLeaderExpiringOutput : EConfig 4 3 0 16 :=
  runLocalSchedule unalignedTwoLeaderRing
    (multiLeaderCleanupTransition (by omega) 0 16)
    unalignedTwoLeaderExpiringConfig unalignedTwoLeaderPlan.word

set_option maxRecDepth 16384 in
set_option maxHeartbeats 12000000 in
/-- The complete finite word strictly lowers the physical leader count, not
merely the raw-kernel count used by the symbolic trace. -/
theorem twoLeaderCleanup_full_expiring_regression_count_lt :
    rawPhysicalLeaderCount
        (eraseExpiringConfig unalignedTwoLeaderExpiringOutput) <
      rawPhysicalLeaderCount
        (eraseExpiringConfig unalignedTwoLeaderExpiringConfig) := by
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 12000000 in
/-- The complete finite transition realizes the repaired strict cleanup on the
same nonconsecutive closing-edge fixture as the raw symbolic theorem. -/
theorem twoLeaderCleanup_full_expiring_regression_uniqueLeader :
    hasUniqueLeader 4
      (eraseExpiringConfig unalignedTwoLeaderExpiringOutput) := by
  apply hasUniqueLeader_of_rawPhysicalLeaderCount_eq_one
  decide

/-! ## Well-founded multi-leader iteration

The executable two-leader word above is a candidate local component of a
future producer for the following contract; no raw-to-expiring bridge is
claimed here.  The contract deliberately exposes the remaining local
research obligation: from every invariant state with more than one physical
leader, produce a literal schedule that preserves the invariant and
positivity while strictly decreasing the physical leader count.  Once that
producer exists, termination at count one is a generic strong-induction
argument rather than an additional protocol assumption. -/

/-- Physical leader count on the finite expiring carrier. -/
def expiringPhysicalLeaderCount
    (C : EConfig n psi kappa tau) : Nat :=
  rawPhysicalLeaderCount (eraseExpiringConfig C)

/-- Count one on the expiring carrier gives a unique leader on its exact raw
physical erasure; no transition-erasure commutation is asserted. -/
theorem hasUniqueLeader_of_expiringPhysicalLeaderCount_eq_one
    (C : EConfig n psi kappa tau)
    (hcount : expiringPhysicalLeaderCount C = 1) :
    hasUniqueLeader n (eraseExpiringConfig C) :=
  hasUniqueLeader_of_rawPhysicalLeaderCount_eq_one
    (eraseExpiringConfig C) hcount

/-- One executable cleanup round.  This is the exact remaining producer
interface for the global multi-leader theorem. -/
structure MultiLeaderCleanupRoundContract
    (ring : DirectedRing n)
    (T : ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau)
    (Inv : EConfig n psi kappa tau → Prop) : Prop where
  produce : ∀ C, Inv C → 1 < expiringPhysicalLeaderCount C →
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring T C word ∧
      Inv D ∧
      0 < expiringPhysicalLeaderCount D ∧
      expiringPhysicalLeaderCount D < expiringPhysicalLeaderCount C

private theorem runLocalSchedule_append_cleanup
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (C : Fin n → Q) (s t : DetSchedule n) :
    runLocalSchedule ring T C (s ++ t) =
      runLocalSchedule ring T (runLocalSchedule ring T C s) t := by
  induction s generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runLocalSchedule]
      exact ih _

/-- Strong induction on the physical leader count iterates any concrete
strict cleanup-round producer to a literal schedule ending at count one. -/
theorem exists_multiLeaderCleanupSchedule_to_count_one_of_count
    (ring : DirectedRing n)
    (T : ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau)
    (Inv : EConfig n psi kappa tau → Prop)
    (K : MultiLeaderCleanupRoundContract ring T Inv)
    (rank : Nat) (C : EConfig n psi kappa tau)
    (hrank : expiringPhysicalLeaderCount C = rank)
    (hInv : Inv C) (hpos : 0 < expiringPhysicalLeaderCount C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring T C word ∧
      Inv D ∧
      expiringPhysicalLeaderCount D = 1 := by
  revert C
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      intro C hrank hInv hpos
      by_cases hone : expiringPhysicalLeaderCount C = 1
      · exact ⟨[], C, rfl, hInv, hone⟩
      · have hmore : 1 < expiringPhysicalLeaderCount C := by omega
        obtain ⟨pref, M, hM, hInvM, hposM, hltM⟩ :=
          K.produce C hInv hmore
        have hltRank : expiringPhysicalLeaderCount M < rank := by
          rw [← hrank]
          exact hltM
        obtain ⟨tail, D, hD, hInvD, honeD⟩ :=
          ih (expiringPhysicalLeaderCount M) hltRank
            M rfl hInvM hposM
        refine ⟨pref ++ tail, D, ?_, hInvD, honeD⟩
        calc
          D = runLocalSchedule ring T M tail := hD
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) tail := by rw [← hM]
          _ = runLocalSchedule ring T C (pref ++ tail) :=
            (runLocalSchedule_append_cleanup ring T C pref tail).symm

/-- Count-free wrapper around the strong-induction theorem. -/
theorem exists_multiLeaderCleanupSchedule_to_count_one
    (ring : DirectedRing n)
    (T : ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau)
    (Inv : EConfig n psi kappa tau → Prop)
    (K : MultiLeaderCleanupRoundContract ring T Inv)
    (C : EConfig n psi kappa tau)
    (hInv : Inv C) (hpos : 0 < expiringPhysicalLeaderCount C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring T C word ∧
      Inv D ∧
      expiringPhysicalLeaderCount D = 1 :=
  exists_multiLeaderCleanupSchedule_to_count_one_of_count
    ring T Inv K (expiringPhysicalLeaderCount C) C rfl hInv hpos

/-- Semantic corollary: the count-one endpoint has exactly one physical
leader after erasing the finite authorization and expiry metadata. -/
theorem exists_multiLeaderCleanupSchedule_to_uniqueLeader
    (ring : DirectedRing n)
    (T : ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau)
    (Inv : EConfig n psi kappa tau → Prop)
    (K : MultiLeaderCleanupRoundContract ring T Inv)
    (C : EConfig n psi kappa tau)
    (hInv : Inv C) (hpos : 0 < expiringPhysicalLeaderCount C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring T C word ∧
      hasUniqueLeader n (eraseExpiringConfig D) ∧
      Inv D := by
  obtain ⟨word, D, hD, hInvD, hcountD⟩ :=
    exists_multiLeaderCleanupSchedule_to_count_one
      ring T Inv K C hInv hpos
  exact ⟨word, D, hD,
    hasUniqueLeader_of_expiringPhysicalLeaderCount_eq_one D hcountD,
    hInvD⟩

/-! ## Quantitative extension

A per-round length bound composes through the same strong
induction.  The recursive budget is indexed by the current physical leader
count and does not assume that a round removes exactly one leader. -/

/-- Cumulative schedule budget for strict positive descent from `rank` to one. -/
def multiLeaderCleanupBudget (roundBound : Nat → Nat) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | k + 2 =>
      multiLeaderCleanupBudget roundBound (k + 1) + roundBound (k + 2)

@[simp] theorem multiLeaderCleanupBudget_zero (roundBound : Nat → Nat) :
    multiLeaderCleanupBudget roundBound 0 = 0 := rfl

@[simp] theorem multiLeaderCleanupBudget_one (roundBound : Nat → Nat) :
    multiLeaderCleanupBudget roundBound 1 = 0 := rfl

@[simp] theorem multiLeaderCleanupBudget_succ_succ
    (roundBound : Nat → Nat) (k : Nat) :
    multiLeaderCleanupBudget roundBound (k + 2) =
      multiLeaderCleanupBudget roundBound (k + 1) +
        roundBound (k + 2) := rfl

theorem multiLeaderCleanupBudget_le_succ
    (roundBound : Nat → Nat) (k : Nat) :
    multiLeaderCleanupBudget roundBound k ≤
      multiLeaderCleanupBudget roundBound (k + 1) := by
  cases k with
  | zero => exact Nat.le_refl 0
  | succ k =>
      rw [show k + 1 + 1 = k + 2 by omega,
        multiLeaderCleanupBudget_succ_succ]
      omega

theorem multiLeaderCleanupBudget_mono
    (roundBound : Nat → Nat) {a b : Nat} (hab : a ≤ b) :
    multiLeaderCleanupBudget roundBound a ≤
      multiLeaderCleanupBudget roundBound b := by
  induction b generalizing a with
  | zero =>
      have : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases ha : a = b + 1
      · subst a
        exact Nat.le_refl _
      · exact Nat.le_trans (ih (by omega))
          (multiLeaderCleanupBudget_le_succ roundBound b)

theorem multiLeaderCleanupBudget_round_step
    (roundBound : Nat → Nat) (rank next : Nat)
    (hnextPos : 0 < next) (hnextLt : next < rank) :
    roundBound rank + multiLeaderCleanupBudget roundBound next ≤
      multiLeaderCleanupBudget roundBound rank := by
  cases rank with
  | zero => omega
  | succ rank =>
      cases rank with
      | zero => omega
      | succ k =>
          rw [show k + 1 + 1 = k + 2 by omega,
            multiLeaderCleanupBudget_succ_succ]
          have hmono : multiLeaderCleanupBudget roundBound next ≤
              multiLeaderCleanupBudget roundBound (k + 1) :=
            multiLeaderCleanupBudget_mono roundBound (by omega)
          omega

/-- Cleanup-round producer carrying an explicit length bound for the witness
word selected at the current leader count. -/
structure MultiLeaderCleanupBoundedRoundContract
    (ring : DirectedRing n)
    (T : ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau)
    (Inv : EConfig n psi kappa tau → Prop)
    (roundBound : Nat → Nat) : Prop where
  produce : ∀ C, Inv C → 1 < expiringPhysicalLeaderCount C →
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring T C word ∧
      Inv D ∧
      0 < expiringPhysicalLeaderCount D ∧
      expiringPhysicalLeaderCount D < expiringPhysicalLeaderCount C ∧
      word.length ≤ roundBound (expiringPhysicalLeaderCount C)

private theorem exists_multiLeaderCleanupSchedule_to_count_one_with_budget_of_count
    (ring : DirectedRing n)
    (T : ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau)
    (Inv : EConfig n psi kappa tau → Prop)
    (roundBound : Nat → Nat)
    (K : MultiLeaderCleanupBoundedRoundContract ring T Inv roundBound)
    (rank : Nat) (C : EConfig n psi kappa tau)
    (hrank : expiringPhysicalLeaderCount C = rank)
    (hInv : Inv C) (hpos : 0 < expiringPhysicalLeaderCount C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring T C word ∧
      Inv D ∧
      expiringPhysicalLeaderCount D = 1 ∧
      word.length ≤ multiLeaderCleanupBudget roundBound rank := by
  revert C
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      intro C hrank hInv hpos
      by_cases hone : expiringPhysicalLeaderCount C = 1
      · refine ⟨[], C, rfl, hInv, hone, ?_⟩
        simp
      · have hmore : 1 < expiringPhysicalLeaderCount C := by omega
        obtain ⟨pref, M, hM, hInvM, hposM, hltM, hlenM⟩ :=
          K.produce C hInv hmore
        have hltRank : expiringPhysicalLeaderCount M < rank := by
          rw [← hrank]
          exact hltM
        obtain ⟨tail, D, hD, hInvD, honeD, hlenD⟩ :=
          ih (expiringPhysicalLeaderCount M) hltRank
            M rfl hInvM hposM
        refine ⟨pref ++ tail, D, ?_, hInvD, honeD, ?_⟩
        · calc
            D = runLocalSchedule ring T M tail := hD
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T C pref) tail := by rw [← hM]
            _ = runLocalSchedule ring T C (pref ++ tail) :=
              (runLocalSchedule_append_cleanup ring T C pref tail).symm
        · simp only [List.length_append]
          have hpref : pref.length ≤ roundBound rank := by
            simpa [hrank] using hlenM
          calc
            pref.length + tail.length ≤
                roundBound rank +
                  multiLeaderCleanupBudget roundBound
                    (expiringPhysicalLeaderCount M) :=
              Nat.add_le_add hpref hlenD
            _ ≤ multiLeaderCleanupBudget roundBound rank :=
              multiLeaderCleanupBudget_round_step roundBound rank
                (expiringPhysicalLeaderCount M) hposM hltRank

/-- Bounded wrapper for the strong-induction schedule. -/
theorem exists_multiLeaderCleanupSchedule_to_count_one_with_budget
    (ring : DirectedRing n)
    (T : ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau)
    (Inv : EConfig n psi kappa tau → Prop)
    (roundBound : Nat → Nat)
    (K : MultiLeaderCleanupBoundedRoundContract ring T Inv roundBound)
    (C : EConfig n psi kappa tau)
    (hInv : Inv C) (hpos : 0 < expiringPhysicalLeaderCount C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring T C word ∧
      Inv D ∧
      expiringPhysicalLeaderCount D = 1 ∧
      word.length ≤ multiLeaderCleanupBudget roundBound
        (expiringPhysicalLeaderCount C) :=
  exists_multiLeaderCleanupSchedule_to_count_one_with_budget_of_count
    ring T Inv roundBound K (expiringPhysicalLeaderCount C)
      C rfl hInv hpos

/-- Bounded semantic corollary at the unique-leader endpoint. -/
theorem exists_multiLeaderCleanupSchedule_to_uniqueLeader_with_budget
    (ring : DirectedRing n)
    (T : ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau)
    (Inv : EConfig n psi kappa tau → Prop)
    (roundBound : Nat → Nat)
    (K : MultiLeaderCleanupBoundedRoundContract ring T Inv roundBound)
    (C : EConfig n psi kappa tau)
    (hInv : Inv C) (hpos : 0 < expiringPhysicalLeaderCount C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring T C word ∧
      hasUniqueLeader n (eraseExpiringConfig D) ∧
      Inv D ∧
      word.length ≤ multiLeaderCleanupBudget roundBound
        (expiringPhysicalLeaderCount C) := by
  obtain ⟨word, D, hD, hInvD, honeD, hlenD⟩ :=
    exists_multiLeaderCleanupSchedule_to_count_one_with_budget
      ring T Inv roundBound K C hInv hpos
  exact ⟨word, D, hD,
    hasUniqueLeader_of_expiringPhysicalLeaderCount_eq_one D honeD,
    hInvD, hlenD⟩

/-! ## Top-level interface (pending concrete round producer)

The global induction layer is now executable once a concrete
`MultiLeaderCleanupRoundContract` is supplied.  What remains is the protocol
proof that every invariant state with count greater than one admits such a
round; the intended stronger top-level signature is recorded below.

```
-- Prerequisites (not yet implemented):
-- structure MultiLeaderCleanupEntry (hpsi : psi > 0)
--     (ring : DirectedRing n) (C : EConfig n psi kappa tau)
--     (root : Fin n) : Prop
--
-- def MultiLeaderCleanupInv
--     (hpsi : psi > 0) (ring : DirectedRing n)
--     (C : EConfig n psi kappa tau) : Prop
--
-- theorem exists_multiLeaderCleanup_to_uniqueLeader
--     (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
--     (C : EConfig n psi kappa tau) (root : Fin n)
--     (K : MultiLeaderCleanupRoundContract ring
--       (multiLeaderCleanupTransition hpsi kappa tau)
--       (MultiLeaderCleanupInv hpsi ring))
--     (hentry : MultiLeaderCleanupEntry hpsi ring C root) :
--     exists word D leader,
--       D = runLocalSchedule ring
--         (multiLeaderCleanupTransition hpsi kappa tau) C word ∧
--       hasUniqueLeader n (eraseExpiringConfig D) ∧
--       BulletTwoFreeAwayFrom D leader
```

The narrow terminal compatibility theorem that bridges the cleanup and retry
transitions is also pending:

```
-- theorem multiLeaderCleanup_twoStep_eq_retry
--     (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
--     (C : EConfig n psi kappa tau) (root : Fin n)
--     (hseed : ...) :
--     runLocalSchedule ring
--         (multiLeaderCleanupTransition hpsi kappa tau)
--         C [root, root] =
--       runLocalSchedule ring
--         (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
--           hpsi kappa tau)
--         C [root, root]
```
-/

end PPLLCompleteMultiLeaderCleanup
