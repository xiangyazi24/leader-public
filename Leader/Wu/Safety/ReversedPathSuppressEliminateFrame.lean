import Leader.Wu.Safety.Counterexamples
import Leader.Wu.Scheduler.BoundedToRepairedLift


set_option autoImplicit false
set_option Elab.async false


namespace ZZSafeN4ReversedEliminateGPT


open PPLL PPLLRepair


theorem hpsi2 : 0 < 2 := by
  decide


/-- Exact protocol family requested by the downstream proof. -/
abbrev Raw : PopulationProtocol :=
  PPLLRepair.protocol hpsi2 10


/-- The two consecutive substages isolated in this leaf. -/
def suppressThenEliminate
    (l r : AgentState 2) : AgentState 2 × AgentState 2 :=
  let q := PPLL.suppressSig hpsi2 l r
  PPLLRepair.eliminateLeadersNoCollision hpsi2 q.1 q.2


/-- Exactly the fields Task 5 asks us to protect. -/
structure ProtectedView where
  leader : Bool
  bullet : Fin 3
  shield : Bool
  signal_B : Fin 2
  label : Fin 2
  probe : Bool
  phase : Bool
  state : MainState
  path : PathInfo
  path2 : Option Path2Info
  p : Bool
  p_carry : Bool
  path4 : Option (Int × Nat)
  path5 : Option (Int × Nat)


namespace ProtectedView


abbrev ofState (u : AgentState 2) : ProtectedView :=
  ⟨u.leader, u.bullet, u.shield, u.signal_B,
    u.label, u.probe, u.phase, u.state, u.path, u.path2,
    u.p, u.p_carry, u.path4, u.path5⟩

theorem ext (a b : ProtectedView)
    (hleader : a.leader = b.leader)
    (hbullet : a.bullet = b.bullet)
    (hshield : a.shield = b.shield)
    (hsignal_B : a.signal_B = b.signal_B)
    (hlabel : a.label = b.label)
    (hprobe : a.probe = b.probe)
    (hphase : a.phase = b.phase)
    (hstate : a.state = b.state)
    (hpath : a.path = b.path)
    (hpath2 : a.path2 = b.path2)
    (hp : a.p = b.p)
    (hp_carry : a.p_carry = b.p_carry)
    (hpath4 : a.path4 = b.path4)
    (hpath5 : a.path5 = b.path5) : a = b := by
  cases a
  cases b
  simp_all


end ProtectedView


abbrev protectedPairOf
    (l r : AgentState 2) : ProtectedView × ProtectedView :=
  (ProtectedView.ofState l, ProtectedView.ofState r)


/-- Requested non-Algorithm-15 physical frames. -/
structure PassiveFrame
    (l r l' r' : AgentState 2) : Prop where
  leftLabel : l'.label = l.label
  rightLabel : r'.label = r.label
  leftProbe : l'.probe = l.probe
  rightProbe : r'.probe = r.probe
  leftPhase : l'.phase = l.phase
  rightPhase : r'.phase = r.phase
  leftState : l'.state = l.state
  rightState : r'.state = r.state
  leftPath : l'.path = l.path
  rightPath : r'.path = r.path
  leftPath2 : l'.path2 = l.path2
  rightPath2 : r'.path2 = r.path2
  leftP : l'.p = l.p
  rightP : r'.p = r.p
  leftPCarry : l'.p_carry = l.p_carry
  rightPCarry : r'.p_carry = r.p_carry
  leftPath4 : l'.path4 = l.path4
  rightPath4 : r'.path4 = r.path4
  leftPath5 : l'.path5 = l.path5
  rightPath5 : r'.path5 = r.path5


/-- All Task-5 protected fields, with the four Algorithm-15 physical
coordinates separated from the passive frame. -/
structure ProtectedFrame
    (l r l' r' : AgentState 2) : Prop where
  leftLeader : l'.leader = l.leader
  rightLeader : r'.leader = r.leader
  leftBullet : l'.bullet = l.bullet
  rightBullet : r'.bullet = r.bullet
  leftShield : l'.shield = l.shield
  rightShield : r'.shield = r.shield
  leftSignal : l'.signal_B = l.signal_B
  rightSignal : r'.signal_B = r.signal_B
  passive : PassiveFrame l r l' r'


private theorem protectedFrame_of_view_eq
    {l r l' r' : AgentState 2}
    (h :
      protectedPairOf l' r' =
        protectedPairOf l r) :
    ProtectedFrame l r l' r' := by
  have hl :
      ProtectedView.ofState l' =
        ProtectedView.ofState l :=
    congrArg Prod.fst h
  have hr :
      ProtectedView.ofState r' =
        ProtectedView.ofState r :=
    congrArg Prod.snd h
  exact {
    leftLeader := congrArg ProtectedView.leader hl
    rightLeader := congrArg ProtectedView.leader hr
    leftBullet := congrArg ProtectedView.bullet hl
    rightBullet := congrArg ProtectedView.bullet hr
    leftShield := congrArg ProtectedView.shield hl
    rightShield := congrArg ProtectedView.shield hr
    leftSignal := congrArg ProtectedView.signal_B hl
    rightSignal := congrArg ProtectedView.signal_B hr
    passive := {
      leftLabel := congrArg ProtectedView.label hl
      rightLabel := congrArg ProtectedView.label hr
      leftProbe := congrArg ProtectedView.probe hl
      rightProbe := congrArg ProtectedView.probe hr
      leftPhase := congrArg ProtectedView.phase hl
      rightPhase := congrArg ProtectedView.phase hr
      leftState := congrArg ProtectedView.state hl
      rightState := congrArg ProtectedView.state hr
      leftPath := congrArg ProtectedView.path hl
      rightPath := congrArg ProtectedView.path hr
      leftPath2 := congrArg ProtectedView.path2 hl
      rightPath2 := congrArg ProtectedView.path2 hr
      leftP := congrArg ProtectedView.p hl
      rightP := congrArg ProtectedView.p hr
      leftPCarry := congrArg ProtectedView.p_carry hl
      rightPCarry := congrArg ProtectedView.p_carry hr
      leftPath4 := congrArg ProtectedView.path4 hl
      rightPath4 := congrArg ProtectedView.path4 hr
      leftPath5 := congrArg ProtectedView.path5 hl
      rightPath5 := congrArg ProtectedView.path5 hr } }


private theorem passiveFrame_trans
    {l r m n l' r' : AgentState 2}
    (h1 : PassiveFrame l r m n)
    (h2 : PassiveFrame m n l' r') :
    PassiveFrame l r l' r' := by
  exact {
    leftLabel := h2.leftLabel.trans h1.leftLabel
    rightLabel := h2.rightLabel.trans h1.rightLabel
    leftProbe := h2.leftProbe.trans h1.leftProbe
    rightProbe := h2.rightProbe.trans h1.rightProbe
    leftPhase := h2.leftPhase.trans h1.leftPhase
    rightPhase := h2.rightPhase.trans h1.rightPhase
    leftState := h2.leftState.trans h1.leftState
    rightState := h2.rightState.trans h1.rightState
    leftPath := h2.leftPath.trans h1.leftPath
    rightPath := h2.rightPath.trans h1.rightPath
    leftPath2 := h2.leftPath2.trans h1.leftPath2
    rightPath2 := h2.rightPath2.trans h1.rightPath2
    leftP := h2.leftP.trans h1.leftP
    rightP := h2.rightP.trans h1.rightP
    leftPCarry := h2.leftPCarry.trans h1.leftPCarry
    rightPCarry := h2.rightPCarry.trans h1.rightPCarry
    leftPath4 := h2.leftPath4.trans h1.leftPath4
    rightPath4 := h2.rightPath4.trans h1.rightPath4
    leftPath5 := h2.leftPath5.trans h1.leftPath5
    rightPath5 := h2.rightPath5.trans h1.rightPath5 }


private theorem protectedFrame_trans
    {l r m n l' r' : AgentState 2}
    (h1 : ProtectedFrame l r m n)
    (h2 : ProtectedFrame m n l' r') :
    ProtectedFrame l r l' r' := by
  exact {
    leftLeader := h2.leftLeader.trans h1.leftLeader
    rightLeader := h2.rightLeader.trans h1.rightLeader
    leftBullet := h2.leftBullet.trans h1.leftBullet
    rightBullet := h2.rightBullet.trans h1.rightBullet
    leftShield := h2.leftShield.trans h1.leftShield
    rightShield := h2.rightShield.trans h1.rightShield
    leftSignal := h2.leftSignal.trans h1.leftSignal
    rightSignal := h2.rightSignal.trans h1.rightSignal
    passive := passiveFrame_trans h1.passive h2.passive }


/-! SUPPRESS_SIG.  Each named substage changes only reset_cmd, echo, or count,
so every ProtectedView coordinate is an exact frame. -/


private theorem suppressSigStart_view_frame
    (l r : AgentState 2) :
    protectedPairOf
        (PPLL.suppressSigStart l r).1
        (PPLL.suppressSigStart l r).2 =
      protectedPairOf l r := by
  apply Prod.ext <;> apply ProtectedView.ext
  all_goals
    unfold protectedPairOf ProtectedView.ofState PPLL.suppressSigStart
    try dsimp only []
    repeat (first | rfl | split)


private theorem suppressSigMoveReset_view_frame
    (l r : AgentState 2) :
    protectedPairOf
        (PPLL.suppressSigMoveReset l r).1
        (PPLL.suppressSigMoveReset l r).2 =
      protectedPairOf l r := by
  apply Prod.ext <;> apply ProtectedView.ext
  all_goals
    unfold protectedPairOf ProtectedView.ofState PPLL.suppressSigMoveReset
    try dsimp only []
    repeat (first | rfl | split)


private theorem suppressSigTerminal_view_frame
    (l r : AgentState 2) :
    protectedPairOf
        (PPLL.suppressSigTerminal hpsi2 l r).1
        (PPLL.suppressSigTerminal hpsi2 l r).2 =
      protectedPairOf l r := by
  apply Prod.ext <;> apply ProtectedView.ext
  all_goals
    unfold protectedPairOf ProtectedView.ofState PPLL.suppressSigTerminal
    try dsimp only []
    repeat (first | rfl | split)


private theorem suppressSigEcho_view_frame
    (l r : AgentState 2) :
    protectedPairOf
        (PPLL.suppressSigEcho l r).1
        (PPLL.suppressSigEcho l r).2 =
      protectedPairOf l r := by
  apply Prod.ext <;> apply ProtectedView.ext
  all_goals
    unfold protectedPairOf ProtectedView.ofState PPLL.suppressSigEcho
    try dsimp only []
    repeat (first | rfl | split)


private theorem suppressSigFinish_view_frame
    (l r : AgentState 2) :
    protectedPairOf
        (PPLL.suppressSigFinish l r).1
        (PPLL.suppressSigFinish l r).2 =
      protectedPairOf l r := by
  apply Prod.ext <;> apply ProtectedView.ext
  all_goals
    unfold protectedPairOf ProtectedView.ofState PPLL.suppressSigFinish
    try dsimp only []
    repeat (first | rfl | split)


private theorem suppressSig_view_frame
    (l r : AgentState 2) :
    protectedPairOf
        (PPLL.suppressSig hpsi2 l r).1
        (PPLL.suppressSig hpsi2 l r).2 =
      protectedPairOf l r := by
  rw [PPLL.suppressSig_eq_staged]
  let q0 := PPLL.suppressSigStart l r
  let q1 := PPLL.suppressSigMoveReset q0.1 q0.2
  let q2 := PPLL.suppressSigTerminal hpsi2 q1.1 q1.2
  let q3 := PPLL.suppressSigEcho q2.1 q2.2
  let q4 := PPLL.suppressSigFinish q3.1 q3.2
  have h0 := suppressSigStart_view_frame l r
  have h1 := suppressSigMoveReset_view_frame q0.1 q0.2
  have h2 := suppressSigTerminal_view_frame q1.1 q1.2
  have h3 := suppressSigEcho_view_frame q2.1 q2.2
  have h4 := suppressSigFinish_view_frame q3.1 q3.2
  change protectedPairOf q0.1 q0.2 = protectedPairOf l r at h0
  change protectedPairOf q1.1 q1.2 = protectedPairOf q0.1 q0.2 at h1
  change protectedPairOf q2.1 q2.2 = protectedPairOf q1.1 q1.2 at h2
  change protectedPairOf q3.1 q3.2 = protectedPairOf q2.1 q2.2 at h3
  change protectedPairOf q4.1 q4.2 = protectedPairOf q3.1 q3.2 at h4
  change protectedPairOf q4.1 q4.2 = protectedPairOf l r
  exact h4.trans (h3.trans (h2.trans (h1.trans h0)))


/-- Public generic SUPPRESS_SIG frame.  reset_cmd, echo, count, and every
omitted field may have arbitrary input values. -/
theorem suppressSig_protected_frame
    (l r : AgentState 2) :
    ProtectedFrame l r
      (PPLL.suppressSig hpsi2 l r).1
      (PPLL.suppressSig hpsi2 l r).2 := by
  exact protectedFrame_of_view_eq (suppressSig_view_frame l r)


/-! Repaired Algorithm 15.  These are the only three named stages used below:
FIRE, MOVE, SIGNAL. -/


private theorem fire_eq_of_signals_zero
    (l r : AgentState 2)
    (hl : l.signal_B = (0 : Fin 2))
    (hr : r.signal_B = (0 : Fin 2)) :
    PPLLRepair.eliminateLeadersNoCollisionFire hpsi2 l r =
      (l, r) := by
  simp [PPLLRepair.eliminateLeadersNoCollisionFire, hl, hr]


private theorem move_eq_of_shielded_leader_live_responder
    (nextLabel : Fin 2) (l r : AgentState 2)
    (hlLeader : l.leader = true)
    (hlShield : l.shield = true)
    (hrBullet : r.bullet = (2 : Fin 3)) :
    PPLLRepair.eliminateLeadersNoCollisionMove
        nextLabel l r =
      (l, r) := by
  simp [PPLLRepair.eliminateLeadersNoCollisionMove,
    hlLeader, hlShield, hrBullet]


private theorem move_eq_of_right_bullet_zero
    (nextLabel : Fin 2) (l r : AgentState 2)
    (hrBullet : r.bullet = (0 : Fin 3)) :
    PPLLRepair.eliminateLeadersNoCollisionMove
        nextLabel l r =
      (l, r) := by
  simp [PPLLRepair.eliminateLeadersNoCollisionMove, hrBullet]


private theorem signal_view_frame_of_leader_live
    (nextLabel : Fin 2) (l r : AgentState 2)
    (hlLeader : l.leader = true)
    (hrBullet : r.bullet = (2 : Fin 3))
    (hlSignal : l.signal_B = (0 : Fin 2))
    (hrSignal : r.signal_B = (0 : Fin 2)) :
    protectedPairOf
        (PPLLRepair.eliminateLeadersNoCollisionSignal
          nextLabel l r).1
        (PPLLRepair.eliminateLeadersNoCollisionSignal
          nextLabel l r).2 =
      protectedPairOf l r := by
  apply Prod.ext <;> apply ProtectedView.ext
  all_goals
    simp [protectedPairOf, ProtectedView.ofState,
      PPLLRepair.eliminateLeadersNoCollisionSignal,
      hlLeader, hrBullet, hlSignal, hrSignal]


private theorem signal_view_frame_of_follower_zero_aligned
    (nextLabel : Fin 2) (l r : AgentState 2)
    (hlFollower : l.leader = false)
    (hrBullet : r.bullet = (0 : Fin 3))
    (hlSignal : l.signal_B = (0 : Fin 2))
    (hrSignal : r.signal_B = (0 : Fin 2))
    (halign : r.label = nextLabel) :
    protectedPairOf
        (PPLLRepair.eliminateLeadersNoCollisionSignal
          nextLabel l r).1
        (PPLLRepair.eliminateLeadersNoCollisionSignal
          nextLabel l r).2 =
      protectedPairOf l r := by
  apply Prod.ext <;> apply ProtectedView.ext
  all_goals
    simp [protectedPairOf, ProtectedView.ofState,
      PPLLRepair.eliminateLeadersNoCollisionSignal,
      hlFollower, hrBullet, hlSignal, hrSignal, halign] <;> rfl


/-- Exact 01 kernel: a signal-zero shielded initiating leader blocks the
responder live bullet.  FIRE is identity, MOVE is blocked by shield=true,
and SIGNAL clamps the live responder to signal_B=0, already its input value. -/
private theorem noCollision_leader_liveBlocked_frame
    (l r : AgentState 2)
    (hlLeader : l.leader = true)
    (hlShield : l.shield = true)
    (hrBullet : r.bullet = (2 : Fin 3))
    (hlSignal : l.signal_B = (0 : Fin 2))
    (hrSignal : r.signal_B = (0 : Fin 2)) :
    ProtectedFrame l r
      (PPLLRepair.eliminateLeadersNoCollision hpsi2 l r).1
      (PPLLRepair.eliminateLeadersNoCollision hpsi2 l r).2 := by
  apply protectedFrame_of_view_eq
  rw [PPLLRepair.eliminateLeadersNoCollision_eq_staged]
  let nextLabel : Fin 2 :=
    ⟨(l.label.val + 1) % 2, Nat.mod_lt _ hpsi2⟩
  let q0 :=
    PPLLRepair.eliminateLeadersNoCollisionFire hpsi2 l r
  let q1 :=
    PPLLRepair.eliminateLeadersNoCollisionMove
      nextLabel q0.1 q0.2
  change
    protectedPairOf
        (PPLLRepair.eliminateLeadersNoCollisionSignal
          nextLabel q1.1 q1.2).1
        (PPLLRepair.eliminateLeadersNoCollisionSignal
          nextLabel q1.1 q1.2).2 =
      protectedPairOf l r
  have hq0 : q0 = (l, r) := by
    unfold q0
    exact fire_eq_of_signals_zero l r hlSignal hrSignal
  have hq1 : q1 = (l, r) := by
    unfold q1
    rw [hq0]
    exact move_eq_of_shielded_leader_live_responder
      nextLabel l r hlLeader hlShield hrBullet
  rw [hq1]
  exact signal_view_frame_of_leader_live
    nextLabel l r hlLeader hrBullet hlSignal hrSignal


/-- Exact common 12/23/30 kernel: the initiator is a follower, the aligned
responder has no bullet, and both absence signals are zero.  The responder
leader bit is intentionally unrestricted here, so this covers both
follower->follower and follower->leader orientations. -/
private theorem noCollision_follower_zero_aligned_frame
    (l r : AgentState 2)
    (hlFollower : l.leader = false)
    (hrBullet : r.bullet = (0 : Fin 3))
    (hlSignal : l.signal_B = (0 : Fin 2))
    (hrSignal : r.signal_B = (0 : Fin 2))
    (halign :
      r.label =
        ⟨(l.label.val + 1) % 2, Nat.mod_lt _ hpsi2⟩) :
    ProtectedFrame l r
      (PPLLRepair.eliminateLeadersNoCollision hpsi2 l r).1
      (PPLLRepair.eliminateLeadersNoCollision hpsi2 l r).2 := by
  apply protectedFrame_of_view_eq
  rw [PPLLRepair.eliminateLeadersNoCollision_eq_staged]
  let nextLabel : Fin 2 :=
    ⟨(l.label.val + 1) % 2, Nat.mod_lt _ hpsi2⟩
  let q0 :=
    PPLLRepair.eliminateLeadersNoCollisionFire hpsi2 l r
  let q1 :=
    PPLLRepair.eliminateLeadersNoCollisionMove
      nextLabel q0.1 q0.2
  change
    protectedPairOf
        (PPLLRepair.eliminateLeadersNoCollisionSignal
          nextLabel q1.1 q1.2).1
        (PPLLRepair.eliminateLeadersNoCollisionSignal
          nextLabel q1.1 q1.2).2 =
      protectedPairOf l r
  have hq0 : q0 = (l, r) := by
    unfold q0
    exact fire_eq_of_signals_zero l r hlSignal hrSignal
  have hq1 : q1 = (l, r) := by
    unfold q1
    rw [hq0]
    exact move_eq_of_right_bullet_zero
      nextLabel l r hrBullet
  rw [hq1]
  have halign' : r.label = nextLabel := by
    exact halign
  exact signal_view_frame_of_follower_zero_aligned
    nextLabel l r hlFollower hrBullet hlSignal hrSignal halign'


private theorem headline_of_frame
    {l r l' r' : AgentState 2}
    {ll rl : Bool}
    {lb rb : Fin 3}
    {ls rs : Bool}
    {lsg rsg : Fin 2}
    (hframe : ProtectedFrame l r l' r')
    (hll : l.leader = ll)
    (hrl : r.leader = rl)
    (hlb : l.bullet = lb)
    (hrb : r.bullet = rb)
    (hls : l.shield = ls)
    (hrs : r.shield = rs)
    (hlsg : l.signal_B = lsg)
    (hrsg : r.signal_B = rsg) :
    l'.leader = ll ∧
    r'.leader = rl ∧
    l'.bullet = lb ∧
    r'.bullet = rb ∧
    l'.shield = ls ∧
    r'.shield = rs ∧
    l'.signal_B = lsg ∧
    r'.signal_B = rsg ∧
    l'.label = l.label ∧
    r'.label = r.label ∧
    l'.probe = l.probe ∧
    r'.probe = r.probe ∧
    l'.phase = l.phase ∧
    r'.phase = r.phase ∧
    l'.state = l.state ∧
    r'.state = r.state ∧
    l'.path = l.path ∧
    r'.path = r.path ∧
    l'.path2 = l.path2 ∧
    r'.path2 = r.path2 ∧
    l'.p = l.p ∧
    r'.p = r.p ∧
    l'.p_carry = l.p_carry ∧
    r'.p_carry = r.p_carry ∧
    l'.path4 = l.path4 ∧
    r'.path4 = r.path4 ∧
    l'.path5 = l.path5 ∧
    r'.path5 = r.path5 := by
  exact ⟨
    hframe.leftLeader.trans hll,
    hframe.rightLeader.trans hrl,
    hframe.leftBullet.trans hlb,
    hframe.rightBullet.trans hrb,
    hframe.leftShield.trans hls,
    hframe.rightShield.trans hrs,
    hframe.leftSignal.trans hlsg,
    hframe.rightSignal.trans hrsg,
    hframe.passive.leftLabel,
    hframe.passive.rightLabel,
    hframe.passive.leftProbe,
    hframe.passive.rightProbe,
    hframe.passive.leftPhase,
    hframe.passive.rightPhase,
    hframe.passive.leftState,
    hframe.passive.rightState,
    hframe.passive.leftPath,
    hframe.passive.rightPath,
    hframe.passive.leftPath2,
    hframe.passive.rightPath2,
    hframe.passive.leftP,
    hframe.passive.rightP,
    hframe.passive.leftPCarry,
    hframe.passive.rightPCarry,
    hframe.passive.leftPath4,
    hframe.passive.rightPath4,
    hframe.passive.leftPath5,
    hframe.passive.rightPath5⟩


/-- 01: A0 -> B1. -/
theorem pair01_A0_B1_protected
    (l r : AgentState 2)
    (hlLeader : l.leader = true)
    (hrLeader : r.leader = false)
    (hlLabel : l.label = (0 : Fin 2))
    (hrLabel : r.label = (1 : Fin 2))
    (hlBullet : l.bullet = (0 : Fin 3))
    (hrBullet : r.bullet = (2 : Fin 3))
    (hlShield : l.shield = true)
    (hrShield : r.shield = true)
    (hlSignal : l.signal_B = (0 : Fin 2))
    (hrSignal : r.signal_B = (0 : Fin 2)) :
    let q := suppressThenEliminate l r
    q.1.leader = true ∧
    q.2.leader = false ∧
    q.1.bullet = (0 : Fin 3) ∧
    q.2.bullet = (2 : Fin 3) ∧
    q.1.shield = true ∧
    q.2.shield = true ∧
    q.1.signal_B = (0 : Fin 2) ∧
    q.2.signal_B = (0 : Fin 2) ∧
    q.1.label = l.label ∧
    q.2.label = r.label ∧
    q.1.probe = l.probe ∧
    q.2.probe = r.probe ∧
    q.1.phase = l.phase ∧
    q.2.phase = r.phase ∧
    q.1.state = l.state ∧
    q.2.state = r.state ∧
    q.1.path = l.path ∧
    q.2.path = r.path ∧
    q.1.path2 = l.path2 ∧
    q.2.path2 = r.path2 ∧
    q.1.p = l.p ∧
    q.2.p = r.p ∧
    q.1.p_carry = l.p_carry ∧
    q.2.p_carry = r.p_carry ∧
    q.1.path4 = l.path4 ∧
    q.2.path4 = r.path4 ∧
    q.1.path5 = l.path5 ∧
    q.2.path5 = r.path5 := by
  let s := PPLL.suppressSig hpsi2 l r
  let q :=
    PPLLRepair.eliminateLeadersNoCollision hpsi2 s.1 s.2
  change
    q.1.leader = true ∧
    q.2.leader = false ∧
    q.1.bullet = (0 : Fin 3) ∧
    q.2.bullet = (2 : Fin 3) ∧
    q.1.shield = true ∧
    q.2.shield = true ∧
    q.1.signal_B = (0 : Fin 2) ∧
    q.2.signal_B = (0 : Fin 2) ∧
    q.1.label = l.label ∧
    q.2.label = r.label ∧
    q.1.probe = l.probe ∧
    q.2.probe = r.probe ∧
    q.1.phase = l.phase ∧
    q.2.phase = r.phase ∧
    q.1.state = l.state ∧
    q.2.state = r.state ∧
    q.1.path = l.path ∧
    q.2.path = r.path ∧
    q.1.path2 = l.path2 ∧
    q.2.path2 = r.path2 ∧
    q.1.p = l.p ∧
    q.2.p = r.p ∧
    q.1.p_carry = l.p_carry ∧
    q.2.p_carry = r.p_carry ∧
    q.1.path4 = l.path4 ∧
    q.2.path4 = r.path4 ∧
    q.1.path5 = l.path5 ∧
    q.2.path5 = r.path5
  have hs := suppressSig_protected_frame l r
  change ProtectedFrame l r s.1 s.2 at hs
  have hn :=
    noCollision_leader_liveBlocked_frame
      s.1 s.2
      (hs.leftLeader.trans hlLeader)
      (hs.leftShield.trans hlShield)
      (hs.rightBullet.trans hrBullet)
      (hs.leftSignal.trans hlSignal)
      (hs.rightSignal.trans hrSignal)
  change ProtectedFrame s.1 s.2 q.1 q.2 at hn
  have hframe : ProtectedFrame l r q.1 q.2 :=
    protectedFrame_trans hs hn
  exact headline_of_frame hframe
    hlLeader hrLeader hlBullet hrBullet
    hlShield hrShield hlSignal hrSignal


/-- 12: B1 -> A2. -/
theorem pair12_B1_A2_protected
    (l r : AgentState 2)
    (hlLeader : l.leader = false)
    (hrLeader : r.leader = false)
    (hlLabel : l.label = (1 : Fin 2))
    (hrLabel : r.label = (0 : Fin 2))
    (hlBullet : l.bullet = (2 : Fin 3))
    (hrBullet : r.bullet = (0 : Fin 3))
    (hlShield : l.shield = true)
    (hrShield : r.shield = true)
    (hlSignal : l.signal_B = (0 : Fin 2))
    (hrSignal : r.signal_B = (0 : Fin 2)) :
    let q := suppressThenEliminate l r
    q.1.leader = false ∧
    q.2.leader = false ∧
    q.1.bullet = (2 : Fin 3) ∧
    q.2.bullet = (0 : Fin 3) ∧
    q.1.shield = true ∧
    q.2.shield = true ∧
    q.1.signal_B = (0 : Fin 2) ∧
    q.2.signal_B = (0 : Fin 2) ∧
    q.1.label = l.label ∧
    q.2.label = r.label ∧
    q.1.probe = l.probe ∧
    q.2.probe = r.probe ∧
    q.1.phase = l.phase ∧
    q.2.phase = r.phase ∧
    q.1.state = l.state ∧
    q.2.state = r.state ∧
    q.1.path = l.path ∧
    q.2.path = r.path ∧
    q.1.path2 = l.path2 ∧
    q.2.path2 = r.path2 ∧
    q.1.p = l.p ∧
    q.2.p = r.p ∧
    q.1.p_carry = l.p_carry ∧
    q.2.p_carry = r.p_carry ∧
    q.1.path4 = l.path4 ∧
    q.2.path4 = r.path4 ∧
    q.1.path5 = l.path5 ∧
    q.2.path5 = r.path5 := by
  let s := PPLL.suppressSig hpsi2 l r
  let q :=
    PPLLRepair.eliminateLeadersNoCollision hpsi2 s.1 s.2
  change
    q.1.leader = false ∧
    q.2.leader = false ∧
    q.1.bullet = (2 : Fin 3) ∧
    q.2.bullet = (0 : Fin 3) ∧
    q.1.shield = true ∧
    q.2.shield = true ∧
    q.1.signal_B = (0 : Fin 2) ∧
    q.2.signal_B = (0 : Fin 2) ∧
    q.1.label = l.label ∧
    q.2.label = r.label ∧
    q.1.probe = l.probe ∧
    q.2.probe = r.probe ∧
    q.1.phase = l.phase ∧
    q.2.phase = r.phase ∧
    q.1.state = l.state ∧
    q.2.state = r.state ∧
    q.1.path = l.path ∧
    q.2.path = r.path ∧
    q.1.path2 = l.path2 ∧
    q.2.path2 = r.path2 ∧
    q.1.p = l.p ∧
    q.2.p = r.p ∧
    q.1.p_carry = l.p_carry ∧
    q.2.p_carry = r.p_carry ∧
    q.1.path4 = l.path4 ∧
    q.2.path4 = r.path4 ∧
    q.1.path5 = l.path5 ∧
    q.2.path5 = r.path5
  have hs := suppressSig_protected_frame l r
  change ProtectedFrame l r s.1 s.2 at hs
  have hsl : s.1.label = (1 : Fin 2) :=
    hs.passive.leftLabel.trans hlLabel
  have hsr : s.2.label = (0 : Fin 2) :=
    hs.passive.rightLabel.trans hrLabel
  have halign :
      s.2.label =
        ⟨(s.1.label.val + 1) % 2, Nat.mod_lt _ hpsi2⟩ := by
    apply Fin.ext
    simp [hsl, hsr]
  have hn :=
    noCollision_follower_zero_aligned_frame
      s.1 s.2
      (hs.leftLeader.trans hlLeader)
      (hs.rightBullet.trans hrBullet)
      (hs.leftSignal.trans hlSignal)
      (hs.rightSignal.trans hrSignal)
      halign
  change ProtectedFrame s.1 s.2 q.1 q.2 at hn
  have hframe : ProtectedFrame l r q.1 q.2 :=
    protectedFrame_trans hs hn
  exact headline_of_frame hframe
    hlLeader hrLeader hlBullet hrBullet
    hlShield hrShield hlSignal hrSignal


/-- 23: A2 -> B3. -/
theorem pair23_A2_B3_protected
    (l r : AgentState 2)
    (hlLeader : l.leader = false)
    (hrLeader : r.leader = false)
    (hlLabel : l.label = (0 : Fin 2))
    (hrLabel : r.label = (1 : Fin 2))
    (hlBullet : l.bullet = (0 : Fin 3))
    (hrBullet : r.bullet = (0 : Fin 3))
    (hlShield : l.shield = true)
    (hrShield : r.shield = true)
    (hlSignal : l.signal_B = (0 : Fin 2))
    (hrSignal : r.signal_B = (0 : Fin 2)) :
    let q := suppressThenEliminate l r
    q.1.leader = false ∧
    q.2.leader = false ∧
    q.1.bullet = (0 : Fin 3) ∧
    q.2.bullet = (0 : Fin 3) ∧
    q.1.shield = true ∧
    q.2.shield = true ∧
    q.1.signal_B = (0 : Fin 2) ∧
    q.2.signal_B = (0 : Fin 2) ∧
    q.1.label = l.label ∧
    q.2.label = r.label ∧
    q.1.probe = l.probe ∧
    q.2.probe = r.probe ∧
    q.1.phase = l.phase ∧
    q.2.phase = r.phase ∧
    q.1.state = l.state ∧
    q.2.state = r.state ∧
    q.1.path = l.path ∧
    q.2.path = r.path ∧
    q.1.path2 = l.path2 ∧
    q.2.path2 = r.path2 ∧
    q.1.p = l.p ∧
    q.2.p = r.p ∧
    q.1.p_carry = l.p_carry ∧
    q.2.p_carry = r.p_carry ∧
    q.1.path4 = l.path4 ∧
    q.2.path4 = r.path4 ∧
    q.1.path5 = l.path5 ∧
    q.2.path5 = r.path5 := by
  let s := PPLL.suppressSig hpsi2 l r
  let q :=
    PPLLRepair.eliminateLeadersNoCollision hpsi2 s.1 s.2
  change
    q.1.leader = false ∧
    q.2.leader = false ∧
    q.1.bullet = (0 : Fin 3) ∧
    q.2.bullet = (0 : Fin 3) ∧
    q.1.shield = true ∧
    q.2.shield = true ∧
    q.1.signal_B = (0 : Fin 2) ∧
    q.2.signal_B = (0 : Fin 2) ∧
    q.1.label = l.label ∧
    q.2.label = r.label ∧
    q.1.probe = l.probe ∧
    q.2.probe = r.probe ∧
    q.1.phase = l.phase ∧
    q.2.phase = r.phase ∧
    q.1.state = l.state ∧
    q.2.state = r.state ∧
    q.1.path = l.path ∧
    q.2.path = r.path ∧
    q.1.path2 = l.path2 ∧
    q.2.path2 = r.path2 ∧
    q.1.p = l.p ∧
    q.2.p = r.p ∧
    q.1.p_carry = l.p_carry ∧
    q.2.p_carry = r.p_carry ∧
    q.1.path4 = l.path4 ∧
    q.2.path4 = r.path4 ∧
    q.1.path5 = l.path5 ∧
    q.2.path5 = r.path5
  have hs := suppressSig_protected_frame l r
  change ProtectedFrame l r s.1 s.2 at hs
  have hsl : s.1.label = (0 : Fin 2) :=
    hs.passive.leftLabel.trans hlLabel
  have hsr : s.2.label = (1 : Fin 2) :=
    hs.passive.rightLabel.trans hrLabel
  have halign :
      s.2.label =
        ⟨(s.1.label.val + 1) % 2, Nat.mod_lt _ hpsi2⟩ := by
    apply Fin.ext
    simp [hsl, hsr]
  have hn :=
    noCollision_follower_zero_aligned_frame
      s.1 s.2
      (hs.leftLeader.trans hlLeader)
      (hs.rightBullet.trans hrBullet)
      (hs.leftSignal.trans hlSignal)
      (hs.rightSignal.trans hrSignal)
      halign
  change ProtectedFrame s.1 s.2 q.1 q.2 at hn
  have hframe : ProtectedFrame l r q.1 q.2 :=
    protectedFrame_trans hs hn
  exact headline_of_frame hframe
    hlLeader hrLeader hlBullet hrBullet
    hlShield hrShield hlSignal hrSignal


/-- 30: B3 -> A0. -/
theorem pair30_B3_A0_protected
    (l r : AgentState 2)
    (hlLeader : l.leader = false)
    (hrLeader : r.leader = true)
    (hlLabel : l.label = (1 : Fin 2))
    (hrLabel : r.label = (0 : Fin 2))
    (hlBullet : l.bullet = (0 : Fin 3))
    (hrBullet : r.bullet = (0 : Fin 3))
    (hlShield : l.shield = true)
    (hrShield : r.shield = true)
    (hlSignal : l.signal_B = (0 : Fin 2))
    (hrSignal : r.signal_B = (0 : Fin 2)) :
    let q := suppressThenEliminate l r
    q.1.leader = false ∧
    q.2.leader = true ∧
    q.1.bullet = (0 : Fin 3) ∧
    q.2.bullet = (0 : Fin 3) ∧
    q.1.shield = true ∧
    q.2.shield = true ∧
    q.1.signal_B = (0 : Fin 2) ∧
    q.2.signal_B = (0 : Fin 2) ∧
    q.1.label = l.label ∧
    q.2.label = r.label ∧
    q.1.probe = l.probe ∧
    q.2.probe = r.probe ∧
    q.1.phase = l.phase ∧
    q.2.phase = r.phase ∧
    q.1.state = l.state ∧
    q.2.state = r.state ∧
    q.1.path = l.path ∧
    q.2.path = r.path ∧
    q.1.path2 = l.path2 ∧
    q.2.path2 = r.path2 ∧
    q.1.p = l.p ∧
    q.2.p = r.p ∧
    q.1.p_carry = l.p_carry ∧
    q.2.p_carry = r.p_carry ∧
    q.1.path4 = l.path4 ∧
    q.2.path4 = r.path4 ∧
    q.1.path5 = l.path5 ∧
    q.2.path5 = r.path5 := by
  let s := PPLL.suppressSig hpsi2 l r
  let q :=
    PPLLRepair.eliminateLeadersNoCollision hpsi2 s.1 s.2
  change
    q.1.leader = false ∧
    q.2.leader = true ∧
    q.1.bullet = (0 : Fin 3) ∧
    q.2.bullet = (0 : Fin 3) ∧
    q.1.shield = true ∧
    q.2.shield = true ∧
    q.1.signal_B = (0 : Fin 2) ∧
    q.2.signal_B = (0 : Fin 2) ∧
    q.1.label = l.label ∧
    q.2.label = r.label ∧
    q.1.probe = l.probe ∧
    q.2.probe = r.probe ∧
    q.1.phase = l.phase ∧
    q.2.phase = r.phase ∧
    q.1.state = l.state ∧
    q.2.state = r.state ∧
    q.1.path = l.path ∧
    q.2.path = r.path ∧
    q.1.path2 = l.path2 ∧
    q.2.path2 = r.path2 ∧
    q.1.p = l.p ∧
    q.2.p = r.p ∧
    q.1.p_carry = l.p_carry ∧
    q.2.p_carry = r.p_carry ∧
    q.1.path4 = l.path4 ∧
    q.2.path4 = r.path4 ∧
    q.1.path5 = l.path5 ∧
    q.2.path5 = r.path5
  have hs := suppressSig_protected_frame l r
  change ProtectedFrame l r s.1 s.2 at hs
  have hsl : s.1.label = (1 : Fin 2) :=
    hs.passive.leftLabel.trans hlLabel
  have hsr : s.2.label = (0 : Fin 2) :=
    hs.passive.rightLabel.trans hrLabel
  have halign :
      s.2.label =
        ⟨(s.1.label.val + 1) % 2, Nat.mod_lt _ hpsi2⟩ := by
    apply Fin.ext
    simp [hsl, hsr]
  have hn :=
    noCollision_follower_zero_aligned_frame
      s.1 s.2
      (hs.leftLeader.trans hlLeader)
      (hs.rightBullet.trans hrBullet)
      (hs.leftSignal.trans hlSignal)
      (hs.rightSignal.trans hrSignal)
      halign
  change ProtectedFrame s.1 s.2 q.1 q.2 at hn
  have hframe : ProtectedFrame l r q.1 q.2 :=
    protectedFrame_trans hs hn
  exact headline_of_frame hframe
    hlLeader hrLeader hlBullet hrBullet
    hlShield hrShield hlSignal hrSignal


end ZZSafeN4ReversedEliminateGPT


#print axioms ZZSafeN4ReversedEliminateGPT.suppressSig_protected_frame
#print axioms ZZSafeN4ReversedEliminateGPT.pair01_A0_B1_protected
#print axioms ZZSafeN4ReversedEliminateGPT.pair12_B1_A2_protected
#print axioms ZZSafeN4ReversedEliminateGPT.pair23_A2_B3_protected
#print axioms ZZSafeN4ReversedEliminateGPT.pair30_B3_A0_protected
