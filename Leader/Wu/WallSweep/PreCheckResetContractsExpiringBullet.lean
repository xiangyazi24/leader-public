import Leader.Wu.WallSweep.PreCheckResetContractsExpiringOutput

/-!
# Pre-CHECK reset contracts: ExpiringBullet

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

/-- Structured live-bullet rank comparison between two expiring physical
pairs. -/
structure ExpiringBulletTwoPairNonincrease
    (input output : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop where
  le : bulletTwoPairMass output.1.core.erase.core
      output.2.core.erase.core ≤
    bulletTwoPairMass input.1.core.erase.core input.2.core.erase.core

/-- Structured strict live-bullet rank decrease between two expiring physical
pairs. -/
structure ExpiringBulletTwoPairDecrease
    (input output : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop where
  lt : bulletTwoPairMass output.1.core.erase.core
      output.2.core.erase.core <
    bulletTwoPairMass input.1.core.erase.core input.2.core.erase.core
  inputInitiatorUnshielded :
    input.1.core.erase.core.shield = false
  inputResponderLive :
    input.2.core.erase.core.bullet = ⟨2, by omega⟩
  outputInitiatorFollower : output.1.core.erase.core.leader = false
  outputResponderFollower : output.2.core.erase.core.leader = false

/-- On a priority-open physical edge with a follower initiator, the complete
rooted transition cannot increase live-bullet mass. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_left_follower_bulletTwoPair
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlFollower : l.core.erase.core.leader = false) :
    let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    ExpiringBulletTwoPairNonincrease (l, r) out := by
  let authorizedOut : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
    wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
  refine { le := ?_ }
  change bulletTwoPairMass out.1.core.erase.core out.2.core.erase.core ≤
    bulletTwoPairMass l.core.erase.core r.core.erase.core
  have hview :=
    wallSweepPreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hleft := congrArg (fun q => q.1.bullet) hview
  have hright := congrArg (fun q => q.2.bullet) hview
  change out.1.core.erase.core.bullet = authorizedOut.1.core.bullet at hleft
  change out.2.core.erase.core.bullet = authorizedOut.2.core.bullet at hright
  have hmass : bulletTwoPairMass out.1.core.erase.core
      out.2.core.erase.core =
      bulletTwoPairMass authorizedOut.1.core authorizedOut.2.core :=
    bulletTwoPairMass_eq_of_bullets_eq hleft hright
  have ha : AuthorizedBulletTwoPairNonincrease
      (l.core.erase, r.core.erase) authorizedOut :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_left_follower_bulletTwoPair
      hpsi kappa l.core.erase r.core.erase hopen hlFollower
  calc
    bulletTwoPairMass out.1.core.erase.core out.2.core.erase.core =
        bulletTwoPairMass authorizedOut.1.core authorizedOut.2.core := hmass
    _ ≤ bulletTwoPairMass l.core.erase.core r.core.erase.core := ha.le

/-- Finite reification and both expiry stages preserve live-bullet
nonincrease for a zero-signal leader source. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_left_leader_signal_zero_bulletTwoPair
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true)
    (hlSignalZero : l.core.erase.core.signal_B = ⟨0, by omega⟩) :
    let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    ExpiringBulletTwoPairNonincrease (l, r) out := by
  let authorizedOut : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
    wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
  refine { le := ?_ }
  change bulletTwoPairMass out.1.core.erase.core out.2.core.erase.core ≤
    bulletTwoPairMass l.core.erase.core r.core.erase.core
  have hview :=
    wallSweepPreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hleft := congrArg (fun q => q.1.bullet) hview
  have hright := congrArg (fun q => q.2.bullet) hview
  change out.1.core.erase.core.bullet = authorizedOut.1.core.bullet at hleft
  change out.2.core.erase.core.bullet = authorizedOut.2.core.bullet at hright
  have hmass : bulletTwoPairMass out.1.core.erase.core
      out.2.core.erase.core =
      bulletTwoPairMass authorizedOut.1.core authorizedOut.2.core :=
    bulletTwoPairMass_eq_of_bullets_eq hleft hright
  have ha : AuthorizedBulletTwoPairNonincrease
      (l.core.erase, r.core.erase) authorizedOut :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_left_leader_signal_zero_bulletTwoPair
      hpsi kappa l.core.erase r.core.erase hopen hlLeader hlSignalZero
  calc
    bulletTwoPairMass out.1.core.erase.core out.2.core.erase.core =
        bulletTwoPairMass authorizedOut.1.core authorizedOut.2.core := hmass
    _ ≤ bulletTwoPairMass l.core.erase.core r.core.erase.core := ha.le

/-- On a leader-source edge the integrated reset-aware transition agrees
with the rooted transition, so the zero-signal live-bullet bound transfers
unchanged. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_left_leader_signal_zero_bulletTwoPair
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true)
    (hlSignalZero : l.core.erase.core.signal_B = ⟨0, by omega⟩) :
    let out := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    ExpiringBulletTwoPairNonincrease (l, r) out := by
  rw [wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
    hpsi kappa tau l r hlLeader]
  exact
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_left_leader_signal_zero_bulletTwoPair
      hpsi l r hopen hlLeader hlSignalZero

/-- The live-bullet nonincrease for a reset-aware follower/reset/follower
interaction survives finite reification and both pointwise expiry stages. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_reset_follower_bulletTwoPair
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlFollower : l.core.erase.core.leader = false)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hrFollower : r.core.erase.core.leader = false) :
    let out := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    ExpiringBulletTwoPairNonincrease (l, r) out := by
  let authorizedOut : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
  refine { le := ?_ }
  change bulletTwoPairMass out.1.core.erase.core out.2.core.erase.core ≤
    bulletTwoPairMass l.core.erase.core r.core.erase.core
  have hview :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hleft := congrArg (fun q => q.1.bullet) hview
  have hright := congrArg (fun q => q.2.bullet) hview
  change out.1.core.erase.core.bullet = authorizedOut.1.core.bullet at hleft
  change out.2.core.erase.core.bullet = authorizedOut.2.core.bullet at hright
  have hmass : bulletTwoPairMass out.1.core.erase.core
      out.2.core.erase.core =
      bulletTwoPairMass authorizedOut.1.core authorizedOut.2.core :=
    bulletTwoPairMass_eq_of_bullets_eq hleft hright
  have ha : AuthorizedBulletTwoPairNonincrease
      (l.core.erase, r.core.erase) authorizedOut :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_priority_open_reset_follower_bulletTwoPair
      hpsi kappa l.core.erase r.core.erase hopen hlFollower hlReset hrFollower
  calc
    bulletTwoPairMass out.1.core.erase.core out.2.core.erase.core =
        bulletTwoPairMass authorizedOut.1.core authorizedOut.2.core := hmass
    _ ≤ bulletTwoPairMass l.core.erase.core r.core.erase.core := ha.le

/-- Finite reification and pointwise expiry preserve the exact directional
live-bullet transport of a reset-aware follower step. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_reset_follower_live_bullets
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlFollower : l.core.erase.core.leader = false)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hrFollower : r.core.erase.core.leader = false)
    (hrLive : r.core.erase.core.bullet = ⟨2, by omega⟩) :
    let out := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    out.1.core.erase.core.bullet = ⟨2, by omega⟩ ∧
      out.2.core.erase.core.bullet = ⟨0, by omega⟩ := by
  let authorizedOut : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
  have hview :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hleft := congrArg (fun q => q.1.bullet) hview
  have hright := congrArg (fun q => q.2.bullet) hview
  change out.1.core.erase.core.bullet = authorizedOut.1.core.bullet at hleft
  change out.2.core.erase.core.bullet = authorizedOut.2.core.bullet at hright
  have ha :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_priority_open_follower_live_bullets
      hpsi kappa l.core.erase r.core.erase hopen hlFollower hlReset
        hrFollower hrLive
  change authorizedOut.1.core.bullet = ⟨2, by omega⟩ ∧
      authorizedOut.2.core.bullet = ⟨0, by omega⟩ at ha
  exact ⟨hleft.trans ha.1, hright.trans ha.2⟩

/-- Bounded reification and pointwise path-stall expiration preserve the
reset-aware signal-or-dummy progress dichotomy exactly. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_signal_or_dummy_moves
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlFollower : l.core.erase.core.leader = false)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hrFollower : r.core.erase.core.leader = false)
    (hlSignal : l.core.erase.core.signal_B = ⟨1, by omega⟩)
    (hrNotLive : r.core.erase.core.bullet ≠ ⟨2, by omega⟩) :
    let out :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r
    out.2.core.erase.core.signal_B = ⟨1, by omega⟩ ∨
      (r.core.erase.core.bullet = ⟨1, by omega⟩ ∧
        out.1.core.erase.core.bullet = ⟨1, by omega⟩ ∧
        out.2.core.erase.core.bullet = ⟨0, by omega⟩) := by
  let authorizedOut : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
  have hview :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hrightSignal := congrArg (fun q => q.2.signal_B) hview
  have hleftBullet := congrArg (fun q => q.1.bullet) hview
  have hrightBullet := congrArg (fun q => q.2.bullet) hview
  change out.2.core.erase.core.signal_B =
    authorizedOut.2.core.signal_B at hrightSignal
  change out.1.core.erase.core.bullet =
    authorizedOut.1.core.bullet at hleftBullet
  change out.2.core.erase.core.bullet =
    authorizedOut.2.core.bullet at hrightBullet
  have ha :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_priority_open_signal_or_dummy_moves
      hpsi kappa l.core.erase r.core.erase hopen hlFollower hlReset
        hrFollower hlSignal hrNotLive
  change authorizedOut.2.core.signal_B = ⟨1, by omega⟩ ∨
      (r.core.erase.core.bullet = ⟨1, by omega⟩ ∧
        authorizedOut.1.core.bullet = ⟨1, by omega⟩ ∧
        authorizedOut.2.core.bullet = ⟨0, by omega⟩) at ha
  rcases ha with hsignal | hdummy
  · exact .inl (hrightSignal.trans hsignal)
  · exact .inr ⟨hdummy.1, hleftBullet.trans hdummy.2.1,
      hrightBullet.trans hdummy.2.2⟩

/-- Bounded reification and pointwise path-stall expiration preserve the
exact reset-aware dummy-bullet transport equation. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_follower_bullets
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlFollower : l.core.erase.core.leader = false)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hrFollower : r.core.erase.core.leader = false)
    (hrNotLive : r.core.erase.core.bullet ≠ ⟨2, by omega⟩) :
    let out :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r
    out.1.core.erase.core.bullet =
        (if r.core.erase.core.bullet = ⟨1, by omega⟩ then
          ⟨1, by omega⟩ else l.core.erase.core.bullet) ∧
      out.2.core.erase.core.bullet = ⟨0, by omega⟩ := by
  let authorizedOut : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
  have hview :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hleftBullet := congrArg (fun q => q.1.bullet) hview
  have hrightBullet := congrArg (fun q => q.2.bullet) hview
  change out.1.core.erase.core.bullet =
    authorizedOut.1.core.bullet at hleftBullet
  change out.2.core.erase.core.bullet =
    authorizedOut.2.core.bullet at hrightBullet
  have ha :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_priority_open_follower_bullets
      hpsi kappa l.core.erase r.core.erase hopen hlFollower hlReset
        hrFollower hrNotLive
  change authorizedOut.1.core.bullet =
        (if r.core.erase.core.bullet = ⟨1, by omega⟩ then
          ⟨1, by omega⟩ else l.core.erase.core.bullet) ∧
      authorizedOut.2.core.bullet = ⟨0, by omega⟩ at ha
  exact ⟨hleftBullet.trans ha.1, hrightBullet.trans ha.2⟩

/-- Bounded reification and expiration preserve the source-covered responder
follower fact for the complete physical transition. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_follower_of_initiator_leader
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true)
    (hrFollower : r.core.erase.core.leader = false) :
    (wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r).2.core.erase.core.leader = false := by
  let authorizedOut :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau l r
  have hview :=
    wallSweepPreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hright := congrArg (fun q => q.2.leader) hview
  change out.2.core.erase.core.leader =
    authorizedOut.2.core.leader at hright
  exact hright.trans
    (wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_responder_follower_of_initiator_leader
      hpsi kappa l.core.erase r.core.erase hopen hlLeader hrFollower)

/-- Finite reification and both expiry stages preserve the leader-source
initiator signal clearing contract. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_left_signal_zero_of_left_leader
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true) :
    (wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r).1.core.erase.core.signal_B =
        ⟨0, by omega⟩ := by
  let authorizedOut :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau l r
  have hview :=
    wallSweepPreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hleft := congrArg (fun q => q.1.signal_B) hview
  change out.1.core.erase.core.signal_B =
    authorizedOut.1.core.signal_B at hleft
  exact hleft.trans
    (wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_left_signal_zero_of_left_leader
      hpsi kappa l.core.erase r.core.erase hopen hlLeader)

/-- The integrated reset-aware transition agrees with the rooted transition
on leader-source edges and therefore clears the same initiator signal. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_left_signal_zero_of_left_leader
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true) :
    (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r).1.core.erase.core.signal_B =
        ⟨0, by omega⟩ := by
  rw [wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
    hpsi kappa tau l r hlLeader]
  exact
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_left_signal_zero_of_left_leader
      hpsi l r hopen hlLeader

/-- The complete bounded/expiry rooted transition preserves the leader-source
absence signal write at a non-live follower responder. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_right_signal_one_of_left_leader_not_live
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true)
    (hrFollower : r.core.erase.core.leader = false)
    (hrNotLive : r.core.erase.core.bullet ≠ ⟨2, by omega⟩) :
    (wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r).2.core.erase.core.signal_B =
        ⟨1, by omega⟩ := by
  let authorizedOut :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau l r
  have hview :=
    wallSweepPreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hright := congrArg (fun q => q.2.signal_B) hview
  change out.2.core.erase.core.signal_B =
    authorizedOut.2.core.signal_B at hright
  exact hright.trans
    (wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_right_signal_one_of_left_leader_not_live
      hpsi kappa l.core.erase r.core.erase hopen hlLeader hrFollower
        hrNotLive)

/-- On an existing leader edge, the reset-aware probe prefix coincides with
the rooted transition.  Hence its complete physical output performs the same
positive signal write at every non-live follower responder. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_right_signal_one_of_left_leader_not_live
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true)
    (hrFollower : r.core.erase.core.leader = false)
    (hrNotLive : r.core.erase.core.bullet ≠ ⟨2, by omega⟩) :
    (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r).2.core.erase.core.signal_B =
        ⟨1, by omega⟩ := by
  rw [wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
    hpsi kappa tau l r hlLeader]
  exact
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_right_signal_one_of_left_leader_not_live
      hpsi l r hopen hlLeader hrFollower hrNotLive

/-- The complete bounded/expiry output of a surviving leader edge is
collision-safe for an immediate replay of that same edge. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_survivor_safe
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true)
    (hrFollower : r.core.erase.core.leader = false)
    (houtLeader :
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r).1.core.erase.core.leader = true) :
    (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r).2.core.erase.core.bullet =
        ⟨2, by omega⟩ →
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r).1.core.erase.core.shield = true := by
  let authorizedOut :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau l r
  have hview :=
    wallSweepPreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hleftLeader := congrArg (fun q => q.1.leader) hview
  have hrightBullet := congrArg (fun q => q.2.bullet) hview
  have hleftShield := congrArg (fun q => q.1.shield) hview
  change out.1.core.erase.core.leader =
    authorizedOut.1.core.leader at hleftLeader
  change out.2.core.erase.core.bullet =
    authorizedOut.2.core.bullet at hrightBullet
  change out.1.core.erase.core.shield =
    authorizedOut.1.core.shield at hleftShield
  have haLeader : authorizedOut.1.core.leader = true :=
    hleftLeader.symm.trans houtLeader
  have haSafe :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_survivor_safe
      hpsi kappa l.core.erase r.core.erase hopen
        hlLeader hrFollower haLeader
  intro houtBullet
  have haBullet : authorizedOut.2.core.bullet =
      ⟨2, by omega⟩ := hrightBullet.symm.trans houtBullet
  exact hleftShield.trans (haSafe haBullet)

/-- Physical/path-stall lift of survivor preservation for a live follower
responder. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_survivor_preserves_responder_live
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true)
    (hrFollower : r.core.erase.core.leader = false)
    (hrLive : r.core.erase.core.bullet = ⟨2, by omega⟩)
    (houtLeader :
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r).1.core.erase.core.leader = true) :
    (wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r).2.core.erase.core.bullet = ⟨2, by omega⟩ := by
  let authorizedOut :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau l r
  have hview :=
    wallSweepPreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hleftLeader := congrArg (fun q => q.1.leader) hview
  have hrightBullet := congrArg (fun q => q.2.bullet) hview
  change out.1.core.erase.core.leader =
    authorizedOut.1.core.leader at hleftLeader
  change out.2.core.erase.core.bullet =
    authorizedOut.2.core.bullet at hrightBullet
  have haLeader : authorizedOut.1.core.leader = true :=
    hleftLeader.symm.trans houtLeader
  have haLive :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_survivor_preserves_responder_live
      hpsi kappa l.core.erase r.core.erase hopen hlLeader hrFollower
        hrLive haLeader
  exact hrightBullet.trans haLive

/-- On an existing leader edge, the reset-probe prefix reduces to the rooted
transition, so survivor preservation of a live follower responder transfers
unchanged to the integrated transition. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_survivor_preserves_responder_live
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true)
    (hrFollower : r.core.erase.core.leader = false)
    (hrLive : r.core.erase.core.bullet = ⟨2, by omega⟩)
    (houtLeader :
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r).1.core.erase.core.leader = true) :
    (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r).2.core.erase.core.bullet = ⟨2, by omega⟩ := by
  rw [wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
    hpsi kappa tau l r hlLeader] at houtLeader ⊢
  exact
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_survivor_preserves_responder_live
      hpsi l r hopen hlLeader hrFollower hrLive houtLeader

/-- If a priority-open physical interaction kills its initiating leader against
a follower responder, the complete bounded/expiry transition strictly consumes
one live bullet on the active pair. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_killed_bulletTwoPair
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true)
    (hrFollower : r.core.erase.core.leader = false)
    (houtFollower :
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r).1.core.erase.core.leader = false) :
    let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    ExpiringBulletTwoPairDecrease (l, r) out := by
  let authorizedOut : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
    wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
  have hview :=
    wallSweepPreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hleftLeader := congrArg (fun q => q.1.leader) hview
  change out.1.core.erase.core.leader =
    authorizedOut.1.core.leader at hleftLeader
  have haFollower : authorizedOut.1.core.leader = false :=
    hleftLeader.symm.trans houtFollower
  have ha : AuthorizedBulletTwoPairDecrease
      (l.core.erase, r.core.erase) authorizedOut :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_initiator_killed_bulletTwoPair
      hpsi kappa l.core.erase r.core.erase hopen
        hlLeader hrFollower haFollower
  have hleft := congrArg (fun q => q.1.bullet) hview
  have hright := congrArg (fun q => q.2.bullet) hview
  change out.1.core.erase.core.bullet = authorizedOut.1.core.bullet at hleft
  change out.2.core.erase.core.bullet = authorizedOut.2.core.bullet at hright
  have hmass : bulletTwoPairMass out.1.core.erase.core
      out.2.core.erase.core =
      bulletTwoPairMass authorizedOut.1.core authorizedOut.2.core :=
    bulletTwoPairMass_eq_of_bullets_eq hleft hright
  have hrightLeader := congrArg (fun q => q.2.leader) hview
  change out.2.core.erase.core.leader =
    authorizedOut.2.core.leader at hrightLeader
  refine {
    lt := ?_
    inputInitiatorUnshielded := ha.inputInitiatorUnshielded
    inputResponderLive := ha.inputResponderLive
    outputInitiatorFollower := houtFollower
    outputResponderFollower :=
      hrightLeader.trans ha.outputResponderFollower }
  · calc
      bulletTwoPairMass out.1.core.erase.core out.2.core.erase.core =
          bulletTwoPairMass authorizedOut.1.core authorizedOut.2.core := hmass
      _ < bulletTwoPairMass l.core.erase.core r.core.erase.core := ha.lt

/-- Collision safety is sufficient for an existing initiating leader to
survive the complete priority-open physical interaction. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_survives_of_safe
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true)
    (hrFollower : r.core.erase.core.leader = false)
    (hsafe : r.core.erase.core.bullet = ⟨2, by omega⟩ →
      l.core.erase.core.shield = true) :
    (wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r).1.core.erase.core.leader = true := by
  cases hout :
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r).1.core.erase.core.leader with
  | false =>
      have hdecrease :=
        wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_killed_bulletTwoPair
          hpsi l r hopen hlLeader hrFollower hout
      have hshield := hsafe hdecrease.inputResponderLive
      have hbad : (false : Bool) = true :=
        hdecrease.inputInitiatorUnshielded.symm.trans hshield
      simp at hbad
  | true => rfl

/-- The rooted leader-sink repair preserves a shielded initiating leader when
its responder is a follower.  At the post-suppression boundary the responder
is still a follower, so the guarded Algorithm-15 suffix agrees with the
established suffix; the common leader-birth marker preserves the anchor. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_initiator_anchor_of_responder_follower
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core)
    (hrFollower : r.core.leader = false) :
    authorizedInitiatorAnchor
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeCheck := wallSweepPreCheckResetBeforeCheck hpsi kappa l0 r0
  let afterCheck := wallSweepPreCheckResetAfterCheck hpsi kappa l0 r0
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  have hafterAnchor : InitiatorAnchor after.1.core :=
    wallSweepPreCheckResetNormalAfterSuppress_initiator_anchor
      hpsi kappa l r hanchor
  have hafterFollower : after.2.core.leader = false :=
    (wallSweepPreCheckResetNormalAfterSuppress_responder_leader_eq_of_initiator_leader
      hpsi kappa l r hanchor.1).trans hrFollower
  have htailAnchor : authorizedInitiatorAnchor tail := by
    change authorizedInitiatorAnchor
      (authorizedPostSuppressLeaderSink hpsi after.1 after.2)
    rw [authorizedPostSuppressLeaderSink_eq_of_responder_follower
      hpsi after.1 after.2 hafterFollower]
    exact authorizedPostSuppress_initiator_anchor
      hpsi after.1 after.2 hafterAnchor
  have heq :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change wallSweepPreCheckResetLeaderSinkAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at heq
  rw [heq]
  exact markLeaderBirth_initiator_anchor born tail htailAnchor

/-- Bounded reification and both expiry stages lift the rooted
leader-to-follower anchor contract to the physical transition. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_anchor_of_responder_follower
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core.erase.core)
    (hrFollower : r.core.erase.core.leader = false) :
    expiringInitiatorAnchor
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  have ha :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_initiator_anchor_of_responder_follower
      hpsi kappa l.core.erase r.core.erase hopen hanchor hrFollower
  have he := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  change bounded.1.erase =
    (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  have hbase : InitiatorAnchor lBase.core.erase.core := by
    change InitiatorAnchor bounded.1.erase.core
    rw [hL]
    exact ha
  have hf := deletionPriorityExpireOne_path_frame l lBase
  have hs := deletionPriorityExpireOne_shield_frame l lBase
  have hfinal : InitiatorAnchor
      (deletionPriorityExpireOne tau l lBase).core.erase.core :=
    ⟨hf.2.1.trans hbase.1, hs.trans hbase.2⟩
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages]
  exact hfinal

/-- A leader whose absence signal is one fires and installs its shield on a
priority-open follower edge without any input label-alignment premise.  The
ordinary pre-Algorithm-15 prefix frames the source signal; the exact live-hit
certificate excludes leader death, and the rooted Algorithm-15 output frames
the newly installed shield through gated WRITE. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_initiator_anchor_of_signal_one
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlLeader : l.core.leader = true)
    (hlSignal : l.core.signal_B = ⟨1, by omega⟩)
    (hrFollower : r.core.leader = false) :
    authorizedInitiatorAnchor
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r) := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  let raw := eliminateLeadersNoCollisionLeaderSink
    hpsi after.1.core after.2.core
  have hafterFields : authorizedBulletFieldPair after =
      authorizedBulletFieldPair (l, r) :=
    wallSweepPreCheckResetNormalAfterSuppress_bulletFieldPair
      hpsi kappa l r
  have hafterSignal := congrArg (fun q => q.1.signal_B) hafterFields
  unfold authorizedBulletFieldPair bulletFieldPair
    BulletFields.ofState at hafterSignal
  dsimp only at hafterSignal
  have hafterSignalOne : after.1.core.signal_B = ⟨1, by omega⟩ :=
    hafterSignal.trans hlSignal
  have hstage :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  have hstageLeader := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.1.core.leader) hstage
  have hmarkLeaders := markLeaderBirth_leaders_eq
    (leaderBirthBeforeOrAtCheck
      (normalizeDeletion l) (normalizeDeletion r)
      (wallSweepPreCheckResetBeforeCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))
      (wallSweepPreCheckResetAfterCheck hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))) tail
  have houtLeader : out.1.core.leader = true := by
    cases hout : out.1.core.leader with
    | true => rfl
    | false =>
        have htailFollower : tail.1.core.leader = false :=
          hmarkLeaders.1.symm.trans (hstageLeader.symm.trans hout)
        have hhit :=
          wallSweepPreCheckResetLeaderSinkNormalTail_live_hit_of_initiator_killed
            hpsi kappa l r hlLeader hrFollower htailFollower
        change AuthorizedInitiatorLeaderLiveHit after.1 after.2 tail at hhit
        have hbad : (⟨0, by omega⟩ : Fin 2) = ⟨1, by omega⟩ :=
          hhit.sourceSignalZero.symm.trans hafterSignalOne
        have hval := congrArg Fin.val hbad
        simp at hval
  have hafterLeader : after.1.core.leader = true :=
    (wallSweepPreCheckResetNormalAfterSuppress_initiator_leader_eq
      hpsi kappa l r).trans hlLeader
  have hafterFollower : after.2.core.leader = false :=
    (wallSweepPreCheckResetNormalAfterSuppress_responder_leader_eq_of_initiator_leader
      hpsi kappa l r hlLeader).trans hrFollower
  have hrawEq :=
    eliminateLeadersNoCollisionLeaderSink_eq_of_responder_follower
      hpsi after.1.core after.2.core hafterFollower
  have hrawShield : raw.1.shield = true := by
    change (eliminateLeadersNoCollisionLeaderSink
      hpsi after.1.core after.2.core).1.shield = true
    rw [hrawEq]
    exact (noCollision_left_fire_fields
      hpsi after.1.core after.2.core hafterLeader hafterSignalOne).1
  have houtFields :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_bulletFieldPair
      hpsi kappa l r hopen
  change authorizedBulletFieldPair out = bulletFieldPair raw at houtFields
  have houtShield := congrArg (fun q => q.1.shield) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair
    BulletFields.ofState at houtShield
  dsimp only at houtShield
  exact ⟨houtLeader, houtShield.trans hrawShield⟩

/-- Bounded reification and both expiry stages preserve the no-alignment
signal-one fire anchor. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_anchor_of_signal_one
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true)
    (hlSignal : l.core.erase.core.signal_B = ⟨1, by omega⟩)
    (hrFollower : r.core.erase.core.leader = false) :
    expiringInitiatorAnchor
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r) := by
  let authorizedOut :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau l r
  have ha :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_initiator_anchor_of_signal_one
      hpsi kappa l.core.erase r.core.erase hopen hlLeader hlSignal hrFollower
  have hview :=
    wallSweepPreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hleft := congrArg Prod.fst hview
  have hleader := congrArg PeaceView.leader hleft
  have hshield := congrArg PeaceView.shield hleft
  change out.1.core.erase.core.leader = authorizedOut.1.core.leader at hleader
  change out.1.core.erase.core.shield = authorizedOut.1.core.shield at hshield
  exact ⟨hleader.trans ha.1, hshield.trans ha.2⟩

/-- The integrated reset-aware transition agrees with the rooted transition
on an existing leader source and therefore inherits the no-alignment
signal-one fire anchor. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_initiator_anchor_of_signal_one
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true)
    (hlSignal : l.core.erase.core.signal_B = ⟨1, by omega⟩)
    (hrFollower : r.core.erase.core.leader = false) :
    expiringInitiatorAnchor
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r) := by
  rw [wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
    hpsi kappa tau l r hlLeader]
  exact
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_anchor_of_signal_one
      hpsi l r hopen hlLeader hlSignal hrFollower


end PPLLWallSweepPreCheckResetContracts
