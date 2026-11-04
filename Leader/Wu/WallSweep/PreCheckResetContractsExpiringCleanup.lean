import Leader.Wu.WallSweep.PreCheckResetContractsExpiringBullet

/-!
# Pre-CHECK reset contracts: ExpiringCleanup

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

/-- Physical/path-stall projection of the exact leader-source cleanup
contract. -/
def ExpiringLeaderSourceCleanup
    (input output : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop :=
  ComparisonNeutral output.1.core.erase.core ∧
    ComparisonNeutral output.2.core.erase.core ∧
    output.1.core.erase.core.reset_cmd = false ∧
    output.2.core.erase.core.reset_cmd =
      !input.2.core.erase.core.echo ∧
    output.1.core.erase.core.echo = false ∧
    output.2.core.erase.core.echo = false

/-- Bounded reification and path-stall expiry preserve the exact
comparison/reset/echo cleanup of a priority-open edge sourced by an existing
leader. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_leader_source_cleanup
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true) :
    ExpiringLeaderSourceCleanup (l, r)
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_leader_source_cleanup
      hpsi kappa l.core.erase r.core.erase hopen hlLeader
  have he := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change bounded.1.erase =
    (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  change bounded.2.erase =
    (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbaseL : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hL]
    exact ha.1
  have hbaseR : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hR]
    exact ha.2.1
  have hLf := deletionPriorityExpireOne_neutral_fields l lBase hbaseL
  have hRf := deletionPriorityExpireOne_neutral_fields r rBase hbaseR
  have hbaseLReset : lBase.core.erase.core.reset_cmd = false := by
    change bounded.1.erase.core.reset_cmd = false
    rw [hL]
    exact ha.2.2.1
  have hbaseRReset : rBase.core.erase.core.reset_cmd =
      !r.core.erase.core.echo := by
    change bounded.2.erase.core.reset_cmd = !r.core.erase.core.echo
    rw [hR]
    exact ha.2.2.2.1
  have hbaseLEcho : lBase.core.erase.core.echo = false := by
    change bounded.1.erase.core.echo = false
    rw [hL]
    exact ha.2.2.2.2.1
  have hbaseREcho : rBase.core.erase.core.echo = false := by
    change bounded.2.erase.core.echo = false
    rw [hR]
    exact ha.2.2.2.2.2
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages]
  exact ⟨hLf.1, hRf.1,
    hLf.2.2.2.1.trans hbaseLReset,
    hRf.2.2.2.1.trans hbaseRReset,
    hLf.2.2.2.2.1.trans hbaseLEcho,
    hRf.2.2.2.2.1.trans hbaseREcho⟩

/-- A complete finite pre-CHECK-reset interaction starting with two follower
endpoints cannot finish with both endpoints leaders. -/
theorem wallSweepPreCheckResetPathStall_followers_not_both_leaders
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : l.core.erase.core.leader = false)
    (hr : r.core.erase.core.leader = false) :
    let q := wallSweepPreCheckResetPathStallTransition
      hpsi kappa tau l r
    ¬ (q.1.core.erase.core.leader = true ∧
      q.2.core.erase.core.leader = true) := by
  let q := wallSweepPreCheckResetPathStallTransition
    hpsi kappa tau l r
  let a := wallSweepPreCheckResetAuthorizedTransition
    hpsi kappa l.core.erase r.core.erase
  have ha := wallSweepPreCheckResetAuthorized_followers_not_both_leaders
    hpsi kappa l.core.erase r.core.erase hl hr
  change ¬ (a.1.core.leader = true ∧ a.2.core.leader = true) at ha
  have hview := wallSweepPreCheckResetPathStall_peaceView_eq_authorized
    hpsi l r
  change (PeaceView.ofState q.1.core.erase.core,
      PeaceView.ofState q.2.core.erase.core) =
    authorizedPeaceViewPair a at hview
  have hleft := congrArg (fun p => p.1.leader) hview
  have hright := congrArg (fun p => p.2.leader) hview
  change ¬ (q.1.core.erase.core.leader = true ∧
    q.2.core.erase.core.leader = true)
  rintro ⟨hqLeft, hqRight⟩
  apply ha
  exact ⟨hleft.symm.trans hqLeft,
    hright.symm.trans hqRight⟩

/-- Finite reification and expiry preserve the stronger priority-open
follower-initiator contract: regardless of the input responder leader bit,
the two endpoints cannot both finish as leaders. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_left_follower_not_both
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hl : l.core.erase.core.leader = false) :
    let q := wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    ¬ (q.1.core.erase.core.leader = true ∧
      q.2.core.erase.core.leader = true) := by
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  let a := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l.core.erase r.core.erase
  have ha :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_left_follower_not_both
      hpsi kappa l.core.erase r.core.erase hopen hl
  change ¬ (a.1.core.leader = true ∧ a.2.core.leader = true) at ha
  have he := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change bounded.1.erase = a.1 at hL
  change bounded.2.erase = a.2 at hR
  have hfL := deletionPriorityExpireOne_path_frame l lBase
  have hfR := deletionPriorityExpireOne_path_frame r rBase
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages]
  dsimp only
  rintro ⟨houtL, houtR⟩
  apply ha
  constructor
  · have hbaseL : lBase.core.erase.core.leader = true :=
      hfL.2.1.symm.trans houtL
    change bounded.1.erase.core.leader = true at hbaseL
    exact (congrArg (fun u : AuthorizedAgentState psi => u.core.leader)
      hL).symm.trans hbaseL
  · have hbaseR : rBase.core.erase.core.leader = true :=
      hfR.2.1.symm.trans houtR
    change bounded.2.erase.core.leader = true at hbaseR
    exact (congrArg (fun u : AuthorizedAgentState psi => u.core.leader)
      hR).symm.trans hbaseR

/-- Follower/follower specialization retained for first-birth consumers. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_followers_not_both
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hl : l.core.erase.core.leader = false)
    (_hr : r.core.erase.core.leader = false) :
    let q := wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    ¬ (q.1.core.erase.core.leader = true ∧
      q.2.core.erase.core.leader = true) := by
  exact
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_left_follower_not_both
      hpsi l r hopen hl


end PPLLWallSweepPreCheckResetContracts
