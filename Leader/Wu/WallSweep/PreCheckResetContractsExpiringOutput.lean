import Leader.Wu.WallSweep.PreCheckResetContractsOutput

/-!
# Pre-CHECK reset contracts: ExpiringOutput

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

/-- A complete authorized pre-CHECK-reset interaction starting with two
followers cannot return two leaders. -/
theorem wallSweepPreCheckResetAuthorized_followers_not_both_leaders
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false)
    (hr : r.core.leader = false) :
    let q := wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r
    ¬ (q.1.core.leader = true ∧ q.2.core.leader = true) := by
  dsimp only
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 : l0.core.leader = false :=
    (normalizeDeletion_leader_eq l).trans hl
  have hr0 : r0.core.leader = false :=
    (normalizeDeletion_leader_eq r).trans hr
  by_cases hrActive : deletionActive r0 = true
  · have hbranch :
        wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
          authorizedEliminateSig hpsi l0 r0 :=
      wallSweepPreCheckResetAuthorizedTransition_eq_eliminate_of_active
        hpsi kappa l r hrActive
    have hleftFrame :
        (authorizedEliminateSig hpsi l0 r0).1.core.leader =
          l0.core.leader :=
      (PPLLVerify.eliminateSig_leaders_eq
        hpsi l0.core r0.core).1
    have hleftEq := congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.1.core.leader) hbranch
    rintro ⟨hleft, _⟩
    have hbad : (false : Bool) = true :=
      hl0.symm.trans (hleftFrame.symm.trans (hleftEq.symm.trans hleft))
    simp at hbad
  · have hrFalse : deletionActive r0 = false := by
      cases h : deletionActive r0
      · rfl
      · exact (hrActive h).elim
    by_cases hlActive : deletionActive l0 = true
    · have hbranch :
          wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
            (l0, r0) :=
        wallSweepPreCheckResetAuthorizedTransition_eq_pair_of_left_active
          hpsi kappa l r hrFalse hlActive
      have hleftEq := congrArg
        (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
          q.1.core.leader) hbranch
      rintro ⟨hleft, _⟩
      have hbad : (false : Bool) = true :=
        hl0.symm.trans (hleftEq.symm.trans hleft)
      simp at hbad
    · have hlFalse : deletionActive l0 = false := by
        cases h : deletionActive l0
        · rfl
        · exact (hlActive h).elim
      have hopen : AuthorizedPriorityOpen l r := by
        change deletionActive l0 = false ∧ deletionActive r0 = false
        exact ⟨hlFalse, hrFalse⟩
      let beforeRaw := wallSweepAuthorizedBeforeCheck
        hpsi kappa l0 r0
      let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
      let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
      let afterCheck := authorizedCheckSig
        hpsi beforeCheck.1 beforeCheck.2
      let born := leaderBirthBeforeOrAtCheck
        l0 r0 beforeCheck afterCheck
      let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
      have heq :=
        wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
          hpsi kappa l r hopen
      have htail := wallSweepPreCheckResetNormalTail_left_follower_not_both
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

/-- Bounded reification and outer expiration are transparent on all five
`PeaceView` fields for the pre-CHECK-reset transition. -/
theorem wallSweepPreCheckResetPathStall_peaceView_eq_authorized
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau) :
    let q := wallSweepPreCheckResetPathStallTransition
      hpsi kappa tau l r
    (PeaceView.ofState q.1.core.erase.core,
      PeaceView.ofState q.2.core.erase.core) =
      authorizedPeaceViewPair
        (wallSweepPreCheckResetAuthorizedTransition
          hpsi kappa l.core.erase r.core.erase) := by
  let bounded := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau :=
    ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau :=
    ⟨bounded.2, r.stall⟩
  have hlView := deletionPriorityExpireOne_peaceView_frame l lBase
  have hrView := deletionPriorityExpireOne_peaceView_frame r rBase
  have herase := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  change
    (PeaceView.ofState
        (deletionPriorityExpireOne tau l lBase).core.erase.core,
      PeaceView.ofState
        (deletionPriorityExpireOne tau r rBase).core.erase.core) = _
  calc
    _ = (PeaceView.ofState bounded.1.erase.core,
        PeaceView.ofState bounded.2.erase.core) :=
      Prod.ext hlView hrView
    _ = authorizedPeaceViewPair
        (bounded.1.erase, bounded.2.erase) := rfl
    _ = authorizedPeaceViewPair
        (wallSweepPreCheckResetAuthorizedTransition
          hpsi kappa l.core.erase r.core.erase) :=
      congrArg authorizedPeaceViewPair herase

/-- Bounded reification and outer expiration are also transparent on all five
`PeaceView` fields for the rooted leader-sink transition. -/
theorem wallSweepPreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau) :
    let q := wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    (PeaceView.ofState q.1.core.erase.core,
      PeaceView.ofState q.2.core.erase.core) =
      authorizedPeaceViewPair
        (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
          hpsi kappa l.core.erase r.core.erase) := by
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau :=
    ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau :=
    ⟨bounded.2, r.stall⟩
  have hlView := deletionPriorityExpireOne_peaceView_frame l lBase
  have hrView := deletionPriorityExpireOne_peaceView_frame r rBase
  have herase := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  change
    (PeaceView.ofState
        (deletionPriorityExpireOne tau l lBase).core.erase.core,
      PeaceView.ofState
        (deletionPriorityExpireOne tau r rBase).core.erase.core) = _
  calc
    _ = (PeaceView.ofState bounded.1.erase.core,
        PeaceView.ofState bounded.2.erase.core) :=
      Prod.ext hlView hrView
    _ = authorizedPeaceViewPair
        (bounded.1.erase, bounded.2.erase) := rfl
    _ = authorizedPeaceViewPair
        (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
          hpsi kappa l.core.erase r.core.erase) :=
      congrArg authorizedPeaceViewPair herase

/-- Finite reification and outer path-stall expiry preserve the complete
nonzero-responder migration contract of the rooted transition. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_nonzero_responder_migrates
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hrLeader : r.core.erase.core.leader = true)
    (hrNonzero : r.core.erase.core.label ≠ ⟨0, hpsi⟩) :
    let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    out.1.core.erase.core.leader = true ∧
      out.2.core.erase.core.leader = false ∧
      out.1.core.erase.core.label = l.core.erase.core.label ∧
      out.2.core.erase.core.label = r.core.erase.core.label := by
  let authorizedOut :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau l r
  have ha :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_nonzero_responder_migrates
      hpsi kappa l.core.erase r.core.erase hopen hrLeader hrNonzero
  have hview :=
    wallSweepPreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hleftLeader := congrArg (fun q => q.1.leader) hview
  have hrightLeader := congrArg (fun q => q.2.leader) hview
  have hleftLabel := congrArg (fun q => q.1.label) hview
  have hrightLabel := congrArg (fun q => q.2.label) hview
  change out.1.core.erase.core.leader =
    authorizedOut.1.core.leader at hleftLeader
  change out.2.core.erase.core.leader =
    authorizedOut.2.core.leader at hrightLeader
  change out.1.core.erase.core.label =
    authorizedOut.1.core.label at hleftLabel
  change out.2.core.erase.core.label =
    authorizedOut.2.core.label at hrightLabel
  change out.1.core.erase.core.leader = true ∧
    out.2.core.erase.core.leader = false ∧
    out.1.core.erase.core.label = l.core.erase.core.label ∧
    out.2.core.erase.core.label = r.core.erase.core.label
  exact ⟨hleftLeader.trans ha.1,
    hrightLeader.trans ha.2.1,
    hleftLabel.trans ha.2.2.1,
    hrightLabel.trans ha.2.2.2⟩

/-- The same physical migration theorem holds for the integrated reset-aware
transition: an existing responder leader makes its extra P-prime guard
definitionally redundant before the rooted full interaction runs. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_nonzero_responder_migrates
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hrLeader : r.core.erase.core.leader = true)
    (hrNonzero : r.core.erase.core.label ≠ ⟨0, hpsi⟩) :
    let out := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    out.1.core.erase.core.leader = true ∧
      out.2.core.erase.core.leader = false ∧
      out.1.core.erase.core.label = l.core.erase.core.label ∧
      out.2.core.erase.core.label = r.core.erase.core.label := by
  have heq :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_right_leader
      hpsi kappa tau l r hrLeader
  rw [heq]
  exact
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_nonzero_responder_migrates
      hpsi l r hopen hrLeader hrNonzero

/-- A priority-open rooted transition with an existing responder leader leaves
both authorized endpoints comparison-neutral.  The pre-CHECK repair supplies
neutrality before suppression, and neutral birth marking is inert. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_responder_leader_neutral
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hrLeader : r.core.leader = true) :
    authorizedBothNeutral
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r) := by
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  have htail :=
    wallSweepPreCheckResetLeaderSinkNormalTail_neutral_of_responder_leader
      hpsi kappa l r hrLeader
  have heq :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeCheck := wallSweepPreCheckResetBeforeCheck hpsi kappa l0 r0
  let afterCheck := wallSweepPreCheckResetAfterCheck hpsi kappa l0 r0
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have hmark := markLeaderBirth_eq_of_neutral born tail htail.1 htail.2
  exact bothNeutral_of_authorizedPair_eq (heq.trans hmark) htail

/-- Bounded reification and path-stall expiry preserve responder-leader
neutrality for the rooted transition. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_leader_neutral
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hrLeader : r.core.erase.core.leader = true) :
    let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    ComparisonNeutral out.1.core.erase.core ∧
      ComparisonNeutral out.2.core.erase.core := by
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_responder_leader_neutral
      hpsi kappa l.core.erase r.core.erase hopen hrLeader
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
    exact ha.2
  have hLf := deletionPriorityExpireOne_neutral_fields l lBase hbaseL
  have hRf := deletionPriorityExpireOne_neutral_fields r rBase hbaseR
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages]
  exact ⟨hLf.1, hRf.1⟩

/-- The integrated reset-aware transition has the same responder-leader
neutrality contract as the rooted transition. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_responder_leader_neutral
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hrLeader : r.core.erase.core.leader = true) :
    let out := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    ComparisonNeutral out.1.core.erase.core ∧
      ComparisonNeutral out.2.core.erase.core := by
  rw [wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_right_leader
    hpsi kappa tau l r hrLeader]
  exact
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_leader_neutral
      hpsi l r hopen hrLeader

/-- A live bullet at the responder of the authorized rooted transition has a
two-part origin: it was already at the input responder, and the input
initiator was a leader. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_responder_live_origin_and_initiator_leader
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (houtLive :
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r).2.core.bullet = ⟨2, by omega⟩) :
    r.core.bullet = ⟨2, by omega⟩ ∧ l.core.leader = true := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let raw := eliminateLeadersNoCollisionLeaderSink
    hpsi after.1.core after.2.core
  let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  have houtFields :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_bulletFieldPair
      hpsi kappa l r hopen
  change authorizedBulletFieldPair out = bulletFieldPair raw at houtFields
  have hrightOut := congrArg (fun q => q.2.bullet) houtFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hrightOut
  dsimp only at hrightOut
  have hrawLive : raw.2.bullet = ⟨2, by omega⟩ :=
    hrightOut.symm.trans houtLive
  have hsinkBullets := eliminateLeadersNoCollisionLeaderSink_bullets_eq
    hpsi after.1.core after.2.core
  have hnormalLive :
      (eliminateLeadersNoCollision hpsi
        after.1.core after.2.core).2.bullet = ⟨2, by omega⟩ :=
    hsinkBullets.2.symm.trans hrawLive
  have horigin := noCollision_right_live_origin
    hpsi after.1.core after.2.core hnormalLive
  have hinputFields :=
    wallSweepPreCheckResetNormalAfterSuppress_bulletFieldPair
      hpsi kappa l r
  change authorizedBulletFieldPair after =
    authorizedBulletFieldPair (l, r) at hinputFields
  have hrightInput := congrArg (fun q => q.2.bullet) hinputFields
  unfold authorizedBulletFieldPair bulletFieldPair BulletFields.ofState at hrightInput
  dsimp only at hrightInput
  have hleftLeader :=
    wallSweepPreCheckResetNormalAfterSuppress_initiator_leader_eq
      hpsi kappa l r
  exact ⟨hrightInput.symm.trans horigin.1,
    hleftLeader.symm.trans horigin.2⟩

/-- A follower initiator excludes a live bullet at the old responder-root
after the authorized reverse migration. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_right_not_live_of_left_follower
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlFollower : l.core.leader = false) :
    (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r).2.core.bullet ≠ ⟨2, by omega⟩ := by
  intro houtLive
  have horigin :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_responder_live_origin_and_initiator_leader
      hpsi kappa l r hopen houtLive
  have hbad : (true : Bool) = false := horigin.2.symm.trans hlFollower
  simp at hbad

/-- The old responder-root is also live-bullet-free after finite reification
and path-stall expiry. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_right_not_live_of_left_follower
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlFollower : l.core.erase.core.leader = false) :
    (wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r).2.core.erase.core.bullet ≠ ⟨2, by omega⟩ := by
  let authorizedOut :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau l r
  have hview :=
    wallSweepPreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hright := congrArg (fun q => q.2.bullet) hview
  change out.2.core.erase.core.bullet =
    authorizedOut.2.core.bullet at hright
  intro houtLive
  have ha :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_right_not_live_of_left_follower
      hpsi kappa l.core.erase r.core.erase hopen hlFollower
  exact ha (hright.symm.trans houtLive)

/-- The integrated reset-aware transition inherits old-root live-bullet
freedom when its input responder is the existing leader. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_right_not_live_of_left_follower
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlFollower : l.core.erase.core.leader = false)
    (hrLeader : r.core.erase.core.leader = true) :
    (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r).2.core.erase.core.bullet ≠ ⟨2, by omega⟩ := by
  rw [wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_right_leader
    hpsi kappa tau l r hrLeader]
  exact
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_right_not_live_of_left_follower
      hpsi l r hopen hlFollower

/-- Complete physical reverse-migration frame for an existing nonzero-label
responder leader.  It combines leader movement, exact labels, comparison
neutrality, and exclusion of a live bullet at the vacated root. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_nonzero_responder_migration_frame
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlFollower : l.core.erase.core.leader = false)
    (hrLeader : r.core.erase.core.leader = true)
    (hrNonzero : r.core.erase.core.label ≠ ⟨0, hpsi⟩) :
    let out := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    out.1.core.erase.core.leader = true ∧
      out.2.core.erase.core.leader = false ∧
      out.1.core.erase.core.label = l.core.erase.core.label ∧
      out.2.core.erase.core.label = r.core.erase.core.label ∧
      ComparisonNeutral out.1.core.erase.core ∧
      ComparisonNeutral out.2.core.erase.core ∧
      out.2.core.erase.core.bullet ≠ ⟨2, by omega⟩ := by
  have hmigrate :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_nonzero_responder_migrates
      hpsi l r hopen hrLeader hrNonzero
  have hneutral :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_responder_leader_neutral
      hpsi l r hopen hrLeader
  have hrightFree :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_right_not_live_of_left_follower
      hpsi l r hopen hlFollower hrLeader
  exact ⟨hmigrate.1, hmigrate.2.1, hmigrate.2.2.1,
    hmigrate.2.2.2, hneutral.1, hneutral.2, hrightFree⟩

/-- Finite reification and expiry preserve the responder live-bullet origin
contract of the complete priority-open rooted transition. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_live_origin
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (houtLive :
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r).2.core.erase.core.bullet = ⟨2, by omega⟩) :
    r.core.erase.core.bullet = ⟨2, by omega⟩ := by
  let authorizedOut :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau l r
  have hview :=
    wallSweepPreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
      hpsi l r
  have hright := congrArg (fun q => q.2.bullet) hview
  change out.2.core.erase.core.bullet =
    authorizedOut.2.core.bullet at hright
  have haLive : authorizedOut.2.core.bullet = ⟨2, by omega⟩ :=
    hright.symm.trans houtLive
  exact
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_responder_live_origin
      hpsi kappa l.core.erase r.core.erase hopen haLive

/-- Bounded reification and outer expiration are transparent on `PeaceView`
for the integrated reset-aware rooted transition as well. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_peaceView_eq_authorized
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau) :
    let q := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    (PeaceView.ofState q.1.core.erase.core,
      PeaceView.ofState q.2.core.erase.core) =
      authorizedPeaceViewPair
        (wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
          hpsi kappa l.core.erase r.core.erase) := by
  let bounded := wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau :=
    ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau :=
    ⟨bounded.2, r.stall⟩
  have hlView := deletionPriorityExpireOne_peaceView_frame l lBase
  have hrView := deletionPriorityExpireOne_peaceView_frame r rBase
  have herase :=
    erase_wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
      hpsi kappa l.core r.core
  change
    (PeaceView.ofState
        (deletionPriorityExpireOne tau l lBase).core.erase.core,
      PeaceView.ofState
        (deletionPriorityExpireOne tau r rBase).core.erase.core) = _
  calc
    _ = (PeaceView.ofState bounded.1.erase.core,
        PeaceView.ofState bounded.2.erase.core) :=
      Prod.ext hlView hrView
    _ = authorizedPeaceViewPair
        (bounded.1.erase, bounded.2.erase) := rfl
    _ = authorizedPeaceViewPair
        (wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
          hpsi kappa l.core.erase r.core.erase) :=
      congrArg authorizedPeaceViewPair herase


end PPLLWallSweepPreCheckResetContracts
