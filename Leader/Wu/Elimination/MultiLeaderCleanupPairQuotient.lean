import Leader.Wu.Elimination.MultiLeaderCleanup
import Leader.Wu.WallSweep.NormalResetContract
import Leader.Wu.Safety.NoCheckBirthConditionTwoProtocol
import Leader.Wu.WallSweep.RestartableGeneric

namespace PPLLCompleteMultiLeaderCleanup
namespace PhysicalBridge

open PPLL PPLLRepair PPLLVerify PPLLResearchFormulation PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLTerminalEqualSupportRepair PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepNormalResetContract PPLLWallSweepPreCheckResetRepair
  PPLLNoCheckBirthLeaderFrames PPLLNoCheckBirthBoundaryFrames
  PPLLNoCheckBirthConditionTwoFrames
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol
  PPLLNoCheckBirthConditionTwoWriteFrames
  PPLLWriteIncrementGate

variable {n psi kappa tau : Nat}

/-! ## The local five-field projection -/

private def cleanupPhysicalViewOfPeaceView
    (v : PeaceView psi) : CleanupPhysicalView psi where
  leader := v.leader
  label := v.label
  shield := v.shield
  bullet := v.bullet
  signal_B := v.signal_B

private def peaceViewOfCleanupPhysicalView
    (v : CleanupPhysicalView psi) : PeaceView psi where
  leader := v.leader
  label := v.label
  shield := v.shield
  bullet := v.bullet
  signal_B := v.signal_B

/-- Use a fresh projection name so this bridge does not depend on whether the
local file also gives `CleanupPhysicalView.ofState`. -/
def cleanupPhysicalViewOfState
    (u : AgentState psi) : CleanupPhysicalView psi :=
  cleanupPhysicalViewOfPeaceView (PeaceView.ofState u)

def cleanupPhysicalViewPair
    (q : AgentState psi × AgentState psi) :
    CleanupPhysicalView psi × CleanupPhysicalView psi :=
  (cleanupPhysicalViewOfState q.1, cleanupPhysicalViewOfState q.2)

def authorizedCleanupPhysicalViewPair
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    CleanupPhysicalView psi × CleanupPhysicalView psi :=
  cleanupPhysicalViewPair (q.1.core, q.2.core)

def expiringCleanupPhysicalViewPair
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) :
    CleanupPhysicalView psi × CleanupPhysicalView psi :=
  cleanupPhysicalViewPair
    (q.1.core.erase.core, q.2.core.erase.core)

private theorem cleanupPhysicalViewPair_eq_of_peaceViewPair_eq
    {a b : AgentState psi × AgentState psi}
    (h : peaceViewPair a = peaceViewPair b) :
    cleanupPhysicalViewPair a = cleanupPhysicalViewPair b := by
  have h' := congrArg
    (fun q : PeaceView psi × PeaceView psi =>
      (cleanupPhysicalViewOfPeaceView q.1,
       cleanupPhysicalViewOfPeaceView q.2)) h
  simpa [cleanupPhysicalViewPair, cleanupPhysicalViewOfState,
    peaceViewPair] using h'

private theorem peaceView_eq_of_cleanupPhysicalView_eq
    {a b : AgentState psi}
    (h : cleanupPhysicalViewOfState a = cleanupPhysicalViewOfState b) :
    PeaceView.ofState a = PeaceView.ofState b := by
  have h' := congrArg peaceViewOfCleanupPhysicalView h
  simpa [cleanupPhysicalViewOfState, cleanupPhysicalViewOfPeaceView,
    peaceViewOfCleanupPhysicalView, PeaceView.ofState] using h'

/-! ## 1. Exact bounded erasure -/

/-- Reification of the complete authorized cleanup transition erases exactly;
no observational quotient is used in this theorem. -/
theorem erase_multiLeaderCleanupBoundedTransition
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedBoundedAgentState psi kappa) :
    let q := multiLeaderCleanupBoundedTransition hpsi kappa l r
    (q.1.erase, q.2.erase) =
      multiLeaderCleanupAuthorizedTransition
        hpsi kappa l.erase r.erase := by
  let q := multiLeaderCleanupAuthorizedTransition
    hpsi kappa l.erase r.erase
  let hq := multiLeaderCleanupAuthorizedTransition_inProtocolDomain
    hpsi kappa l.erase r.erase
      l.core.erase_inProtocolDomain r.core.erase_inProtocolDomain
  change
    (⟨(BoundedAgentState.ofDomain q.1.core hq.1).erase,
        q.1.path0Crossed⟩,
     ⟨(BoundedAgentState.ofDomain q.2.core hq.2).erase,
        q.2.path0Crossed⟩) = q
  rw [BoundedAgentState.erase_ofDomain,
    BoundedAgentState.erase_ofDomain]

/-! ## 2. Deletion-priority/path-stall preservation of the five fields -/

/-- The outer expiry policy may clear comparison state and reset its timer, but
it cannot change leader, label, shield, bullet, or `signal_B`. -/
theorem deletionPriorityExpireOne_cleanupPhysicalView
    (old out : ExpiringAgentState psi kappa tau) :
    cleanupPhysicalViewOfState
        (deletionPriorityExpireOne tau old out).core.erase.core =
      cleanupPhysicalViewOfState out.core.erase.core := by
  change cleanupPhysicalViewOfPeaceView
      (PeaceView.ofState
        (deletionPriorityExpireOne tau old out).core.erase.core) =
    cleanupPhysicalViewOfPeaceView
      (PeaceView.ofState out.core.erase.core)
  exact congrArg cleanupPhysicalViewOfPeaceView
    (deletionPriorityExpireOne_peaceView_frame old out)

/-- The complete expiring transition has exactly the view of its authorized
transition.  This deliberately does not assert equality of erased states. -/
theorem multiLeaderCleanupTransition_cleanupPhysicalView_eq_authorized
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    expiringCleanupPhysicalViewPair
        (multiLeaderCleanupTransition hpsi kappa tau l r) =
      authorizedCleanupPhysicalViewPair
        (multiLeaderCleanupAuthorizedTransition
          hpsi kappa l.core.erase r.core.erase) := by
  let bounded := multiLeaderCleanupBoundedTransition
    hpsi kappa l.core r.core
  let lOut : ExpiringAgentState psi kappa tau :=
    ⟨bounded.1, l.stall⟩
  let rOut : ExpiringAgentState psi kappa tau :=
    ⟨bounded.2, r.stall⟩
  have hL := deletionPriorityExpireOne_cleanupPhysicalView l lOut
  have hR := deletionPriorityExpireOne_cleanupPhysicalView r rOut
  have hErase := erase_multiLeaderCleanupBoundedTransition
    hpsi kappa l.core r.core
  change
    (cleanupPhysicalViewOfState
        (deletionPriorityExpireOne tau l lOut).core.erase.core,
     cleanupPhysicalViewOfState
        (deletionPriorityExpireOne tau r rOut).core.erase.core) =
      authorizedCleanupPhysicalViewPair
        (multiLeaderCleanupAuthorizedTransition
          hpsi kappa l.core.erase r.core.erase)
  calc
    _ = cleanupPhysicalViewPair
        (lOut.core.erase.core, rOut.core.erase.core) :=
      Prod.ext hL hR
    _ = authorizedCleanupPhysicalViewPair
        (bounded.1.erase, bounded.2.erase) := rfl
    _ = authorizedCleanupPhysicalViewPair
        (multiLeaderCleanupAuthorizedTransition
          hpsi kappa l.core.erase r.core.erase) :=
      congrArg authorizedCleanupPhysicalViewPair hErase

/-! ## Exact tail-idle hypotheses -/

/-- These four left-endpoint fields, and no `path2/path4/path5/p/reset/echo`
or WRITE field, are needed to make CHECK, DISAPPEAR and action-one COMPARE
exactly idle. -/
structure CleanupLeftTailIdle
    (u : AuthorizedAgentState psi) : Prop where
  state_none : u.core.state = .none
  path_bot : u.core.path = .bot
  p_carry_false : u.core.p_carry = false
  permit_false : u.path0Crossed = false

/-- The responder is never the source of DISAPPEAR's carry, so its exact idle
contract needs only CHECK's state/path fields and the normalized permit. -/
structure CleanupRightTailIdle
    (u : AuthorizedAgentState psi) : Prop where
  state_none : u.core.state = .none
  path_bot : u.core.path = .bot
  permit_false : u.path0Crossed = false

private theorem authorizedCheckSig_eq_of_cleanup_idle
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hL : CleanupLeftTailIdle l)
    (hR : CleanupRightTailIdle r) :
    authorizedCheckSig hpsi l r = (l, r) := by
  rcases hL with ⟨hLs, hLp, _hLCarry, hpL⟩
  rcases hR with ⟨hRs, hRp, hpR⟩
  simp [authorizedCheckSig, authorizedReconcile, checkSig,
    checkSigSetReady, checkSigCheckL, checkSigCheckR,
    checkSigSetResult, checkSigSetLeader,
    reconcilePermit, normalizePermit,
    hLs, hLp, hRs, hRp]
  constructor
  · cases l
    simp_all
  · cases r
    simp_all

private theorem authorizedDisappear_eq_of_cleanup_idle
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hL : CleanupLeftTailIdle l)
    (hR : CleanupRightTailIdle r) :
    authorizedDisappear hpsi l r = (l, r) := by
  rcases hL with ⟨hLs, hLp, hLCarry, hpL⟩
  rcases hR with ⟨hRs, hRp, hpR⟩
  simp [authorizedDisappear, authorizedReconcile, disappear,
    reconcilePermit, normalizePermit,
    hLs, hLp, hLCarry, hRs, hRp]
  constructor
  · cases l
    simp_all
  · cases r
    simp_all

private theorem authorizedCompareSigActionOne_eq_of_cleanup_idle
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hL : CleanupLeftTailIdle l) :
    authorizedCompareSigActionOne hpsi l r = (l, r) := by
  rcases hL with ⟨hLs, hLp, _hLCarry, hpL⟩
  simp [authorizedCompareSigActionOne, compareSigInit,
    normalizePermit, hLs, hLp]
  cases l with
  | mk core permit =>
      cases core
      simp_all

/-! ## Prefix frames -/

private theorem pPsiLeaderResetProbeWall_peaceViewPair_of_route
    (hpsi : psi > 0) (l r : AgentState psi)
    (hroute : r.leader = true ∨
      r.label =
        ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) :
    peaceViewPair (pPsiLeaderResetProbeWall hpsi l r) =
      peaceViewPair (l, r) := by
  let l0 := if l.leader = true then { l with probe := false } else l
  let r0 := if r.leader = true ∨ l.leader = true ∨
      l.reset_cmd = true then
    { r with probe := false }
  else r
  have hleftLeader :
      (pPsiLeaderResetProbeWall hpsi l r).1.leader = l.leader := by
    change (pPsi hpsi l0 r0).1.leader = l.leader
    exact (PPLLVerify.pPsi_initiator_leader_eq hpsi l0 r0).trans (by
      unfold l0
      split <;> rfl)
  have hleftLabel :
      (pPsiLeaderResetProbeWall hpsi l r).1.label = l.label := by
    change (pPsi hpsi l0 r0).1.label = l.label
    exact (PPLLVerify.pPsi_initiator_label_eq hpsi l0 r0).trans (by
      unfold l0
      split <;> rfl)
  have hrightLeader :
      (pPsiLeaderResetProbeWall hpsi l r).2.leader = r.leader := by
    rcases hroute with hLeader | hAligned
    · simp [pPsiLeaderResetProbeWall, pPsi, hLeader]
    · simp [pPsiLeaderResetProbeWall, pPsi, hAligned]
  have hrightLabel :
      (pPsiLeaderResetProbeWall hpsi l r).2.label = r.label := by
    rcases hroute with hLeader | hAligned
    · simp [pPsiLeaderResetProbeWall, pPsi, hLeader]
    · simp [pPsiLeaderResetProbeWall, pPsi, hAligned]
  exact PPLLWallSweepNormalResetContract.peaceViewPair_eq_of_frames
    (Prod.ext hleftLeader hrightLeader)
    (Prod.ext hleftLabel hrightLabel)
    (pPsiLeaderResetProbeWall_bulletFieldPair hpsi l r)

private theorem authorizedPPsiLeaderResetProbeWall_peaceViewPair_of_route
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (hroute : r.core.leader = true ∨
      r.core.label =
        ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) :
    authorizedPeaceViewPair
        (authorizedPPsiLeaderResetProbeWall hpsi l r) =
      authorizedPeaceViewPair (l, r) := by
  have hcore := authorizedPPsiLeaderResetProbeWall_core hpsi l r
  exact (congrArg peaceViewPair hcore).trans
    (pPsiLeaderResetProbeWall_peaceViewPair_of_route
      hpsi l.core r.core hroute)

private theorem authorizedGenSig_peaceViewPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (authorizedGenSig hpsi kappa l r) =
      authorizedPeaceViewPair (l, r) := by
  have hleaders := genSigSaturated_leaders
    hpsi kappa l.core r.core
  have hlabels := genSigSaturated_labels
    hpsi kappa l.core r.core
  have hbullets := genSigSaturated_bulletFieldPair
    hpsi kappa l.core r.core
  apply Prod.ext <;> apply PeaceView.ext
  · exact congrArg Prod.fst hleaders
  · exact congrArg Prod.fst hlabels
  · exact congrArg (fun q => q.1.shield) hbullets
  · exact congrArg (fun q => q.1.bullet) hbullets
  · exact congrArg (fun q => q.1.signal_B) hbullets
  · exact congrArg Prod.snd hleaders
  · exact congrArg Prod.snd hlabels
  · exact congrArg (fun q => q.2.shield) hbullets
  · exact congrArg (fun q => q.2.bullet) hbullets
  · exact congrArg (fun q => q.2.signal_B) hbullets

private theorem authorizedCleanSig_peaceViewPair
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (authorizedCleanSig hpsi l r) =
      authorizedPeaceViewPair (l, r) := by
  have hleaders := PPLLVerify.cleanSig_leaders_eq
    hpsi l.core r.core
  have hlabels := PPLLVerify.cleanSig_labels_eq
    hpsi l.core r.core
  have hbullets := cleanSig_bulletFieldPair
    hpsi l.core r.core
  apply Prod.ext <;> apply PeaceView.ext
  · exact hleaders.1
  · exact hlabels.1
  · exact congrArg (fun q => q.1.shield) hbullets
  · exact congrArg (fun q => q.1.bullet) hbullets
  · exact congrArg (fun q => q.1.signal_B) hbullets
  · exact hleaders.2
  · exact hlabels.2
  · exact congrArg (fun q => q.2.shield) hbullets
  · exact congrArg (fun q => q.2.bullet) hbullets
  · exact congrArg (fun q => q.2.signal_B) hbullets

private theorem authorizedEliminateSig_peaceViewPair
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (authorizedEliminateSig hpsi l r) =
      authorizedPeaceViewPair (l, r) := by
  have hleaders := PPLLVerify.eliminateSig_leaders_eq
    hpsi l.core r.core
  have hlabels := PPLLVerify.eliminateSig_labels_eq
    hpsi l.core r.core
  have hbullets := eliminateSig_bulletFieldPair
    hpsi l.core r.core
  apply Prod.ext <;> apply PeaceView.ext
  · exact hleaders.1
  · exact hlabels.1
  · exact congrArg (fun q => q.1.shield) hbullets
  · exact congrArg (fun q => q.1.bullet) hbullets
  · exact congrArg (fun q => q.1.signal_B) hbullets
  · exact hleaders.2
  · exact hlabels.2
  · exact congrArg (fun q => q.2.shield) hbullets
  · exact congrArg (fun q => q.2.bullet) hbullets
  · exact congrArg (fun q => q.2.signal_B) hbullets

private theorem authorizedSigMoveLeaderWall_peaceViewPair
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (authorizedSigMoveLeaderWall hpsi l r) =
      authorizedPeaceViewPair (l, r) := by
  have hcore := authorizedSigMoveLeaderWall_core hpsi l r
  have hleaders := sigMoveLeaderWall_leaders_eq
    hpsi l.core r.core
  have hlabels := sigMoveLeaderWall_labels_eq
    hpsi l.core r.core
  have hbullets := sigMoveLeaderWall_bulletFieldPair
    hpsi l.core r.core
  have hraw : peaceViewPair
      (sigMoveLeaderWall hpsi l.core r.core) =
      peaceViewPair (l.core, r.core) := by
    apply Prod.ext <;> apply PeaceView.ext
    · exact hleaders.1
    · exact hlabels.1
    · exact congrArg (fun q => q.1.shield) hbullets
    · exact congrArg (fun q => q.1.bullet) hbullets
    · exact congrArg (fun q => q.1.signal_B) hbullets
    · exact hleaders.2
    · exact hlabels.2
    · exact congrArg (fun q => q.2.shield) hbullets
    · exact congrArg (fun q => q.2.bullet) hbullets
    · exact congrArg (fun q => q.2.signal_B) hbullets
  exact (congrArg peaceViewPair hcore).trans hraw

private theorem wallSweepResetProbeAuthorizedBeforeCheck_peaceViewPair_of_route
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hroute : r.core.leader = true ∨
      r.core.label =
        ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) :
    authorizedPeaceViewPair
        (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r) =
      authorizedPeaceViewPair (l, r) := by
  let q0 := authorizedPPsiLeaderResetProbeWall hpsi l r
  let q1 := authorizedGenSig hpsi kappa q0.1 q0.2
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  let q3 := authorizedEliminateSig hpsi q2.1 q2.2
  have h0 := authorizedPPsiLeaderResetProbeWall_peaceViewPair_of_route
    hpsi l r hroute
  have h1 := authorizedGenSig_peaceViewPair
    hpsi kappa q0.1 q0.2
  have h2 := authorizedCleanSig_peaceViewPair
    hpsi q1.1 q1.2
  have h3 := authorizedEliminateSig_peaceViewPair
    hpsi q2.1 q2.2
  have h4 := authorizedSigMoveLeaderWall_peaceViewPair
    hpsi q3.1 q3.2
  change authorizedPeaceViewPair
    (authorizedSigMoveLeaderWall hpsi q3.1 q3.2) =
      authorizedPeaceViewPair (l, r)
  exact h4.trans (h3.trans (h2.trans (h1.trans h0)))

private theorem sanitizeAuthorizedPair_peaceViewPair
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedPeaceViewPair (sanitizeAuthorizedPair hpsi q) =
      authorizedPeaceViewPair q := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold sanitizeAuthorizedPair sanitizeAuthorizedTerminalEqual
      authorizedPeaceViewPair peaceViewPair PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem normalizeDeletionPair_peaceViewPair
    (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (normalizeDeletion l, normalizeDeletion r) =
      authorizedPeaceViewPair (l, r) :=
  Prod.ext (normalizeDeletion_peaceView l)
    (normalizeDeletion_peaceView r)

set_option maxHeartbeats 2000000 in
private theorem wallSweepResetProbePreCheckResetBeforeCheck_peaceViewPair_of_route
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hroute : r.core.leader = true ∨
      r.core.label =
        ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) :
    authorizedPeaceViewPair
        (wallSweepResetProbePreCheckResetBeforeCheck
          hpsi kappa l r) =
      authorizedPeaceViewPair (l, r) := by
  let q0 := wallSweepResetProbeAuthorizedBeforeCheck
    hpsi kappa l r
  let qR := preCheckResetWall q0.1 q0.2
  have h0 :=
    wallSweepResetProbeAuthorizedBeforeCheck_peaceViewPair_of_route
      hpsi kappa l r hroute
  have hR := preCheckResetWall_peaceViewPair q0.1 q0.2
  have h1 := sanitizeAuthorizedPair_peaceViewPair hpsi qR
  change authorizedPeaceViewPair (sanitizeAuthorizedPair hpsi qR) =
    authorizedPeaceViewPair (l, r)
  exact h1.trans (hR.trans h0)

/-! ## The egress-sink kernel descends to the five-field quotient -/

private def cleanupCanon (u : AgentState psi) : AgentState psi :=
  PeaceView.toState (PeaceView.ofState u)

private theorem cleanupFire_canon
    (hpsi : psi > 0) (l r : AgentState psi) :
    peaceViewPair
        (eliminateLeadersNoCollisionFire
          hpsi (cleanupCanon l) (cleanupCanon r)) =
      peaceViewPair (eliminateLeadersNoCollisionFire hpsi l r) := by
  by_cases hl : l.leader = true ∧
      l.signal_B = ⟨1, by omega⟩
  · have hlc : (cleanupCanon l).leader = true ∧
        (cleanupCanon l).signal_B = ⟨1, by omega⟩ := hl
    by_cases hr : r.leader = true ∧
        r.signal_B = ⟨1, by omega⟩
    · have hrc : (cleanupCanon r).leader = true ∧
          (cleanupCanon r).signal_B = ⟨1, by omega⟩ := hr
      unfold eliminateLeadersNoCollisionFire
      rw [if_pos hlc, if_pos hrc, if_pos hl, if_pos hr]
      rfl
    · have hrc : ¬((cleanupCanon r).leader = true ∧
          (cleanupCanon r).signal_B = ⟨1, by omega⟩) := hr
      unfold eliminateLeadersNoCollisionFire
      rw [if_pos hlc, if_neg hrc, if_pos hl, if_neg hr]
      rfl
  · have hlc : ¬((cleanupCanon l).leader = true ∧
        (cleanupCanon l).signal_B = ⟨1, by omega⟩) := hl
    by_cases hr : r.leader = true ∧
        r.signal_B = ⟨1, by omega⟩
    · have hrc : (cleanupCanon r).leader = true ∧
          (cleanupCanon r).signal_B = ⟨1, by omega⟩ := hr
      unfold eliminateLeadersNoCollisionFire
      rw [if_neg hlc, if_pos hrc, if_neg hl, if_pos hr]
      rfl
    · have hrc : ¬((cleanupCanon r).leader = true ∧
          (cleanupCanon r).signal_B = ⟨1, by omega⟩) := hr
      unfold eliminateLeadersNoCollisionFire
      rw [if_neg hlc, if_neg hrc, if_neg hl, if_neg hr]
      rfl

private theorem cleanupEgressMove_canon
    (hpsi : psi > 0) (next : Fin psi)
    (l r : AgentState psi) :
    peaceViewPair
        (eliminateLeadersNoCollisionZeroLeaderEgressMove
          hpsi next (cleanupCanon l) (cleanupCanon r)) =
      peaceViewPair
        (eliminateLeadersNoCollisionZeroLeaderEgressMove
          hpsi next l r) := by
  by_cases h1 : r.bullet.val > 0 ∧ l.leader = true
  · by_cases hkill : r.bullet = ⟨2, by omega⟩ ∧
        l.shield = false
    · simp [eliminateLeadersNoCollisionZeroLeaderEgressMove,
        cleanupCanon, PeaceView.toState, PeaceView.ofState,
        peaceViewPair, h1, hkill]
    · simp [eliminateLeadersNoCollisionZeroLeaderEgressMove,
        cleanupCanon, PeaceView.toState, PeaceView.ofState,
        peaceViewPair, h1, hkill]
  · by_cases h2 : r.bullet.val > 0 ∧ l.leader = false
    · by_cases hroute : r.label = next ∨
          (r.leader = true ∧ r.label = ⟨0, hpsi⟩)
      · simp [eliminateLeadersNoCollisionZeroLeaderEgressMove,
          cleanupCanon, PeaceView.toState, PeaceView.ofState,
          peaceViewPair, h1, h2, hroute]
      · simp [eliminateLeadersNoCollisionZeroLeaderEgressMove,
          cleanupCanon, PeaceView.toState, PeaceView.ofState,
          peaceViewPair, h1, h2, hroute]
    · simp [eliminateLeadersNoCollisionZeroLeaderEgressMove,
        cleanupCanon, PeaceView.toState, PeaceView.ofState,
        peaceViewPair, h1, h2]

private theorem cleanupLeaderSinkSignal_canon
    (next : Fin psi) (l r : AgentState psi) :
    peaceViewPair
        (eliminateLeadersNoCollisionSignalLeaderSink
          next (cleanupCanon l) (cleanupCanon r)) =
      peaceViewPair
        (eliminateLeadersNoCollisionSignalLeaderSink next l r) := by
  by_cases hcond : r.label = next ∨
      l.leader = true ∨ r.leader = true
  · by_cases hb : r.bullet = ⟨2, by omega⟩
    · simp [eliminateLeadersNoCollisionSignalLeaderSink,
        cleanupCanon, PeaceView.toState, PeaceView.ofState,
        peaceViewPair, hcond, hb]
    · by_cases hl : l.leader = true
      · simp [eliminateLeadersNoCollisionSignalLeaderSink,
          cleanupCanon, PeaceView.toState, PeaceView.ofState,
          peaceViewPair, hcond, hb, hl]
      · simp [eliminateLeadersNoCollisionSignalLeaderSink,
          cleanupCanon, PeaceView.toState, PeaceView.ofState,
          peaceViewPair, hcond, hb, hl]
  · simp [eliminateLeadersNoCollisionSignalLeaderSink,
      cleanupCanon, PeaceView.toState, PeaceView.ofState,
      peaceViewPair, hcond]

private theorem cleanupDummySink_canon
    (q : AgentState psi × AgentState psi) :
    peaceViewPair
        (dummyBulletSink (cleanupCanon q.1, cleanupCanon q.2)) =
      peaceViewPair (dummyBulletSink q) := by
  by_cases hcond : q.1.leader = true ∧
      q.2.leader = false ∧ q.2.bullet = ⟨1, by omega⟩
  · have hcanon : (cleanupCanon q.1).leader = true ∧
        (cleanupCanon q.2).leader = false ∧
        (cleanupCanon q.2).bullet = ⟨1, by omega⟩ := hcond
    unfold dummyBulletSink
    rw [if_pos hcanon, if_pos hcond]
    rfl
  · have hcanon : ¬((cleanupCanon q.1).leader = true ∧
        (cleanupCanon q.2).leader = false ∧
        (cleanupCanon q.2).bullet = ⟨1, by omega⟩) := hcond
    unfold dummyBulletSink
    rw [if_neg hcanon, if_neg hcond]
    rfl

private theorem cleanupFire_congr
    (hpsi : psi > 0) (l r l' r' : AgentState psi)
    (hL : PeaceView.ofState l = PeaceView.ofState l')
    (hR : PeaceView.ofState r = PeaceView.ofState r') :
    peaceViewPair (eliminateLeadersNoCollisionFire hpsi l r) =
      peaceViewPair
        (eliminateLeadersNoCollisionFire hpsi l' r') := by
  have hcL : cleanupCanon l = cleanupCanon l' :=
    congrArg PeaceView.toState hL
  have hcR : cleanupCanon r = cleanupCanon r' :=
    congrArg PeaceView.toState hR
  have hc : peaceViewPair
      (eliminateLeadersNoCollisionFire hpsi
        (cleanupCanon l) (cleanupCanon r)) =
      peaceViewPair
        (eliminateLeadersNoCollisionFire hpsi
          (cleanupCanon l') (cleanupCanon r')) := by
    rw [hcL, hcR]
  exact (cleanupFire_canon hpsi l r).symm.trans
    (hc.trans (cleanupFire_canon hpsi l' r'))

private theorem cleanupEgressMove_congr
    (hpsi : psi > 0) (next next' : Fin psi)
    (l r l' r' : AgentState psi)
    (hnext : next = next')
    (hL : PeaceView.ofState l = PeaceView.ofState l')
    (hR : PeaceView.ofState r = PeaceView.ofState r') :
    peaceViewPair
        (eliminateLeadersNoCollisionZeroLeaderEgressMove
          hpsi next l r) =
      peaceViewPair
        (eliminateLeadersNoCollisionZeroLeaderEgressMove
          hpsi next' l' r') := by
  have hcL : cleanupCanon l = cleanupCanon l' :=
    congrArg PeaceView.toState hL
  have hcR : cleanupCanon r = cleanupCanon r' :=
    congrArg PeaceView.toState hR
  have hc : peaceViewPair
      (eliminateLeadersNoCollisionZeroLeaderEgressMove hpsi next
        (cleanupCanon l) (cleanupCanon r)) =
      peaceViewPair
        (eliminateLeadersNoCollisionZeroLeaderEgressMove hpsi next'
          (cleanupCanon l') (cleanupCanon r')) := by
    rw [hnext, hcL, hcR]
  exact (cleanupEgressMove_canon hpsi next l r).symm.trans
    (hc.trans (cleanupEgressMove_canon hpsi next' l' r'))

private theorem cleanupLeaderSinkSignal_congr
    (next next' : Fin psi) (l r l' r' : AgentState psi)
    (hnext : next = next')
    (hL : PeaceView.ofState l = PeaceView.ofState l')
    (hR : PeaceView.ofState r = PeaceView.ofState r') :
    peaceViewPair
        (eliminateLeadersNoCollisionSignalLeaderSink next l r) =
      peaceViewPair
        (eliminateLeadersNoCollisionSignalLeaderSink next' l' r') := by
  have hcL : cleanupCanon l = cleanupCanon l' :=
    congrArg PeaceView.toState hL
  have hcR : cleanupCanon r = cleanupCanon r' :=
    congrArg PeaceView.toState hR
  have hc : peaceViewPair
      (eliminateLeadersNoCollisionSignalLeaderSink next
        (cleanupCanon l) (cleanupCanon r)) =
      peaceViewPair
        (eliminateLeadersNoCollisionSignalLeaderSink next'
          (cleanupCanon l') (cleanupCanon r')) := by
    rw [hnext, hcL, hcR]
  exact (cleanupLeaderSinkSignal_canon next l r).symm.trans
    (hc.trans (cleanupLeaderSinkSignal_canon next' l' r'))

private theorem cleanupDummySink_congr
    (q q' : AgentState psi × AgentState psi)
    (h : peaceViewPair q = peaceViewPair q') :
    peaceViewPair (dummyBulletSink q) =
      peaceViewPair (dummyBulletSink q') := by
  have hcL : cleanupCanon q.1 = cleanupCanon q'.1 :=
    congrArg PeaceView.toState (congrArg Prod.fst h)
  have hcR : cleanupCanon q.2 = cleanupCanon q'.2 :=
    congrArg PeaceView.toState (congrArg Prod.snd h)
  have hc : peaceViewPair
      (dummyBulletSink (cleanupCanon q.1, cleanupCanon q.2)) =
      peaceViewPair
        (dummyBulletSink (cleanupCanon q'.1, cleanupCanon q'.2)) := by
    rw [hcL, hcR]
  exact (cleanupDummySink_canon q).symm.trans
    (hc.trans (cleanupDummySink_canon q'))

private theorem eliminateLeadersNoCollisionEgressSink_peaceView_congr
    (hpsi : psi > 0)
    (l r l' r' : AgentState psi)
    (hL : PeaceView.ofState l = PeaceView.ofState l')
    (hR : PeaceView.ofState r = PeaceView.ofState r') :
    peaceViewPair (eliminateLeadersNoCollisionEgressSink hpsi l r) =
      peaceViewPair
        (eliminateLeadersNoCollisionEgressSink hpsi l' r') := by
  let next : Fin psi :=
    ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  let next' : Fin psi :=
    ⟨(l'.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  let q0 := eliminateLeadersNoCollisionFire hpsi l r
  let q0' := eliminateLeadersNoCollisionFire hpsi l' r'
  let q1 := eliminateLeadersNoCollisionZeroLeaderEgressMove
    hpsi next q0.1 q0.2
  let q1' := eliminateLeadersNoCollisionZeroLeaderEgressMove
    hpsi next' q0'.1 q0'.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink
    next q1.1 q1.2
  let q2' := eliminateLeadersNoCollisionSignalLeaderSink
    next' q1'.1 q1'.2
  have hlabel := congrArg PeaceView.label hL
  unfold PeaceView.ofState at hlabel
  dsimp only at hlabel
  have hnext : next = next' := by
    apply Fin.ext
    simp [next, next', hlabel]
  have h0 := cleanupFire_congr hpsi l r l' r' hL hR
  have h1 := cleanupEgressMove_congr hpsi next next'
    q0.1 q0.2 q0'.1 q0'.2 hnext
      (congrArg Prod.fst h0) (congrArg Prod.snd h0)
  have h2 := cleanupLeaderSinkSignal_congr next next'
    q1.1 q1.2 q1'.1 q1'.2 hnext
      (congrArg Prod.fst h1) (congrArg Prod.snd h1)
  have h3 := cleanupDummySink_congr q2 q2' h2
  simpa [eliminateLeadersNoCollisionEgressSink,
    next, next', q0, q0', q1, q1', q2, q2'] using h3

private theorem eliminateLeadersNoCollisionEgressSink_cleanupPhysicalView_congr
    (hpsi : psi > 0)
    (l r l' r' : AgentState psi)
    (hL : cleanupPhysicalViewOfState l = cleanupPhysicalViewOfState l')
    (hR : cleanupPhysicalViewOfState r = cleanupPhysicalViewOfState r') :
    cleanupPhysicalViewPair
        (eliminateLeadersNoCollisionEgressSink hpsi l r) =
      cleanupPhysicalViewPair
        (eliminateLeadersNoCollisionEgressSink hpsi l' r') := by
  apply cleanupPhysicalViewPair_eq_of_peaceViewPair_eq
  exact eliminateLeadersNoCollisionEgressSink_peaceView_congr
    hpsi l r l' r'
      (peaceView_eq_of_cleanupPhysicalView_eq hL)
      (peaceView_eq_of_cleanupPhysicalView_eq hR)

private theorem eliminateLeadersNoCollisionEgressSink_responder_frame
    (hpsi : psi > 0) (l r : AgentState psi) :
    let q := eliminateLeadersNoCollisionEgressSink hpsi l r
    q.2.leader = r.leader ∧ q.2.label = r.label := by
  let next : Fin psi :=
    ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  let q0 := eliminateLeadersNoCollisionFire hpsi l r
  let q1 := eliminateLeadersNoCollisionZeroLeaderEgressMove
    hpsi next q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink
    next q1.1 q1.2
  have h0Leader : q0.2.leader = r.leader := by
    unfold q0 eliminateLeadersNoCollisionFire
    repeat (first | rfl | split)
  have h0Label : q0.2.label = r.label := by
    unfold q0 eliminateLeadersNoCollisionFire
    repeat (first | rfl | split)
  have h1Leader : q1.2.leader = q0.2.leader := by
    unfold q1 eliminateLeadersNoCollisionZeroLeaderEgressMove
    repeat (first | rfl | split)
  have h1Label : q1.2.label = q0.2.label := by
    unfold q1 eliminateLeadersNoCollisionZeroLeaderEgressMove
    repeat (first | rfl | split)
  have h2Leader : q2.2.leader = q1.2.leader := by
    unfold q2 eliminateLeadersNoCollisionSignalLeaderSink
    repeat (first | rfl | split)
  have h2Label : q2.2.label = q1.2.label := by
    unfold q2 eliminateLeadersNoCollisionSignalLeaderSink
    repeat (first | rfl | split)
  have h3Leader : (dummyBulletSink q2).2.leader = q2.2.leader := by
    unfold dummyBulletSink
    repeat (first | rfl | split)
  have h3Label : (dummyBulletSink q2).2.label = q2.2.label := by
    unfold dummyBulletSink
    repeat (first | rfl | split)
  change (dummyBulletSink q2).2.leader = r.leader ∧
    (dummyBulletSink q2).2.label = r.label
  exact ⟨h3Leader.trans (h2Leader.trans (h1Leader.trans h0Leader)),
    h3Label.trans (h2Label.trans (h1Label.trans h0Label))⟩
end PhysicalBridge
end PPLLCompleteMultiLeaderCleanup
