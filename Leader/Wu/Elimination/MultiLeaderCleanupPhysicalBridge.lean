import Leader.Wu.Elimination.MultiLeaderCleanup
import Leader.Wu.WallSweep.NormalResetContract
import Leader.Wu.Safety.NoCheckBirthConditionTwoProtocol
import Leader.Wu.WallSweep.RestartableGeneric
import Leader.Wu.Scheduler.RepeatedBlocks

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

/-- Raw erasure local to this bridge. -/
def eraseExpiringCleanupConfig
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    Fin n → AgentState psi :=
  fun i => (C i).core.erase.core

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

theorem authorizedCheckSig_pair_eq_of_cleanup_idle
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hL : CleanupLeftTailIdle q.1)
    (hR : CleanupRightTailIdle q.2) :
    authorizedCheckSig hpsi q.1 q.2 = q := by
  have h := authorizedCheckSig_eq_of_cleanup_idle
    hpsi q.1 q.2 hL hR
  cases q
  exact h

theorem authorizedDisappear_eq_of_cleanup_idle
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

theorem authorizedCompareSigActionOne_eq_of_cleanup_idle
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

theorem authorizedGenSig_peaceViewPair
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

theorem authorizedCleanSig_peaceViewPair
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

theorem authorizedEliminateSig_peaceViewPair
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

theorem authorizedSigMoveLeaderWall_peaceViewPair
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

theorem sanitizeAuthorizedPair_peaceViewPair
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

/-- The pre after the reset-aware P-prime wall preserves that wall's
five-field view, independently of whether the responder is already aligned. -/
theorem wallSweepResetProbePreCheckResetBeforeCheck_peaceViewPair_eq_probe
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair
        (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r) =
      authorizedPeaceViewPair
        (authorizedPPsiLeaderResetProbeWall hpsi l r) := by
  let q0 := authorizedPPsiLeaderResetProbeWall hpsi l r
  let q1 := authorizedGenSig hpsi kappa q0.1 q0.2
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  let q3 := authorizedEliminateSig hpsi q2.1 q2.2
  let q4 := authorizedSigMoveLeaderWall hpsi q3.1 q3.2
  let qR := preCheckResetWall q4.1 q4.2
  change authorizedPeaceViewPair (sanitizeAuthorizedPair hpsi qR) =
    authorizedPeaceViewPair q0
  rw [sanitizeAuthorizedPair_peaceViewPair,
    preCheckResetWall_peaceViewPair,
    authorizedSigMoveLeaderWall_peaceViewPair,
    authorizedEliminateSig_peaceViewPair,
    authorizedCleanSig_peaceViewPair,
    authorizedGenSig_peaceViewPair]

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

theorem eliminateLeadersNoCollisionEgressSink_peaceView_congr
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

/-! ## Suffix frames -/

theorem markLeaderBirth_peaceViewPair
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedPeaceViewPair (markLeaderBirth born q) =
      authorizedPeaceViewPair q := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold markLeaderBirth markComparisonForDeletion
      authorizedPeaceViewPair peaceViewPair PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem authorizedReconcile_peaceViewPair
    (f : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (authorizedReconcile f l r) =
      peaceViewPair (f l.core r.core) := by
  rfl

private theorem peaceViewPair_eq_of_leader_label_bulletFields
    (q q' : AgentState psi × AgentState psi)
    (hleaders : q.1.leader = q'.1.leader ∧ q.2.leader = q'.2.leader)
    (hlabels : q.1.label = q'.1.label ∧ q.2.label = q'.2.label)
    (hbullets : bulletFieldPair q = bulletFieldPair q') :
    peaceViewPair q = peaceViewPair q' := by
  have hleft := congrArg Prod.fst hbullets
  have hright := congrArg Prod.snd hbullets
  apply Prod.ext
  · apply PeaceView.ext _ _ hleaders.1 hlabels.1
    · exact congrArg BulletFields.shield hleft
    · exact congrArg BulletFields.bullet hleft
    · exact congrArg BulletFields.signal_B hleft
  · apply PeaceView.ext _ _ hleaders.2 hlabels.2
    · exact congrArg BulletFields.shield hright
    · exact congrArg BulletFields.bullet hright
    · exact congrArg BulletFields.signal_B hright

private theorem writeSeqIncrementGate_peaceViewPair_of_responder_zero
    (hpsi : psi > 0) (l r : AgentState psi)
    (hzero : r.leader = true → r.label = ⟨0, hpsi⟩) :
    peaceViewPair (writeSeqIncrementGate hpsi l r) =
      peaceViewPair (l, r) := by
  have hleaders :
      (writeSeqIncrementGate hpsi l r).1.leader = l.leader ∧
        (writeSeqIncrementGate hpsi l r).2.leader = r.leader :=
    writeSeqIncrementGate_leaders_of_responder_zero hpsi l r hzero
  have hlabels :
      (writeSeqIncrementGate hpsi l r).1.label = l.label ∧
        (writeSeqIncrementGate hpsi l r).2.label = r.label :=
    writeSeqIncrementGate_labels hpsi l r
  have hbullets :
      bulletFieldPair (writeSeqIncrementGate hpsi l r) =
        bulletFieldPair (l, r) :=
    writeSeqIncrementGate_bulletFieldPair hpsi l r
  exact peaceViewPair_eq_of_leader_label_bulletFields
    (writeSeqIncrementGate hpsi l r) (l, r) hleaders hlabels hbullets

/-! ## 3. Minimal authorized-pair contract and exact quotient theorem -/

/-- The reset/P-prime route is either an aligned follower edge or an edge whose
responder is already a leader.  The latter disjunct is what handles the two
leader-closing edges; no closing-label alignment is assumed.  The explicit idle
fields are exactly those consumed by CHECK, DISAPPEAR, and action-one COMPARE.
SUPPRESS and the reset wall are unconditional five-field frames.  Gated WRITE
needs only the final `responder_zero` implication. -/
structure MultiLeaderCleanupPhysicalPairReady
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : Prop where
  priority_open : AuthorizedPriorityOpen l r
  reset_ppsi_route :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    r0.core.leader = true ∨
      r0.core.label =
        ⟨(l0.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  left_idle :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let before := wallSweepResetProbePreCheckResetBeforeCheck
      hpsi kappa l0 r0
    CleanupLeftTailIdle before.1
  right_idle :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let before := wallSweepResetProbePreCheckResetBeforeCheck
      hpsi kappa l0 r0
    CleanupRightTailIdle before.2
  responder_zero :
    r.core.leader = true → r.core.label = ⟨0, hpsi⟩

theorem multiLeaderCleanupAuthorizedTransition_of_priority_open
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    multiLeaderCleanupAuthorizedTransition hpsi kappa l r =
      let l0 := normalizeDeletion l
      let r0 := normalizeDeletion r
      let before := wallSweepResetProbePreCheckResetBeforeCheck
        hpsi kappa l0 r0
      let after := wallSweepResetProbePreCheckResetAfterCheck
        hpsi kappa l0 r0
      let born := leaderBirthBeforeOrAtCheck
        l0 r0 before after
      markLeaderBirth born
        (multiLeaderAfterCheckSuffix hpsi after.1 after.2) := by
  have h := hopen
  change deletionActive (normalizeDeletion l) = false ∧
    deletionActive (normalizeDeletion r) = false at h
  simp [multiLeaderCleanupAuthorizedTransition, h.1, h.2]

private theorem multiLeaderCleanup_beforeCheck_view
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hready : MultiLeaderCleanupPhysicalPairReady hpsi kappa l r) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let before := wallSweepResetProbePreCheckResetBeforeCheck
      hpsi kappa l0 r0
    authorizedPeaceViewPair before = authorizedPeaceViewPair (l, r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let before := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  have hroute := hready.reset_ppsi_route
  change r0.core.leader = true ∨
    r0.core.label =
      ⟨(l0.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ at hroute
  have hbefore0 :=
    wallSweepResetProbePreCheckResetBeforeCheck_peaceViewPair_of_route
      hpsi kappa l0 r0 hroute
  exact hbefore0.trans (normalizeDeletionPair_peaceViewPair l r)

theorem cleanupIdleTail_suppress_peaceView
    (hpsi : psi > 0)
    (before after : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hafter : after = before)
    (hIdleL : CleanupLeftTailIdle before.1)
    (hIdleR : CleanupRightTailIdle before.2) :
    let q0 := authorizedDisappear hpsi after.1 after.2
    let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
    let q2 := authorizedReconcile
      (suppressSigResetKill hpsi) q1.1 q1.2
    authorizedPeaceViewPair q2 = authorizedPeaceViewPair before := by
  let q0 := authorizedDisappear hpsi after.1 after.2
  have hq0 : q0 = before := by
    change authorizedDisappear hpsi after.1 after.2 = before
    rw [hafter]
    exact authorizedDisappear_eq_of_cleanup_idle
      hpsi before.1 before.2 hIdleL hIdleR
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  have hq1 : q1 = before := by
    change authorizedCompareSigActionOne hpsi q0.1 q0.2 = before
    rw [hq0]
    exact authorizedCompareSigActionOne_eq_of_cleanup_idle
      hpsi before.1 before.2 hIdleL
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  change authorizedPeaceViewPair
    (authorizedReconcile
      (suppressSigResetKill hpsi) q1.1 q1.2) = _
  exact (authorizedSuppressSigResetKill_peaceViewPair
    hpsi q1.1 q1.2).trans (by rw [hq1])

theorem cleanupKernelWrite_peaceView
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (q2 : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hq2view : authorizedPeaceViewPair q2 =
      authorizedPeaceViewPair (l, r))
    (hzero : r.core.leader = true →
      r.core.label = ⟨0, hpsi⟩) :
    let q3 := authorizedReconcile
      (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
    let q4 := authorizedReconcile
      (writeSeqIncrementGate hpsi) q3.1 q3.2
    authorizedPeaceViewPair q4 =
      peaceViewPair
        (eliminateLeadersNoCollisionEgressSink hpsi l.core r.core) := by
  let k := eliminateLeadersNoCollisionEgressSink
    hpsi q2.1.core q2.2.core
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  have hq3core : (q3.1.core, q3.2.core) = k := rfl
  have hq3view : authorizedPeaceViewPair q3 = peaceViewPair k :=
    authorizedReconcile_peaceViewPair
      (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  have hkOriginal : peaceViewPair k =
      peaceViewPair
        (eliminateLeadersNoCollisionEgressSink hpsi l.core r.core) :=
    eliminateLeadersNoCollisionEgressSink_peaceView_congr
      hpsi q2.1.core q2.2.core l.core r.core
        (congrArg Prod.fst hq2view)
        (congrArg Prod.snd hq2view)
  have hkFrame :=
    eliminateLeadersNoCollisionEgressSink_responder_frame
      hpsi q2.1.core q2.2.core
  have hq2R := congrArg Prod.snd hq2view
  have hkZero : k.2.leader = true → k.2.label = ⟨0, hpsi⟩ := by
    intro hkLeader
    have hq2Leader : q2.2.core.leader = true :=
      hkFrame.1.symm.trans hkLeader
    have hrLeader : r.core.leader = true :=
      (congrArg PeaceView.leader hq2R).symm.trans hq2Leader
    exact hkFrame.2.trans
      ((congrArg PeaceView.label hq2R).trans (hzero hrLeader))
  have hq3Zero :
      q3.2.core.leader = true → q3.2.core.label = ⟨0, hpsi⟩ := by
    have hq3R := congrArg Prod.snd hq3core
    intro hleader
    have hkLeader : k.2.leader = true :=
      (congrArg AgentState.leader hq3R).symm.trans hleader
    exact (congrArg AgentState.label hq3R).trans (hkZero hkLeader)
  let q4 := authorizedReconcile
    (writeSeqIncrementGate hpsi) q3.1 q3.2
  have hq4view : authorizedPeaceViewPair q4 =
      authorizedPeaceViewPair q3 := by
    exact (authorizedReconcile_peaceViewPair
      (writeSeqIncrementGate hpsi) q3.1 q3.2).trans
      (writeSeqIncrementGate_peaceViewPair_of_responder_zero
        hpsi q3.1.core q3.2.core hq3Zero)
  exact hq4view.trans (hq3view.trans hkOriginal)

private theorem multiLeaderCleanup_tail_peaceView_eq_egressSink
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hready : MultiLeaderCleanupPhysicalPairReady
      hpsi kappa l r) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let after := wallSweepResetProbePreCheckResetAfterCheck
      hpsi kappa l0 r0
    authorizedPeaceViewPair
        (multiLeaderAfterCheckSuffix hpsi after.1 after.2) =
      peaceViewPair
        (eliminateLeadersNoCollisionEgressSink
          hpsi l.core r.core) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let before := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let after := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  have hIdleL := hready.left_idle
  have hIdleR := hready.right_idle
  change CleanupLeftTailIdle before.1 at hIdleL
  change CleanupRightTailIdle before.2 at hIdleR
  have hbefore := multiLeaderCleanup_beforeCheck_view
    hpsi kappa l r hready
  change authorizedPeaceViewPair before =
    authorizedPeaceViewPair (l, r) at hbefore
  have hafter : after = before := by
    change authorizedCheckSig hpsi before.1 before.2 = before
    exact authorizedCheckSig_pair_eq_of_cleanup_idle
      hpsi before hIdleL hIdleR
  let q0 := authorizedDisappear hpsi after.1 after.2
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  have hq2Before := cleanupIdleTail_suppress_peaceView
    hpsi before after hafter hIdleL hIdleR
  change authorizedPeaceViewPair q2 = authorizedPeaceViewPair before
    at hq2Before
  have hq2view : authorizedPeaceViewPair q2 =
      authorizedPeaceViewPair (l, r) := hq2Before.trans hbefore
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  let q4 := authorizedReconcile
    (writeSeqIncrementGate hpsi) q3.1 q3.2
  have hq4view := cleanupKernelWrite_peaceView
    hpsi l r q2 hq2view hready.responder_zero
  change authorizedPeaceViewPair q4 =
    peaceViewPair
      (eliminateLeadersNoCollisionEgressSink hpsi l.core r.core)
        at hq4view
  change authorizedPeaceViewPair q4 = _
  exact hq4view

/-- On the minimal pair contract, the complete authorized transition has
exactly the five-field output of the isolated egress-sink kernel. -/
theorem multiLeaderCleanupAuthorizedTransition_peaceView_eq_egressSink
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hready : MultiLeaderCleanupPhysicalPairReady
      hpsi kappa l r) :
    authorizedPeaceViewPair
        (multiLeaderCleanupAuthorizedTransition hpsi kappa l r) =
      peaceViewPair
        (eliminateLeadersNoCollisionEgressSink
          hpsi l.core r.core) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let before := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let after := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  let tail := multiLeaderAfterCheckSuffix hpsi after.1 after.2
  have htailView := multiLeaderCleanup_tail_peaceView_eq_egressSink
    hpsi kappa l r hready
  change authorizedPeaceViewPair tail =
      peaceViewPair
        (eliminateLeadersNoCollisionEgressSink
          hpsi l.core r.core) at htailView
  let born := leaderBirthBeforeOrAtCheck l0 r0 before after
  have htransition :=
    multiLeaderCleanupAuthorizedTransition_of_priority_open
      hpsi kappa l r hready.priority_open
  change multiLeaderCleanupAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at htransition
  calc
    authorizedPeaceViewPair
        (multiLeaderCleanupAuthorizedTransition hpsi kappa l r) =
      authorizedPeaceViewPair (markLeaderBirth born tail) :=
        congrArg authorizedPeaceViewPair htransition
    _ = authorizedPeaceViewPair tail :=
      markLeaderBirth_peaceViewPair born tail
    _ = peaceViewPair
        (eliminateLeadersNoCollisionEgressSink
          hpsi l.core r.core) := htailView

/-- CleanupPhysicalView form of the authorized refinement. -/
theorem multiLeaderCleanupAuthorizedTransition_cleanupPhysicalView_eq_egressSink
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hready : MultiLeaderCleanupPhysicalPairReady
      hpsi kappa l r) :
    authorizedCleanupPhysicalViewPair
        (multiLeaderCleanupAuthorizedTransition hpsi kappa l r) =
      cleanupPhysicalViewPair
        (eliminateLeadersNoCollisionEgressSink
          hpsi l.core r.core) := by
  apply cleanupPhysicalViewPair_eq_of_peaceViewPair_eq
  exact multiLeaderCleanupAuthorizedTransition_peaceView_eq_egressSink
    hpsi kappa l r hready

abbrev ExpiringMultiLeaderCleanupPhysicalPairReady
    (hpsi : psi > 0) (kappa : Nat)
    (l r : ExpiringAgentState psi kappa tau) : Prop :=
  MultiLeaderCleanupPhysicalPairReady
    hpsi kappa l.core.erase r.core.erase

/-- The actual expiring pair transition refines the raw kernel on its erased
input cores, exactly in CleanupPhysicalView. -/
theorem multiLeaderCleanupTransition_cleanupPhysicalView_eq_egressSink
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hready : ExpiringMultiLeaderCleanupPhysicalPairReady
      hpsi kappa l r) :
    expiringCleanupPhysicalViewPair
        (multiLeaderCleanupTransition hpsi kappa tau l r) =
      cleanupPhysicalViewPair
        (eliminateLeadersNoCollisionEgressSink hpsi
          l.core.erase.core r.core.erase.core) := by
  exact
    (multiLeaderCleanupTransition_cleanupPhysicalView_eq_authorized
      hpsi kappa tau l r).trans
      (multiLeaderCleanupAuthorizedTransition_cleanupPhysicalView_eq_egressSink
        hpsi kappa l.core.erase r.core.erase hready)

/-! ## 4. Local-step and schedule simulation -/

/-- The pair contract must be reconstructed at every concrete full-state
pre.  It is intentionally not inferred from the five-field quotient, since
its CHECK/COMPARE hypotheses mention hidden comparison fields. -/
def MultiLeaderCleanupPhysicalReadyAlong
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    DetSchedule n → Prop
  | [] => True
  | e :: rest =>
      ExpiringMultiLeaderCleanupPhysicalPairReady
        hpsi kappa (C e) (C (ring.rightNeighbor e)) ∧
      MultiLeaderCleanupPhysicalReadyAlong
        hpsi kappa tau ring
        (localStep ring
          (multiLeaderCleanupTransition hpsi kappa tau) C e) rest

/-! ## Schedule algebra for physical pair readiness -/

/-- Specialized append law for the executable multi-leader cleanup schedule.
The pre is executed first; the suffix starts from the pre endpoint. -/
theorem runLocalSchedule_multiLeaderCleanupTransition_append
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (pre suffix : DetSchedule n) :
    runLocalSchedule ring
        (multiLeaderCleanupTransition hpsi kappa tau)
        C (pre ++ suffix) =
      runLocalSchedule ring
        (multiLeaderCleanupTransition hpsi kappa tau)
        (runLocalSchedule ring
          (multiLeaderCleanupTransition hpsi kappa tau)
          C pre)
        suffix := by
  exact PPLLSchedulerBlocks.runLocalSchedule_append
    ring (multiLeaderCleanupTransition hpsi kappa tau)
    C pre suffix

/-- Physical readiness along an appended word is exactly readiness along the
pre together with readiness along the suffix from the executable pre
endpoint. -/
theorem multiLeaderCleanupPhysicalReadyAlong_append_iff
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (pre suffix : DetSchedule n) :
    MultiLeaderCleanupPhysicalReadyAlong
        hpsi kappa tau ring C (pre ++ suffix) ↔
      MultiLeaderCleanupPhysicalReadyAlong
          hpsi kappa tau ring C pre ∧
        MultiLeaderCleanupPhysicalReadyAlong
          hpsi kappa tau ring
          (runLocalSchedule ring
            (multiLeaderCleanupTransition hpsi kappa tau)
            C pre)
          suffix := by
  induction pre generalizing C with
  | nil =>
      simp [MultiLeaderCleanupPhysicalReadyAlong, runLocalSchedule]
  | cons e pre ih =>
      simp only [List.cons_append,
        MultiLeaderCleanupPhysicalReadyAlong, runLocalSchedule]
      rw [ih (C := localStep ring
        (multiLeaderCleanupTransition hpsi kappa tau) C e)]
      constructor
      · intro h
        exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
      · intro h
        exact ⟨h.1.1, h.1.2, h.2⟩

/-- Constructor form of the append equivalence. -/
theorem multiLeaderCleanupPhysicalReadyAlong_append
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (pre suffix : DetSchedule n)
    (hprefix : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C pre)
    (hsuffix : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring
      (runLocalSchedule ring
        (multiLeaderCleanupTransition hpsi kappa tau)
        C pre)
      suffix) :
    MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C (pre ++ suffix) := by
  exact
    (multiLeaderCleanupPhysicalReadyAlong_append_iff
      hpsi kappa tau ring C pre suffix).2
      ⟨hprefix, hsuffix⟩

/-- Readiness on an appended word restricts to its literal pre. -/
theorem multiLeaderCleanupPhysicalReadyAlong_prefix
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (pre suffix : DetSchedule n)
    (hready : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C (pre ++ suffix)) :
    MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C pre := by
  exact
    ((multiLeaderCleanupPhysicalReadyAlong_append_iff
      hpsi kappa tau ring C pre suffix).1 hready).1

/-- Readiness on an appended word restricts to its suffix at the exact
configuration obtained by executing the pre. -/
theorem multiLeaderCleanupPhysicalReadyAlong_suffix
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (pre suffix : DetSchedule n)
    (hready : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C (pre ++ suffix)) :
    MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring
      (runLocalSchedule ring
        (multiLeaderCleanupTransition hpsi kappa tau)
        C pre)
      suffix := by
  exact
    ((multiLeaderCleanupPhysicalReadyAlong_append_iff
      hpsi kappa tau ring C pre suffix).1 hready).2

/-- One-step unfolding of the recursive physical-readiness contract. -/
@[simp] theorem multiLeaderCleanupPhysicalReadyAlong_cons_iff
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (e : Fin n) (rest : DetSchedule n) :
    MultiLeaderCleanupPhysicalReadyAlong
        hpsi kappa tau ring C (e :: rest) ↔
      ExpiringMultiLeaderCleanupPhysicalPairReady
          hpsi kappa (C e) (C (ring.rightNeighbor e)) ∧
        MultiLeaderCleanupPhysicalReadyAlong
          hpsi kappa tau ring
          (localStep ring
            (multiLeaderCleanupTransition hpsi kappa tau)
            C e)
          rest := by
  rfl

/-- A singleton physical-readiness contract is exactly readiness of its one
selected pair. -/
@[simp] theorem multiLeaderCleanupPhysicalReadyAlong_singleton_iff
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (e : Fin n) :
    MultiLeaderCleanupPhysicalReadyAlong
        hpsi kappa tau ring C [e] ↔
      ExpiringMultiLeaderCleanupPhysicalPairReady
        hpsi kappa (C e) (C (ring.rightNeighbor e)) := by
  simp [MultiLeaderCleanupPhysicalReadyAlong]

/-- The head edge of a ready word is a physically ready pair. -/
theorem multiLeaderCleanupPhysicalReadyAlong_head
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (e : Fin n) (rest : DetSchedule n)
    (hready : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C (e :: rest)) :
    ExpiringMultiLeaderCleanupPhysicalPairReady
      hpsi kappa (C e) (C (ring.rightNeighbor e)) := by
  exact
    ((multiLeaderCleanupPhysicalReadyAlong_cons_iff
      hpsi kappa tau ring C e rest).1 hready).1

/-- Lookup at a specified schedule position represented by the literal
`pre ++ e :: suffix` decomposition.  The selected pair is read in the
configuration after exactly `pre`. -/
theorem multiLeaderCleanupPhysicalReadyAlong_pairReady_of_append_cons
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (pre : DetSchedule n) (e : Fin n) (suffix : DetSchedule n)
    (hready : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C (pre ++ (e :: suffix))) :
    ExpiringMultiLeaderCleanupPhysicalPairReady
      hpsi kappa
      ((runLocalSchedule ring
        (multiLeaderCleanupTransition hpsi kappa tau)
        C pre) e)
      ((runLocalSchedule ring
        (multiLeaderCleanupTransition hpsi kappa tau)
        C pre) (ring.rightNeighbor e)) := by
  have htail : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring
      (runLocalSchedule ring
        (multiLeaderCleanupTransition hpsi kappa tau)
        C pre)
      (e :: suffix) :=
    multiLeaderCleanupPhysicalReadyAlong_suffix
      hpsi kappa tau ring C pre (e :: suffix) hready
  exact multiLeaderCleanupPhysicalReadyAlong_head
    hpsi kappa tau ring
    (runLocalSchedule ring
      (multiLeaderCleanupTransition hpsi kappa tau)
      C pre)
    e suffix htail

/-- Final-position specialization: readiness on `pre ++ [e]` exposes the
pair selected after executing `pre`. -/
theorem multiLeaderCleanupPhysicalReadyAlong_pairReady_of_append_singleton
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (pre : DetSchedule n) (e : Fin n)
    (hready : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C (pre ++ [e])) :
    ExpiringMultiLeaderCleanupPhysicalPairReady
      hpsi kappa
      ((runLocalSchedule ring
        (multiLeaderCleanupTransition hpsi kappa tau)
        C pre) e)
      ((runLocalSchedule ring
        (multiLeaderCleanupTransition hpsi kappa tau)
        C pre) (ring.rightNeighbor e)) := by
  exact multiLeaderCleanupPhysicalReadyAlong_pairReady_of_append_cons
    hpsi kappa tau ring C pre e [] hready

/-- Equality-oriented pre destructor for named word decompositions such as
`SegmentCleanupPlan.word`. -/
theorem multiLeaderCleanupPhysicalReadyAlong_prefix_of_eq_append
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (word pre suffix : DetSchedule n)
    (hword : word = pre ++ suffix)
    (hready : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C word) :
    MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C pre := by
  rw [hword] at hready
  exact multiLeaderCleanupPhysicalReadyAlong_prefix
    hpsi kappa tau ring C pre suffix hready

/-- Equality-oriented suffix destructor.  Its initial configuration is the
literal executable endpoint after the named pre. -/
theorem multiLeaderCleanupPhysicalReadyAlong_suffix_of_eq_append
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (word pre suffix : DetSchedule n)
    (hword : word = pre ++ suffix)
    (hready : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C word) :
    MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring
      (runLocalSchedule ring
        (multiLeaderCleanupTransition hpsi kappa tau)
        C pre)
      suffix := by
  rw [hword] at hready
  exact multiLeaderCleanupPhysicalReadyAlong_suffix
    hpsi kappa tau ring C pre suffix hready

/-- Equality-oriented lookup at a named position.  This is the direct consumer
for a proved suffix decomposition of `SegmentCleanupPlan.word`. -/
theorem multiLeaderCleanupPhysicalReadyAlong_pairReady_of_eq_append_cons
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (word pre : DetSchedule n) (e : Fin n)
    (suffix : DetSchedule n)
    (hword : word = pre ++ (e :: suffix))
    (hready : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C word) :
    ExpiringMultiLeaderCleanupPhysicalPairReady
      hpsi kappa
      ((runLocalSchedule ring
        (multiLeaderCleanupTransition hpsi kappa tau)
        C pre) e)
      ((runLocalSchedule ring
        (multiLeaderCleanupTransition hpsi kappa tau)
        C pre) (ring.rightNeighbor e)) := by
  rw [hword] at hready
  exact multiLeaderCleanupPhysicalReadyAlong_pairReady_of_append_cons
    hpsi kappa tau ring C pre e suffix hready

/-- One concrete full-state interaction simulates one raw-kernel interaction
pointwise in CleanupPhysicalView. -/
theorem localStep_multiLeaderCleanup_cleanupPhysicalView_simulation
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (R : Fin n → AgentState psi) (e : Fin n)
    (hview : ∀ i,
      cleanupPhysicalViewOfState (C i).core.erase.core =
        cleanupPhysicalViewOfState (R i))
    (hready : ExpiringMultiLeaderCleanupPhysicalPairReady
      hpsi kappa (C e) (C (ring.rightNeighbor e))) :
    ∀ i,
      cleanupPhysicalViewOfState
          ((localStep ring
            (multiLeaderCleanupTransition hpsi kappa tau) C e) i).core.erase.core =
        cleanupPhysicalViewOfState
          ((localStep ring
            (eliminateLeadersNoCollisionEgressSink hpsi) R e) i) := by
  let j := ring.rightNeighbor e
  have hfull :=
    multiLeaderCleanupTransition_cleanupPhysicalView_eq_egressSink
      hpsi kappa tau (C e) (C j) hready
  have hraw :=
    eliminateLeadersNoCollisionEgressSink_cleanupPhysicalView_congr
      hpsi (C e).core.erase.core (C j).core.erase.core
        (R e) (R j) (hview e) (hview j)
  have hpair := hfull.trans hraw
  change
    (cleanupPhysicalViewOfState
        (multiLeaderCleanupTransition hpsi kappa tau
          (C e) (C j)).1.core.erase.core,
      cleanupPhysicalViewOfState
        (multiLeaderCleanupTransition hpsi kappa tau
          (C e) (C j)).2.core.erase.core) =
    (cleanupPhysicalViewOfState
        (eliminateLeadersNoCollisionEgressSink hpsi
          (R e) (R j)).1,
      cleanupPhysicalViewOfState
        (eliminateLeadersNoCollisionEgressSink hpsi
          (R e) (R j)).2) at hpair
  intro i
  by_cases hie : i = e
  · subst i
    simpa [localStep, j] using congrArg Prod.fst hpair
  · by_cases hij : i = j
    · subst i
      simpa [localStep, j, hie] using congrArg Prod.snd hpair
    · simpa [localStep, j, hie, hij] using hview i

/-- Iterating the preceding local simulation gives the exact pointwise quotient
simulation for any literal schedule carrying the per-pre pair contracts. -/
theorem runLocalSchedule_multiLeaderCleanup_cleanupPhysicalView_simulation
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (R : Fin n → AgentState psi) (word : DetSchedule n)
    (hview : ∀ i,
      cleanupPhysicalViewOfState (C i).core.erase.core =
        cleanupPhysicalViewOfState (R i))
    (halong : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C word) :
    ∀ i,
      cleanupPhysicalViewOfState
          ((runLocalSchedule ring
            (multiLeaderCleanupTransition hpsi kappa tau)
            C word) i).core.erase.core =
        cleanupPhysicalViewOfState
          ((runLocalSchedule ring
            (eliminateLeadersNoCollisionEgressSink hpsi)
            R word) i) := by
  induction word generalizing C R with
  | nil =>
      simpa [runLocalSchedule] using hview
  | cons e rest ih =>
      change ExpiringMultiLeaderCleanupPhysicalPairReady
          hpsi kappa (C e) (C (ring.rightNeighbor e)) ∧
        MultiLeaderCleanupPhysicalReadyAlong
          hpsi kappa tau ring
          (localStep ring
            (multiLeaderCleanupTransition hpsi kappa tau) C e) rest
        at halong
      rcases halong with ⟨hedge, hrest⟩
      have hstep :=
        localStep_multiLeaderCleanup_cleanupPhysicalView_simulation
          hpsi kappa tau ring C R e hview hedge
      simp only [runLocalSchedule]
      exact ih
        (C := localStep ring
          (multiLeaderCleanupTransition hpsi kappa tau) C e)
        (R := localStep ring
          (eliminateLeadersNoCollisionEgressSink hpsi) R e)
        hstep hrest

/-- Initializing the raw execution with the literal erased configuration gives
the form used by the two-leader cleanup word. -/
theorem runLocalSchedule_multiLeaderCleanup_cleanupPhysicalView_eq_raw
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (word : DetSchedule n)
    (halong : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C word) :
    ∀ i,
      cleanupPhysicalViewOfState
          ((runLocalSchedule ring
            (multiLeaderCleanupTransition hpsi kappa tau)
            C word) i).core.erase.core =
        cleanupPhysicalViewOfState
          ((runLocalSchedule ring
            (eliminateLeadersNoCollisionEgressSink hpsi)
            (eraseExpiringCleanupConfig C) word) i) := by
  exact runLocalSchedule_multiLeaderCleanup_cleanupPhysicalView_simulation
    hpsi kappa tau ring C (eraseExpiringCleanupConfig C) word
      (fun _ => rfl) halong

/-- `runLocalSchedule` and the raw trace's `applySchedule` are extensionally
identical for the egress-sink kernel. -/
theorem runLocalSchedule_eq_applySchedule_egressSink
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState psi) (word : DetSchedule n) :
    runLocalSchedule ring
        (eliminateLeadersNoCollisionEgressSink hpsi) C word =
      applySchedule ring
        (eliminateLeadersNoCollisionEgressSink hpsi) C word := by
  induction word generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [runLocalSchedule, applySchedule]
      have hstep :
          localStep ring
              (eliminateLeadersNoCollisionEgressSink hpsi) C e =
            stepConfig ring
              (eliminateLeadersNoCollisionEgressSink hpsi) C e := by
        rfl
      rw [hstep]
      exact ih
        (C := stepConfig ring
          (eliminateLeadersNoCollisionEgressSink hpsi) C e)

/-- Exact bridge to the output function used by `TwoLeaderCleanupTrace`. -/
theorem runLocalSchedule_egressSink_eq_plan_output
    (hpsi : psi > 0) (ring : DirectedRing n)
    (plan : TwoLeaderCleanupSchedule ring)
    (C : Fin n → AgentState psi) :
    runLocalSchedule ring
        (eliminateLeadersNoCollisionEgressSink hpsi) C plan.word =
      plan.output hpsi C := by
  unfold TwoLeaderCleanupSchedule.output
  exact runLocalSchedule_eq_applySchedule_egressSink
    hpsi ring C plan.word

/-- The compiled raw trace and the full-transition quotient simulation can now
be consumed together without changing either theorem. -/
theorem TwoLeaderCleanupReady.trace_with_multiLeaderCleanup_simulation
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (plan : TwoLeaderCleanupSchedule ring)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hready : TwoLeaderCleanupReady
      hpsi ring plan (eraseExpiringCleanupConfig C))
    (halong : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C plan.word) :
    (∀ i,
      cleanupPhysicalViewOfState
          ((runLocalSchedule ring
            (multiLeaderCleanupTransition hpsi kappa tau)
            C plan.word) i).core.erase.core =
        cleanupPhysicalViewOfState
          ((plan.output hpsi (eraseExpiringCleanupConfig C)) i)) ∧
      TwoLeaderCleanupTrace
        hpsi ring plan (eraseExpiringCleanupConfig C) := by
  constructor
  · have hsim :=
      runLocalSchedule_multiLeaderCleanup_cleanupPhysicalView_eq_raw
        hpsi kappa tau ring C plan.word halong
    have hout := runLocalSchedule_egressSink_eq_plan_output
      hpsi ring plan (eraseExpiringCleanupConfig C)
    rw [hout] at hsim
    exact hsim
  · exact hready.trace

end PhysicalBridge
end PPLLCompleteMultiLeaderCleanup
