import Leader.Wu.Elimination.MultiLeaderCleanupPhysicalBridge
import Leader.Wu.Elimination.MultiLeaderCleanupRepairTail
import Leader.Wu.Birth.PpsiLeaderCreationSchedule

/-!
# Reset-free multi-leader repair edge

The leader-kill word need not leave a reset token on the incoming predecessor.
This module isolates the other live P-prime branch: on follower inputs, a
nonbirth P-prime interaction installs the cyclic successor label.  The result
is lifted through the complete authorized, bounded, and expiring transition.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PhysicalBridge

open PPLL PPLLRepair PPLLVerify PPLLResearchFormulation PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLTerminalEqualSupportRepair
  PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepFiniteCleanup PPLLWallSweepNormalResetContract
  PPLLWallSweepPreCheckResetRepair
  PPLLWallSweepPreCheckResetContracts
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol
  PPLLPpsiLeaderCreationSchedule PPLLPpsiLeaderCreationRepair
  PPLLWriteIncrementGate

variable {n psi kappa tau : Nat}

/-- Hidden-field contract for one reset-free follower repair edge.  The
`ppsi_responder_follower` field selects the nonbirth side of the exact P-prime
dichotomy; the two idle fields exclude a later CHECK birth or comparison-side
rewrite. -/
structure MultiLeaderCleanupResetFreePairReady
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : Prop where
  priority_open : AuthorizedPriorityOpen l r
  left_follower : (normalizeDeletion l).core.leader = false
  right_follower : (normalizeDeletion r).core.leader = false
  left_reset_false : (normalizeDeletion l).core.reset_cmd = false
  ppsi_responder_follower :
    (pPsi hpsi (normalizeDeletion l).core
      (normalizeDeletion r).core).2.leader = false
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

/-- Conjunctive form of the reset-free readiness contract.  Unlike the named
structure, this form inherits a computational `Decidable` instance and is
therefore suitable for finite regression sweeps. -/
abbrev MultiLeaderCleanupResetFreePairConditions
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : Prop :=
  AuthorizedPriorityOpen l r ∧
  (normalizeDeletion l).core.leader = false ∧
  (normalizeDeletion r).core.leader = false ∧
  (normalizeDeletion l).core.reset_cmd = false ∧
  (pPsi hpsi (normalizeDeletion l).core
    (normalizeDeletion r).core).2.leader = false ∧
  (let before := wallSweepResetProbePreCheckResetBeforeCheck
      hpsi kappa (normalizeDeletion l) (normalizeDeletion r);
    CleanupLeftTailIdle before.1) ∧
  (let before := wallSweepResetProbePreCheckResetBeforeCheck
      hpsi kappa (normalizeDeletion l) (normalizeDeletion r);
    CleanupRightTailIdle before.2)

theorem multiLeaderCleanupResetFreePairReady_iff_conditions
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    MultiLeaderCleanupResetFreePairReady hpsi kappa l r ↔
      MultiLeaderCleanupResetFreePairConditions hpsi kappa l r := by
  constructor
  · intro h
    exact ⟨h.priority_open, h.left_follower, h.right_follower,
      h.left_reset_false, h.ppsi_responder_follower,
      h.left_idle, h.right_idle⟩
  · rintro ⟨hopen, hl, hr, hlReset, hp, hIdleL, hIdleR⟩
    exact
      { priority_open := hopen
        left_follower := hl
        right_follower := hr
        left_reset_false := hlReset
        ppsi_responder_follower := hp
        left_idle := hIdleL
        right_idle := hIdleR }

/-- A responder probe is the only possible P-prime birth trigger on a
follower/follower edge.  This constructor replaces the opaque nonbirth field
by the more tractable producer obligation that the concrete responder carry
no probe. -/
theorem multiLeaderCleanupResetFreePairReady_of_responder_probe_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hl : (normalizeDeletion l).core.leader = false)
    (hr : (normalizeDeletion r).core.leader = false)
    (hlReset : (normalizeDeletion l).core.reset_cmd = false)
    (hrProbe : (normalizeDeletion r).core.probe = false)
    (hIdleL :
      let before := wallSweepResetProbePreCheckResetBeforeCheck
        hpsi kappa (normalizeDeletion l) (normalizeDeletion r)
      CleanupLeftTailIdle before.1)
    (hIdleR :
      let before := wallSweepResetProbePreCheckResetBeforeCheck
        hpsi kappa (normalizeDeletion l) (normalizeDeletion r)
      CleanupRightTailIdle before.2) :
    MultiLeaderCleanupResetFreePairReady hpsi kappa l r := by
  have hleaders :=
    pPsiLeaderProbeWall_leaders_false_of_no_responder_probe
      hpsi (normalizeDeletion l).core (normalizeDeletion r).core
        hl hr hrProbe
  rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders
    hpsi (normalizeDeletion l).core (normalizeDeletion r).core hl hr]
    at hleaders
  exact
    { priority_open := hopen
      left_follower := hl
      right_follower := hr
      left_reset_false := hlReset
      ppsi_responder_follower := hleaders.2
      left_idle := hIdleL
      right_idle := hIdleR }

/-- Literal Algorithm 2 always consumes the responder probe.  The initiator
may receive or create a probe, but no branch leaves one on the responder. -/
theorem pPsi_responder_probe_false
    (hpsi : psi > 0) (l r : AgentState psi) :
    (pPsi hpsi l r).2.probe = false := by
  simp [pPsi]

/-- The leader/reset probe wall inherits unconditional responder clearing. -/
theorem pPsiLeaderResetProbeWall_responder_probe_false
    (hpsi : psi > 0) (l r : AgentState psi) :
    (pPsiLeaderResetProbeWall hpsi l r).2.probe = false := by
  cases hl : l.leader <;> cases hr : r.leader <;>
    cases hlReset : l.reset_cmd <;> cases hrProbe : r.probe <;>
      simp [pPsiLeaderResetProbeWall, pPsi, hl, hr, hlReset, hrProbe]

/-- A leader initiator makes both endpoint probes false before the rest of the
ordinary cleanup prefix. -/
theorem pPsiLeaderResetProbeWall_consumes_at_left_leader
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = true) :
    let q := pPsiLeaderResetProbeWall hpsi l r
    q.1.probe = false ∧ q.2.probe = false := by
  simp [pPsiLeaderResetProbeWall, pPsi, hl]

/-- The complete reset-aware prefix through SIGMOVE preserves the exact
three-field P-prime control output of its first stage. -/
theorem wallSweepResetProbeAuthorizedBeforeCheck_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair
        (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r) =
      ppsiControlPair (pPsiLeaderResetProbeWall hpsi l.core r.core) := by
  let q0 := authorizedPPsiLeaderResetProbeWall hpsi l r
  let q1 := authorizedGenSig hpsi kappa q0.1 q0.2
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  let q3 := authorizedEliminateSig hpsi q2.1 q2.2
  have h0 : authorizedPpsiControlPair q0 =
      ppsiControlPair (pPsiLeaderResetProbeWall hpsi l.core r.core) := rfl
  change authorizedPpsiControlPair
      (authorizedSigMoveLeaderWall hpsi q3.1 q3.2) = _
  exact (authorizedSigMoveLeaderWall_ppsiControlPair
      hpsi q3.1 q3.2).trans
    ((authorizedEliminateSig_ppsiControlPair hpsi q2.1 q2.2).trans
      ((authorizedCleanSig_ppsiControlPair hpsi q1.1 q1.2).trans
        ((authorizedGenSig_ppsiControlPair hpsi kappa q0.1 q0.2).trans h0)))

/-- The pre-CHECK reset wall and terminal sanitizer preserve the exact
reset-aware P-prime control pair. -/
theorem wallSweepResetProbePreCheckResetBeforeCheck_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair
        (wallSweepResetProbePreCheckResetBeforeCheck
          hpsi kappa l r) =
      ppsiControlPair
        (pPsiLeaderResetProbeWall hpsi l.core r.core) := by
  let q0 : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa l r
  have hpreCheckResetWall :
      ∀ q : AuthorizedAgentState psi × AuthorizedAgentState psi,
        authorizedPpsiControlPair
            (preCheckResetWall q.1 q.2) =
          authorizedPpsiControlPair q := by
    intro q
    rcases q with ⟨ql, qr⟩
    exact preCheckResetWall_ppsiControlPair ql qr
  have hsanitize :
      ∀ q : AuthorizedAgentState psi × AuthorizedAgentState psi,
        authorizedPpsiControlPair
            (sanitizeAuthorizedPair hpsi q) =
          authorizedPpsiControlPair q := by
    intro q
    exact sanitizeAuthorizedPair_ppsiControlPair hpsi q
  have houter :
      wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r =
        sanitizeAuthorizedPair hpsi
          (preCheckResetWall q0.1 q0.2) := by
    rfl
  have houterControl :
      authorizedPpsiControlPair
          (wallSweepResetProbePreCheckResetBeforeCheck
            hpsi kappa l r) =
        authorizedPpsiControlPair
          (sanitizeAuthorizedPair hpsi
            (preCheckResetWall q0.1 q0.2)) :=
    congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        authorizedPpsiControlPair q)
      houter
  have hq0 :
      authorizedPpsiControlPair q0 =
        ppsiControlPair
          (pPsiLeaderResetProbeWall hpsi l.core r.core) := by
    exact
      wallSweepResetProbeAuthorizedBeforeCheck_ppsiControlPair
        hpsi kappa l r
  calc
    authorizedPpsiControlPair
        (wallSweepResetProbePreCheckResetBeforeCheck
          hpsi kappa l r) =
      authorizedPpsiControlPair
        (sanitizeAuthorizedPair hpsi
          (preCheckResetWall q0.1 q0.2)) := houterControl
    _ = authorizedPpsiControlPair
          (preCheckResetWall q0.1 q0.2) :=
      hsanitize (preCheckResetWall q0.1 q0.2)
    _ = authorizedPpsiControlPair q0 :=
      hpreCheckResetWall q0
    _ = ppsiControlPair
          (pPsiLeaderResetProbeWall hpsi l.core r.core) := hq0

/-- The real CHECK stage also preserves the exact reset-aware P-prime control
pair. -/
theorem wallSweepResetProbePreCheckResetAfterCheck_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair
        (wallSweepResetProbePreCheckResetAfterCheck
          hpsi kappa l r) =
      ppsiControlPair
        (pPsiLeaderResetProbeWall hpsi l.core r.core) := by
  let beforeCheck :
      AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r
  have hcheck :
      ∀ q : AuthorizedAgentState psi × AuthorizedAgentState psi,
        authorizedPpsiControlPair
            (authorizedCheckSig hpsi q.1 q.2) =
          authorizedPpsiControlPair q := by
    intro q
    rcases q with ⟨ql, qr⟩
    exact authorizedCheckSig_ppsiControlPair hpsi ql qr
  have houter :
      wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r =
        authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2 := by
    rfl
  have houterControl :
      authorizedPpsiControlPair
          (wallSweepResetProbePreCheckResetAfterCheck
            hpsi kappa l r) =
        authorizedPpsiControlPair
          (authorizedCheckSig hpsi
            beforeCheck.1 beforeCheck.2) :=
    congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        authorizedPpsiControlPair q)
      houter
  have hbeforeCheck :
      authorizedPpsiControlPair beforeCheck =
        ppsiControlPair
          (pPsiLeaderResetProbeWall hpsi l.core r.core) := by
    exact
      wallSweepResetProbePreCheckResetBeforeCheck_ppsiControlPair
        hpsi kappa l r
  calc
    authorizedPpsiControlPair
        (wallSweepResetProbePreCheckResetAfterCheck
          hpsi kappa l r) =
      authorizedPpsiControlPair
        (authorizedCheckSig hpsi
          beforeCheck.1 beforeCheck.2) := houterControl
    _ = authorizedPpsiControlPair beforeCheck :=
      hcheck beforeCheck
    _ = ppsiControlPair
          (pPsiLeaderResetProbeWall hpsi l.core r.core) :=
      hbeforeCheck

/-- Every custom post-CHECK stage frames labels, probes, and phases. -/
theorem multiLeaderAfterCheckSuffix_ppsiControlPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPpsiControlPair (multiLeaderAfterCheckSuffix hpsi l r) =
      authorizedPpsiControlPair (l, r) := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  change authorizedPpsiControlPair
      (authorizedReconcile
        (writeSeqIncrementGate hpsi) q3.1 q3.2) = _
  exact (authorizedWriteSeqIncrementGate_ppsiControlPair
      hpsi q3.1 q3.2).trans
    ((authorizedEgressSink_ppsiControlPair hpsi q2.1 q2.2).trans
      ((authorizedSuppressSigResetKill_ppsiControlPair
        hpsi q1.1 q1.2).trans
        ((authorizedCompareSigActionOne_ppsiControlPair
          hpsi q0.1 q0.2).trans
          (authorizedDisappear_ppsiControlPair hpsi l r))))

/-- On the priority-open branch, the complete custom authorized transition
has exactly the controls produced by its reset-aware P-prime wall. -/
theorem multiLeaderCleanupAuthorizedTransition_priority_open_ppsiControlPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    authorizedPpsiControlPair
        (multiLeaderCleanupAuthorizedTransition hpsi kappa l r) =
      ppsiControlPair
        (pPsiLeaderResetProbeWall hpsi l0.core r0.core) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let before := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let after := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  let born := leaderBirthBeforeOrAtCheck l0 r0 before after
  let tail := multiLeaderAfterCheckSuffix hpsi after.1 after.2
  have hstage := multiLeaderCleanupAuthorizedTransition_of_priority_open
    hpsi kappa l r hopen
  change multiLeaderCleanupAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at hstage
  calc
    authorizedPpsiControlPair
        (multiLeaderCleanupAuthorizedTransition hpsi kappa l r) =
      authorizedPpsiControlPair (markLeaderBirth born tail) :=
        congrArg authorizedPpsiControlPair hstage
    _ = authorizedPpsiControlPair tail :=
      markLeaderBirth_ppsiControlPair born tail
    _ = authorizedPpsiControlPair after :=
      multiLeaderAfterCheckSuffix_ppsiControlPair
        hpsi after.1 after.2
    _ = ppsiControlPair
        (pPsiLeaderResetProbeWall hpsi l0.core r0.core) :=
      wallSweepResetProbePreCheckResetAfterCheck_ppsiControlPair
        hpsi kappa l0 r0

/-- Every priority-open complete authorized interaction leaves its responder
probe false, without a nonbirth, alignment, or follower hypothesis. -/
theorem multiLeaderCleanupAuthorizedTransition_responder_probe_false
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    (multiLeaderCleanupAuthorizedTransition hpsi kappa l r).2.core.probe =
      false := by
  have h := multiLeaderCleanupAuthorizedTransition_priority_open_ppsiControlPair
    hpsi kappa l r hopen
  have hp := congrArg
    (fun q : PpsiControlView psi × PpsiControlView psi => q.2.probe) h
  exact hp.trans
    (pPsiLeaderResetProbeWall_responder_probe_false hpsi
      (normalizeDeletion l).core (normalizeDeletion r).core)

/-- Exact reset behavior of Algorithm 14 on a reset-free follower initiator.
A stale responder reset survives precisely when its echo is false; hence a
pure reset-free induction needs a real suffix condition, not only the current
edge's left-reset premise. -/
theorem suppressSigResetKill_reset_of_left_follower
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hlReset : l.reset_cmd = false) :
    let q := suppressSigResetKill hpsi l r
    q.1.reset_cmd = false ∧
      q.2.reset_cmd = (r.reset_cmd && !r.echo) := by
  cases hrReset : r.reset_cmd <;> cases hrEcho : r.echo <;>
    simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
      resetKillComparison, clearComparisonSignal, suppressSigTerminal,
      suppressSigEcho, suppressSigFinish, hl, hlReset, hrReset, hrEcho]

/-- Exact reset output of the custom post-CHECK suffix when its initiator is
a reset-free follower.  This statement is independent of the cleanup prefix
and is the reusable induction step for reset-free repair edges. -/
theorem multiLeaderAfterCheckSuffix_reset_of_left_follower
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false)
    (hlReset : l.core.reset_cmd = false) :
    let q := multiLeaderAfterCheckSuffix hpsi l r
    q.1.core.reset_cmd = false ∧
      q.2.core.reset_cmd = (r.core.reset_cmd && !r.core.echo) := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  let q4 := authorizedReconcile
    (writeSeqIncrementGate hpsi) q3.1 q3.2
  have h0Reset := authorizedDisappear_resetEchoPair hpsi l r
  have h1Reset := authorizedCompareSigActionOne_resetEchoPair
    hpsi q0.1 q0.2
  have hpreFields := resetEcho_fields_of_pair_eq (h1Reset.trans h0Reset)
  have h0Leaders := PPLLVerify.disappear_leaders_eq
    hpsi l.core r.core
  have h1Leaders := compareActionOne_leaders hpsi q0.1 q0.2
  have hq1LeftFollower : q1.1.core.leader = false :=
    h1Leaders.1.trans (h0Leaders.1.trans hl)
  have hq1LeftReset : q1.1.core.reset_cmd = false :=
    hpreFields.1.trans hlReset
  have hraw := suppressSigResetKill_reset_of_left_follower
    hpsi q1.1.core q1.2.core hq1LeftFollower hq1LeftReset
  have hq3Frame := authorizedReconcile_resetEchoPair_of_cleanupAuxFrame
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
      (egressSink_cleanupAuxPair hpsi q2.1.core q2.2.core)
  have hq4Frame := authorizedReconcile_resetEchoPair_of_cleanupAuxFrame
    (writeSeqIncrementGate hpsi) q3.1 q3.2
      (writeSeqIncrementGate_cleanupAux_frame hpsi q3.1.core q3.2.core)
  have hpostFields := resetEcho_fields_of_pair_eq (hq4Frame.trans hq3Frame)
  have hout : q4.1.core.reset_cmd = false ∧
      q4.2.core.reset_cmd = (r.core.reset_cmd && !r.core.echo) :=
    ⟨hpostFields.1.trans hraw.1,
      hpostFields.2.2.1.trans
        (hraw.2.trans (by
          rw [hpreFields.2.2.1, hpreFields.2.2.2]))⟩
  simpa only [multiLeaderAfterCheckSuffix, q0, q1, q2, q3, q4]
    using hout

theorem wallSweepResetProbePreCheckResetBeforeCheck_peaceViewPair_eq_ppsi
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false)
    (hrFollower : r.core.leader = false)
    (hlReset : l.core.reset_cmd = false) :
    authorizedPeaceViewPair
        (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r) =
      peaceViewPair (pPsi hpsi l.core r.core) := by
  let q0 := authorizedPPsiLeaderResetProbeWall hpsi l r
  have hprefix :=
    wallSweepResetProbePreCheckResetBeforeCheck_peaceViewPair_eq_probe
      hpsi kappa l r
  change authorizedPeaceViewPair
      (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r) =
    authorizedPeaceViewPair q0 at hprefix
  have hcore := authorizedPPsiLeaderResetProbeWall_core hpsi l r
  have hreset := pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_no_reset
    hpsi l.core r.core hlReset
  have hfollowers := pPsiLeaderProbeWall_eq_pPsi_of_no_leaders
    hpsi l.core r.core hlFollower hrFollower
  calc
    authorizedPeaceViewPair
        (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r) =
      authorizedPeaceViewPair q0 := hprefix
    _ = peaceViewPair (pPsiLeaderResetProbeWall hpsi l.core r.core) :=
      congrArg peaceViewPair hcore
    _ = peaceViewPair (pPsiLeaderProbeWall hpsi l.core r.core) :=
      congrArg peaceViewPair hreset
    _ = peaceViewPair (pPsi hpsi l.core r.core) :=
      congrArg peaceViewPair hfollowers

private theorem eliminateLeadersNoCollisionEgressSink_followers_of_followers
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = false) :
    let q := eliminateLeadersNoCollisionEgressSink hpsi l r
    q.1.leader = false ∧ q.2.leader = false := by
  simp (config := { maxSteps := 20000 })
    [eliminateLeadersNoCollisionEgressSink,
      eliminateLeadersNoCollisionFire,
      eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink,
      dummyBulletSink, hl, hr]

private theorem eliminateLeadersNoCollisionEgressSink_labels_eq
    (hpsi : psi > 0) (l r : AgentState psi) :
    let q := eliminateLeadersNoCollisionEgressSink hpsi l r
    q.1.label = l.label ∧ q.2.label = r.label := by
  simp (config := { maxSteps := 20000 })
    [eliminateLeadersNoCollisionEgressSink,
      eliminateLeadersNoCollisionFire,
      eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink,
      dummyBulletSink]

private theorem authorizedPeaceViewPair_eq_peaceViewPair_fst
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (p : AgentState psi × AgentState psi)
    (h : authorizedPeaceViewPair q = peaceViewPair p) :
    PeaceView.ofState q.1.core = PeaceView.ofState p.1 :=
  congrArg Prod.fst h

private theorem authorizedPeaceViewPair_eq_peaceViewPair_snd
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (p : AgentState psi × AgentState psi)
    (h : authorizedPeaceViewPair q = peaceViewPair p) :
    PeaceView.ofState q.2.core = PeaceView.ofState p.2 :=
  congrArg Prod.snd h

/-- Leader read-off of the first endpoint, stated at variables so that callers
unify syntactically instead of reducing a concrete stage output. -/
private theorem authorizedPeaceViewPair_eq_peaceViewPair_fst_leader
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (p : AgentState psi × AgentState psi)
    (h : authorizedPeaceViewPair q = peaceViewPair p) :
    q.1.core.leader = p.1.leader :=
  congrArg (fun v : PeaceView psi × PeaceView psi => v.1.leader) h

private theorem authorizedPeaceViewPair_eq_peaceViewPair_snd_leader
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (p : AgentState psi × AgentState psi)
    (h : authorizedPeaceViewPair q = peaceViewPair p) :
    q.2.core.leader = p.2.leader :=
  congrArg (fun v : PeaceView psi × PeaceView psi => v.2.leader) h

/-- The complete reset-free prefix through real CHECK presents the custom
suffix with a follower/reset-free initiator and frames both input reset/echo
pairs. -/
theorem multiLeaderCleanupResetFree_afterCheck_control
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hready : MultiLeaderCleanupResetFreePairReady hpsi kappa l r) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let after := wallSweepResetProbePreCheckResetAfterCheck
      hpsi kappa l0 r0
    after.1.core.leader = false ∧
      after.1.core.reset_cmd = false ∧
      authorizedResetEchoPair after = authorizedResetEchoPair (l0, r0) := by
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
  have hafter : after = before :=
    authorizedCheckSig_pair_eq_of_cleanup_idle
      hpsi before hIdleL hIdleR
  have hbeforeView :=
    wallSweepResetProbePreCheckResetBeforeCheck_peaceViewPair_eq_ppsi
      hpsi kappa l0 r0 hready.left_follower hready.right_follower
        hready.left_reset_false
  have hpLeft : (pPsi hpsi l0.core r0.core).1.leader = false :=
    (PPLLVerify.pPsi_initiator_leader_eq hpsi l0.core r0.core).trans
      hready.left_follower
  have hbeforeLeft : before.1.core.leader = false :=
    (authorizedPeaceViewPair_eq_peaceViewPair_fst_leader
      before (pPsi hpsi l0.core r0.core) hbeforeView).trans hpLeft
  have hresetFrame :=
    wallSweepResetProbePreCheckResetAfterCheck_resetEchoPair
      hpsi kappa l0 r0
  have hresetFields := resetEcho_fields_of_pair_eq hresetFrame
  change after.1.core.leader = false ∧
    after.1.core.reset_cmd = false ∧
    authorizedResetEchoPair after = authorizedResetEchoPair (l0, r0)
  exact ⟨by rw [hafter]; exact hbeforeLeft,
    hresetFields.1.trans hready.left_reset_false, hresetFrame⟩

private theorem cleanupResetFreeAfterCheckSuffix_peaceView
    (hpsi : psi > 0)
    (before : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (p : AgentState psi × AgentState psi)
    (hview : authorizedPeaceViewPair before = peaceViewPair p)
    (hIdleL : CleanupLeftTailIdle before.1)
    (hIdleR : CleanupRightTailIdle before.2)
    (hpRightFollower : p.2.leader = false) :
    let after := authorizedCheckSig hpsi before.1 before.2
    authorizedPeaceViewPair
        (multiLeaderAfterCheckSuffix hpsi after.1 after.2) =
      peaceViewPair
        (eliminateLeadersNoCollisionEgressSink hpsi p.1 p.2) := by
  let after := authorizedCheckSig hpsi before.1 before.2
  have hafter : after = before :=
    authorizedCheckSig_pair_eq_of_cleanup_idle
      hpsi before hIdleL hIdleR
  let q0 := authorizedDisappear hpsi after.1 after.2
  let q1 := authorizedCompareSigActionOne hpsi q0.1 q0.2
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  have hq2Before := cleanupIdleTail_suppress_peaceView
    hpsi before after hafter hIdleL hIdleR
  change authorizedPeaceViewPair q2 = authorizedPeaceViewPair before
    at hq2Before
  have hbeforeRightView :=
    authorizedPeaceViewPair_eq_peaceViewPair_snd before p hview
  have hbeforeRightFollower : before.2.core.leader = false :=
    (authorizedPeaceViewPair_eq_peaceViewPair_snd_leader
      before p hview).trans hpRightFollower
  have hzero : before.2.core.leader = true →
      before.2.core.label = ⟨0, hpsi⟩ := by
    intro hleader
    rw [hbeforeRightFollower] at hleader
    contradiction
  let q3 := authorizedReconcile
    (eliminateLeadersNoCollisionEgressSink hpsi) q2.1 q2.2
  let q4 := authorizedReconcile
    (writeSeqIncrementGate hpsi) q3.1 q3.2
  have hq4 := cleanupKernelWrite_peaceView
    hpsi before.1 before.2 q2 hq2Before hzero
  change authorizedPeaceViewPair q4 =
    peaceViewPair
      (eliminateLeadersNoCollisionEgressSink
        hpsi before.1.core before.2.core) at hq4
  have hkernel := eliminateLeadersNoCollisionEgressSink_peaceView_congr
    hpsi before.1.core before.2.core p.1 p.2
      (authorizedPeaceViewPair_eq_peaceViewPair_fst before p hview)
      hbeforeRightView
  change authorizedPeaceViewPair q4 = _
  exact hq4.trans hkernel

private theorem multiLeaderCleanupResetFree_tail_peaceView_eq_ppsiEgressSink
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hready : MultiLeaderCleanupResetFreePairReady hpsi kappa l r) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let p := pPsi hpsi l0.core r0.core
    let after := wallSweepResetProbePreCheckResetAfterCheck
      hpsi kappa l0 r0
    authorizedPeaceViewPair
        (multiLeaderAfterCheckSuffix hpsi after.1 after.2) =
      peaceViewPair
        (eliminateLeadersNoCollisionEgressSink hpsi p.1 p.2) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let p := pPsi hpsi l0.core r0.core
  let before := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let after := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  have hbefore :=
    wallSweepResetProbePreCheckResetBeforeCheck_peaceViewPair_eq_ppsi
      hpsi kappa l0 r0 hready.left_follower hready.right_follower
        hready.left_reset_false
  change authorizedPeaceViewPair before = peaceViewPair p at hbefore
  have hIdleL := hready.left_idle
  have hIdleR := hready.right_idle
  change CleanupLeftTailIdle before.1 at hIdleL
  change CleanupRightTailIdle before.2 at hIdleR
  have htail := cleanupResetFreeAfterCheckSuffix_peaceView
    hpsi before p hbefore hIdleL hIdleR
      hready.ppsi_responder_follower
  change authorizedPeaceViewPair
      (multiLeaderAfterCheckSuffix hpsi after.1 after.2) =
    peaceViewPair
      (eliminateLeadersNoCollisionEgressSink hpsi p.1 p.2)
  exact htail

theorem multiLeaderCleanupAuthorizedTransition_peaceView_eq_resetFreePpsi
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hready : MultiLeaderCleanupResetFreePairReady hpsi kappa l r) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let p := pPsi hpsi l0.core r0.core
    authorizedPeaceViewPair
        (multiLeaderCleanupAuthorizedTransition hpsi kappa l r) =
      peaceViewPair
        (eliminateLeadersNoCollisionEgressSink hpsi p.1 p.2) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let p := pPsi hpsi l0.core r0.core
  let before := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let after := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  let born := leaderBirthBeforeOrAtCheck l0 r0 before after
  let tail := multiLeaderAfterCheckSuffix hpsi after.1 after.2
  have htail :=
    multiLeaderCleanupResetFree_tail_peaceView_eq_ppsiEgressSink
      hpsi kappa l r hready
  change authorizedPeaceViewPair tail =
    peaceViewPair
      (eliminateLeadersNoCollisionEgressSink hpsi p.1 p.2) at htail
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
        (eliminateLeadersNoCollisionEgressSink hpsi p.1 p.2) := htail

/-- A complete authorized reset-free follower edge preserves both follower
bits and replaces the responder label by the successor of the initiator label.
-/
theorem multiLeaderCleanupAuthorizedTransition_resetFree_follower_edge
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hready : MultiLeaderCleanupResetFreePairReady hpsi kappa l r) :
    let q := multiLeaderCleanupAuthorizedTransition hpsi kappa l r
    q.1.core.leader = false ∧
      q.2.core.leader = false ∧
      q.1.core.label = l.core.label ∧
      q.2.core.label =
        ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let p := pPsi hpsi l0.core r0.core
  let raw := eliminateLeadersNoCollisionEgressSink hpsi p.1 p.2
  let q := multiLeaderCleanupAuthorizedTransition hpsi kappa l r
  have hview :=
    multiLeaderCleanupAuthorizedTransition_peaceView_eq_resetFreePpsi
      hpsi kappa l r hready
  change authorizedPeaceViewPair q = peaceViewPair raw at hview
  have hpLeftFollower : p.1.leader = false :=
    (PPLLVerify.pPsi_initiator_leader_eq
      hpsi l0.core r0.core).trans hready.left_follower
  have hrawFollowers :=
    eliminateLeadersNoCollisionEgressSink_followers_of_followers
      hpsi p.1 p.2 hpLeftFollower hready.ppsi_responder_follower
  change raw.1.leader = false ∧ raw.2.leader = false at hrawFollowers
  have hrawLabels := eliminateLeadersNoCollisionEgressSink_labels_eq
    hpsi p.1 p.2
  change raw.1.label = p.1.label ∧ raw.2.label = p.2.label at hrawLabels
  have hpAligned : p.2.label =
      ⟨(l0.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
    have hwall :=
      pPsiLeaderProbeWall_responder_aligned_of_followers_of_output_follower
        hpsi l0.core r0.core hready.left_follower hready.right_follower
          (by
            rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders
              hpsi l0.core r0.core hready.left_follower
                hready.right_follower]
            exact hready.ppsi_responder_follower)
    rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders
      hpsi l0.core r0.core hready.left_follower hready.right_follower]
      at hwall
    exact hwall
  have hpLeftLabel : p.1.label = l0.core.label :=
    PPLLVerify.pPsi_initiator_label_eq hpsi l0.core r0.core
  have hl0Label : l0.core.label = l.core.label :=
    congrArg PeaceView.label (normalizeDeletion_peaceView l)
  have hqLeftLeader := congrArg
    (fun v : PeaceView psi × PeaceView psi => v.1.leader) hview
  have hqRightLeader := congrArg
    (fun v : PeaceView psi × PeaceView psi => v.2.leader) hview
  have hqLeftLabel := congrArg
    (fun v : PeaceView psi × PeaceView psi => v.1.label) hview
  have hqRightLabel := congrArg
    (fun v : PeaceView psi × PeaceView psi => v.2.label) hview
  change q.1.core.leader = raw.1.leader at hqLeftLeader
  change q.2.core.leader = raw.2.leader at hqRightLeader
  change q.1.core.label = raw.1.label at hqLeftLabel
  change q.2.core.label = raw.2.label at hqRightLabel
  exact ⟨hqLeftLeader.trans hrawFollowers.1,
    hqRightLeader.trans hrawFollowers.2,
    hqLeftLabel.trans (hrawLabels.1.trans (hpLeftLabel.trans hl0Label)),
    hqRightLabel.trans (hrawLabels.2.trans (hpAligned.trans (by
      rw [hl0Label])))⟩

abbrev ExpiringMultiLeaderCleanupResetFreePairReady
    (hpsi : psi > 0) (kappa : Nat)
    (l r : ExpiringAgentState psi kappa tau) : Prop :=
  MultiLeaderCleanupResetFreePairReady
    hpsi kappa l.core.erase r.core.erase

/-- Expiring form of the reset-free follower repair edge. -/
theorem multiLeaderCleanupTransition_resetFree_follower_edge
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hready : ExpiringMultiLeaderCleanupResetFreePairReady
      hpsi kappa l r) :
    let q := multiLeaderCleanupTransition hpsi kappa tau l r
    q.1.core.erase.core.leader = false ∧
      q.2.core.erase.core.leader = false ∧
      q.1.core.erase.core.label = l.core.erase.core.label ∧
      q.2.core.erase.core.label =
        ⟨(l.core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := by
  let qa := multiLeaderCleanupAuthorizedTransition
    hpsi kappa l.core.erase r.core.erase
  let q := multiLeaderCleanupTransition hpsi kappa tau l r
  have ha := multiLeaderCleanupAuthorizedTransition_resetFree_follower_edge
    hpsi kappa l.core.erase r.core.erase hready
  change qa.1.core.leader = false ∧ qa.2.core.leader = false ∧
    qa.1.core.label = l.core.erase.core.label ∧
    qa.2.core.label =
      ⟨(l.core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ at ha
  have hv := multiLeaderCleanupTransition_cleanupPhysicalView_eq_authorized
    hpsi kappa tau l r
  change expiringCleanupPhysicalViewPair q =
    authorizedCleanupPhysicalViewPair qa at hv
  have hll := congrArg
    (fun v : CleanupPhysicalView psi × CleanupPhysicalView psi =>
      v.1.leader) hv
  have hrl := congrArg
    (fun v : CleanupPhysicalView psi × CleanupPhysicalView psi =>
      v.2.leader) hv
  have hlabelL := congrArg
    (fun v : CleanupPhysicalView psi × CleanupPhysicalView psi =>
      v.1.label) hv
  have hlabelR := congrArg
    (fun v : CleanupPhysicalView psi × CleanupPhysicalView psi =>
      v.2.label) hv
  change q.1.core.erase.core.leader = qa.1.core.leader at hll
  change q.2.core.erase.core.leader = qa.2.core.leader at hrl
  change q.1.core.erase.core.label = qa.1.core.label at hlabelL
  change q.2.core.erase.core.label = qa.2.core.label at hlabelR
  exact ⟨hll.trans ha.1, hrl.trans ha.2.1,
    hlabelL.trans ha.2.2.1, hlabelR.trans ha.2.2.2⟩

/-! ## Cleanup-idle handoff through endpoint expiry -/

/-- The comparison/lottery payload survives the endpoint policy unchanged. -/
structure CleanupCarrierFramed
    (before out : AuthorizedAgentState psi) : Prop where
  path2 : out.core.path2 = before.core.path2
  path4 : out.core.path4 = before.core.path4
  path5 : out.core.path5 = before.core.path5
  p : out.core.p = before.core.p
  p_carry : out.core.p_carry = before.core.p_carry

/-- The endpoint policy deleted the complete comparison/lottery payload. -/
structure CleanupCarrierCleared
    (out : AuthorizedAgentState psi) : Prop where
  path2 : out.core.path2 = none
  path4 : out.core.path4 = none
  path5 : out.core.path5 = none
  p : out.core.p = false
  p_carry : out.core.p_carry = false

/-- Strongest timer-independent responder result at the cleanup-idle boundary.
The carrier alternative is a single common branch. -/
structure CleanupResponderPost
    (before out : AuthorizedAgentState psi) : Prop where
  state_none : out.core.state = .none
  path_bot : out.core.path = .bot
  permit_false : out.path0Crossed = false
  echo_false : out.core.echo = false
  carrier :
    CleanupCarrierFramed before out ∨
      CleanupCarrierCleared out

/-- The current right-idle contract plus the one Boolean needed when this
responder becomes the next initiator. -/
structure CleanupRightTailHandoffIdle
    (u : AuthorizedAgentState psi) : Prop where
  right : CleanupRightTailIdle u
  p_carry_false : u.core.p_carry = false

/-- The strengthened right contract is exactly a left-idle contract. -/
theorem CleanupRightTailHandoffIdle.toLeft
    {u : AuthorizedAgentState psi}
    (h : CleanupRightTailHandoffIdle u) :
    CleanupLeftTailIdle u := by
  exact
    { state_none := h.right.state_none
      path_bot := h.right.path_bot
      p_carry_false := h.p_carry_false
      permit_false := h.right.permit_false }

/-- The strongest postcondition always retains current right-idleness. -/
theorem CleanupResponderPost.toRight
    {before out : AuthorizedAgentState psi}
    (h : CleanupResponderPost before out) :
    CleanupRightTailIdle out := by
  exact
    { state_none := h.state_none
      path_bot := h.path_bot
      permit_false := h.permit_false }

/-- If the internal responder entered with no lottery carry, either endpoint
policy branch returns no lottery carry. -/
theorem CleanupResponderPost.toLeft_of_before_pCarry_false
    {before out : AuthorizedAgentState psi}
    (h : CleanupResponderPost before out)
    (hcarry : before.core.p_carry = false) :
    CleanupLeftTailIdle out := by
  refine
    { state_none := h.state_none
      path_bot := h.path_bot
      p_carry_false := ?_
      permit_false := h.permit_false }
  rcases h.carrier with hframe | hclear
  · exact hframe.p_carry.trans hcarry
  · exact hclear.p_carry

/-- Path absence makes the deletion-priority wrapper use the path-stall policy.
That policy either retains the complete bounded output or clears the complete
comparison carrier. -/
theorem deletionPriorityExpireOne_core_eq_or_clear
    (tau : Nat)
    (old out : ExpiringAgentState psi kappa tau)
    (hpath : out.core.erase.core.path = .bot) :
    (deletionPriorityExpireOne tau old out).core = out.core ∨
      (deletionPriorityExpireOne tau old out).core =
        clearComparisonCarrier out.core := by
  have hdel : deletionActive out.core.erase = false := by
    simp [deletionActive, pathPresent, hpath]
  by_cases hprogress :
      PathProgressView.ofState out.core ≠
        PathProgressView.ofState old.core
  · left
    simp [deletionPriorityExpireOne, hdel,
      pathExpireOne, hprogress]
  · have hstatic :
        PathProgressView.ofState out.core =
          PathProgressView.ofState old.core :=
      Decidable.not_not.mp hprogress
    by_cases hzero : old.stall.val = 0
    · right
      simp [deletionPriorityExpireOne, hdel,
        pathExpireOne, hstatic, hzero]
    · left
      simp [deletionPriorityExpireOne, hdel,
        pathExpireOne, hstatic, hzero]

/-- Generic endpoint lift. The complete transition-specific proof only has to
supply the authorized base-output frame. -/
theorem cleanupResponderPost_of_expire
    (before : AuthorizedAgentState psi)
    (old base : ExpiringAgentState psi kappa tau)
    (hstate : base.core.erase.core.state = .none)
    (hpath : base.core.erase.core.path = .bot)
    (hpermit : base.core.erase.path0Crossed = false)
    (hecho : base.core.erase.core.echo = false)
    (hframe : CleanupCarrierFramed before base.core.erase) :
    CleanupResponderPost before
      (deletionPriorityExpireOne tau old base).core.erase := by
  rcases deletionPriorityExpireOne_core_eq_or_clear
      tau old base hpath with hsame | hclear
  · rw [hsame]
    exact
      { state_none := hstate
        path_bot := hpath
        permit_false := hpermit
        echo_false := hecho
        carrier := Or.inl hframe }
  · rw [hclear]
    refine
      { state_none := by rfl
        path_bot := by rfl
        permit_false := by rfl
        echo_false := ?_
        carrier := Or.inr ?_ }
    · simpa [clearComparisonCarrier,
        AuthorizedBoundedAgentState.erase,
        BoundedAgentState.erase] using hecho
    · exact
        { path2 := by rfl
          path4 := by rfl
          path5 := by rfl
          p := by rfl
          p_carry := by rfl }

private def rightIdleCarryCounter
    (u : AuthorizedBoundedAgentState psi kappa) :
    AuthorizedBoundedAgentState psi kappa :=
  ⟨{ u.core with
      state := .none
      path := .bot
      p_carry := true },
    false⟩

/-- `CleanupRightTailIdle` does not imply the left-idle handoff. The smallest
positive timer, tau=1 with stall=1, takes the static positive branch and
preserves the true carry bit. -/
theorem cleanupRightTailIdle_not_left_after_positive_static_expiry
    (u : AuthorizedBoundedAgentState psi kappa) :
    let v := rightIdleCarryCounter u
    let s : ExpiringAgentState psi kappa 1 :=
      ⟨v, ⟨1, by omega⟩⟩
    CleanupRightTailIdle s.core.erase ∧
      ¬ CleanupLeftTailIdle
        (deletionPriorityExpireOne 1 s s).core.erase := by
  let v := rightIdleCarryCounter u
  let s : ExpiringAgentState psi kappa 1 :=
    ⟨v, ⟨1, by omega⟩⟩
  change CleanupRightTailIdle s.core.erase ∧
    ¬ CleanupLeftTailIdle
      (deletionPriorityExpireOne 1 s s).core.erase
  have hright : CleanupRightTailIdle s.core.erase := by
    exact
      { state_none := rfl
        path_bot := rfl
        permit_false := rfl }
  have hinactive : deletionActive s.core.erase = false := by
    simp [s, v, rightIdleCarryCounter,
      deletionActive, pathPresent,
      AuthorizedBoundedAgentState.erase,
      BoundedAgentState.erase]
  have hpos : s.stall.val > 0 := by
    simp [s]
  have hstatic :
      PathProgressView.ofState s.core =
        PathProgressView.ofState s.core := rfl
  have hpathStep :=
    pathExpireOne_succ_of_static 1 s s hstatic hpos
  have houter :
      deletionPriorityExpireOne 1 s s = pathExpireOne 1 s s := by
    simp [deletionPriorityExpireOne, hinactive]
  have houtCarry :
      (deletionPriorityExpireOne 1 s s).core.erase.core.p_carry = true := by
    rw [houter, hpathStep]
    rfl
  refine ⟨hright, ?_⟩
  intro hleft
  have hbad : true = false :=
    houtCarry.symm.trans hleft.p_carry_false
  simp at hbad

end PhysicalBridge
end PPLLCompleteMultiLeaderCleanup
