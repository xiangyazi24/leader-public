import Leader.Wu.WallSweep.ClockwiseRetry
import Leader.Wu.Birth.PpsiLeaderCreationRepair

/-!
# Terminal shield edge for the corrected pre-CHECK sweep

The zero-rank clockwise pass stops with an absence signal and reset token back
at the unique unshielded leader.  This module proves the next physical edge:
repaired Algorithm 14 clears or hands off the reset without changing the fire
fields, Algorithm 15 installs the shield before moving its live bullet, and the
later WRITE and expiry stages preserve the resulting protected anchor.
-/

namespace PPLLWallSweepPreCheckAnchor

open PPLL PPLLRepair PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLTerminalEqualSupportRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepSchedule PPLLWallSweepEchoDrain
  PPLLWallSweepNormalResetContract PPLLWallSweepPreCheckResetRepair
  PPLLWallSweepPreCheckResetContracts PPLLWallSweepPreCheckNoFire
  PPLLWallSweepClockwiseScheduler PPLLWallSweepUnshieldedRetry
  PPLLWallSweepClockwiseAttempt PPLLWallSweepRestartableProtected
  PPLLWallSweepRestartableGeneric PPLLWallSweepEchoRank
  PPLLPpsiLeaderCreationRepair PPLLPpsiLeaderCreationSchedule
  PPLLNoCheckBirthConditionTwoGeometry
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoKernel PPLLNoCheckBirthLeaderFrames
  PPLLWriteSeqRelocation PPLLWriteSeqPersistenceRegression

variable {n psi kappa tau : Nat}

/-! ## Pair-level fire contract -/

/-- Exact protected fields after a priority-open authorized leader fire. -/
structure AuthorizedLeaderFireOutput
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  left_neutral : ComparisonNeutral q.1.core
  right_neutral : ComparisonNeutral q.2.core
  left_leader : q.1.core.leader = true
  right_follower : q.2.core.leader = false
  left_label : q.1.core.label = l.core.label
  right_label : q.2.core.label = r.core.label
  left_shield_true : q.1.core.shield = true
  left_signal_zero : q.1.core.signal_B = ⟨0, by omega⟩

/-- The same protected fields after bounded reification and path-stall expiry. -/
structure LeaderFireOutput
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop where
  left_neutral : ComparisonNeutral q.1.core.erase.core
  right_neutral : ComparisonNeutral q.2.core.erase.core
  left_leader : q.1.core.erase.core.leader = true
  right_follower : q.2.core.erase.core.leader = false
  left_label : q.1.core.erase.core.label = l.core.erase.core.label
  right_label : q.2.core.erase.core.label = r.core.erase.core.label
  left_shield_true : q.1.core.erase.core.shield = true
  left_signal_zero : q.1.core.erase.core.signal_B = ⟨0, by omega⟩

/-- Exact closing-edge output of the rooted leader-sink repair before bounded
reification.  The returning absence signal reaches the existing leader while
every other physical field and the repaired reset/echo handoff are framed. -/
structure AuthorizedLeaderSinkClosingOutput
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  left_neutral : ComparisonNeutral q.1.core
  right_neutral : ComparisonNeutral q.2.core
  left_leader : q.1.core.leader = false
  right_leader : q.2.core.leader = true
  left_label : q.1.core.label = l.core.label
  right_label : q.2.core.label = r.core.label
  left_shield : q.1.core.shield = l.core.shield
  right_shield : q.2.core.shield = r.core.shield
  left_bullet_zero : q.1.core.bullet = ⟨0, by omega⟩
  right_bullet_zero : q.2.core.bullet = ⟨0, by omega⟩
  left_signal_one : q.1.core.signal_B = ⟨1, by omega⟩
  right_signal_one : q.2.core.signal_B = ⟨1, by omega⟩
  left_reset_false : q.1.core.reset_cmd = false
  right_reset_exact : q.2.core.reset_cmd = !r.core.echo
  right_echo_false : q.2.core.echo = false
  left_echo_exact : q.1.core.echo =
    if l.core.leader = true then false
    else if r.core.label = ⟨psi - 1, by omega⟩ then true
    else l.core.echo

/-- Abstract post-Algorithm-14 contract for the rooted leader-sink suffix.
Keeping this boundary independent of the complete pre-CHECK prefix prevents
later endpoint projections from reducing that prefix. -/
structure AuthorizedLeaderSinkPostOutput
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  left_neutral : ComparisonNeutral q.1.core
  right_neutral : ComparisonNeutral q.2.core
  left_leader : q.1.core.leader = false
  right_leader : q.2.core.leader = true
  left_label : q.1.core.label = l.core.label
  right_label : q.2.core.label = r.core.label
  left_shield : q.1.core.shield = l.core.shield
  right_shield : q.2.core.shield = r.core.shield
  left_bullet_zero : q.1.core.bullet = ⟨0, by omega⟩
  right_bullet_zero : q.2.core.bullet = ⟨0, by omega⟩
  left_signal_one : q.1.core.signal_B = ⟨1, by omega⟩
  right_signal_one : q.2.core.signal_B = ⟨1, by omega⟩
  left_reset : q.1.core.reset_cmd = l.core.reset_cmd
  right_reset : q.2.core.reset_cmd = r.core.reset_cmd
  left_echo : q.1.core.echo = l.core.echo
  right_echo : q.2.core.echo = r.core.echo

/-- Minimal rooted closing projection needed by the subsequent leader fire.
Unlike `AuthorizedLeaderSinkClosingOutput`, it does not retain either output
bullet or reset/echo field: the barrier movement branch clears any responder
bullet before delivering the returning signal. -/
structure AuthorizedLeaderSinkSignalOutput
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  left_neutral : ComparisonNeutral q.1.core
  right_neutral : ComparisonNeutral q.2.core
  left_leader : q.1.core.leader = false
  right_leader : q.2.core.leader = true
  left_label : q.1.core.label = l.core.label
  right_label : q.2.core.label = r.core.label
  right_signal_one : q.2.core.signal_B = ⟨1, by omega⟩

/-- Transport the weak closing projection backward across an equality of
output pairs.  Keeping the pair abstract prevents dependent rewriting from
unfolding the complete wall transition merely to expose its outer head. -/
private theorem authorizedLeaderSinkSignalOutput_pullback
    {hpsi : psi > 0}
    {l r : AuthorizedAgentState psi}
    {q q' : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hqq' : q = q')
    (hq' : AuthorizedLeaderSinkSignalOutput hpsi l r q') :
    AuthorizedLeaderSinkSignalOutput hpsi l r q :=
  Eq.mpr
    (congrArg (fun x => AuthorizedLeaderSinkSignalOutput hpsi l r x) hqq')
    hq'

/-- Rebase the weak closing projection from intermediate endpoint labels to
the original edge labels.  All other fields are independent of the input pair. -/
private theorem authorizedLeaderSinkSignalOutput_rebase
    {hpsi : psi > 0}
    {l r a b : AuthorizedAgentState psi}
    {q : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : AuthorizedLeaderSinkSignalOutput hpsi a b q)
    (hla : a.core.label = l.core.label)
    (hrb : b.core.label = r.core.label) :
    AuthorizedLeaderSinkSignalOutput hpsi l r q := {
  left_neutral := h.left_neutral
  right_neutral := h.right_neutral
  left_leader := h.left_leader
  right_leader := h.right_leader
  left_label := h.left_label.trans hla
  right_label := h.right_label.trans hrb
  right_signal_one := h.right_signal_one
}

/-- Pull comparison neutrality back across an opaque state equality. -/
private theorem comparisonNeutral_pullback
    {a b : AgentState psi} (hab : a = b)
    (hb : ComparisonNeutral b) : ComparisonNeutral a :=
  Eq.mpr (congrArg ComparisonNeutral hab) hb

/-- Bounded/path-stall lift of the exact rooted closing-edge output. -/
structure LeaderSinkClosingOutput
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop where
  left_neutral : ComparisonNeutral q.1.core.erase.core
  right_neutral : ComparisonNeutral q.2.core.erase.core
  left_leader : q.1.core.erase.core.leader = false
  right_leader : q.2.core.erase.core.leader = true
  left_label : q.1.core.erase.core.label = l.core.erase.core.label
  right_label : q.2.core.erase.core.label = r.core.erase.core.label
  left_shield : q.1.core.erase.core.shield = l.core.erase.core.shield
  right_shield : q.2.core.erase.core.shield = r.core.erase.core.shield
  left_bullet_zero : q.1.core.erase.core.bullet = ⟨0, by omega⟩
  right_bullet_zero : q.2.core.erase.core.bullet = ⟨0, by omega⟩
  left_signal_one : q.1.core.erase.core.signal_B = ⟨1, by omega⟩
  right_signal_one : q.2.core.erase.core.signal_B = ⟨1, by omega⟩
  left_reset_false : q.1.core.erase.core.reset_cmd = false
  right_reset_exact : q.2.core.erase.core.reset_cmd =
    !r.core.erase.core.echo
  right_echo_false : q.2.core.erase.core.echo = false
  left_echo_exact : q.1.core.erase.core.echo =
    if l.core.erase.core.leader = true then false
    else if r.core.erase.core.label = ⟨psi - 1, by omega⟩ then true
    else l.core.erase.core.echo

/-- Bounded/path-stall lift of the minimal rooted signal-delivery
projection.  This is the exact local contract consumed by the global closing
step. -/
structure LeaderSinkSignalOutput
    (hpsi : psi > 0) (l r : ExpiringAgentState psi kappa tau)
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop where
  left_neutral : ComparisonNeutral q.1.core.erase.core
  right_neutral : ComparisonNeutral q.2.core.erase.core
  left_leader : q.1.core.erase.core.leader = false
  right_leader : q.2.core.erase.core.leader = true
  left_label : q.1.core.erase.core.label = l.core.erase.core.label
  right_label : q.2.core.erase.core.label = r.core.erase.core.label
  right_signal_one : q.2.core.erase.core.signal_B = ⟨1, by omega⟩

private theorem authorizedPeaceViewPair_left_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    PeaceView.ofState a.1.core = PeaceView.ofState b.1.core :=
  congrArg Prod.fst h

private theorem authorizedPeaceViewPair_right_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    PeaceView.ofState a.2.core = PeaceView.ofState b.2.core :=
  congrArg Prod.snd h

private theorem authorizedRawPeaceViewPair_left_eq
    {a : AuthorizedAgentState psi × AuthorizedAgentState psi}
    {b : AgentState psi × AgentState psi}
    (h : authorizedPeaceViewPair a = peaceViewPair b) :
    PeaceView.ofState a.1.core = PeaceView.ofState b.1 :=
  congrArg Prod.fst h

private theorem authorizedRawPeaceViewPair_right_eq
    {a : AuthorizedAgentState psi × AuthorizedAgentState psi}
    {b : AgentState psi × AgentState psi}
    (h : authorizedPeaceViewPair a = peaceViewPair b) :
    PeaceView.ofState a.2.core = PeaceView.ofState b.2 :=
  congrArg Prod.snd h

private theorem authorizedPeaceViewPair_core_eq
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authorizedPeaceViewPair a = authorizedPeaceViewPair b) :
    peaceViewPair (a.1.core, a.2.core) =
      peaceViewPair (b.1.core, b.2.core) :=
  h

private theorem peaceViewPair_left_eq
    {a b : AgentState psi × AgentState psi}
    (h : peaceViewPair a = peaceViewPair b) :
    PeaceView.ofState a.1 = PeaceView.ofState b.1 :=
  congrArg Prod.fst h

private theorem peaceViewPair_right_eq
    {a b : AgentState psi × AgentState psi}
    (h : peaceViewPair a = peaceViewPair b) :
    PeaceView.ofState a.2 = PeaceView.ofState b.2 :=
  congrArg Prod.snd h

private theorem peaceView_leader_eq
    {a b : AgentState psi}
    (h : PeaceView.ofState a = PeaceView.ofState b) :
    a.leader = b.leader :=
  congrArg PeaceView.leader h

private theorem peaceView_label_eq
    {a b : AgentState psi}
    (h : PeaceView.ofState a = PeaceView.ofState b) :
    a.label = b.label :=
  congrArg PeaceView.label h

private theorem peaceView_shield_eq
    {a b : AgentState psi}
    (h : PeaceView.ofState a = PeaceView.ofState b) :
    a.shield = b.shield :=
  congrArg PeaceView.shield h

private theorem peaceView_signal_eq
    {a b : AgentState psi}
    (h : PeaceView.ofState a = PeaceView.ofState b) :
    a.signal_B = b.signal_B :=
  congrArg PeaceView.signal_B h

private theorem peaceView_bullet_eq
    {a b : AgentState psi}
    (h : PeaceView.ofState a = PeaceView.ofState b) :
    a.bullet = b.bullet :=
  congrArg PeaceView.bullet h

private theorem authorizedReconcile_left_core_eq
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    (authorizedReconcile f l r).1.core = (f l.core r.core).1 := by
  rfl

private theorem authorizedReconcile_right_core_eq
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    (authorizedReconcile f l r).2.core = (f l.core r.core).2 := by
  rfl

private theorem normalTail_eq_postSuppress
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
    wallSweepPreCheckResetNormalTail hpsi kappa l r =
      authorizedPostSuppress hpsi after.1 after.2 := by
  rfl

private theorem leaderSinkNormalTail_eq_postSuppress
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
    wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r =
      authorizedPostSuppressLeaderSink hpsi after.1 after.2 := by
  rfl

/-! ## Rooted closing edge -/

attribute [local irreducible] authorizedPostSuppressLeaderSink

/-- The post-Algorithm-14 leader-sink suffix delivers the returning signal on
a barrier edge without any bullet or responder-signal premise: nonalignment
clears a positive responder bullet before the signal stage. -/
theorem authorizedPostSuppressLeaderSink_closing_signal
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hLNeutral : ComparisonNeutral l.core)
    (hRNeutral : ComparisonNeutral r.core)
    (hbarrier : isBarrier hpsi l.core r.core)
    (hlFollower : l.core.leader = false)
    (hrLeader : r.core.leader = true)
    (hrZero : r.core.label = ⟨0, hpsi⟩)
    (hlSignal : l.core.signal_B = ⟨1, by omega⟩) :
    AuthorizedLeaderSinkSignalOutput hpsi l r
      (authorizedPostSuppressLeaderSink hpsi l r) := by
  let nc := eliminateLeadersNoCollisionLeaderSink hpsi l.core r.core
  have hnc :=
    eliminateLeadersNoCollisionLeaderSink_closing_signal_fields
      hpsi l.core r.core hbarrier hlFollower hrLeader hlSignal
  change nc.1.leader = false ∧ nc.2.leader = true ∧
      nc.1.label = l.core.label ∧ nc.2.label = r.core.label ∧
      nc.2.signal_B = ⟨1, by omega⟩ at hnc
  rcases hnc with
    ⟨hncLLeader, hncRLeader, hncLLabel, hncRLabel, hncRSignal⟩
  have hzero : nc.2.leader = true → nc.2.label = ⟨0, hpsi⟩ := by
    intro _
    exact hncRLabel.trans hrZero
  have hpostPV := authorizedPostSuppressLeaderSink_peaceView_eq
    hpsi l r hzero
  have hpostLView := authorizedRawPeaceViewPair_left_eq hpostPV
  have hpostRView := authorizedRawPeaceViewPair_right_eq hpostPV
  have hpostNeutral := authorizedPostSuppressLeaderSink_neutral
    hpsi l r hLNeutral hRNeutral
  exact {
    left_neutral := hpostNeutral.1
    right_neutral := hpostNeutral.2
    left_leader := (peaceView_leader_eq hpostLView).trans hncLLeader
    right_leader := (peaceView_leader_eq hpostRView).trans hncRLeader
    left_label := (peaceView_label_eq hpostLView).trans hncLLabel
    right_label := (peaceView_label_eq hpostRView).trans hncRLabel
    right_signal_one :=
      (peaceView_signal_eq hpostRView).trans hncRSignal }

/-- The leader-sink Algorithm-15/WRITE suffix consumes an abstract neutral
closing-edge state.  It changes only the two signal fields and frames all
other fields needed by the reset circuit. -/
theorem authorizedPostSuppressLeaderSink_closing
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hLNeutral : ComparisonNeutral l.core)
    (hRNeutral : ComparisonNeutral r.core)
    (hlFollower : l.core.leader = false)
    (hrLeader : r.core.leader = true)
    (hrZero : r.core.label = ⟨0, hpsi⟩)
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩)
    (hlSignal : l.core.signal_B = ⟨1, by omega⟩)
    (hrSignal : r.core.signal_B = ⟨0, by omega⟩) :
    AuthorizedLeaderSinkPostOutput hpsi l r
      (authorizedPostSuppressLeaderSink hpsi l r) := by
  let nc := eliminateLeadersNoCollisionLeaderSink hpsi l.core r.core
  have hnc := eliminateLeadersNoCollisionLeaderSink_closing_fields
    hpsi l.core r.core hlFollower hrLeader hlSignal hrSignal
      hlBullet hrBullet
  change nc.1.signal_B = ⟨1, by omega⟩ ∧
      nc.2.signal_B = ⟨1, by omega⟩ ∧
      nc.1.leader = false ∧ nc.2.leader = true ∧
      nc.1.label = l.core.label ∧ nc.2.label = r.core.label ∧
      nc.1.shield = l.core.shield ∧ nc.2.shield = r.core.shield ∧
      nc.1.bullet = ⟨0, by omega⟩ ∧
      nc.2.bullet = ⟨0, by omega⟩ at hnc
  rcases hnc with ⟨hncLSignal, hncRSignal, hncLLeader, hncRLeader,
    hncLLabel, hncRLabel, hncLShield, hncRShield,
    hncLBullet, hncRBullet⟩
  have hzero : nc.2.leader = true → nc.2.label = ⟨0, hpsi⟩ := by
    intro _
    exact hncRLabel.trans hrZero
  have hpostPV := authorizedPostSuppressLeaderSink_peaceView_eq
    hpsi l r hzero
  have hpostLView := authorizedRawPeaceViewPair_left_eq hpostPV
  have hpostRView := authorizedRawPeaceViewPair_right_eq hpostPV
  have hpostNeutral := authorizedPostSuppressLeaderSink_neutral
    hpsi l r hLNeutral hRNeutral
  have hpostControl := authorizedPostSuppressLeaderSink_resetEchoPair hpsi l r
  exact {
    left_neutral := hpostNeutral.1
    right_neutral := hpostNeutral.2
    left_leader := (peaceView_leader_eq hpostLView).trans hncLLeader
    right_leader := (peaceView_leader_eq hpostRView).trans hncRLeader
    left_label := (peaceView_label_eq hpostLView).trans hncLLabel
    right_label := (peaceView_label_eq hpostRView).trans hncRLabel
    left_shield := (peaceView_shield_eq hpostLView).trans hncLShield
    right_shield := (peaceView_shield_eq hpostRView).trans hncRShield
    left_bullet_zero := (peaceView_bullet_eq hpostLView).trans hncLBullet
    right_bullet_zero := (peaceView_bullet_eq hpostRView).trans hncRBullet
    left_signal_one := (peaceView_signal_eq hpostLView).trans hncLSignal
    right_signal_one := (peaceView_signal_eq hpostRView).trans hncRSignal
    left_reset := congrArg (fun v => v.1.1) hpostControl
    right_reset := congrArg (fun v => v.2.1) hpostControl
    left_echo := congrArg (fun v => v.1.2) hpostControl
    right_echo := congrArg (fun v => v.2.2) hpostControl
  }

/-- At the nondivisible predecessor-to-leader closing edge, the returning
signal reaches the responder leader without any bullet or responder-signal
premise.  The repaired prefix is used only for its source/PeaceView frame and
neutral Algorithm-14 output; the barrier branch clears any obstructing bullet
before delivery. -/
theorem wallSweepPreCheckResetLeaderSinkNormalTail_closing_signal
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hbarrier : isBarrier hpsi l.core r.core)
    (hlReset : l.core.reset_cmd = true)
    (hlFollower : l.core.leader = false)
    (hrLeader : r.core.leader = true)
    (hrZero : r.core.label = ⟨0, hpsi⟩)
    (hlSignal : l.core.signal_B = ⟨1, by omega⟩) :
    AuthorizedLeaderSinkSignalOutput hpsi l r
      (wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r) := by
  let pre : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    sourcePreStage hpsi kappa l r
  let raw : AgentState psi × AgentState psi :=
    suppressSigResetKill hpsi pre.1.core pre.2.core
  have hpre : AuthorizedSourcePreOutput l r pre := by
    simpa only [pre] using sourcePreStage_frame_of_responder_leader
      hpsi kappa l r hrLeader (.inr hlReset)
  have hcontrol : RawSuppressControlOutput hpsi l r raw := by
    simpa only [raw] using
      suppressSigResetKill_control_of_frame hpsi l r pre hpre
  let after : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hafterEq : after = authorizedReconcile
      (suppressSigResetKill hpsi) pre.1 pre.2 := by
    simpa only [after, pre, sourcePreStage] using
      wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
        hpsi kappa l r
  have hafterLCore : after.1.core = raw.1 := by
    exact (congrArg (fun q => q.1.core) hafterEq).trans
      (by
        simpa only [raw] using authorizedReconcile_left_core_eq
          (suppressSigResetKill hpsi) pre.1 pre.2)
  have hafterRCore : after.2.core = raw.2 := by
    exact (congrArg (fun q => q.2.core) hafterEq).trans
      (by
        simpa only [raw] using authorizedReconcile_right_core_eq
          (suppressSigResetKill hpsi) pre.1 pre.2)
  have hafterLNeutral : ComparisonNeutral after.1.core :=
    comparisonNeutral_pullback hafterLCore hcontrol.left_neutral
  have hafterRNeutral : ComparisonNeutral after.2.core :=
    comparisonNeutral_pullback hafterRCore hcontrol.right_neutral
  have hrawPV : peaceViewPair raw =
      peaceViewPair (pre.1.core, pre.2.core) := by
    simpa only [raw] using
      suppressSigResetKill_peaceViewPair hpsi pre.1.core pre.2.core
  have hpreCorePV := authorizedPeaceViewPair_core_eq hpre.peace
  have hafterLView : PeaceView.ofState after.1.core =
      PeaceView.ofState l.core :=
    (congrArg PeaceView.ofState hafterLCore).trans
      ((peaceViewPair_left_eq hrawPV).trans
        (peaceViewPair_left_eq hpreCorePV))
  have hafterRView : PeaceView.ofState after.2.core =
      PeaceView.ofState r.core :=
    (congrArg PeaceView.ofState hafterRCore).trans
      ((peaceViewPair_right_eq hrawPV).trans
        (peaceViewPair_right_eq hpreCorePV))
  have hafterBarrier : isBarrier hpsi after.1.core after.2.core := by
    have hleftLabel := peaceView_label_eq hafterLView
    have hrightLabel := peaceView_label_eq hafterRView
    simpa [isBarrier, hleftLabel, hrightLabel] using hbarrier
  have hpost := authorizedPostSuppressLeaderSink_closing_signal
    hpsi after.1 after.2 hafterLNeutral hafterRNeutral
      hafterBarrier
      ((peaceView_leader_eq hafterLView).trans hlFollower)
      ((peaceView_leader_eq hafterRView).trans hrLeader)
      ((peaceView_label_eq hafterRView).trans hrZero)
      ((peaceView_signal_eq hafterLView).trans hlSignal)
  have houtPost : AuthorizedLeaderSinkSignalOutput hpsi l r
      (authorizedPostSuppressLeaderSink hpsi after.1 after.2) := by
    exact authorizedLeaderSinkSignalOutput_rebase hpost
      (peaceView_label_eq hafterLView)
      (peaceView_label_eq hafterRView)
  have htailEq : wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r =
      authorizedPostSuppressLeaderSink hpsi after.1 after.2 := by
    simpa only [after] using
      leaderSinkNormalTail_eq_postSuppress hpsi kappa l r
  exact authorizedLeaderSinkSignalOutput_pullback htailEq houtPost

/-- At the nondivisible predecessor-to-leader closing edge, the separately
named leader-sink repair delivers the returning absence signal to the leader.
The premise records the actual closing geometry, although the local sink rule
needs only the endpoint roles and fields. -/
theorem wallSweepPreCheckResetLeaderSinkNormalTail_closing_delivers
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (_hbarrier : isBarrier hpsi l.core r.core)
    (hlReset : l.core.reset_cmd = true)
    (hlFollower : l.core.leader = false)
    (hrLeader : r.core.leader = true)
    (hrZero : r.core.label = ⟨0, hpsi⟩)
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩)
    (hlSignal : l.core.signal_B = ⟨1, by omega⟩)
    (hrSignal : r.core.signal_B = ⟨0, by omega⟩) :
    AuthorizedLeaderSinkClosingOutput hpsi l r
      (wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r) := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hpre := sourcePreStage_frame_of_responder_leader
    hpsi kappa l r hrLeader (.inr hlReset)
  have hafter : AuthorizedAfterSuppressNoFireOutput hpsi l r after := by
    simpa only [after] using
      wallSweepPreCheckResetNormalAfterSuppress_source_frame_of_pre
        hpsi kappa l r hpre hlBullet hrBullet
  have hpost := authorizedPostSuppressLeaderSink_closing
    hpsi after.1 after.2 hafter.left_neutral hafter.right_neutral
      (hafter.left_leader.trans hlFollower)
      (hafter.right_leader.trans hrLeader)
      (hafter.right_label.trans hrZero)
      hafter.left_bullet_zero hafter.right_bullet_zero
      (hafter.left_signal.trans hlSignal)
      (hafter.right_signal.trans hrSignal)
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  have htailEq : tail =
      authorizedPostSuppressLeaderSink hpsi after.1 after.2 := by
    simpa only [tail, after] using
      leaderSinkNormalTail_eq_postSuppress hpsi kappa l r
  change AuthorizedLeaderSinkClosingOutput hpsi l r tail
  rw [htailEq]
  exact {
    left_neutral := hpost.left_neutral
    right_neutral := hpost.right_neutral
    left_leader := hpost.left_leader
    right_leader := hpost.right_leader
    left_label := hpost.left_label.trans hafter.left_label
    right_label := hpost.right_label.trans hafter.right_label
    left_shield := hpost.left_shield.trans hafter.left_shield
    right_shield := hpost.right_shield.trans hafter.right_shield
    left_bullet_zero := hpost.left_bullet_zero
    right_bullet_zero := hpost.right_bullet_zero
    left_signal_one := hpost.left_signal_one
    right_signal_one := hpost.right_signal_one
    left_reset_false := hpost.left_reset.trans hafter.left_reset_false
    right_reset_exact := hpost.right_reset.trans hafter.right_reset_exact
    right_echo_false := hpost.right_echo.trans hafter.right_echo_false
    left_echo_exact := hpost.left_echo.trans hafter.left_echo_exact
  }

/-- Priority openness selects the minimal rooted signal-delivery tail, whose
neutral output makes the proof-only birth marker inert. -/
theorem wallSweepPreCheckResetLeaderSinkAuthorized_closing_signal
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hbarrier : isBarrier hpsi l.core r.core)
    (hlReset : l.core.reset_cmd = true)
    (hlFollower : l.core.leader = false)
    (hrLeader : r.core.leader = true)
    (hrZero : r.core.label = ⟨0, hpsi⟩)
    (hlSignal : l.core.signal_B = ⟨1, by omega⟩) :
    AuthorizedLeaderSinkSignalOutput hpsi l r
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  have htail : AuthorizedLeaderSinkSignalOutput hpsi l r tail := by
    simpa only [tail] using
      wallSweepPreCheckResetLeaderSinkNormalTail_closing_signal
        hpsi kappa l r hbarrier hlReset hlFollower hrLeader hrZero
          hlSignal
  have hmark := markLeaderBirth_eq_of_neutral born tail
    htail.left_neutral htail.right_neutral
  have heq :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r = markLeaderBirth born tail at heq
  rw [heq, hmark]
  exact htail

/-- Priority openness selects the rooted normal tail, and its neutral output
makes the proof-only birth marker inert. -/
theorem wallSweepPreCheckResetLeaderSinkAuthorized_closing_delivers
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hbarrier : isBarrier hpsi l.core r.core)
    (hlReset : l.core.reset_cmd = true)
    (hlFollower : l.core.leader = false)
    (hrLeader : r.core.leader = true)
    (hrZero : r.core.label = ⟨0, hpsi⟩)
    (hlBullet : l.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.bullet = ⟨0, by omega⟩)
    (hlSignal : l.core.signal_B = ⟨1, by omega⟩)
    (hrSignal : r.core.signal_B = ⟨0, by omega⟩) :
    AuthorizedLeaderSinkClosingOutput hpsi l r
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  have htail : AuthorizedLeaderSinkClosingOutput hpsi l r tail := by
    simpa only [tail] using
      wallSweepPreCheckResetLeaderSinkNormalTail_closing_delivers
        hpsi kappa l r hbarrier hlReset hlFollower hrLeader hrZero
          hlBullet hrBullet hlSignal hrSignal
  have hmark := markLeaderBirth_eq_of_neutral born tail
    htail.left_neutral htail.right_neutral
  have heq :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r = markLeaderBirth born tail at heq
  rw [heq, hmark]
  exact htail

/-- Bounded reification and path-stall expiry preserve the minimal closing
projection; no initiator-bullet fact is introduced or consumed. -/
theorem wallSweepPreCheckResetLeaderSinkPathStall_closing_signal
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hbarrier : isBarrier hpsi l.core.erase.core r.core.erase.core)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hlFollower : l.core.erase.core.leader = false)
    (hrLeader : r.core.erase.core.leader = true)
    (hrZero : r.core.erase.core.label = ⟨0, hpsi⟩)
    (hlSignal : l.core.erase.core.signal_B = ⟨1, by omega⟩) :
    LeaderSinkSignalOutput hpsi l r
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha := wallSweepPreCheckResetLeaderSinkAuthorized_closing_signal
    hpsi kappa l.core.erase r.core.erase hopen hbarrier hlReset
      hlFollower hrLeader hrZero hlSignal
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
  have hbaseLNeutral : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hL]
    exact ha.left_neutral
  have hbaseRNeutral : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hR]
    exact ha.right_neutral
  have hLf := deletionPriorityExpireOne_neutral_fields l lBase hbaseLNeutral
  have hRf := deletionPriorityExpireOne_neutral_fields r rBase hbaseRNeutral
  have hRPV := deletionPriorityExpireOne_peaceView_frame r rBase
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages]
  refine {
    left_neutral := hLf.1
    right_neutral := hRf.1
    left_leader := hLf.2.1.trans ?_
    right_leader := hRf.2.1.trans ?_
    left_label := hLf.2.2.1.trans ?_
    right_label := hRf.2.2.1.trans ?_
    right_signal_one := (congrArg PeaceView.signal_B hRPV).trans ?_ }
  · change bounded.1.erase.core.leader = false
    rw [hL]
    exact ha.left_leader
  · change bounded.2.erase.core.leader = true
    rw [hR]
    exact ha.right_leader
  · change bounded.1.erase.core.label = l.core.erase.core.label
    rw [hL]
    exact ha.left_label
  · change bounded.2.erase.core.label = r.core.erase.core.label
    rw [hR]
    exact ha.right_label
  · change bounded.2.erase.core.signal_B = ⟨1, by omega⟩
    rw [hR]
    exact ha.right_signal_one

/-- Bounded reification and path-stall expiry preserve the exact signal
delivery and every framed closing-edge field. -/
theorem wallSweepPreCheckResetLeaderSinkPathStall_closing_delivers
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hbarrier : isBarrier hpsi l.core.erase.core r.core.erase.core)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hlFollower : l.core.erase.core.leader = false)
    (hrLeader : r.core.erase.core.leader = true)
    (hrZero : r.core.erase.core.label = ⟨0, hpsi⟩)
    (hlBullet : l.core.erase.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.erase.core.bullet = ⟨0, by omega⟩)
    (hlSignal : l.core.erase.core.signal_B = ⟨1, by omega⟩)
    (hrSignal : r.core.erase.core.signal_B = ⟨0, by omega⟩) :
    LeaderSinkClosingOutput hpsi l r
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha := wallSweepPreCheckResetLeaderSinkAuthorized_closing_delivers
    hpsi kappa l.core.erase r.core.erase hopen hbarrier hlReset
      hlFollower hrLeader hrZero hlBullet hrBullet hlSignal hrSignal
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
  have hbaseLNeutral : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hL]
    exact ha.left_neutral
  have hbaseRNeutral : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hR]
    exact ha.right_neutral
  have hLf := deletionPriorityExpireOne_neutral_fields l lBase hbaseLNeutral
  have hRf := deletionPriorityExpireOne_neutral_fields r rBase hbaseRNeutral
  have hLPV := deletionPriorityExpireOne_peaceView_frame l lBase
  have hRPV := deletionPriorityExpireOne_peaceView_frame r rBase
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages]
  refine {
    left_neutral := hLf.1
    right_neutral := hRf.1
    left_leader := hLf.2.1.trans ?_
    right_leader := hRf.2.1.trans ?_
    left_label := hLf.2.2.1.trans ?_
    right_label := hRf.2.2.1.trans ?_
    left_shield := hLf.2.2.2.2.2.trans ?_
    right_shield := hRf.2.2.2.2.2.trans ?_
    left_bullet_zero := (congrArg PeaceView.bullet hLPV).trans ?_
    right_bullet_zero := (congrArg PeaceView.bullet hRPV).trans ?_
    left_signal_one := (congrArg PeaceView.signal_B hLPV).trans ?_
    right_signal_one := (congrArg PeaceView.signal_B hRPV).trans ?_
    left_reset_false := hLf.2.2.2.1.trans ?_
    right_reset_exact := hRf.2.2.2.1.trans ?_
    right_echo_false := hRf.2.2.2.2.1.trans ?_
    left_echo_exact := hLf.2.2.2.2.1.trans ?_
  }
  · change bounded.1.erase.core.leader = false
    rw [hL]
    exact ha.left_leader
  · change bounded.2.erase.core.leader = true
    rw [hR]
    exact ha.right_leader
  · change bounded.1.erase.core.label = l.core.erase.core.label
    rw [hL]
    exact ha.left_label
  · change bounded.2.erase.core.label = r.core.erase.core.label
    rw [hR]
    exact ha.right_label
  · change bounded.1.erase.core.shield = l.core.erase.core.shield
    rw [hL]
    exact ha.left_shield
  · change bounded.2.erase.core.shield = r.core.erase.core.shield
    rw [hR]
    exact ha.right_shield
  · change bounded.1.erase.core.bullet = ⟨0, by omega⟩
    rw [hL]
    exact ha.left_bullet_zero
  · change bounded.2.erase.core.bullet = ⟨0, by omega⟩
    rw [hR]
    exact ha.right_bullet_zero
  · change bounded.1.erase.core.signal_B = ⟨1, by omega⟩
    rw [hL]
    exact ha.left_signal_one
  · change bounded.2.erase.core.signal_B = ⟨1, by omega⟩
    rw [hR]
    exact ha.right_signal_one
  · change bounded.1.erase.core.reset_cmd = false
    rw [hL]
    exact ha.left_reset_false
  · change bounded.2.erase.core.reset_cmd = !r.core.erase.core.echo
    rw [hR]
    exact ha.right_reset_exact
  · change bounded.2.erase.core.echo = false
    rw [hR]
    exact ha.right_echo_false
  · change bounded.1.erase.core.echo = _
    rw [hL]
    exact ha.left_echo_exact

/-- The reset-aware integrated transition has the same minimal closing
projection.  Responder-leader agreement removes its extra P-prime wall, while
the initiator bullet remains entirely unconstrained. -/
theorem wallSweepResetProbePreCheckResetLeaderSinkPathStall_closing_signal
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hbarrier : isBarrier hpsi l.core.erase.core r.core.erase.core)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hlFollower : l.core.erase.core.leader = false)
    (hrLeader : r.core.erase.core.leader = true)
    (hrZero : r.core.erase.core.label = ⟨0, hpsi⟩)
    (hlSignal : l.core.erase.core.signal_B = ⟨1, by omega⟩) :
    LeaderSinkSignalOutput hpsi l r
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r) := by
  rw [
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_right_leader
      hpsi kappa tau l r hrLeader]
  exact wallSweepPreCheckResetLeaderSinkPathStall_closing_signal
    hpsi l r hopen hbarrier hlReset hlFollower hrLeader hrZero
      hlSignal

/-- The reset-aware integrated transition has the same exact closing output.
On this edge the responder is the existing leader, so the reset-aware
P-prime wall is definitionally redundant after the responder-leader agreement
proved in `WallSweepPreCheckResetContracts`. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_closing_delivers
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hbarrier : isBarrier hpsi l.core.erase.core r.core.erase.core)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hlFollower : l.core.erase.core.leader = false)
    (hrLeader : r.core.erase.core.leader = true)
    (hrZero : r.core.erase.core.label = ⟨0, hpsi⟩)
    (hlBullet : l.core.erase.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.erase.core.bullet = ⟨0, by omega⟩)
    (hlSignal : l.core.erase.core.signal_B = ⟨1, by omega⟩)
    (hrSignal : r.core.erase.core.signal_B = ⟨0, by omega⟩) :
    LeaderSinkClosingOutput hpsi l r
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r) := by
  rw [
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_right_leader
      hpsi kappa tau l r hrLeader]
  exact wallSweepPreCheckResetLeaderSinkPathStall_closing_delivers
    hpsi l r hopen hbarrier hlReset hlFollower hrLeader hrZero
      hlBullet hrBullet hlSignal hrSignal

/-! ## Duplicate-leader unshielding edge

The closing edge above only *delivers* the absence signal.  This section
records the separate local contract for the next interaction: a label-zero
responder leader that already carries `signal_B = 1` keeps its leader bit and
its host label but loses its shield.  Nothing here creates a live bullet,
delivers one, or deletes any leader; those remain independent obligations. -/

/-- Exact local output of the rooted leader-sink repair at an already
signalled label-zero duplicate leader.  Algorithm 15 retains the leader bit
and the host label and clears the shield; the surrounding output stays
comparison-neutral so the proof-only birth marker is inert. -/
structure AuthorizedLeaderSinkUnshieldOutput
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  left_neutral : ComparisonNeutral q.1.core
  right_neutral : ComparisonNeutral q.2.core
  right_leader : q.2.core.leader = true
  right_label_zero : q.2.core.label = ⟨0, hpsi⟩
  right_unshielded : q.2.core.shield = false

/-- Bounded/path-stall lift of the duplicate-leader unshielding output. -/
structure LeaderSinkUnshieldOutput
    (hpsi : psi > 0)
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop where
  left_neutral : ComparisonNeutral q.1.core.erase.core
  right_neutral : ComparisonNeutral q.2.core.erase.core
  right_leader : q.2.core.erase.core.leader = true
  right_label_zero : q.2.core.erase.core.label = ⟨0, hpsi⟩
  right_unshielded : q.2.core.erase.core.shield = false

/-- Transport the unshielding output backward across an equality of output
pairs.  Keeping the pair abstract prevents dependent rewriting from unfolding
the complete wall transition merely to expose its outer head. -/
private theorem authorizedLeaderSinkUnshieldOutput_pullback
    {hpsi : psi > 0}
    {q q' : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hqq' : q = q')
    (hq' : AuthorizedLeaderSinkUnshieldOutput hpsi q') :
    AuthorizedLeaderSinkUnshieldOutput hpsi q :=
  Eq.mpr
    (congrArg (fun x => AuthorizedLeaderSinkUnshieldOutput hpsi x) hqq')
    hq'

/-- Complete repaired transition, normal-tail form.  When the initiator still
carries the sweep source (it is a leader or holds a reset token) and the
responder is a label-zero leader already carrying the absence signal, the
whole repaired pre-CHECK prefix, repaired Algorithm 14, Algorithm 15 and the
gated WRITE suffix leave the responder a leader at label zero and remove its
shield.  The zero-label premise is essential: gated WRITE migrates a nonzero
responder leader to the initiator.  No barrier, bullet, echo or
responder-shield premise is consumed. -/
theorem wallSweepPreCheckResetLeaderSinkNormalTail_responder_zero_unshield
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hrLeader : r.core.leader = true)
    (hrZero : r.core.label = ⟨0, hpsi⟩)
    (hrSignal : r.core.signal_B = ⟨1, by omega⟩) :
    AuthorizedLeaderSinkUnshieldOutput hpsi
      (wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r) := by
  let pre : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    sourcePreStage hpsi kappa l r
  let raw : AgentState psi × AgentState psi :=
    suppressSigResetKill hpsi pre.1.core pre.2.core
  have hpre : AuthorizedSourcePreOutput l r pre := by
    simpa only [pre] using sourcePreStage_frame_of_responder_leader
      hpsi kappa l r hrLeader hsource
  have hcontrol : RawSuppressControlOutput hpsi l r raw := by
    simpa only [raw] using
      suppressSigResetKill_control_of_frame hpsi l r pre hpre
  let after : AuthorizedAgentState psi × AuthorizedAgentState psi :=
    wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hafterEq : after = authorizedReconcile
      (suppressSigResetKill hpsi) pre.1 pre.2 := by
    simpa only [after, pre, sourcePreStage] using
      wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
        hpsi kappa l r
  have hafterLCore : after.1.core = raw.1 := by
    exact (congrArg (fun q => q.1.core) hafterEq).trans
      (by
        simpa only [raw] using authorizedReconcile_left_core_eq
          (suppressSigResetKill hpsi) pre.1 pre.2)
  have hafterRCore : after.2.core = raw.2 := by
    exact (congrArg (fun q => q.2.core) hafterEq).trans
      (by
        simpa only [raw] using authorizedReconcile_right_core_eq
          (suppressSigResetKill hpsi) pre.1 pre.2)
  have hafterLNeutral : ComparisonNeutral after.1.core :=
    comparisonNeutral_pullback hafterLCore hcontrol.left_neutral
  have hafterRNeutral : ComparisonNeutral after.2.core :=
    comparisonNeutral_pullback hafterRCore hcontrol.right_neutral
  have hrawPV : peaceViewPair raw =
      peaceViewPair (pre.1.core, pre.2.core) := by
    simpa only [raw] using
      suppressSigResetKill_peaceViewPair hpsi pre.1.core pre.2.core
  have hpreCorePV := authorizedPeaceViewPair_core_eq hpre.peace
  have hafterRView : PeaceView.ofState after.2.core =
      PeaceView.ofState r.core :=
    (congrArg PeaceView.ofState hafterRCore).trans
      ((peaceViewPair_right_eq hrawPV).trans
        (peaceViewPair_right_eq hpreCorePV))
  have hun :=
    authorizedPostSuppressLeaderSink_responder_zero_signal_one_unshielded
      hpsi after.1 after.2
      ((peaceView_leader_eq hafterRView).trans hrLeader)
      ((peaceView_label_eq hafterRView).trans hrZero)
      ((peaceView_signal_eq hafterRView).trans hrSignal)
  have hneutral := authorizedPostSuppressLeaderSink_neutral
    hpsi after.1 after.2 hafterLNeutral hafterRNeutral
  have htailEq : wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r =
      authorizedPostSuppressLeaderSink hpsi after.1 after.2 := by
    simpa only [after] using
      leaderSinkNormalTail_eq_postSuppress hpsi kappa l r
  exact authorizedLeaderSinkUnshieldOutput_pullback htailEq
    { left_neutral := hneutral.1
      right_neutral := hneutral.2
      right_leader := hun.1
      right_label_zero := hun.2.1
      right_unshielded := hun.2.2 }

/-- Priority openness selects the rooted normal tail, and the neutral
unshielding output makes the proof-only birth marker inert. -/
theorem wallSweepPreCheckResetLeaderSinkAuthorized_responder_zero_unshield
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hrLeader : r.core.leader = true)
    (hrZero : r.core.label = ⟨0, hpsi⟩)
    (hrSignal : r.core.signal_B = ⟨1, by omega⟩) :
    AuthorizedLeaderSinkUnshieldOutput hpsi
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  have htail : AuthorizedLeaderSinkUnshieldOutput hpsi tail := by
    simpa only [tail] using
      wallSweepPreCheckResetLeaderSinkNormalTail_responder_zero_unshield
        hpsi kappa l r hsource hrLeader hrZero hrSignal
  have hmark := markLeaderBirth_eq_of_neutral born tail
    htail.left_neutral htail.right_neutral
  have heq :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r = markLeaderBirth born tail at heq
  rw [heq, hmark]
  exact htail

/-- Bounded reification and path-stall expiry preserve the duplicate-leader
unshielding output.  Deletion-priority expiry frames leader, label and shield
exactly, so no field of the conclusion is weakened. -/
theorem wallSweepPreCheckResetLeaderSinkPathStall_responder_zero_unshield
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hsource : l.core.erase.core.leader = true ∨
      l.core.erase.core.reset_cmd = true)
    (hrLeader : r.core.erase.core.leader = true)
    (hrZero : r.core.erase.core.label = ⟨0, hpsi⟩)
    (hrSignal : r.core.erase.core.signal_B = ⟨1, by omega⟩) :
    LeaderSinkUnshieldOutput hpsi
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha := wallSweepPreCheckResetLeaderSinkAuthorized_responder_zero_unshield
    hpsi kappa l.core.erase r.core.erase hopen hsource hrLeader hrZero
      hrSignal
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
  have hbaseLNeutral : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hL]
    exact ha.left_neutral
  have hbaseRNeutral : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hR]
    exact ha.right_neutral
  have hLf := deletionPriorityExpireOne_neutral_fields l lBase hbaseLNeutral
  have hRf := deletionPriorityExpireOne_neutral_fields r rBase hbaseRNeutral
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages]
  refine {
    left_neutral := hLf.1
    right_neutral := hRf.1
    right_leader := hRf.2.1.trans ?_
    right_label_zero := hRf.2.2.1.trans ?_
    right_unshielded := hRf.2.2.2.2.2.trans ?_ }
  · change bounded.2.erase.core.leader = true
    rw [hR]
    exact ha.right_leader
  · change bounded.2.erase.core.label = ⟨0, hpsi⟩
    rw [hR]
    exact ha.right_label_zero
  · change bounded.2.erase.core.shield = false
    rw [hR]
    exact ha.right_unshielded

/-- Exact endpoint fact about the rooted closing edge: afterwards the
initiator endpoint is a follower with no reset token, so it satisfies neither
disjunct of the source premise required by the PeaceView route
`sourcePreStage_frame_of_responder_leader`.

This blocks only that route.  It does **not** block a same-edge second
interaction: the source-free frames below discharge the source premise
altogether, and
`preCheckResetLeaderSink_sameEdge_replay_unshields_duplicate` proves the
same-edge replay outright. -/
theorem wallSweepPreCheckResetLeaderSinkPathStall_closing_output_no_source
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hbarrier : isBarrier hpsi l.core.erase.core r.core.erase.core)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hlFollower : l.core.erase.core.leader = false)
    (hrLeader : r.core.erase.core.leader = true)
    (hrZero : r.core.erase.core.label = ⟨0, hpsi⟩)
    (hlBullet : l.core.erase.core.bullet = ⟨0, by omega⟩)
    (hrBullet : r.core.erase.core.bullet = ⟨0, by omega⟩)
    (hlSignal : l.core.erase.core.signal_B = ⟨1, by omega⟩)
    (hrSignal : r.core.erase.core.signal_B = ⟨0, by omega⟩) :
    ¬ ((wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau l r).1.core.erase.core.leader = true ∨
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau l r).1.core.erase.core.reset_cmd = true) := by
  have hclose := wallSweepPreCheckResetLeaderSinkPathStall_closing_delivers
    hpsi l r hopen hbarrier hlReset hlFollower hrLeader hrZero
      hlBullet hrBullet hlSignal hrSignal
  rintro (hh | hh)
  · rw [hclose.left_leader] at hh
    simp at hh
  · rw [hclose.left_reset_false] at hh
    simp at hh

/-- Local **two-edge** contract for a separated label-zero duplicate leader.
It composes two *pair-level* facts, not two consecutive interactions of one
schedule:

* the first edge is the nondivisible closing edge, where a reset-carrying
  follower initiator delivers the returning absence signal to the label-zero
  responder leader (`wallSweepPreCheckResetLeaderSinkPathStall_closing_signal`);
* the second edge is a separate edge whose responder is exactly that
  post-closing state and whose initiator `m` is assumed to carry the sweep
  source; there Algorithm 15 clears the shield.

`m` is an abstract initiator, **not** the post-state of the first edge's
initiator, so this statement alone is two local edges rather than one path.

Superseded as the route to a real schedule: the source premise it carries is
unnecessary, and
`preCheckResetLeaderSink_sameEdge_replay_unshields_duplicate` below gives the
literal configuration-level two-interaction word `[e, e]` on a single directed
edge.  This theorem is retained only as the general pair-level statement for
an arbitrary source-carrying initiator.

The conclusion is only that a label-zero duplicate leader survives unshielded
at label zero; nothing here produces a live bullet, delivers one, or deletes
any leader. -/
theorem wallSweepPreCheckResetLeaderSinkPathStall_two_edge_duplicate_unshield
    (hpsi : psi > 0)
    (l r m : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hbarrier : isBarrier hpsi l.core.erase.core r.core.erase.core)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hlFollower : l.core.erase.core.leader = false)
    (hrLeader : r.core.erase.core.leader = true)
    (hrZero : r.core.erase.core.label = ⟨0, hpsi⟩)
    (hlSignal : l.core.erase.core.signal_B = ⟨1, by omega⟩)
    (hmOpen : WallPriorityOpen m
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r).2)
    (hmSource : m.core.erase.core.leader = true ∨
      m.core.erase.core.reset_cmd = true) :
    let q := wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    LeaderSinkUnshieldOutput hpsi
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau m q.2) := by
  have hstep := wallSweepPreCheckResetLeaderSinkPathStall_closing_signal
    hpsi l r hopen hbarrier hlReset hlFollower hrLeader hrZero hlSignal
  exact wallSweepPreCheckResetLeaderSinkPathStall_responder_zero_unshield
    hpsi m
    (wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r).2
    hmOpen hmSource hstep.right_leader
      (hstep.right_label.trans hrZero) hstep.right_signal_one

/-! ## Source-free duplicate-leader unshielding

The source premise above is an artefact of the PeaceView route, not of the
transition.  No stage of the repaired pre-CHECK prefix writes `signal_B` at
all: `wallSweepPreCheckResetNormalAfterSuppress_bulletFieldPair` frames
`⟨shield, bullet, signal_B⟩` at both endpoints of the complete prefix and
repaired Algorithm 14 with no premise whatever, and
`wallSweepPreCheckResetNormalAfterSuppress_responder_zero_anchor` frames the
responder leader and its host label from the responder-zero anchor alone.
Together they discharge the initiator leader/reset source premise, and with it
the obstruction recorded in
`wallSweepPreCheckResetLeaderSinkPathStall_closing_output_no_source`. -/

/-- Comparison neutrality at both endpoints of one edge opens deletion
priority on that edge. -/
private theorem wallPriorityOpen_of_neutral
    (l r : ExpiringAgentState psi kappa tau)
    (hl : ComparisonNeutral l.core.erase.core)
    (hr : ComparisonNeutral r.core.erase.core) :
    WallPriorityOpen l r := by
  unfold WallPriorityOpen AuthorizedPriorityOpen
  refine ⟨deletionActive_normalize_false _ ?_,
    deletionActive_normalize_false _ ?_⟩
  · simp [deletionActive, pathPresent, hl.1, hl.2.1]
  · simp [deletionActive, pathPresent, hr.1, hr.2.1]

/-- Endpoint bookkeeping for firing the same directed edge twice.  The
responder slot of the two-interaction word `[e, e]` is the responder output of
the second firing, whose inputs are the two outputs of the first. -/
private theorem sameEdge_replay_endpoints
    (ring : DirectedRing n) (hn : 1 < n)
    (T : ExpiringAgentState psi kappa tau → ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau)
    (C : EConfig n psi kappa tau) (e : Fin n) :
    let j := ring.rightNeighbor e
    let D1 := localStep ring T C e
    D1 e = (T (C e) (C j)).1 ∧ D1 j = (T (C e) (C j)).2 ∧
      runLocalSchedule ring T C [e, e] j = (T (D1 e) (D1 j)).2 := by
  have hje : ring.rightNeighbor e ≠ e :=
    rightNeighbor_ne_self_of_one_lt ring hn e
  refine ⟨?_, ?_, ?_⟩
  · simp [localStep]
  · simp [localStep, hje]
  · simp [runLocalSchedule, localStep, hje]

/-- **Configuration-level literal schedule.**  Firing the same directed edge
`e` twice — the executable interaction word `[e, e]` — carries the physical
agent at the fixed ring position `ring.rightNeighbor e` from a shielded
label-zero duplicate leader to an unshielded one.

The first firing is the nondivisible closing edge: a reset-carrying follower
initiator holding the absence signal delivers that signal to the label-zero
responder leader.  The second firing is the same edge again, with the
initiator now being exactly the first firing's initiator output; its
deletion-priority openness is derived from the first firing's comparison
neutrality rather than assumed.

Responder identity is positional and fixed: the agent at index
`ring.rightNeighbor e` is the same physical agent in `C` and in the final
configuration.  Nothing here produces a live bullet, delivers one, deletes any
leader, or moves the final protected singleton. -/
theorem preCheckResetLeaderSink_sameEdge_replay_unshields_duplicate
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hopen : WallPriorityOpen (C e) (C (ring.rightNeighbor e)))
    (hbarrier : isBarrier hpsi (C e).core.erase.core
      (C (ring.rightNeighbor e)).core.erase.core)
    (hlReset : (C e).core.erase.core.reset_cmd = true)
    (hlFollower : (C e).core.erase.core.leader = false)
    (hrLeader : (C (ring.rightNeighbor e)).core.erase.core.leader = true)
    (hrZero : (C (ring.rightNeighbor e)).core.erase.core.label = ⟨0, hpsi⟩)
    (hlSignal : (C e).core.erase.core.signal_B = ⟨1, by omega⟩) :
    let D := runLocalSchedule ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
      C [e, e]
    (D (ring.rightNeighbor e)).core.erase.core.leader = true ∧
      (D (ring.rightNeighbor e)).core.erase.core.label = ⟨0, hpsi⟩ ∧
      (D (ring.rightNeighbor e)).core.erase.core.shield = false := by
  dsimp only
  obtain ⟨hD1e, hD1j, hrun⟩ := sameEdge_replay_endpoints ring hn
    (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau) C e
  have hstep1 := wallSweepPreCheckResetLeaderSinkPathStall_closing_signal
    hpsi (C e) (C (ring.rightNeighbor e)) hopen hbarrier hlReset hlFollower
      hrLeader hrZero hlSignal
  have hopen2 : WallPriorityOpen
      (localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
        C e e)
      (localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
        C e (ring.rightNeighbor e)) := by
    rw [hD1e, hD1j]
    exact wallPriorityOpen_of_neutral _ _ hstep1.left_neutral
      hstep1.right_neutral
  have hLeader2 :
      (localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
        C e (ring.rightNeighbor e)).core.erase.core.leader = true := by
    rw [hD1j]
    exact hstep1.right_leader
  have hZero2 :
      (localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
        C e (ring.rightNeighbor e)).core.erase.core.label = ⟨0, hpsi⟩ := by
    rw [hD1j]
    exact hstep1.right_label.trans hrZero
  have hSignal2 :
      (localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
        C e (ring.rightNeighbor e)).core.erase.core.signal_B =
        ⟨1, by omega⟩ := by
    rw [hD1j]
    exact hstep1.right_signal_one
  rw [hrun]
  exact
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_zero_unshield
      hpsi _ _ hopen2 hLeader2 hZero2 hSignal2

/-- The reset-aware non-wrap endpoint crosses its nondivisible closing edge
and reaches exactly the weak boundary needed by the outgoing leader fire.
This theorem consumes no shield or echo premise. -/
theorem resetAwareRootedClosingReady_close_step
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (h : ResetAwareRootedClosingReady hpsi ring leader C) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C (groupOffset ring leader (n - 1))
    ResetAwareLeaderFireReady hpsi ring leader D := by
  let e := groupOffset ring leader (n - 1)
  let j := groupOffset ring leader n
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hneighbor : ring.rightNeighbor e = j := by
    have hnEq : n - 1 + 1 = n := by omega
    simpa only [e, j, hnEq] using
      rightNeighbor_groupOffset ring leader (n - 1)
  have hjLeader : j = leader := by
    apply Fin.ext
    simp [j]
  have hene : e ≠ j := by
    rw [← hneighbor]
    exact Ne.symm (rightNeighbor_ne_self_of_one_lt ring hn e)
  have heNotLeader : e ≠ leader := by
    intro heq
    exact hene (heq.trans hjLeader.symm)
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [hneighbor] using
      WallPriorityOpen.of_noActiveDeletion C h.no_active ring e
  have hbarrier : isBarrier hpsi
      (C e).core.erase.core (C j).core.erase.core := by
    intro hclosingAlign
    apply hndvd
    apply dvd_of_all_successor_labels hpsi ring
      (fun i => (C i).core.erase.core)
    intro i
    by_cases hie : i = e
    · subst i
      rw [hneighbor]
      exact hclosingAlign
    · have hrightNotLeader : ring.rightNeighbor i ≠ leader := by
        intro hright
        apply hie
        apply rightNeighbor_injective ring
        calc
          ring.rightNeighbor i = leader := hright
          _ = j := hjLeader.symm
          _ = ring.rightNeighbor e := hneighbor.symm
      exact h.successor_label_of_right_ne i hrightNotLeader
  have hlFollower : (C e).core.erase.core.leader = false :=
    h.unique_leader e heNotLeader
  have hrLeader : (C j).core.erase.core.leader = true := by
    rw [hjLeader]
    exact h.leader_alive
  have hlocal : LeaderSinkSignalOutput hpsi (C e) (C j) q := by
    exact
      wallSweepResetProbePreCheckResetLeaderSinkPathStall_closing_signal
        hpsi (C e) (C j) hopen hbarrier h.predecessor_reset
          hlFollower hrLeader (by simpa [hjLeader] using h.leader_zero)
          h.predecessor_signal_one
  have hleft : D e = q.1 := by
    simp [D, q, T, localStep, hneighbor]
  have hright : D j = q.2 := by
    simp [D, q, T, localStep, hneighbor, Ne.symm hene]
  have hoff : ∀ i, i ≠ e → i ≠ j → D i = C i := by
    intro i hie hij
    simp [D, T, localStep, hie, hneighbor, hij]
  have hleaderAt : ∀ i,
      (D i).core.erase.core.leader = (C i).core.erase.core.leader := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hlocal.left_leader.trans hlFollower.symm
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_leader.trans hrLeader.symm
      · rw [hoff i hie hij]
  have hlabelAt : ∀ i,
      (D i).core.erase.core.label = (C i).core.erase.core.label := by
    intro i
    by_cases hie : i = e
    · subst i; rw [hleft]; exact hlocal.left_label
    · by_cases hij : i = j
      · subst i; rw [hright]; exact hlocal.right_label
      · rw [hoff i hie hij]
  have hneutralAt : ∀ i, ComparisonNeutral
      (D i).core.erase.core := by
    intro i
    by_cases hie : i = e
    · subst i; rw [hleft]; exact hlocal.left_neutral
    · by_cases hij : i = j
      · subst i; rw [hright]; exact hlocal.right_neutral
      · rw [hoff i hie hij]
        exact h.comparison_neutral i
  have hnoFreeD : noFreeBarrier hpsi ring
      (fun i => (D i).core.erase.core) := by
    intro i
    dsimp only
    intro hbarrierD
    have hbarrierC : isBarrier hpsi
        (C i).core.erase.core
        (C (ring.rightNeighbor i)).core.erase.core := by
      intro halignC
      apply hbarrierD
      apply Fin.ext
      have hrightLabel := congrArg Fin.val
        (hlabelAt (ring.rightNeighbor i))
      have hleftLabel := congrArg Fin.val (hlabelAt i)
      have halignVal := congrArg Fin.val halignC
      dsimp only at halignVal ⊢
      calc
        (D (ring.rightNeighbor i)).core.erase.core.label.val =
            (C (ring.rightNeighbor i)).core.erase.core.label.val :=
          hrightLabel
        _ = ((C i).core.erase.core.label.val + 1) % psi := halignVal
        _ = ((D i).core.erase.core.label.val + 1) % psi := by
          rw [hleftLabel]
    exact (hleaderAt (ring.rightNeighbor i)).trans
      (h.no_free_barrier i hbarrierC)
  change ResetAwareLeaderFireReady hpsi ring leader D
  exact {
    leader_alive := by
      rw [hleaderAt leader]
      exact h.leader_alive
    leader_zero := by
      rw [hlabelAt leader]
      exact h.leader_zero
    unique_leader := by
      intro i hi
      rw [hleaderAt i]
      exact h.unique_leader i hi
    no_free_barrier := hnoFreeD
    comparison_neutral := hneutralAt
    leader_signal_one := by
      rw [← hjLeader, hright]
      exact hlocal.right_signal_one }

/-- A source-covered leader carrying `signal_B=1` fires through the complete
authorized corrected transition.  The responder echo may be either Boolean
value; it affects reset disposal but not the Algorithm-15 fire fields. -/
theorem wallSweepPreCheckResetAuthorized_leader_fire
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hlLeader : l.core.leader = true)
    (hlSignal : l.core.signal_B = ⟨1, by omega⟩)
    (hrFollower : r.core.leader = false) :
    AuthorizedLeaderFireOutput hpsi l r
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := sourcePreStage hpsi kappa l r
  have hpre := sourcePreStage_frame hpsi kappa l r halign (.inl hlLeader)
  change AuthorizedSourcePreOutput l r pre at hpre
  rcases hpre with ⟨hprePV, hpreSource, _, _, _⟩
  let raw := suppressSigResetKill hpsi pre.1.core pre.2.core
  have hrawNeutral : ComparisonNeutral raw.1 ∧ ComparisonNeutral raw.2 := by
    by_cases he : pre.2.core.echo = true
    · have hc := suppressSigResetKill_source_echo_collision
        hpsi pre.1.core pre.2.core hpreSource he
      exact ⟨hc.1, hc.2.1⟩
    · have he0 : pre.2.core.echo = false := by
        cases h : pre.2.core.echo
        · rfl
        · exact (he h).elim
      rcases hpreSource with hleader | hreset
      · exact suppressSigResetKill_leader_reseed_neutral
          hpsi pre.1.core pre.2.core hleader he0
      · have hn := suppressSigResetKill_handoff
          hpsi pre.1.core pre.2.core hreset he0
        exact ⟨hn.1, hn.2.1⟩
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hafterEq := wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
    hpsi kappa l r
  change after = authorizedReconcile
    (suppressSigResetKill hpsi) pre.1 pre.2 at hafterEq
  have hafterLCore : after.1.core = raw.1 := by
    exact (congrArg (fun q => q.1.core) hafterEq).trans
      (authorizedReconcile_left_core_eq
        (suppressSigResetKill hpsi) pre.1 pre.2)
  have hafterRCore : after.2.core = raw.2 := by
    exact (congrArg (fun q => q.2.core) hafterEq).trans
      (authorizedReconcile_right_core_eq
        (suppressSigResetKill hpsi) pre.1 pre.2)
  have hafterNeutral : ComparisonNeutral after.1.core ∧
      ComparisonNeutral after.2.core := by
    exact ⟨by rw [hafterLCore]; exact hrawNeutral.1,
      by rw [hafterRCore]; exact hrawNeutral.2⟩
  have hpreCorePV := authorizedPeaceViewPair_core_eq hprePV
  have hrawPV0 := suppressSigResetKill_peaceViewPair
    hpsi pre.1.core pre.2.core
  have hrawPV : peaceViewPair raw =
      peaceViewPair (pre.1.core, pre.2.core) := by
    simpa only [raw] using hrawPV0
  have hrawLView := peaceViewPair_left_eq hrawPV
  have hrawRView := peaceViewPair_right_eq hrawPV
  have hpreLView := peaceViewPair_left_eq hpreCorePV
  have hpreRView := peaceViewPair_right_eq hpreCorePV
  have hafterLView : PeaceView.ofState after.1.core =
      PeaceView.ofState l.core :=
    (congrArg PeaceView.ofState hafterLCore).trans
      (hrawLView.trans hpreLView)
  have hafterRView : PeaceView.ofState after.2.core =
      PeaceView.ofState r.core :=
    (congrArg PeaceView.ofState hafterRCore).trans
      (hrawRView.trans hpreRView)
  have hafterLLeader := peaceView_leader_eq hafterLView
  have hafterRLeader := peaceView_leader_eq hafterRView
  have hafterLLabel := peaceView_label_eq hafterLView
  have hafterRLabel := peaceView_label_eq hafterRView
  have hafterLSignal := peaceView_signal_eq hafterLView
  have hleftLeader : after.1.core.leader = true :=
    hafterLLeader.trans hlLeader
  have hleftSignal : after.1.core.signal_B = ⟨1, by omega⟩ :=
    hafterLSignal.trans hlSignal
  have hrightFollower : after.2.core.leader = false :=
    hafterRLeader.trans hrFollower
  have hfire := noCollision_left_fire_fields
    hpsi after.1.core after.2.core hleftLeader hleftSignal
  have hncLeader := noCollision_left_fire_leader
    hpsi after.1.core after.2.core hleftLeader hleftSignal
  have hncLabels := noCollision_labels hpsi after.1.core after.2.core
  have hncFollower := (eliminateLeadersNoCollision_responder_leader_eq
    hpsi after.1.core after.2.core).trans hrightFollower
  have hzero :
      let q := eliminateLeadersNoCollision hpsi after.1.core after.2.core
      q.2.leader = true → q.2.label = ⟨0, hpsi⟩ := by
    dsimp only
    intro hleader
    have hbad : (false : Bool) = true := hncFollower.symm.trans hleader
    simp at hbad
  have hpostPV := authorizedPostSuppress_peaceView_eq_noCollision
    hpsi after.1 after.2 hzero
  have hpostLView := authorizedRawPeaceViewPair_left_eq hpostPV
  have hpostRView := authorizedRawPeaceViewPair_right_eq hpostPV
  have hpostControl := postSuppress_normalReset_handoff
    hpsi after.1 after.2 hafterNeutral.1 hafterNeutral.2
  dsimp only at hpostControl
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  have htailEq : tail = authorizedPostSuppress hpsi after.1 after.2 := by
    simpa only [tail, after] using normalTail_eq_postSuppress hpsi kappa l r
  have htailOut : AuthorizedLeaderFireOutput hpsi l r tail := by
    rw [htailEq]
    exact {
      left_neutral := hpostControl.1
      right_neutral := hpostControl.2.1
      left_leader :=
        (peaceView_leader_eq hpostLView).trans hncLeader
      right_follower :=
        (peaceView_leader_eq hpostRView).trans hncFollower
      left_label := (peaceView_label_eq hpostLView).trans
        (hncLabels.1.trans hafterLLabel)
      right_label := (peaceView_label_eq hpostRView).trans
        (hncLabels.2.trans hafterRLabel)
      left_shield_true :=
        (peaceView_shield_eq hpostLView).trans hfire.1
      left_signal_zero :=
        (peaceView_signal_eq hpostLView).trans hfire.2
    }
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have hmark := markLeaderBirth_eq_of_neutral born tail
    htailOut.left_neutral htailOut.right_neutral
  have heq := wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
    hpsi kappa l r hopen
  change wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at heq
  rw [heq, hmark]
  exact htailOut

/-- Bounded reification and path-stall expiry retain the protected fire
fields and the neutral comparison outputs. -/
theorem wallSweepPreCheckResetPathStall_leader_fire
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (halign : r.core.erase.core.label =
      ⟨(l.core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩)
    (hlLeader : l.core.erase.core.leader = true)
    (hlSignal : l.core.erase.core.signal_B = ⟨1, by omega⟩)
    (hrFollower : r.core.erase.core.leader = false) :
    LeaderFireOutput hpsi l r
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha := wallSweepPreCheckResetAuthorized_leader_fire
    hpsi kappa l.core.erase r.core.erase hopen halign
      hlLeader hlSignal hrFollower
  have he := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change bounded.1.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  change bounded.2.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbaseLNeutral : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hL]
    exact ha.left_neutral
  have hbaseRNeutral : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hR]
    exact ha.right_neutral
  have hLf := deletionPriorityExpireOne_neutral_fields l lBase hbaseLNeutral
  have hRf := deletionPriorityExpireOne_neutral_fields r rBase hbaseRNeutral
  have hLPV := deletionPriorityExpireOne_peaceView_frame l lBase
  rw [wallSweepPreCheckResetPathStall_eq_expiryStages]
  refine {
    left_neutral := hLf.1
    right_neutral := hRf.1
    left_leader := hLf.2.1.trans ?_
    right_follower := hRf.2.1.trans ?_
    left_label := hLf.2.2.1.trans ?_
    right_label := hRf.2.2.1.trans ?_
    left_shield_true := hLf.2.2.2.2.2.trans ?_
    left_signal_zero := (congrArg PeaceView.signal_B hLPV).trans ?_
  }
  · change bounded.1.erase.core.leader = true
    rw [hL]
    exact ha.left_leader
  · change bounded.2.erase.core.leader = false
    rw [hR]
    exact ha.right_follower
  · change bounded.1.erase.core.label = l.core.erase.core.label
    rw [hL]
    exact ha.left_label
  · change bounded.2.erase.core.label = r.core.erase.core.label
    rw [hR]
    exact ha.right_label
  · change bounded.1.erase.core.shield = true
    rw [hL]
    exact ha.left_shield_true
  · change bounded.1.erase.core.signal_B = ⟨0, by omega⟩
    rw [hL]
    exact ha.left_signal_zero

private theorem leaderSinkNormalTail_eq_of_after_responder_follower
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hrFollower :
      (wallSweepPreCheckResetNormalAfterSuppress
        hpsi kappa l r).2.core.leader = false) :
    wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r =
      wallSweepPreCheckResetNormalTail hpsi kappa l r := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hsink := leaderSinkNormalTail_eq_postSuppress hpsi kappa l r
  have hold := normalTail_eq_postSuppress hpsi kappa l r
  change wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r =
    authorizedPostSuppressLeaderSink hpsi after.1 after.2 at hsink
  change wallSweepPreCheckResetNormalTail hpsi kappa l r =
    authorizedPostSuppress hpsi after.1 after.2 at hold
  have hpost := authorizedPostSuppressLeaderSink_eq_of_responder_follower
    hpsi after.1 after.2 hrFollower
  exact hsink.trans (hpost.trans hold.symm)

/-- On a leader-to-follower edge the complete rooted repair is exactly the
established transition.  This is the formal noninterference boundary for the
single new responder-leader guard. -/
theorem wallSweepPreCheckResetLeaderSinkAuthorized_eq_of_leader_follower
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hlLeader : l.core.leader = true)
    (hrFollower : r.core.leader = false) :
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition hpsi kappa l r =
      wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have hpre := sourcePreStage_frame hpsi kappa l r halign (.inl hlLeader)
  have hafterFollower : after.2.core.leader = false :=
    (wallSweepPreCheckResetNormalAfterSuppress_right_leader_of_pre
      hpsi kappa l r hpre).trans hrFollower
  have htail := leaderSinkNormalTail_eq_of_after_responder_follower
    hpsi kappa l r hafterFollower
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have hnew :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  have hold := wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
    hpsi kappa l r hopen
  change wallSweepPreCheckResetLeaderSinkAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born
      (wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r) at hnew
  change wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) at hold
  exact hnew.trans ((congrArg (markLeaderBirth born) htail).trans hold.symm)

/-- The rooted repair therefore reuses the established protected leader-fire
contract on the next outgoing leader edge. -/
theorem wallSweepPreCheckResetLeaderSinkAuthorized_leader_fire
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hlLeader : l.core.leader = true)
    (hlSignal : l.core.signal_B = ⟨1, by omega⟩)
    (hrFollower : r.core.leader = false) :
    AuthorizedLeaderFireOutput hpsi l r
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r) := by
  rw [wallSweepPreCheckResetLeaderSinkAuthorized_eq_of_leader_follower
    hpsi kappa l r hopen halign hlLeader hrFollower]
  exact wallSweepPreCheckResetAuthorized_leader_fire
    hpsi kappa l r hopen halign hlLeader hlSignal hrFollower

/-- Bounded reification and expiry lift the reused leader-fire contract for
the rooted repair. -/
theorem wallSweepPreCheckResetLeaderSinkPathStall_leader_fire
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (halign : r.core.erase.core.label =
      ⟨(l.core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩)
    (hlLeader : l.core.erase.core.leader = true)
    (hlSignal : l.core.erase.core.signal_B = ⟨1, by omega⟩)
    (hrFollower : r.core.erase.core.leader = false) :
    LeaderFireOutput hpsi l r
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha := wallSweepPreCheckResetLeaderSinkAuthorized_leader_fire
    hpsi kappa l.core.erase r.core.erase hopen halign
      hlLeader hlSignal hrFollower
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
  have hbaseLNeutral : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hL]
    exact ha.left_neutral
  have hbaseRNeutral : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hR]
    exact ha.right_neutral
  have hLf := deletionPriorityExpireOne_neutral_fields l lBase hbaseLNeutral
  have hRf := deletionPriorityExpireOne_neutral_fields r rBase hbaseRNeutral
  have hLPV := deletionPriorityExpireOne_peaceView_frame l lBase
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages]
  refine {
    left_neutral := hLf.1
    right_neutral := hRf.1
    left_leader := hLf.2.1.trans ?_
    right_follower := hRf.2.1.trans ?_
    left_label := hLf.2.2.1.trans ?_
    right_label := hRf.2.2.1.trans ?_
    left_shield_true := hLf.2.2.2.2.2.trans ?_
    left_signal_zero := (congrArg PeaceView.signal_B hLPV).trans ?_
  }
  · change bounded.1.erase.core.leader = true
    rw [hL]
    exact ha.left_leader
  · change bounded.2.erase.core.leader = false
    rw [hR]
    exact ha.right_follower
  · change bounded.1.erase.core.label = l.core.erase.core.label
    rw [hL]
    exact ha.left_label
  · change bounded.2.erase.core.label = r.core.erase.core.label
    rw [hR]
    exact ha.right_label
  · change bounded.1.erase.core.shield = true
    rw [hL]
    exact ha.left_shield_true
  · change bounded.1.erase.core.signal_B = ⟨0, by omega⟩
    rw [hL]
    exact ha.left_signal_zero

/-- The reset-aware integrated transition has the same protected leader-fire
output.  Its additional reset-source probe wall is redundant on an edge
initiated by the existing leader. -/
theorem wallSweepResetProbePreCheckResetLeaderSinkPathStall_leader_fire
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (halign : r.core.erase.core.label =
      ⟨(l.core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩)
    (hlLeader : l.core.erase.core.leader = true)
    (hlSignal : l.core.erase.core.signal_B = ⟨1, by omega⟩)
    (hrFollower : r.core.erase.core.leader = false) :
    LeaderFireOutput hpsi l r
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r) := by
  rw [
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
      hpsi kappa tau l r hlLeader]
  exact wallSweepPreCheckResetLeaderSinkPathStall_leader_fire
    hpsi l r hopen halign hlLeader hlSignal hrFollower

private theorem rooted_groupOffset_zero_eq
    (ring : DirectedRing n) (leader : Fin n) :
    groupOffset ring leader 0 = leader := by
  apply Fin.ext
  simp [groupOffset, Nat.mod_eq_of_lt leader.isLt]

private theorem rooted_groupOffset_n_eq
    (ring : DirectedRing n) (leader : Fin n) :
    groupOffset ring leader n = leader := by
  apply Fin.ext
  simp [groupOffset, Nat.add_mod_right, Nat.mod_eq_of_lt leader.isLt]

/-- On a nondivisible ring, the rooted zero-rank pass uses ordinary
source/follower behavior on its first `n-1` edges and the leader-sink rule on
the unique closing edge.  The signal and reset both return to the leader
without assuming cyclic alignment at that edge. -/
theorem preCheckResetLeaderSink_rooted_zeroRank_fullPass_exact
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : RootedClockwiseRetryReady hpsi ring leader C)
    (hzero : clockwiseEchoRank ring leader C = 0) :
    RootedLeaderSinkRetryDoneExact hpsi ring leader
      (clockwiseAttemptConfig
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau)
        ring leader C n) := by
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let pre := clockwiseAttemptConfig T ring leader C (n - 1)
  let e := groupOffset ring leader (n - 1)
  let j := groupOffset ring leader n
  let q := T (pre e) (pre j)
  let D := localStep ring T pre e
  have hpre := rootedClockwiseZeroPrefix_reaches
    hpsi ring hn leader C hready hzero (n - 1) (by omega)
  change RootedClockwiseZeroPrefixState
    hpsi ring leader C pre (n - 1) at hpre
  have heBound : n - 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    have hnEq : n - 1 + 1 = n := by omega
    simpa only [e, j, hnEq] using
      rightNeighbor_groupOffset ring leader (n - 1)
  have hjLeader : j = leader := rooted_groupOffset_n_eq ring leader
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      (by omega : 0 < n) (by omega : n - 1 ≠ 0)
    exact fun heq =>
      hne (heq.trans (rooted_groupOffset_zero_eq ring leader).symm)
  have hene : e ≠ j := by
    rw [hjLeader]
    exact heNotLeader
  have hopen : WallPriorityOpen (pre e) (pre j) := by
    simpa [hneighbor] using
      WallPriorityOpen.of_noActiveDeletion pre hpre.ready.no_active ring e
  have hsource : (pre e).core.erase.core.leader = true ∨
      (pre e).core.erase.core.reset_cmd = true := by
    rcases hpre.source with hzeroSource | hresetSource
    · omega
    · exact .inr hresetSource.2
  have hlReset : (pre e).core.erase.core.reset_cmd = true := by
    rcases hsource with hleader | hreset
    · have hfollower := hpre.ready.unique_leader e heNotLeader
      rw [hfollower] at hleader
      simp at hleader
    · exact hreset
  have hlFollower : (pre e).core.erase.core.leader = false :=
    hpre.ready.unique_leader e heNotLeader
  have hrLeader : (pre j).core.erase.core.leader = true := by
    rw [hjLeader]
    exact hpre.ready.leader_alive
  have hrZero : (pre j).core.erase.core.label = ⟨0, hpsi⟩ := by
    rw [hjLeader]
    exact hpre.ready.leader_zero
  have hlSignal : (pre e).core.erase.core.signal_B = ⟨1, by omega⟩ :=
    hpre.frontier_signal_one (by omega) heBound
  have hrSignal : (pre j).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hjLeader]
    exact hpre.ready.leader_signal_zero
  have hpreLeaderEcho : (pre j).core.erase.core.echo = false := by
    rw [hjLeader]
    exact hpre.leader_echo_false (by omega)
  have hbarrier : isBarrier hpsi
      (pre e).core.erase.core (pre j).core.erase.core := by
    intro hclosingAlign
    apply hndvd
    apply dvd_of_all_successor_labels hpsi ring
      (fun i => (pre i).core.erase.core)
    intro i
    by_cases hie : i = e
    · subst i
      rw [hneighbor]
      exact hclosingAlign
    · have hrightNotLeader : ring.rightNeighbor i ≠ leader := by
        intro hright
        apply hie
        apply rightNeighbor_injective ring
        calc
          ring.rightNeighbor i = leader := hright
          _ = j := hjLeader.symm
          _ = ring.rightNeighbor e := hneighbor.symm
      exact hpre.ready.successor_label_of_right_ne i hrightNotLeader
  have hlocal : LeaderSinkClosingOutput hpsi (pre e) (pre j) q := by
    exact wallSweepPreCheckResetLeaderSinkPathStall_closing_delivers
      hpsi (pre e) (pre j) hopen hbarrier hlReset hlFollower
        hrLeader hrZero (hpre.ready.bullets_zero e)
        (hpre.ready.bullets_zero j) hlSignal hrSignal
  have hleft : D e = q.1 := by
    simp [D, q, localStep, hneighbor]
  have hright : D j = q.2 := by
    simp [D, q, localStep, hneighbor, Ne.symm hene]
  have hoff : ∀ i, i ≠ e → i ≠ j → D i = pre i := by
    intro i hie hij
    simp [D, localStep, hie, hneighbor, hij]
  have hleaderAt : ∀ i, (D i).core.erase.core.leader =
      (pre i).core.erase.core.leader := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hlocal.left_leader.trans hlFollower.symm
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_leader.trans hrLeader.symm
      · rw [hoff i hie hij]
  have hlabelAt : ∀ i, (D i).core.erase.core.label =
      (pre i).core.erase.core.label := by
    intro i
    by_cases hie : i = e
    · subst i; rw [hleft]; exact hlocal.left_label
    · by_cases hij : i = j
      · subst i; rw [hright]; exact hlocal.right_label
      · rw [hoff i hie hij]
  have hshieldAt : ∀ i, (D i).core.erase.core.shield =
      (pre i).core.erase.core.shield := by
    intro i
    by_cases hie : i = e
    · subst i; rw [hleft]; exact hlocal.left_shield
    · by_cases hij : i = j
      · subst i; rw [hright]; exact hlocal.right_shield
      · rw [hoff i hie hij]
  have hbulletAt : ∀ i,
      (D i).core.erase.core.bullet = ⟨0, by omega⟩ := by
    intro i
    by_cases hie : i = e
    · subst i; rw [hleft]; exact hlocal.left_bullet_zero
    · by_cases hij : i = j
      · subst i; rw [hright]; exact hlocal.right_bullet_zero
      · rw [hoff i hie hij]
        exact hpre.ready.bullets_zero i
  have hpreNeutral : ∀ i, ComparisonNeutral
      (pre i).core.erase.core := by
    intro i
    let k := cwDist ring leader i
    have hkBound : k < n := cwDist_lt ring leader i
    have hpos : groupOffset ring leader k = i := by
      simpa [groupOffset, cwPos] using cwPos_cwDist ring leader i
    rw [← hpos]
    exact hpre.visited_neutral k (by omega) (by omega)
  have hneutralD : ∀ i, ComparisonNeutral
      (D i).core.erase.core := by
    intro i
    by_cases hie : i = e
    · subst i; rw [hleft]; exact hlocal.left_neutral
    · by_cases hij : i = j
      · subst i; rw [hright]; exact hlocal.right_neutral
      · rw [hoff i hie hij]
        exact hpreNeutral i
  have hfollowerReset : ∀ i, i ≠ leader →
      (D i).core.erase.core.reset_cmd = false := by
    intro i hi
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hlocal.left_reset_false
    · have hij : i ≠ j := by
        rw [hjLeader]
        exact hi
      rw [hoff i hie hij]
      let k := cwDist ring leader i
      have hkBound : k < n := cwDist_lt ring leader i
      have hpos : groupOffset ring leader k = i := by
        simpa [groupOffset, cwPos] using cwPos_cwDist ring leader i
      have hkPos : 0 < k := by
        have hkNe : k ≠ 0 := by
          intro hkZero
          apply hi
          rw [← hpos, hkZero]
          exact rooted_groupOffset_zero_eq ring leader
        omega
      have hkLast : k ≠ n - 1 := by
        intro hk
        apply hie
        rw [← hpos, hk]
      have hkBehind : k < n - 1 := by omega
      rw [← hpos]
      exact hpre.reset_behind k hkBehind
  have hnoFreeD : noFreeBarrier hpsi ring
      (fun i => (D i).core.erase.core) := by
    intro i
    dsimp only
    intro hbarrierD
    have hbarrierPre : isBarrier hpsi
        (pre i).core.erase.core
        (pre (ring.rightNeighbor i)).core.erase.core := by
      intro halignPre
      apply hbarrierD
      apply Fin.ext
      have hrightLabel := congrArg Fin.val
        (hlabelAt (ring.rightNeighbor i))
      have hleftLabel := congrArg Fin.val (hlabelAt i)
      have halignVal := congrArg Fin.val halignPre
      dsimp only at halignVal ⊢
      calc
        (D (ring.rightNeighbor i)).core.erase.core.label.val =
            (pre (ring.rightNeighbor i)).core.erase.core.label.val :=
          hrightLabel
        _ = ((pre i).core.erase.core.label.val + 1) % psi := halignVal
        _ = ((D i).core.erase.core.label.val + 1) % psi := by
          rw [hleftLabel]
    exact (hleaderAt (ring.rightNeighbor i)).trans
      (hpre.ready.no_free_barrier i hbarrierPre)
  have hsucc : clockwiseAttemptConfig T ring leader C n = D := by
    have hs := clockwiseAttemptConfig_succ T ring leader C (n - 1)
    have hnEq : n - 1 + 1 = n := by omega
    rw [hnEq] at hs
    exact hs
  rw [hsucc]
  exact {
    leader_alive := by
      rw [hleaderAt leader]
      exact hpre.ready.leader_alive
    leader_zero := by
      rw [hlabelAt leader]
      exact hpre.ready.leader_zero
    unique_leader := by
      intro i hi
      rw [hleaderAt i]
      exact hpre.ready.unique_leader i hi
    no_free_barrier := hnoFreeD
    leader_unshielded := by
      rw [hshieldAt leader]
      exact hpre.ready.leader_unshielded
    bullets_zero := hbulletAt
    comparison_neutral := hneutralD
    leader_signal_one := by
      rw [← hjLeader, hright]
      exact hlocal.right_signal_one
    leader_reset_true := by
      rw [← hjLeader, hright]
      simpa [hpreLeaderEcho] using hlocal.right_reset_exact
    follower_reset_false := hfollowerReset
    leader_echo_false := by
      rw [← hjLeader, hright]
      exact hlocal.right_echo_false
  }

/-! ## Global zero-rank completion -/

/-- Protected global endpoint reached by the extra leader edge.  The live
leader bullet is intentionally unrestricted; Algorithm 15 creates it while
installing the shield. -/
structure ClockwiseShieldedDone
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop where
  stable_labels : ∀ i,
    (C (ring.rightNeighbor i)).core.erase.core.label =
      ⟨((C i).core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩
  protected_leader : ProtectedLeaderAt hpsi C leader
  unique_leader : ∀ i, i ≠ leader →
    (C i).core.erase.core.leader = false
  comparison_neutral : ∀ i, ComparisonNeutral (C i).core.erase.core
  leader_signal_zero :
    (C leader).core.erase.core.signal_B = ⟨0, by omega⟩

/-- Protected endpoint for the rooted nondivisible lane.  It retains the
paper's no-free-barrier geometry instead of the impossible all-edge cyclic
label condition. -/
structure RootedClockwiseShieldedDone
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop
    extends RootedRetryGeometry hpsi ring leader C where
  protected_leader : ProtectedLeaderAt hpsi C leader
  comparison_neutral : ∀ i, ComparisonNeutral (C i).core.erase.core
  leader_signal_zero :
    (C leader).core.erase.core.signal_B = ⟨0, by omega⟩

private theorem noActiveDeletion_of_neutral
    (C : EConfig n psi kappa tau)
    (hneutral : ∀ i, ComparisonNeutral (C i).core.erase.core) :
    NoActiveDeletion C := by
  intro i
  have h := hneutral i
  simp [deletionActive, pathPresent, h.1, h.2.1]

/-- The extra outgoing leader edge fires after the rooted closing-edge signal
delivery and reaches a protected unique leader without introducing cyclic
alignment at the nondivisible closing edge. -/
theorem RootedLeaderSinkRetryDoneExact.fire_step
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (h : RootedLeaderSinkRetryDoneExact hpsi ring leader C) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C leader
    RootedClockwiseShieldedDone hpsi ring leader D := by
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader := rightNeighbor_ne_self_of_one_lt ring hn leader
  have hjFollower : (C j).core.erase.core.leader = false :=
    h.unique_leader j hje
  have hnoActive : NoActiveDeletion C :=
    noActiveDeletion_of_neutral C h.comparison_neutral
  have hopen : WallPriorityOpen (C leader) (C j) := by
    simpa [j] using WallPriorityOpen.of_noActiveDeletion C hnoActive ring leader
  have halign : (C j).core.erase.core.label =
      ⟨((C leader).core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ := by
    simpa only [j] using h.successor_label_of_right_ne leader hje
  let q := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau (C leader) (C j)
  have hlocal : LeaderFireOutput hpsi (C leader) (C j) q := by
    exact wallSweepPreCheckResetLeaderSinkPathStall_leader_fire
      hpsi (C leader) (C j) hopen halign h.leader_alive
        h.leader_signal_one hjFollower
  let D := localStep ring
    (wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau) C leader
  change RootedClockwiseShieldedDone hpsi ring leader D
  have hleft : D leader = q.1 := by
    simp [D, q, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, localStep, j, hje]
  have hoff : ∀ i, i ≠ leader → i ≠ j → D i = C i := by
    intro i hil hij
    simp [D, localStep, hil, j, hij]
  have hleaderAt : ∀ i,
      (D i).core.erase.core.leader = (C i).core.erase.core.leader := by
    intro i
    by_cases hil : i = leader
    · subst i
      rw [hleft, hlocal.left_leader, h.leader_alive]
    · by_cases hij : i = j
      · subst i
        rw [hright, hlocal.right_follower, hjFollower]
      · rw [hoff i hil hij]
  have hlabelAt : ∀ i,
      (D i).core.erase.core.label = (C i).core.erase.core.label := by
    intro i
    by_cases hil : i = leader
    · subst i
      rw [hleft]
      exact hlocal.left_label
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_label
      · rw [hoff i hil hij]
  have hneutralAt : ∀ i, ComparisonNeutral
      (D i).core.erase.core := by
    intro i
    by_cases hil : i = leader
    · subst i
      rw [hleft]
      exact hlocal.left_neutral
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_neutral
      · rw [hoff i hil hij]
        exact h.comparison_neutral i
  have hnoFreeD : noFreeBarrier hpsi ring
      (fun i => (D i).core.erase.core) := by
    intro i
    dsimp only
    intro hbarrierD
    have hbarrierC : isBarrier hpsi
        (C i).core.erase.core
        (C (ring.rightNeighbor i)).core.erase.core := by
      intro halignC
      apply hbarrierD
      apply Fin.ext
      have hrightLabel := congrArg Fin.val
        (hlabelAt (ring.rightNeighbor i))
      have hleftLabel := congrArg Fin.val (hlabelAt i)
      have halignVal := congrArg Fin.val halignC
      dsimp only at halignVal ⊢
      calc
        (D (ring.rightNeighbor i)).core.erase.core.label.val =
            (C (ring.rightNeighbor i)).core.erase.core.label.val :=
          hrightLabel
        _ = ((C i).core.erase.core.label.val + 1) % psi := halignVal
        _ = ((D i).core.erase.core.label.val + 1) % psi := by
          rw [hleftLabel]
    exact (hleaderAt (ring.rightNeighbor i)).trans
      (h.no_free_barrier i hbarrierC)
  exact {
    leader_alive := by
      rw [hleaderAt leader]
      exact h.leader_alive
    leader_zero := by
      rw [hlabelAt leader]
      exact h.leader_zero
    unique_leader := by
      intro i hi
      rw [hleaderAt i]
      exact h.unique_leader i hi
    no_free_barrier := hnoFreeD
    protected_leader := by
      unfold ProtectedLeaderAt
      rw [hleft]
      exact ⟨⟨hlocal.left_leader, hlocal.left_shield_true⟩,
        hlocal.left_label.trans h.leader_zero⟩
    comparison_neutral := hneutralAt
    leader_signal_zero := by
      rw [hleft]
      exact hlocal.left_signal_zero
  }

/-- The weak reset-aware post-closing boundary fires through the same
integrated transition and reaches a protected unique label-zero leader. -/
theorem resetAwareLeaderFireReady_fire_step
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (h : ResetAwareLeaderFireReady hpsi ring leader C) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C leader
    RootedClockwiseShieldedDone hpsi ring leader D := by
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader := rightNeighbor_ne_self_of_one_lt ring hn leader
  have hjFollower : (C j).core.erase.core.leader = false :=
    h.unique_leader j hje
  have hnoActive : NoActiveDeletion C :=
    noActiveDeletion_of_neutral C h.comparison_neutral
  have hopen : WallPriorityOpen (C leader) (C j) := by
    simpa [j] using WallPriorityOpen.of_noActiveDeletion C hnoActive ring leader
  have halign : (C j).core.erase.core.label =
      ⟨((C leader).core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ := by
    simpa only [j] using h.successor_label_of_right_ne leader hje
  let q := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau (C leader) (C j)
  have hlocal : LeaderFireOutput hpsi (C leader) (C j) q := by
    exact
      wallSweepResetProbePreCheckResetLeaderSinkPathStall_leader_fire
        hpsi (C leader) (C j) hopen halign h.leader_alive
          h.leader_signal_one hjFollower
  let D := localStep ring
    (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau) C leader
  change RootedClockwiseShieldedDone hpsi ring leader D
  have hleft : D leader = q.1 := by
    simp [D, q, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, localStep, j, hje]
  have hoff : ∀ i, i ≠ leader → i ≠ j → D i = C i := by
    intro i hil hij
    simp [D, localStep, hil, j, hij]
  have hleaderAt : ∀ i,
      (D i).core.erase.core.leader = (C i).core.erase.core.leader := by
    intro i
    by_cases hil : i = leader
    · subst i
      rw [hleft, hlocal.left_leader, h.leader_alive]
    · by_cases hij : i = j
      · subst i
        rw [hright, hlocal.right_follower, hjFollower]
      · rw [hoff i hil hij]
  have hlabelAt : ∀ i,
      (D i).core.erase.core.label = (C i).core.erase.core.label := by
    intro i
    by_cases hil : i = leader
    · subst i
      rw [hleft]
      exact hlocal.left_label
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_label
      · rw [hoff i hil hij]
  have hneutralAt : ∀ i, ComparisonNeutral
      (D i).core.erase.core := by
    intro i
    by_cases hil : i = leader
    · subst i
      rw [hleft]
      exact hlocal.left_neutral
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_neutral
      · rw [hoff i hil hij]
        exact h.comparison_neutral i
  have hnoFreeD : noFreeBarrier hpsi ring
      (fun i => (D i).core.erase.core) := by
    intro i
    dsimp only
    intro hbarrierD
    have hbarrierC : isBarrier hpsi
        (C i).core.erase.core
        (C (ring.rightNeighbor i)).core.erase.core := by
      intro halignC
      apply hbarrierD
      apply Fin.ext
      have hrightLabel := congrArg Fin.val
        (hlabelAt (ring.rightNeighbor i))
      have hleftLabel := congrArg Fin.val (hlabelAt i)
      have halignVal := congrArg Fin.val halignC
      dsimp only at halignVal ⊢
      calc
        (D (ring.rightNeighbor i)).core.erase.core.label.val =
            (C (ring.rightNeighbor i)).core.erase.core.label.val :=
          hrightLabel
        _ = ((C i).core.erase.core.label.val + 1) % psi := halignVal
        _ = ((D i).core.erase.core.label.val + 1) % psi := by
          rw [hleftLabel]
    exact (hleaderAt (ring.rightNeighbor i)).trans
      (h.no_free_barrier i hbarrierC)
  exact {
    leader_alive := by
      rw [hleaderAt leader]
      exact h.leader_alive
    leader_zero := by
      rw [hlabelAt leader]
      exact h.leader_zero
    unique_leader := by
      intro i hi
      rw [hleaderAt i]
      exact h.unique_leader i hi
    no_free_barrier := hnoFreeD
    protected_leader := by
      unfold ProtectedLeaderAt
      rw [hleft]
      exact ⟨⟨hlocal.left_leader, hlocal.left_shield_true⟩,
        hlocal.left_label.trans h.leader_zero⟩
    comparison_neutral := hneutralAt
    leader_signal_zero := by
      rw [hleft]
      exact hlocal.left_signal_zero }

/-- The terminal reset-aware closing edge followed by the outgoing leader edge
is a literal two-interaction schedule to a protected rooted endpoint. -/
theorem ResetAwareRootedClosingReady.exists_close_fire_schedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (h : ResetAwareRootedClosingReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      word.length = 2 ∧
      RootedClockwiseShieldedDone hpsi ring leader D := by
  let e := groupOffset ring leader (n - 1)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let M := localStep ring T C e
  have hclose : ResetAwareLeaderFireReady hpsi ring leader M := by
    simpa only [e, T, M] using
      resetAwareRootedClosingReady_close_step
        hpsi ring hn hndvd leader C h
  let D := localStep ring T M leader
  have hfire : RootedClockwiseShieldedDone hpsi ring leader D := by
    simpa only [T, D] using
      resetAwareLeaderFireReady_fire_step
        hpsi ring hn leader M hclose
  exact ⟨[e, leader], D, rfl, by simp, hfire⟩

/-- Birth-signal-transition form of the terminal close/fire word.  The first
edge has the existing leader as responder and the second as initiator, so the
wrapper is inert on both interactions. -/
theorem ResetAwareRootedClosingReady.exists_birthSignalZero_close_fire_schedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (h : ResetAwareRootedClosingReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      word.length = 2 ∧
      RootedClockwiseShieldedDone hpsi ring leader D := by
  let e := groupOffset ring leader (n - 1)
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Mold := localStep ring Told C e
  let Mnew := localStep ring Tnew C e
  have hneighbor : ring.rightNeighbor e = leader := by
    let j := groupOffset ring leader n
    have hnEq : n - 1 + 1 = n := by omega
    have hej : ring.rightNeighbor e = j := by
      simpa only [e, j, hnEq] using
        rightNeighbor_groupOffset ring leader (n - 1)
    have hj : j = leader := by
      apply Fin.ext
      simp [j]
    exact hej.trans hj
  have hM : Mnew = Mold := by
    have hpair : Tnew (C e) (C (ring.rightNeighbor e)) =
        Told (C e) (C (ring.rightNeighbor e)) := by
      simpa [Tnew, Told, hneighbor] using
        wallSweepBirthSignalZeroPathStall_eq_of_right_leader
          hpsi kappa tau (C e) (C leader) h.leader_alive
    funext i
    simp [Mnew, Mold, localStep, hpair]
  have hclose := resetAwareRootedClosingReady_close_step
    hpsi ring hn hndvd leader C h
  change ResetAwareLeaderFireReady hpsi ring leader Mold at hclose
  let Dold := localStep ring Told Mold leader
  let Dnew := localStep ring Tnew Mnew leader
  have hsecond : localStep ring Tnew Mold leader =
      localStep ring Told Mold leader := by
    have hpair : Tnew (Mold leader) (Mold (ring.rightNeighbor leader)) =
        Told (Mold leader) (Mold (ring.rightNeighbor leader)) := by
      simpa [Tnew, Told] using
        wallSweepBirthSignalZeroPathStall_eq_of_left_leader
          hpsi kappa tau (Mold leader)
            (Mold (ring.rightNeighbor leader)) hclose.leader_alive
    funext i
    simp [localStep, hpair]
  have hD : Dnew = Dold := by
    change localStep ring Tnew Mnew leader =
      localStep ring Told Mold leader
    rw [hM]
    exact hsecond
  have holdEndpoint : RootedClockwiseShieldedDone
      hpsi ring leader Dold := by
    simpa [Dold, Told] using
      resetAwareLeaderFireReady_fire_step
        hpsi ring hn leader Mold hclose
  exact ⟨[e, leader], Dnew, rfl, by simp, by
    rw [hD]
    exact holdEndpoint⟩

/-- The complete reset-aware repair from an authenticated outgoing frontier:
normalize once, migrate once to a zero-labelled root, run the signal-aware
well-founded retry at that fixed root, close the nondivisible edge, and fire
the surviving leader.  The result names the physical root installed by the
one-time migration and uses one literal schedule throughout. -/
theorem exists_resetAwareRootedShieldRepairSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (newRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      RootedClockwiseShieldedDone hpsi ring newRoot D := by
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  obtain ⟨pref, M, newRoot, hM, hrooted⟩ :=
    exists_resetAwareRootedClosingRepairSchedule
      hpsi ring hn hpsiLe leader C hready
  obtain ⟨tail, D, hD, _htailLength, hshielded⟩ :=
    ResetAwareRootedClosingReady.exists_close_fire_schedule
      hpsi ring hn hndvd newRoot M hrooted
  let word := pref ++ tail
  refine ⟨word, D, newRoot, ?_, hshielded⟩
  calc
    D = runLocalSchedule ring T M tail := hD
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T C pref) tail := by rw [← hM]
    _ = runLocalSchedule ring T C (pref ++ tail) :=
      (runLocalSchedule_append_generic ring T C pref tail).symm
    _ = runLocalSchedule ring T C word := by rfl

/-- The complete birth-signal-transition reset-aware repair from an authenticated outgoing frontier:
normalize once, migrate once to a zero-labelled root, run the signal-aware
well-founded retry at that fixed root, close the nondivisible edge, and fire
the surviving leader.  The result names the physical root installed by the
one-time migration and uses one literal schedule throughout. -/
theorem exists_resetAwareRootedBirthSignalZeroShieldRepairSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (newRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      RootedClockwiseShieldedDone hpsi ring newRoot D := by
  let T :=
    wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
  obtain ⟨pref, M, newRoot, hM, hrooted⟩ :=
    exists_resetAwareRootedBirthSignalZeroClosingRepairSchedule
      hpsi ring hn hpsiLe leader C hready
  obtain ⟨tail, D, hD, _htailLength, hshielded⟩ :=
    ResetAwareRootedClosingReady.exists_birthSignalZero_close_fire_schedule
      hpsi ring hn hndvd newRoot M hrooted
  let word := pref ++ tail
  refine ⟨word, D, newRoot, ?_, hshielded⟩
  calc
    D = runLocalSchedule ring T M tail := hD
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T C pref) tail := by rw [← hM]
    _ = runLocalSchedule ring T C (pref ++ tail) :=
      (runLocalSchedule_append_generic ring T C pref tail).symm
    _ = runLocalSchedule ring T C word := by rfl

/-- Complete the formerly open shielded frontier lane.  The pre-migration
sweep and zero-root dispatch feed the combined live/echo scheduler.  A
follower-live-free endpoint is consumed by the existing rooted close/fire
repair; the only alternative is a genuine leaderless configuration with a
strict decrease of global live-bullet mass. -/
theorem exists_resetAwareShieldedProtectedOrLeaderlessSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (finalRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      (ProtectedLeaderAt hpsi D finalRoot ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  obtain ⟨pref, M, root, hM, hpre⟩ :=
    exists_resetAwareShieldedProtectedOrLiveRetrySchedule
      hpsi ring hn hpsiLe leader C hready
  rcases hpre with hprotected | hlive
  · exact ⟨pref, M, root, hM, Or.inl hprotected⟩
  · obtain ⟨middle, E, hE, hmiddle⟩ :=
      exists_resetAwareLiveRetrySchedule
        hpsi ring hn root M hlive.1 hlive.2.1
    rcases hmiddle with hprotected | hleaderless | hretry
    · let word := pref ++ middle
      refine ⟨word, E, root, ?_, Or.inl hprotected⟩
      calc
        E = runLocalSchedule ring T M middle := hE
        _ = runLocalSchedule ring T
            (runLocalSchedule ring T C pref) middle := by rw [← hM]
        _ = runLocalSchedule ring T C (pref ++ middle) :=
          (runLocalSchedule_append_generic ring T C pref middle).symm
        _ = runLocalSchedule ring T C word := by rfl
    · let word := pref ++ middle
      refine ⟨word, E, root, ?_, Or.inr ⟨hleaderless.1, ?_⟩⟩
      · calc
          E = runLocalSchedule ring T M middle := hE
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) middle := by rw [← hM]
          _ = runLocalSchedule ring T C (pref ++ middle) :=
            (runLocalSchedule_append_generic ring T C pref middle).symm
          _ = runLocalSchedule ring T C word := by rfl
      · exact Nat.lt_of_lt_of_le hleaderless.2 hlive.2.2
    · obtain ⟨tail, D, finalRoot, hD, hdone⟩ :=
        exists_resetAwareRootedShieldRepairSchedule
          hpsi ring hn hpsiLe hndvd root E hretry.1
      let word := pref ++ middle ++ tail
      refine ⟨word, D, finalRoot, ?_, Or.inl hdone.protected_leader⟩
      calc
        D = runLocalSchedule ring T E tail := hD
        _ = runLocalSchedule ring T
            (runLocalSchedule ring T M middle) tail := by rw [← hE]
        _ = runLocalSchedule ring T M (middle ++ tail) :=
          (runLocalSchedule_append_generic ring T M middle tail).symm
        _ = runLocalSchedule ring T
            (runLocalSchedule ring T C pref) (middle ++ tail) := by rw [← hM]
        _ = runLocalSchedule ring T C (pref ++ (middle ++ tail)) :=
          (runLocalSchedule_append_generic ring T C pref
            (middle ++ tail)).symm
        _ = runLocalSchedule ring T C word := by
          simp only [word, List.append_assoc]

/-- Birth-signal-transition completion of the shielded and zero-root live
lanes.  The only remaining branch is the follower-live-free rooted closing
boundary; protected and leader-deletion outcomes are already final. -/
theorem exists_birthSignalZeroShieldedProtectedOrLeaderlessOrRetrySchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (finalRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      (ProtectedLeaderAt hpsi D finalRoot ∨
        (NoActiveDeletion D ∧
          RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareRetryReady hpsi ring finalRoot D ∧
          (D finalRoot).core.erase.core.label = ⟨0, hpsi⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  obtain ⟨pref, M, root, hM, hpre⟩ :=
    exists_resetAwareShieldedBirthSignalZeroProtectedOrLiveRetrySchedule
      hpsi ring hn hpsiLe leader C hready
  rcases hpre with hprotected | hlive
  · exact ⟨pref, M, root, hM, Or.inl hprotected⟩
  · obtain ⟨middle, E, hE, hmiddle⟩ :=
      exists_resetAwareLiveRetryBirthSignalZeroSchedule
        hpsi ring hn root M hlive.1 hlive.2.1
    let word := pref ++ middle
    refine ⟨word, E, root, ?_, ?_⟩
    · calc
        E = runLocalSchedule ring T M middle := hE
        _ = runLocalSchedule ring T
            (runLocalSchedule ring T C pref) middle := by rw [← hM]
        _ = runLocalSchedule ring T C (pref ++ middle) :=
          (runLocalSchedule_append_generic ring T C pref middle).symm
        _ = runLocalSchedule ring T C word := by rfl
    · rcases hmiddle with hprotected | hleaderless | hretry
      · exact Or.inl hprotected
      · exact Or.inr (Or.inl ⟨hleaderless.1,
          hleaderless.2.1,
          Nat.lt_of_lt_of_le hleaderless.2.2 hlive.2.2⟩)
      · exact Or.inr (Or.inr ⟨hretry.1, hretry.2.1,
          Nat.le_trans hretry.2.2 hlive.2.2⟩)

/-- Close the final live-free retry branch under the birth-signal transition.
Every shielded frontier now reaches either a protected leader or a genuinely
leaderless configuration with a strict decrease of live-bullet mass. -/
theorem exists_birthSignalZeroShieldedProtectedOrLeaderlessSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (finalRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      (ProtectedLeaderAt hpsi D finalRoot ∨
        (NoActiveDeletion D ∧
          RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  obtain ⟨pref, M, root, hM, hpre⟩ :=
    exists_birthSignalZeroShieldedProtectedOrLeaderlessOrRetrySchedule
      hpsi ring hn hpsiLe leader C hready
  rcases hpre with hprotected | hleaderless | hretry
  · exact ⟨pref, M, root, hM, Or.inl hprotected⟩
  · exact ⟨pref, M, root, hM, Or.inr hleaderless⟩
  · obtain ⟨tail, D, finalRoot, hD, hdone⟩ :=
      exists_resetAwareRootedBirthSignalZeroShieldRepairSchedule
        hpsi ring hn hpsiLe hndvd root M hretry.1
    let word := pref ++ tail
    refine ⟨word, D, finalRoot, ?_, Or.inl hdone.protected_leader⟩
    calc
      D = runLocalSchedule ring T M tail := hD
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C pref) tail := by rw [← hM]
      _ = runLocalSchedule ring T C (pref ++ tail) :=
        (runLocalSchedule_append_generic ring T C pref tail).symm
      _ = runLocalSchedule ring T C word := by rfl

/-- Consume an authenticated outgoing reset frontier at an arbitrary physical
label.  A live first follower already certifies the leader shield.  Otherwise
the label-independent live/echo scheduler reaches either the shielded lane,
the follower-live-free rooted lane, or a leaderless configuration with a
strict global live-count decrease. -/
theorem exists_resetAwareFrontierProtectedOrLeaderlessSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hfrontier :
      PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
        hpsi ring C leader)
    (hsignal :
      (C leader).core.erase.core.signal_B = ⟨0, by omega⟩) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (finalRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      (ProtectedLeaderAt hpsi D finalRoot ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  by_cases hrightLive :
      (C (ring.rightNeighbor leader)).core.erase.core.bullet =
        ⟨2, by omega⟩
  · have hlive : ResetAwareShieldedLiveRetryReady
        hpsi ring leader C := ⟨hfrontier, hrightLive, hsignal⟩
    have hshielded : ResetAwareShieldedRetryReady
        hpsi ring leader C := hlive.toShielded
    exact exists_resetAwareShieldedProtectedOrLeaderlessSchedule
      hpsi ring hn hpsiLe hndvd leader C hshielded
  · have hliveReady : ResetAwareLiveRetryReady
        hpsi ring leader C := ⟨hfrontier, hrightLive, hsignal⟩
    obtain ⟨pref, M, hM, hmiddle⟩ :=
      exists_resetAwareLiveRetryToShieldedSchedule
        hpsi ring hn leader C hliveReady
    rcases hmiddle with hshielded | hleaderless | hretry
    · obtain ⟨tail, D, finalRoot, hD, hout⟩ :=
        exists_resetAwareShieldedProtectedOrLeaderlessSchedule
          hpsi ring hn hpsiLe hndvd leader M hshielded.1
      let word := pref ++ tail
      refine ⟨word, D, finalRoot, ?_, ?_⟩
      · calc
          D = runLocalSchedule ring T M tail := hD
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) tail := by rw [← hM]
          _ = runLocalSchedule ring T C (pref ++ tail) :=
            (runLocalSchedule_append_generic ring T C pref tail).symm
          _ = runLocalSchedule ring T C word := by rfl
      · rcases hout with hprotected | hleaderlessD
        · exact Or.inl hprotected
        · exact Or.inr ⟨hleaderlessD.1,
            Nat.lt_of_lt_of_le hleaderlessD.2 hshielded.2⟩
    · exact ⟨pref, M, leader, hM, Or.inr hleaderless⟩
    · obtain ⟨tail, D, finalRoot, hD, hdone⟩ :=
        exists_resetAwareRootedShieldRepairSchedule
          hpsi ring hn hpsiLe hndvd leader M hretry.1
      let word := pref ++ tail
      refine ⟨word, D, finalRoot, ?_, Or.inl hdone.protected_leader⟩
      calc
        D = runLocalSchedule ring T M tail := hD
        _ = runLocalSchedule ring T
            (runLocalSchedule ring T C pref) tail := by rw [← hM]
        _ = runLocalSchedule ring T C (pref ++ tail) :=
          (runLocalSchedule_append_generic ring T C pref tail).symm
        _ = runLocalSchedule ring T C word := by rfl

/-- Under the birth-signal transition, consume an authenticated outgoing reset frontier at an arbitrary physical
label.  A live first follower already certifies the leader shield.  Otherwise
the label-independent live/echo scheduler reaches either the shielded lane,
the follower-live-free rooted lane, or a leaderless configuration with a
strict global live-count decrease. -/
theorem exists_birthSignalZeroFrontierProtectedOrLeaderlessSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hfrontier :
      PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
        hpsi ring C leader)
    (hsignal :
      (C leader).core.erase.core.signal_B = ⟨0, by omega⟩) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (finalRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      (ProtectedLeaderAt hpsi D finalRoot ∨
        (NoActiveDeletion D ∧
          RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  let T :=
    wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
  by_cases hrightLive :
      (C (ring.rightNeighbor leader)).core.erase.core.bullet =
        ⟨2, by omega⟩
  · have hlive : ResetAwareShieldedLiveRetryReady
        hpsi ring leader C := ⟨hfrontier, hrightLive, hsignal⟩
    have hshielded : ResetAwareShieldedRetryReady
        hpsi ring leader C := hlive.toShielded
    exact exists_birthSignalZeroShieldedProtectedOrLeaderlessSchedule
      hpsi ring hn hpsiLe hndvd leader C hshielded
  · have hliveReady : ResetAwareLiveRetryReady
        hpsi ring leader C := ⟨hfrontier, hrightLive, hsignal⟩
    obtain ⟨pref, M, hM, hmiddle⟩ :=
      exists_resetAwareLiveRetryBirthSignalZeroToShieldedSchedule
        hpsi ring hn leader C hliveReady
    rcases hmiddle with hshielded | hleaderless | hretry
    · obtain ⟨tail, D, finalRoot, hD, hout⟩ :=
        exists_birthSignalZeroShieldedProtectedOrLeaderlessSchedule
          hpsi ring hn hpsiLe hndvd leader M hshielded.1
      let word := pref ++ tail
      refine ⟨word, D, finalRoot, ?_, ?_⟩
      · calc
          D = runLocalSchedule ring T M tail := hD
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) tail := by rw [← hM]
          _ = runLocalSchedule ring T C (pref ++ tail) :=
            (runLocalSchedule_append_generic ring T C pref tail).symm
          _ = runLocalSchedule ring T C word := by rfl
      · rcases hout with hprotected | hleaderlessD
        · exact Or.inl hprotected
        · exact Or.inr ⟨hleaderlessD.1, hleaderlessD.2.1,
            Nat.lt_of_lt_of_le hleaderlessD.2.2 hshielded.2⟩
    · exact ⟨pref, M, leader, hM, Or.inr hleaderless⟩
    · obtain ⟨tail, D, finalRoot, hD, hdone⟩ :=
        exists_resetAwareRootedBirthSignalZeroShieldRepairSchedule
          hpsi ring hn hpsiLe hndvd leader M hretry.1
      let word := pref ++ tail
      refine ⟨word, D, finalRoot, ?_, Or.inl hdone.protected_leader⟩
      calc
        D = runLocalSchedule ring T M tail := hD
        _ = runLocalSchedule ring T
            (runLocalSchedule ring T C pref) tail := by rw [← hM]
        _ = runLocalSchedule ring T C (pref ++ tail) :=
          (runLocalSchedule_append_generic ring T C pref tail).symm
        _ = runLocalSchedule ring T C word := by rfl

/-- One complete leaderless repair cycle is globally live-count
nonexpansive.  The frontier entry can spend at most one live bullet when an
arbitrary positive leader signal fires; every consumer failure removes at
least one live bullet, cancelling that debt. -/
theorem
    exists_resetAwareLeaderlessProtectedOrNonincreaseSchedule_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (finalRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      (ProtectedLeaderAt hpsi D finalRoot ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  obtain ⟨pref, M, leader, hM, hfrontier, hsignal, hcountM⟩ :=
    exists_resetProbeLeaderSink_resetFrontier_from_leaderless_of_not_dvd
      hpsi ring hn hpsiLe hndvd C hnoActive hleaderless
  obtain ⟨tail, D, finalRoot, hD, hout⟩ :=
    exists_resetAwareFrontierProtectedOrLeaderlessSchedule
      hpsi ring hn hpsiLe hndvd leader M hfrontier hsignal
  let word := pref ++ tail
  refine ⟨word, D, finalRoot, ?_, ?_⟩
  · calc
      D = runLocalSchedule ring T M tail := hD
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C pref) tail := by rw [← hM]
      _ = runLocalSchedule ring T C (pref ++ tail) :=
        (runLocalSchedule_append_generic ring T C pref tail).symm
      _ = runLocalSchedule ring T C word := by rfl
  · rcases hout with hprotected | hleaderlessD
    · exact Or.inl hprotected
    · exact Or.inr ⟨hleaderlessD.1, by omega⟩

/-- One complete birth-signal repair cycle either protects a leader or
returns leaderless with a strict live-bullet decrease.  The zero-at-birth
producer is nonexpansive, while every leaderless consumer exit is strict. -/
theorem
    exists_birthSignalZeroLeaderlessProtectedOrStrictDecreaseSchedule_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (finalRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      (ProtectedLeaderAt hpsi D finalRoot ∨
        (NoActiveDeletion D ∧
          RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  let T :=
    wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
  obtain ⟨pref, M, leader, hM, hfrontier, hsignal, hcountM⟩ :=
    exists_birthSignalZero_resetFrontier_from_leaderless_of_not_dvd
      hpsi ring hn hpsiLe hndvd C hnoActive hleaderless
  obtain ⟨tail, D, finalRoot, hD, hout⟩ :=
    exists_birthSignalZeroFrontierProtectedOrLeaderlessSchedule
      hpsi ring hn hpsiLe hndvd leader M hfrontier hsignal
  let word := pref ++ tail
  refine ⟨word, D, finalRoot, ?_, ?_⟩
  · calc
      D = runLocalSchedule ring T M tail := hD
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C pref) tail := by rw [← hM]
      _ = runLocalSchedule ring T C (pref ++ tail) :=
        (runLocalSchedule_append_generic ring T C pref tail).symm
      _ = runLocalSchedule ring T C word := by rfl
  · rcases hout with hprotected | hleaderlessD
    · exact Or.inl hprotected
    · exact Or.inr ⟨hleaderlessD.1, hleaderlessD.2.1,
        Nat.lt_of_lt_of_le hleaderlessD.2.2 hcountM⟩

/-- Strong induction on global live-bullet mass iterates the strict repaired
cycle until it reaches a protected leader.  Every recursive leaderless
endpoint remains deletion-free, so the next cycle has exactly the premises
of the previous one. -/
theorem exists_birthSignalZeroLeaderlessProtectedSchedule_of_count
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (rank : Nat) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hrank : PPLLPpsiLeaderCreationRepair.bulletTwoCount C = rank) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (finalRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ProtectedLeaderAt hpsi D finalRoot := by
  revert C
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      intro C hnoActive hleaderless hrank
      obtain ⟨pref, M, root, hM, hout⟩ :=
        exists_birthSignalZeroLeaderlessProtectedOrStrictDecreaseSchedule_of_not_dvd
          hpsi ring hn hpsiLe hndvd C hnoActive hleaderless
      rcases hout with hprotected | hretry
      · exact ⟨pref, M, root, hM, hprotected⟩
      · have hlt :
            PPLLPpsiLeaderCreationRepair.bulletTwoCount M < rank := by
          calc
            PPLLPpsiLeaderCreationRepair.bulletTwoCount M <
                PPLLPpsiLeaderCreationRepair.bulletTwoCount C := hretry.2.2
            _ = rank := hrank
        obtain ⟨tail, D, finalRoot, hD, hprotected⟩ :=
          ih (PPLLPpsiLeaderCreationRepair.bulletTwoCount M) hlt
            M hretry.1 hretry.2.1 rfl
        let T := wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau
        let word := pref ++ tail
        refine ⟨word, D, finalRoot, ?_, hprotected⟩
        calc
          D = runLocalSchedule ring T M tail := hD
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) tail := by rw [← hM]
          _ = runLocalSchedule ring T C (pref ++ tail) :=
            (runLocalSchedule_append_generic ring T C pref tail).symm
          _ = runLocalSchedule ring T C word := by rfl

/-- Every deletion-free leaderless configuration on a nondivisible ring has a
literal repaired schedule to a protected leader. -/
theorem exists_birthSignalZeroLeaderlessProtectedSchedule_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (finalRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ProtectedLeaderAt hpsi D finalRoot := by
  exact exists_birthSignalZeroLeaderlessProtectedSchedule_of_count
    hpsi ring hn hpsiLe hndvd
      (PPLLPpsiLeaderCreationRepair.bulletTwoCount C)
      C hnoActive hleaderless rfl

/-- A reset-command-free leaderless configuration may first drain arbitrary
active comparison paths and then enter the strict leaderless induction. -/
theorem exists_birthSignalZeroResetFreeLeaderlessProtectedSchedule_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau)
    (hfree : ResetCommandFree C)
    (hleaderless : RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (finalRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ProtectedLeaderAt hpsi D finalRoot := by
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  obtain ⟨pref, _hprefLength, _hempty, hnoActiveM,
      hpeace, _hcontrol, _hfreeM⟩ :=
    exists_birthSignalZeroDeletionDrain hpsi ring hn C hfree
  let M := runLocalSchedule ring T C pref
  change NoActiveDeletion M at hnoActiveM
  change PeaceViewConfigFrame C M at hpeace
  have hleaderlessM : RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig M) := by
    intro i
    have hfield := congrArg
      (fun v : PPLLNoCheckBirthConditionTwoPhysical.PeaceView psi =>
        v.leader) (hpeace i)
    exact hfield.trans (hleaderless i)
  obtain ⟨tail, D, finalRoot, hD, hprotected⟩ :=
    exists_birthSignalZeroLeaderlessProtectedSchedule_of_not_dvd
      hpsi ring hn hpsiLe hndvd M hnoActiveM hleaderlessM
  let word := pref ++ tail
  refine ⟨word, D, finalRoot, ?_, hprotected⟩
  calc
    D = runLocalSchedule ring T M tail := hD
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T C pref) tail := by rfl
    _ = runLocalSchedule ring T C (pref ++ tail) :=
      (runLocalSchedule_append_generic ring T C pref tail).symm
    _ = runLocalSchedule ring T C word := by rfl

/-- At rank zero, the concrete `n`-edge rooted pass followed by the outgoing
leader edge reaches a protected unique leader in exactly `n+1` interactions. -/
theorem exists_preCheckResetLeaderSinkRootedZeroShieldSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : RootedClockwiseRetryReady hpsi ring leader C)
    (hzero : clockwiseEchoRank ring leader C = 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau)
        C word ∧
      word.length = n + 1 ∧
      RootedClockwiseShieldedDone hpsi ring leader D := by
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let M := clockwiseAttemptConfig T ring leader C n
  have hdone : RootedLeaderSinkRetryDoneExact hpsi ring leader M := by
    simpa only [T, M] using
      preCheckResetLeaderSink_rooted_zeroRank_fullPass_exact
        hpsi ring hn hndvd leader C hready hzero
  let D := localStep ring T M leader
  have hshield : RootedClockwiseShieldedDone hpsi ring leader D :=
    RootedLeaderSinkRetryDoneExact.fire_step
      hpsi ring hn leader M hdone
  let word := resetSweepSchedule ring leader n ++ [leader]
  have hrun : D = runLocalSchedule ring T C word := by
    calc
      D = runLocalSchedule ring T M [leader] := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C
            (resetSweepSchedule ring leader n)) [leader] := by rfl
      _ = runLocalSchedule ring T C word :=
        (runLocalSchedule_append_generic ring T C
          (resetSweepSchedule ring leader n) [leader]).symm
  refine ⟨word, D, hrun, ?_, hshield⟩
  simp only [word, List.length_append, List.length_cons, List.length_nil,
    resetSweepSchedule_length]

/-- The edge initiated by the exact zero-pass endpoint preserves uniqueness
and stable labels while converting the designated leader into a protected
anchor. -/
theorem ClockwiseRetryDoneExact.fire_step
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (h : ClockwiseRetryDoneExact hpsi ring leader C) :
    let D := localStep ring
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C leader
    ClockwiseShieldedDone hpsi ring leader D := by
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader := rightNeighbor_ne_self_of_one_lt ring hn leader
  have hjFollower : (C j).core.erase.core.leader = false :=
    h.unique_leader j hje
  have hnoActive : NoActiveDeletion C :=
    noActiveDeletion_of_neutral C h.comparison_neutral
  have hopen : WallPriorityOpen (C leader) (C j) := by
    simpa [j] using WallPriorityOpen.of_noActiveDeletion C hnoActive ring leader
  let q := wallSweepPreCheckResetPathStallTransition
    hpsi kappa tau (C leader) (C j)
  have hlocal : LeaderFireOutput hpsi (C leader) (C j) q := by
    exact wallSweepPreCheckResetPathStall_leader_fire
      hpsi (C leader) (C j) hopen
      (by simpa [j] using h.stable_labels leader)
      h.leader_alive h.leader_signal_one hjFollower
  let D := localStep ring
    (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C leader
  change ClockwiseShieldedDone hpsi ring leader D
  have hleft : D leader = q.1 := by
    simp [D, q, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, localStep, j, hje]
  have hoff : ∀ i, i ≠ leader → i ≠ j → D i = C i := by
    intro i hil hij
    simp [D, localStep, hil, j, hij]
  have hleaderAt : ∀ i,
      (D i).core.erase.core.leader = (C i).core.erase.core.leader := by
    intro i
    by_cases hil : i = leader
    · subst i
      rw [hleft, hlocal.left_leader, h.leader_alive]
    · by_cases hij : i = j
      · subst i
        rw [hright, hlocal.right_follower, hjFollower]
      · rw [hoff i hil hij]
  have hlabelAt : ∀ i,
      (D i).core.erase.core.label = (C i).core.erase.core.label := by
    intro i
    by_cases hil : i = leader
    · subst i
      rw [hleft]
      exact hlocal.left_label
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_label
      · rw [hoff i hil hij]
  have hneutralAt : ∀ i, ComparisonNeutral (D i).core.erase.core := by
    intro i
    by_cases hil : i = leader
    · subst i
      rw [hleft]
      exact hlocal.left_neutral
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_neutral
      · rw [hoff i hil hij]
        exact h.comparison_neutral i
  exact {
    stable_labels := by
      intro i
      rw [hlabelAt (ring.rightNeighbor i), hlabelAt i]
      exact h.stable_labels i
    protected_leader := by
      unfold ProtectedLeaderAt
      rw [hleft]
      exact ⟨⟨hlocal.left_leader, hlocal.left_shield_true⟩,
        hlocal.left_label.trans h.leader_zero⟩
    unique_leader := by
      intro i hi
      rw [hleaderAt i]
      exact h.unique_leader i hi
    comparison_neutral := hneutralAt
    leader_signal_zero := by
      rw [hleft]
      exact hlocal.left_signal_zero
  }

/-! ## Rank scheduler followed by the terminal edge -/

/-- Concrete arbitrary-rank attempt contract for the rooted leader-sink
repair on a nondivisible ring. -/
theorem preCheckResetLeaderSinkRootedAttemptContract
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n) (leader : Fin n) :
    ClockwiseAttemptContract
      (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
      ring hn leader (RootedClockwiseRetryReady hpsi ring leader)
        (RootedLeaderSinkRetryDoneExact hpsi ring leader) where
  failed := by
    intro C hready hrank
    exact preCheckResetLeaderSink_rootedClockwiseFailedAttempt
      hpsi ring hn leader C hready hrank
  zero_rank := by
    intro C hready hzero
    exact preCheckResetLeaderSink_rooted_zeroRank_fullPass_exact
      hpsi ring hn hndvd leader C hready hzero

/-- From any rooted retry-ready boundary, binary-rank retry followed by one
outgoing leader edge reaches the protected endpoint.  This is the arbitrary
rank repair of the paper's shield circuit for `psi ∤ n`. -/
theorem exists_preCheckResetLeaderSinkRootedShieldSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : RootedClockwiseRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau)
        C word ∧
      word.length ≤ n + 1 +
        (n - 1) * clockwiseEchoRank ring leader C ∧
      RootedClockwiseShieldedDone hpsi ring leader D := by
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  obtain ⟨retryWord, M, hM, hretryWord, hdone⟩ :=
    exists_clockwiseRetrySchedule T ring hn leader
      (RootedClockwiseRetryReady hpsi ring leader)
      (RootedLeaderSinkRetryDoneExact hpsi ring leader)
      (preCheckResetLeaderSinkRootedAttemptContract
        hpsi ring hn hndvd leader)
      C hready
  let D := localStep ring T M leader
  have hshield : RootedClockwiseShieldedDone hpsi ring leader D :=
    RootedLeaderSinkRetryDoneExact.fire_step
      hpsi ring hn leader M hdone
  have hrun : D = runLocalSchedule ring T C (retryWord ++ [leader]) := by
    calc
      D = runLocalSchedule ring T M [leader] := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C retryWord) [leader] := by rw [← hM]
      _ = runLocalSchedule ring T C (retryWord ++ [leader]) :=
        (runLocalSchedule_append_generic ring T C retryWord [leader]).symm
  refine ⟨retryWord ++ [leader], D, hrun, ?_, hshield⟩
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- From the weaker rooted seed, one deletion drain, arbitrary-rank retry,
and the terminal outgoing leader edge reach a protected unique leader.  Path
cleanup is charged once and cyclic closing-edge alignment is never assumed. -/
theorem exists_preCheckResetLeaderSinkRootedShieldSchedule_after_oneDrain
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hseed : RootedUnshieldedRetrySeed hpsi ring leader C) :
    ∃ (actual : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau)
        C actual ∧
      actual.length ≤ comparisonPathCount C + n + 1 +
        (n - 1) * clockwiseEchoRank ring leader C ∧
      RootedClockwiseShieldedDone hpsi ring leader D := by
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  obtain ⟨retryWord, M, hM, hretryWord, hdone⟩ :=
    exists_clockwiseRetrySchedule_after_oneDrain T ring hn leader
      (RootedUnshieldedRetrySeed hpsi ring leader)
      (RootedClockwiseRetryReady hpsi ring leader)
      (RootedLeaderSinkRetryDoneExact hpsi ring leader)
      (preCheckResetLeaderSinkRootedAttemptContract
        hpsi ring hn hndvd leader)
      (preCheckResetLeaderSinkRootedOneDrainContract
        hpsi ring hn leader)
      C hseed
  let D := localStep ring T M leader
  have hshield : RootedClockwiseShieldedDone hpsi ring leader D :=
    RootedLeaderSinkRetryDoneExact.fire_step
      hpsi ring hn leader M hdone
  have hrun : D = runLocalSchedule ring T C (retryWord ++ [leader]) := by
    calc
      D = runLocalSchedule ring T M [leader] := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C retryWord) [leader] := by rw [← hM]
      _ = runLocalSchedule ring T C (retryWord ++ [leader]) :=
        (runLocalSchedule_append_generic ring T C retryWord [leader]).symm
  refine ⟨retryWord ++ [leader], D, hrun, ?_, hshield⟩
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- From a retry-ready boundary, binary-rank retry followed by one designated
leader edge reaches the protected endpoint.  The terminal cost is one more
than the zero-pass cost because the `n`-edge pass stops before firing. -/
theorem exists_preCheckResetClockwiseShieldSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ClockwiseRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        C word ∧
      word.length ≤ n + 1 +
        (n - 1) * clockwiseEchoRank ring leader C ∧
      ClockwiseShieldedDone hpsi ring leader D := by
  let T := wallSweepPreCheckResetPathStallTransition hpsi kappa tau
  obtain ⟨retryWord, M, hM, hretryWord, hdone⟩ :=
    exists_preCheckResetClockwiseRetryScheduleExact
      hpsi ring hn leader C hready
  let D := localStep ring T M leader
  have hshield : ClockwiseShieldedDone hpsi ring leader D :=
    ClockwiseRetryDoneExact.fire_step hpsi ring hn leader M hdone
  have hrun : D = runLocalSchedule ring T C (retryWord ++ [leader]) := by
    calc
      D = runLocalSchedule ring T M [leader] := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C retryWord) [leader] := by rw [← hM]
      _ = runLocalSchedule ring T C (retryWord ++ [leader]) :=
        (runLocalSchedule_append_generic ring T C retryWord [leader]).symm
  refine ⟨retryWord ++ [leader], D, hrun, ?_, hshield⟩
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- The one-time deletion drain, rank retry, and terminal leader edge together
reach a unique protected leader.  Path cleanup is charged once, outside the
well-founded retry. -/
theorem exists_preCheckResetClockwiseShieldSchedule_after_oneDrain
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hseed : UnshieldedRetrySeed hpsi ring leader C) :
    ∃ (actual : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        C actual ∧
      actual.length ≤ comparisonPathCount C + n + 1 +
        (n - 1) * clockwiseEchoRank ring leader C ∧
      ClockwiseShieldedDone hpsi ring leader D := by
  let T := wallSweepPreCheckResetPathStallTransition hpsi kappa tau
  obtain ⟨retryWord, M, hM, hretryWord, hdone⟩ :=
    exists_preCheckResetClockwiseRetryScheduleExact_after_oneDrain
      hpsi ring hn leader C hseed
  let D := localStep ring T M leader
  have hshield : ClockwiseShieldedDone hpsi ring leader D :=
    ClockwiseRetryDoneExact.fire_step hpsi ring hn leader M hdone
  have hrun : D = runLocalSchedule ring T C (retryWord ++ [leader]) := by
    calc
      D = runLocalSchedule ring T M [leader] := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C retryWord) [leader] := by rw [← hM]
      _ = runLocalSchedule ring T C (retryWord ++ [leader]) :=
        (runLocalSchedule_append_generic ring T C retryWord [leader]).symm
  refine ⟨retryWord ++ [leader], D, hrun, ?_, hshield⟩
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-! ## First-leader reset frontier to the self-normalizing pass -/

/-- The concrete first-leader frontier supplies the exact length-one state for
the reset-aware normalized-prefix traversal.  No leader-zero or remote-carrier
conclusion is added. -/
theorem outgoingResetFrontier_to_normalizedPrefixState
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau)
    (hfrontier : OutgoingResetFrontierUniqueLeader hpsi ring C) :
    ∃ leader : Fin n,
      ResetAwareNormalizedPrefixState hpsi ring leader C C 1 := by
  obtain ⟨leader, hnoActive, hunique, hleader, _hrightFollower,
      hrightLabel, _hleftProbe, _hrightProbe, hleftNeutral,
      hrightNeutral, hleftReset, hrightReset, _hleftEcho,
      _hrightEcho, _hsafe⟩ := hfrontier
  obtain ⟨only, _honlyLeader, honly⟩ := hunique
  have hleaderOnly : leader = only := by
    apply honly leader
    change (C leader).core.erase.core.leader = true
    exact hleader
  have huniquePoint : ∀ i, i ≠ leader →
      (C i).core.erase.core.leader = false := by
    intro i hi
    cases hvalue : (C i).core.erase.core.leader with
    | false => rfl
    | true =>
        have hiOnly : i = only := by
          apply honly i
          change (C i).core.erase.core.leader = true
          exact hvalue
        exact (hi (hiOnly.trans hleaderOnly.symm)).elim
  exact ⟨leader,
    resetAwareNormalizedPrefixState_one hpsi ring hn leader C
      hnoActive hleader huniquePoint hrightLabel hleftNeutral
      hrightNeutral hleftReset hrightReset⟩

/-! ## Physical leader-count frontier -/

/-- One unit of mass for a physical leader bit and zero for a follower. -/
def physicalLeaderMass (u : AgentState psi) : Nat :=
  if u.leader then 1 else 0

/-- Physical leader mass on one interacting pair. -/
def physicalLeaderPairMass (l r : AgentState psi) : Nat :=
  physicalLeaderMass l + physicalLeaderMass r

/-- Number of physical leaders in a complete finite configuration. -/
def physicalLeaderCount (C : EConfig n psi kappa tau) : Nat :=
  (List.ofFn (fun i : Fin n =>
    physicalLeaderMass (C i).core.erase.core)).sum

/-- On a priority-open edge that already contains a physical leader, the
birth-signal transition cannot increase the pair's physical leader mass.
Follower/follower first birth is deliberately excluded from this contract. -/
theorem
    wallSweepBirthSignalZeroPathStall_priority_open_leaderPairMass_le
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hinput : l.core.erase.core.leader = true ∨
      r.core.erase.core.leader = true) :
    let q := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau l r
    physicalLeaderPairMass q.1.core.erase.core q.2.core.erase.core ≤
      physicalLeaderPairMass l.core.erase.core r.core.erase.core := by
  dsimp only
  let q := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau l r
  cases hl : l.core.erase.core.leader <;>
    cases hr : r.core.erase.core.leader
  · simp [hl, hr] at hinput
  · have hbirth :=
      wallSweepBirthSignalZeroPathStall_eq_of_right_leader
        hpsi kappa tau l r hr
    change q =
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r at hbirth
    have hreset :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_right_leader
        hpsi kappa tau l r hr
    have hnotBoth : ¬ (q.1.core.erase.core.leader = true ∧
        q.2.core.erase.core.leader = true) := by
      rw [hbirth, hreset]
      exact
        wallSweepPreCheckResetLeaderSinkPathStall_priority_open_left_follower_not_both
          hpsi l r hopen hl
    simp only [physicalLeaderPairMass, physicalLeaderMass, hl, hr]
    change (if q.1.core.erase.core.leader = true then 1 else 0) +
        (if q.2.core.erase.core.leader = true then 1 else 0) ≤ 1
    cases hqLeft : q.1.core.erase.core.leader <;>
      cases hqRight : q.2.core.erase.core.leader
    · simp
    · simp
    · simp
    · exact (hnotBoth ⟨hqLeft, hqRight⟩).elim
  · have hbirth :=
      wallSweepBirthSignalZeroPathStall_eq_of_left_leader
        hpsi kappa tau l r hl
    change q =
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r at hbirth
    have hreset :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau l r hl
    have hrightFollower : q.2.core.erase.core.leader = false := by
      rw [hbirth, hreset]
      exact
        wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_follower_of_initiator_leader
          hpsi l r hopen hl hr
    simp only [physicalLeaderPairMass, physicalLeaderMass, hl, hr]
    change (if q.1.core.erase.core.leader = true then 1 else 0) +
        (if q.2.core.erase.core.leader = true then 1 else 0) ≤ 1
    rw [hrightFollower]
    cases hqLeft : q.1.core.erase.core.leader <;> simp
  · simp only [physicalLeaderPairMass, physicalLeaderMass, hl, hr]
    change (if q.1.core.erase.core.leader = true then 1 else 0) +
        (if q.2.core.erase.core.leader = true then 1 else 0) ≤ 2
    cases hqLeft : q.1.core.erase.core.leader <;>
      cases hqRight : q.2.core.erase.core.leader <;>
      simp

/-- If both endpoints are leaders and the responder has nonzero label, the
rooted migration atomically merges the two leaders.  This is the exact strict
branch currently available for physical leader-count descent. -/
theorem
    wallSweepBirthSignalZeroPathStall_priority_open_two_leaders_nonzero_mass_lt
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlLeader : l.core.erase.core.leader = true)
    (hrLeader : r.core.erase.core.leader = true)
    (hrNonzero : r.core.erase.core.label ≠ ⟨0, hpsi⟩) :
    let q := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau l r
    physicalLeaderPairMass q.1.core.erase.core q.2.core.erase.core <
      physicalLeaderPairMass l.core.erase.core r.core.erase.core := by
  dsimp only
  let q := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau l r
  have hbirth :=
    wallSweepBirthSignalZeroPathStall_eq_of_right_leader
      hpsi kappa tau l r hrLeader
  change q =
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r at hbirth
  have hreset :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_right_leader
      hpsi kappa tau l r hrLeader
  have hmigrate :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_nonzero_responder_migrates
      hpsi l r hopen hrLeader hrNonzero
  have hleft : q.1.core.erase.core.leader = true := by
    rw [hbirth, hreset]
    exact hmigrate.1
  have hright : q.2.core.erase.core.leader = false := by
    rw [hbirth, hreset]
    exact hmigrate.2.1
  simp only [physicalLeaderPairMass, physicalLeaderMass, hlLeader, hrLeader]
  change (if q.1.core.erase.core.leader = true then 1 else 0) +
      (if q.2.core.erase.core.leader = true then 1 else 0) < 2
  rw [hleft, hright]
  decide

/-- A deletion-free local step on an edge already containing a leader is
globally leader-count nonincreasing. -/
theorem localStep_birthSignalZero_physicalLeaderCount_le_of_edge_leader
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hinput : (C e).core.erase.core.leader = true ∨
      (C (ring.rightNeighbor e)).core.erase.core.leader = true) :
    let D := localStep ring
      (wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau) C e
    physicalLeaderCount D ≤ physicalLeaderCount C := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hlocal :
      physicalLeaderPairMass q.1.core.erase.core q.2.core.erase.core ≤
        physicalLeaderPairMass
          (C e).core.erase.core (C j).core.erase.core := by
    exact wallSweepBirthSignalZeroPathStall_priority_open_leaderPairMass_le
      hpsi (C e) (C j) hopen (by simpa [j] using hinput)
  unfold physicalLeaderCount
  apply PPLLPpsiLeaderCreationRepair.sum_ofFn_le_of_pair_le
    (fun i => physicalLeaderMass (D i).core.erase.core)
    (fun i => physicalLeaderMass (C i).core.erase.core)
    e j (Ne.symm hje)
  · simpa [D, q, T, localStep, j, hje, physicalLeaderPairMass]
      using hlocal
  · intro i hie hij
    simp [D, T, localStep, j, hie, hij]

/-- An adjacent pair of leaders with a nonzero-label responder gives a strict
global physical leader-count step under the actual birth-signal transition. -/
theorem
    localStep_birthSignalZero_two_leaders_nonzero_physicalLeaderCount_lt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlLeader : (C e).core.erase.core.leader = true)
    (hrLeader :
      (C (ring.rightNeighbor e)).core.erase.core.leader = true)
    (hrNonzero :
      (C (ring.rightNeighbor e)).core.erase.core.label ≠ ⟨0, hpsi⟩) :
    let D := localStep ring
      (wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau) C e
    physicalLeaderCount D < physicalLeaderCount C := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hlocal :
      physicalLeaderPairMass q.1.core.erase.core q.2.core.erase.core <
        physicalLeaderPairMass
          (C e).core.erase.core (C j).core.erase.core := by
    exact
      wallSweepBirthSignalZeroPathStall_priority_open_two_leaders_nonzero_mass_lt
        hpsi (C e) (C j) hopen hlLeader
          (by simpa [j] using hrLeader)
          (by simpa [j] using hrNonzero)
  unfold physicalLeaderCount
  apply PPLLPpsiLeaderCreationRepair.sum_ofFn_lt_of_pair_lt
    (fun i => physicalLeaderMass (D i).core.erase.core)
    (fun i => physicalLeaderMass (C i).core.erase.core)
    e j (Ne.symm hje)
  · simpa [D, q, T, localStep, j, hje, physicalLeaderPairMass]
      using hlocal
  · intro i hie hij
    simp [D, T, localStep, j, hie, hij]

end PPLLWallSweepPreCheckAnchor
