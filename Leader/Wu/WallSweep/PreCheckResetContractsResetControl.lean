import Leader.Wu.WallSweep.PreCheckResetContractsCore

/-!
# Pre-CHECK reset contracts: ResetControl

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

/-- Exact comparison/reset/echo contract for a follower carrying reset.  The
left echo records the terminal return precisely in terms of the final
responder label, so the same structure covers both ordinary and closing
clockwise edges. -/
structure AuthorizedResetFollowerControlOutput
    (hpsi : psi > 0)
    (input output : AuthorizedAgentState psi ×
      AuthorizedAgentState psi) : Prop where
  left_neutral : ComparisonNeutral output.1.core
  right_neutral : ComparisonNeutral output.2.core
  left_reset_false : output.1.core.reset_cmd = false
  right_reset_exact : output.2.core.reset_cmd = !input.2.core.echo
  right_echo_false : output.2.core.echo = false
  left_echo_exact : output.1.core.echo =
    if output.2.core.label = ⟨psi - 1, by omega⟩ then true
    else input.1.core.echo

theorem AuthorizedResetFollowerControlOutput.of_pair_eq
    {hpsi : psi > 0}
    {input a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hab : a = b)
    (hb : AuthorizedResetFollowerControlOutput hpsi input b) :
    AuthorizedResetFollowerControlOutput hpsi input a := by
  rw [hab]
  exact hb

/-- The follower-reset control contract depends on its input only through the
left and right echo bits.  This transports a suffix certificate across an
earlier prefix that frames those two bits. -/
theorem AuthorizedResetFollowerControlOutput.of_input_echo_eq
    {hpsi : psi > 0}
    {input₁ input₂ output : AuthorizedAgentState psi ×
      AuthorizedAgentState psi}
    (hleft : input₁.1.core.echo = input₂.1.core.echo)
    (hright : input₁.2.core.echo = input₂.2.core.echo)
    (hcontrol : AuthorizedResetFollowerControlOutput hpsi input₁ output) :
    AuthorizedResetFollowerControlOutput hpsi input₂ output := by
  exact {
    left_neutral := hcontrol.left_neutral
    right_neutral := hcontrol.right_neutral
    left_reset_false := hcontrol.left_reset_false
    right_reset_exact := hcontrol.right_reset_exact.trans
      (congrArg (fun b : Bool => !b) hright)
    right_echo_false := hcontrol.right_echo_false
    left_echo_exact := by
      calc
        output.1.core.echo =
            if output.2.core.label = ⟨psi - 1, by omega⟩ then true
            else input₁.1.core.echo := hcontrol.left_echo_exact
        _ = if output.2.core.label = ⟨psi - 1, by omega⟩ then true
            else input₂.1.core.echo := by rw [hleft] }

/-- Physical/path-stall form of the exact follower-reset control contract. -/
structure ExpiringResetFollowerControlOutput
    (hpsi : psi > 0)
    (input output : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop where
  left_neutral : ComparisonNeutral output.1.core.erase.core
  right_neutral : ComparisonNeutral output.2.core.erase.core
  left_reset_false : output.1.core.erase.core.reset_cmd = false
  right_reset_exact : output.2.core.erase.core.reset_cmd =
    !input.2.core.erase.core.echo
  right_echo_false : output.2.core.erase.core.echo = false
  left_echo_exact : output.1.core.erase.core.echo =
    if output.2.core.erase.core.label = ⟨psi - 1, by omega⟩ then true
    else input.1.core.erase.core.echo

/-- An echo at the responder cancels a leader- or reset-generated token after
both comparison carriers have been cleared. -/
theorem suppressSigResetKill_source_echo_collision
    (hpsi : psi > 0) (l r : AgentState psi)
    (hsource : l.leader = true ∨ l.reset_cmd = true)
    (hrEcho : r.echo = true) :
    let q := suppressSigResetKill hpsi l r
    ComparisonNeutral q.1 ∧ ComparisonNeutral q.2 ∧
      q.1.reset_cmd = false ∧ q.2.reset_cmd = false ∧
      q.2.echo = false := by
  rcases hsource with hleader | hreset
  · simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
      resetKillComparison, clearComparisonSignal, ComparisonNeutral,
      suppressSigTerminal, suppressSigEcho, suppressSigFinish,
      hleader, hrEcho]
  · by_cases hleader : l.leader = true
    · simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
        resetKillComparison, clearComparisonSignal, ComparisonNeutral,
        suppressSigTerminal, suppressSigEcho, suppressSigFinish,
        hleader, hrEcho]
    · have hleaderFalse : l.leader = false := by
        cases h : l.leader <;> simp_all
      simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
        resetKillComparison, clearComparisonSignal, ComparisonNeutral,
        suppressSigTerminal, suppressSigEcho, suppressSigFinish,
        hleaderFalse, hreset, hrEcho]

/-- Exact reset/echo behavior of a leader- or reset-covered Algorithm-14 edge.
The responder reset is precisely the negation of its input echo; terminal echo
creation is retained on a follower initiator and consumed on a leader. -/
theorem suppressSigResetKill_source_reset_echo_exact
    (hpsi : psi > 0) (l r : AgentState psi)
    (hsource : l.leader = true ∨ l.reset_cmd = true) :
    let q := suppressSigResetKill hpsi l r
    q.1.reset_cmd = false ∧ q.2.reset_cmd = !r.echo ∧
      q.2.echo = false ∧
      q.1.echo = if l.leader = true then false
        else if r.label = ⟨psi - 1, by omega⟩ then true else l.echo := by
  rcases hsource with hleader | hreset
  · simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
      resetKillComparison, clearComparisonSignal, suppressSigTerminal,
      suppressSigEcho, suppressSigFinish, hleader]
  · by_cases hleader : l.leader = true
    · simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
        resetKillComparison, clearComparisonSignal, suppressSigTerminal,
        suppressSigEcho, suppressSigFinish, hleader]
    · have hleaderFalse : l.leader = false := by
        cases h : l.leader <;> simp_all
      cases hrEcho : r.echo <;>
        simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
          resetKillComparison, clearComparisonSignal, suppressSigTerminal,
          suppressSigEcho, suppressSigFinish, hleaderFalse, hreset, hrEcho]

/-- Once real CHECK has left a follower/reset source, the complete rooted
post-CHECK suffix realizes the exact collision-or-handoff control contract.
No input label alignment is assumed. -/
theorem wallSweepLeaderSinkAfterCheckSuffix_reset_follower_control
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = true) :
    AuthorizedResetFollowerControlOutput hpsi (l, r)
      (wallSweepLeaderSinkAfterCheckSuffix hpsi l r) := by
  let q0 := authorizedDisappear hpsi l r
  let q1 := authorizedCompareSig hpsi q0.1 q0.2
  let raw := suppressSigResetKill hpsi q1.1.core q1.2.core
  let q2 := authorizedReconcile
    (suppressSigResetKill hpsi) q1.1 q1.2
  let q3 := authorizedPostSuppressLeaderSink hpsi q2.1 q2.2
  have h0ctl := authorizedDisappear_resetEchoPair hpsi l r
  have h1ctl := authorizedCompareSig_resetEchoPair hpsi q0.1 q0.2
  have h1ctl' : authorizedResetEchoPair q1 =
      authorizedResetEchoPair q0 :=
    authorizedResetEchoPair_eq_trans h1ctl
      (authorizedResetEchoPair_eta q0)
  have hpreCtl : authorizedResetEchoPair q1 =
      authorizedResetEchoPair (l, r) :=
    authorizedResetEchoPair_eq_trans h1ctl' h0ctl
  have hpreFields := resetEcho_fields_of_pair_eq hpreCtl
  have hpreReset : q1.1.core.reset_cmd = true :=
    hpreFields.1.trans hlReset
  have h0Leaders := authorizedDisappear_leaders_eq hpsi l r
  have h1Leaders := authorizedCompareSig_leaders_eq hpsi q0.1 q0.2
  have hpreFollower : q1.1.core.leader = false :=
    h1Leaders.1.trans (h0Leaders.1.trans hlFollower)
  have hrawExact := suppressSigResetKill_source_reset_echo_exact
    hpsi q1.1.core q1.2.core (.inr hpreReset)
  change raw.1.reset_cmd = false ∧
      raw.2.reset_cmd = !q1.2.core.echo ∧
      raw.2.echo = false ∧
      raw.1.echo = if q1.1.core.leader = true then false
        else if q1.2.core.label = ⟨psi - 1, by omega⟩ then true
        else q1.1.core.echo at hrawExact
  have hrawNeutral : ComparisonNeutral raw.1 ∧
      ComparisonNeutral raw.2 := by
    by_cases he : q1.2.core.echo = true
    · have hc := suppressSigResetKill_source_echo_collision
        hpsi q1.1.core q1.2.core (.inr hpreReset) he
      exact ⟨hc.1, hc.2.1⟩
    · have he0 : q1.2.core.echo = false := by
        cases h : q1.2.core.echo
        · rfl
        · exact (he h).elim
      have hn := suppressSigResetKill_handoff
        hpsi q1.1.core q1.2.core hpreReset he0
      exact ⟨hn.1, hn.2.1⟩
  have hq2Neutral : ComparisonNeutral q2.1.core ∧
      ComparisonNeutral q2.2.core := hrawNeutral
  have hpostNeutral := authorizedPostSuppressLeaderSink_neutral
    hpsi q2.1 q2.2 hq2Neutral.1 hq2Neutral.2
  have hpostCtl := resetEcho_fields_of_pair_eq
    (authorizedPostSuppressLeaderSink_resetEchoPair hpsi q2.1 q2.2)
  have hpostLabels := authorizedPostSuppressLeaderSink_labels_eq
    hpsi q2.1 q2.2
  have hq2RightLabel : q2.2.core.label = q1.2.core.label :=
    suppressSigResetKill_right_label_eq hpsi q1.1.core q1.2.core
  have hq3RightLabel : q3.2.core.label = q1.2.core.label :=
    hpostLabels.2.trans hq2RightLabel
  have hrawLeftEcho : raw.1.echo =
      if q1.2.core.label = ⟨psi - 1, by omega⟩ then true
      else l.core.echo := by
    calc
      raw.1.echo = if q1.1.core.leader = true then false
          else if q1.2.core.label = ⟨psi - 1, by omega⟩ then true
          else q1.1.core.echo := hrawExact.2.2.2
      _ = if q1.2.core.label = ⟨psi - 1, by omega⟩ then true
          else l.core.echo := by
        simp [hpreFollower, hpreFields.2.1]
  change AuthorizedResetFollowerControlOutput hpsi (l, r) q3
  exact {
    left_neutral := hpostNeutral.1
    right_neutral := hpostNeutral.2
    left_reset_false := hpostCtl.1.trans hrawExact.1
    right_reset_exact := by
      calc
        q3.2.core.reset_cmd = q2.2.core.reset_cmd := hpostCtl.2.2.1
        _ = !q1.2.core.echo := hrawExact.2.1
        _ = !r.core.echo := by rw [hpreFields.2.2.2]
    right_echo_false := hpostCtl.2.2.2.trans hrawExact.2.2.1
    left_echo_exact := by
      calc
        q3.1.core.echo = q2.1.core.echo := hpostCtl.2.1
        _ = raw.1.echo := rfl
        _ = if q1.2.core.label = ⟨psi - 1, by omega⟩ then true
            else l.core.echo := hrawLeftEcho
        _ = if q3.2.core.label = ⟨psi - 1, by omega⟩ then true
            else l.core.echo := by rw [hq3RightLabel] }

/-- Priority openness selects the single marked ordinary suffix of the
integrated reset-aware transition.  Naming this branch equation prevents
every downstream field projection from reopening the complete transition. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_marked_suffix_of_priority_open
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let beforeCheck := wallSweepResetProbePreCheckResetBeforeCheck
      hpsi kappa l0 r0
    let afterCheck := wallSweepResetProbePreCheckResetAfterCheck
      hpsi kappa l0 r0
    let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r =
      markLeaderBirth born
        (wallSweepLeaderSinkAfterCheckSuffix
          hpsi afterCheck.1 afterCheck.2) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  change deletionActive l0 = false ∧ deletionActive r0 = false at hopen
  have hrInactive : ¬deletionActive r0 = true := by
    rw [hopen.2]
    decide
  have hlInactive : ¬deletionActive l0 = true := by
    rw [hopen.1]
    decide
  unfold wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
  dsimp only
  rw [if_neg hrInactive, if_neg hlInactive]

/-- On a priority-open follower/reset/follower edge, the integrated complete
transition returns two followers.  This closes the same-interaction stale
barrier gap: neither P-prime nor CHECK nor the rooted suffix can create a new
leader while the reset token crosses that edge. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_followers_of_reset_source
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false) :
    let q := wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    q.1.core.leader = false ∧ q.2.core.leader = false := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0Follower : l0.core.leader = false :=
    (normalizeDeletion_leader_eq l).trans hlFollower
  have hr0Follower : r0.core.leader = false :=
    (normalizeDeletion_leader_eq r).trans hrFollower
  have hnormalize := normalizeDeletionPair_resetEcho l r
  have hl0Reset : l0.core.reset_cmd = true :=
    (resetEcho_fields_of_pair_eq hnormalize).1.trans hlReset
  let beforeCheck := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let afterCheck := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  have hafter : afterCheck.1.core.leader = false ∧
      afterCheck.2.core.leader = false :=
    wallSweepResetProbePreCheckResetAfterCheck_followers_of_reset_source
      hpsi kappa l0 r0 hl0Follower hl0Reset hr0Follower
  let tail := wallSweepLeaderSinkAfterCheckSuffix
    hpsi afterCheck.1 afterCheck.2
  have htail : tail.1.core.leader = false ∧
      tail.2.core.leader = false :=
    wallSweepLeaderSinkAfterCheckSuffix_followers_of_followers
      hpsi afterCheck.1 afterCheck.2 hafter.1 hafter.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have hmark := markLeaderBirth_leaders_eq born tail
  have hstage :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_marked_suffix_of_priority_open
      hpsi kappa l r hopen
  change wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r = markLeaderBirth born tail at hstage
  rw [hstage]
  exact ⟨hmark.1.trans htail.1, hmark.2.trans htail.2⟩

/-- On every priority-open source/follower edge, the complete integrated
transition retains the source label and installs its exact successor at the
responder.  No input alignment premise is required. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_source_follower_labels
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hsource : l.core.leader = true ∨ l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false) :
    let q := wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    q.1.core.label = l.core.label ∧
      q.2.core.label =
        ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hnormalize := resetEcho_fields_of_pair_eq
    (normalizeDeletionPair_resetEcho l r)
  have hsource0 : l0.core.leader = true ∨
      l0.core.reset_cmd = true := by
    rcases hsource with hleader | hreset
    · exact .inl ((normalizeDeletion_leader_eq l).trans hleader)
    · exact .inr (hnormalize.1.trans hreset)
  have hrFollower0 : r0.core.leader = false :=
    (normalizeDeletion_leader_eq r).trans hrFollower
  let beforeCheck := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let afterCheck := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  have hafter :=
    wallSweepResetProbePreCheckResetAfterCheck_source_follower_labels
      hpsi kappa l0 r0 hsource0 hrFollower0
  rw [normalizeDeletion_label_eq l] at hafter
  let tail := wallSweepLeaderSinkAfterCheckSuffix
    hpsi afterCheck.1 afterCheck.2
  have htail := wallSweepLeaderSinkAfterCheckSuffix_labels_eq
    hpsi afterCheck.1 afterCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have hmark := markLeaderBirth_labels_eq born tail
  have hstage :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_marked_suffix_of_priority_open
      hpsi kappa l r hopen
  change wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r = markLeaderBirth born tail at hstage
  rw [hstage]
  exact ⟨hmark.1.trans (htail.1.trans hafter.1),
    hmark.2.trans (htail.2.trans hafter.2)⟩

/-- The normalized real-CHECK output feeds an exact rooted suffix control
certificate, translated back to the original input reset/echo fields. -/
theorem wallSweepResetProbePreCheckResetLeaderSinkTail_reset_follower_control
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let afterCheck := wallSweepResetProbePreCheckResetAfterCheck
      hpsi kappa l0 r0
    let tail := wallSweepLeaderSinkAfterCheckSuffix
      hpsi afterCheck.1 afterCheck.2
    AuthorizedResetFollowerControlOutput hpsi (l, r) tail := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hnorm := normalizeDeletionPair_resetEcho l r
  have hnormFields := resetEcho_fields_of_pair_eq hnorm
  have hl0Follower : l0.core.leader = false :=
    (normalizeDeletion_leader_eq l).trans hlFollower
  have hr0Follower : r0.core.leader = false :=
    (normalizeDeletion_leader_eq r).trans hrFollower
  have hl0Reset : l0.core.reset_cmd = true :=
    hnormFields.1.trans hlReset
  let afterCheck := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  have hafterPair0 :=
    wallSweepResetProbePreCheckResetAfterCheck_resetEchoPair
      hpsi kappa l0 r0
  have hafterPair : authorizedResetEchoPair afterCheck =
      authorizedResetEchoPair (l, r) :=
    authorizedResetEchoPair_eq_trans hafterPair0 hnorm
  have hafterFields := resetEcho_fields_of_pair_eq hafterPair
  have hafterFollowers :=
    wallSweepResetProbePreCheckResetAfterCheck_followers_of_reset_source
      hpsi kappa l0 r0 hl0Follower hl0Reset hr0Follower
  have hafterReset : afterCheck.1.core.reset_cmd = true :=
    hafterFields.1.trans hlReset
  let tail := wallSweepLeaderSinkAfterCheckSuffix
    hpsi afterCheck.1 afterCheck.2
  have htail := wallSweepLeaderSinkAfterCheckSuffix_reset_follower_control
    hpsi afterCheck.1 afterCheck.2 hafterFollowers.1 hafterReset
  exact AuthorizedResetFollowerControlOutput.of_input_echo_eq
    hafterFields.2.1 hafterFields.2.2.2 htail

/-- A marked birth is inert on any output already certified comparison-neutral
on both endpoints. -/
theorem markLeaderBirth_eq_of_reset_follower_control
    (born : Bool)
    {hpsi : psi > 0}
    {input output : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hcontrol : AuthorizedResetFollowerControlOutput hpsi input output) :
    markLeaderBirth born output = output :=
  markLeaderBirth_eq_of_neutral born output
    hcontrol.left_neutral hcontrol.right_neutral

/-- On a priority-open follower/reset/follower edge, the marked authorized
branch is exactly its rooted post-CHECK suffix. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_tail_of_reset_follower
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false) :
    let l0 := normalizeDeletion l
    let r0 := normalizeDeletion r
    let afterCheck := wallSweepResetProbePreCheckResetAfterCheck
      hpsi kappa l0 r0
    let tail := wallSweepLeaderSinkAfterCheckSuffix
      hpsi afterCheck.1 afterCheck.2
    wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l r = tail := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeCheck := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let afterCheck := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  let tail := wallSweepLeaderSinkAfterCheckSuffix
    hpsi afterCheck.1 afterCheck.2
  have htailInput :=
    wallSweepResetProbePreCheckResetLeaderSinkTail_reset_follower_control
      hpsi kappa l r hlFollower hlReset hrFollower
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  have hmark := markLeaderBirth_eq_of_reset_follower_control born htailInput
  have hstage :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_marked_suffix_of_priority_open
      hpsi kappa l r hopen
  change wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r = markLeaderBirth born tail at hstage
  exact hstage.trans hmark

/-- The complete integrated priority-open follower/reset/follower edge has an
exact control result for both possible responder-echo values.  A false echo
moves reset right; a true echo cancels it, while both cases leave neutral
comparisons and consume the responder echo. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_exists_reset_follower_control
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = true)
    (hrFollower : r.core.leader = false) :
    ∃ output, output =
        wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
          hpsi kappa l r ∧
      AuthorizedResetFollowerControlOutput hpsi (l, r) output := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeCheck := wallSweepResetProbePreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let afterCheck := wallSweepResetProbePreCheckResetAfterCheck
    hpsi kappa l0 r0
  let tail := wallSweepLeaderSinkAfterCheckSuffix
    hpsi afterCheck.1 afterCheck.2
  have hout :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_eq_tail_of_reset_follower
      hpsi kappa l r hopen hlFollower hlReset hrFollower
  have htailInput :=
    wallSweepResetProbePreCheckResetLeaderSinkTail_reset_follower_control
      hpsi kappa l r hlFollower hlReset hrFollower
  exact ⟨tail, hout.symm, htailInput⟩

/-- Finite reification and path-stall expiry preserve the same follower-pair
result on a reset-covered edge. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_followers_of_reset_source
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlFollower : l.core.erase.core.leader = false)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hrFollower : r.core.erase.core.leader = false) :
    let q :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r
    q.1.core.erase.core.leader = false ∧
      q.2.core.erase.core.leader = false := by
  let bounded :=
    wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
      hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_followers_of_reset_source
      hpsi kappa l.core.erase r.core.erase hopen
        hlFollower hlReset hrFollower
  have he :=
    erase_wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
      hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change bounded.1.erase =
    (wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  change bounded.2.erase =
    (wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbaseL : lBase.core.erase.core.leader = false := by
    change bounded.1.erase.core.leader = false
    rw [hL]
    exact ha.1
  have hbaseR : rBase.core.erase.core.leader = false := by
    change bounded.2.erase.core.leader = false
    rw [hR]
    exact ha.2
  have hLf := deletionPriorityExpireOne_path_frame l lBase
  have hRf := deletionPriorityExpireOne_path_frame r rBase
  rw [wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_expiryStages]
  exact ⟨hLf.2.1.trans hbaseL, hRf.2.1.trans hbaseR⟩

/-- Finite reification and path-stall expiry preserve the newly established
successor labels of the integrated reset-aware edge. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_source_follower_labels
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hsource : l.core.erase.core.leader = true ∨
      l.core.erase.core.reset_cmd = true)
    (hrFollower : r.core.erase.core.leader = false) :
    let q :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r
    q.1.core.erase.core.label = l.core.erase.core.label ∧
      q.2.core.erase.core.label =
        ⟨(l.core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := by
  let bounded :=
    wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
      hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha :=
    wallSweepResetProbePreCheckResetLeaderSinkAuthorized_source_follower_labels
      hpsi kappa l.core.erase r.core.erase hopen hsource hrFollower
  have he := erase_wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change bounded.1.erase =
    (wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  change bounded.2.erase =
    (wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbaseL : lBase.core.erase.core.label =
      l.core.erase.core.label := by
    change bounded.1.erase.core.label = l.core.erase.core.label
    rw [hL]
    exact ha.1
  have hbaseR : rBase.core.erase.core.label =
      ⟨(l.core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ := by
    change bounded.2.erase.core.label = _
    rw [hR]
    exact ha.2
  have hLf := deletionPriorityExpireOne_path_frame l lBase
  have hRf := deletionPriorityExpireOne_path_frame r rBase
  rw [wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_expiryStages]
  exact ⟨hLf.2.2.1.trans hbaseL, hRf.2.2.1.trans hbaseR⟩

/-- Path-stall expiry preserves a neutral comparison carrier together with
the six protocol fields used by source-covered retry steps. -/
theorem deletionPriorityExpireOne_neutral_fields
    (old out : ExpiringAgentState psi kappa tau)
    (hneutral : ComparisonNeutral out.core.erase.core) :
    let q := deletionPriorityExpireOne tau old out
    ComparisonNeutral q.core.erase.core ∧
      q.core.erase.core.leader = out.core.erase.core.leader ∧
      q.core.erase.core.label = out.core.erase.core.label ∧
      q.core.erase.core.reset_cmd = out.core.erase.core.reset_cmd ∧
      q.core.erase.core.echo = out.core.erase.core.echo ∧
      q.core.erase.core.shield = out.core.erase.core.shield := by
  have hframe := deletionPriorityExpireOne_path_frame old out
  refine ⟨?_, hframe.2.1, hframe.2.2.1, hframe.2.2.2.1,
    hframe.2.2.2.2.1, deletionPriorityExpireOne_shield_frame old out⟩
  unfold deletionPriorityExpireOne
  split
  · exact hneutral
  · unfold pathExpireOne
    split
    · exact hneutral
    · split
      · simp [ComparisonNeutral, clearComparisonCarrier,
          AuthorizedBoundedAgentState.erase, BoundedAgentState.erase]
        rfl
      · exact hneutral

/-- Path-stall expiration may clear comparison carriers or update only the
stall counter, but it never changes shield, bullet, or absence-signal fields
of the already computed physical output. -/
theorem deletionPriorityExpireOne_bulletFields
    (old out : ExpiringAgentState psi kappa tau) :
    BulletFields.ofState
        (deletionPriorityExpireOne tau old out).core.erase.core =
      BulletFields.ofState out.core.erase.core := by
  apply BulletFields.ext
  · exact deletionPriorityExpireOne_shield_frame old out
  · unfold deletionPriorityExpireOne pathExpireOne
    repeat (first | rfl | split)
  · unfold deletionPriorityExpireOne pathExpireOne
    repeat (first | rfl | split)

/-- Bounded reification and path-stall expiry preserve the exact
collision-or-handoff control result of a priority-open follower/reset/follower
edge. -/
theorem
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_exists_reset_follower_control
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlFollower : l.core.erase.core.leader = false)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hrFollower : r.core.erase.core.leader = false) :
    ∃ output, output =
        wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau l r ∧
      ExpiringResetFollowerControlOutput hpsi (l, r) output := by
  let bounded :=
    wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
      hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  rcases
      wallSweepResetProbePreCheckResetLeaderSinkAuthorized_exists_reset_follower_control
      hpsi kappa l.core.erase r.core.erase hopen
        hlFollower hlReset hrFollower with
    ⟨authorizedOut, hauthorizedOut, ha⟩
  have he := erase_wallSweepResetProbePreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change bounded.1.erase =
    (wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  change bounded.2.erase =
    (wallSweepResetProbePreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hL' : bounded.1.erase = authorizedOut.1 :=
    hL.trans (congrArg Prod.fst hauthorizedOut).symm
  have hR' : bounded.2.erase = authorizedOut.2 :=
    hR.trans (congrArg Prod.snd hauthorizedOut).symm
  have hbaseLNeutral : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hL']
    exact ha.left_neutral
  have hbaseRNeutral : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hR']
    exact ha.right_neutral
  have hbaseLReset : lBase.core.erase.core.reset_cmd = false := by
    change bounded.1.erase.core.reset_cmd = false
    rw [hL']
    exact ha.left_reset_false
  have hbaseRReset : rBase.core.erase.core.reset_cmd =
      !r.core.erase.core.echo := by
    change bounded.2.erase.core.reset_cmd = !r.core.erase.core.echo
    rw [hR']
    exact ha.right_reset_exact
  have hbaseREcho : rBase.core.erase.core.echo = false := by
    change bounded.2.erase.core.echo = false
    rw [hR']
    exact ha.right_echo_false
  have hbaseLEcho : lBase.core.erase.core.echo =
      if rBase.core.erase.core.label = ⟨psi - 1, by omega⟩ then true
      else l.core.erase.core.echo := by
    change bounded.1.erase.core.echo =
      if bounded.2.erase.core.label = ⟨psi - 1, by omega⟩ then true
      else l.core.erase.core.echo
    rw [hL', hR']
    exact ha.left_echo_exact
  have hLf := deletionPriorityExpireOne_neutral_fields
    l lBase hbaseLNeutral
  have hRf := deletionPriorityExpireOne_neutral_fields
    r rBase hbaseRNeutral
  let output : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau :=
    (deletionPriorityExpireOne tau l lBase,
      deletionPriorityExpireOne tau r rBase)
  have hactual :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_expiryStages
      hpsi kappa tau l r
  change wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r = output at hactual
  have houtput : ExpiringResetFollowerControlOutput hpsi (l, r) output := {
    left_neutral := hLf.1
    right_neutral := hRf.1
    left_reset_false := hLf.2.2.2.1.trans hbaseLReset
    right_reset_exact := hRf.2.2.2.1.trans hbaseRReset
    right_echo_false := hRf.2.2.2.2.1.trans hbaseREcho
    left_echo_exact := by
      calc
        (deletionPriorityExpireOne tau l lBase).core.erase.core.echo =
            lBase.core.erase.core.echo := hLf.2.2.2.2.1
        _ = if rBase.core.erase.core.label =
              ⟨psi - 1, by omega⟩ then true
            else l.core.erase.core.echo := hbaseLEcho
        _ = if (deletionPriorityExpireOne tau r rBase).core.erase.core.label =
              ⟨psi - 1, by omega⟩ then true
            else l.core.erase.core.echo := by rw [hRf.2.2.1] }
  exact ⟨output, hactual.symm, houtput⟩


end PPLLWallSweepPreCheckResetContracts
