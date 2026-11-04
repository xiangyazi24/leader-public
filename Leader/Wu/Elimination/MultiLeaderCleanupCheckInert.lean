import Leader.Wu.Elimination.MultiLeaderCleanupHiddenControl

/-!
# Check-inert pair contract for the multi-leader cleanup transition

The physical bridge proves that one priority-open interaction of the actual
`multiLeaderCleanupAuthorizedTransition` has exactly the five-field
`PeaceView` output of the isolated egress-sink Algorithm-15 kernel, under the
contract `MultiLeaderCleanupPhysicalPairReady`.  That contract demands the
literal idle records `CleanupLeftTailIdle`/`CleanupRightTailIdle` at the
pre-CHECK boundary: `state = .none`, `path = .bot`, `p_carry = false` and a
false permit.  Those fields are used only to make CHECK, DISAPPEAR and
action-one COMPARE literal identities.

This module proves that the five-field target never needed them.

* `compareActionOne_peaceViewPair`: action-one COMPARE is a premise-free
  `PeaceView` frame.
* `checkInert_authorizedDisappear_peaceViewPair`: DISAPPEAR is a premise-free frame.
* `checkSig_peaceViewPair_of_safe`: CHECK is a frame whenever the sanitized
  responder satisfies the existing stage-local predicate `CheckResponderSafe`
  (an existing leader, a nonterminal label, no carrier without stale equality,
  or a departing component).  This is the only fact CHECK consumes.
* `checkInertBefore_check_safe_of_aligned_neutral`: aligned comparison-neutral
  inputs produce that predicate through the actual reset-aware prefix, on
  every reset/leader configuration of the edge.
* `MultiLeaderCleanupCheckInertPairReady` replaces both idle records by that
  single responder condition, and
  `multiLeaderCleanupAuthorizedTransition_peaceView_eq_egressSink_of_checkInert`
  proves the same exact quotient theorem under it.  `ofPhysical` shows it is a
  weakening of the bridge contract.
* The compiled reset-free residual pair — a path-free `.produce`
  initiator beside a responder with a pre-existing `p_carry = true` — satisfies
  the new contract while refuting the old one, so its hidden control fields do
  not change the five-field output.

No protocol definition is changed; the theorems are about the current
transition.  No `let`-bound contract fields are used, so the statements are
syntactically stable under `rw`.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PhysicalBridge
namespace CheckInert

open PPLL PPLLRepair PPLLResearchFormulation PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLTerminalEqualSupportRepair PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepNormalResetContract PPLLWallSweepPreCheckResetRepair
  PPLLNoCheckBirthLeaderFrames PPLLNoCheckBirthBoundaryFrames
  PPLLNoCheckBirthConditionTwoFrames
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLWallSweepShieldCircuit
  PPLLPpsiLeaderCreationRepair

set_option autoImplicit false

variable {psi kappa : Nat}

/-! ## 1. Premise-free five-field frame of action-one COMPARE -/

private theorem compareSigInit_bulletFields (u : AgentState psi) :
    BulletFields.ofState (compareSigInit u) = BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState compareSigInit
    try dsimp only []
    repeat (first | rfl | split)

private theorem cmpUpdateReturnPriority_bulletFields_fst
    (hpsi : psi > 0) (l r : AgentState psi) :
    BulletFields.ofState (cmpUpdateReturnPriority hpsi l r).1 =
      BulletFields.ofState l := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState cmpUpdateReturnPriority
    try dsimp only []
    repeat (first | rfl | split)

private theorem cmpUpdateReturnPriority_bulletFields_snd
    (hpsi : psi > 0) (l r : AgentState psi) :
    BulletFields.ofState (cmpUpdateReturnPriority hpsi l r).2 =
      BulletFields.ofState r := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState cmpUpdateReturnPriority
    try dsimp only []
    repeat (first | rfl | split)

private theorem cmpUpdateSetPath2_bulletFields
    (hpsi : psi > 0) (u : AgentState psi) :
    BulletFields.ofState (cmpUpdateSetPath2 hpsi u) =
      BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState cmpUpdateSetPath2
    try dsimp only []
    repeat (first | rfl | split)

private theorem compareBitUpdateL_bulletFields
    (hpsi : psi > 0) (u : AgentState psi) :
    BulletFields.ofState (compareBitUpdateL hpsi u) =
      BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState compareBitUpdateL
    try dsimp only []
    repeat (first | rfl | split)

private theorem compareBitUpdateRActionOne_bulletFields
    (hpsi : psi > 0) (u : AgentState psi) :
    BulletFields.ofState (compareBitUpdateRActionOne hpsi u) =
      BulletFields.ofState u := by
  apply BulletFields.ext
  all_goals
    unfold BulletFields.ofState compareBitUpdateRActionOne
    try dsimp only []
    repeat (first | rfl | split)

private theorem compareBitActionOne_bulletFieldPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    bulletFieldPair (compareBitActionOne hpsi l r) =
      bulletFieldPair (l, r) := by
  apply Prod.ext
  · change BulletFields.ofState (compareBitUpdateL hpsi l) =
      BulletFields.ofState l
    exact compareBitUpdateL_bulletFields hpsi l
  · change BulletFields.ofState (compareBitUpdateRActionOne hpsi r) =
      BulletFields.ofState r
    exact compareBitUpdateRActionOne_bulletFields hpsi r

private theorem compareSigDispatchActionOne_bulletFieldPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    bulletFieldPair (compareSigDispatchActionOne hpsi l r) =
      bulletFieldPair (l, r) := by
  unfold compareSigDispatchActionOne
  split <;>
    first
      | exact compareBitActionOne_bulletFieldPair hpsi l r
      | rfl

private theorem authorizedCmpUpdate_bulletFieldPair'
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair (authorizedCmpUpdate hpsi l r) =
      authorizedBulletFieldPair (l, r) := by
  let allowed := freshComparisonStart hpsi l
  let lCore := if allowed && !comparisonActive l.core.state then
    { l.core with state := MainState.congest }
  else l.core
  let q := cmpUpdateReturnPriority hpsi lCore r.core
  have hlCore : BulletFields.ofState lCore = BulletFields.ofState l.core := by
    unfold lCore
    split <;> rfl
  have h1 : BulletFields.ofState (authorizedCmpUpdate hpsi l r).1.core =
      BulletFields.ofState l.core := by
    change BulletFields.ofState (cmpUpdateSetPath2 hpsi q.1) =
      BulletFields.ofState l.core
    exact (cmpUpdateSetPath2_bulletFields hpsi q.1).trans
      ((cmpUpdateReturnPriority_bulletFields_fst hpsi lCore r.core).trans
        hlCore)
  have h2 : BulletFields.ofState (authorizedCmpUpdate hpsi l r).2.core =
      BulletFields.ofState r.core := by
    change BulletFields.ofState q.2 = BulletFields.ofState r.core
    exact cmpUpdateReturnPriority_bulletFields_snd hpsi lCore r.core
  exact Prod.ext h1 h2

/-- Action-one COMPARE writes only `state`, `path`, and `path2`; the three
bullet fields of both endpoints are framed unconditionally. -/
theorem compareActionOne_bulletFieldPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedBulletFieldPair (authorizedCompareSigActionOne hpsi l r) =
      authorizedBulletFieldPair (l, r) := by
  let lCore := compareSigInit l.core
  let l0 : AuthorizedAgentState psi :=
    ⟨lCore, normalizePermit lCore l.path0Crossed⟩
  have hinit : BulletFields.ofState lCore = BulletFields.ofState l.core :=
    compareSigInit_bulletFields l.core
  unfold authorizedCompareSigActionOne
  dsimp only
  split
  · exact Prod.ext hinit rfl
  · split
    · exact Prod.ext hinit rfl
    · let q := authorizedCmpUpdate hpsi l0 r
      have hq := authorizedCmpUpdate_bulletFieldPair' hpsi l0 r
      have hout := compareSigDispatchActionOne_bulletFieldPair
        hpsi q.1.core q.2.core
      exact hout.trans (hq.trans (Prod.ext hinit rfl))

/-- **Premise-free five-field frame of the actual action-one COMPARE.**  This
is the strongest source-correct statement: the stage never writes `leader`,
`label`, `shield`, `bullet`, or `signal_B` on any input. -/
theorem compareActionOne_peaceViewPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (authorizedCompareSigActionOne hpsi l r) =
      authorizedPeaceViewPair (l, r) := by
  have hleaders := compareActionOne_leaders hpsi l r
  have hlabels := compareActionOne_labels hpsi l r
  have hbullets := compareActionOne_bulletFieldPair hpsi l r
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

/-! ## 2. Premise-free DISAPPEAR frame and the CHECK frame under safety -/

/-- DISAPPEAR writes only `state`, `path2`, `p`, and `p_carry`.  In particular
a pre-existing responder `p_carry` is invisible to the five-field target. -/
theorem checkInert_authorizedDisappear_peaceViewPair
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    authorizedPeaceViewPair (authorizedDisappear hpsi l r) =
      authorizedPeaceViewPair (l, r) := by
  have hleaders := PPLLVerify.disappear_leaders_eq hpsi l.core r.core
  have hlabels := PPLLVerify.disappear_labels_eq hpsi l.core r.core
  have hbullets := disappear_bulletFieldPair hpsi l.core r.core
  have hraw : peaceViewPair (disappear hpsi l.core r.core) =
      peaceViewPair (l.core, r.core) :=
    PPLLWallSweepNormalResetContract.peaceViewPair_eq_of_frames
      (Prod.ext hleaders.1 hleaders.2)
      (Prod.ext hlabels.1 hlabels.2)
      hbullets
  exact hraw

/-- CHECK writes `leader` only at a terminal `.equal` responder; on a
`CheckResponderSafe` responder it is a complete five-field frame.  Nothing is
assumed about the initiator: its `state`, `path`, or `p_carry` may be
arbitrary. -/
theorem checkSig_peaceViewPair_of_safe
    (hpsi : psi > 0) (l r : AgentState psi)
    (hsafe : CheckResponderSafe hpsi r) :
    peaceViewPair (checkSig hpsi l r) = peaceViewPair (l, r) := by
  have hleftLeader := PPLLVerify.checkSig_initiator_leader_eq hpsi l r
  have hrightLeader := checkSig_responder_leader_eq_of_safe hpsi l r hsafe
  have hlabels := PPLLVerify.checkSig_labels_eq hpsi l r
  have hbullets := checkSig_bulletFieldPair hpsi l r
  exact PPLLWallSweepNormalResetContract.peaceViewPair_eq_of_frames
    (Prod.ext hleftLeader hrightLeader)
    (Prod.ext hlabels.1 hlabels.2)
    hbullets

theorem authorizedCheckSig_peaceViewPair_of_safe
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hsafe : CheckResponderSafe hpsi r.core) :
    authorizedPeaceViewPair (authorizedCheckSig hpsi l r) =
      authorizedPeaceViewPair (l, r) := by
  exact checkSig_peaceViewPair_of_safe hpsi l.core r.core hsafe

/-- Pair-variable form: the right-hand side is the pair itself, so downstream
`Eq.trans` junctions are syntactic and never require structure eta on an
unevaluated boundary term. -/
theorem authorizedCheckSig_peaceViewPair_of_safe_pair
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hsafe : CheckResponderSafe hpsi q.2.core) :
    authorizedPeaceViewPair (authorizedCheckSig hpsi q.1 q.2) =
      authorizedPeaceViewPair q := by
  obtain ⟨a, b⟩ := q
  exact checkSig_peaceViewPair_of_safe hpsi a.core b.core hsafe

/-- Pair-variable form of the action-one COMPARE frame. -/
theorem compareActionOne_peaceViewPair_pair
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedPeaceViewPair (authorizedCompareSigActionOne hpsi q.1 q.2) =
      authorizedPeaceViewPair q := by
  obtain ⟨a, b⟩ := q
  exact compareActionOne_peaceViewPair hpsi a b

/-- Pair-variable form of the reset-kill SUPPRESS frame. -/
theorem authorizedSuppressSigResetKill_peaceViewPair_pair
    (hpsi : psi > 0)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    authorizedPeaceViewPair
        (authorizedReconcile (suppressSigResetKill hpsi) q.1 q.2) =
      authorizedPeaceViewPair q := by
  obtain ⟨a, b⟩ := q
  exact authorizedSuppressSigResetKill_peaceViewPair hpsi a b

/-! ## 3. Named pre-CHECK boundaries of the actual transition -/

/-- The exact sanitized CHECK input computed by the current transition on its
ordinary branch. -/
def checkInertBefore (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa
    (normalizeDeletion l) (normalizeDeletion r)

/-- The exact real-CHECK output computed by the current transition. -/
def checkInertAfter (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  wallSweepResetProbePreCheckResetAfterCheck hpsi kappa
    (normalizeDeletion l) (normalizeDeletion r)

theorem checkInertAfter_eq_check (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    checkInertAfter hpsi kappa l r =
      authorizedCheckSig hpsi
        (checkInertBefore hpsi kappa l r).1
        (checkInertBefore hpsi kappa l r).2 := by
  rfl

/-! ## 4. Producer: aligned neutral inputs are CHECK-safe through the real
reset-aware prefix -/

private theorem normalizeDeletion_eq_of_neutral'
    (u : AuthorizedAgentState psi) (h : ComparisonNeutral u.core) :
    normalizeDeletion u = u := by
  simp [normalizeDeletion, pathPresent, h.1, h.2.1]

/-- Terminal-equality sanitation of a comparison-neutral endpoint is
CHECK-safe: the endpoint stays pathless and never becomes `.equal`. -/
private theorem sanitizeAuthorizedTerminalEqual_check_safe_of_neutral
    (hpsi : psi > 0) (u : AuthorizedAgentState psi)
    (hn : ComparisonNeutral u.core) :
    CheckResponderSafe hpsi (sanitizeAuthorizedTerminalEqual hpsi u).core := by
  unfold CheckResponderSafe sanitizeAuthorizedTerminalEqual
  split
  · exact Or.inr (Or.inr (Or.inl ⟨hn.2.1, by simp⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hn.2.1, by simp [hn.1]⟩))

/-- **CHECK-safety feeder for the reset-aware prefix.**  On a stable edge with
comparison-neutral inputs, the sanitized responder of the actual
`wallSweepResetProbePreCheckResetBeforeCheck` is `CheckResponderSafe`,
whatever the leader/reset controls of the edge are.  When the pre-CHECK reset
wall fires, the responder is cleared and is safe by absence of a carrier;
otherwise the prefix is exactly the established no-reset prefix and the
shield-circuit producer applies. -/
theorem wallSweepResetProbePreCheckResetBeforeCheck_check_safe_of_aligned_neutral
    (hpsi : psi > 0) (kappa : Nat)
    (a b : AuthorizedAgentState psi)
    (halign : b.core.label =
      ⟨(a.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hl : ComparisonNeutral a.core) (hr : ComparisonNeutral b.core) :
    CheckResponderSafe hpsi
      (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa a b).2.core := by
  have hframe := wallSweepResetProbeAuthorizedBeforeCheck_resetEchoPair
    hpsi kappa a b
  have hnoReset := wallSweepResetProbeAuthorizedBeforeCheck_eq_of_no_reset
    hpsi kappa a b
  have hstage : wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa a b =
      sanitizeAuthorizedPair hpsi
        (preCheckResetWall
          (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa a b).1
          (wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa a b).2) := by
    rfl
  rw [hstage]
  generalize hq0 :
    wallSweepResetProbeAuthorizedBeforeCheck hpsi kappa a b = q0
  rw [hq0] at hframe hnoReset
  by_cases hsend : q0.1.core.leader = true ∨ q0.1.core.reset_cmd = true
  · have hn : ComparisonNeutral (preCheckResetWall q0.1 q0.2).2.core :=
      (preCheckResetWall_both_neutral_of_send q0.1 q0.2 hsend).2.1
    exact sanitizeAuthorizedTerminalEqual_check_safe_of_neutral hpsi _ hn
  · by_cases hrReset : q0.2.core.reset_cmd = true
    · have hn : ComparisonNeutral (preCheckResetWall q0.1 q0.2).2.core :=
        (preCheckResetWall_responder_neutral_of_reset q0.1 q0.2 hrReset).1
      exact sanitizeAuthorizedTerminalEqual_check_safe_of_neutral hpsi _ hn
    · have hlLeader : q0.1.core.leader = false := by
        cases h : q0.1.core.leader with
        | false => rfl
        | true => exact absurd (Or.inl h) hsend
      have hlReset : q0.1.core.reset_cmd = false := by
        cases h : q0.1.core.reset_cmd with
        | false => rfl
        | true => exact absurd (Or.inr h) hsend
      have hrReset' : q0.2.core.reset_cmd = false := by
        cases h : q0.2.core.reset_cmd with
        | false => rfl
        | true => exact absurd h hrReset
      have hinactive :=
        preCheckResetWall_eq_of_inactive q0.1 q0.2 hlLeader hlReset hrReset'
      rw [hinactive]
      have haReset : a.core.reset_cmd = false := by
        have h1 : q0.1.core.reset_cmd = a.core.reset_cmd :=
          congrArg (fun p => p.1.1) hframe
        exact h1.symm.trans hlReset
      have hq0' : q0 = wallSweepAuthorizedBeforeCheck hpsi kappa a b :=
        hnoReset haReset
      have hna := normalizeDeletion_eq_of_neutral' a hl
      have hnb := normalizeDeletion_eq_of_neutral' b hr
      have hsafe : CheckResponderSafe hpsi
          (sanitizeAuthorizedPair hpsi
            (wallSweepAuthorizedBeforeCheck hpsi kappa
              (normalizeDeletion a) (normalizeDeletion b))).2.core :=
        wallSweepNormalSanitizedStage_check_safe_of_aligned_neutral
          hpsi kappa a b halign hl hr
      rw [hna, hnb] at hsafe
      rw [hq0']
      exact hsafe

/-- The same producer at the normalized boundary used by the transition. -/
theorem checkInertBefore_check_safe_of_aligned_neutral
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hl : ComparisonNeutral l.core) (hr : ComparisonNeutral r.core) :
    CheckResponderSafe hpsi (checkInertBefore hpsi kappa l r).2.core := by
  unfold checkInertBefore
  rw [normalizeDeletion_eq_of_neutral' l hl,
    normalizeDeletion_eq_of_neutral' r hr]
  exact wallSweepResetProbePreCheckResetBeforeCheck_check_safe_of_aligned_neutral
    hpsi kappa l r halign hl hr

/-! ## 5. The check-inert pair contract -/

/-- Minimal pair contract for the exact five-field quotient theorem.  Compared
with `MultiLeaderCleanupPhysicalPairReady`, both literal idle records are
replaced by the single stage-local condition actually consumed by CHECK.  The
initiator's `state`, `path`, `p_carry`, WAIT controls, and both permits are
unconstrained; the responder may carry a pre-existing `p_carry`. -/
structure MultiLeaderCleanupCheckInertPairReady
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) : Prop where
  priority_open : AuthorizedPriorityOpen l r
  reset_ppsi_route :
    (normalizeDeletion r).core.leader = true ∨
      (normalizeDeletion r).core.label =
        ⟨((normalizeDeletion l).core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩
  responder_zero :
    r.core.leader = true → r.core.label = ⟨0, hpsi⟩
  check_inert :
    CheckResponderSafe hpsi (checkInertBefore hpsi kappa l r).2.core

namespace MultiLeaderCleanupCheckInertPairReady

/-- The bridge contract implies the check-inert contract: a right-idle
responder is pathless and not `.equal`. -/
theorem ofPhysical
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hready : MultiLeaderCleanupPhysicalPairReady hpsi kappa l r) :
    MultiLeaderCleanupCheckInertPairReady hpsi kappa l r := by
  have hright : CleanupRightTailIdle (checkInertBefore hpsi kappa l r).2 :=
    hready.right_idle
  refine
    { priority_open := hready.priority_open
      reset_ppsi_route := hready.reset_ppsi_route
      responder_zero := hready.responder_zero
      check_inert := ?_ }
  unfold CheckResponderSafe
  refine Or.inr (Or.inr (Or.inl ⟨hright.path_bot, ?_⟩))
  rw [hright.state_none]
  decide

/-- Aligned comparison-neutral inputs with a label-zero responder leader
satisfy the contract; no idle record is needed. -/
theorem ofAlignedNeutral
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (halign : r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hl : ComparisonNeutral l.core) (hr : ComparisonNeutral r.core)
    (hzero : r.core.leader = true → r.core.label = ⟨0, hpsi⟩) :
    MultiLeaderCleanupCheckInertPairReady hpsi kappa l r := by
  have hna := normalizeDeletion_eq_of_neutral' l hl
  have hnb := normalizeDeletion_eq_of_neutral' r hr
  refine
    { priority_open := hopen
      reset_ppsi_route := ?_
      responder_zero := hzero
      check_inert :=
        checkInertBefore_check_safe_of_aligned_neutral
          hpsi kappa l r halign hl hr }
  rw [hna, hnb]
  exact Or.inr halign

end MultiLeaderCleanupCheckInertPairReady

/-! ## 6. Prefix and CHECK views under the contract -/

private theorem pPsiLeaderResetProbeWall_peaceViewPair_of_route'
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

private theorem wallSweepResetProbePreCheckResetBeforeCheck_peaceViewPair_of_route'
    (hpsi : psi > 0) (kappa : Nat)
    (a b : AuthorizedAgentState psi)
    (hroute : b.core.leader = true ∨
      b.core.label =
        ⟨(a.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) :
    authorizedPeaceViewPair
        (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa a b) =
      authorizedPeaceViewPair (a, b) := by
  have hprobe :=
    wallSweepResetProbePreCheckResetBeforeCheck_peaceViewPair_eq_probe
      hpsi kappa a b
  have hcore := authorizedPPsiLeaderResetProbeWall_core hpsi a b
  have hwall : peaceViewPair (pPsiLeaderResetProbeWall hpsi a.core b.core) =
      peaceViewPair (a.core, b.core) :=
    pPsiLeaderResetProbeWall_peaceViewPair_of_route' hpsi a.core b.core hroute
  exact hprobe.trans ((congrArg peaceViewPair hcore).trans hwall)

/-- The pre-CHECK boundary of the transition frames the input `PeaceView`
under the reset/P-prime route clause alone. -/
theorem checkInertBefore_peaceViewPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hroute : (normalizeDeletion r).core.leader = true ∨
      (normalizeDeletion r).core.label =
        ⟨((normalizeDeletion l).core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩) :
    authorizedPeaceViewPair (checkInertBefore hpsi kappa l r) =
      authorizedPeaceViewPair (l, r) := by
  have hbefore :=
    wallSweepResetProbePreCheckResetBeforeCheck_peaceViewPair_of_route'
      hpsi kappa (normalizeDeletion l) (normalizeDeletion r) hroute
  have hnorm : authorizedPeaceViewPair
      (normalizeDeletion l, normalizeDeletion r) =
      authorizedPeaceViewPair (l, r) :=
    Prod.ext (normalizeDeletion_peaceView l) (normalizeDeletion_peaceView r)
  exact hbefore.trans hnorm

/-- Under the check-inert contract, real CHECK adds nothing to the five-field
view: the CHECK output pair has the input `PeaceView`. -/
theorem checkInertAfter_peaceViewPair
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hready : MultiLeaderCleanupCheckInertPairReady hpsi kappa l r) :
    authorizedPeaceViewPair (checkInertAfter hpsi kappa l r) =
      authorizedPeaceViewPair (l, r) := by
  rw [checkInertAfter_eq_check]
  have hcheck :=
    authorizedCheckSig_peaceViewPair_of_safe_pair hpsi
      (checkInertBefore hpsi kappa l r) hready.check_inert
  exact hcheck.trans
    (checkInertBefore_peaceViewPair hpsi kappa l r hready.reset_ppsi_route)

/-! ## 7. Post-CHECK suffix under a view equation only -/

/-- The post-CHECK suffix through Algorithm 14 is a `PeaceView` frame with no
idle premise: DISAPPEAR, action-one COMPARE, and reset-kill SUPPRESS never
write the five fields. -/
theorem multiLeaderSuffixThroughSuppress_peaceViewPair
    (hpsi : psi > 0) (a b : AuthorizedAgentState psi) :
    authorizedPeaceViewPair
        (authorizedReconcile (suppressSigResetKill hpsi)
          (authorizedCompareSigActionOne hpsi
            (authorizedDisappear hpsi a b).1
            (authorizedDisappear hpsi a b).2).1
          (authorizedCompareSigActionOne hpsi
            (authorizedDisappear hpsi a b).1
            (authorizedDisappear hpsi a b).2).2) =
      authorizedPeaceViewPair (a, b) := by
  have h0 := checkInert_authorizedDisappear_peaceViewPair hpsi a b
  have h1 := compareActionOne_peaceViewPair_pair hpsi
    (authorizedDisappear hpsi a b)
  have h2 := authorizedSuppressSigResetKill_peaceViewPair_pair hpsi
    (authorizedCompareSigActionOne hpsi
      (authorizedDisappear hpsi a b).1
      (authorizedDisappear hpsi a b).2)
  exact h2.trans (h1.trans h0)

/-- The complete post-CHECK suffix has the egress-sink kernel's five-field
output whenever its input pair has the `PeaceView` of the original endpoints
and any responder leader sits at label zero. -/
theorem multiLeaderAfterCheckSuffix_peaceView_of_view
    (hpsi : psi > 0)
    (l r : AuthorizedAgentState psi)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hview : authorizedPeaceViewPair q = authorizedPeaceViewPair (l, r))
    (hzero : r.core.leader = true → r.core.label = ⟨0, hpsi⟩) :
    authorizedPeaceViewPair (multiLeaderAfterCheckSuffix hpsi q.1 q.2) =
      peaceViewPair
        (eliminateLeadersNoCollisionEgressSink hpsi l.core r.core) := by
  obtain ⟨a, b⟩ := q
  show authorizedPeaceViewPair (multiLeaderAfterCheckSuffix hpsi a b) =
    peaceViewPair (eliminateLeadersNoCollisionEgressSink hpsi l.core r.core)
  have hq2 :=
    (multiLeaderSuffixThroughSuppress_peaceViewPair hpsi a b).trans hview
  exact cleanupKernelWrite_peaceView hpsi l r _ hq2 hzero

/-! ## 8. Exact quotient theorem under the check-inert contract -/

/-- **Five-field refinement under the check-inert contract.**  One
priority-open interaction of the actual `multiLeaderCleanupAuthorizedTransition`
has exactly the `PeaceView` output of the isolated egress-sink Algorithm-15
kernel.  Unlike the bridge theorem, no `state = .none`, `path = .bot`, or
`p_carry = false` premise is used at either endpoint. -/
theorem multiLeaderCleanupAuthorizedTransition_peaceView_eq_egressSink_of_checkInert
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hready : MultiLeaderCleanupCheckInertPairReady hpsi kappa l r) :
    authorizedPeaceViewPair
        (multiLeaderCleanupAuthorizedTransition hpsi kappa l r) =
      peaceViewPair
        (eliminateLeadersNoCollisionEgressSink
          hpsi l.core r.core) := by
  have htransition :
      multiLeaderCleanupAuthorizedTransition hpsi kappa l r =
        markLeaderBirth
          (leaderBirthBeforeOrAtCheck
            (normalizeDeletion l) (normalizeDeletion r)
            (checkInertBefore hpsi kappa l r)
            (checkInertAfter hpsi kappa l r))
          (multiLeaderAfterCheckSuffix hpsi
            (checkInertAfter hpsi kappa l r).1
            (checkInertAfter hpsi kappa l r).2) :=
    multiLeaderCleanupAuthorizedTransition_of_priority_open
      hpsi kappa l r hready.priority_open
  have hafter : authorizedPeaceViewPair (checkInertAfter hpsi kappa l r) =
      authorizedPeaceViewPair (l, r) :=
    checkInertAfter_peaceViewPair hpsi kappa l r hready
  have htail := multiLeaderAfterCheckSuffix_peaceView_of_view hpsi l r
    (checkInertAfter hpsi kappa l r) hafter hready.responder_zero
  rw [htransition, markLeaderBirth_peaceViewPair]
  exact htail

/-- The bridge's `CleanupPhysicalView` is a function of the `PeaceView`. -/
private theorem cleanupPhysicalViewOfState_eq_of_peaceView'
    {u v : AgentState psi}
    (h : PeaceView.ofState u = PeaceView.ofState v) :
    cleanupPhysicalViewOfState u = cleanupPhysicalViewOfState v := by
  unfold cleanupPhysicalViewOfState
  exact congrArg _ h

/-- `CleanupPhysicalView` form of the same theorem. -/
theorem multiLeaderCleanupAuthorizedTransition_cleanupPhysicalView_eq_egressSink_of_checkInert
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hready : MultiLeaderCleanupCheckInertPairReady hpsi kappa l r) :
    authorizedCleanupPhysicalViewPair
        (multiLeaderCleanupAuthorizedTransition hpsi kappa l r) =
      cleanupPhysicalViewPair
        (eliminateLeadersNoCollisionEgressSink
          hpsi l.core r.core) := by
  have h :=
    multiLeaderCleanupAuthorizedTransition_peaceView_eq_egressSink_of_checkInert
      hpsi kappa l r hready
  have h1 : PeaceView.ofState
      (multiLeaderCleanupAuthorizedTransition hpsi kappa l r).1.core =
      PeaceView.ofState
        (eliminateLeadersNoCollisionEgressSink hpsi l.core r.core).1 :=
    congrArg Prod.fst h
  have h2 : PeaceView.ofState
      (multiLeaderCleanupAuthorizedTransition hpsi kappa l r).2.core =
      PeaceView.ofState
        (eliminateLeadersNoCollisionEgressSink hpsi l.core r.core).2 :=
    congrArg Prod.snd h
  exact Prod.ext
    (cleanupPhysicalViewOfState_eq_of_peaceView' h1)
    (cleanupPhysicalViewOfState_eq_of_peaceView' h2)

/-! ## 9. Regression: the compiled reset-free residual pair -/

section Q5577Residual

open PPLLCompleteMultiLeaderCleanup.PhysicalBridge.Q5577HiddenControlAudit

private theorem traceHPsi' : TracePsi > 0 := by
  decide

/-- Deletion normalization is inert on both residual endpoints. -/
theorem q5577_residual_normalizeDeletion :
    normalizeDeletion remainingResetFreeLeft = remainingResetFreeLeft ∧
      normalizeDeletion remainingResetFreeRight = remainingResetFreeRight := by
  constructor <;> decide

/-- The prefix only moves the residual pair's labels through the reset-aware
P-prime wall, which is a non-barrier edge here; the responder stays at label
one, which is nonterminal for `psi = 3`. -/
theorem q5577_residual_responder_label :
    (wallSweepResetProbePreCheckResetBeforeCheck traceHPsi' TraceKappa
      remainingResetFreeLeft remainingResetFreeRight).2.core.label =
      (1 : Fin TracePsi) := by
  have hctrl := wallSweepResetProbePreCheckResetBeforeCheck_ppsiControlPair
    traceHPsi' TraceKappa remainingResetFreeLeft remainingResetFreeRight
  have hlabel :
      (wallSweepResetProbePreCheckResetBeforeCheck traceHPsi' TraceKappa
        remainingResetFreeLeft remainingResetFreeRight).2.core.label =
      (pPsiLeaderResetProbeWall traceHPsi'
        remainingResetFreeLeft.core remainingResetFreeRight.core).2.label :=
    congrArg (fun q => q.2.label) hctrl
  have hwall :
      (pPsiLeaderResetProbeWall traceHPsi'
        remainingResetFreeLeft.core remainingResetFreeRight.core).2.label =
      (1 : Fin TracePsi) := by
    decide
  exact hlabel.trans hwall

/-- The residual boundary responder is CHECK-safe by the nonterminal clause,
independently of its pre-existing `p_carry` and of the initiator's `.produce`. -/
theorem q5577_residual_check_safe :
    CheckResponderSafe traceHPsi'
      (checkInertBefore traceHPsi' TraceKappa
        remainingResetFreeLeft remainingResetFreeRight).2.core := by
  unfold checkInertBefore
  rw [q5577_residual_normalizeDeletion.1, q5577_residual_normalizeDeletion.2]
  unfold CheckResponderSafe
  refine Or.inr (Or.inl ?_)
  rw [q5577_residual_responder_label]
  decide

/-- The compiled reset-free residual pair satisfies the new contract. -/
theorem q5577_residual_checkInert_ready :
    MultiLeaderCleanupCheckInertPairReady traceHPsi' TraceKappa
      remainingResetFreeLeft remainingResetFreeRight where
  priority_open := by decide
  reset_ppsi_route := Or.inr (by decide)
  responder_zero := fun h => absurd h (by decide)
  check_inert := q5577_residual_check_safe

/-- The same pair refutes the bridge's left-idle record at the same boundary:
the initiator is a path-free `.produce`.  (Imported from the compiled audit.) -/
theorem q5577_residual_old_left_idle_fails :
    ¬ CleanupLeftTailIdle
      (checkInertBefore traceHPsi' TraceKappa
        remainingResetFreeLeft remainingResetFreeRight).1 := by
  unfold checkInertBefore
  rw [q5577_residual_normalizeDeletion.1, q5577_residual_normalizeDeletion.2]
  exact combined_remaining_reset_free_not_left_idle

/-- Hence the hidden-control fields of the residual pair (initiator
`state = .produce`, `path = .bot`, `wait = false`; responder `p_carry = true`)
do not change the five-field output of the complete authorized transition. -/
theorem q5577_residual_transition_peaceView :
    authorizedPeaceViewPair
        (multiLeaderCleanupAuthorizedTransition traceHPsi' TraceKappa
          remainingResetFreeLeft remainingResetFreeRight) =
      peaceViewPair
        (eliminateLeadersNoCollisionEgressSink traceHPsi'
          remainingResetFreeLeft.core remainingResetFreeRight.core) :=
  multiLeaderCleanupAuthorizedTransition_peaceView_eq_egressSink_of_checkInert
    traceHPsi' TraceKappa remainingResetFreeLeft remainingResetFreeRight
    q5577_residual_checkInert_ready

end Q5577Residual

end CheckInert
end PhysicalBridge
end PPLLCompleteMultiLeaderCleanup
