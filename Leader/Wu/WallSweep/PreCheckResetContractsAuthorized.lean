import Leader.Wu.WallSweep.PreCheckResetContractsNormalized

/-!
# Pre-CHECK reset contracts: Authorized

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

/-! ## Complete priority-open authorized contracts -/

/-- The first output endpoint keeps the initiating endpoint's label.  Keeping
this as a named proposition prevents projection reduction from unfolding the
entire full-wall transition during theorem elaboration. -/
inductive AuthorizedInitiatorLabelFrame
    (input : AuthorizedAgentState psi)
    (output : AuthorizedAgentState psi × AuthorizedAgentState psi) : Prop where
  | intro (witness : AuthorizedAgentState psi × AuthorizedAgentState psi)
      (witness_eq : witness = output)
      (label_eq : witness.1.core.label = input.core.label)

theorem AuthorizedInitiatorLabelFrame.exact_eq
    {input : AuthorizedAgentState psi}
    {output : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : AuthorizedInitiatorLabelFrame input output) :
    output.1.core.label = input.core.label := by
  rcases h with ⟨witness, hwitness, hlabel⟩
  rw [← hwitness]
  exact hlabel

theorem AuthorizedInitiatorLabelFrame.of_pair_eq
    (input : AuthorizedAgentState psi)
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hab : a = b) (hb : AuthorizedInitiatorLabelFrame input b) :
    AuthorizedInitiatorLabelFrame input a := by
  rcases hb with ⟨witness, hwitness, hlabel⟩
  exact ⟨witness, hwitness.trans hab.symm, hlabel⟩

private theorem AuthorizedInitiatorLabelFrame.of_output_label_eq
    (input : AuthorizedAgentState psi)
    {before after : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hout : after.1.core.label = before.1.core.label)
    (hbefore : AuthorizedInitiatorLabelFrame input before) :
    AuthorizedInitiatorLabelFrame input after :=
  ⟨after, rfl, hout.trans hbefore.exact_eq⟩

private theorem AuthorizedInitiatorLabelFrame.retarget
    {a b : AuthorizedAgentState psi}
    {q : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : AuthorizedInitiatorLabelFrame a q)
    (hab : a.core.label = b.core.label) :
    AuthorizedInitiatorLabelFrame b q := by
  rcases h with ⟨witness, hwitness, hlabel⟩
  exact ⟨witness, hwitness, hlabel.trans hab⟩

/-- The post-Algorithm-14 boundary preserves a shielded initiating leader. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  exact afterSuppress_initiator_anchor_of_eq hpsi
    (pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0)
    (out := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r)
    (wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
      hpsi kappa l r)
    (wallSweepPreCheckResetBeforeSuppress_initiator_anchor
      hpsi kappa l0 r0 (normalizeDeletion_initiator_anchor l h))

/-- The post-Algorithm-14 boundary preserves a label-zero responder leader on
an edge covered by an initiator reset. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_responder_zero_of_left_reset
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = true)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderZeroAnchor hpsi
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 : l0.core.reset_cmd = true := by
    unfold l0 normalizeDeletion
    split <;> exact hlReset
  exact afterSuppress_responder_zero_anchor_of_eq hpsi
    (pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0)
    (out := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r)
    (wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
      hpsi kappa l r)
    (wallSweepPreCheckResetBeforeSuppress_responder_zero_of_left_reset
      hpsi kappa l0 r0 hl0
        (normalizeDeletion_responder_zero_anchor hpsi r h))

/-- Transport a responder-zero anchor backward across an equality of
authorized output pairs.  The namespace-local copy in
`WallSweepNormalResetContract` is private, so the pre-CHECK contracts keep
their own. -/
private theorem responderZeroAnchor_of_pair_eq
    (hpsi : psi > 0)
    {a b : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (hab : a = b) (hb : authorizedResponderZeroAnchor hpsi b) :
    authorizedResponderZeroAnchor hpsi a := by
  rw [hab]
  exact hb

/-- An existing label-zero responder leader is framed by the complete
pre-Algorithm-15 prefix even without an initiator reset premise.  The
leader/probe wall frames the existing responder, the pre-CHECK reset wall and
real CHECK retain its zero anchor, and repaired Algorithm 14 changes neither
leader nor label. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_responder_zero_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderZeroAnchor hpsi
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  have hr0 : ResponderZeroAnchor hpsi r0.core :=
    normalizeDeletion_responder_zero_anchor hpsi r h
  have hraw :
      beforeRaw.2.core.leader = true ∧
      beforeRaw.1.core.label = l0.core.label ∧
      beforeRaw.2.core.label = r0.core.label := by
    simpa only [beforeRaw] using
      (wallSweepAuthorizedBeforeCheck_responder_frame_of_responder_leader
        hpsi kappa l0 r0 hr0.1)
  have hrawAnchor : authorizedResponderZeroAnchor hpsi beforeRaw := by
    exact ⟨hraw.1, hraw.2.2.trans hr0.2⟩
  have hcheck := preCheckResetCheckTail_responder_zero_anchor
    hpsi beforeRaw hrawAnchor
  have hpreEq :=
    wallSweepPreCheckResetBeforeSuppress_eq_checkTail
      hpsi kappa l0 r0
  have hpre : authorizedResponderZeroAnchor hpsi pre :=
    responderZeroAnchor_of_pair_eq hpsi hpreEq hcheck
  exact afterSuppress_responder_zero_anchor_of_eq hpsi
    (pre := pre)
    (out := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r)
    (wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
      hpsi kappa l r)
    hpre

/-- The repaired Algorithm-14 boundary preserves a fresh P-prime
barrier/probe birth.  Orphan-deletion normalization changes none of the four
physical premises. -/
theorem wallSweepPreCheckResetNormalAfterSuppress_barrier_probe_birth
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hprobe : r.core.probe = true)
    (hbarrier : isBarrier hpsi l.core r.core) :
    authorizedResponderZeroAnchor hpsi
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 : l0.core.leader = false :=
    (normalizeDeletion_leader_eq l).trans hl
  have hr0 : r0.core.leader = false :=
    (normalizeDeletion_leader_eq r).trans hr
  have hprobe0 : r0.core.probe = true :=
    (normalizeDeletion_probe_eq r).trans hprobe
  have hbarrier0 : isBarrier hpsi l0.core r0.core :=
    (normalizeDeletion_isBarrier_iff hpsi l r).2 hbarrier
  exact afterSuppress_responder_zero_anchor_of_eq hpsi
    (pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0)
    (out := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r)
    (wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
      hpsi kappa l r)
    (wallSweepPreCheckResetBeforeSuppress_barrier_probe_birth
      hpsi kappa l0 r0 hl0 hr0 hprobe0 hbarrier0)

private theorem beforeSuppress_label_of_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    AuthorizedInitiatorLabelFrame l
      (wallSweepPreCheckResetBeforeSuppress hpsi kappa l r) := by
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l r
  have hraw := wallSweepAuthorizedBeforeCheck_initiator_anchor
    hpsi kappa l r h
  exact ⟨wallSweepPreCheckResetBeforeSuppress hpsi kappa l r, rfl,
    wallSweepPreCheckResetBeforeSuppress_label_of_send
      hpsi kappa l r (.inl hraw.1)⟩

private theorem beforeSuppress_label_of_left_reset
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = true) :
    AuthorizedInitiatorLabelFrame l
      (wallSweepPreCheckResetBeforeSuppress hpsi kappa l r) := by
  have hreset := beforeRaw_left_reset_true hpsi kappa l r hlReset
  exact ⟨wallSweepPreCheckResetBeforeSuppress hpsi kappa l r, rfl,
    wallSweepPreCheckResetBeforeSuppress_label_of_send
      hpsi kappa l r (.inr hreset)⟩

private theorem afterSuppress_label_of_before
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlabel : AuthorizedInitiatorLabelFrame (normalizeDeletion l)
      (wallSweepPreCheckResetBeforeSuppress hpsi kappa
        (normalizeDeletion l) (normalizeDeletion r))) :
    AuthorizedInitiatorLabelFrame l
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l0 r0
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  rcases hlabel with ⟨witness, hwitness, hwitnessLabel⟩
  have hpreLabel : authorizedInitiatorLabel pre = l0.core.label :=
    (initiatorLabel_eq_of_authorizedPair_eq hwitness.symm).trans
      hwitnessLabel
  have heq := initiatorLabel_eq_of_authorizedPair_eq
    (wallSweepPreCheckResetNormalAfterSuppress_eq_reconcile
      hpsi kappa l r)
  have hrec := authorizedReconcile_initiatorLabel_frame_of_raw
    (suppressSigResetKill hpsi) pre
      (suppressSigResetKill_left_label_eq
        hpsi pre.1.core pre.2.core)
  exact ⟨after, rfl, heq.trans (hrec.trans
    (hpreLabel.trans (normalizeDeletion_label_eq l)))⟩

theorem normalTail_eq_postSuppress
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
    wallSweepPreCheckResetNormalTail hpsi kappa l r =
      authorizedPostSuppress hpsi after.1 after.2 := by
  rfl

/-- Algorithm 15 and gated WRITE preserve the initiating shielded leader. -/
theorem wallSweepPreCheckResetNormalTail_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) := by
  exact normalTail_initiator_anchor_of_eq hpsi
    (before := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r)
    (after := wallSweepPreCheckResetNormalTail hpsi kappa l r)
    (normalTail_eq_postSuppress hpsi kappa l r)
    (wallSweepPreCheckResetNormalAfterSuppress_initiator_anchor
      hpsi kappa l r h)

/-- A reset-covered label-zero responder leader survives the ordinary tail. -/
theorem wallSweepPreCheckResetNormalTail_responder_zero_survives
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = true)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderLeader
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) := by
  exact normalTail_responder_survives_of_eq hpsi
    (before := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r)
    (after := wallSweepPreCheckResetNormalTail hpsi kappa l r)
    (normalTail_eq_postSuppress hpsi kappa l r)
    (wallSweepPreCheckResetNormalAfterSuppress_responder_zero_of_left_reset
      hpsi kappa l r hlReset h)

/-- No-collision elimination and gated WRITE preserve the responder leader
created by the fresh barrier/probe return. -/
theorem wallSweepPreCheckResetNormalTail_barrier_probe_birth_survives
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hprobe : r.core.probe = true)
    (hbarrier : isBarrier hpsi l.core r.core) :
    authorizedResponderLeader
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) := by
  exact normalTail_responder_survives_of_eq hpsi
    (before := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r)
    (after := wallSweepPreCheckResetNormalTail hpsi kappa l r)
    (normalTail_eq_postSuppress hpsi kappa l r)
    (wallSweepPreCheckResetNormalAfterSuppress_barrier_probe_birth
      hpsi kappa l r hl hr hprobe hbarrier)

/-- The same fresh barrier/probe leader survives the rooted leader-sink tail.
The new Algorithm-15 guard preserves the responder's zero-label anchor before
the unchanged gated WRITE stage. -/
theorem wallSweepPreCheckResetLeaderSinkNormalTail_barrier_probe_birth_survives
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hprobe : r.core.probe = true)
    (hbarrier : isBarrier hpsi l.core r.core) :
    authorizedResponderLeader
      (wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r) := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  change authorizedResponderLeader
    (authorizedPostSuppressLeaderSink hpsi after.1 after.2)
  exact authorizedPostSuppressLeaderSink_responder_zero_survives
    hpsi after.1 after.2
      (wallSweepPreCheckResetNormalAfterSuppress_barrier_probe_birth
        hpsi kappa l r hl hr hprobe hbarrier)

/-- The rooted leader-sink tail retains the zero label assigned by the
barrier/probe birth, in addition to retaining the newborn responder leader. -/
theorem wallSweepPreCheckResetLeaderSinkNormalTail_barrier_probe_birth_zero
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hprobe : r.core.probe = true)
    (hbarrier : isBarrier hpsi l.core r.core) :
    authorizedResponderZeroAnchor hpsi
      (wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r) := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  change authorizedResponderZeroAnchor hpsi
    (authorizedPostSuppressLeaderSink hpsi after.1 after.2)
  exact authorizedPostSuppressLeaderSink_responder_zero_anchor
    hpsi after.1 after.2
      (wallSweepPreCheckResetNormalAfterSuppress_barrier_probe_birth
        hpsi kappa l r hl hr hprobe hbarrier)

/-- Independently of how the prefix produced it, a responder leader remaining
after the complete rooted leader-sink normal tail is hosted at label zero. -/
theorem wallSweepPreCheckResetLeaderSinkNormalTail_responder_leader_zero
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    let out := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
    out.2.core.leader = true → out.2.core.label = ⟨0, hpsi⟩ := by
  dsimp only
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  have heq : wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r =
      authorizedPostSuppressLeaderSink hpsi after.1 after.2 := rfl
  intro hout
  have hleader := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.leader) heq
  have hout' : (authorizedPostSuppressLeaderSink
      hpsi after.1 after.2).2.core.leader = true :=
    hleader.symm.trans hout
  have hzero := authorizedPostSuppressLeaderSink_responder_leader_zero
    hpsi after.1 after.2 hout'
  have hlabel := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.label) heq
  exact hlabel.trans hzero

private theorem normalTail_label_of_after
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlabel : AuthorizedInitiatorLabelFrame l
      (wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r)) :
    AuthorizedInitiatorLabelFrame l
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) := by
  let after := wallSweepPreCheckResetNormalAfterSuppress hpsi kappa l r
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  rcases hlabel with ⟨witness, hwitness, hwitnessLabel⟩
  have hafterLabel : authorizedInitiatorLabel after = l.core.label :=
    (initiatorLabel_eq_of_authorizedPair_eq hwitness.symm).trans
      hwitnessLabel
  have hpost := authorizedPostSuppress_initiator_label_eq
    hpsi after.1 after.2
  have heq := initiatorLabel_eq_of_authorizedPair_eq
    (normalTail_eq_postSuppress hpsi kappa l r)
  exact ⟨tail, rfl, heq.trans (hpost.trans hafterLabel)⟩

private theorem markComparisonForDeletion_initiator_anchor
    (u : AuthorizedAgentState psi) (h : InitiatorAnchor u.core) :
    InitiatorAnchor (markComparisonForDeletion u).core := by
  unfold markComparisonForDeletion
  cases u.core.path <;> exact h

theorem markLeaderBirth_initiator_anchor
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (h : authorizedInitiatorAnchor q) :
    authorizedInitiatorAnchor (markLeaderBirth born q) := by
  unfold markLeaderBirth
  split
  · exact markComparisonForDeletion_initiator_anchor q.1 h
  · exact h

private theorem markLeaderBirth_responder_leader
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (h : authorizedResponderLeader q) :
    authorizedResponderLeader (markLeaderBirth born q) := by
  unfold markLeaderBirth
  split
  · unfold markComparisonForDeletion
    cases q.2.core.path <;> exact h
  · exact h

private theorem markLeaderBirth_responder_zero_anchor
    (hpsi : psi > 0) (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (h : authorizedResponderZeroAnchor hpsi q) :
    authorizedResponderZeroAnchor hpsi (markLeaderBirth born q) := by
  unfold markLeaderBirth
  split
  · unfold markComparisonForDeletion
    cases q.2.core.path <;> exact h
  · exact h

private theorem markLeaderBirth_initiator_label_eq
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (markLeaderBirth born q).1.core.label = q.1.core.label := by
  unfold markLeaderBirth
  split
  · unfold markComparisonForDeletion
    cases q.1.core.path <;> rfl
  · rfl

private theorem markLeaderBirth_responder_label_eq
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (markLeaderBirth born q).2.core.label = q.2.core.label := by
  unfold markLeaderBirth
  split
  · unfold markComparisonForDeletion
    cases q.2.core.path <;> rfl
  · rfl

/-- A priority-open corrected edge preserves a shielded initiating leader. -/
theorem wallSweepPreCheckResetAuthorized_priority_open_initiator_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (h : InitiatorAnchor l.core) :
    authorizedInitiatorAnchor
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  have heq :=
    wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at heq
  rw [heq]
  exact markLeaderBirth_initiator_anchor born tail
    (wallSweepPreCheckResetNormalTail_initiator_anchor hpsi kappa l r h)

/-- On a priority-open reset-covered edge, a label-zero responder leader
survives every repaired wrapper. -/
theorem wallSweepPreCheckResetAuthorized_priority_open_responder_zero_survives
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlReset : l.core.reset_cmd = true)
    (h : ResponderZeroAnchor hpsi r.core) :
    authorizedResponderLeader
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  have heq :=
    wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at heq
  rw [heq]
  exact markLeaderBirth_responder_leader born tail
    (wallSweepPreCheckResetNormalTail_responder_zero_survives
      hpsi kappa l r hlReset h)

/-- On a priority-open edge, the complete authorized repair preserves the
first leader produced when a responder probe returns across a barrier. -/
theorem wallSweepPreCheckResetAuthorized_priority_open_barrier_probe_birth
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hprobe : r.core.probe = true)
    (hbarrier : isBarrier hpsi l.core r.core) :
    authorizedResponderLeader
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  have heq :=
    wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at heq
  rw [heq]
  exact markLeaderBirth_responder_leader born tail
    (wallSweepPreCheckResetNormalTail_barrier_probe_birth_survives
      hpsi kappa l r hl hr hprobe hbarrier)

/-- On a priority-open edge, the rooted leader-sink transition preserves the
same first barrier/probe birth as the established pre-CHECK reset repair. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_barrier_probe_birth
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hprobe : r.core.probe = true)
    (hbarrier : isBarrier hpsi l.core r.core) :
    authorizedResponderLeader
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
  have heq :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r = markLeaderBirth born tail at heq
  rw [heq]
  exact markLeaderBirth_responder_leader born tail
    (wallSweepPreCheckResetLeaderSinkNormalTail_barrier_probe_birth_survives
      hpsi kappa l r hl hr hprobe hbarrier)

/-- On the decisive priority-open barrier/probe edge, the complete rooted
leader-sink interaction retains the exact label-zero responder birth. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_barrier_probe_birth_zero
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hl : l.core.leader = false) (hr : r.core.leader = false)
    (hprobe : r.core.probe = true)
    (hbarrier : isBarrier hpsi l.core r.core) :
    authorizedResponderZeroAnchor hpsi
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
  have heq :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r = markLeaderBirth born tail at heq
  rw [heq]
  exact markLeaderBirth_responder_zero_anchor hpsi born tail
    (wallSweepPreCheckResetLeaderSinkNormalTail_barrier_probe_birth_zero
      hpsi kappa l r hl hr hprobe hbarrier)

/-- On every priority-open rooted leader-sink call, any leader remaining at
the responder endpoint is at label zero. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_responder_leader_zero
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r) :
    let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    out.2.core.leader = true → out.2.core.label = ⟨0, hpsi⟩ := by
  dsimp only
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  have heq :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r = markLeaderBirth born tail at heq
  intro hout
  have hmarkLeaders := markLeaderBirth_leaders_eq born tail
  have htailLeader : tail.2.core.leader = true := by
    have hright := congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.2.core.leader) heq
    exact hmarkLeaders.2.symm.trans (hright.symm.trans hout)
  have htailZero :=
    wallSweepPreCheckResetLeaderSinkNormalTail_responder_leader_zero
      hpsi kappa l r htailLeader
  have hmarkLabel := markLeaderBirth_responder_label_eq born tail
  have hrightLabel := congrArg
    (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      q.2.core.label) heq
  exact hrightLabel.trans (hmarkLabel.trans htailZero)

/-- On a priority-open physical edge, an existing nonzero-label responder
leader crosses to the initiator through the complete rooted transition.  The
pre-CHECK prefix and real CHECK frame the leader's host; the rooted WRITE
suffix performs the migration; birth bookkeeping frames both leaders and
labels. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_nonzero_responder_migrates
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hrLeader : r.core.leader = true)
    (hrNonzero : r.core.label ≠ ⟨0, hpsi⟩) :
    let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    out.1.core.leader = true ∧
      out.2.core.leader = false ∧
      out.1.core.label = l.core.label ∧
      out.2.core.label = r.core.label := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeCheck := wallSweepPreCheckResetBeforeCheck
    hpsi kappa l0 r0
  let afterCheck := wallSweepPreCheckResetAfterCheck
    hpsi kappa l0 r0
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  have hr0Leader : r0.core.leader = true :=
    (normalizeDeletion_leader_eq r).trans hrLeader
  have hr0Label : r0.core.label = r.core.label :=
    normalizeDeletion_label_eq r
  have hl0Label : l0.core.label = l.core.label :=
    normalizeDeletion_label_eq l
  have hr0Nonzero : r0.core.label ≠ ⟨0, hpsi⟩ := by
    intro hzero
    exact hrNonzero (hr0Label.symm.trans hzero)
  have hafter :=
    wallSweepPreCheckResetAfterCheck_responder_frame_of_responder_leader
      hpsi kappa l0 r0 hr0Leader
  have hafterNonzero : afterCheck.2.core.label ≠ ⟨0, hpsi⟩ := by
    intro hzero
    exact hr0Nonzero (hafter.2.2.symm.trans hzero)
  have hmigrate := wallSweepLeaderSinkAfterCheckSuffix_nonzero_responder_migrates
    hpsi afterCheck.1 afterCheck.2 hafter.1 hafterNonzero
  have htailEq :=
    wallSweepPreCheckResetLeaderSinkNormalTail_eq_afterCheckSuffix
      hpsi kappa l r
  change tail = wallSweepLeaderSinkAfterCheckSuffix
    hpsi afterCheck.1 afterCheck.2 at htailEq
  have htailLeftLeader : tail.1.core.leader = true :=
    (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.1.core.leader) htailEq).trans hmigrate.1
  have htailRightFollower : tail.2.core.leader = false :=
    (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.2.core.leader) htailEq).trans hmigrate.2.1
  have htailLeftLabel : tail.1.core.label = l.core.label :=
    (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.1.core.label) htailEq).trans
      (hmigrate.2.2.1.trans (hafter.2.1.trans hl0Label))
  have htailRightLabel : tail.2.core.label = r.core.label :=
    (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.2.core.label) htailEq).trans
      (hmigrate.2.2.2.trans (hafter.2.2.trans hr0Label))
  have heq :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change out = markLeaderBirth born tail at heq
  have hleaders := markLeaderBirth_leaders_eq born tail
  have hlabels := markLeaderBirth_labels_eq born tail
  change out.1.core.leader = true ∧
    out.2.core.leader = false ∧
    out.1.core.label = l.core.label ∧
    out.2.core.label = r.core.label
  exact ⟨(congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.1.core.leader) heq).trans (hleaders.1.trans htailLeftLeader),
    (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.2.core.leader) heq).trans
      (hleaders.2.trans htailRightFollower),
    (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.1.core.label) heq).trans (hlabels.1.trans htailLeftLabel),
    (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.2.core.label) heq).trans (hlabels.2.trans htailRightLabel)⟩

private theorem normalTail_label_of_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) (h : InitiatorAnchor l.core) :
    AuthorizedInitiatorLabelFrame l
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hbefore := beforeSuppress_label_of_anchor hpsi kappa l0 r0
    (normalizeDeletion_initiator_anchor l h)
  exact normalTail_label_of_after hpsi kappa l r
    (afterSuppress_label_of_before hpsi kappa l r hbefore)

private theorem normalTail_label_of_left_reset
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlReset : l.core.reset_cmd = true) :
    AuthorizedInitiatorLabelFrame l
      (wallSweepPreCheckResetNormalTail hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 : l0.core.reset_cmd = true := by
    unfold l0 normalizeDeletion
    split <;> exact hlReset
  have hbefore := beforeSuppress_label_of_left_reset
    hpsi kappa l0 r0 hl0
  exact normalTail_label_of_after hpsi kappa l r
    (afterSuppress_label_of_before hpsi kappa l r hbefore)

/-- Priority-open corrected edges frame the initiator label whenever the edge
is covered by the designated leader anchor. -/
theorem wallSweepPreCheckResetAuthorized_priority_open_label_of_anchor
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (h : InitiatorAnchor l.core) :
    AuthorizedInitiatorLabelFrame l
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  have heq :=
    wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at heq
  have hmark := markLeaderBirth_initiator_label_eq born tail
  apply AuthorizedInitiatorLabelFrame.of_pair_eq l heq
  exact ⟨markLeaderBirth born tail, rfl,
    hmark.trans (normalTail_label_of_anchor hpsi kappa l r h).exact_eq⟩

/-- Priority-open corrected edges frame the initiator label whenever an
existing reset covers the edge. -/
theorem wallSweepPreCheckResetAuthorized_priority_open_label_of_left_reset
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlReset : l.core.reset_cmd = true) :
    AuthorizedInitiatorLabelFrame l
      (wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r) := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  let beforeRaw := wallSweepAuthorizedBeforeCheck hpsi kappa l0 r0
  let beforeReset := preCheckResetWall beforeRaw.1 beforeRaw.2
  let beforeCheck := sanitizeAuthorizedPair hpsi beforeReset
  let afterCheck := authorizedCheckSig hpsi beforeCheck.1 beforeCheck.2
  let born := leaderBirthBeforeOrAtCheck l0 r0 beforeCheck afterCheck
  let tail := wallSweepPreCheckResetNormalTail hpsi kappa l r
  have heq :=
    wallSweepPreCheckResetAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change wallSweepPreCheckResetAuthorizedTransition hpsi kappa l r =
    markLeaderBirth born tail at heq
  have hmark := markLeaderBirth_initiator_label_eq born tail
  apply AuthorizedInitiatorLabelFrame.of_pair_eq l heq
  exact ⟨markLeaderBirth born tail, rfl, hmark.trans
    (normalTail_label_of_left_reset hpsi kappa l r hlReset).exact_eq⟩


end PPLLWallSweepPreCheckResetContracts
