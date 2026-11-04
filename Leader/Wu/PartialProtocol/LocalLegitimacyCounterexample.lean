import Leader.Wu.PartialProtocol.DomainClosure

/-!
# Unconditional local-legitimacy counterexample for P_partial

The exact current legitimacy predicate accepts any configuration with exactly
one leader output.  It does not require that leader to be at label zero.
Algorithm 16 is allowed to migrate a nonzero-label responder leader to the
initiator.  The clean two-group witness below therefore keeps exactly one
leader but changes the pointwise output vector in one exact P_partial step.

Proof architecture, for default heartbeats: the exact pair transition is never
evaluated as a whole.  The responder's leader bit and label are transported
stage by stage through the compiled dispatcher with frame lemmas
stated for arbitrary endpoints; the only closed evaluations are the P'_ψ
probe wall and the deletion/normalization guards on the two literal inputs.
The bounded reification and the outer expiry are crossed by generic projection
equalities, so every junction on a closed term is syntactic.
-/

namespace PPLLCompleteMultiLeaderCleanup

open PPLL PPLLRepair PPLLResearchFormulation PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWriteIncrementGate PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepPreCheckResetRepair
  PPLLPpsiLeaderCreationRepair
  PPLLNoCheckBirthConditionTwoPhysical

open PhysicalBridge
open PhysicalBridge.Q5577HiddenControlAudit

set_option autoImplicit false

namespace Q5804

variable {psi : Nat}

private theorem q5804HPsi : (3 : Nat) > 0 := by
  omega

private def q5804Ring : DirectedRing 6 :=
  ⟨by omega⟩

/-- A completely neutral source state.  The only variable physical fields are
its stable label and leader bit. -/
private def q5804Raw
    (label : Fin 3) (leader : Bool) : AgentState 3 :=
  { leader := leader
    probe := false
    phase := false
    bit := false
    wait := true
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := label
    h_field := false
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := 0
    bullet := 0
    shield := false
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false }

private theorem q5804Raw_inProtocolDomain
    (label : Fin 3) (leader : Bool) :
    (q5804Raw label leader).inProtocolDomain 1 := by
  simp [q5804Raw, AgentState.inProtocolDomain]

private def q5804Audit
    (label : Fin 3) (leader : Bool) : AuthorizedAgentState 3 :=
  ⟨q5804Raw label leader, false⟩

private def q5804Finite
    (label : Fin 3) (leader : Bool) :
    ExpiringAgentState 3 1 1 :=
  ⟨⟨BoundedAgentState.ofDomain
        (q5804Raw label leader)
        (q5804Raw_inProtocolDomain label leader),
      false⟩,
    freshStall 1⟩

/-- The exact domain theorem proved by the numeric-domain closure. -/
private abbrev q5804Domain :
    PPartialAuthorizedDomainClosure q5804HPsi 1 :=
  PPartialAuthorizedDomainClosure_q5776 q5804HPsi 1

private abbrev q5804Protocol : PopulationProtocol :=
  P_partialProtocol q5804HPsi 1 1 q5804Domain

private def q5804Left : ExpiringAgentState 3 1 1 :=
  q5804Finite 1 false

private def q5804Right : ExpiringAgentState 3 1 1 :=
  q5804Finite 2 true

private theorem q5804Finite_core_erase
    (label : Fin 3) (leader : Bool) :
    (q5804Finite label leader).core.erase =
      q5804Audit label leader := by
  change
    (⟨(BoundedAgentState.ofDomain
          (q5804Raw label leader)
          (q5804Raw_inProtocolDomain label leader)).erase,
        false⟩ : AuthorizedAgentState 3) =
      q5804Audit label leader
  rw [BoundedAgentState.erase_ofDomain]
  rfl

private theorem q5804Left_core_erase :
    q5804Left.core.erase = q5804Audit 1 false :=
  q5804Finite_core_erase 1 false

private theorem q5804Right_core_erase :
    q5804Right.core.erase = q5804Audit 2 true :=
  q5804Finite_core_erase 2 true

/-! ## Generic five-field projections -/

private theorem q5804_peaceView_leader_snd_pair
    (q : AgentState psi × AgentState psi) (a b : AgentState psi)
    (h : peaceViewPair q = peaceViewPair (a, b)) :
    q.2.leader = b.leader := by
  have h' := congrArg
    (fun z : PeaceView psi × PeaceView psi => z.2.leader) h
  exact h'

private theorem q5804_peaceView_label_snd_pair
    (q : AgentState psi × AgentState psi) (a b : AgentState psi)
    (h : peaceViewPair q = peaceViewPair (a, b)) :
    q.2.label = b.label := by
  have h' := congrArg
    (fun z : PeaceView psi × PeaceView psi => z.2.label) h
  exact h'

private theorem q5804_authorized_leader_fst
    (q q' : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (h : authorizedPeaceViewPair q = authorizedPeaceViewPair q') :
    q.1.core.leader = q'.1.core.leader := by
  have h' := congrArg
    (fun z : PeaceView psi × PeaceView psi => z.1.leader) h
  exact h'

private theorem q5804_authorized_leader_snd
    (q q' : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (h : authorizedPeaceViewPair q = authorizedPeaceViewPair q') :
    q.2.core.leader = q'.2.core.leader := by
  have h' := congrArg
    (fun z : PeaceView psi × PeaceView psi => z.2.leader) h
  exact h'

private theorem q5804_authorized_label_snd
    (q q' : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (h : authorizedPeaceViewPair q = authorizedPeaceViewPair q') :
    q.2.core.label = q'.2.core.label := by
  have h' := congrArg
    (fun z : PeaceView psi × PeaceView psi => z.2.label) h
  exact h'

/-! ## Source-locked stage frames of the compiled suffix -/

private theorem q5804_resetHostSanitizer_peaceView (u : AgentState psi) :
    PeaceView.ofState (resetHostSanitizerQ5577 u) = PeaceView.ofState u := by
  apply PeaceView.ext
  all_goals
    unfold resetHostSanitizerQ5577 clearComparisonSignal PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem q5804_suppressSigStart_peaceViewPair (l r : AgentState psi) :
    peaceViewPair (suppressSigStart l r) = peaceViewPair (l, r) := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold suppressSigStart peaceViewPair PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem q5804_suppressSigMoveReset_peaceViewPair
    (l r : AgentState psi) :
    peaceViewPair (suppressSigMoveReset l r) = peaceViewPair (l, r) := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold suppressSigMoveReset peaceViewPair PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem q5804_suppressSigTerminal_peaceViewPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    peaceViewPair (suppressSigTerminal hpsi l r) = peaceViewPair (l, r) := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold suppressSigTerminal peaceViewPair PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem q5804_suppressSigEcho_peaceViewPair (l r : AgentState psi) :
    peaceViewPair (suppressSigEcho l r) = peaceViewPair (l, r) := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold suppressSigEcho peaceViewPair PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

private theorem q5804_suppressSigFinish_peaceViewPair (l r : AgentState psi) :
    peaceViewPair (suppressSigFinish l r) = peaceViewPair (l, r) := by
  apply Prod.ext <;> apply PeaceView.ext
  all_goals
    unfold suppressSigFinish peaceViewPair PeaceView.ofState
    try dsimp only []
    repeat (first | rfl | split)

/-- The hidden-control Algorithm-14 lane is a premise-free five-field
frame. -/
private theorem q5804_suppressQ5577_peaceViewPair
    (hpsi : psi > 0) (l r : AgentState psi) :
    peaceViewPair (suppressSigHiddenControlQ5577 hpsi l r) =
      peaceViewPair (l, r) := by
  let q0 := suppressSigStart l r
  let q0' := (resetHostSanitizerQ5577 q0.1, resetHostSanitizerQ5577 q0.2)
  let q1 := suppressSigMoveReset q0'.1 q0'.2
  let q1' := (resetHostSanitizerQ5577 q1.1, resetHostSanitizerQ5577 q1.2)
  let q2 := suppressSigTerminal hpsi q1'.1 q1'.2
  let q3 := suppressSigEcho q2.1 q2.2
  change peaceViewPair (suppressSigFinish q3.1 q3.2) = peaceViewPair (l, r)
  have h0 : peaceViewPair q0' = peaceViewPair q0 :=
    Prod.ext (q5804_resetHostSanitizer_peaceView q0.1)
      (q5804_resetHostSanitizer_peaceView q0.2)
  have h1 : peaceViewPair q1' = peaceViewPair q1 :=
    Prod.ext (q5804_resetHostSanitizer_peaceView q1.1)
      (q5804_resetHostSanitizer_peaceView q1.2)
  exact (q5804_suppressSigFinish_peaceViewPair q3.1 q3.2).trans
    ((q5804_suppressSigEcho_peaceViewPair q2.1 q2.2).trans
      ((q5804_suppressSigTerminal_peaceViewPair hpsi q1'.1 q1'.2).trans
        (h1.trans
          ((q5804_suppressSigMoveReset_peaceViewPair q0'.1 q0'.2).trans
            (h0.trans (q5804_suppressSigStart_peaceViewPair l r))))))

/-- Algorithm 15 never writes the responder's leader bit or label. -/
private theorem q5804_egressSink_responder_frame
    (hpsi : psi > 0) (l r : AgentState psi) :
    (eliminateLeadersNoCollisionEgressSink hpsi l r).2.leader = r.leader ∧
      (eliminateLeadersNoCollisionEgressSink hpsi l r).2.label = r.label := by
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

/-! ## Opaque stage wrappers for the compiled suffix

The suffix is factored into named stages so that every later statement is
about an unevaluated constant application, and the only definitional step is
one delta unfolding whose result is syntactically the next stage. -/

private def q5804Stage0
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  authorizedDisappearResponderPCarryOffQ5577 hpsi l r

private def q5804Stage1
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  authorizedCompareSigActionOne hpsi
    (q5804Stage0 hpsi l r).1 (q5804Stage0 hpsi l r).2

private def q5804Stage2
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  authorizedReconcile (suppressSigHiddenControlQ5577 hpsi)
    (q5804Stage1 hpsi l r).1 (q5804Stage1 hpsi l r).2

private def q5804Stage3
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  authorizedReconcile (eliminateLeadersNoCollisionEgressSink hpsi)
    (q5804Stage2 hpsi l r).1 (q5804Stage2 hpsi l r).2

/-- The exact compiled suffix is the gated WRITE stage applied to stage 3.
Both sides have head `authorizedReconcile` after one unfolding, so no stage
body is ever reduced. -/
private theorem q5804_suffix_eq_stage3
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    multiLeaderAfterCheckSuffixCombinedQ5577 hpsi l r =
      authorizedReconcile (writeSeqIncrementGate hpsi)
        (q5804Stage3 hpsi l r).1 (q5804Stage3 hpsi l r).2 :=
  rfl

private theorem q5804_stage0_eq
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    q5804Stage0 hpsi l r =
      ((authorizedDisappear hpsi l r).1,
        clearAuthorizedResponderPCarryQ5577
          (authorizedDisappear hpsi l r).2) :=
  rfl

/-! ## Generic projection lemmas (stated for a variable stage function) -/

private theorem q5804_reconcile_leader_fst
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    (authorizedReconcile f l r).1.core.leader = (f l.core r.core).1.leader :=
  rfl

private theorem q5804_reconcile_leader_snd
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    (authorizedReconcile f l r).2.core.leader = (f l.core r.core).2.leader :=
  rfl

private theorem q5804_reconcile_label_snd
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    (authorizedReconcile f l r).2.core.label = (f l.core r.core).2.label :=
  rfl

private theorem q5804_clear_leader (u : AuthorizedAgentState psi) :
    (clearAuthorizedResponderPCarryQ5577 u).core.leader = u.core.leader :=
  rfl

private theorem q5804_clear_label (u : AuthorizedAgentState psi) :
    (clearAuthorizedResponderPCarryQ5577 u).core.label = u.core.label :=
  rfl

private theorem q5804_leader_fst_congr
    (p q : AuthorizedAgentState psi × AuthorizedAgentState psi) (h : p = q) :
    p.1.core.leader = q.1.core.leader := by
  subst h
  rfl

private theorem q5804_leader_snd_congr
    (p q : AuthorizedAgentState psi × AuthorizedAgentState psi) (h : p = q) :
    p.2.core.leader = q.2.core.leader := by
  subst h
  rfl

private theorem q5804_label_snd_congr
    (p q : AuthorizedAgentState psi × AuthorizedAgentState psi) (h : p = q) :
    p.2.core.label = q.2.core.label := by
  subst h
  rfl

/-! ## Responder leader/label through each stage -/

private theorem q5804_disappear_leader_snd
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedDisappear hpsi l r).2.core.leader = r.core.leader :=
  (q5804_reconcile_leader_snd (disappear hpsi) l r).trans
    (PPLLVerify.disappear_leaders_eq hpsi l.core r.core).2

private theorem q5804_disappear_label_snd
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (authorizedDisappear hpsi l r).2.core.label = r.core.label :=
  (q5804_reconcile_label_snd (disappear hpsi) l r).trans
    (PPLLVerify.disappear_labels_eq hpsi l.core r.core).2

private theorem q5804_stage0_leader_snd
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (q5804Stage0 hpsi l r).2.core.leader = r.core.leader :=
  ((q5804_leader_snd_congr (q5804Stage0 hpsi l r)
      ((authorizedDisappear hpsi l r).1,
        clearAuthorizedResponderPCarryQ5577 (authorizedDisappear hpsi l r).2)
      (q5804_stage0_eq hpsi l r)).trans
    (q5804_clear_leader (authorizedDisappear hpsi l r).2)).trans
    (q5804_disappear_leader_snd hpsi l r)

private theorem q5804_stage0_label_snd
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (q5804Stage0 hpsi l r).2.core.label = r.core.label :=
  ((q5804_label_snd_congr (q5804Stage0 hpsi l r)
      ((authorizedDisappear hpsi l r).1,
        clearAuthorizedResponderPCarryQ5577 (authorizedDisappear hpsi l r).2)
      (q5804_stage0_eq hpsi l r)).trans
    (q5804_clear_label (authorizedDisappear hpsi l r).2)).trans
    (q5804_disappear_label_snd hpsi l r)

private theorem q5804_stage1_leader_snd
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (q5804Stage1 hpsi l r).2.core.leader =
      (q5804Stage0 hpsi l r).2.core.leader :=
  (compareActionOne_leaders hpsi
    (q5804Stage0 hpsi l r).1 (q5804Stage0 hpsi l r).2).2

private theorem q5804_stage1_label_snd
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (q5804Stage1 hpsi l r).2.core.label =
      (q5804Stage0 hpsi l r).2.core.label :=
  (compareActionOne_labels hpsi
    (q5804Stage0 hpsi l r).1 (q5804Stage0 hpsi l r).2).2

private theorem q5804_stage2_leader_snd
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (q5804Stage2 hpsi l r).2.core.leader =
      (q5804Stage1 hpsi l r).2.core.leader :=
  (q5804_reconcile_leader_snd (suppressSigHiddenControlQ5577 hpsi)
    (q5804Stage1 hpsi l r).1 (q5804Stage1 hpsi l r).2).trans
    (q5804_peaceView_leader_snd_pair
      (suppressSigHiddenControlQ5577 hpsi
        (q5804Stage1 hpsi l r).1.core (q5804Stage1 hpsi l r).2.core)
      (q5804Stage1 hpsi l r).1.core (q5804Stage1 hpsi l r).2.core
      (q5804_suppressQ5577_peaceViewPair hpsi
        (q5804Stage1 hpsi l r).1.core (q5804Stage1 hpsi l r).2.core))

private theorem q5804_stage2_label_snd
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (q5804Stage2 hpsi l r).2.core.label =
      (q5804Stage1 hpsi l r).2.core.label :=
  (q5804_reconcile_label_snd (suppressSigHiddenControlQ5577 hpsi)
    (q5804Stage1 hpsi l r).1 (q5804Stage1 hpsi l r).2).trans
    (q5804_peaceView_label_snd_pair
      (suppressSigHiddenControlQ5577 hpsi
        (q5804Stage1 hpsi l r).1.core (q5804Stage1 hpsi l r).2.core)
      (q5804Stage1 hpsi l r).1.core (q5804Stage1 hpsi l r).2.core
      (q5804_suppressQ5577_peaceViewPair hpsi
        (q5804Stage1 hpsi l r).1.core (q5804Stage1 hpsi l r).2.core))

private theorem q5804_stage3_leader_snd
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (q5804Stage3 hpsi l r).2.core.leader =
      (q5804Stage2 hpsi l r).2.core.leader :=
  (q5804_reconcile_leader_snd (eliminateLeadersNoCollisionEgressSink hpsi)
    (q5804Stage2 hpsi l r).1 (q5804Stage2 hpsi l r).2).trans
    (q5804_egressSink_responder_frame hpsi
      (q5804Stage2 hpsi l r).1.core (q5804Stage2 hpsi l r).2.core).1

private theorem q5804_stage3_label_snd
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (q5804Stage3 hpsi l r).2.core.label =
      (q5804Stage2 hpsi l r).2.core.label :=
  (q5804_reconcile_label_snd (eliminateLeadersNoCollisionEgressSink hpsi)
    (q5804Stage2 hpsi l r).1 (q5804Stage2 hpsi l r).2).trans
    (q5804_egressSink_responder_frame hpsi
      (q5804Stage2 hpsi l r).1.core (q5804Stage2 hpsi l r).2.core).2

/-- Both leader bits of the exact suffix are the leader bits of the gated
WRITE stage on stage 3, with no stage body reduced. -/
private theorem q5804_suffix_leader_fst
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi l r).1.core.leader =
      (writeSeqIncrementGate hpsi
        (q5804Stage3 hpsi l r).1.core (q5804Stage3 hpsi l r).2.core).1.leader :=
  (q5804_leader_fst_congr
      (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi l r)
      (authorizedReconcile (writeSeqIncrementGate hpsi)
        (q5804Stage3 hpsi l r).1 (q5804Stage3 hpsi l r).2)
      (q5804_suffix_eq_stage3 hpsi l r)).trans
    (q5804_reconcile_leader_fst (writeSeqIncrementGate hpsi)
      (q5804Stage3 hpsi l r).1 (q5804Stage3 hpsi l r).2)

private theorem q5804_suffix_leader_snd
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi) :
    (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi l r).2.core.leader =
      (writeSeqIncrementGate hpsi
        (q5804Stage3 hpsi l r).1.core (q5804Stage3 hpsi l r).2.core).2.leader :=
  (q5804_leader_snd_congr
      (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi l r)
      (authorizedReconcile (writeSeqIncrementGate hpsi)
        (q5804Stage3 hpsi l r).1 (q5804Stage3 hpsi l r).2)
      (q5804_suffix_eq_stage3 hpsi l r)).trans
    (q5804_reconcile_leader_snd (writeSeqIncrementGate hpsi)
      (q5804Stage3 hpsi l r).1 (q5804Stage3 hpsi l r).2)

/-- Through the complete compiled post-CHECK suffix, a responder
leader with nonzero label at the suffix input is migrated by the gated
Algorithm 16: DISAPPEAR, the responder `p_carry` clear, action-one COMPARE,
the hidden-control SUPPRESS lane, and Algorithm 15 all frame the responder's
leader bit and label. -/
private theorem q5804_suffix_migrates
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hr : r.core.leader = true) (hlabel : r.core.label ≠ ⟨0, hpsi⟩) :
    (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi l r).1.core.leader = true ∧
      (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi l r).2.core.leader =
        false := by
  have hlead : (q5804Stage3 hpsi l r).2.core.leader = true :=
    (q5804_stage3_leader_snd hpsi l r).trans
      ((q5804_stage2_leader_snd hpsi l r).trans
        ((q5804_stage1_leader_snd hpsi l r).trans
          ((q5804_stage0_leader_snd hpsi l r).trans hr)))
  have hlab : (q5804Stage3 hpsi l r).2.core.label ≠ ⟨0, hpsi⟩ := by
    intro h
    exact hlabel
      ((q5804_stage0_label_snd hpsi l r).symm.trans
        ((q5804_stage1_label_snd hpsi l r).symm.trans
          ((q5804_stage2_label_snd hpsi l r).symm.trans
            ((q5804_stage3_label_snd hpsi l r).symm.trans h))))
  exact ⟨(q5804_suffix_leader_fst hpsi l r).trans
      (writeSeqIncrementGate_initiator_true_of_nonzero_responder_leader hpsi
        (q5804Stage3 hpsi l r).1.core (q5804Stage3 hpsi l r).2.core
        ⟨hlead, hlab⟩),
    (q5804_suffix_leader_snd hpsi l r).trans
      (writeSeqIncrementGate_responder_false_of_nonzero_leader hpsi
        (q5804Stage3 hpsi l r).1.core (q5804Stage3 hpsi l r).2.core
        ⟨hlead, hlab⟩)⟩

/-- Birth marking frames both leader bits around the migrated suffix. -/
private theorem q5804_marked_suffix_migrates
    (hpsi : psi > 0) (born : Bool) (x y : AuthorizedAgentState psi)
    (hy : y.core.leader = true) (hlabel : y.core.label ≠ ⟨0, hpsi⟩) :
    (markLeaderBirth born
      (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi x y)).1.core.leader =
        true ∧
      (markLeaderBirth born
        (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi x y)).2.core.leader =
          false := by
  have hmark := markLeaderBirth_peaceViewPair born
    (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi x y)
  have hsuffix := q5804_suffix_migrates hpsi x y hy hlabel
  exact ⟨(q5804_authorized_leader_fst
      (markLeaderBirth born (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi x y))
      (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi x y) hmark).trans
        hsuffix.1,
    (q5804_authorized_leader_snd
      (markLeaderBirth born (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi x y))
      (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi x y) hmark).trans
        hsuffix.2⟩

/-- Exact open-priority branch of the compiled dispatcher on
normalized, deletion-free inputs. -/
private theorem q5804_combined_open
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : normalizeDeletion l = l) (hr : normalizeDeletion r = r)
    (hdl : deletionActive l = false) (hdr : deletionActive r = false) :
    multiLeaderCleanupAuthorizedTransitionCombinedQ5577 hpsi kappa l r =
      markLeaderBirth
        (leaderBirthBeforeOrAtCheck l r
          (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r)
          (wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r))
        (multiLeaderAfterCheckSuffixCombinedQ5577 hpsi
          (wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r).1
          (wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r).2) := by
  simp [multiLeaderCleanupAuthorizedTransitionCombinedQ5577,
    multiLeaderCleanupAuthorizedTransitionWithSuffixQ5577,
    hl, hr, hdl, hdr]

/-- The complete compiled dispatcher migrates a pre-CHECK responder leader
with nonzero label: CHECK keeps an existing responder leader and frames
labels, and the marked suffix performs the Algorithm-16 migration. -/
private theorem q5804_combined_migrates
    (hpsi : psi > 0) (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hl : normalizeDeletion l = l) (hr : normalizeDeletion r = r)
    (hdl : deletionActive l = false) (hdr : deletionActive r = false)
    (hlead :
      (wallSweepResetProbePreCheckResetBeforeCheck
        hpsi kappa l r).2.core.leader = true)
    (hlabel :
      (wallSweepResetProbePreCheckResetBeforeCheck
        hpsi kappa l r).2.core.label ≠ ⟨0, hpsi⟩) :
    (multiLeaderCleanupAuthorizedTransitionCombinedQ5577
      hpsi kappa l r).1.core.leader = true ∧
      (multiLeaderCleanupAuthorizedTransitionCombinedQ5577
        hpsi kappa l r).2.core.leader = false := by
  have hafterLead :
      (wallSweepResetProbePreCheckResetAfterCheck
        hpsi kappa l r).2.core.leader = true :=
    PPLLVerify.checkSig_responder_leader_of_true hpsi
      (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r).1.core
      (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r).2.core
      hlead
  have hafterLabel :
      (wallSweepResetProbePreCheckResetAfterCheck
        hpsi kappa l r).2.core.label ≠ ⟨0, hpsi⟩ := by
    intro h
    have hframe := (PPLLVerify.checkSig_labels_eq hpsi
      (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r).1.core
      (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r).2.core).2
    exact hlabel (hframe.symm.trans h)
  rw [q5804_combined_open hpsi kappa l r hl hr hdl hdr]
  exact q5804_marked_suffix_migrates hpsi
    (leaderBirthBeforeOrAtCheck l r
      (wallSweepResetProbePreCheckResetBeforeCheck hpsi kappa l r)
      (wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r))
    (wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r).1
    (wallSweepResetProbePreCheckResetAfterCheck hpsi kappa l r).2
    hafterLead hafterLabel

/-! ## Closed facts on the two literal inputs -/

/-- The exact current Algorithm-16 wrapper migrates this nonzero-label
responder leader on the literal raw inputs. -/
theorem q5804_writeSeq_migrates_nonzero_responder :
    (writeSeqIncrementGate q5804HPsi
      (q5804Raw 1 false) (q5804Raw 2 true)).1.leader = true ∧
      (writeSeqIncrementGate q5804HPsi
        (q5804Raw 1 false) (q5804Raw 2 true)).2.leader = false := by
  decide

private theorem q5804_normalize_left :
    normalizeDeletion (q5804Audit 1 false) = q5804Audit 1 false := by
  rfl

private theorem q5804_normalize_right :
    normalizeDeletion (q5804Audit 2 true) = q5804Audit 2 true := by
  rfl

private theorem q5804_deletion_left :
    deletionActive (q5804Audit 1 false) = false := by
  decide

private theorem q5804_deletion_right :
    deletionActive (q5804Audit 2 true) = false := by
  decide

/-- The P'_ψ leader/reset probe wall is five-field inert on the aligned
neutral pair (labels 1 and 2, no probes). -/
private theorem q5804_probe_peaceView :
    authorizedPeaceViewPair
        (authorizedPPsiLeaderResetProbeWall q5804HPsi
          (q5804Audit 1 false) (q5804Audit 2 true)) =
      authorizedPeaceViewPair (q5804Audit 1 false, q5804Audit 2 true) := by
  decide

/-- The complete reset-aware pre-CHECK prefix is five-field inert on the
pair, by the exported prefix-to-probe frame. -/
private theorem q5804_before_peaceView :
    authorizedPeaceViewPair
        (wallSweepResetProbePreCheckResetBeforeCheck q5804HPsi 1
          (q5804Audit 1 false) (q5804Audit 2 true)) =
      authorizedPeaceViewPair (q5804Audit 1 false, q5804Audit 2 true) :=
  (wallSweepResetProbePreCheckResetBeforeCheck_peaceViewPair_eq_probe
    q5804HPsi 1 (q5804Audit 1 false) (q5804Audit 2 true)).trans
    q5804_probe_peaceView

private theorem q5804_right_leader :
    (q5804Audit 1 false, q5804Audit 2 true).2.core.leader = true :=
  rfl

private theorem q5804_right_label_ne_zero :
    (q5804Audit 1 false, q5804Audit 2 true).2.core.label ≠
      ⟨0, q5804HPsi⟩ := by
  decide

private theorem q5804_before_responder_leader :
    (wallSweepResetProbePreCheckResetBeforeCheck q5804HPsi 1
      (q5804Audit 1 false) (q5804Audit 2 true)).2.core.leader = true :=
  (q5804_authorized_leader_snd
    (wallSweepResetProbePreCheckResetBeforeCheck q5804HPsi 1
      (q5804Audit 1 false) (q5804Audit 2 true))
    (q5804Audit 1 false, q5804Audit 2 true)
    q5804_before_peaceView).trans q5804_right_leader

private theorem q5804_before_responder_label_ne :
    (wallSweepResetProbePreCheckResetBeforeCheck q5804HPsi 1
      (q5804Audit 1 false) (q5804Audit 2 true)).2.core.label ≠
        ⟨0, q5804HPsi⟩ := by
  intro h
  have hlabel := q5804_authorized_label_snd
    (wallSweepResetProbePreCheckResetBeforeCheck q5804HPsi 1
      (q5804Audit 1 false) (q5804Audit 2 true))
    (q5804Audit 1 false, q5804Audit 2 true)
    q5804_before_peaceView
  exact absurd (hlabel.symm.trans h) q5804_right_label_ne_zero

/-- The complete compiled authorized dispatcher migrates the
leader from the responder to the initiator on the literal neutral inputs. -/
theorem q5804_authorized_migration :
    (P_partialAuthorized q5804HPsi 1
      (q5804Audit 1 false) (q5804Audit 2 true)).1.core.leader = true ∧
      (P_partialAuthorized q5804HPsi 1
        (q5804Audit 1 false) (q5804Audit 2 true)).2.core.leader = false := by
  unfold P_partialAuthorized
  exact q5804_combined_migrates q5804HPsi 1
    (q5804Audit 1 false) (q5804Audit 2 true)
    q5804_normalize_left q5804_normalize_right
    q5804_deletion_left q5804_deletion_right
    q5804_before_responder_leader q5804_before_responder_label_ne

/-! ## The bounded lift and every expiry branch preserve that result -/

/-- Path expiration frames the leader bit in all three path-expiry leaves:
progress, zero-budget clear, and positive-budget decrement. -/
private theorem q5804_pathExpireOne_leader_eq
    {kappa tau : Nat}
    (old out : ExpiringAgentState psi kappa tau) :
    (pathExpireOne tau old out).core.core.leader =
      out.core.core.leader := by
  unfold pathExpireOne
  split
  · rfl
  · split
    · simp [clearComparisonCarrier]
    · rfl

/-- The deletion-priority leaf also frames the leader bit, so the preceding
path-expiry theorem exhausts the inactive-deletion side. -/
private theorem q5804_deletionPriorityExpireOne_leader_eq
    {kappa tau : Nat}
    (old out : ExpiringAgentState psi kappa tau) :
    (deletionPriorityExpireOne tau old out).core.core.leader =
      out.core.core.leader := by
  unfold deletionPriorityExpireOne
  split
  · rfl
  · exact q5804_pathExpireOne_leader_eq old out

/-- Bounded reification copies the authorized leader bit verbatim. -/
private theorem q5804_expiringBase_leader_fst
    {kappa tau : Nat} (hpsi : psi > 0)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (l r : ExpiringAgentState psi kappa tau) :
    (P_partialExpiringBase hpsi kappa tau hDomain l r).1.core.core.leader =
      (P_partialAuthorized hpsi kappa
        l.core.erase r.core.erase).1.core.leader :=
  rfl

private theorem q5804_expiringBase_leader_snd
    {kappa tau : Nat} (hpsi : psi > 0)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (l r : ExpiringAgentState psi kappa tau) :
    (P_partialExpiringBase hpsi kappa tau hDomain l r).2.core.core.leader =
      (P_partialAuthorized hpsi kappa
        l.core.erase r.core.erase).2.core.leader :=
  rfl

/-- The finite `P_partial`, including the exact outer expiry, exposes the
authorized leader bits of both endpoints. -/
private theorem q5804_partial_leader_fst
    {kappa tau : Nat} (hpsi : psi > 0)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (l r : ExpiringAgentState psi kappa tau) :
    (P_partial hpsi kappa tau hDomain l r).1.core.core.leader =
      (P_partialAuthorized hpsi kappa
        l.core.erase r.core.erase).1.core.leader :=
  (q5804_deletionPriorityExpireOne_leader_eq l
    (P_partialExpiringBase hpsi kappa tau hDomain l r).1).trans
    (q5804_expiringBase_leader_fst hpsi hDomain l r)

private theorem q5804_partial_leader_snd
    {kappa tau : Nat} (hpsi : psi > 0)
    (hDomain : PPartialAuthorizedDomainClosure hpsi kappa)
    (l r : ExpiringAgentState psi kappa tau) :
    (P_partial hpsi kappa tau hDomain l r).2.core.core.leader =
      (P_partialAuthorized hpsi kappa
        l.core.erase r.core.erase).2.core.leader :=
  (q5804_deletionPriorityExpireOne_leader_eq r
    (P_partialExpiringBase hpsi kappa tau hDomain l r).2).trans
    (q5804_expiringBase_leader_snd hpsi hDomain l r)

/-- The complete finite `P_partial`, including the exact current outer expiry,
therefore migrates the leader. -/
theorem q5804_full_migration :
    (P_partial q5804HPsi 1 1 q5804Domain
      q5804Left q5804Right).1.core.core.leader = true ∧
      (P_partial q5804HPsi 1 1 q5804Domain
        q5804Left q5804Right).2.core.core.leader = false := by
  have h1 := q5804_partial_leader_fst q5804HPsi q5804Domain
    q5804Left q5804Right
  have h2 := q5804_partial_leader_snd q5804HPsi q5804Domain
    q5804Left q5804Right
  rw [q5804Left_core_erase, q5804Right_core_erase] at h1 h2
  exact ⟨h1.trans q5804_authorized_migration.1,
    h2.trans q5804_authorized_migration.2⟩

/-! ## Six-agent two-group configuration -/

private def q5804Config : Fin 6 → ExpiringAgentState 3 1 1
  | ⟨0, _⟩ => q5804Finite 0 false
  | ⟨1, _⟩ => q5804Left
  | ⟨2, _⟩ => q5804Right
  | ⟨3, _⟩ => q5804Finite 0 false
  | ⟨4, _⟩ => q5804Finite 1 false
  | ⟨5, _⟩ => q5804Finite 2 false

private def q5804After : Fin 6 → ExpiringAgentState 3 1 1 :=
  q5804Protocol.step q5804Ring q5804Config (1 : Fin 6)

private theorem q5804_fin6_cases (i : Fin 6) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  have h :
      i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨
        i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by
    omega
  rcases h with h | h | h | h | h | h
  · exact .inl (Fin.ext h)
  · exact .inr (.inl (Fin.ext h))
  · exact .inr (.inr (.inl (Fin.ext h)))
  · exact .inr (.inr (.inr (.inl (Fin.ext h))))
  · exact .inr (.inr (.inr (.inr (.inl (Fin.ext h)))))
  · exact .inr (.inr (.inr (.inr (.inr (Fin.ext h)))))

/-- The witness lies in a non-self ring and has two complete label groups. -/
theorem q5804_nondegenerate_regime :
    1 < 6 /\ 2 * 3 ≤ 6 := by
  omega

/-- Clockwise labels are exactly stable modulo three. -/
theorem q5804_stable_labels :
    ∀ i : Fin 6,
      (q5804Config (q5804Ring.rightNeighbor i)).core.core.label =
        ⟨((q5804Config i).core.core.label.val + 1) % 3,
          Nat.mod_lt _ q5804HPsi⟩ := by
  intro i
  rcases q5804_fin6_cases i with h | h | h | h | h | h
  all_goals subst i <;> decide

/-! ## Output projections -/

/-- Packaged output is the leader bit, stated for an arbitrary carrier state
so that its application to a step result is syntactic. -/
private theorem q5804_output_of_leader
    (s : ExpiringAgentState 3 1 1) (h : s.core.core.leader = true) :
    q5804Protocol.output s = .leader := by
  change (if s.core.core.leader then
    LeaderOutput.leader else LeaderOutput.follower) = .leader
  rw [h, if_pos rfl]

private theorem q5804_output_of_follower
    (s : ExpiringAgentState 3 1 1) (h : s.core.core.leader = false) :
    q5804Protocol.output s = .follower := by
  change (if s.core.core.leader then
    LeaderOutput.leader else LeaderOutput.follower) = .follower
  rw [h, if_neg Bool.false_ne_true]

/-- Initially position two is the unique leader output. -/
theorem q5804_initial_legit :
    PPartialLegit q5804HPsi 1 1 q5804Domain q5804Config := by
  change UniqueLeaderOutput
    q5804Protocol 6 q5804Config isLeaderOutput
  refine ⟨(2 : Fin 6), by decide, ?_⟩
  intro j hj
  rcases q5804_fin6_cases j with h | h | h | h | h | h
  · subst h
    exact absurd hj (by decide)
  · subst h
    exact absurd hj (by decide)
  · subst h
    rfl
  · subst h
    exact absurd hj (by decide)
  · subst h
    exact absurd hj (by decide)
  · subst h
    exact absurd hj (by decide)

/-! ## Exact packaged step projections -/

private theorem q5804After_zero :
    q5804After 0 = q5804Config 0 := by
  rfl

private theorem q5804After_one :
    q5804After 1 =
      (P_partial q5804HPsi 1 1 q5804Domain
        q5804Left q5804Right).1 := by
  rfl

private theorem q5804After_two :
    q5804After 2 =
      (P_partial q5804HPsi 1 1 q5804Domain
        q5804Left q5804Right).2 := by
  rfl

private theorem q5804After_three :
    q5804After 3 = q5804Config 3 := by
  rfl

private theorem q5804After_four :
    q5804After 4 = q5804Config 4 := by
  rfl

private theorem q5804After_five :
    q5804After 5 = q5804Config 5 := by
  rfl

private theorem q5804After_zero_leader :
    (q5804After 0).core.core.leader = false := by
  rw [q5804After_zero]
  rfl

private theorem q5804After_one_leader :
    (q5804After 1).core.core.leader = true := by
  rw [q5804After_one]
  exact q5804_full_migration.1

private theorem q5804After_two_leader :
    (q5804After 2).core.core.leader = false := by
  rw [q5804After_two]
  exact q5804_full_migration.2

private theorem q5804After_three_leader :
    (q5804After 3).core.core.leader = false := by
  rw [q5804After_three]
  rfl

private theorem q5804After_four_leader :
    (q5804After 4).core.core.leader = false := by
  rw [q5804After_four]
  rfl

private theorem q5804After_five_leader :
    (q5804After 5).core.core.leader = false := by
  rw [q5804After_five]
  rfl

private theorem q5804Config_one_output :
    q5804Protocol.output (q5804Config 1) = .follower :=
  q5804_output_of_follower (q5804Config 1) rfl

private theorem q5804After_zero_output :
    q5804Protocol.output (q5804After 0) = .follower :=
  q5804_output_of_follower (q5804After 0) q5804After_zero_leader

private theorem q5804After_one_output :
    q5804Protocol.output (q5804After 1) = .leader :=
  q5804_output_of_leader (q5804After 1) q5804After_one_leader

private theorem q5804After_two_output :
    q5804Protocol.output (q5804After 2) = .follower :=
  q5804_output_of_follower (q5804After 2) q5804After_two_leader

private theorem q5804After_three_output :
    q5804Protocol.output (q5804After 3) = .follower :=
  q5804_output_of_follower (q5804After 3) q5804After_three_leader

private theorem q5804After_four_output :
    q5804Protocol.output (q5804After 4) = .follower :=
  q5804_output_of_follower (q5804After 4) q5804After_four_leader

private theorem q5804After_five_output :
    q5804Protocol.output (q5804After 5) = .follower :=
  q5804_output_of_follower (q5804After 5) q5804After_five_leader

private theorem q5804_not_leader_of_follower_output
    (s : ExpiringAgentState 3 1 1)
    (hout : q5804Protocol.output s = .follower)
    (hj : isLeaderOutput (q5804Protocol.output s) = true) : False :=
  absurd ((congrArg isLeaderOutput hout).symm.trans hj) (by decide)

/-- The successor still has exactly one leader, now at position one.  This
isolates the failure to the pointwise-output conjunct rather than uniqueness. -/
theorem q5804_successor_still_legit :
    PPartialLegit q5804HPsi 1 1 q5804Domain q5804After := by
  change UniqueLeaderOutput
    q5804Protocol 6 q5804After isLeaderOutput
  refine ⟨(1 : Fin 6), ?_, ?_⟩
  · exact (congrArg isLeaderOutput q5804After_one_output).trans rfl
  · intro j hj
    rcases q5804_fin6_cases j with h | h | h | h | h | h
    · subst h
      exact (q5804_not_leader_of_follower_output _
        q5804After_zero_output hj).elim
    · subst h
      rfl
    · subst h
      exact (q5804_not_leader_of_follower_output _
        q5804After_two_output hj).elim
    · subst h
      exact (q5804_not_leader_of_follower_output _
        q5804After_three_output hj).elim
    · subst h
      exact (q5804_not_leader_of_follower_output _
        q5804After_four_output hj).elim
    · subst h
      exact (q5804_not_leader_of_follower_output _
        q5804After_five_output hj).elim

/-- The exact failed conjunct: position one changes from follower to leader. -/
theorem q5804_output_changed_at_one :
    q5804Protocol.output (q5804After 1) ≠
      q5804Protocol.output (q5804Config 1) := by
  rw [q5804After_one_output, q5804Config_one_output]
  intro h
  exact LeaderOutput.noConfusion h

/-- Therefore the pointwise output-preservation conjunct is false. -/
theorem q5804_failed_output_conjunct :
    ¬(∀ i : Fin 6,
      q5804Protocol.output (q5804After i) =
        q5804Protocol.output (q5804Config i)) := by
  intro h
  exact q5804_output_changed_at_one (h 1)

/-- Exact refutation of the local interface instantiated with the proven
domain closure. -/
theorem q5804_not_local_legitimacy :
    ¬PPartialLocalLegitimacy
      q5804HPsi 1 1 q5804Domain q5804Ring := by
  intro hLocal
  have hstep :
      PPartialLegit q5804HPsi 1 1 q5804Domain q5804After ∧
        (∀ i : Fin 6,
          q5804Protocol.output (q5804After i) =
            q5804Protocol.output (q5804Config i)) :=
    hLocal q5804Config q5804_initial_legit (1 : Fin 6)
  exact q5804_failed_output_conjunct hstep.2

/-- The exact unconditional premise introduced after the domain closure is false. -/
theorem PPartialLocalLegitimacyUnconditional_false_q5804 :
    ¬PPartialLocalLegitimacyUnconditional
      q5804HPsi 1 1 q5804Ring :=
  q5804_not_local_legitimacy

end Q5804

end PPLLCompleteMultiLeaderCleanup
