import Leader.Wu.PartialProtocol.LocalLegitimacyCounterexample

/-!
# An unbounded local-legitimacy counterfamily for the current `P_partial`

The accepted six-agent witness is local: on its critical pair the exact
current finite transition migrates a nonzero-label responder leader to the
initiator.  This file embeds that same pair at the non-wrapping edge `1 -> 2`
of every directed ring with at least six sites.  Every other site is a
follower, so padding neither creates another leader nor participates in the
chosen step.

The transition itself is not recomputed here.  The only protocol-specific
input is `Q5804.q5804_full_migration`; the rest is a generic finite-ring frame
argument.  Thus the result covers every population size `n >= 6`, not merely
a finite prefix or a doubled-cover subsequence.
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

set_option autoImplicit false

namespace PPartialErratumLocalLegitimacyCounterfamilySol

abbrev FamilyPsi : Nat := 3
abbrev FamilyKappa : Nat := 1
abbrev FamilyTau : Nat := 1

private theorem familyHPsi : FamilyPsi > 0 := by
  decide

/-- The numeric-domain closure theorem used by the accepted six-agent witness. -/
private abbrev familyDomain :
    PPartialAuthorizedDomainClosure familyHPsi FamilyKappa :=
  PPartialAuthorizedDomainClosure_q5776 familyHPsi FamilyKappa

/-- The exact current `P_partial`, packaged with its leader output. -/
private abbrev familyProtocol : PopulationProtocol :=
  P_partialProtocol familyHPsi FamilyKappa FamilyTau familyDomain

/-- The neutral raw state used in the six-agent witness.  Only its stable label and leader bit
vary. -/
private def familyRaw
    (label : Fin FamilyPsi) (leader : Bool) : AgentState FamilyPsi :=
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

private theorem familyRaw_inProtocolDomain
    (label : Fin FamilyPsi) (leader : Bool) :
    (familyRaw label leader).inProtocolDomain FamilyKappa := by
  simp [familyRaw, AgentState.inProtocolDomain, FamilyKappa]

private def familyFinite
    (label : Fin FamilyPsi) (leader : Bool) :
    ExpiringAgentState FamilyPsi FamilyKappa FamilyTau :=
  ⟨⟨BoundedAgentState.ofDomain
        (familyRaw label leader)
        (familyRaw_inProtocolDomain label leader),
      false⟩,
    freshStall FamilyTau⟩

/-- The critical initiator, critical responder, and padding state. -/
private def familyLeft :
    ExpiringAgentState FamilyPsi FamilyKappa FamilyTau :=
  familyFinite 1 false

private def familyRight :
    ExpiringAgentState FamilyPsi FamilyKappa FamilyTau :=
  familyFinite 2 true

private def familyFollower
    {n : Nat} (i : Fin n) :
    ExpiringAgentState FamilyPsi FamilyKappa FamilyTau :=
  familyFinite
    ⟨i.val % FamilyPsi, Nat.mod_lt _ familyHPsi⟩ false

/-- Fixed non-wrapping initiator at site one. -/
def familyInitiator {n : Nat} (hn : 6 ≤ n) : Fin n :=
  ⟨1, by omega⟩

/-- Its responder at site two. -/
def familyResponder {n : Nat} (hn : 6 ≤ n) : Fin n :=
  ⟨2, by omega⟩

private theorem familyInitiator_ne_responder
    {n : Nat} (hn : 6 ≤ n) :
    familyInitiator hn ≠ familyResponder hn := by
  intro h
  have hv := congrArg Fin.val h
  simp [familyInitiator, familyResponder] at hv

private theorem familyResponder_ne_initiator
    {n : Nat} (hn : 6 ≤ n) :
    familyResponder hn ≠ familyInitiator hn :=
  (familyInitiator_ne_responder hn).symm

/-- On every ring of size at least six, edge one has responder two. -/
theorem family_rightNeighbor_initiator
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    ring.rightNeighbor (familyInitiator hn) = familyResponder hn := by
  apply Fin.ext
  change 2 % n = 2
  rw [Nat.mod_eq_of_lt (by omega)]

/-- The accepted pair, padded uniformly by follower states. -/
def familyConfig
    {n : Nat} (hn : 6 ≤ n) :
    Fin n → ExpiringAgentState FamilyPsi FamilyKappa FamilyTau :=
  fun i =>
    if i = familyResponder hn then familyRight
    else familyFollower i

@[simp]
private theorem familyConfig_responder
    {n : Nat} (hn : 6 ≤ n) :
    familyConfig hn (familyResponder hn) = familyRight := by
  simp [familyConfig]

@[simp]
private theorem familyConfig_initiator
    {n : Nat} (hn : 6 ≤ n) :
    familyConfig hn (familyInitiator hn) = familyLeft := by
  rw [familyConfig, if_neg (familyInitiator_ne_responder hn)]
  rfl

private theorem familyConfig_follower
    {n : Nat} (hn : 6 ≤ n) (i : Fin n)
    (hr : i ≠ familyResponder hn) :
    familyConfig hn i = familyFollower i := by
  simp [familyConfig, hr]

/-- The whole padded word retains the accepted periodic label pattern.  This
also makes the member at `n = 6` exactly the six-state witness configuration. -/
private theorem familyConfig_label_val
    {n : Nat} (hn : 6 ≤ n) (i : Fin n) :
    (familyConfig hn i).core.core.label.val = i.val % FamilyPsi := by
  by_cases hr : i = familyResponder hn
  · subst i
    rw [familyConfig_responder]
    rfl
  · rw [familyConfig_follower hn i hr]
    rfl

/-- Whenever three divides the population size, the padded counterexample has
stable clockwise labels around the entire cycle, not just at the active pair. -/
theorem family_stable_labels_of_dvd
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n)
    (hdiv : FamilyPsi ∣ n) :
    ∀ i : Fin n,
      (familyConfig hn (ring.rightNeighbor i)).core.core.label =
        ⟨((familyConfig hn i).core.core.label.val + 1) % FamilyPsi,
          Nat.mod_lt _ familyHPsi⟩ := by
  intro i
  apply Fin.ext
  rw [familyConfig_label_val, familyConfig_label_val]
  change (((i.val + 1) % n) % FamilyPsi) =
    (i.val % FamilyPsi + 1) % FamilyPsi
  calc
    ((i.val + 1) % n) % FamilyPsi = (i.val + 1) % FamilyPsi :=
      Nat.mod_mod_of_dvd _ hdiv
    _ = (i.val % FamilyPsi + 1) % FamilyPsi := by
      simp [Nat.add_mod]

/-! ## Reuse of the accepted exact pair migration -/

/-- The critical pair is definitionally the pair from the six-agent witness, so its accepted
symbolic migration theorem applies without evaluating `P_partial` again. -/
theorem family_pair_migrates :
    (P_partial familyHPsi FamilyKappa FamilyTau familyDomain
      familyLeft familyRight).1.core.core.leader = true ∧
      (P_partial familyHPsi FamilyKappa FamilyTau familyDomain
        familyLeft familyRight).2.core.core.leader = false := by
  exact Q5804.q5804_full_migration

/-! ## Exact local step and frame -/

/-- The exact local update at the named edge `1 -> 2`. -/
def familyAfter
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    Fin n → ExpiringAgentState FamilyPsi FamilyKappa FamilyTau :=
  localStep ring
    (P_partial familyHPsi FamilyKappa FamilyTau familyDomain)
    (familyConfig hn) (familyInitiator hn)

/-- The explicit update is definitionally the packaged protocol step. -/
theorem familyAfter_eq_protocol_step
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    familyAfter hn ring =
      familyProtocol.step ring (familyConfig hn) (familyInitiator hn) := by
  rfl

private theorem familyAfter_initiator
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    familyAfter hn ring (familyInitiator hn) =
      (P_partial familyHPsi FamilyKappa FamilyTau familyDomain
        familyLeft familyRight).1 := by
  simp [familyAfter, localStep, family_rightNeighbor_initiator,
    familyConfig_initiator, familyConfig_responder]

private theorem familyAfter_responder
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    familyAfter hn ring (familyResponder hn) =
      (P_partial familyHPsi FamilyKappa FamilyTau familyDomain
        familyLeft familyRight).2 := by
  simp [familyAfter, localStep, family_rightNeighbor_initiator,
    familyResponder_ne_initiator hn, familyConfig_initiator,
    familyConfig_responder]

/-- Every padded site is literally untouched by the chosen local step. -/
theorem familyAfter_eq_config_of_off_edge
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) (i : Fin n)
    (hl : i ≠ familyInitiator hn)
    (hr : i ≠ familyResponder hn) :
    familyAfter hn ring i = familyConfig hn i := by
  simp [familyAfter, localStep, family_rightNeighbor_initiator, hl, hr]

private theorem familyLeft_leader :
    familyLeft.core.core.leader = false := by
  rfl

private theorem familyRight_leader :
    familyRight.core.core.leader = true := by
  rfl

private theorem familyFollower_leader
    {n : Nat} (i : Fin n) :
    (familyFollower i).core.core.leader = false := by
  rfl

private theorem family_output_of_leader
    (s : ExpiringAgentState FamilyPsi FamilyKappa FamilyTau)
    (h : s.core.core.leader = true) :
    familyProtocol.output s = .leader := by
  change (if s.core.core.leader then
    LeaderOutput.leader else LeaderOutput.follower) = .leader
  rw [h, if_pos rfl]

private theorem family_output_of_follower
    (s : ExpiringAgentState FamilyPsi FamilyKappa FamilyTau)
    (h : s.core.core.leader = false) :
    familyProtocol.output s = .follower := by
  change (if s.core.core.leader then
    LeaderOutput.leader else LeaderOutput.follower) = .follower
  rw [h, if_neg Bool.false_ne_true]

private theorem familyConfig_responder_output
    {n : Nat} (hn : 6 ≤ n) :
    familyProtocol.output (familyConfig hn (familyResponder hn)) =
      .leader := by
  rw [familyConfig_responder]
  exact family_output_of_leader familyRight familyRight_leader

private theorem familyConfig_output_follower_of_ne_responder
    {n : Nat} (hn : 6 ≤ n) (i : Fin n)
    (hr : i ≠ familyResponder hn) :
    familyProtocol.output (familyConfig hn i) = .follower := by
  rw [familyConfig_follower hn i hr]
  exact family_output_of_follower
    (familyFollower i) (familyFollower_leader i)

private theorem familyAfter_initiator_leader
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    (familyAfter hn ring (familyInitiator hn)).core.core.leader = true := by
  rw [familyAfter_initiator]
  exact family_pair_migrates.1

private theorem familyAfter_responder_leader
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    (familyAfter hn ring (familyResponder hn)).core.core.leader = false := by
  rw [familyAfter_responder]
  exact family_pair_migrates.2

private theorem familyAfter_initiator_output
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    familyProtocol.output (familyAfter hn ring (familyInitiator hn)) =
      .leader :=
  family_output_of_leader _ (familyAfter_initiator_leader hn ring)

private theorem familyAfter_responder_output
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    familyProtocol.output (familyAfter hn ring (familyResponder hn)) =
      .follower :=
  family_output_of_follower _ (familyAfter_responder_leader hn ring)

private theorem familyAfter_output_follower_of_ne_initiator
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) (i : Fin n)
    (hl : i ≠ familyInitiator hn) :
    familyProtocol.output (familyAfter hn ring i) = .follower := by
  by_cases hr : i = familyResponder hn
  · subst i
    exact familyAfter_responder_output hn ring
  · rw [familyAfter_eq_config_of_off_edge hn ring i hl hr]
    exact familyConfig_output_follower_of_ne_responder hn i hr

/-! ## Legitimacy before and after, and the changed output -/

/-- For every `n >= 6`, the padded initial configuration has its unique
leader at site two. -/
theorem family_initial_legit
    {n : Nat} (hn : 6 ≤ n) :
    PPartialLegit familyHPsi FamilyKappa FamilyTau familyDomain
      (familyConfig hn) := by
  change UniqueLeaderOutput familyProtocol n (familyConfig hn) isLeaderOutput
  refine ⟨familyResponder hn, ?_, ?_⟩
  · exact (congrArg isLeaderOutput
      (familyConfig_responder_output hn)).trans rfl
  · intro i hi
    by_cases hr : i = familyResponder hn
    · exact hr
    · rw [familyConfig_output_follower_of_ne_responder hn i hr] at hi
      simp [isLeaderOutput] at hi

/-- The exact successor again has one leader, now at site one. -/
theorem family_successor_still_legit
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    PPartialLegit familyHPsi FamilyKappa FamilyTau familyDomain
      (familyAfter hn ring) := by
  change UniqueLeaderOutput familyProtocol n (familyAfter hn ring)
    isLeaderOutput
  refine ⟨familyInitiator hn, ?_, ?_⟩
  · exact (congrArg isLeaderOutput
      (familyAfter_initiator_output hn ring)).trans rfl
  · intro i hi
    by_cases hl : i = familyInitiator hn
    · exact hl
    · rw [familyAfter_output_follower_of_ne_initiator hn ring i hl] at hi
      simp [isLeaderOutput] at hi

/-- Site one changes output from follower to leader in the named exact step. -/
theorem family_output_changed_at_initiator
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    familyProtocol.output (familyAfter hn ring (familyInitiator hn)) ≠
      familyProtocol.output (familyConfig hn (familyInitiator hn)) := by
  rw [familyAfter_initiator_output, familyConfig_initiator]
  rw [family_output_of_follower familyLeft familyLeft_leader]
  intro h
  exact LeaderOutput.noConfusion h

/-- Hence pointwise output preservation fails for every member of the
counterfamily. -/
theorem family_failed_output_conjunct
    {n : Nat} (hn : 6 ≤ n) (ring : DirectedRing n) :
    ¬(∀ i : Fin n,
      familyProtocol.output (familyAfter hn ring i) =
        familyProtocol.output (familyConfig hn i)) := by
  intro h
  exact family_output_changed_at_initiator hn ring
    (h (familyInitiator hn))

/-- Strong unbounded form: on every directed ring of every size `n >= 6`,
the exact current unconditional local-legitimacy obligation is false. -/
theorem PPartialLocalLegitimacyUnconditional_false_of_six_le
    (n : Nat) (hn : 6 ≤ n) (ring : DirectedRing n) :
    ¬PPartialLocalLegitimacyUnconditional
      familyHPsi FamilyKappa FamilyTau ring := by
  intro hLocal
  have hstep := hLocal
    (familyConfig hn) (family_initial_legit hn) (familyInitiator hn)
  have houtputs :
      ∀ i : Fin n,
        familyProtocol.output (familyAfter hn ring i) =
          familyProtocol.output (familyConfig hn i) := by
    simpa [familyAfter_eq_protocol_step hn ring] using hstep.2
  exact family_failed_output_conjunct hn ring houtputs

/-- Explicit arbitrarily-large corollary. -/
theorem arbitrarily_large_local_legitimacy_counterexample
    (bound : Nat) :
    ∃ n : Nat, bound ≤ n ∧ 6 ≤ n ∧
      ∀ ring : DirectedRing n,
        ¬PPartialLocalLegitimacyUnconditional
          familyHPsi FamilyKappa FamilyTau ring := by
  refine ⟨bound + 6, by omega, by omega, ?_⟩
  intro ring
  exact PPartialLocalLegitimacyUnconditional_false_of_six_le
    (bound + 6) (by omega) ring

#print axioms family_pair_migrates
#print axioms family_initial_legit
#print axioms family_successor_still_legit
#print axioms PPartialLocalLegitimacyUnconditional_false_of_six_le
#print axioms arbitrarily_large_local_legitimacy_counterexample

end PPartialErratumLocalLegitimacyCounterfamilySol

end PPLLCompleteMultiLeaderCleanup
