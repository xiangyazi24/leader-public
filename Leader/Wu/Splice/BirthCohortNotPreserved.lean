import Leader.Wu.Birth.PPrimeProbeRearm


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace Q11536B9CohortRefutation


open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLComparisonHistory
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
  BirthShortDoneTerminalCheckInputSources
  BirthReleaseTerminalInvariant
open BirthPhaseCohortDesign
open Q11531PPrimeRebirth


private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide


/-! ## 1. Exact initial-site comparison history -/


private def idleHistory : LocalComparisonHistory 4 where
  state := .absent
  path := .absent
  path2 := .absent
  pCarry := .absent


open PPLLLeaderCreationCleanupRepair
open BirthShortDoneTerminalEntryCut

private theorem fin4_cases (i : Fin 4) :
    i = siteA ∨ i = siteB ∨ i = siteC ∨ i = siteRoot := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  simpa [siteA, siteB, siteC, siteRoot] using hi

theorem raw_initial_of_ne_root
    (i : Fin 4) (h : i != siteRoot) :
    rawAt initialConfig i =
      BirthShortDoneTerminalPositiveWitness.raw false := by
  have hne : i ≠ siteRoot := by
    intro hi
    subst i
    simp at h
  unfold rawAt initialConfig
  rw [if_neg hne]
  exact BirthShortDoneTerminalPositiveWitness.endpoint_erase false


theorem raw_initial_root :
    rawAt initialConfig siteRoot = leaderRaw := by
  simp [rawAt, initialConfig, leaderEndpoint, leaderRaw,
    BoundedAgentState.erase_ofDomain]


private theorem idleHistory_trusted_follower :
    FullLocalHistoryTrusted
      (BirthShortDoneTerminalPositiveWitness.raw false) idleHistory := by
  simp [FullLocalHistoryTrusted, AuditLocalHistoryTrusted,
    PCarryHistoryTrusted, MarkMatches, idleHistory,
    BirthShortDoneTerminalPositiveWitness.raw]


private theorem idleHistory_trusted_leader :
    FullLocalHistoryTrusted leaderRaw idleHistory := by
  simp [FullLocalHistoryTrusted, AuditLocalHistoryTrusted,
    PCarryHistoryTrusted, MarkMatches, idleHistory, leaderRaw,
    BirthShortDoneTerminalPositiveWitness.raw]


/-- `leader_exists` holds at the hand-built root. -/
theorem initial_leader_exists :
    exists i, (initialConfig i).core.core.leader = true := by
  exact ⟨siteRoot, initial_one_remote_leader.2.2.2⟩


theorem initial_comparison_classified :
    exists H : Fin 4 -> LocalComparisonHistory 4,
      forall i, CohortClassifiedAt hTwo (initialConfig i) (H i) := by
  refine ⟨fun _ => idleHistory, ?_⟩
  intro i
  unfold CohortClassifiedAt
  left
  change FullLocalHistoryTrusted (rawAt initialConfig i) idleHistory
  rcases fin4_cases i with rfl | rfl | rfl | rfl
  · rw [raw_initial_of_ne_root siteA (by decide)]
    exact idleHistory_trusted_follower
  · rw [raw_initial_of_ne_root siteB (by decide)]
    exact idleHistory_trusted_follower
  · rw [raw_initial_of_ne_root siteC (by decide)]
    exact idleHistory_trusted_follower
  · rw [raw_initial_root]
    exact idleHistory_trusted_leader


private def initialPreparedPair (e : Fin 4) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let l := initialConfig e
  let r := initialConfig (ring4.rightNeighbor e)
  let pl := prepareExpiringDisposal hTwo l
  let pr := prepareExpiringDisposal hTwo r
  (normalizeDeletion pl.core.erase, normalizeDeletion pr.core.erase)


private theorem initialPreparedPair_probe_a :
    (initialPreparedPair siteA).2.core.probe = false := by
  decide

private theorem initialPreparedPair_probe_b :
    (initialPreparedPair siteB).2.core.probe = false := by
  decide

private theorem initialPreparedPair_probe_c :
    (initialPreparedPair siteC).2.core.probe = false := by
  decide

private theorem initialPreparedPair_probe_root :
    (initialPreparedPair siteRoot).2.core.probe = false := by
  decide

private theorem initialPreparedPair_responder_probe_false (e : Fin 4) :
    (initialPreparedPair e).2.core.probe = false := by
  rcases fin4_cases e with rfl | rfl | rfl | rfl
  · exact initialPreparedPair_probe_a
  · exact initialPreparedPair_probe_b
  · exact initialPreparedPair_probe_c
  · exact initialPreparedPair_probe_root


private theorem pprimeBlocked_of_probe_false
    (e : Fin 4)
    (hz : (initialPreparedPair e).2.core.probe = false) :
    PPrimeBlockedAt hTwo ring4 initialConfig e := by
  unfold PPrimeBlockedAt
  dsimp only
  intro hguard
  have hp : (initialPreparedPair e).2.core.probe = true := by
    simpa only [initialPreparedPair] using hguard.2.2.2.1
  rw [hz] at hp
  cases hp

theorem initial_pprime_blocked :
    forall e, PPrimeBlockedAt hTwo ring4 initialConfig e := by
  intro e
  rcases fin4_cases e with rfl | rfl | rfl | rfl
  · exact pprimeBlocked_of_probe_false siteA initialPreparedPair_probe_a
  · exact pprimeBlocked_of_probe_false siteB initialPreparedPair_probe_b
  · exact pprimeBlocked_of_probe_false siteC initialPreparedPair_probe_c
  · exact pprimeBlocked_of_probe_false siteRoot initialPreparedPair_probe_root


private def initialBeforeCheck (e : Fin 4) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  doneBeforeCheckEntryWidth hTwo hTwo hTwoLe 1
    (initialPreparedPair e).1 (initialPreparedPair e).2


private def initialPprime (e : Fin 4) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall
    hTwo (initialPreparedPair e).1 (initialPreparedPair e).2

private def initialGen (e : Fin 4) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  BirthShortDoneTerminalEntryCut.authorizedGenCleanEntryWidth
    hTwo hTwo hTwoLe 1 (initialPprime e).1 (initialPprime e).2

private def initialClean (e : Fin 4) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedCleanSig hTwo (initialGen e).1 (initialGen e).2

private def initialEliminate (e : Fin 4) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedEliminateSig hTwo (initialClean e).1 (initialClean e).2

private def initialMoved (e : Fin 4) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  BirthGenerationDone.authorizedDoneMove
    hTwo (initialEliminate e).1 (initialEliminate e).2

private def initialResetWall (e : Fin 4) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  PPLLWallSweepPreCheckResetRepair.preCheckResetWall
    (initialMoved e).1 (initialMoved e).2

private def initialSanitized (e : Fin 4) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair
    hTwo (initialResetWall e)

private theorem initialBeforeCheck_eq_staged (e : Fin 4) :
    initialBeforeCheck e = initialSanitized e := by
  unfold initialBeforeCheck initialSanitized initialResetWall initialMoved
    initialEliminate initialClean initialGen initialPprime
    BirthShortDoneTerminalEntryCut.doneBeforeCheckEntryWidth
    BirthShortDoneTerminalEntryCut.generationBeforeMoveEntryWidth
  rfl

private theorem initialSanitized_a_state :
    (initialSanitized siteA).2.core.state = .none := by
  decide

private theorem initialSanitized_a_path :
    (initialSanitized siteA).2.core.path = .bot := by
  decide

private theorem initialSanitized_b_state :
    (initialSanitized siteB).2.core.state = .none := by
  decide

private theorem initialSanitized_b_path :
    (initialSanitized siteB).2.core.path = .bot := by
  decide

private theorem initialSanitized_c_state :
    (initialSanitized siteC).2.core.state = .none := by
  decide

private theorem initialSanitized_c_path :
    (initialSanitized siteC).2.core.path = .bot := by
  decide

private theorem initialSanitized_root_state :
    (initialSanitized siteRoot).2.core.state = .none := by
  decide

private theorem initialSanitized_root_path :
    (initialSanitized siteRoot).2.core.path = .bot := by
  decide

private theorem initialBeforeCheck_responder_quiet (e : Fin 4) :
    (initialBeforeCheck e).2.core.state = .none /\
      (initialBeforeCheck e).2.core.path = .bot := by
  rw [initialBeforeCheck_eq_staged]
  rcases fin4_cases e with rfl | rfl | rfl | rfl
  · exact ⟨initialSanitized_a_state, initialSanitized_a_path⟩
  · exact ⟨initialSanitized_b_state, initialSanitized_b_path⟩
  · exact ⟨initialSanitized_c_state, initialSanitized_c_path⟩
  · exact ⟨initialSanitized_root_state, initialSanitized_root_path⟩


private theorem no_actualCheckBirthInput_of_responder_none_bot
    {psi : Nat} (hpsi : 0 < psi)
    (b : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hs : b.2.core.state = .none) (hp : b.2.core.path = .bot) :
    ¬ ActualCheckBirthInput hpsi b := by
  intro h
  have hf := h.2.2.2.2.2.2
  rcases hf.2.2 with heq | hex
  · have hne : (MainState.none : MainState) ≠ .equal := by decide
    exact hne (hs.symm.trans heq)
  · rcases hex with ⟨pathLabel, pathBit, hpath, _⟩
    rw [hp] at hpath
    cases hpath


private theorem checkBlocked_of_responder_quiet
    (e : Fin 4)
    (hs : (initialBeforeCheck e).2.core.state = .none)
    (hp : (initialBeforeCheck e).2.core.path = .bot) :
    CheckBlockedAt hTwo hTwoLe ring4 initialConfig e := by
  have hnot : ¬ ActualCheckBirthInput hTwo (initialBeforeCheck e) :=
    no_actualCheckBirthInput_of_responder_none_bot
      hTwo (initialBeforeCheck e) hs hp
  simpa only [CheckBlockedAt, initialBeforeCheck, initialPreparedPair] using hnot

theorem initial_check_blocked :
    forall e, CheckBlockedAt hTwo hTwoLe ring4 initialConfig e := by
  intro e
  rcases fin4_cases e with rfl | rfl | rfl | rfl
  · have hq := initialBeforeCheck_responder_quiet siteA
    exact checkBlocked_of_responder_quiet siteA hq.1 hq.2
  · have hq := initialBeforeCheck_responder_quiet siteB
    exact checkBlocked_of_responder_quiet siteB hq.1 hq.2
  · have hq := initialBeforeCheck_responder_quiet siteC
    exact checkBlocked_of_responder_quiet siteC hq.1 hq.2
  · have hq := initialBeforeCheck_responder_quiet siteRoot
    exact checkBlocked_of_responder_quiet siteRoot hq.1 hq.2


private theorem noTerminalFive_of_path2_none
    {psi : Nat} (u : AgentState psi) (h : u.path2 = none) :
    NoTerminalFive u := by
  intro p hp ha
  rw [h] at hp
  cases hp


private theorem initial_raw_path2_none (i : Fin 4) :
    (rawAt initialConfig i).path2 = none := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl
  · rw [raw_initial_of_ne_root siteA (by decide)]
    rfl
  · rw [raw_initial_of_ne_root siteB (by decide)]
    rfl
  · rw [raw_initial_of_ne_root siteC (by decide)]
    rfl
  · rw [raw_initial_root]
    rfl


theorem initial_no_terminal_five :
    forall i, NoTerminalFive (initialConfig i).core.erase.core := by
  intro i
  change NoTerminalFive (rawAt initialConfig i)
  exact noTerminalFive_of_path2_none _ (initial_raw_path2_none i)


private theorem ring4_right_b : ring4.rightNeighbor siteB = siteC := by
  decide


private theorem ring4_right_a : ring4.rightNeighbor siteA = siteB := by
  decide


private theorem initialConfig_b :
    initialConfig siteB =
      BirthShortDoneTerminalPositiveWitness.endpoint false := by
  simp [initialConfig, siteB, siteRoot]


private theorem initialConfig_c :
    initialConfig siteC =
      BirthShortDoneTerminalPositiveWitness.endpoint false := by
  simp [initialConfig, siteC, siteRoot]


private def followerPrepared : AuthorizedAgentState 2 :=
  (prepareExpiringDisposal hTwo
    (BirthShortDoneTerminalPositiveWitness.endpoint false)).core.erase

private theorem followerPrepared_state_none :
    followerPrepared.core.state = .none := by
  decide

private theorem followerPrepared_path_bot :
    followerPrepared.core.path = .bot := by
  decide

private theorem followerPrepared_path2_none :
    followerPrepared.core.path2 = none := by
  decide

private theorem followerPrepared_pcarry_false :
    followerPrepared.core.p_carry = false := by
  decide

private theorem followerPrepared_not_live :
    ¬ ComparisonLive
      (prepareExpiringDisposal hTwo
        (BirthShortDoneTerminalPositiveWitness.endpoint false)).core.erase.core := by
  intro hlive
  change ComparisonLive followerPrepared.core at hlive
  unfold ComparisonLive at hlive
  rcases hlive with hstate | hpath | hpath2 | hp
  · exact hstate followerPrepared_state_none
  · exact hpath followerPrepared_path_bot
  · exact hpath2 followerPrepared_path2_none
  · have hbad : false = true :=
      followerPrepared_pcarry_false.symm.trans hp
    cases hbad


theorem initial_endpoint_safe_b_c :
    EndpointSafeForCohort hTwo hTwoLe 1 ring4 initialConfig siteB := by
  unfold EndpointSafeForCohort
  rw [ring4_right_b, initialConfig_b, initialConfig_c]
  dsimp only
  constructor
  · intro hlive
    exact (followerPrepared_not_live hlive).elim
  · intro hlive
    exact (followerPrepared_not_live hlive).elim


theorem initial_birthCohort :
    BirthCohort hTwo hTwoLe ring4 initialConfig where
  leader_exists := initial_leader_exists
  comparison_classified := initial_comparison_classified
  pprime_blocked := initial_pprime_blocked
  check_blocked := initial_check_blocked
  no_terminal_five := initial_no_terminal_five


/-- The second-edge guard is exactly the negation of the stored
`PPrimeBlockedAt` clause on `siteA -> siteB` after the re-arm row. -/
theorem afterRearm_pprime_unblocked_at_a :
    ¬ PPrimeBlockedAt hTwo ring4 afterRearm siteA := by
  intro hblocked
  unfold PPrimeBlockedAt at hblocked
  dsimp only at hblocked
  rw [ring4_right_a] at hblocked
  apply hblocked
  exact second_edge_pprime_guard


/-- Hence the actual one-row successor is not a `BirthCohort`, independently
of what happens to its other four fields. -/
theorem afterRearm_not_birthCohort :
    ¬ BirthCohort hTwo hTwoLe ring4 afterRearm := by
  intro hcohort
  exact afterRearm_pprime_unblocked_at_a
    (hcohort.pprime_blocked siteA)


theorem b9_cohort_preservation_refuted :
    BirthCohort hTwo hTwoLe ring4 initialConfig /\
      EndpointSafeForCohort hTwo hTwoLe 1 ring4 initialConfig siteB /\
      ¬ BirthCohort hTwo hTwoLe ring4
        (BirthShortDoneTerminalConsumer.step
          hTwo hTwo hTwoLe ring4 initialConfig siteB) := by
  refine ⟨initial_birthCohort, initial_endpoint_safe_b_c, ?_⟩
  simpa only [afterRearm] using afterRearm_not_birthCohort


/-- Remove only the live-probe conjunct from `PPrimeBarrierBirthGuard`.
This excludes a reset-free follower/follower barrier before it can seed the
probe that arms the next P-prime birth. -/
def NoResetFreeFollowerBarrierAt
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n) : Prop :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let l0 := normalizeDeletion pl.core.erase
  let r0 := normalizeDeletion pr.core.erase
  ¬ (l0.core.leader = false /\
      r0.core.leader = false /\
      l0.core.reset_cmd = false /\
      isBarrier hpsi l0.core r0.core)


theorem noResetFreeFollowerBarrierAt_implies_pprimeBlocked
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) (e : Fin n)
    (h : NoResetFreeFollowerBarrierAt hpsi ring C e) :
    PPrimeBlockedAt hpsi ring C e := by
  let l := C e
  let r := C (ring.rightNeighbor e)
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let l0 := normalizeDeletion pl.core.erase
  let r0 := normalizeDeletion pr.core.erase
  change ¬ (l0.core.leader = false /\
      r0.core.leader = false /\
      l0.core.reset_cmd = false /\
      isBarrier hpsi l0.core r0.core) at h
  change ¬ PPrimeBarrierBirthGuard hpsi l0 r0
  intro hguard
  apply h
  exact ⟨hguard.1, hguard.2.1, hguard.2.2.1,
    hguard.2.2.2.2⟩


private theorem initialPreparedPair_b_rearm_shape :
    (initialPreparedPair siteB).1.core.leader = false /\
      (initialPreparedPair siteB).2.core.leader = false /\
      (initialPreparedPair siteB).1.core.reset_cmd = false /\
      isBarrier hTwo
        (initialPreparedPair siteB).1.core
        (initialPreparedPair siteB).2.core := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · unfold isBarrier
    decide

theorem initial_rearm_edge_violates_noResetFreeFollowerBarrierAt :
    ¬ NoResetFreeFollowerBarrierAt hTwo ring4 initialConfig siteB := by
  intro h
  unfold NoResetFreeFollowerBarrierAt at h
  rw [ring4_right_b, initialConfig_b, initialConfig_c] at h
  apply h
  simpa only [initialPreparedPair, ring4_right_b, initialConfig_b,
    initialConfig_c] using initialPreparedPair_b_rearm_shape


theorem no_preserved_pprime_strengthening_containing_initial
    (Inv : BirthPhaseCohortDesign.FC 4 2 1 1 -> Prop)
    (hinit : Inv initialConfig)
    (hpres : forall C e,
      Inv C ->
      EndpointSafeForCohort hTwo hTwoLe 1 ring4 C e ->
      Inv (BirthShortDoneTerminalConsumer.step
        hTwo hTwo hTwoLe ring4 C e))
    (hblocks : forall C, Inv C -> forall e,
      PPrimeBlockedAt hTwo ring4 C e) : False := by
  have hnext : Inv afterRearm := by
    have h := hpres initialConfig siteB hinit initial_endpoint_safe_b_c
    simpa only [afterRearm] using h
  exact afterRearm_pprime_unblocked_at_a
    (hblocks afterRearm hnext siteA)


theorem no_theorem_side_pprime_strengthening_containing_initial :
    ¬ exists Inv : BirthPhaseCohortDesign.FC 4 2 1 1 -> Prop,
      Inv initialConfig /\
      (forall C e,
        Inv C ->
        EndpointSafeForCohort hTwo hTwoLe 1 ring4 C e ->
        Inv (BirthShortDoneTerminalConsumer.step
          hTwo hTwo hTwoLe ring4 C e)) /\
      (forall C, Inv C -> forall e,
        PPrimeBlockedAt hTwo ring4 C e) := by
  rintro ⟨Inv, hinit, hpres, hblocks⟩
  exact no_preserved_pprime_strengthening_containing_initial
    Inv hinit hpres hblocks


#print axioms Q11536B9CohortRefutation.initial_leader_exists
#print axioms Q11536B9CohortRefutation.initial_comparison_classified
#print axioms Q11536B9CohortRefutation.initial_pprime_blocked
#print axioms Q11536B9CohortRefutation.initial_check_blocked
#print axioms Q11536B9CohortRefutation.initial_no_terminal_five
#print axioms Q11536B9CohortRefutation.initial_endpoint_safe_b_c
#print axioms Q11536B9CohortRefutation.initial_birthCohort
#print axioms Q11536B9CohortRefutation.afterRearm_pprime_unblocked_at_a
#print axioms Q11536B9CohortRefutation.afterRearm_not_birthCohort
#print axioms Q11536B9CohortRefutation.b9_cohort_preservation_refuted
#print axioms Q11536B9CohortRefutation.noResetFreeFollowerBarrierAt_implies_pprimeBlocked
#print axioms Q11536B9CohortRefutation.initial_rearm_edge_violates_noResetFreeFollowerBarrierAt
#print axioms Q11536B9CohortRefutation.no_preserved_pprime_strengthening_containing_initial
#print axioms Q11536B9CohortRefutation.no_theorem_side_pprime_strengthening_containing_initial


end Q11536B9CohortRefutation
