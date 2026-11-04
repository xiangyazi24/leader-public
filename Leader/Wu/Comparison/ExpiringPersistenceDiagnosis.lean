import Leader.Wu.Comparison.ExpiringRepair

/-!
# Diagnosing the transient n=4 recovery snapshot

The expiration repair reaches one leader after `[1,0,3,0]`, but the continuation
`[1,0,2,1,2]` creates a second.  This file factors that continuation into opaque
one-edge stages so that the first output-changing interaction and its internal
Algorithm-1 boundary can be inspected without repeatedly normalizing the full
nine-edge trace.
-/

namespace PPLLExpiringPersistenceDiagnosis


open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLAuthorizedComparisonRepair PPLLRepair

/-- First continuation edge, `1 → 2`, from the recovered snapshot. -/
def persistenceAfter1 : Fin 4 → ExpiringAgentState 2 0 0 :=
  localStep recoveryRing (expiringTransition (by omega) 0 0) recoveryAfter 1

/-- Second continuation edge, `0 → 1`. -/
def persistenceAfter2 : Fin 4 → ExpiringAgentState 2 0 0 :=
  localStep recoveryRing (expiringTransition (by omega) 0 0) persistenceAfter1 0

/-- Third continuation edge, `2 → 3`. -/
def persistenceAfter3 : Fin 4 → ExpiringAgentState 2 0 0 :=
  localStep recoveryRing (expiringTransition (by omega) 0 0) persistenceAfter2 2

/-- Fourth continuation edge, `1 → 2`. -/
def persistenceAfter4 : Fin 4 → ExpiringAgentState 2 0 0 :=
  localStep recoveryRing (expiringTransition (by omega) 0 0) persistenceAfter3 1

/-- Fifth continuation edge, `2 → 3`; this is definitionally the checked bad
future after factoring its schedule. -/
def persistenceAfter5 : Fin 4 → ExpiringAgentState 2 0 0 :=
  localStep recoveryRing (expiringTransition (by omega) 0 0) persistenceAfter4 2

/-! ## Projection back to literal P_PLL -/

/-- Erase the timer and authorization fields from the recovered snapshot. -/
def recoveredCoreConfig : Fin 4 → AgentState 2 :=
  fun i => (recoveryAfter i).core.core.erase

/-- Erase the same fields immediately before the output-changing edge. -/
def movedCoreConfig : Fin 4 → AgentState 2 :=
  fun i => (persistenceAfter4 i).core.core.erase

/-- Execute the four physical carrier-movement edges with Wu's literal audited
transition, starting from the recovered physical core. -/
def originalMovedCarrier : Fin 4 → AgentState 2 :=
  runLocalSchedule recoveryRing (ppll (by omega) 0)
    recoveredCoreConfig [1, 0, 2, 1]

private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hi := i.isLt
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Authorization and expiration are inactive along the four carrier-movement
edges: literal P_PLL reaches exactly the same CHECK-ready physical core. -/
theorem original_movement_reaches_movedCoreConfig :
    originalMovedCarrier = movedCoreConfig := by
  funext i
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 8192 in
private theorem movedCore_unique : hasUniqueLeader 4 movedCoreConfig := by
  refine ⟨0, by decide, ?_⟩
  intro j hj
  rcases fin4_cases j with rfl | rfl | rfl | rfl
  · rfl
  · have h : (movedCoreConfig 1).isLeader = false := by decide
    rw [h] at hj
    contradiction
  · have h : (movedCoreConfig 2).isLeader = false := by decide
    rw [h] at hj
    contradiction
  · have h : (movedCoreConfig 3).isLeader = false := by decide
    rw [h] at hj
    contradiction

set_option maxRecDepth 8192 in
private theorem movedCore_no_bad_bullet :
    noNonPeacefulBullet (by omega : 2 > 0) recoveryRing
      movedCoreConfig := by
  intro i hi
  rcases fin4_cases i with rfl | rfl | rfl | rfl
  · have h : (movedCoreConfig 0).bullet = 0 := by decide
    rw [h] at hi
    contradiction
  · have h : (movedCoreConfig 1).bullet = 0 := by decide
    rw [h] at hi
    contradiction
  · have h : (movedCoreConfig 2).bullet = 0 := by decide
    rw [h] at hi
    contradiction
  · have h : (movedCoreConfig 3).bullet = 0 := by decide
    rw [h] at hi
    contradiction

set_option maxRecDepth 8192 in
private theorem movedCore_no_free_overwriting :
    noFreeOverwritingSignal (by omega : 2 > 0) recoveryRing
      movedCoreConfig := by
  refine ⟨0, by decide, by decide, ?_⟩
  intro i hi hlt hfree
  have hieq : i = 1 := by omega
  subst i
  obtain ⟨_, haligned⟩ := hfree.1
  obtain ⟨p, hpath, _⟩ := haligned 0 (by omega)
  have hnone : ∀ k : Fin 4, (movedCoreConfig k).path3 = none := by
    intro k
    rcases fin4_cases k with rfl | rfl | rfl | rfl <;> decide
  rw [hnone] at hpath
  contradiction

set_option maxRecDepth 8192 in
private theorem movedCore_stable_id :
    isStableIDSequence (by omega : 2 > 0) recoveryRing
      movedCoreConfig := by
  refine ⟨0, by decide, by decide, ?_, ?_⟩
  · intro k hk
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;> decide
  · intro i hi hlt
    have hieq : i = 1 := by omega
    subst i
    change groupID recoveryRing.hn movedCoreConfig 2 = trailingZeros 1
    have h2 : (movedCoreConfig 2).bit = false := by decide
    have h3 : (movedCoreConfig 3).bit = false := by decide
    unfold groupID trailingZeros
    simp [List.range_succ, h2, h3]

private theorem movedCore_no_free_barrier :
    noFreeBarrier (by omega : 2 > 0) recoveryRing movedCoreConfig :=
  noFreeBarrier_of_stableID (by omega) recoveryRing movedCoreConfig
    movedCore_stable_id

/-- The CHECK-ready moved-carrier configuration satisfies all five conditions
of Wu's Definition 2, including the stable-ID condition. In particular, that
condition does not constrain the leader group's own bits or invalidate its
residual comparison signal. -/
theorem movedCoreConfig_paper_safe :
    PaperSafeConfig (by omega : 2 > 0) recoveryRing movedCoreConfig where
  unique_leader := movedCore_unique
  no_nonpeaceful_bullet := movedCore_no_bad_bullet
  no_free_barrier := movedCore_no_free_barrier
  no_free_overwriting_signal := movedCore_no_free_overwriting
  stable_id_sequence := movedCore_stable_id

/-- Literal P_PLL's output-changing edge from the moved carrier. -/
def originalBadAfter : Fin 4 → AgentState 2 :=
  localStep recoveryRing (ppll (by omega) 0) movedCoreConfig 2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Literal P_PLL keeps the old leader at position zero and creates a second
leader at position two in one interaction. -/
theorem original_moved_carrier_creates_second_leader :
    (originalBadAfter 0).leader = true ∧
      (originalBadAfter 2).leader = true := by
  decide

/-- Two distinct leader outputs rule out the first field of Definition 2. -/
theorem originalBadAfter_not_unique :
    ¬hasUniqueLeader 4 originalBadAfter := by
  intro h
  obtain ⟨i, _, hunique⟩ := h
  have h0 : (0 : Fin 4) = i :=
    hunique 0 original_moved_carrier_creates_second_leader.1
  have h2 : (2 : Fin 4) = i :=
    hunique 2 original_moved_carrier_creates_second_leader.2
  have : (0 : Fin 4) = 2 := h0.trans h2.symm
  omega

/-- Direct refutation of Lemma 4.1.1 on literal P_PLL: the moved-carrier
Definition-2 configuration leaves the five-condition set in one edge. -/
theorem paperSafe_not_closed_by_moved_carrier :
    ¬PopulationProtocol.ClosedPred (PPLL.protocol (by omega) 0) recoveryRing
      (PaperSafeConfig (by omega : 2 > 0) recoveryRing) := by
  intro hclosed
  have hnext := hclosed movedCoreConfig movedCoreConfig_paper_safe
    originalBadAfter ⟨2, rfl⟩
  exact originalBadAfter_not_unique hnext.unique_leader

/-- Event that the old leader at zero and the moved-carrier leader at two
coexist. -/
def movedCarrierTwoLeaderTest (C : Fin 4 → AgentState 2) : Bool :=
  (C 0).leader && (C 2).leader

set_option maxRecDepth 8192 in
/-- Exactly one of the four one-edge schedules creates the second leader. -/
theorem moved_carrier_bad_schedule_count :
    hitCount recoveryRing (ppll (by omega : 2 > 0) 0)
      movedCarrierTwoLeaderTest movedCoreConfig 1 = 1 := by
  decide

/-- The literal moved-carrier bad event has exact one-step probability `1/4`. -/
theorem moved_carrier_bad_event_probability :
    hitProbability recoveryRing (ppll (by omega : 2 > 0) 0)
      movedCarrierTwoLeaderTest movedCoreConfig 1 = (1 : Rat) / 4 := by
  unfold hitProbability
  rw [moved_carrier_bad_schedule_count, allSchedules_length]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Rat.natCast_ofNat]

set_option maxRecDepth 8192 in
/-- The moved-carrier Definition-2 configuration is not Definition-1 safe for
literal P_PLL. This strengthens T1 by exhibiting a carrier that the literal
transition itself can move through the preceding four-edge route. -/
theorem movedCoreConfig_not_semantically_safe :
    ¬PopulationProtocol.IsSafe (PPLL.protocol (by omega) 0) recoveryRing
      movedCoreConfig isLeaderOutput := by
  intro hsafe
  have hreach : PopulationProtocol.Reachable
      (PPLL.protocol (by omega) 0) recoveryRing
      movedCoreConfig originalBadAfter :=
    PopulationProtocol.OneStep.to_reachable ⟨2, rfl⟩
  have hout := hsafe.2 originalBadAfter hreach 2
  change AgentState.outputFn (originalBadAfter 2) =
    AgentState.outputFn (movedCoreConfig 2) at hout
  have hne : AgentState.outputFn (originalBadAfter 2) ≠
      AgentState.outputFn (movedCoreConfig 2) := by decide
  exact hne hout

/-! ## Internal stages of the output-changing interaction -/

/-- Audit-level initiator presented to the final edge. -/
def finalInputL : AuthorizedAgentState 2 := (persistenceAfter4 2).core.erase

/-- Audit-level responder presented to the final edge. -/
def finalInputR : AuthorizedAgentState 2 := (persistenceAfter4 3).core.erase

/-- Final interaction through SIGMOVE, immediately before CHECK. -/
def finalBeforeCheck : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedBeforeCheck (by omega) 0 finalInputL finalInputR

/-- Final interaction immediately after CHECK. -/
def finalAfterCheck : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedCheckSig (by omega) finalBeforeCheck.1 finalBeforeCheck.2

/-- Final interaction immediately after DISAPPEAR. -/
def finalAfterDisappear : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedDisappear (by omega) finalAfterCheck.1 finalAfterCheck.2

/-- Final interaction immediately after repaired COMPARE. -/
def finalAfterCompare : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedCompareSig (by omega) finalAfterDisappear.1 finalAfterDisappear.2

/-- Final interaction immediately after SUPPRESS_SIG. -/
def finalAfterSuppress : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedReconcile (suppressSig (by omega))
    finalAfterCompare.1 finalAfterCompare.2

/-- Final interaction immediately after the no-collision leader-elimination
stage. -/
def finalAfterEliminate : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedReconcile (eliminateLeadersNoCollision (by omega))
    finalAfterSuppress.1 finalAfterSuppress.2

/-- Final audit-level pair after WRITE_SEQ. -/
def finalAfterWrite : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedReconcile (writeSeq (by omega))
    finalAfterEliminate.1 finalAfterEliminate.2

/-! ## Exact mechanism certificate -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Immediately before the output-changing edge, position zero is still the
only leader. Thus the second output is not created in an earlier continuation
prefix and merely exposed at the end. -/
theorem persistenceAfter4_has_only_leader_zero :
    (persistenceAfter4 0).core.core.leader = true ∧
      (persistenceAfter4 1).core.core.leader = false ∧
      (persistenceAfter4 2).core.core.leader = false ∧
      (persistenceAfter4 3).core.core.leader = false := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The continuation physically moves the two components of the carrier from
positions zero/one to positions two/three. The payload-zero component starts
without permission and acquires it only on the terminal-to-zero host crossing
in the fourth continuation edge. -/
theorem continuation_moves_carrier_across_group :
    (recoveryAfter 0).core.core.path = .some 0 0 ∧
      (recoveryAfter 1).core.core.path = .some 1 0 ∧
      (recoveryAfter 0).core.path0Crossed = false ∧
      (persistenceAfter1 1).core.core.path = .bot ∧
      (persistenceAfter1 2).core.core.path = .some 1 0 ∧
      (persistenceAfter2 0).core.core.path = .bot ∧
      (persistenceAfter2 1).core.core.path = .some 0 0 ∧
      (persistenceAfter3 2).core.core.path = .bot ∧
      (persistenceAfter3 3).core.core.path = .some 1 0 ∧
      (persistenceAfter4 1).core.core.path = .bot ∧
      (persistenceAfter4 2).core.core.path = .some 0 0 ∧
      (persistenceAfter4 2).core.path0Crossed = true := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The final edge starts with an execution-authorized, aligned, complete
`CHECK_ready` carrier. The persistence failure is therefore not caused by a
forged permission bit or by the old source-self rearm. -/
theorem final_input_is_authorized_check_ready :
    finalInputL.core.leader = false ∧ finalInputR.core.leader = false ∧
      finalInputL.core.label = 0 ∧ finalInputR.core.label = 1 ∧
      finalInputL.core.path = .some 0 0 ∧
      finalInputR.core.path = .some 1 0 ∧
      finalInputL.core.state = .CHECK_ready ∧
      finalInputR.core.state = .CHECK_ready ∧
      finalInputL.path0Crossed = true := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Both groups still carry ID `00`. Wu's printed stable sequence constrains
only positive-index groups, leaving the leader group `s₀` arbitrary; therefore
this equality is compatible with `movedCoreConfig_paper_safe`. -/
theorem recovered_snapshot_has_equal_zero_group_ids :
    (recoveryAfter 0).core.core.bit = false ∧
      (recoveryAfter 1).core.core.bit = false ∧
      (recoveryAfter 2).core.core.bit = false ∧
      (recoveryAfter 3).core.core.bit = false := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- CHECK is the first internal stage that changes an output: equal payload and
group bits create a leader at the terminal responder. -/
theorem final_check_creates_responder_leader :
    finalBeforeCheck.1.core.leader = false ∧
      finalBeforeCheck.2.core.leader = false ∧
      finalAfterCheck.1.core.leader = false ∧
      finalAfterCheck.2.core.leader = true ∧
      finalAfterCheck.1.core.state = .equal ∧
      finalAfterCheck.2.core.state = .equal := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The middle suffix stages preserve the new responder leader; WRITE_SEQ then
moves that leader output to the label-zero initiator exactly as Algorithm 16
prescribes. -/
theorem final_write_migrates_created_leader :
    finalAfterEliminate.1.core.leader = false ∧
      finalAfterEliminate.2.core.leader = true ∧
      finalAfterWrite.1.core.leader = true ∧
      finalAfterWrite.2.core.leader = false := by
  decide

end PPLLExpiringPersistenceDiagnosis
