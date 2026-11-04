import Leader.Wu.Birth.PPrimeRearmThenBirthRingSix
import Leader.Wu.Birth.PPrimeResetFreeBarrierBlock
import Leader.Wu.WallSweep.EchoDrain
import Leader.Wu.Comparison.ExpiringK2ProjectionInvariants

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace Q11575PostBirthSanitation

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
open BirthPhaseCohortDesign
open PPLLWriteSeqRelocation

private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide

abbrev E := ExpiringAgentState 2 1 1

def ring3 : DirectedRing 3 := Q11541PPrimeReachability.ring3

def q11541Start : Fin 3 -> E := Q11541PPrimeReachability.strongStart

private theorem fin3_cases (i : Fin 3) :
    i = 0 ∨ i = 1 ∨ i = 2 := by
  omega

/-- Prepared/normalized pair used by the P-prime blocker. -/
def preparedPair {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  (normalizeDeletion pl.core.erase, normalizeDeletion pr.core.erase)

/-! ## 1. Staged certificate for the actual n=3 counterexample -/

/-- Exact prepared pair for the scheduled leader edge `0 -> 1`. -/
def q11541Prepared : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  preparedPair hTwo ring3 q11541Start 0

/-- Exact P-prime/reset-wall output on the scheduled pair. -/
def q11541Pprime : AgentState 2 × AgentState 2 :=
  pPsiLeaderResetProbeWall hTwo
    q11541Prepared.1.core q11541Prepared.2.core

/-- Exact current prefix through CHECK. -/
def q11541ThroughCheck :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
    hTwo hTwo hTwoLe 1 q11541Prepared.1 q11541Prepared.2

/-- Exact post-DISAPPEAR cut. -/
def q11541AfterDisappear :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedDisappear hTwo q11541ThroughCheck.1 q11541ThroughCheck.2

/-- Exact post-COMPARE / pre-SUPPRESS cut. -/
def q11541BeforeSuppress :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hTwo
    q11541AfterDisappear.1 q11541AfterDisappear.2

/-- Published SUPPRESS prefix: START, reset-kill, MOVE-RESET, reset-kill. -/
def q11541SuppressPrefix : AgentState 2 × AgentState 2 :=
  BirthShortWait.suppressPrefix
    q11541BeforeSuppress.1.core q11541BeforeSuppress.2.core

/-- Width-two short-count insertion. -/
def q11541SuppressShort : AgentState 2 × AgentState 2 :=
  BirthShortWait.shortCountReset hTwo hTwoLe
    q11541SuppressPrefix.1 q11541SuppressPrefix.2

/-- Published terminal substage. -/
def q11541SuppressTerminal : AgentState 2 × AgentState 2 :=
  suppressSigTerminal hTwo
    q11541SuppressShort.1 q11541SuppressShort.2

/-- Published echo collision substage. -/
def q11541SuppressEcho : AgentState 2 × AgentState 2 :=
  suppressSigEcho q11541SuppressTerminal.1 q11541SuppressTerminal.2

/-- Published SUPPRESS finish substage. -/
def q11541SuppressFinish : AgentState 2 × AgentState 2 :=
  suppressSigFinish q11541SuppressEcho.1 q11541SuppressEcho.2

/-- Per-field certificate of the exact mechanism.
P-prime first changes the responder label to 1; the current prefix keeps the
old responder echo; SUPPRESS moves a reset onto that responder; then ECHO sees
`echo=true` and `reset_cmd=true` simultaneously and clears both. -/
theorem q11541_suppress_echo_collision :
    q11541Pprime.2.label = (1 : Fin 2) ∧
      q11541Pprime.2.echo = true ∧
      q11541BeforeSuppress.1.core.leader = true ∧
      q11541BeforeSuppress.1.core.reset_cmd = false ∧
      q11541BeforeSuppress.2.core.reset_cmd = false ∧
      q11541BeforeSuppress.2.core.echo = true ∧
      q11541SuppressPrefix.2.reset_cmd = true ∧
      q11541SuppressPrefix.2.echo = true ∧
      q11541SuppressTerminal.2.reset_cmd = true ∧
      q11541SuppressTerminal.2.echo = true ∧
      q11541SuppressEcho.2.reset_cmd = false ∧
      q11541SuppressEcho.2.echo = false ∧
      q11541SuppressFinish.2.reset_cmd = false ∧
      q11541SuppressFinish.2.echo = false := by
  decide

private theorem q11541_finish_is_actual_raw_suppress :
    q11541SuppressFinish =
      BirthShortWait.suppressSigResetKillWidth
        hTwo hTwo hTwoLe
        q11541BeforeSuppress.1.core q11541BeforeSuppress.2.core := by
  rfl

private def q11541AuthorizedSuppress :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  BirthShortDoneCuts.authorizedSuppressWidth
    hTwo hTwo hTwoLe q11541BeforeSuppress.1 q11541BeforeSuppress.2

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem q11541_authorized_suppress_collision :
    q11541AuthorizedSuppress.2.core.reset_cmd = false ∧
      q11541AuthorizedSuppress.2.core.echo = false := by
  decide

/-- Own spelling of the actual full current step, so the final edge check does
not depend on private proof constants. -/
def q11541After : Fin 3 -> E :=
  BirthShortDoneTerminalConsumer.step hTwo hTwo hTwoLe
    ring3 q11541Start 0

private theorem q11541Start_all_blockers :
    ∀ e, Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt
      hTwo ring3 q11541Start e := by
  intro e
  rcases fin3_cases e with rfl | rfl | rfl
  · unfold Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt
    dsimp only
    unfold isBarrier
    decide
  · unfold Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt
    dsimp only
    unfold isBarrier
    decide
  · unfold Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt
    dsimp only
    unfold isBarrier
    decide

private def q11541BadEdge : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  preparedPair hTwo ring3 q11541After 1

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem q11541_bad_left_follower :
    q11541BadEdge.1.core.leader = false := by decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem q11541_bad_right_follower :
    q11541BadEdge.2.core.leader = false := by decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem q11541_bad_left_reset_free :
    q11541BadEdge.1.core.reset_cmd = false := by decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem q11541_bad_barrier :
    isBarrier hTwo q11541BadEdge.1.core q11541BadEdge.2.core := by
  unfold isBarrier
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem q11541After_not_blocked :
    ¬ Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt
      hTwo ring3 q11541After 1 := by
  intro h
  unfold Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt at h
  dsimp only at h
  apply h
  change q11541BadEdge.1.core.leader = false ∧
    q11541BadEdge.2.core.leader = false ∧
    q11541BadEdge.1.core.reset_cmd = false ∧
    isBarrier hTwo q11541BadEdge.1.core q11541BadEdge.2.core
  exact ⟨q11541_bad_left_follower, q11541_bad_right_follower,
    q11541_bad_left_reset_free, q11541_bad_barrier⟩

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
/-- Actual-current-consumer certification of the three-site counterexample,
with the strengthened blocker. -/
theorem q11541_n3_actual_counterexample :
    (∀ e, Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt
      hTwo ring3 q11541Start e) ∧
      (q11541After 0).core.core.leader = true ∧
      ¬ Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt
        hTwo ring3 q11541After 1 := by
  exact ⟨q11541Start_all_blockers, by decide, q11541After_not_blocked⟩

/-! ## 2. Smallest direct augmented candidate from the existing machinery -/

/-- The exact raw WallSweep state, carried only as theorem-side ghost data.
The `initial` configuration is required echo-free; `ResetSweepState` itself
records the live reset front, neutral processed prefix, and untouched ahead
region. No protocol field is added. -/
def ResetSweepWitnessed {n psi kappa tau : Nat}
    (ring : DirectedRing n) (C : FC n psi kappa tau) : Prop :=
  ∃ start : Fin n, ∃ initial : Fin n -> AgentState psi, ∃ steps : Nat,
    (∀ i, (initial i).echo = false) ∧
    PPLLWallSweepSchedule.ResetSweepState
      ring start initial (fun i => rawAt C i) steps

/-- Current leader labels are already in the normalization chosen by the
terminal host. -/
def LeadersLabelZero {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (C : FC n psi kappa tau) : Prop :=
  ∀ i, (C i).core.core.leader = true ->
    (C i).core.core.label = (⟨0, hpsi⟩ : Fin psi)

/-- Direct no-protocol-change candidate: static P-prime blocker + exact
WallSweep front witness + leader-label normal form + the existing K2
leader-persistence/peacefulness package. -/
def SanitationCandidate {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) : Prop :=
  (∀ e, Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt
      hpsi ring C e) ∧
    ResetSweepWitnessed ring C ∧
    LeadersLabelZero hpsi C ∧
    ExpiringK2Projection.PeacefulGlobal ring C

/-- Part 2(i): the candidate blocks every P-prime birth for exactly the
latch-design reason; the extra front/K2 clauses are not needed for this implication. -/
theorem sanitationCandidate_pprimeBlocked
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau)
    (h : SanitationCandidate hpsi ring C) :
    ∀ e, PPrimeBlockedAt hpsi ring C e := by
  intro e
  exact Q11540PPrimeLatchDesign.noResetFreeFollowerBarrierAt_implies_pprimeBlocked
    hpsi ring C e (h.1 e)

/-! ## 3. Next counterexample: a genuine reset front is not arbitrary-row closed -/

/-- Echo-free follower carrying the reset token. -/
def reset0Raw : AgentState 2 :=
  { BirthShortDoneTerminalPositiveWitness.raw false with reset_cmd := true }

private theorem reset0_domain : reset0Raw.inProtocolDomain 1 := by
  simp [reset0Raw, BirthShortDoneTerminalPositiveWitness.raw,
    AgentState.inProtocolDomain]

def reset0 : E :=
  ⟨⟨BoundedAgentState.ofDomain reset0Raw reset0_domain, false⟩, 0⟩

/-- One normalized leader, then the reset front, then an echo-free follower. -/
def frontStart : Fin 3 -> E := fun i =>
  if i = 0 then Q11531PPrimeRebirth.leaderEndpoint
  else if i = 1 then reset0
  else BirthShortDoneTerminalPositiveWitness.endpoint false

private def frontPrepared : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  preparedPair hTwo ring3 frontStart 1

private def frontPprime : AgentState 2 × AgentState 2 :=
  pPsiLeaderResetProbeWall hTwo frontPrepared.1.core frontPrepared.2.core

private def frontThroughCheck :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
    hTwo hTwo hTwoLe 1 frontPrepared.1 frontPrepared.2

private def frontAfterDisappear :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedDisappear hTwo frontThroughCheck.1 frontThroughCheck.2

private def frontBeforeSuppress :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hTwo
    frontAfterDisappear.1 frontAfterDisappear.2

private def frontPrefix : AgentState 2 × AgentState 2 :=
  BirthShortWait.suppressPrefix
    frontBeforeSuppress.1.core frontBeforeSuppress.2.core

private def frontShort : AgentState 2 × AgentState 2 :=
  BirthShortWait.shortCountReset hTwo hTwoLe frontPrefix.1 frontPrefix.2

private def frontTerminal : AgentState 2 × AgentState 2 :=
  suppressSigTerminal hTwo frontShort.1 frontShort.2

private def frontEcho : AgentState 2 × AgentState 2 :=
  suppressSigEcho frontTerminal.1 frontTerminal.2

private def frontFinish : AgentState 2 × AgentState 2 :=
  suppressSigFinish frontEcho.1 frontEcho.2

/-- A legitimate follower reset handoff creates an echo behind the moving
front. This is why global `forall i, echo=false` is not an invariant. -/
theorem front_step_creates_behind_echo :
    frontPprime.2.label = (1 : Fin 2) ∧
      frontPprime.2.echo = false ∧
      frontBeforeSuppress.1.core.leader = false ∧
      frontBeforeSuppress.1.core.reset_cmd = true ∧
      frontPrefix.1.reset_cmd = false ∧
      frontPrefix.2.reset_cmd = true ∧
      frontTerminal.1.echo = true ∧
      frontTerminal.2.reset_cmd = true ∧
      frontEcho.1.echo = true ∧
      frontEcho.2.reset_cmd = true ∧
      frontFinish.1.echo = true ∧
      frontFinish.2.reset_cmd = true := by
  decide

private theorem front_finish_is_actual_raw_suppress :
    frontFinish =
      BirthShortWait.suppressSigResetKillWidth hTwo hTwo hTwoLe
        frontBeforeSuppress.1.core frontBeforeSuppress.2.core := by
  rfl

/-- Advance the actual current consumer on the genuine reset-front edge. -/
def frontAfter : Fin 3 -> E :=
  BirthShortDoneTerminalConsumer.step hTwo hTwo hTwoLe
    ring3 frontStart 1

private theorem frontStart_initial_echo_free :
    ∀ i, (rawAt frontStart i).echo = false := by
  intro i
  rcases fin3_cases i with rfl | rfl | rfl <;> decide

private theorem offset10 :
    groupOffset ring3 (1 : Fin 3) 0 = (1 : Fin 3) := by decide

private theorem offset11 :
    groupOffset ring3 (1 : Fin 3) 1 = (2 : Fin 3) := by decide

private theorem offset12 :
    groupOffset ring3 (1 : Fin 3) 2 = (0 : Fin 3) := by decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontAfter_site2_reset :
    (rawAt frontAfter 2).reset_cmd = true := by decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontAfter_site2_neutral :
    ComparisonNeutral (rawAt frontAfter 2) := by
  unfold ComparisonNeutral
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontAfter_site1_neutral :
    ComparisonNeutral (rawAt frontAfter 1) := by
  unfold ComparisonNeutral
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontAfter_site0_unchanged :
    rawAt frontAfter 0 = rawAt frontStart 0 := by
  decide

private theorem frontAfter_resetSweepWitnessed :
    ResetSweepWitnessed ring3 frontAfter := by
  refine ⟨(1 : Fin 3), (fun i => rawAt frontStart i), 1,
    frontStart_initial_echo_free, ?_⟩
  unfold PPLLWallSweepSchedule.ResetSweepState
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · rw [offset11]
    exact frontAfter_site2_reset
  · rw [offset11]
    exact frontAfter_site2_neutral
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    rw [offset10]
    exact frontAfter_site1_neutral
  · intro k hk hkn
    have hk2 : k = 2 := by omega
    subst k
    rw [offset12]
    exact frontAfter_site0_unchanged

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontAfter_blockers :
    ∀ e, Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt
      hTwo ring3 frontAfter e := by
  intro e
  rcases fin3_cases e with rfl | rfl | rfl
  · unfold Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt
    dsimp only
    unfold isBarrier
    decide
  · unfold Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt
    dsimp only
    unfold isBarrier
    decide
  · unfold Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt
    dsimp only
    unfold isBarrier
    decide

/-- Correction.  The failed `decide` in the old
`frontAfter_leaders_zero` did not establish a nonzero-labelled leader.  In the
`i = 2` branch the target had already become the bare proposition
`(frontAfter 2).core.core.label = 0`; `decide` therefore evaluated that
proposition (correctly) as false and had no reason to use the contradictory
local hypothesis `hi : (frontAfter 2).core.core.leader = true`.


The fixture itself is behaving as the current row says it should.  Site 1 is a
reset source and site 2 is a follower.  At the literal reset-aware P-prime cut,
the responder probe is cleared and literal `pPsi` takes its nonbirth mismatch
branch: the responder remains a follower and is written to the successor label
1.  This is follower-label normalization at P-prime, not a leader birth and not
the later `K2BirthLeaderNormalize.normalizeLeader` seam (which would write zero
only to a computed leader).  The two final fields below certify that the same
leader/label facts hold in the actual complete current-row output. -/
private theorem frontPprime_site2_follower :
    frontPprime.2.leader = false := by
  decide


private theorem frontPprime_site2_label_one :
    frontPprime.2.label = (1 : Fin 2) := by
  exact front_step_creates_behind_echo.1


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontAfter_site2_follower :
    (frontAfter 2).core.core.leader = false := by
  decide


set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontAfter_site2_label_one :
    (frontAfter 2).core.core.label = (1 : Fin 2) := by
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontAfter_leaders_zero :
    LeadersLabelZero hTwo frontAfter := by
  unfold LeadersLabelZero
  intro i hi
  rcases fin3_cases i with rfl | rfl | rfl
  · decide
  · decide
  · have hne : (frontAfter 2).core.core.leader ≠ true := by
      rw [frontAfter_site2_follower]
      decide
    exact (hne hi).elim

private theorem peaceful_of_no_live
    (C : Fin 3 -> E)
    (hleader : ∃ i, (C i).core.core.leader = true)
    (hno : ∀ i, (C i).core.core.bullet ≠ (2 : Fin 3)) :
    ExpiringK2Projection.PeacefulGlobal ring3 C := by
  apply (ExpiringK2Projection.peacefulGlobal_iff ring3 C).2
  refine ⟨hleader, ?_⟩
  intro start hb
  exact (hno start hb).elim

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontAfter_no_live :
    ∀ i, (frontAfter i).core.core.bullet ≠ (2 : Fin 3) := by
  intro i
  rcases fin3_cases i with rfl | rfl | rfl <;> decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontAfter_peaceful :
    ExpiringK2Projection.PeacefulGlobal ring3 frontAfter := by
  apply peaceful_of_no_live frontAfter
  · exact ⟨0, by decide⟩
  · exact frontAfter_no_live

/-- The state *after* a legitimate current reset-front handoff satisfies the
full direct candidate, even though it already contains an echo behind the
front. -/
theorem frontAfter_sanitationCandidate :
    SanitationCandidate hTwo ring3 frontAfter := by
  exact ⟨frontAfter_blockers, frontAfter_resetSweepWitnessed,
    frontAfter_leaders_zero, frontAfter_peaceful⟩

/-- Now take an arbitrary allowed current row behind the distinguished front. -/
def frontBreak : Fin 3 -> E :=
  BirthShortDoneTerminalConsumer.step hTwo hTwo hTwoLe
    ring3 frontAfter 0

private def frontBreakBadEdge :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  preparedPair hTwo ring3 frontBreak 1

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontBreak_left_follower :
    frontBreakBadEdge.1.core.leader = false := by decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontBreak_right_follower :
    frontBreakBadEdge.2.core.leader = false := by decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontBreak_left_reset_free :
    frontBreakBadEdge.1.core.reset_cmd = false := by decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontBreak_barrier :
    isBarrier hTwo frontBreakBadEdge.1.core frontBreakBadEdge.2.core := by
  unfold isBarrier
  decide

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 32768 in
private theorem frontBreak_not_blocker :
    ¬ Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt
      hTwo ring3 frontBreak 1 := by
  intro h
  unfold Q11540PPrimeLatchDesign.NoResetFreeFollowerBarrierAt at h
  dsimp only at h
  apply h
  change frontBreakBadEdge.1.core.leader = false ∧
    frontBreakBadEdge.2.core.leader = false ∧
    frontBreakBadEdge.1.core.reset_cmd = false ∧
    isBarrier hTwo frontBreakBadEdge.1.core frontBreakBadEdge.2.core
  exact ⟨frontBreak_left_follower, frontBreak_right_follower,
    frontBreak_left_reset_free, frontBreak_barrier⟩

theorem reset_front_not_arbitrary_row_invariant :
    SanitationCandidate hTwo ring3 frontAfter ∧
      ¬ SanitationCandidate hTwo ring3 frontBreak := by
  constructor
  · -- All four fields of `SanitationCandidate`, explicitly: the static
    -- blocker, exact reset-front witness, leader-label normal form, and
    -- `PeacefulGlobal`.
    exact ⟨frontAfter_blockers, frontAfter_resetSweepWitnessed,
      frontAfter_leaders_zero, frontAfter_peaceful⟩
  · -- `frontBreak` is definitionally one literal current consumer row at
    -- edge 0.  `frontBreak_not_blocker` is already staged through the four
    -- concrete fields of the prepared bad edge at edge 1: both followers,
    -- reset-free initiator, and `isBarrier`.
    intro h
    exact frontBreak_not_blocker (h.1 1)

end Q11575PostBirthSanitation

#print axioms Q11575PostBirthSanitation.q11541_suppress_echo_collision
#print axioms Q11575PostBirthSanitation.q11541_n3_actual_counterexample
#print axioms Q11575PostBirthSanitation.sanitationCandidate_pprimeBlocked
#print axioms Q11575PostBirthSanitation.front_step_creates_behind_echo
#print axioms Q11575PostBirthSanitation.frontAfter_sanitationCandidate
#print axioms Q11575PostBirthSanitation.reset_front_not_arbitrary_row_invariant
