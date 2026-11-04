import Leader.Wu.Birth.FirstBirthCohort
import Leader.Wu.Birth.ShortDoneTerminalPositiveWitness
import Leader.Wu.Birth.ShortDoneTerminalDeletionPpsiFrame
import Leader.Wu.Birth.ShortDoneTerminalBirthSources

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

/-! ## 1. Repair of the raw re-arm leaf, statement unchanged -/

namespace Q11527ProbeQuarantineCensus

open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open BirthShortDoneTerminalBirthSources

/-- Same statement as the original leaf.  The only repair is to avoid asking `decide`
for a conjunction containing the proposition-valued `isBarrier`. -/
theorem pprime_wall_rearms_probe_from_absence :
    let l := BirthShortDoneTerminalPositiveWitness.raw false
    let r := BirthShortDoneTerminalPositiveWitness.raw false
    l.probe = false /\
      r.probe = false /\
      isBarrier (by decide : 0 < 2) l r /\
      (PPLLWallSweepRepair.pPsiLeaderResetProbeWall
        (by decide : 0 < 2) l r).1.probe = true := by
  dsimp
  refine ⟨rfl, rfl, ?_, ?_⟩
  · unfold isBarrier
    decide
  · decide

end Q11527ProbeQuarantineCensus

/-! ## 2. Current width-two suffix and the exact reset seam -/

namespace Q11531PPrimeRebirth

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
open BirthGenerationControlRepair BirthGenerationDone BirthShortWait
  BirthShortDoneCuts BirthShortDoneTerminalEntryCut
  BirthSigMoveDisposalRepair BirthShortDoneTerminalBirthSources

variable {psi kappa tau : Nat}

private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 ≤ 2 := by decide
private theorem hFour : 0 < 4 := by decide

/-- The old P-prime control view plus the one extra field needed by the
P-prime birth guard. -/
def PpsiResetView (u : AgentState psi) :
    PPLLPpsiLeaderCreationRepair.PpsiControlView psi × Bool :=
  (PPLLPpsiLeaderCreationRepair.PpsiControlView.ofState u, u.reset_cmd)

def expiringPpsiResetPair
    (q : ExpiringAgentState psi kappa tau × ExpiringAgentState psi kappa tau) :
    (PPLLPpsiLeaderCreationRepair.PpsiControlView psi × Bool) ×
      (PPLLPpsiLeaderCreationRepair.PpsiControlView psi × Bool) :=
  (PpsiResetView q.1.core.core.erase, PpsiResetView q.2.core.core.erase)

private def rearmPprime : AgentState 2 × AgentState 2 :=
  PPLLWallSweepRepair.pPsiLeaderResetProbeWall hTwo
    (BirthShortDoneTerminalPositiveWitness.raw false)
    (BirthShortDoneTerminalPositiveWitness.raw false)

private def rearmRow :
    ExpiringAgentState 2 1 1 × ExpiringAgentState 2 1 1 :=
  BirthShortDoneTerminalHost.row hTwo hTwo hTwoLe
    (BirthShortDoneTerminalPositiveWitness.endpoint false)
    (BirthShortDoneTerminalPositiveWitness.endpoint false)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 32768 in
/-- The exact first trace pair really reaches the ordinary width-two branch
and has no birth on that row. -/
theorem width_two_rearm_pair_is_ordinary_no_birth :
    let e := BirthShortDoneTerminalPositiveWitness.endpoint false
    deletionActive
        (normalizeDeletion (prepareExpiringDisposal hTwo e).core.erase) = false /\
      deletionActive
        (normalizeDeletion (prepareExpiringDisposal hTwo e).core.erase) = false /\
      BirthShortDoneTerminalObserver.birthEvent hTwo hTwo hTwoLe e e = false := by
  decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 32768 in
/-- On the reset-free follower/follower pair used by the trace, the complete
CURRENT host suffix retains `(label, probe, phase, reset_cmd)` exactly from the
actual P-prime-wall output. -/
theorem width_two_rearm_suffix_frame :
    expiringPpsiResetPair rearmRow =
      (PpsiResetView rearmPprime.1, PpsiResetView rearmPprime.2) := by
  decide

/-! The four-field statement is not an unconditional ordinary-row frame.
An existing initiator leader generates a reset command at Algorithm 14. -/

def leaderRaw : AgentState 2 :=
  { BirthShortDoneTerminalPositiveWitness.raw false with leader := true }

private theorem leaderRaw_domain : leaderRaw.inProtocolDomain 1 := by
  simp [leaderRaw, BirthShortDoneTerminalPositiveWitness.raw,
    AgentState.inProtocolDomain]

def leaderEndpoint : ExpiringAgentState 2 1 1 :=
  ⟨⟨BoundedAgentState.ofDomain leaderRaw leaderRaw_domain, false⟩, 0⟩

private def leaderPreparedL : AuthorizedAgentState 2 :=
  normalizeDeletion (prepareExpiringDisposal hTwo leaderEndpoint).core.erase

private def leaderPreparedR : AuthorizedAgentState 2 :=
  normalizeDeletion
    (prepareExpiringDisposal hTwo
      (BirthShortDoneTerminalPositiveWitness.endpoint false)).core.erase

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 32768 in
/-- This is genuinely the current ordinary branch: both prepared deletion
priorities are false, and the current width-two local birth bit is false. -/
theorem leader_pair_is_ordinary_no_birth :
    deletionActive leaderPreparedR = false /\
      deletionActive leaderPreparedL = false /\
      BirthShortDoneTerminalObserver.birthEvent hTwo hTwo hTwoLe
        leaderEndpoint
        (BirthShortDoneTerminalPositiveWitness.endpoint false) = false := by
  decide

private def leaderPprime : AgentState 2 × AgentState 2 :=
  PPLLWallSweepRepair.pPsiLeaderResetProbeWall hTwo
    leaderPreparedL.core leaderPreparedR.core

private def leaderThroughCheck :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
    hTwo hTwo hTwoLe 1 leaderPreparedL leaderPreparedR

private def leaderAfterDisappear :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedDisappear hTwo leaderThroughCheck.1 leaderThroughCheck.2

private def leaderBeforeSuppress :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hTwo
    leaderAfterDisappear.1 leaderAfterDisappear.2

private def leaderSuppressed :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  BirthShortDoneCuts.authorizedSuppressWidth hTwo hTwo hTwoLe
    leaderBeforeSuppress.1 leaderBeforeSuppress.2

/-- Every current suffix stage before SUPPRESS has retained the P-prime
three-field view and the reset bit on this ordinary/no-birth witness. -/
theorem ordinary_prefix_through_compare_frames_ppsi_reset :
    (PpsiResetView leaderBeforeSuppress.1.core,
      PpsiResetView leaderBeforeSuppress.2.core) =
    (PpsiResetView leaderPprime.1, PpsiResetView leaderPprime.2) := by
  decide

/-- The existing PpsiControlView theorem still applies at the first bad reset
stage: SUPPRESS changes no `(label, probe, phase)`. -/
theorem ppsiControl_survives_first_reset_failure :
    PPLLPpsiLeaderCreationRepair.authorizedPpsiControlPair leaderSuppressed =
      PPLLPpsiLeaderCreationRepair.authorizedPpsiControlPair
        leaderBeforeSuppress := by
  change
    PPLLPpsiLeaderCreationRepair.authorizedPpsiControlPair
        (BirthShortDoneCuts.authorizedSuppressWidth hTwo hTwo hTwoLe
          leaderBeforeSuppress.1 leaderBeforeSuppress.2) =
      PPLLPpsiLeaderCreationRepair.authorizedPpsiControlPair leaderBeforeSuppress
  rw [BirthShortDoneCuts.authorizedSuppressWidth_full hTwo]
  exact
    PPLLPpsiLeaderCreationRepair.authorizedSuppressSigResetKill_ppsiControlPair
      hTwo leaderBeforeSuppress.1 leaderBeforeSuppress.2

/-- Exact first failure of the attempted four-field frame.  At the actual
post-CHECK/post-DISAPPEAR/post-COMPARE cut, both reset bits are still false and
the initiator is still the pre-existing leader; the very first raw SUPPRESS
substage sets its reset command. -/
theorem reset_cmd_frame_first_fails_at_suppressSigStart :
    leaderBeforeSuppress.1.core.leader = true /\
      leaderBeforeSuppress.1.core.reset_cmd = false /\
      leaderBeforeSuppress.2.core.reset_cmd = false /\
      (PPLL.suppressSigStart
        leaderBeforeSuppress.1.core leaderBeforeSuppress.2.core).1.reset_cmd = true := by
  decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 32768 in
/-- Consequently the combined four-field frame is already false across the
current width-two SUPPRESS stage, even though the PpsiControlView part frames. -/
theorem reset_cmd_not_preserved_by_ordinary_suffix :
    (leaderSuppressed.1.core.reset_cmd, leaderSuppressed.2.core.reset_cmd) ≠
      (leaderBeforeSuppress.1.core.reset_cmd,
        leaderBeforeSuppress.2.core.reset_cmd) := by
  decide

/-! ## 3. The actual four-site two-step trace -/

def ring4 : DirectedRing 4 := ⟨hFour⟩

def siteA : Fin 4 := 0
def siteB : Fin 4 := 1
def siteC : Fin 4 := 2
def siteRoot : Fin 4 := 3

/-- Arbitrary one-leader configuration used only for this finite countertrace.
Sites 0,1,2 are the reset-free follower records; site 3 is the same
finite record with only its leader bit set. -/
def initialConfig : Fin 4 → ExpiringAgentState 2 1 1 := fun i =>
  if i = siteRoot then leaderEndpoint
  else BirthShortDoneTerminalPositiveWitness.endpoint false

/-- The manually supplied initial configuration has exactly the advertised
four local leader bits. -/
theorem initial_one_remote_leader :
    (initialConfig siteA).core.core.leader = false /\
      (initialConfig siteB).core.core.leader = false /\
      (initialConfig siteC).core.core.leader = false /\
      (initialConfig siteRoot).core.core.leader = true := by
  decide

def afterRearm : Fin 4 → ExpiringAgentState 2 1 1 :=
  BirthShortDoneTerminalConsumer.step hTwo hTwo hTwoLe
    ring4 initialConfig siteB

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 32768 in
/-- The first ACTUAL current-consumer step is edge 1->2.  It does not birth;
it leaves the old leader untouched and re-arms site 1 exactly as needed for
the next P-prime source. -/
theorem first_step_rearms_probe_and_keeps_remote_leader :
    (afterRearm siteRoot).core.core.leader = true /\
      (afterRearm siteB).core.core.leader = false /\
      (afterRearm siteB).core.core.label = (0 : Fin 2) /\
      (afterRearm siteB).core.core.probe = true /\
      (afterRearm siteB).core.core.phase = true /\
      (afterRearm siteB).core.core.reset_cmd = false /\
      (afterRearm siteC).core.core.leader = false /\
      (afterRearm siteC).core.core.label = (1 : Fin 2) := by
  decide

private def secondPreparedL : AuthorizedAgentState 2 :=
  normalizeDeletion
    (prepareExpiringDisposal hTwo (afterRearm siteA)).core.erase

private def secondPreparedR : AuthorizedAgentState 2 :=
  normalizeDeletion
    (prepareExpiringDisposal hTwo (afterRearm siteB)).core.erase

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 32768 in
/-- The second edge's ACTUAL prepared/normalized P-prime input satisfies the
source guard.  The proposition-valued barrier component is discharged
separately, avoiding a Decidable failure. -/
theorem second_edge_pprime_guard :
    PPrimeBarrierBirthGuard hTwo secondPreparedL secondPreparedR := by
  unfold PPrimeBarrierBirthGuard
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · unfold isBarrier
    decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 32768 in
/-- This is specifically a P-prime-stage birth, before CHECK can be blamed. -/
theorem second_edge_pprime_birth :
    pPrimeBirth hTwo secondPreparedL secondPreparedR = true := by
  decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 32768 in
/-- The full current metadata observer also records a birth on edge 0->1. -/
theorem second_edge_actual_birth_event :
    BirthShortDoneTerminalObserver.birthEvent hTwo hTwo hTwoLe
      (afterRearm siteA) (afterRearm siteB) = true := by
  decide

def afterRebirth : Fin 4 → ExpiringAgentState 2 1 1 :=
  BirthShortDoneTerminalConsumer.step hTwo hTwo hTwoLe
    ring4 afterRearm siteA

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 32768 in
/-- Complete current-consumer certificate.  Site 3 is already a leader before
the second interaction; site 1 is still a follower then, and is a leader after
edge 0->1, while site 3 remains a leader. -/
theorem actual_two_step_rebirth_while_first_present :
    (afterRearm siteRoot).core.core.leader = true /\
      (afterRearm siteB).core.core.leader = false /\
      (afterRebirth siteRoot).core.core.leader = true /\
      (afterRebirth siteB).core.core.leader = true /\
      siteRoot ≠ siteB := by
  decide

end Q11531PPrimeRebirth

#print axioms Q11527ProbeQuarantineCensus.pprime_wall_rearms_probe_from_absence
#print axioms Q11531PPrimeRebirth.width_two_rearm_pair_is_ordinary_no_birth
#print axioms Q11531PPrimeRebirth.width_two_rearm_suffix_frame
#print axioms Q11531PPrimeRebirth.leader_pair_is_ordinary_no_birth
#print axioms Q11531PPrimeRebirth.ordinary_prefix_through_compare_frames_ppsi_reset
#print axioms Q11531PPrimeRebirth.ppsiControl_survives_first_reset_failure
#print axioms Q11531PPrimeRebirth.reset_cmd_frame_first_fails_at_suppressSigStart
#print axioms Q11531PPrimeRebirth.reset_cmd_not_preserved_by_ordinary_suffix
#print axioms Q11531PPrimeRebirth.initial_one_remote_leader
#print axioms Q11531PPrimeRebirth.first_step_rearms_probe_and_keeps_remote_leader
#print axioms Q11531PPrimeRebirth.second_edge_pprime_guard
#print axioms Q11531PPrimeRebirth.second_edge_pprime_birth
#print axioms Q11531PPrimeRebirth.second_edge_actual_birth_event
#print axioms Q11531PPrimeRebirth.actual_two_step_rebirth_while_first_present
