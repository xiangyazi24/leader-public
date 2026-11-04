import Leader.Wu.Birth.ShortDoneTerminalObserver

/-!
# Positive event witness for the actual terminal-entry DONE metadata

This is only local event nonvacuity.  The endpoints below are explicit values
of the existing finite expiring carrier.  No reachability, scheduler mass,
NoBirthAlong production, or baseline-dispatcher equivalence is asserted.
-/

namespace BirthShortDoneTerminalPositiveWitness

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  BirthSigMoveDisposalRepair

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

private theorem hTwo : 0 < 2 := by decide
private theorem hOne : 0 < 1 := by decide
private theorem hOneTwo : 1 ≤ 2 := by decide

/-- Full raw record.  The two endpoints below differ only in `probe`. -/
def raw (probe : Bool) : AgentState 2 :=
  { leader := false, probe := probe, phase := false, bit := false,
    wait := true, state := .none, path := .bot, reset := false,
    carry := false, count := 0, label := 0, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := 0, bullet := 0, shield := true,
    write_state := .none, write := .none, last := false,
    last_set := false, last_unset := false, b_carry := false,
    gen_ws := false, ws_echo := false, signal_ws := false }

/-- The raw records are genuine members of the κ=1 numeric/payload domain. -/
theorem raw_domain (probe : Bool) : (raw probe).inProtocolDomain 1 := by
  simp [raw, AgentState.inProtocolDomain]

/-- Exact bounded reification, authorization bit, expiry clock; no extra state. -/
def endpoint (probe : Bool) : ExpiringAgentState 2 1 1 :=
  ⟨⟨BoundedAgentState.ofDomain (raw probe) (raw_domain probe), false⟩, 0⟩

def left : ExpiringAgentState 2 1 1 := endpoint false

def right : ExpiringAgentState 2 1 1 := endpoint true

/-- The finite records erase exactly to the displayed raw records. -/
theorem endpoint_erase (probe : Bool) :
    (endpoint probe).core.core.erase = raw probe := by
  simp [endpoint, BoundedAgentState.erase_ofDomain]

/-- Their actual finite carriers carry the required raw-domain certificates. -/
theorem input_domains :
    left.core.core.erase.inProtocolDomain 1 ∧
      right.core.core.erase.inProtocolDomain 1 :=
  ⟨left.core.core.erase_inProtocolDomain,
    right.core.core.erase_inProtocolDomain⟩

/-- Exact source guard: follower/follower, reset-free initiator, live responder
probe, and a barrier because at ψ=2 the successor of label 0 is label 1. -/
theorem pprime_guard :
    (raw false).leader = false ∧
      (raw true).leader = false ∧
      (raw true).probe = true ∧
      (raw false).reset_cmd = false ∧
      isBarrier hTwo (raw false) (raw true) := by
  unfold isBarrier
  decide

/-- The retained reset-aware P-prime stage really creates the responder. -/
theorem pprime_birth :
    (pPsiLeaderResetProbeWall hTwo (raw false) (raw true)).2.leader = true := by
  rw [pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_no_reset
    hTwo (raw false) (raw true) pprime_guard.2.2.2.1]
  exact pPsiLeaderProbeWall_preserves_barrier_birth
    hTwo (raw false) (raw true)
      pprime_guard.1 pprime_guard.2.1 pprime_guard.2.2.1
      pprime_guard.2.2.2.2

/-- These exact finite inputs enter the ordinary metadata branch; neither
entry-disposal priority is active. -/
theorem ordinary_entry :
    deletionActive
        (normalizeDeletion (prepareExpiringDisposal hTwo left).core.erase) = false ∧
      deletionActive
        (normalizeDeletion (prepareExpiringDisposal hTwo right).core.erase) = false := by
  decide

set_option maxRecDepth 32768 in
/-- Direct kernel check of the ACTUAL terminal-entry metadata at width 1 < 2.
The old responder is a follower and the normalized computed responder is a
leader.  This is one fixed local row, not a replay of `positiveRun`. -/
theorem actual_responder_born :
    right.core.core.leader = false ∧
      (BirthShortDoneTerminalHost.metadata
        hTwo hOne hOneTwo left right).2.core.core.leader = true := by
  decide

/-- Exact requested nonvacuity of the observer's executable event. -/
theorem actual_terminal_birth :
    BirthShortDoneTerminalObserver.birthEvent
      hTwo hOne hOneTwo left right = true := by
  unfold BirthShortDoneTerminalObserver.birthEvent
  dsimp only
  unfold K2BirthDispatcher.newborn
  rw [actual_responder_born.1, actual_responder_born.2]
  simp

end BirthShortDoneTerminalPositiveWitness

#print axioms BirthShortDoneTerminalPositiveWitness.raw_domain
#print axioms BirthShortDoneTerminalPositiveWitness.endpoint_erase
#print axioms BirthShortDoneTerminalPositiveWitness.input_domains
#print axioms BirthShortDoneTerminalPositiveWitness.pprime_birth
#print axioms BirthShortDoneTerminalPositiveWitness.ordinary_entry
#print axioms BirthShortDoneTerminalPositiveWitness.actual_responder_born
#print axioms BirthShortDoneTerminalPositiveWitness.actual_terminal_birth
