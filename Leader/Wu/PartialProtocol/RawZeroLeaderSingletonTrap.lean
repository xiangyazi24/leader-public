import Leader.Wu.PartialProtocol.DomainClosure

/-!
# Raw `P_partial`: a singleton zero-leader boundary trap

This module audits the compiled, unmodified `P_partial` transition.  It does
not use a seal, birth, or other overlay repair.

The witness is deliberately marked as a boundary result: its ring has one
agent, whereas `OperationalRegime` assumes `1 < n`.  On the singleton ring the
initiator and responder are the same site, and `localStep` keeps the first
transition output.  A terminal deletion carrier is unchanged in that first
output, so this follower configuration is fixed under every finite schedule.
No statement below extrapolates the witness to a nontrivial ring.
-/

namespace PPLLCompleteMultiLeaderCleanup

open PPLL PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair

set_option autoImplicit false

/-! ## Exact finite witness -/

theorem rawZeroBoundary_hpsi : (1 : Nat) > 0 := by
  omega

/-- A domain-valid terminal deletion carrier with follower output. -/
def rawZeroBoundaryCore : BoundedAgentState 1 0 where
  leader := false
  probe := false
  phase := false
  bit := false
  wait := false
  state := .eliminate_signal
  path := .some 0 0
  reset := false
  carry := false
  count := 0
  label := 0
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
  signal_ws := false

def rawZeroBoundaryState : ExpiringAgentState 1 0 0 :=
  ⟨⟨rawZeroBoundaryCore, false⟩, freshStall 0⟩

def rawZeroBoundaryConfig : PPartialConfig 1 1 0 0 :=
  fun _ => rawZeroBoundaryState

/-- The unique directed ring of size one, outside `OperationalRegime`. -/
theorem rawZeroBoundaryRing : DirectedRing 1 :=
  ⟨by omega⟩

/-! ## Exact raw transition and schedule closure -/

/-- The first output of the exact raw interaction is definitionally the input.
The second output is cleared, but a singleton `localStep` never selects it. -/
theorem rawZeroBoundary_transition_first_fixed :
    (P_partialUnconditional rawZeroBoundary_hpsi 0 0
      rawZeroBoundaryState rawZeroBoundaryState).1 =
        rawZeroBoundaryState := by
  rfl

/-- Every singleton-ring local step is identity on the witness. -/
theorem rawZeroBoundary_localStep_fixed (e : Fin 1) :
    localStep rawZeroBoundaryRing
      (P_partialUnconditional rawZeroBoundary_hpsi 0 0)
      rawZeroBoundaryConfig e = rawZeroBoundaryConfig := by
  funext i
  have hi : i = e := Subsingleton.elim i e
  subst i
  simpa [localStep, rawZeroBoundaryConfig] using
    rawZeroBoundary_transition_first_fixed

/-- Hence every finite exact schedule leaves the whole configuration fixed. -/
theorem rawZeroBoundary_run_fixed (word : DetSchedule 1) :
    runLocalSchedule rawZeroBoundaryRing
      (P_partialUnconditional rawZeroBoundary_hpsi 0 0)
      rawZeroBoundaryConfig word = rawZeroBoundaryConfig := by
  induction word with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only [runLocalSchedule]
      rw [rawZeroBoundary_localStep_fixed, ih]

/-! ## Zero output and producer failure -/

theorem rawZeroBoundary_leader_false :
    rawZeroBoundaryState.core.core.leader = false := by
  rfl

theorem rawZeroBoundary_leaderCount_zero :
    P_partialLeaderCount rawZeroBoundaryConfig = 0 := by
  rfl

theorem rawZeroBoundary_not_legit :
    ¬ PPartialLegitUnconditional rawZeroBoundary_hpsi 0 0
      rawZeroBoundaryConfig := by
  intro h
  rcases h with ⟨i, hi, _⟩
  simp [P_partialProtocol, rawZeroBoundaryConfig,
    rawZeroBoundaryState, rawZeroBoundaryCore, isLeaderOutput] at hi

/-- No finite exact word can create a legitimate leader output from the
singleton witness. -/
theorem rawZeroBoundary_no_finite_birth :
    ¬ ∃ word : DetSchedule 1,
      PPartialLegitUnconditional rawZeroBoundary_hpsi 0 0
        (runLocalSchedule rawZeroBoundaryRing
          (P_partialUnconditional rawZeroBoundary_hpsi 0 0)
          rawZeroBoundaryConfig word) := by
  rintro ⟨word, hword⟩
  rw [rawZeroBoundary_run_fixed] at hword
  exact rawZeroBoundary_not_legit hword

/-- Consequently the unconditional rank-zero/rank-one producer premise fails
for every proposed finite bound on this boundary ring. -/
theorem rawZeroBoundary_not_baseProducer (baseBound : Nat) :
    ¬ PPartialBaseProducerUnconditional rawZeroBoundary_hpsi 0 0
      rawZeroBoundaryRing baseBound := by
  intro hproducer
  obtain ⟨word, _hLength, hlegit⟩ :=
    hproducer rawZeroBoundaryConfig (by
      rw [rawZeroBoundary_leaderCount_zero]
      omega)
  exact rawZeroBoundary_no_finite_birth ⟨word, hlegit⟩

#print axioms rawZeroBoundary_transition_first_fixed
#print axioms rawZeroBoundary_run_fixed
#print axioms rawZeroBoundary_no_finite_birth
#print axioms rawZeroBoundary_not_baseProducer

end PPLLCompleteMultiLeaderCleanup
