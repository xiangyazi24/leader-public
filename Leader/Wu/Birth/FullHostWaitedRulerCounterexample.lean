import Leader.Wu.Birth.FullHostRulerCounterexample

set_option autoImplicit false

namespace BirthFullHostWaitedRulerCounterexample

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepPreCheckResetRepair PPLLPpsiLeaderCreationRepair
  BirthFullHostRulerCounterexample

abbrev Local := ExpiringAgentState 2 2 16

/-- The stable ruler starts with WAIT true everywhere and every count zero.
No comparison path or crossing authorization is initially present. -/
def waitedInitial (i : Fin 8) : Local :=
  let s := stableInitial 2 16 i
  { s with core := { s.core with core := { s.core.core with wait := true } } }

theorem waitedInitial_paperSafe :
    PaperSafeConfig (by omega) ringEight (eraseExpiringConfig waitedInitial) := by
  have h := stableInitial_paperSafe 2 16
  exact {
    unique_leader := h.unique_leader
    no_nonpeaceful_bullet := h.no_nonpeaceful_bullet
    no_free_barrier := h.no_free_barrier
    no_free_overwriting_signal := h.no_free_overwriting_signal
    stable_id_sequence := h.stable_id_sequence }

theorem waitedInitial_clean :
    ∀ i : Fin 8,
      (waitedInitial i).core.core.wait = true ∧
      (waitedInitial i).core.core.count = 0 ∧
      (waitedInitial i).core.core.path = .bot ∧
      (waitedInitial i).core.path0Crossed = false ∧
      (waitedInitial i).core.core.state = .none ∧
      (waitedInitial i).core.core.path3 = none := by decide

def waitedSchedule : DetSchedule 8 :=
  [0, 0, 0, 2, 0, 2, 2, 0, 2, 2, 2, 2, 2, 0,
    0, 2, 0, 1, 1, 2, 1, 1, 1, 0, 1, 1, 0, 2,
    1, 1, 1, 0, 0, 1, 2, 1, 0, 2, 0, 1, 2, 2]

def waitedPrefix (t : Nat) : Fin 8 → Local :=
  runLocalSchedule ringEight
    (wallSweepBirthSignalZeroPathStallTransition (by omega) 2 16)
    waitedInitial (waitedSchedule.take t)

private theorem get_ofFn (C : Fin 8 → Local) :
    (Vector.ofFn C).get = C := by
  funext i
  simp [Vector.get]
  apply congrArg C
  apply Fin.ext
  rfl

/-- Tabulate each physical configuration solely to avoid duplicating the
evaluation of shared predecessor states in the finite trace certificates. -/
private def cachedRun : DetSchedule 8 → Vector Local 8 → Vector Local 8
  | [], C => C
  | e :: rest, C => cachedRun rest (Vector.ofFn (localStep ringEight
      (wallSweepBirthSignalZeroPathStallTransition (by omega) 2 16) C.get e))

private theorem cachedRun_correct (C : Fin 8 → Local) (word : DetSchedule 8) :
    (cachedRun word (Vector.ofFn C)).get =
      runLocalSchedule ringEight
        (wallSweepBirthSignalZeroPathStallTransition (by omega) 2 16) C word := by
  induction word generalizing C with
  | nil => exact get_ofFn C
  | cons e rest ih =>
      simp only [cachedRun, get_ofFn, runLocalSchedule]
      exact ih _

/-- All earlier configurations have no comparison path.  The first actual
generation coincides with the target terminal counter reaching kappa two;
the source group subsequently does the same. -/
theorem actual_wait_then_generation :
    (∀ t : Fin 13, ∀ i : Fin 8, (waitedPrefix t.val i).core.core.path = .bot) ∧
      (waitedPrefix 12 3).core.core.count = 1 ∧
      (waitedPrefix 13 3).core.core.count = 2 ∧
      (waitedPrefix 13 3).core.core.path = .some 1 1 ∧
      (waitedPrefix 17 1).core.core.count = 2 ∧
      (waitedPrefix 17 1).core.core.path = .some 1 0 := by
  unfold waitedPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The source terminal component and the target label-zero component are
removed separately.  A new source label-zero component then arrives beside
the retained target terminal component. -/
theorem split_component_trace :
    (waitedPrefix 36 1).core.core.path = .some 1 0 ∧
      (waitedPrefix 37 1).core.core.path = .bot ∧
      (waitedPrefix 37 2).core.core.path = .some 0 0 ∧
      (waitedPrefix 37 2).stall = 0 ∧
      (waitedPrefix 38 2).core.core.path = .bot ∧
      (waitedPrefix 38 3).core.core.path = .some 1 1 ∧
      (waitedPrefix 40 2).core.core.path = .some 0 0 ∧
      (waitedPrefix 40 2).core.core.state = .CHECK_ready := by
  unfold waitedPrefix
  simp only [← cachedRun_correct]
  decide

def finalBeforeCheck : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  wallSweepResetProbePreCheckResetBeforeCheck (by omega) 2
    (normalizeDeletion (waitedPrefix 41 2).core.erase)
    (normalizeDeletion (waitedPrefix 41 3).core.erase)

def finalAfterCheck : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedCheckSig (by omega) finalBeforeCheck.1 finalBeforeCheck.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The exact CHECK input has two congested components and both crossing
permissions false.  CHECK nevertheless re-arms both to compare and creates
the terminal leader from their mixed payload zero/one. -/
theorem check_accepts_congested_mixed_components :
    finalBeforeCheck.1.core.state = .congest ∧
      finalBeforeCheck.2.core.state = .congest ∧
      finalBeforeCheck.1.path0Crossed = false ∧
      finalBeforeCheck.2.path0Crossed = false ∧
      finalBeforeCheck.1.core.path = .some 0 0 ∧
      finalBeforeCheck.2.core.path = .some 1 1 ∧
      finalAfterCheck.1.core.state = .equal ∧
      finalAfterCheck.2.core.state = .equal ∧
      finalAfterCheck.2.core.leader = true := by
  unfold finalAfterCheck finalBeforeCheck waitedPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The real complete host has two leaders after the ordinary WAIT-gated
generation and the mixed-component CHECK. -/
theorem waited_current_host_second_birth :
    (waitedPrefix 42 2).core.core.leader = true ∧
      (waitedPrefix 42 6).core.core.leader = true ∧
      (waitedPrefix 42 2).core.core.label = 0 ∧
      (waitedPrefix 42 2).core.core.signal_B = 0 := by
  unfold waitedPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- No prefix changes the source, target, or any other group's ruler bits or
labels; source rewriting is absent from this witnessed failure. -/
theorem waited_prefix_bits_labels :
    ∀ t : Fin 43, ∀ i : Fin 8,
      (waitedPrefix t.val i).core.core.bit = (waitedInitial i).core.core.bit ∧
      (waitedPrefix t.val i).core.core.label = (waitedInitial i).core.core.label := by
  unfold waitedPrefix
  simp only [← cachedRun_correct]
  decide

end BirthFullHostWaitedRulerCounterexample

#print axioms BirthFullHostWaitedRulerCounterexample.waitedInitial_paperSafe
#print axioms BirthFullHostWaitedRulerCounterexample.actual_wait_then_generation
#print axioms BirthFullHostWaitedRulerCounterexample.split_component_trace
#print axioms BirthFullHostWaitedRulerCounterexample.check_accepts_congested_mixed_components
#print axioms BirthFullHostWaitedRulerCounterexample.waited_current_host_second_birth
#print axioms BirthFullHostWaitedRulerCounterexample.waited_prefix_bits_labels
