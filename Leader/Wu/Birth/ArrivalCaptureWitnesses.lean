import Leader.Wu.Birth.ArrivalCaptureRepair

set_option autoImplicit false

namespace BirthArrivalCaptureWitnesses

open PPLL PPLLRepair PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair PPLLWallSweepFinite
  BirthFullHostRulerCounterexample BirthFullHostWaitedRulerCounterexample
  BirthCheckCongestGuardRepair BirthCheckParametricWait
  BirthSigMoveDisposalRepair BirthDisposalRouteInvariant
  BirthMismatchDisposalProducer BirthMismatchDisposalWitnesses
  BirthArrivalCaptureRepair

/-! Complete finite executions for the captured-arrival host.  Positive
WAIT/GEN comparisons and source-owned deletion are tested together with the
old equality, partial-expiry, full-cohort escape and stale-depart executions.
The old-depart theorem concerns the old named action-one host; the new
capture theorems use `arrivalFullTransition` throughout. -/

theorem hTwo : 2 > 0 := by decide

private theorem get_ofFn {n : Nat} {Q : Type} (C : Fin n → Q) :
    (Vector.ofFn C).get = C := by
  funext i
  simp [Vector.get]
  apply congrArg C
  apply Fin.ext
  rfl

private def cachedRun {n : Nat} {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q) :
    DetSchedule n → Vector Q n → Vector Q n
  | [], C => C
  | e :: rest, C => cachedRun ring T rest (Vector.ofFn (localStep ring T C.get e))

private theorem cachedRun_correct {n : Nat} {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q) (C : Fin n → Q) (word : DetSchedule n) :
    (cachedRun ring T word (Vector.ofFn C)).get = runLocalSchedule ring T C word := by
  induction word generalizing C with
  | nil => exact get_ofFn C
  | cons e rest ih =>
      simp only [cachedRun, get_ofFn, runLocalSchedule]
      exact ih _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Every two-bit word has a full thirteen-interaction positive execution,
including the real WAIT/GEN source, ready arrival and zero-signal leader. -/
theorem capture_all_four_equal_words (a b : Bool) :
    let run := fun t => runLocalSchedule ringEight (arrivalFullTransition hTwo 2 16)
      (familyInitial 16 a b) (equalSchedule.take t)
    (run 7 0).core.core.path = .bot ∧
      (run 7 1).core.core.path = .bot ∧
      (run 8 1).core.core.count = 2 ∧
      (run 8 0).core.core.path = .some 0 (if a then 1 else 0) ∧
      (run 8 1).core.core.path = .some 1 (if b then 1 else 0) ∧
      (run 12 2).core.core.state = .CHECK_ready ∧
      (run 12 3).core.core.state = .CHECK_ready ∧
      (run 12 2).core.path0Crossed = true ∧
      (∀ i : Fin 8, (run 13 i).core.core.leader = true ↔ i = 2) ∧
      (run 13 2).core.core.label = 0 ∧ (run 13 2).core.core.signal_B = 0 := by
  cases a <;> cases b <;> simp only [← cachedRun_correct] <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The prior eighteen-step same-GEN escape remains blocked at every prefix. -/
theorem capture_blocks_eighteen_step_escape :
    ∀ t : Fin 19, ∀ i : Fin 8,
      (runLocalSchedule ringEight (arrivalFullTransition hTwo 2 16) waitedInitial
        (disposalRegressionWord.take t.val) i).core.core.leader = true ↔ i = 6 := by
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The prior forty-two-step partial-expiry splice remains blocked. -/
theorem capture_blocks_forty_two_step_splice :
    ∀ t : Fin 43, ∀ i : Fin 8,
      (runLocalSchedule ringEight (arrivalFullTransition hTwo 2 16) waitedInitial
        (waitedSchedule.take t.val) i).core.core.leader = true ↔ i = 6 := by
  simp only [← cachedRun_correct]
  decide

/-- A nonterminal mismatch in the three-component whole-present window
still propagates its real action four to a terminal disposal entry. -/
theorem capture_preserves_three_bit_disposal :
    let C := runLocalSchedule ringSix (arrivalFullTransition (by decide) 2 16)
      threeBitWindow [0, 1]
    (∀ i : Fin 3, (C ⟨i.val, by omega⟩).core.core.path = .some i 0) ∧
      (C 2).core.erase.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      DisposalDue (by decide) (C 2).core.erase := by
  unfold DisposalDue
  simp only [← cachedRun_correct]
  decide

/-- The rooted stale-equality input now receives a complete comparison and
then the actual action-four deletion service. -/
def rootedWord : DetSchedule 16 :=
  BirthFreshEqualArrivalCounterexample.schedule ++ [5, 6, 6, 6, 5]

def rootedPrefix (t : Nat) : Fin 16 → ExpiringAgentState 2 2 16 :=
  runLocalSchedule BirthFreshEqualArrivalCounterexample.ringSixteen
    (arrivalFullTransition hTwo 2 16) BirthFreshEqualArrivalCounterexample.initial
    (rootedWord.take t)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Fresh terminal arrival is captured at eleven, both components are ready
at twelve, and the first unequal bit emits action four at thirteen.  It
reaches terminal disposal at fourteen and both components are gone at sixteen. -/
theorem capture_rooted_mismatch_inspects_and_retires :
    (rootedPrefix 11 7).core.core.state = .CHECK_ready ∧
      (rootedPrefix 11 7).core.core.path = .some 1 0 ∧
      (rootedPrefix 12 6).core.core.state = .CHECK_ready ∧
      (rootedPrefix 12 7).core.core.state = .CHECK_ready ∧
      (rootedPrefix 12 6).core.path0Crossed = true ∧
      (rootedPrefix 13 6).core.erase.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      DisposalDue hTwo (rootedPrefix 14 7).core.erase ∧
      (rootedPrefix 16 6).core.core.path = .bot ∧
      (rootedPrefix 16 7).core.core.path = .bot ∧
      (∀ t : Fin 17, ∀ i : Fin 16,
        (rootedPrefix t.val i).core.core.leader = true ↔ i = 14) := by
  unfold DisposalDue rootedPrefix
  simp only [← cachedRun_correct]
  decide

/-- Ordinary empty targets except for old depart decisions at three
matching terminal positions.  Timers have the existing fresh-budget value. -/
def departInitial (i : Fin 8) : ExpiringAgentState 2 2 16 :=
  let u := familyInitial 16 false false i
  if i = 3 ∨ i = 5 ∨ i = 7 then
    { u with core := { u.core with core := { u.core.core with state := .depart } } }
  else u

def departWord : DetSchedule 8 :=
  List.replicate 8 0 ++ [1, 2, 3, 4, 5, 6, 0, 1] ++ List.replicate 17 1

def oldDepartPrefix (t : Nat) : Fin 8 → ExpiringAgentState 2 2 16 :=
  runLocalSchedule ringEight (actionOneFullTransition hTwo 2 16)
    departInitial (departWord.take t)

def capturedDepartPrefix (t : Nat) : Fin 8 → ExpiringAgentState 2 2 16 :=
  runLocalSchedule ringEight (arrivalFullTransition hTwo 2 16)
    departInitial (departWord.take t)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- In the old complete action-one host, a real terminal can bypass matching
old depart states and survive five sites ahead when its predecessor expires.
Thus a two-psi coverage premise fails for this host even without bit changes. -/
theorem actual_old_depart_exceeds_two_psi :
    departWord.length = 33 ∧
      (∀ t : Fin 8, ∀ i : Fin 8, (oldDepartPrefix t.val i).core.core.path = .bot) ∧
      (oldDepartPrefix 8 0).core.core.path = .some 0 0 ∧
      (oldDepartPrefix 8 1).core.core.path = .some 1 0 ∧
      (oldDepartPrefix 14 0).core.core.path = .some 0 0 ∧
      (oldDepartPrefix 14 7).core.core.path = .some 1 0 ∧
      (oldDepartPrefix 16 2).core.core.path = .some 0 0 ∧
      (oldDepartPrefix 16 2).stall.val = 16 ∧
      (oldDepartPrefix 32 2).core.core.path = .some 0 0 ∧
      (oldDepartPrefix 32 2).stall.val = 0 ∧
      (oldDepartPrefix 33 2).core.core.path = .bot ∧
      (∀ t : Fin 20,
        (oldDepartPrefix (14 + t.val) 7).core.core.path = .some 1 0) ∧
      ((7 + 8 - 2) % 8 : Nat) > 2 * 2 := by
  unfold oldDepartPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The same original generated terminal is captured at its first matching
site in the new host; the next outgoing edge cannot pass it onward. -/
theorem capture_blocks_old_depart_bypass :
    (capturedDepartPrefix 8 0).core.core.path = .some 0 0 ∧
      (capturedDepartPrefix 8 1).core.core.path = .some 1 0 ∧
      (capturedDepartPrefix 10 3).core.core.path = .some 1 0 ∧
      (capturedDepartPrefix 10 3).core.core.state = .CHECK_ready ∧
      (capturedDepartPrefix 11 3).core.core.path = .some 1 0 ∧
      (capturedDepartPrefix 11 4).core.core.path = .bot ∧
      (capturedDepartPrefix 14 7).core.core.path = .bot := by
  unfold capturedDepartPrefix
  simp only [← cachedRun_correct]
  decide

/-- Expose the two exact GENSIG writer guards in the old causal trace.
Both are false at every post-generation terminal transfer, so matching path
values cannot be explained by a replacement production in those calls. -/
def oldDepartGenStart (t : Nat) (e : Fin 8) : AgentState 2 × AgentState 2 :=
  let p := authorizedPPsiLeaderResetProbeWall hTwo
    (preparedInput hTwo (oldDepartPrefix t e).core.erase)
    (preparedInput hTwo (oldDepartPrefix t (ringEight.rightNeighbor e)).core.erase)
  let w := waitSaturated hTwo 2 p.1.core p.2.core
  genSigSaturatedStart hTwo w.1 w.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The six outward transfers execute no GENSIG emit or backward path
rewrite.  The only initial source event remains the prefix-eight production. -/
theorem old_depart_has_no_replacement_generation :
    ∀ k : Fin 6,
      (oldDepartGenStart (8 + k.val) ⟨1 + k.val, by omega⟩).1.state ≠ .produce ∧
      (oldDepartGenStart (8 + k.val) ⟨1 + k.val, by omega⟩).2.state ≠ .produce := by
  unfold oldDepartGenStart oldDepartPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The same nonproduction guard check supplements the frozen sixteen-site
fresh-equality trace: its three matching path values are actual descendants
through transport, not fresh identical replacements by GENSIG. -/
theorem rooted_old_has_no_replacement_generation :
    ∀ k : Fin 3,
      let p := BirthFreshEqualArrivalCounterexample.afterProbe
        (8 + k.val) (BirthFreshEqualArrivalCounterexample.moveEdge k)
      let w := waitSaturated hTwo 2 p.1.core p.2.core
      let g := genSigSaturatedStart hTwo w.1 w.2
      g.1.state ≠ .produce ∧ g.2.state ≠ .produce := by
  unfold BirthFreshEqualArrivalCounterexample.afterProbe
    BirthFreshEqualArrivalCounterexample.arrivalPrefix
  simp only [← cachedRun_correct]
  decide

/-- A fresh terminal first lands off target at site two.  Its old comparison
state can be any state except the retained explicit produce admission guard. -/
def transitInitial (st : MainState) (i : Fin 8) : ExpiringAgentState 2 2 16 :=
  let u := familyInitial 16 false false i
  if i = 2 then { u with core := { u.core with core := { u.core.core with state := st } } }
  else u

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Real WAIT/GEN transport crosses every admitted old receiver-state case,
including lock and compare1, and then captures the matching target. -/
theorem capture_misaligned_state_family (st : MainState) (hs : st ≠ .produce) :
    let C := runLocalSchedule ringEight (arrivalFullTransition hTwo 2 16)
      (transitInitial st) (List.replicate 8 0 ++ [1, 2])
    (C 3).core.core.path = .some 1 0 ∧ (C 3).core.core.state = .CHECK_ready ∧
      (C 2).core.core.path = .bot := by
  cases st <;> try contradiction
  all_goals simp only [← cachedRun_correct]
  all_goals decide

end BirthArrivalCaptureWitnesses

#print axioms BirthArrivalCaptureWitnesses.capture_all_four_equal_words
#print axioms BirthArrivalCaptureWitnesses.capture_blocks_eighteen_step_escape
#print axioms BirthArrivalCaptureWitnesses.capture_blocks_forty_two_step_splice
#print axioms BirthArrivalCaptureWitnesses.capture_preserves_three_bit_disposal
#print axioms BirthArrivalCaptureWitnesses.capture_rooted_mismatch_inspects_and_retires
#print axioms BirthArrivalCaptureWitnesses.actual_old_depart_exceeds_two_psi
#print axioms BirthArrivalCaptureWitnesses.capture_blocks_old_depart_bypass

#print axioms BirthArrivalCaptureWitnesses.old_depart_has_no_replacement_generation
#print axioms BirthArrivalCaptureWitnesses.rooted_old_has_no_replacement_generation
#print axioms BirthArrivalCaptureWitnesses.capture_misaligned_state_family
