import Leader.Wu.Birth.SingleUseReleaseRepair

set_option autoImplicit false

namespace BirthSingleUseReleaseWitnesses

open PPLL PPLLRepair PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair PPLLWallSweepFinite
  BirthFullHostRulerCounterexample BirthFullHostWaitedRulerCounterexample
  BirthCheckCongestGuardRepair BirthCheckParametricWait
  BirthSigMoveDisposalRepair BirthDisposalRouteInvariant
  BirthMismatchDisposalProducer BirthMismatchDisposalWitnesses
  BirthArrivalCaptureRepair BirthArrivalCaptureWitnesses BirthGenerationControlRepair
  BirthTossCheckRearmCounterexample BirthTossCheckPreservationRepair
  BirthTossReleaseLifecycleWitnesses BirthSingleUseReleaseRepair

/-! Complete executions of single-use release.  The genuine fresh-comparison
producer still releases its current terminal.  Consumption then restores
capture and a real comparison at the next ruler group.  The previously
checked thirty-four-step repeat-release word is blocked on this same host.
These finite witnesses do not assume a global cohort or span invariant. -/

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
/-- All four two-bit words retain their actual thirteen-step equal
comparison and unique zero-signal leader. -/
theorem single_use_preserves_all_four_equal_words (a b : Bool) :
    let run := fun t => runLocalSchedule ringEight (singleUseFullTransition hTwo 2 16)
      (familyInitial 16 a b) (equalSchedule.take t)
    (run 8 0).core.core.path = .some 0 (if a then 1 else 0) ∧
      (run 8 1).core.core.path = .some 1 (if b then 1 else 0) ∧
      (∀ i : Fin 8, (run 13 i).core.core.leader = true ↔ i = 2) ∧
      (run 13 2).core.core.signal_B = 0 := by
  cases a <;> cases b <;> simp only [← cachedRun_correct] <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The eighteen-step complete-cohort escape is still blocked throughout. -/
theorem single_use_blocks_eighteen_step_escape :
    ∀ t : Fin 19, ∀ i : Fin 8,
      (runLocalSchedule ringEight (singleUseFullTransition hTwo 2 16) waitedInitial
        (disposalRegressionWord.take t.val) i).core.core.leader = true ↔ i = 6 := by
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The old forty-two-step partial-expiry splice remains blocked. -/
theorem single_use_blocks_forty_two_step_splice :
    ∀ t : Fin 43, ∀ i : Fin 8,
      (runLocalSchedule ringEight (singleUseFullTransition hTwo 2 16) waitedInitial
        (waitedSchedule.take t.val) i).core.core.leader = true ↔ i = 6 := by
  simp only [← cachedRun_correct]
  decide

/-- The whole-present three-bit mismatch still propagates action four into
terminal disposal on the new complete host. -/
theorem single_use_preserves_three_bit_disposal :
    let C := runLocalSchedule ringSix (singleUseFullTransition (by decide) 2 16)
      threeBitWindow [0, 1]
    (∀ i : Fin 3, (C ⟨i.val, by omega⟩).core.core.path = .some i 0) ∧
      (C 2).core.erase.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      DisposalDue (by decide) (C 2).core.erase := by
  unfold DisposalDue
  simp only [← cachedRun_correct]
  decide

def singleUseLifecyclePrefix (t : Nat) : Fin 16 → ExpiringAgentState 2 2 16 :=
  runLocalSchedule BirthFreshEqualArrivalCounterexample.ringSixteen
    (singleUseFullTransition hTwo 2 16) tossInitial (lifecycleWord.take t)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Real generation, comparison and toss still produce the new release.
Its first terminal application leaves depart and consumes its control. -/
theorem single_use_delivers_genuine_release :
    (singleUseLifecyclePrefix 8 6).core.core.path = .some 0 1 ∧
      (singleUseLifecyclePrefix 8 7).core.core.path = .some 1 0 ∧
      (singleUseLifecyclePrefix 14 8).core.core.state = .toss ∧
      (singleUseLifecyclePrefix 15 8).core.core.state = .toss_done ∧
      (singleUseLifecyclePrefix 15 8).core.erase.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      (singleUseLifecyclePrefix 16 9).core.core.path = .some 1 0 ∧
      (singleUseLifecyclePrefix 16 9).core.core.state = .depart ∧
      (singleUseLifecyclePrefix 16 9).core.erase.core.path2 = none ∧
      (singleUseLifecyclePrefix 16 8).core.core.state = .less ∧
      (singleUseLifecyclePrefix 16 8).core.erase.core.path2 = some ⟨0, 0, 0, 6⟩ := by
  unfold singleUseLifecyclePrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The same old repeat-release word now captures its terminal at eleven.
The next outgoing edge cannot pass it onward; when the zero component
expires, the surviving terminal is only three sites ahead. -/
theorem single_use_blocks_thirty_four_step_repeat_release :
    (singleUseLifecyclePrefix 17 10).core.core.path = .some 1 0 ∧
      (singleUseLifecyclePrefix 17 10).core.erase.core.path2 = none ∧
      (singleUseLifecyclePrefix 18 11).core.core.path = .some 1 0 ∧
      (singleUseLifecyclePrefix 18 11).core.core.state = .CHECK_ready ∧
      (singleUseLifecyclePrefix 19 11).core.core.path = .some 1 0 ∧
      (singleUseLifecyclePrefix 19 12).core.core.path = .bot ∧
      (singleUseLifecyclePrefix 20 13).core.core.path = .bot ∧
      (singleUseLifecyclePrefix 34 8).core.core.path = .bot ∧
      (singleUseLifecyclePrefix 34 11).core.core.path = .some 1 0 ∧
      (singleUseLifecyclePrefix 34 11).core.core.state = .CHECK_ready ∧
      (singleUseLifecyclePrefix 34 11).core.erase.core.path2 = none ∧
      ((11 + 16 - 8) % 16 : Nat) ≤ 2 * 2 ∧
      (∀ t : Fin 35, ∀ i : Fin 16,
        (singleUseLifecyclePrefix t.val i).core.core.leader = true ↔ i = 14) := by
  unfold singleUseLifecyclePrefix
  simp only [← cachedRun_correct]
  decide

/-- After releasing the current group, advance both real components into
the next group and schedule its next CHECK. -/
def inspectionWord : DetSchedule 16 := tossWord ++ [8, 9, 8, 10, 9, 10]

def inspectionPrefix (t : Nat) : Fin 16 → ExpiringAgentState 2 2 16 :=
  runLocalSchedule BirthFreshEqualArrivalCounterexample.ringSixteen
    (singleUseFullTransition hTwo 2 16) tossInitial (inspectionWord.take t)

def inspectionAfterProbe (t : Nat) (e : Fin 16) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedPPsiLeaderResetProbeWall hTwo
    (preparedInput hTwo (inspectionPrefix t e).core.erase)
    (preparedInput hTwo
      (inspectionPrefix t (BirthFreshEqualArrivalCounterexample.ringSixteen.rightNeighbor e)).core.erase)

def inspectionBeforeCheck (t : Nat) (e : Fin 16) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  singleUseBeforeCheck hTwo 2
    (preparedInput hTwo (inspectionPrefix t e).core.erase)
    (preparedInput hTwo
      (inspectionPrefix t (BirthFreshEqualArrivalCounterexample.ringSixteen.rightNeighbor e)).core.erase)

def inspectionAfterCheck (t : Nat) (e : Fin 16) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let b := inspectionBeforeCheck t e
  preserveTossCheck hTwo b.1 b.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The whole released signal reaches its next ruler group.  Both
components are freshly ready with the actual zero permission, and CHECK
really reads the next unequal bit and produces the next result. -/
theorem single_use_signal_inspects_next_group :
    (inspectionPrefix 20 10).core.core.path = .some 0 1 ∧
      (inspectionPrefix 20 11).core.core.path = .some 1 0 ∧
      (inspectionPrefix 20 10).core.core.state = .CHECK_ready ∧
      (inspectionPrefix 20 11).core.core.state = .CHECK_ready ∧
      (inspectionPrefix 20 10).core.path0Crossed = true ∧
      (inspectionBeforeCheck 20 10).1.core.state = .CHECK_ready ∧
      (inspectionBeforeCheck 20 10).2.core.state = .CHECK_ready ∧
      (inspectionAfterCheck 20 10).1.core.state = .less ∧
      (inspectionAfterCheck 20 10).1.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
      (inspectionPrefix 21 10).core.core.path = .some 0 1 ∧
      (inspectionPrefix 21 11).core.core.path = .some 1 0 ∧
      (inspectionPrefix 21 10).core.erase.core.path2 = some ⟨0, 0, 0, 6⟩ := by
  unfold inspectionAfterCheck inspectionBeforeCheck inspectionPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- There is one real source batch at eight and no later GENSIG writer.
Following the first release, no responder toss writes a replacement five
before the next group inspection. -/
theorem single_use_next_inspection_has_actual_source :
    (∀ t : Fin 8, ∀ i : Fin 16, (inspectionPrefix t.val i).core.core.path = .bot) ∧
      (let p := inspectionAfterProbe 7 6
       generationWrites hTwo 2 p.1.core p.2.core = (true, true)) ∧
      (∀ k : Fin 13,
        let e := (inspectionWord.drop 8)[k.val]'(by exact k.isLt)
        let p := inspectionAfterProbe (8 + k.val) e
        generationWrites hTwo 2 p.1.core p.2.core = (false, false)) ∧
      (∀ k : Fin 6,
        let e := (inspectionWord.drop 15)[k.val]'(by exact k.isLt)
        (inspectionAfterCheck (15 + k.val) e).2.core.state ≠ .toss) ∧
      (∀ t : Fin 22, ∀ i : Fin 16,
        (inspectionPrefix t.val i).core.core.label = (tossInitial i).core.core.label ∧
          (inspectionPrefix t.val i).core.core.bit = (tossInitial i).core.core.bit ∧
          ((inspectionPrefix t.val i).core.core.leader = true ↔ i = 14)) := by
  unfold inspectionAfterProbe inspectionAfterCheck inspectionBeforeCheck inspectionPrefix
  simp only [← cachedRun_correct]
  decide

#print axioms single_use_preserves_all_four_equal_words
#print axioms single_use_blocks_eighteen_step_escape
#print axioms single_use_blocks_forty_two_step_splice
#print axioms single_use_preserves_three_bit_disposal
#print axioms single_use_delivers_genuine_release
#print axioms single_use_blocks_thirty_four_step_repeat_release
#print axioms single_use_signal_inspects_next_group
#print axioms single_use_next_inspection_has_actual_source

end BirthSingleUseReleaseWitnesses
