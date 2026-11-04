import Leader.Wu.Birth.TossCheckPreservationRepair

set_option autoImplicit false

namespace BirthTossReleaseLifecycleWitnesses

open PPLL PPLLRepair PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair PPLLWallSweepFinite
  BirthFullHostRulerCounterexample BirthFullHostWaitedRulerCounterexample
  BirthCheckCongestGuardRepair BirthCheckParametricWait
  BirthSigMoveDisposalRepair BirthDisposalRouteInvariant
  BirthMismatchDisposalProducer BirthMismatchDisposalWitnesses
  BirthArrivalCaptureRepair BirthArrivalCaptureWitnesses BirthGenerationControlRepair
  BirthTossCheckRearmCounterexample BirthTossCheckPreservationRepair

/-! The toss guard restores the real fresh-comparison release producer.
These complete executions also identify its next, separate lifecycle gap:
the genuinely produced action five keeps releasing later terminal arrivals,
while the zero component is re-read after toss_done.  The old-control reset
cannot remove this newly produced release.  Neither result asserts global
convergence or final paper parameter bounds. -/

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
/-- All four true equal source words retain their complete thirteen-step
WAIT/GEN comparison and unique zero-signal leader. -/
theorem toss_guard_preserves_all_four_equal_words (a b : Bool) :
    let run := fun t => runLocalSchedule ringEight (tossFullTransition hTwo 2 16)
      (familyInitial 16 a b) (equalSchedule.take t)
    (run 8 0).core.core.path = .some 0 (if a then 1 else 0) ∧
      (run 8 1).core.core.path = .some 1 (if b then 1 else 0) ∧
      (∀ i : Fin 8, (run 13 i).core.core.leader = true ↔ i = 2) ∧
      (run 13 2).core.core.signal_B = 0 := by
  cases a <;> cases b <;> simp only [← cachedRun_correct] <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The full-cohort eighteen-step escape remains blocked at every prefix. -/
theorem toss_guard_blocks_eighteen_step_escape :
    ∀ t : Fin 19, ∀ i : Fin 8,
      (runLocalSchedule ringEight (tossFullTransition hTwo 2 16) waitedInitial
        (disposalRegressionWord.take t.val) i).core.core.leader = true ↔ i = 6 := by
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The old partial-expiry forty-two-step splice remains blocked. -/
theorem toss_guard_blocks_forty_two_step_splice :
    ∀ t : Fin 43, ∀ i : Fin 8,
      (runLocalSchedule ringEight (tossFullTransition hTwo 2 16) waitedInitial
        (waitedSchedule.take t.val) i).core.core.leader = true ↔ i = 6 := by
  simp only [← cachedRun_correct]
  decide

/-- The three-component nonterminal mismatch still enters terminal disposal. -/
theorem toss_guard_preserves_three_bit_disposal :
    let C := runLocalSchedule ringSix (tossFullTransition (by decide) 2 16)
      threeBitWindow [0, 1]
    (∀ i : Fin 3, (C ⟨i.val, by omega⟩).core.core.path = .some i 0) ∧
      (C 2).core.erase.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      DisposalDue (by decide) (C 2).core.erase := by
  unfold DisposalDue
  simp only [← cachedRun_correct]
  decide

/-- First restore the fresh-comparison release, then let its terminal move
four more sites and let the zero component expire on its incoming edge. -/
def lifecycleWord : DetSchedule 16 :=
  tossWord ++ [8, 9, 10, 11, 12] ++ List.replicate 14 7

def lifecyclePrefix (t : Nat) : Fin 16 → ExpiringAgentState 2 2 16 :=
  runLocalSchedule BirthFreshEqualArrivalCounterexample.ringSixteen
    (tossFullTransition hTwo 2 16) tossInitial (lifecycleWord.take t)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The repaired host executes both actual fresh source writers and reaches
the same complete target window and its genuine unequal-comparison toss. -/
theorem actual_prefix_reaches_fresh_toss :
    (∀ t : Fin 8, ∀ i : Fin 16, (lifecyclePrefix t.val i).core.core.path = .bot) ∧
      (let p := authorizedPPsiLeaderResetProbeWall hTwo
         (preparedInput hTwo (lifecyclePrefix 7 6).core.erase)
         (preparedInput hTwo (lifecyclePrefix 7 7).core.erase)
       generationWrites hTwo 2 p.1.core p.2.core = (true, true)) ∧
      (lifecyclePrefix 8 6).core.core.path = .some 0 1 ∧
      (lifecyclePrefix 8 7).core.core.path = .some 1 0 ∧
      (lifecyclePrefix 12 8).core.core.path = .some 0 1 ∧
      (lifecyclePrefix 12 9).core.core.path = .some 1 0 ∧
      (lifecyclePrefix 12 8).core.core.state = .CHECK_ready ∧
      (lifecyclePrefix 12 9).core.core.state = .CHECK_ready ∧
      (lifecyclePrefix 12 8).core.path0Crossed = true ∧
      (lifecyclePrefix 14 8).core.core.state = .toss ∧
      (lifecyclePrefix 14 8).core.core.path = .some 0 1 ∧
      (lifecyclePrefix 14 8).core.erase.core.path2 = some ⟨0, 0, 0, 6⟩ := by
  unfold lifecyclePrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The formerly preempted incoming edge now produces toss_done and a new
action five in the full suffix.  The next complete edge releases the real
terminal, although it also re-reads the zero component after toss_done. -/
theorem actual_fresh_comparison_produces_and_delivers_release :
    (lifecyclePrefix 14 8).core.core.state = .toss ∧
      (lifecyclePrefix 14 8).core.erase.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
      (lifecyclePrefix 15 8).core.core.state = .toss_done ∧
      (lifecyclePrefix 15 8).core.core.path = .some 0 1 ∧
      (lifecyclePrefix 15 8).core.erase.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      (lifecyclePrefix 16 9).core.core.path = .some 1 0 ∧
      (lifecyclePrefix 16 9).core.core.state = .depart ∧
      (lifecyclePrefix 16 9).core.erase.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      (lifecyclePrefix 16 8).core.core.state = .less ∧
      (lifecyclePrefix 16 8).core.erase.core.path2 = some ⟨0, 0, 0, 6⟩ := by
  unfold lifecyclePrefix
  simp only [← cachedRun_correct]
  decide

def lifecycleAfterProbe (t : Nat) (e : Fin 16) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedPPsiLeaderResetProbeWall hTwo
    (preparedInput hTwo (lifecyclePrefix t e).core.erase)
    (preparedInput hTwo
      (lifecyclePrefix t (BirthFreshEqualArrivalCounterexample.ringSixteen.rightNeighbor e)).core.erase)

def lifecycleBeforeMovement (t : Nat) (e : Fin 16) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  generationBeforeMove hTwo 2
    (preparedInput hTwo (lifecyclePrefix t e).core.erase)
    (preparedInput hTwo
      (lifecyclePrefix t (BirthFreshEqualArrivalCounterexample.ringSixteen.rightNeighbor e)).core.erase)

def lifecycleAfterCheck (t : Nat) (e : Fin 16) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let b := generationBeforeCheck hTwo 2
    (preparedInput hTwo (lifecyclePrefix t e).core.erase)
    (preparedInput hTwo
      (lifecyclePrefix t (BirthFreshEqualArrivalCounterexample.ringSixteen.rightNeighbor e)).core.erase)
  preserveTossCheck hTwo b.1 b.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- From its first delivery onward, the release has neither a new GENSIG
writer nor another DISAPPEAR toss-completion producer in any call. -/
theorem actual_release_has_no_replacement_producer :
    (∀ k : Fin 26,
      let e := (lifecycleWord.drop 8)[k.val]'(by exact k.isLt)
      let p := lifecycleAfterProbe (8 + k.val) e
      generationWrites hTwo 2 p.1.core p.2.core = (false, false)) ∧
    (∀ k : Fin 19,
      let e := (lifecycleWord.drop 15)[k.val]'(by exact k.isLt)
      let c := lifecycleAfterCheck (15 + k.val) e
      c.1.core.state ≠ .toss ∧ c.2.core.state ≠ .toss) := by
  unfold lifecycleAfterCheck lifecycleAfterProbe lifecyclePrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Four genuine captured-SIGMOVE events transport both the terminal and
the same release command.  Each old receiver is empty with no control. -/
theorem actual_release_moves_with_terminal :
    ∀ k : Fin 4,
      let e : Fin 16 := ⟨9 + k.val, by omega⟩
      let b := lifecycleBeforeMovement (16 + k.val) e
      let q := authorizedCaptureSigMove hTwo b.1 b.2
      b.1.core.path = .some 1 0 ∧ b.2.core.path = .bot ∧
        b.1.core.path2 = some ⟨0, 0, 0, 5⟩ ∧ b.2.core.path2 = none ∧
        q.1.core.path = .bot ∧ q.2.core.path = .some 1 0 ∧
        q.2.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
        (lifecyclePrefix (17 + k.val)
          (BirthFreshEqualArrivalCounterexample.ringSixteen.rightNeighbor e)).core.core.path =
          .some 1 0 := by
  unfold lifecycleBeforeMovement lifecyclePrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- A genuinely generated and genuinely released signal still exceeds two
psi after release: its zero component expires five sites behind its terminal.
Clearing old source controls does not consume this new action five. -/
theorem actual_genuine_release_exceeds_two_psi :
    lifecycleWord.length = 34 ∧
      (lifecyclePrefix 16 8).core.core.path = .some 0 1 ∧
      (lifecyclePrefix 16 8).stall.val = 13 ∧
      (lifecyclePrefix 20 8).core.core.path = .some 0 1 ∧
      (lifecyclePrefix 20 13).core.core.path = .some 1 0 ∧
      (lifecyclePrefix 33 8).core.core.path = .some 0 1 ∧
      (lifecyclePrefix 33 8).stall.val = 0 ∧
      (lifecyclePrefix 34 8).core.core.path = .bot ∧
      (∀ t : Fin 15,
        (lifecyclePrefix (20 + t.val) 13).core.core.path = .some 1 0 ∧
        (lifecyclePrefix (20 + t.val) 13).core.core.state = .depart ∧
        (lifecyclePrefix (20 + t.val) 13).core.erase.core.path2 = some ⟨0, 0, 0, 5⟩) ∧
      ((13 + 16 - 8) % 16 : Nat) > 2 * 2 := by
  unfold lifecyclePrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The entire longer execution retains the correct ruler and unique leader. -/
theorem actual_lifecycle_ruler_fields_preserved :
    ∀ t : Fin 35, ∀ i : Fin 16,
      (lifecyclePrefix t.val i).core.core.label = (tossInitial i).core.core.label ∧
        (lifecyclePrefix t.val i).core.core.bit = (tossInitial i).core.core.bit ∧
        ((lifecyclePrefix t.val i).core.core.leader = true ↔ i = 14) := by
  unfold lifecyclePrefix
  simp only [← cachedRun_correct]
  decide

#print axioms toss_guard_preserves_all_four_equal_words
#print axioms toss_guard_blocks_eighteen_step_escape
#print axioms toss_guard_blocks_forty_two_step_splice
#print axioms toss_guard_preserves_three_bit_disposal
#print axioms actual_prefix_reaches_fresh_toss
#print axioms actual_fresh_comparison_produces_and_delivers_release
#print axioms actual_release_has_no_replacement_producer
#print axioms actual_release_moves_with_terminal
#print axioms actual_genuine_release_exceeds_two_psi
#print axioms actual_lifecycle_ruler_fields_preserved

end BirthTossReleaseLifecycleWitnesses
