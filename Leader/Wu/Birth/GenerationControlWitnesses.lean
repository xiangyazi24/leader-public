import Leader.Wu.Birth.GenerationControlRepair

set_option autoImplicit false

namespace BirthGenerationControlWitnesses

open PPLL PPLLRepair PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLAuthorizedComparisonRepair PPLLLeaderCreationCleanupRepair PPLLWallSweepFinite
  BirthFullHostRulerCounterexample BirthFullHostWaitedRulerCounterexample
  BirthCheckCongestGuardRepair BirthCheckParametricWait
  BirthSigMoveDisposalRepair BirthDisposalRouteInvariant
  BirthMismatchDisposalProducer BirthMismatchDisposalWitnesses
  BirthArrivalCaptureRepair BirthArrivalCaptureWitnesses BirthGenerationControlRepair

/-! Full-host executions for the two source-control resets.  They retain
genuine equal comparisons, unequal disposal and later DISAPPEAR release,
while excluding the source-residue execution on the same finite host. -/

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
/-- Each two-bit word still has its real WAIT/GEN comparison and unique
leader after thirteen interactions under the source-reset host. -/
theorem generation_all_four_equal_words (a b : Bool) :
    let run := fun t => runLocalSchedule ringEight (generationFullTransition hTwo 2 16)
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
      (run 13 2).core.core.signal_B = 0 := by
  cases a <;> cases b <;> simp only [← cachedRun_correct] <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The full-cohort eighteen-step escape remains blocked at every prefix. -/
theorem generation_blocks_eighteen_step_escape :
    ∀ t : Fin 19, ∀ i : Fin 8,
      (runLocalSchedule ringEight (generationFullTransition hTwo 2 16) waitedInitial
        (disposalRegressionWord.take t.val) i).core.core.leader = true ↔ i = 6 := by
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The partial-expiry forty-two-step splice remains blocked throughout. -/
theorem generation_blocks_forty_two_step_splice :
    ∀ t : Fin 43, ∀ i : Fin 8,
      (runLocalSchedule ringEight (generationFullTransition hTwo 2 16) waitedInitial
        (waitedSchedule.take t.val) i).core.core.leader = true ↔ i = 6 := by
  simp only [← cachedRun_correct]
  decide

/-- A real nonterminal unequal CHECK still produces and propagates action
four on the complete three-component window. -/
theorem generation_preserves_three_bit_disposal :
    let C := runLocalSchedule ringSix (generationFullTransition (by decide) 2 16)
      threeBitWindow [0, 1]
    (∀ i : Fin 3, (C ⟨i.val, by omega⟩).core.core.path = .some i 0) ∧
      (C 2).core.erase.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      DisposalDue (by decide) (C 2).core.erase := by
  unfold DisposalDue
  simp only [← cachedRun_correct]
  decide

def rootedGenerationPrefix (t : Nat) : Fin 16 → ExpiringAgentState 2 2 16 :=
  runLocalSchedule BirthFreshEqualArrivalCounterexample.ringSixteen
    (generationFullTransition hTwo 2 16) BirthFreshEqualArrivalCounterexample.initial
    (rootedWord.take t)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The proper-ruler fresh signal still undergoes its first unequal bit
inspection, terminal disposal entry and complete deletion service. -/
theorem generation_rooted_mismatch_inspects_and_retires :
    (rootedGenerationPrefix 11 7).core.core.state = .CHECK_ready ∧
      (rootedGenerationPrefix 12 6).core.core.state = .CHECK_ready ∧
      (rootedGenerationPrefix 12 7).core.core.state = .CHECK_ready ∧
      (rootedGenerationPrefix 13 6).core.erase.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      DisposalDue hTwo (rootedGenerationPrefix 14 7).core.erase ∧
      (rootedGenerationPrefix 16 6).core.core.path = .bot ∧
      (rootedGenerationPrefix 16 7).core.core.path = .bot ∧
      (∀ t : Fin 17, ∀ i : Fin 16,
        (rootedGenerationPrefix t.val i).core.core.leader = true ↔ i = 14) := by
  unfold DisposalDue rootedGenerationPrefix
  simp only [← cachedRun_correct]
  decide

/-- Each old opcode can reside at either source endpoint before generation;
bounded action indices zero through five encode the six raw opcodes. -/
def taintedSourceInitial (site : Fin 2) (action : Fin 6) (i : Fin 8) :
    ExpiringAgentState 2 2 16 :=
  let u := familyInitial 16 false false i
  if i.val = site.val then
    { u with core := { u.core with core :=
        { u.core.core with path2 := some ⟨0, 0, 0, action⟩ } } }
  else u

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Both GENSIG writer positions discard all six old opcodes.  Their new
terminal is captured at its first matching site and cannot bypass it on the
next outgoing edge.  The twelve initial cases are actual complete runs. -/
theorem generation_clears_all_source_opcodes :
    ∀ site : Fin 2, ∀ action : Fin 6,
      let run := fun t => runLocalSchedule ringEight (generationFullTransition hTwo 2 16)
        (taintedSourceInitial site action)
        (BirthSourceActionFiveCounterexample.schedule.take t)
      (run 8 0).core.core.path = .some 0 0 ∧
        (run 8 1).core.core.path = .some 1 0 ∧
        (run 8 0).core.erase.core.path2 = none ∧
        (run 8 1).core.erase.core.path2 = none ∧
        (run 10 3).core.core.path = .some 1 0 ∧
        (run 10 3).core.core.state = .CHECK_ready ∧
        (run 11 3).core.core.path = .some 1 0 ∧
        (run 11 4).core.core.path = .bot := by
  simp only [← cachedRun_correct]
  decide

/-- A toss input with a terminal payload at physical label zero.  Its
control is initially empty; the subsequent release is created by the real
DISAPPEAR stage rather than assumed as an input token. -/
def releaseInitial (i : Fin 8) : ExpiringAgentState 2 2 16 :=
  let u := familyInitial 16 false false i
  if i = 0 then
    { u with core := { u.core with core := { u.core.core with
      state := .toss
      path := .some 1 0 } } }
  else u

def releasePrefix (t : Nat) : Fin 8 → ExpiringAgentState 2 2 16 :=
  runLocalSchedule ringEight (generationFullTransition hTwo 2 16)
    releaseInitial (([7, 0] : DetSchedule 8).take t)

/-- The full suffix produces a new release token from toss.  The next
complete interaction transports it with the payload and leaves the terminal
in depart, so source reset does not remove the actual release mechanism. -/
theorem generation_retains_actual_disappear_release :
    (releasePrefix 0 0).core.erase.core.path2 = none ∧
      (releasePrefix 1 0).core.core.state = .toss_done ∧
      (releasePrefix 1 0).core.core.path = .some 1 0 ∧
      (releasePrefix 1 0).core.erase.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      (releasePrefix 2 0).core.core.path = .bot ∧
      (releasePrefix 2 1).core.core.path = .some 1 0 ∧
      (releasePrefix 2 1).core.core.state = .depart ∧
      (releasePrefix 2 1).core.erase.core.path2 = some ⟨0, 0, 0, 5⟩ := by
  unfold releasePrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The release in the preceding complete run is assigned by the actual
DISAPPEAR toss-completion row, with no old token at its CHECK input.  Neither
of the two complete interactions executes a replacement GENSIG writer. -/
theorem release_has_actual_producer_and_no_generation :
    (let b := generationBeforeCheck hTwo 2
        (preparedInput hTwo (releasePrefix 0 7).core.erase)
        (preparedInput hTwo (releasePrefix 0 0).core.erase)
     let c := congestGuardCheck hTwo b.1 b.2
     c.2.core.state = .toss ∧ c.2.core.label = 0 ∧ c.2.core.path2 = none ∧
       (disappearStartR hTwo c.1.core c.2.core).2.path2 = some ⟨0, 0, 0, 5⟩) ∧
      (∀ k : Fin 2,
        let e : Fin 8 := if k = 0 then 7 else 0
        let p := authorizedPPsiLeaderResetProbeWall hTwo
          (preparedInput hTwo (releasePrefix k.val e).core.erase)
          (preparedInput hTwo (releasePrefix k.val (ringEight.rightNeighbor e)).core.erase)
        generationWrites hTwo 2 p.1.core p.2.core = (false, false)) := by
  unfold releasePrefix
  simp only [← cachedRun_correct]
  decide

#print axioms generation_all_four_equal_words
#print axioms generation_blocks_eighteen_step_escape
#print axioms generation_blocks_forty_two_step_splice
#print axioms generation_preserves_three_bit_disposal
#print axioms generation_rooted_mismatch_inspects_and_retires
#print axioms generation_clears_all_source_opcodes
#print axioms generation_retains_actual_disappear_release
#print axioms release_has_actual_producer_and_no_generation

end BirthGenerationControlWitnesses
