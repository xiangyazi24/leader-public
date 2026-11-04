import Leader.Wu.Birth.GenerationControlWitnesses

set_option autoImplicit false

namespace BirthTossCheckRearmCounterexample

open PPLL PPLLRepair PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLPpsiLeaderCreationRepair PPLLLeaderCreationCleanupRepair
  PPLLNoCheckBirthOutputLegitimacy PPLLWallSweepFinite
  BirthCheckCongestGuardRepair BirthMismatchDisposalProducer
  BirthArrivalCaptureRepair BirthArrivalCaptureWitnesses BirthGenerationControlRepair

/-! A fresh-GEN comparison reaches the intended toss state on the complete
source-reset host.  Its next incoming edge removes the action-six token and
then CHECK rearms the aligned zero component before DISAPPEAR can consume
toss.  The initial configuration is the already checked sixteen-site proper
ruler with its sole leader at fourteen, not an assumed comparison window.

This refutes the specific incoming-edge toss-to-release producer for this
host.  It is not a convergence or final-parameter lower bound. -/

/-- The existing readiness row erases toss on every aligned component. -/
theorem aligned_toss_is_rearmed {psi : Nat} (u : AgentState psi) (label bit : Nat)
    (hp : u.path = .some label bit) (hl : u.label.val = label)
    (hs : u.state = .toss) :
    (checkSigSetReady u).state = .CHECK_ready := by
  simp [checkSigSetReady, hp, hl, hs]

def tossInitial : Fin 16 → ExpiringAgentState 2 2 16 :=
  BirthFreshEqualArrivalCounterexample.initial

/-- This is literally the previously verified proper-ruler input and all
five of its paper safety predicates apply. -/
theorem toss_initial_paperSafe :
    PaperSafeConfig hTwo BirthFreshEqualArrivalCounterexample.ringSixteen
      (eraseExpiringConfig tossInitial) :=
  BirthFreshEqualArrivalCounterexample.initial_paperSafe

def tossWord : DetSchedule 16 := List.replicate 8 6 ++ [7, 6, 8, 7, 8, 8, 7]

def tossPrefix (t : Nat) : Fin 16 → ExpiringAgentState 2 2 16 :=
  runLocalSchedule BirthFreshEqualArrivalCounterexample.ringSixteen
    (generationFullTransition hTwo 2 16) tossInitial (tossWord.take t)

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

def tossAfterProbe (t : Nat) (e : Fin 16) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedPPsiLeaderResetProbeWall hTwo
    (preparedInput hTwo (tossPrefix t e).core.erase)
    (preparedInput hTwo
      (tossPrefix t (BirthFreshEqualArrivalCounterexample.ringSixteen.rightNeighbor e)).core.erase)

def tossBeforeCheck (t : Nat) (e : Fin 16) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  generationBeforeCheck hTwo 2
    (preparedInput hTwo (tossPrefix t e).core.erase)
    (preparedInput hTwo
      (tossPrefix t (BirthFreshEqualArrivalCounterexample.ringSixteen.rightNeighbor e)).core.erase)

def tossAfterCheck (t : Nat) (e : Fin 16) :
    AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  let b := tossBeforeCheck t e
  congestGuardCheck hTwo b.1 b.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Real WAIT terminates and both actual GENSIG writers fire at eight.
The complete source-reset host then captures the two newly generated bits
at the next ruler group, with the true zero-component authorization. -/
theorem actual_fresh_generation_reaches_unequal_group :
    (∀ t : Fin 8, ∀ i : Fin 16, (tossPrefix t.val i).core.core.path = .bot) ∧
      (let p := tossAfterProbe 7 6
       generationWrites hTwo 2 p.1.core p.2.core = (true, true) ∧
         (authorizedGenClean hTwo 2 p.1 p.2).1.core.path = .some 0 1 ∧
         (authorizedGenClean hTwo 2 p.1 p.2).2.core.path = .some 1 0) ∧
      (tossPrefix 8 6).core.core.path = .some 0 1 ∧
      (tossPrefix 8 7).core.core.path = .some 1 0 ∧
      (tossPrefix 12 8).core.core.path = .some 0 1 ∧
      (tossPrefix 12 9).core.core.path = .some 1 0 ∧
      (tossPrefix 12 8).core.core.state = .CHECK_ready ∧
      (tossPrefix 12 9).core.core.state = .CHECK_ready ∧
      (tossPrefix 12 8).core.path0Crossed = true ∧
      (tossPrefix 12 8).core.core.bit = false := by
  unfold tossAfterProbe tossPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The actual CHECK compares source bit one against target bit zero,
creates less and action six, and the following outgoing interaction reaches
toss on the same zero component. -/
theorem actual_unequal_check_produces_toss :
    (tossAfterCheck 12 8).1.core.state = .less ∧
      (tossAfterCheck 12 8).1.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
      (tossPrefix 13 8).core.core.path = .some 0 1 ∧
      (tossPrefix 13 8).core.erase.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
      (tossPrefix 14 8).core.core.state = .toss ∧
      (tossPrefix 14 8).core.core.path = .some 0 1 ∧
      (tossPrefix 14 8).core.erase.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
      (tossPrefix 14 9).core.core.path = .some 1 0 := by
  unfold tossAfterCheck tossBeforeCheck tossPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The next actual incoming edge carries action six away before CHECK.
CHECK then changes toss to ready, so the actual DISAPPEAR producer guard is
false and the complete suffix emits no release at this zero component. -/
theorem actual_incoming_check_preempts_disappear :
    (tossBeforeCheck 14 7).1.core.path = .bot ∧
      (tossBeforeCheck 14 7).1.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
      (tossBeforeCheck 14 7).2.core.path = .some 0 1 ∧
      (tossBeforeCheck 14 7).2.core.state = .toss ∧
      (tossBeforeCheck 14 7).2.core.path2 = none ∧
      (tossAfterCheck 14 7).2.core.state = .CHECK_ready ∧
      (tossAfterCheck 14 7).2.core.path2 = none ∧
      (let c := tossAfterCheck 14 7
       (disappearStartR hTwo c.1.core c.2.core).2.state = .CHECK_ready ∧
         (disappearStartR hTwo c.1.core c.2.core).2.path2 = none) ∧
      (tossPrefix 15 8).core.core.state = .CHECK_ready ∧
      (tossPrefix 15 8).core.core.path = .some 0 1 ∧
      (tossPrefix 15 8).core.erase.core.path2 = none := by
  unfold tossAfterCheck tossBeforeCheck tossPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- All later calls have both genuine source writers disabled.  Thus the
comparison and toss are descendants of the eighth source event, not newly
generated replacements with the same payload value. -/
theorem actual_toss_route_has_no_replacement_generation :
    ∀ k : Fin 7,
      let e := (tossWord.drop 8)[k.val]'(by exact k.isLt)
      let p := tossAfterProbe (8 + k.val) e
      generationWrites hTwo 2 p.1.core p.2.core = (false, false) := by
  unfold tossAfterProbe tossPrefix
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The proper-ruler labels, bits and unique leader persist through every
prefix; no corruption of those fields accounts for the missing release. -/
theorem actual_toss_ruler_fields_preserved :
    ∀ t : Fin 16, ∀ i : Fin 16,
      (tossPrefix t.val i).core.core.label = (tossInitial i).core.core.label ∧
        (tossPrefix t.val i).core.core.bit = (tossInitial i).core.core.bit ∧
        ((tossPrefix t.val i).core.core.leader = true ↔ i = 14) := by
  unfold tossPrefix
  simp only [← cachedRun_correct]
  decide

#print axioms aligned_toss_is_rearmed
#print axioms toss_initial_paperSafe
#print axioms actual_fresh_generation_reaches_unequal_group
#print axioms actual_unequal_check_produces_toss
#print axioms actual_incoming_check_preempts_disappear
#print axioms actual_toss_route_has_no_replacement_generation
#print axioms actual_toss_ruler_fields_preserved

end BirthTossCheckRearmCounterexample
