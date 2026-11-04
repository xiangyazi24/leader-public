import Leader.Wu.Birth.MismatchDisposalProducer

set_option autoImplicit false

namespace BirthMismatchDisposalWitnesses

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLNoCheckBirthOutputLegitimacy BirthFullHostRulerCounterexample
  BirthFullHostWaitedRulerCounterexample BirthCheckCongestGuardRepair
  BirthSigMoveDisposalRepair BirthDisposalRouteInvariant
  BirthMismatchDisposalProducer

/-! Concrete whole-present CHECK inputs expose the nonterminal action
corruption in the frozen old host.  The new COMPARE integration is checked
on the same physical inputs and the established complete WAIT/GEN words.
These are executable witnesses for the general producer, not a claim that
arbitrary initial controller contents normalize to this comparison boundary. -/

private theorem threePositive : 3 > 0 := by decide

/-- A bounded ready component with ordinary neutral auxiliary registers.
All parameters are the existing finite carrier's parameters. -/
def readyCell {psi : Nat} (hpsi : psi > 0) (kappa tau : Nat)
    (label : Fin psi) (targetBit : Bool) (payloadBit : Fin 2) (permit : Bool) :
    ExpiringAgentState psi kappa tau :=
  let u := trapFinite (n := psi) hpsi kappa tau label
  ⟨⟨{ u.core.core with
      wait := true
      state := .CHECK_ready
      path := .some label payloadBit
      bit := targetBit }, permit⟩, freshStall tau⟩

/-- A full aligned three-component zero word.  The target differs only at
its middle bit, and the zero component has its physical crossing permit. -/
def threeBitWindow (i : Fin 6) : ExpiringAgentState 3 2 16 :=
  if i.val < 3 then
    readyCell threePositive 2 16 ⟨i.val % 3, by omega⟩ (i = 1) 0 (i = 0)
  else trapFinite threePositive 2 16 i

theorem ringSix : DirectedRing 6 := ⟨by omega⟩

def threeBitPrefix (t : Nat) : Fin 6 → ExpiringAgentState 3 2 16 :=
  runLocalSchedule ringSix (actionOneFullTransition threePositive 2 16)
    threeBitWindow ([0, 1].take t)

/-- The old complete finite interaction reverses the fresh CHECK-larger
command at a nonterminal site.  The new host retains its clockwise action
and the exact path, on the same whole-present physical input. -/
theorem actual_nonterminal_larger_command_repaired :
    (∀ i : Fin 3, (threeBitWindow ⟨i.val, by omega⟩).core.core.path = .some i 0) ∧
      (actualCheckOutput threePositive 2 (threeBitWindow 0).core.erase
        (threeBitWindow 1).core.erase).2.core.state = .larger ∧
      (actualCheckOutput threePositive 2 (threeBitWindow 0).core.erase
        (threeBitWindow 1).core.erase).2.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      (disposalFullTransition threePositive 2 16 (threeBitWindow 0)
        (threeBitWindow 1)).2.core.erase.core.path2 = some ⟨0, 0, 0, 3⟩ ∧
      (actionOneFullTransition threePositive 2 16 (threeBitWindow 0)
        (threeBitWindow 1)).2.core.erase.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      (threeBitPrefix 1 1).core.erase.core.path = .some 1 0 := by
  decide

/-- The larger command then reaches the actual terminal in the next full
interaction.  All three original components remain present, and the
terminal satisfies the general deletion-entry predicate. -/
theorem actual_nonterminal_larger_reaches_disposal :
    (∀ i : Fin 3, (threeBitPrefix 2 ⟨i.val, by omega⟩).core.core.path = .some i 0) ∧
      pendingTerminalDisposal threePositive (threeBitPrefix 2 2).core.erase.core = true ∧
      DisposalDue threePositive (threeBitPrefix 2 2).core.erase := by
  unfold DisposalDue
  decide

/-- A ready terminal mismatch after an equal one-component prefix.  The
core input is independent of the physical timer budget. -/
def terminalLeft (tau : Nat) : ExpiringAgentState 3 2 tau :=
  let u := readyCell threePositive 2 tau 1 false 0 false
  { u with core := { u.core with core := { u.core.core with state := .equal } } }

def terminalRight (tau : Nat) : ExpiringAgentState 3 2 tau :=
  readyCell threePositive 2 tau 2 true 0 false

private theorem terminalLeft_core (tau : Nat) :
    (terminalLeft tau).core.erase = (terminalLeft 16).core.erase := rfl

private theorem terminalRight_core (tau : Nat) :
    (terminalRight tau).core.erase = (terminalRight 16).core.erase := rfl

/-- The general producer has an actual full-input family for every positive
timer bound.  Its conclusion is obtained from the general CHECK/suffix
theorem, with only the current boundary conditions reduced here. -/
theorem terminal_mismatch_produces_disposal_family (tau : Nat) (htau : 0 < tau) :
    DisposalDue threePositive
      (actionOneFullTransition threePositive 2 tau (terminalLeft tau)
        (terminalRight tau)).2.core.erase := by
  apply actual_ready_terminal_larger_produces_disposal threePositive 2 tau
  case hpositive => exact htau
  case hrterminal =>
    simp only [terminalLeft_core tau, terminalRight_core tau]
    change (actualCheckInput threePositive 2 (terminalLeft 16).core.erase
      (terminalRight 16).core.erase).2.core.label = (2 : Fin 3)
    decide
  all_goals
    simp only [terminalLeft_core tau, terminalRight_core tau]
    decide

private theorem get_ofFn {Q : Type} (C : Fin 8 → Q) :
    (Vector.ofFn C).get = C := by
  funext i
  simp [Vector.get]
  apply congrArg C
  apply Fin.ext
  rfl

private def cachedRun {Q : Type} (T : Q → Q → Q × Q) :
    DetSchedule 8 → Vector Q 8 → Vector Q 8
  | [], C => C
  | e :: rest, C => cachedRun T rest (Vector.ofFn (localStep ringEight T C.get e))

private theorem cachedRun_correct {Q : Type} (T : Q → Q → Q × Q)
    (C : Fin 8 → Q) (word : DetSchedule 8) :
    (cachedRun T word (Vector.ofFn C)).get = runLocalSchedule ringEight T C word := by
  induction word generalizing C with
  | nil => exact get_ofFn C
  | cons e rest ih =>
      simp only [cachedRun, get_ofFn, runLocalSchedule]
      exact ih _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The new opcode guard still permits the full thirteen-interaction
WAIT/GEN/transport/equal-CHECK execution and its unique zero-signal leader. -/
theorem actionOne_preserves_thirteen_step_birth :
    let C := runLocalSchedule ringEight (actionOneFullTransition (by omega) 2 16)
      equalInitial equalSchedule
    (∀ i : Fin 8, (C i).core.core.leader = true ↔ i = 2) ∧
      (C 2).core.core.label = 0 ∧ (C 2).core.core.signal_B = 0 := by
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Every prefix of the original eighteen-interaction complete-cohort
escape witness retains exactly the original leader under the new host. -/
theorem actionOne_blocks_eighteen_step_birth :
    ∀ t : Fin 19, ∀ i : Fin 8,
      (runLocalSchedule ringEight (actionOneFullTransition (by omega) 2 16)
        waitedInitial (disposalRegressionWord.take t.val) i).core.core.leader = true ↔ i = 6 := by
  simp only [← cachedRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The earlier forty-two-interaction partial-expiry splice regression also
remains blocked, at every prefix, after the COMPARE-slot substitution. -/
theorem actionOne_blocks_forty_two_step_birth :
    ∀ t : Fin 43, ∀ i : Fin 8,
      (runLocalSchedule ringEight (actionOneFullTransition (by omega) 2 16)
        waitedInitial (waitedSchedule.take t.val) i).core.core.leader = true ↔ i = 6 := by
  simp only [← cachedRun_correct]
  decide

end BirthMismatchDisposalWitnesses

#print axioms BirthMismatchDisposalWitnesses.actual_nonterminal_larger_command_repaired
#print axioms BirthMismatchDisposalWitnesses.actual_nonterminal_larger_reaches_disposal
#print axioms BirthMismatchDisposalWitnesses.terminal_mismatch_produces_disposal_family
#print axioms BirthMismatchDisposalWitnesses.actionOne_preserves_thirteen_step_birth
#print axioms BirthMismatchDisposalWitnesses.actionOne_blocks_eighteen_step_birth
#print axioms BirthMismatchDisposalWitnesses.actionOne_blocks_forty_two_step_birth
