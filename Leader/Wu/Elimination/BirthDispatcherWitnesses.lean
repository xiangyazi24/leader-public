import Leader.Wu.Elimination.BirthDispatcherObserver

/-! Executable regressions of the complete mixed row. The positive birth
starts from the established clean, leaderless, WAIT=true physical family;
the other examples test deletion priorities and the final physical tail. -/

namespace K2BirthDispatcher
namespace Witnesses

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLAuthorizedComparisonRepair
  BirthFullHostRulerCounterexample BirthCheckCongestGuardRepair
  BirthCheckParametricWait BirthSingleUseReleaseRepair
  BirthTossCheckPreservationRepair BirthSigMoveDisposalRepair
  LDSinkBoundedKernel ExpiringK2Projection

set_option autoImplicit false
set_option pp.structureInstances false

private theorem get_ofFn {n : Nat} {Q : Type} (C : Fin n → Q) :
    (Vector.ofFn C).get = C := by
  funext i
  simp [Vector.get]
  apply congrArg C
  apply Fin.ext
  rfl

/-- A finite-vector evaluator of this actual same-edge mixed step. -/
private def cachedRun {n ψ κ τ : Nat} (hψ : 0 < ψ) (ring : DirectedRing n) :
    List (Fin n) → Vector (ExpiringAgentState ψ κ τ) n → Vector (ExpiringAgentState ψ κ τ) n
  | [], C => C
  | e :: es, C => cachedRun hψ ring es (Vector.ofFn (K2BirthDispatcher.step hψ ring C.get e))

private theorem cachedRun_correct {n ψ κ τ : Nat} (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n)) :
    (cachedRun hψ ring es (Vector.ofFn C)).get = run (K2BirthDispatcher.step hψ ring) C es := by
  induction es generalizing C with
  | nil => exact get_ofFn C
  | cons e es ih =>
    simp only [cachedRun, get_ofFn, run]
    exact ih _

def positiveRun (t : Nat) : Fin 8 → ExpiringAgentState 2 2 16 :=
  run (K2BirthDispatcher.step (by decide) ringEight) (familyInitial 16 false false)
    (equalSchedule.take t)

/-- This uses the actual initial WAIT counter and two GEN payloads. There
are no input leaders, comparison paths, stale permissions or ready seeds. -/
theorem positive_initial_clean :
    ∀ i : Fin 8,
      (positiveRun 0 i).core.core.leader = false ∧
      (positiveRun 0 i).core.core.wait = true ∧
      (positiveRun 0 i).core.core.count = 0 ∧
      (positiveRun 0 i).core.core.path = .bot ∧
      (positiveRun 0 i).core.path0Crossed = false ∧
      (positiveRun 0 i).core.core.state = .none ∧
      (positiveRun 0 i).stall.val = 16 := familyInitial_clean 16 false false

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 16384 in
theorem positive_gen_eight :
    (positiveRun 8 0).core.core.path = .some 0 0 ∧
    (positiveRun 8 1).core.core.path = .some 1 0 ∧
    (∀ i : Fin 8, (positiveRun 8 i).core.core.leader = false) := by
  simp only [positiveRun, ← cachedRun_correct]
  decide

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 16384 in
/-- The stationary writer keeps the new leader at its actual CHECK site 3.
K2 immediately transfers its initialized live bullet to site 2, so the final
leader is shielded with B=0,S=0, not with the literal initialization B=2. -/
theorem positive_birth_thirteen :
    (∀ i : Fin 8, (positiveRun 13 i).core.core.leader = true ↔ i = 3) ∧
    (positiveRun 13 3).core.core.shield = true ∧
    (positiveRun 13 3).core.core.bullet = 0 ∧
    (positiveRun 13 3).core.core.signal_B = 0 ∧
    (positiveRun 13 2).core.core.bullet = 2 ∧
    (positiveRun 13 2).core.core.signal_B = 0 := by
  simp only [positiveRun, ← cachedRun_correct]
  decide

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 16384 in
theorem positive_last_event :
    birthEvent (by decide) (positiveRun 12 2) (positiveRun 12 3) = true := by
  simp only [positiveRun, ← cachedRun_correct]
  decide

def positiveLastLeft := normalizeDeletion
  (prepareExpiringDisposal (by decide) (positiveRun 12 2)).core.erase

def positiveLastRight := normalizeDeletion
  (prepareExpiringDisposal (by decide) (positiveRun 12 3)).core.erase

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 16384 in
/-- The decisive stage is the real guarded CHECK on the actual prefix.
This is not a forged terminal-ready input used as an entry producer. -/
theorem positive_last_check :
    let b := singleUseBeforeCheck (by decide) 2 positiveLastLeft positiveLastRight
    deletionActive positiveLastLeft = false ∧ deletionActive positiveLastRight = false ∧
      b.2.core.leader = false ∧
      (preserveTossCheck (by decide) b.1 b.2).2.core.leader = true := by
  simp only [positiveLastLeft, positiveLastRight, positiveRun, ← cachedRun_correct]
  decide

/-- Incoming terminal action 3 is made effective before any transport.
All other stale non-K2 fields of this physical leader remain present. -/
def disposalLeft : ExpiringAgentState 2 2 3 :=
  let u := Example.staleSeed 0
  { u with core := { u.core with core := { u.core.core with path2 := some ⟨0, 0, 0, 3⟩ } } }

def disposalRight : ExpiringAgentState 2 2 3 := Example.hostRight

theorem disposal_left_priority :
    pendingTerminalDisposal (by decide) disposalLeft.core.core.erase = true ∧
    deletionActive (normalizeDeletion (prepareExpiringDisposal (by decide) disposalLeft).core.erase) = true ∧
    deletionActive (normalizeDeletion (prepareExpiringDisposal (by decide) disposalRight).core.erase) = false ∧
    birthEvent (by decide) disposalLeft disposalRight = false ∧
    (K2BirthDispatcher.row (by decide) disposalLeft disposalRight).1.core.core.path = .some 1 1 ∧
    (K2BirthDispatcher.row (by decide) disposalLeft disposalRight).1.core.core.state = .eliminate_signal ∧
    (K2BirthDispatcher.row (by decide) disposalLeft disposalRight).1.core.path0Crossed = false ∧
    (K2BirthDispatcher.row (by decide) disposalLeft disposalRight).1.stall = 3 ∧
    (K2BirthDispatcher.row (by decide) disposalLeft disposalRight).2.stall = 2 ∧
    (K2BirthDispatcher.row (by decide) disposalLeft disposalRight).2.core.core.bullet = 0 ∧
    (K2BirthDispatcher.row (by decide) disposalLeft disposalRight).2.core.core.signal_B = 1 := by
  decide

/-- Same priority row, with the old stored comparison, WAIT, writer and
probe controls still visible after K2. Only the actual disposal permit is consumed. -/
theorem disposal_stale_controls_retained :
    let q := (K2BirthDispatcher.row (by decide) disposalLeft disposalRight).1
    q.core.core.path2 = disposalLeft.core.core.path2 ∧
    q.core.core.path3 = disposalLeft.core.core.path3 ∧
    q.core.core.path4 = disposalLeft.core.core.path4 ∧
    q.core.core.path5 = disposalLeft.core.core.path5 ∧
    q.core.core.wait = true ∧ q.core.core.count = 2 ∧
    q.core.core.probe = true ∧ q.core.core.phase = true ∧
    q.core.core.write = .increment_group ∧ q.core.core.p_carry = true := by
  decide

def responderDisposal : ExpiringAgentState 2 2 3 :=
  let u := Example.hostRight
  { u with core := { u.core with core := { u.core.core with
    path := .some 1 1, path2 := some ⟨0, 0, 0, 3⟩ } } }

/-- Actual responder disposal deletes its carrier and still reaches K2's
protected-live absorption in this very raw interaction. -/
theorem disposal_responder_priority :
    deletionActive (normalizeDeletion
      (prepareExpiringDisposal (by decide) responderDisposal).core.erase) = true ∧
    birthEvent (by decide) Example.hostLeft responderDisposal = false ∧
    (K2BirthDispatcher.row (by decide) Example.hostLeft responderDisposal).2.core.core.path = .bot ∧
    (K2BirthDispatcher.row (by decide) Example.hostLeft responderDisposal).2.core.core.state = .none ∧
    (K2BirthDispatcher.row (by decide) Example.hostLeft responderDisposal).2.core.core.bullet = 0 ∧
    (K2BirthDispatcher.row (by decide) Example.hostLeft responderDisposal).2.stall = 3 := by
  decide

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 16384 in
/-- The clean protected-live difference persists in the complete candidate.
This checks that old Algorithm 15 was not substituted for the final K2 row. -/
theorem protected_live_complete_difference :
    (singleUseFullTransition (by decide) 2 3 Example.hostLeft Example.hostRight).2.core.core.bullet = 2 ∧
    (K2BirthDispatcher.row (by decide) Example.hostLeft Example.hostRight).2.core.core.bullet = 0 := by
  decide

def collisionRight : ExpiringAgentState 2 2 3 :=
  let u := Example.hostRight
  { u with core := { u.core with core := { u.core.core with leader := true, signal_B := 1 } } }

/-- The complete collision branch retains the incoming live bullet and
clears both S fields; it does not accidentally execute FIRE first. -/
theorem collision_complete :
    (K2BirthDispatcher.row (by decide) disposalLeft collisionRight).1.core.core.leader = false ∧
    (K2BirthDispatcher.row (by decide) disposalLeft collisionRight).2.core.core.leader = true ∧
    (K2BirthDispatcher.row (by decide) disposalLeft collisionRight).1.core.core.bullet = disposalLeft.core.core.bullet ∧
    (K2BirthDispatcher.row (by decide) disposalLeft collisionRight).2.core.core.bullet = 2 ∧
    (K2BirthDispatcher.row (by decide) disposalLeft collisionRight).2.core.core.shield = true ∧
    (K2BirthDispatcher.row (by decide) disposalLeft collisionRight).1.core.core.signal_B = 0 ∧
    (K2BirthDispatcher.row (by decide) disposalLeft collisionRight).2.core.core.signal_B = 0 := by
  decide

#print axioms positive_gen_eight
#print axioms positive_birth_thirteen
#print axioms positive_last_check
#print axioms disposal_left_priority
#print axioms disposal_responder_priority
#print axioms protected_live_complete_difference
#print axioms collision_complete

end Witnesses
end K2BirthDispatcher
