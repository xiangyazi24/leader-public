import Leader.Wu.Elimination.BirthDispatcherWitnesses
import Leader.Wu.Elimination.BirthDispatcherLeaderNormalize

namespace K2BirthLeaderNormalizeWriterAudit

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

private def cachedRun {n ψ κ τ : Nat} (hψ : 0 < ψ) (ring : DirectedRing n) :
    List (Fin n) → Vector (ExpiringAgentState ψ κ τ) n →
      Vector (ExpiringAgentState ψ κ τ) n
  | [], C => C
  | e :: es, C =>
      cachedRun hψ ring es
        (Vector.ofFn (K2BirthDispatcher.step hψ ring C.get e))

private theorem cachedRun_correct {n ψ κ τ : Nat} (hψ : 0 < ψ)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (es : List (Fin n)) :
    (cachedRun hψ ring es (Vector.ofFn C)).get =
      run (K2BirthDispatcher.step hψ ring) C es := by
  induction es generalizing C with
  | nil => exact get_ofFn C
  | cons e es ih =>
    simp only [cachedRun, get_ofFn, run]
    exact ih _

def C12 : Fin 8 → ExpiringAgentState 2 2 16 :=
  (cachedRun (by decide : 0 < 2) ringEight
    (equalSchedule.take 12) (Vector.ofFn (familyInitial 16 false false))).get

theorem C12_eq_source :
    C12 = K2BirthDispatcher.Witnesses.positiveRun 12 := by
  simpa only [C12, K2BirthDispatcher.Witnesses.positiveRun] using
    cachedRun_correct (by decide : 0 < 2) ringEight
      (familyInitial 16 false false) (equalSchedule.take 12)

def l12 : AuthorizedAgentState 2 :=
  normalizeDeletion
    (prepareExpiringDisposal (by decide : 0 < 2) (C12 2)).core.erase

def r12 : AuthorizedAgentState 2 :=
  normalizeDeletion
    (prepareExpiringDisposal (by decide : 0 < 2) (C12 3)).core.erase

def c12 : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  K2BirthDispatcher.throughCheck (by decide : 0 < 2) 2 l12 r12

def w12 : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  K2BirthDispatcher.beforeWrite (by decide : 0 < 2) c12.1 c12.2

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem actual_writer_input_obstruction :
    K2BirthLeaderNormalize.LeadersZero (by decide : 0 < 2) C12 ∧
    deletionActive l12 = false ∧
    deletionActive r12 = false ∧
    c12.2.core.leader = true ∧
    c12.2.core.label = (1 : Fin 2) ∧
    w12.2.core.leader = true ∧
    w12.2.core.label = (1 : Fin 2) ∧
    w12.2.core.label ≠ (0 : Fin 2) := by
  unfold K2BirthLeaderNormalize.LeadersZero
  decide

end K2BirthLeaderNormalizeWriterAudit

#print axioms K2BirthLeaderNormalizeWriterAudit.C12_eq_source
#print axioms K2BirthLeaderNormalizeWriterAudit.actual_writer_input_obstruction
