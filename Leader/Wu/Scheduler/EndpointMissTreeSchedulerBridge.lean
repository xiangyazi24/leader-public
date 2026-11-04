import Leader.Wu.Scheduler.EndpointMissTreeAmplification
import Leader.Wu.Scheduler.ClosedDomainAmplification

/-!
# Scheduler semantics for exact final-miss trees

The generic final-miss tree counts scheduler words whose endpoint fails a
predicate.  For a step-closed predicate, endpoint membership is equivalent to
having reached the predicate at some schedule prefix.  This module identifies
the exact miss tree with the repository's local prefix-miss count, then converts
an exact one-over-`n` endpoint numerator into
`UniformOneOverNFailureAtHorizon`, whose success currency is genuine
`ReachesSafeWithinSchedule`.
-/

namespace PPLLFinalMissTreeSchedulerBridge

open PPLLResearchFormulation PPLLTraceConvergence PPLLSchedulerBlocks
  PPLLFinalMissTreeAmplification
  PPLLClosedDomainSchedulerAmplificationSol

set_option autoImplicit false

/-- Classical Boolean test for an arbitrary configuration predicate. -/
noncomputable def propTest {Q : Type} {n : Nat}
    (Safe : (Fin n → Q) → Prop) (C : Fin n → Q) : Bool :=
  @ite Bool (Safe C) (Classical.propDecidable _) true false

@[simp] theorem propTest_true_iff {Q : Type} {n : Nat}
    (Safe : (Fin n → Q) → Prop) (C : Fin n → Q) :
    propTest Safe C = true ↔ Safe C := by
  classical
  simp [propTest]

private theorem sum_ofFn_eq {n : Nat}
    (f g : Fin n → Nat) (hfg : ∀ i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, hfg 0]
      exact congrArg (g 0 + ·)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

/-- The recursive endpoint-failure tree is the exact finite scheduler count of
words whose final configuration is outside `Safe`. -/
theorem finalMissTree_eq_endpointCount {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Safe : (Fin n → Q) → Prop) (C : Fin n → Q) (t : Nat) :
    finalMissTree ring T Safe C t =
      (allSchedules n t).countP (fun word =>
        !(propTest Safe (runLocalSchedule ring T C word))) := by
  induction t generalizing C with
  | zero =>
      classical
      by_cases hC : Safe C <;>
        simp [finalMissTree, allSchedules, propTest, runLocalSchedule, hC]
  | succ t ih =>
      classical
      rw [finalMissTree]
      rw [show t + 1 = 1 + t by omega, allSchedules_add,
        List.countP_flatMap]
      simp only [allSchedules, List.flatMap_singleton,
        List.map_ofFn]
      apply sum_ofFn_eq
      intro e
      simp only [Function.comp_apply, List.nil_append, List.countP_map]
      rw [ih]
      apply congrArg (fun pred => (allSchedules n t).countP pred)
      funext tail
      simp only [Function.comp_apply]
      rw [runLocalSchedule_append]
      rfl

/-- For a step-closed predicate, endpoint failure and failure to hit the
predicate at any prefix have the same exact scheduler multiplicity. -/
theorem finalMissTree_eq_localMissCount {Q : Type} {n : Nat}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (Safe : (Fin n → Q) → Prop)
    (hclosed : PPLLFinalMissTreeAmplification.LocalStepClosed ring T Safe)
    (C : Fin n → Q) (t : Nat) :
    finalMissTree ring T Safe C t =
      localMissCount ring T (propTest Safe) C t := by
  rw [finalMissTree_eq_endpointCount]
  unfold localMissCount
  apply congrArg (fun pred => (allSchedules n t).countP pred)
  funext word
  have hiff := hitsWithinLocal_iff_closed_endpoint
    ring T Safe (propTest Safe) (propTest_true_iff Safe)
    hclosed C word
  have hbool :
      hitsWithinLocal ring T (propTest Safe) C word = true ↔
        propTest Safe (runLocalSchedule ring T C word) = true :=
    hiff.trans (propTest_true_iff Safe _).symm
  cases hhit : hitsWithinLocal ring T (propTest Safe) C word <;>
    cases hend : propTest Safe (runLocalSchedule ring T C word) <;>
    simp_all

/-- An exact final-miss numerator bounded by `n^(t-1)` yields the repository's
genuine prefix-reaching finite-horizon safety statement. -/
theorem uniformOneOverNFailureAtHorizon_of_finalMissTree_le
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (hn2 : 1 < n) (t : Nat) (ht : 0 < t)
    (hmiss : ∀ C : P.Configuration n,
      n * finalMissTree ring P.transition
        (fun D : P.Configuration n =>
          PopulationProtocol.IsSafe P ring D isLeader) C t ≤
        n ^ t) :
    UniformOneOverNFailureAtHorizon P ring isLeader 1 t := by
  refine ⟨hn2, ht, ?_⟩
  intro C
  have htree := hmiss C
  have htree' :
      finalMissTree ring P.transition
          (fun D : P.Configuration n =>
            PopulationProtocol.IsSafe P ring D isLeader) C t ≤
        n ^ (t - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    change finalMissTree ring P.transition
        (fun D : P.Configuration n =>
          PopulationProtocol.IsSafe P ring D isLeader) C (k + 1) ≤ n ^ k
    rw [Nat.pow_succ] at htree
    exact Nat.le_of_mul_le_mul_left
      (by simpa [Nat.mul_comm] using htree) ring.hn
  have hlocal :
      localMissCount ring P.transition
          (propTest (fun D =>
            PopulationProtocol.IsSafe P ring D isLeader)) C t ≤
        n ^ (t - 1) := by
    rw [← finalMissTree_eq_localMissCount ring P.transition
      (fun D => PopulationProtocol.IsSafe P ring D isLeader)
      (isSafe_localStepClosed P ring isLeader) C t]
    exact htree'
  have hpartition := localMissCount_add_localHitCount
    ring P.transition
    (propTest (fun D =>
      PopulationProtocol.IsSafe P ring D isLeader)) C t
  have hsemantic := localHitCount_le_stabilizingScheduleCount
    P ring isLeader
    (propTest (fun D =>
      PopulationProtocol.IsSafe P ring D isLeader))
    (propTest_true_iff
      (fun D => PopulationProtocol.IsSafe P ring D isLeader)) C t
  change (allSchedules n t).length ≤
    stabilizingScheduleCount P ring isLeader C t + 1 * n ^ (t - 1)
  omega

end PPLLFinalMissTreeSchedulerBridge
