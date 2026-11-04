import Leader.Wu.Elimination.TwoLeaderEntrance
import Leader.Wu.Elimination.NearestPeaceful
import Leader.Wu.Elimination.ShortPairMass
import Leader.Wu.Scheduler.FixedSpanRenewalPayload

set_option autoImplicit false

open StateBoundUnifiedCell LDSinkBoundedKernel PPLLRepair LDSinkGapCleanup
open FiniteUniformStoppingTree LabelFreeElimination K2FiniteProgress
open LeaderCountDyadicTail

namespace K2FiniteSafeEliminationCore

variable {n ψ κ : Nat}

/-- The actual separated signal class intersected with the proved nearest
peacefulness and leader-existence class. No progress law is a domain field. -/
def Domain (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : Prop :=
  SignalGlobal ring C ∧ K2PeacefulGlobal.PeacefulGlobal ring C

/-- Closure is on the actual finite-cell step and every original scheduler edge. -/
theorem domain_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (hC : Domain ring C) :
    Domain ring (step hψ ring C e) :=
  ⟨signalGlobal_step hψ ring C hC.1 e,
    K2PeacefulGlobal.peacefulGlobal_step hψ hn ring C hC.2 e⟩

theorem domain_run (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (es : List (Fin n)) :
    Domain ring (run (step hψ ring) C es) :=
  ⟨signalGlobal_run hψ ring C hC.1 es,
    K2PeacefulGlobal.peacefulGlobal_run hψ hn ring C hC.2 es⟩

theorem count_positive (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hC : Domain ring C) : 1 ≤ count C := by
  have h := K2PeacefulGlobal.peacefulGlobal_count_pos ring C hC.2
  omega

/-- Once count one is reached, no later actual edge can produce extinction. -/
theorem count_one_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (hc : count C = 1) (e : Fin n) :
    count (step hψ ring C e) = 1 := by
  have hl := count_positive ring _ (domain_step hψ hn ring C e hC)
  have hu := step_count_nonincrease hψ ring C e
  omega

theorem count_one_run (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (hc : count C = 1) (es : List (Fin n)) :
    count (run (step hψ ring) C es) = 1 := by
  have hl := count_positive ring _ (domain_run hψ hn ring C hC es)
  have hu := run_count_nonincrease hψ ring C es
  omega

private theorem sum_single (e : Fin n) :
    (List.ofFn (fun i : Fin n => if i = e then 1 else 0)).sum = 1 := by
  induction n with
  | zero => exact Fin.elim0 e
  | succ n ih =>
    have hz : ∀ i : Fin n, i.succ ≠ (0 : Fin (n + 1)) := by
      intro i hh
      have hval := congrArg Fin.val hh
      change i.val + 1 = 0 at hval
      omega
    refine Fin.cases ?_ (fun j => ?_) e
    · simp [List.ofFn_succ, hz, FiniteUniformStoppingTree.ofFn_sum_const]
    · rw [List.ofFn_succ, List.sum_cons]
      have hh : (0 : Fin (n + 1)) ≠ j.succ := fun h => hz j h.symm
      simpa [hh] using ih j

/-- Semantic safety includes exactly one current physical output bit. -/
theorem isSafe_count_one (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ)
    (hs : PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring C id) : count C = 1 := by
  obtain ⟨p, hp, hu⟩ := hs.1
  have hp' : (C p).legacy.leader = true := hp
  have hu' : ∀ j, (C j).legacy.leader = true → j = p := hu
  rw [count_eq_sum]
  have he : ∀ i : Fin n, (if (C i).legacy.leader then 1 else 0) =
      (if i = p then 1 else 0) := by
    intro i
    by_cases hi : i = p
    · simp only [hi, hp', ite_true]
    · have hz : (C i).legacy.leader = false := by
        cases h : (C i).legacy.leader
        · rfl
        · exact (hi (hu' i h)).elim
      simp [hi, hz]
  rw [ofFn_sum_eq _ _ he]
  exact sum_single p

/-- On this proved physical domain, count one is exactly semantic safety. -/
theorem isSafe_iff_count_one (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) :
    PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring C id ↔ count C = 1 :=
  ⟨isSafe_count_one hψ ring C,
    K2PeacefulGlobal.count_one_isSafe hψ hn ring C hC.2⟩

/-- Literal semantic failure weight on an actual physical endpoint. -/
noncomputable def safeMiss (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) : Nat := by
  classical
  exact if PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring C id then 0 else 1

theorem safeMiss_eq_countMiss (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) :
    safeMiss hψ ring C = binMiss 1 (count C) := by
  classical
  have hi := isSafe_iff_count_one hψ hn ring C hC
  have hp := count_positive ring C hC
  unfold safeMiss binMiss
  by_cases h : count C = 1
  · simp [hi.mpr h, h]
  · have hs : ¬ PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring C id := fun hs => h (hi.mp hs)
    have hc : ¬ count C ≤ 1 := by omega
    rw [if_neg hs, if_neg hc]

/-- The real finite configuration after each edge; success observes its first
count-one hit. The proof wrapper changes no labels or controller fields. -/
def oneStep (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) : StopNode (Fin n → UCell ψ κ) :=
  let D := step hψ ring C e
  if count D = 1 then .success else .active D

/-- The initial endpoint is tested too, so initially safe states cost zero. -/
def oneStart (C : Fin n → UCell ψ κ) : StopNode (Fin n → UCell ψ κ) :=
  if count C = 1 then .success else .active C

/-- Erase only the original label and control registers, using the existing
modulus-one observation rather than a changed physical label modulus. -/
def observeStop : StopNode (Fin n → UCell ψ κ) → StopNode (Fin n → AgentState 1)
  | .active C => .active (observe C)
  | .success => .success
  | .failure => .failure

/-- Exact same-edge observation of the frozen final-two hitting tree. -/
theorem observe_oneStep (hψ : 0 < ψ) (ring : DirectedRing n)
    (x : StopNode (Fin n → UCell ψ κ)) (e : Fin n) :
    observeStop (stepNode (oneStep hψ ring) x e) =
      stepNode (K2TwoLeaderGeometry.countOneStep (by decide) ring) (observeStop x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active C =>
      have hc : count (step hψ ring C e) =
          K2GlobalGapClosure.physicalLeaderCount (K2OutputSafety.rawStep (by decide) ring (observe C) e) := by
        rw [count_eq_observe, observe_step]
      by_cases h : K2GlobalGapClosure.physicalLeaderCount
          (K2OutputSafety.rawStep (by decide) ring (observe C) e) = 1 <;>
        simp only [stepNode, oneStep, observeStop, K2TwoLeaderGeometry.countOneStep,
          hc, h, ite_true, ite_false, observe_step]

/-- Every stopped node and terminal outcome agrees on the same literal word. -/
theorem observe_stopped_word (hψ : 0 < ψ) (ring : DirectedRing n)
    (x : StopNode (Fin n → UCell ψ κ)) (es : List (Fin n)) :
    observeStop (FixedSpanRenewalPayload.runStopped (oneStep hψ ring) x es) =
      FixedSpanRenewalPayload.runStopped (K2TwoLeaderGeometry.countOneStep (by decide) ring)
        (observeStop x) es := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
      simp only [FixedSpanRenewalPayload.runStopped, ih, observe_oneStep]

private theorem observe_tree (hψ : 0 < ψ) (ring : DirectedRing n)
    (w : StopNode (Fin n → AgentState 1) → Nat)
    (x : StopNode (Fin n → UCell ψ κ)) (T : Nat) :
    treeWeight (oneStep hψ ring) (fun y => w (observeStop y)) x T =
      treeWeight (K2TwoLeaderGeometry.countOneStep (by decide) ring) w (observeStop x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      exact ofFn_sum_eq _ _ (fun e => by rw [ih, observe_oneStep])

theorem observed_successCount (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) :
    successCount (oneStep hψ ring) (.active C) T =
      successCount (K2TwoLeaderGeometry.countOneStep (by decide) ring) (.active (observe C)) T := by
  have hw : (fun y : StopNode (Fin n → UCell ψ κ) => successWeight (observeStop y)) =
      successWeight := by funext y; cases y <;> rfl
  have h := observe_tree hψ ring successWeight (.active C) T
  rwa [hw] at h

/-- Positivity and physical monotonicity justify success padding; if still
active, the retained configuration is exactly the actual successor. -/
theorem oneStart_next (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (e : Fin n) :
    stepNode (oneStep hψ ring) (oneStart C) e = oneStart (step hψ ring C e) := by
  by_cases hc : count C = 1
  · have hd := count_one_step hψ hn ring C hC hc e
    simp only [oneStart, if_pos hc, stepNode, if_pos hd]
  · simp only [oneStart, if_neg hc, stepNode, oneStep]

/-- Exact full-endpoint semantics for every raw word, after any first hit.
The unstopped process continues to execute every suffix interaction. -/
theorem first_hit_full_endpoint (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (es : List (Fin n)) :
    FixedSpanRenewalPayload.runStopped (oneStep hψ ring) (oneStart C) es =
      oneStart (run (step hψ ring) C es) := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
      rw [FixedSpanRenewalPayload.runStopped, oneStart_next hψ hn ring C hC e]
      exact ih _ (domain_step hψ hn ring C e hC)

/-- The stopping-tree numerator equals the actual full-word count-one numerator. -/
theorem successCount_eq_endpoint (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (T : Nat) :
    successCount (oneStep hψ ring) (oneStart C) T =
      wordSum (step hψ ring) (fun D => if count D = 1 then 1 else 0) C T := by
  induction T generalizing C with
  | zero =>
      by_cases h : count C = 1 <;>
        simp [successCount, treeWeight, oneStart, h, successWeight,
          wordSum_zero]
  | succ T ih =>
      change (List.ofFn (fun e => successCount (oneStep hψ ring)
        (stepNode (oneStep hψ ring) (oneStart C) e) T)).sum = _
      rw [wordSum_succ]
      apply ofFn_sum_eq
      intro e
      rw [oneStart_next hψ hn ring C hC e]
      exact ih _ (domain_step hψ hn ring C e hC)

/-- Absolute mass denominator of the frozen physical final-two producer. -/
def finalDenominator : Nat := 16 * 2 ^ K2TwoLeaderEntranceMass.uniformCollapseBudget

theorem final_denominator_pos : 0 < finalDenominator :=
  Nat.mul_pos (by decide) (Nat.two_pow_pos _)

/-- The genuine final-two mass transferred through exact observation and
full endpoint semantics. No divisibility or favorable-entry premise is used. -/
theorem two_leader_endpoint_mass (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (hc : count C = 2) :
    n ^ (20 * n * n) ≤ finalDenominator *
      wordSum (step hψ ring) (fun D => if count D = 1 then 1 else 0) C (20 * n * n) := by
  have hG : K2GlobalGapClosure.GlobalClass (by decide) ring 2 (observe C) :=
    ⟨by decide, (count_eq_observe C).symm.trans hc, hC.1⟩
  have hm := K2TwoLeaderEntrance.globalClass_countOne_mass (by decide) ring (observe C) hG
  rw [← observed_successCount hψ ring C] at hm
  have he := successCount_eq_endpoint hψ hn ring C hC (20 * n * n)
  have hnot : count C ≠ 1 := by omega
  rw [oneStart, if_neg hnot] at he
  rw [he] at hm
  exact hm

/-- This same full physical endpoint supplies the generic strict-drop input. -/
theorem two_leader_drop_mass (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) (hc : count C = 2) :
    n ^ (20 * n * n) ≤ finalDenominator *
      wordSum (step hψ ring) (fun D => if count D < count C then 1 else 0) C (20 * n * n) := by
  have hm := two_leader_endpoint_mass hψ hn ring C hC hc
  apply Nat.le_trans hm
  apply Nat.mul_le_mul_left
  apply wordSum_mono_on (step hψ ring) (Domain ring) (domain_step hψ hn ring)
  · intro D _
    by_cases h : count D = 1
    · simp [h, hc]
    · simp only [if_neg h]
      exact Nat.zero_le _
  · exact hC

end K2FiniteSafeEliminationCore

#print axioms K2FiniteSafeEliminationCore.domain_step
#print axioms K2FiniteSafeEliminationCore.isSafe_iff_count_one
#print axioms K2FiniteSafeEliminationCore.observe_stopped_word
#print axioms K2FiniteSafeEliminationCore.first_hit_full_endpoint
#print axioms K2FiniteSafeEliminationCore.two_leader_endpoint_mass
#print axioms K2FiniteSafeEliminationCore.two_leader_drop_mass
