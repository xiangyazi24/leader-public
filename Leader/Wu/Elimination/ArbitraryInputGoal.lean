import Leader.Wu.Elimination.ArbitraryInputMissAccounting
import Leader.Wu.Elimination.NearestSupportEntry
import Leader.Wu.Elimination.AdjacentSeparationEntry
import Leader.Wu.Elimination.SafeElimination

/-!
# Actual semantic target and physical handoffs

The process is always AdjacentLeaderElimination.step on existing UCell values.
Preparation predicates are proof accounting at physical endpoints. They do
not change the transition, scheduler alphabet, labels, or controller fields.
-/

namespace K2ArbitraryElimination

open PPLL StateBoundUnifiedCell LDSinkBoundedKernel LabelFreeElimination
  K2PeacefulGlobal K2FiniteProgress K2FiniteSafeEliminationCore
  FiniteUniformStoppingTree LeaderCountDyadicTail FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

variable {n ψ κ : Nat}

/-- Semantic safety itself is closed under actual reachability. -/
theorem isSafe_reachable {P : PopulationProtocol} {ring : DirectedRing n}
    {C D : P.Configuration n} (isLeader : P.Y → Bool)
    (hC : P.IsSafe ring C isLeader) (hD : P.Reachable ring C D) :
    P.IsSafe ring D isLeader := by
  have hout := hC.2 D hD
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp, hu⟩ := hC.1
    refine ⟨p, ?_, ?_⟩
    · rw [hout p]; exact hp
    · intro i hi
      apply hu i
      rw [← hout i]
      exact hi
  · intro E hE i
    exact (hC.2 E (hD.trans hE) i).trans (hout i).symm

/-- Conversely to the frozen old-to-collision transfer, semantic safety of
the collision component makes its guard impossible on every old-row path. -/
theorem old_isSafe_of_collision (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ)
    (hC : PopulationProtocol.IsSafe (AdjacentLeaderElimination.protocol hψ κ) ring C id) :
    PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring C id := by
  have hreach : ∀ D, PopulationProtocol.Reachable (LabelFreeElimination.protocol hψ κ) ring C D →
      PopulationProtocol.Reachable (AdjacentLeaderElimination.protocol hψ κ) ring C D := by
    intro D hD
    induction hD with
    | refl => exact .refl _
    | step D E _ hstep ih =>
      have hout := hC.2 D ih
      have hu : hasUniqueLeader n (observe D) := by
        obtain ⟨p, hp, honly⟩ := hC.1
        refine ⟨p, (hout p).trans hp, ?_⟩
        intro i hi
        exact honly i ((hout i).symm.trans hi)
      obtain ⟨e, rfl⟩ := hstep
      exact .step _ _ _ ih ⟨e, (AdjacentLeaderElimination.unique_step_eq_old hψ hn ring D hu e).symm⟩
  exact ⟨hC.1, fun D hD => hC.2 D (hreach D hD)⟩

/-- On nontrivial rings the two semantic safety predicates agree, without
assuming any signal class. Safety forces unique output at all future states. -/
theorem isSafe_iff_old (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) :
    PopulationProtocol.IsSafe (AdjacentLeaderElimination.protocol hψ κ) ring C id ↔
      PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring C id :=
  ⟨old_isSafe_of_collision hψ hn ring C,
    AdjacentLeaderElimination.isSafe_of_old_isSafe hψ hn ring C⟩

/-- Nearest support and actual count one suffice for semantic safety of
both exact components, with no post-invariant supplied as a field. -/
theorem nearest_count_one_safe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hN : NearestPeaceful ring (observe C)) (h1 : count C = 1) :
    PopulationProtocol.IsSafe (AdjacentLeaderElimination.protocol hψ κ) ring C id ∧
      PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring C id := by
  obtain ⟨p, hp, _⟩ := K2PeacefulGlobal.count_one_unique C h1
  have hP : PeacefulGlobal ring C := ⟨⟨p, hp⟩, hN⟩
  exact ⟨AdjacentLeaderPeaceful.count_one_isSafe hψ hn ring C hP h1,
    K2PeacefulGlobal.count_one_isSafe hψ hn ring C hP h1⟩

/-- The permitted physical terminal alternatives. Extinction is retained. -/
def Goal (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : Prop :=
  PopulationProtocol.IsSafe (AdjacentLeaderElimination.protocol hψ κ) ring C id ∨ count C = 0

/-- Zero leaders is closed because every actual row preserves followers. -/
theorem zero_step (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hz : count C = 0) (e : Fin n) : count (AdjacentLeaderElimination.step hψ ring C e) = 0 := by
  have h := AdjacentSeparationEntry.step_count_nonincrease hψ ring C e
  omega

theorem goal_step (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (e : Fin n) (hC : Goal hψ ring C) : Goal hψ ring (AdjacentLeaderElimination.step hψ ring C e) := by
  rcases hC with hs | hz
  · have he : PopulationProtocol.OneStep (AdjacentLeaderElimination.protocol hψ κ) ring C
        (AdjacentLeaderElimination.step hψ ring C e) := ⟨e, rfl⟩
    exact Or.inl (isSafe_reachable id hs he.to_reachable)
  · exact Or.inr (zero_step hψ ring C hz e)

theorem goal_run (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hC : Goal hψ ring C) (es : List (Fin n)) :
    Goal hψ ring (run (AdjacentLeaderElimination.step hψ ring) C es) := by
  induction es generalizing C with
  | nil => exact hC
  | cons e es ih => exact ih _ (goal_step hψ ring C e hC)

/-- After separation, every complete scheduler word agrees physically,
including the entire suffix after any intermediate successful prefix. -/
theorem separated_word_eq (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hs : AdjacentSeparationEntry.Separated ring C) (es : List (Fin n)) :
    run (AdjacentLeaderElimination.step hψ ring) C es =
      run (LabelFreeElimination.step hψ ring) C es :=
  AdjacentLeaderElimination.separated_run_eq_old hψ ring C hs es

/-- Exact same-state agreement lifts to the existing raw finite scheduler sum. -/
theorem separated_wordSum_eq (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hs : AdjacentSeparationEntry.Separated ring C)
    (w : (Fin n → UCell ψ κ) → Nat) (T : Nat) :
    wordSum (AdjacentLeaderElimination.step hψ ring) w C T =
      wordSum (LabelFreeElimination.step hψ ring) w C T := by
  induction T generalizing C with
  | zero => rfl
  | succ T ih =>
    simp only [wordSum_succ]
    apply ofFn_sum_eq
    intro e
    rw [ih _ (AdjacentLeaderElimination.separated_step hψ ring C hs e),
      AdjacentLeaderElimination.separated_step_eq_old hψ ring C hs e]

/-- The post-separation handoff is either zero or the actual separated
nearest-peaceful domain. No future signal order is built into it. -/
def Prepared (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : Prop :=
  count C = 0 ∨ (AdjacentSeparationEntry.Separated ring C ∧ PeacefulGlobal ring C)

theorem entry_separated_prepared (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hE : K2NearestSupportEntry.Entry ring C) (hs : AdjacentSeparationEntry.Separated ring C) :
    Prepared ring C := by
  by_cases hz : count C = 0
  · exact Or.inl hz
  · apply Or.inr
    refine ⟨hs, ?_, ?_⟩
    · by_cases hL : hasLeader n (observe C)
      · exact hL
      · exact False.elim (hz ((K2NearestSupportEntry.count_zero_iff C).2 hL))
    · exact hE.elim id (fun h => False.elim (hz h))

theorem prepared_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (hC : Prepared ring C) :
    Prepared ring (AdjacentLeaderElimination.step hψ ring C e) := by
  rcases hC with hz | ⟨hs, hp⟩
  · exact Or.inl (zero_step hψ ring C hz e)
  · exact Or.inr ⟨AdjacentLeaderElimination.separated_step hψ ring C hs e,
      AdjacentLeaderPeaceful.peacefulGlobal_step hψ hn ring C hp e⟩

/-- Existing safe-elimination domain is closed for the actual collision
component because its real separated condition disables collision. -/
theorem domain_collision_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (hC : Domain ring C) :
    Domain ring (AdjacentLeaderElimination.step hψ ring C e) := by
  rw [AdjacentLeaderElimination.separated_step_eq_old hψ ring C hC.1.separated e]
  exact domain_step hψ hn ring C e hC

/-- The final accounting handoff keeps actual early safety and extinction. -/
def Ready (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : Prop :=
  Goal hψ ring C ∨ Domain ring C

theorem ready_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (hC : Ready hψ ring C) :
    Ready hψ ring (AdjacentLeaderElimination.step hψ ring C e) := by
  exact hC.elim (fun h => Or.inl (goal_step hψ ring C e h))
    (fun h => Or.inr (domain_collision_step hψ hn ring C e h))

/-- Actual semantic miss is bounded by the old semantic miss at the same
configuration. The zero alternative can only reduce the former. -/
theorem goalMiss_le_oldSafeMiss (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) :
    miss (Goal hψ ring) C ≤ K2FiniteSafeEliminationCore.safeMiss hψ ring C := by
  classical
  by_cases hs : PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring C id
  · have hg : Goal hψ ring C := Or.inl ((isSafe_iff_old hψ hn ring C).2 hs)
    simp [miss, safeMiss, hs, hg]
  · simpa only [safeMiss, if_neg hs] using miss_le_one (Goal hψ ring) C

/-- The published safe bound is consumed on the same actual physical words. -/
theorem domain_goal_tail (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Domain ring C) :
    n * wordSum (AdjacentLeaderElimination.step hψ ring) (miss (Goal hψ ring)) C
        (K2FiniteSafeEliminationTail.safeHorizon n) ≤ n ^ K2FiniteSafeEliminationTail.safeHorizon n := by
  rw [separated_wordSum_eq hψ ring C hC.1.separated]
  have h := (K2FiniteSafeElimination.safe_elimination hψ hn ring C hC.1 hC.2).1
  rw [K2FiniteSafeElimination.failureNumerator_eq] at h
  exact Nat.le_trans (Nat.mul_le_mul_left n
    (FiniteAccounting.wordSum_mono (LabelFreeElimination.step hψ ring) _ _
      (goalMiss_le_oldSafeMiss hψ hn ring) C _)) h

/-- Three repetitions reduce the final-domain miss from 1/n to 1/n³.
Physical closure preserves early semantic safety through all suffixes. -/
theorem ready_goal_tail (hψ : 0 < ψ) (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : Ready hψ ring C) :
    n ^ 3 * wordSum (AdjacentLeaderElimination.step hψ ring) (miss (Goal hψ ring)) C
        (3 * K2FiniteSafeEliminationTail.safeHorizon n) ≤
      n ^ (3 * K2FiniteSafeEliminationTail.safeHorizon n) := by
  rcases hC with hg | hd
  · rw [miss_zero _ (Goal hψ ring) (goal_step hψ ring) C hg]
    exact Nat.zero_le _
  · exact repeat_miss _ (Goal hψ ring) (Domain ring)
      (domain_collision_step hψ hn ring) (goal_step hψ ring)
      (K2FiniteSafeEliminationTail.safeHorizon n) n (domain_goal_tail hψ hn ring) C hd 3

end K2ArbitraryElimination

#print axioms K2ArbitraryElimination.isSafe_iff_old
#print axioms K2ArbitraryElimination.nearest_count_one_safe
#print axioms K2ArbitraryElimination.goal_step
#print axioms K2ArbitraryElimination.separated_wordSum_eq
#print axioms K2ArbitraryElimination.ready_goal_tail
