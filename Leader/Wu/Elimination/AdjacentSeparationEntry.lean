import Leader.Wu.Elimination.AdjacentLeaderPeaceful
import Leader.Wu.Elimination.ShortPairMass
import Leader.Wu.Scheduler.FixedSpanRenewalPayload

/-!
# Physical entry to separated leadership

Every nonseparated configuration has an actual adjacent-leader edge. Its
selection lowers the real finite leader count by one; all other physical
edges preserve or lower that count. The resulting service potential is
`n * count`, with no selected target stored across interactions. All stopped
states below contain only the actual configuration and a present-state proof.

The finite costs and masses are identified with the original scheduler words.
Nearest peacefulness is needed only for positive count and semantic safety at
count one. It is not assumed by the separation cost or mass bounds.
-/

namespace AdjacentSeparationEntry

open StateBoundUnifiedCell LDSinkBoundedKernel LabelFreeElimination K2FiniteProgress
  FiniteUniformStoppingTree K2PeacefulGlobal

set_option autoImplicit false

variable {n ψ κ : Nat}

/-- The existing physical spacing predicate, on the exact observation. -/
abbrev Separated (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : Prop :=
  K2GlobalGapClosure.Separated ring (observe C)

private instance separatedDecision (ring : DirectedRing n) (C : Fin n → UCell ψ κ) :
    Decidable (Separated ring C) := by
  unfold Separated K2GlobalGapClosure.Separated
  infer_instance

/-- Follower preservation orders the actual sums of stored leader bits. -/
theorem count_le_of_noNew {C D : Fin n → UCell ψ κ} (h : NoNewLeaders C D) :
    count D ≤ count C := by
  rw [count_eq_sum, count_eq_sum]
  apply ofFn_sum_le
  intro i
  cases hc : (C i).legacy.leader
  · rw [h i hc]
    simp
  · cases (D i).legacy.leader <;> decide

/-- Neither branch of the actual collision protocol creates a leader. -/
theorem step_noNew (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) :
    NoNewLeaders C (AdjacentLeaderElimination.step hψ ring C e) :=
  fun i hi => AdjacentLeaderElimination.step_follower hψ ring C e i hi

/-- Summing the preserved follower bits makes leader count nonincreasing
on every physical row, even before spacing or peacefulness has been reached. -/
theorem step_count_nonincrease (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) :
    count (AdjacentLeaderElimination.step hψ ring C e) ≤ count C :=
  count_le_of_noNew (step_noNew hψ ring C e)

/-- Arbitrary intervening physical words cannot restore either old endpoint. -/
theorem run_noNew (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n)) :
    NoNewLeaders C (run (AdjacentLeaderElimination.step hψ ring) C es) := by
  induction es generalizing C with
  | nil => exact noNew_refl C
  | cons e es ih => exact noNew_trans (step_noNew hψ ring C e) (ih _)

/-- If an old adjacent pair is no longer present, a real old leader has
already been lost. Otherwise its actual edge deletes its current source.
This statement does not presume permanence of a selected target. -/
theorem old_adjacent_service (hψ : 0 < ψ) (ring : DirectedRing n)
    (C D : Fin n → UCell ψ κ) (e : Fin n) (hnew : NoNewLeaders C D)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true) :
    count D < count C ∨ count (AdjacentLeaderElimination.step hψ ring D e) < count C := by
  cases hleft : (D e).legacy.leader
  · exact Or.inl (lost_leader_count_lt hnew e hl hleft)
  · cases hright : (D (ring.rightNeighbor e)).legacy.leader
    · exact Or.inl (lost_leader_count_lt hnew _ hr hright)
    · have hd := AdjacentLeaderElimination.adjacent_count_drop hψ ring D e hleft hright
      rw [← count_eq_observe, ← count_eq_observe] at hd
      have hm := count_le_of_noNew hnew
      exact Or.inr (by omega)

/-- Negating the real spacing predicate produces an actual adjacent edge. -/
theorem adjacent_of_not_separated (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : ¬ Separated ring C) :
    ∃ e, (C e).legacy.leader = true ∧ (C (ring.rightNeighbor e)).legacy.leader = true := by
  apply Classical.byContradiction
  intro hnone
  apply hC
  intro i hi
  cases hr : (C (ring.rightNeighbor i)).legacy.leader
  · exact hr
  · exact False.elim (hnone ⟨i, hi, hr⟩)

/-! ## A stopped service on actual configurations -/

/-- Proof carrier for configurations that have not yet become separated. -/
abbrev Active (ring : DirectedRing n) (ψ κ : Nat) :=
  {C : Fin n → UCell ψ κ // ¬ Separated ring C}

noncomputable section

/-- The initial configuration is terminal exactly when already separated. -/
def start (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : StopNode (Active ring ψ κ) :=
  if h : Separated ring C then .success else .active ⟨C, h⟩

/-- Every child is the actual post-state of the original selected edge. -/
def entryStep (hψ : 0 < ψ) (ring : DirectedRing n)
    (z : Active ring ψ κ) (e : Fin n) : StopNode (Active ring ψ κ) :=
  start ring (AdjacentLeaderElimination.step hψ ring z.val e)

/-- Only unfinished real leader bits contribute to the service work. -/
def work (ring : DirectedRing n) : StopNode (Active ring ψ κ) → Nat
  | .active z => count z.val
  | .success => 0
  | .failure => 0

/-- One unit of real leader count pays for the n equally likely ports.
Terminal configurations have no remaining charge. -/
def potential (ring : DirectedRing n) (x : StopNode (Active ring ψ κ)) : Nat :=
  n * work ring x

private theorem child_work_le (hψ : 0 < ψ) (ring : DirectedRing n)
    (z : Active ring ψ κ) (e : Fin n) :
    work ring (entryStep hψ ring z e) ≤ count (AdjacentLeaderElimination.step hψ ring z.val e) := by
  classical
  unfold entryStep start
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

/-- The chosen adjacent edge pays one unit of count; summing all original
ports, including arbitrary interfering rows, gives the service inequality. -/
theorem entry_bellman (hψ : 0 < ψ) (ring : DirectedRing n) :
    NatBellmanSuperSolution (entryStep (κ := κ) hψ ring) 1 (potential ring) := by
  refine ⟨rfl, rfl, ?_⟩
  intro z
  obtain ⟨e, hl, hr⟩ := adjacent_of_not_separated ring z.val z.property
  have hm : ∀ j, work ring (entryStep hψ ring z j) ≤ count z.val :=
    fun j => Nat.le_trans (child_work_le hψ ring z j)
      (step_count_nonincrease hψ ring z.val j)
  have hd := AdjacentLeaderElimination.adjacent_count_drop hψ ring z.val e hl hr
  rw [← count_eq_observe, ← count_eq_observe] at hd
  have hchild := child_work_le hψ ring z e
  have hrow := LDSinkGapCleanup.ofFn_sum_lt n
    (fun j => work ring (entryStep hψ ring z j)) (count z.val) e hm (by omega)
  change 1 * n + (List.ofFn (fun j => n * work ring (entryStep hψ ring z j))).sum ≤
    n * (n * count z.val)
  rw [Nat.one_mul, ofFn_sum_mul_left]
  have hs := Nat.mul_le_mul_left n hrow
  simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using hs

/-- State-uniform truncated cost from the actual initial configuration. -/
theorem truncated_cost (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) :
    truncatedActiveCostNumerator (entryStep hψ ring) (start ring C) T ≤ n ^ T * (n * n) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (entryStep hψ ring) 1 (potential ring) (entry_bellman hψ ring) (start ring C) T
  have hp : potential ring (start ring C) ≤ n * n := by
    classical
    unfold start
    split
    · exact Nat.zero_le _
    · exact Nat.mul_le_mul_left n (K2GlobalShortPairMass.count_le_ring_size C)
  exact Nat.le_trans (by simpa only [Nat.one_mul] using h) (Nat.mul_le_mul_left _ hp)

/-! ## Exact costs and endpoint masses on the raw scheduler words -/

/-- Charge a physical interaction exactly until the real configuration is
separated. Every recursive successor uses the literal collision protocol. -/
def physicalWordCost (hψ : 0 < ψ) (ring : DirectedRing n) :
    (Fin n → UCell ψ κ) → List (Fin n) → Nat
  | _, [] => 0
  | C, e :: es => if Separated ring C then 0 else
      1 + physicalWordCost hψ ring (AdjacentLeaderElimination.step hψ ring C e) es

/-- Sum the charged prefix length over all n^T original scheduler words;
division by n^T gives the finite-prefix expected physical cost. -/
def physicalCostNumerator (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n T (physicalWordCost hψ ring C)

private theorem wordSum_one_add (T : Nat) (f : List (Fin n) → Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun es => 1 + f es) =
      n ^ T + FixedSpanRenewalPayload.wordSum n T f := by
  rw [← FixedSpanRenewalPayload.rawWord_sum]
  change (List.ofFn (fun i : Fin (n ^ T) => 1 + f (FixedSpanRenewalPayload.rawWord n T i))).sum = _
  rw [ofFn_sum_add, ofFn_sum_const, Nat.mul_one, FixedSpanRenewalPayload.rawWord_sum]

/-- Equality of the stopped-tree cost and the sum over all literal words,
including words that are still unfinished at the selected horizon. -/
theorem physical_cost_eq (hψ : 0 < ψ) (ring : DirectedRing n) (T : Nat)
    (C : Fin n → UCell ψ κ) :
    physicalCostNumerator hψ ring C T =
      truncatedActiveCostNumerator (entryStep hψ ring) (start ring C) T := by
  classical
  induction T generalizing C with
  | zero => rfl
  | succ T ih =>
    unfold physicalCostNumerator
    rw [FixedSpanRenewalPayload.wordSum_succ]
    by_cases hs : Separated ring C
    · simp only [physicalWordCost, if_pos hs, start, dif_pos hs,
        truncatedActiveCostNumerator]
      rw [← FixedSpanRenewalPayload.rawWord_sum]
      simp only [ofFn_sum_const, Nat.mul_zero]
    · simp only [physicalWordCost, if_neg hs]
      have he : ∀ e : Fin n,
          FixedSpanRenewalPayload.wordSum n T (fun es =>
            1 + physicalWordCost hψ ring (AdjacentLeaderElimination.step hψ ring C e) es) =
          n ^ T + truncatedActiveCostNumerator (entryStep hψ ring)
            (start ring (AdjacentLeaderElimination.step hψ ring C e)) T := by
        intro e
        rw [wordSum_one_add]
        exact congrArg (n ^ T + ·) (ih _)
      rw [ofFn_sum_eq _ _ he, ofFn_sum_add, ofFn_sum_const]
      simp only [start, dif_neg hs, truncatedActiveCostNumerator, entryStep]
      rw [Nat.pow_succ]
      ac_rfl

/-- The actual finite-prefix expectation numerator is at most n squared
times the number of scheduler words, for every current configuration. -/
theorem physical_truncated_cost (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) :
    physicalCostNumerator hψ ring C T ≤ n ^ T * (n * n) := by
  rw [physical_cost_eq]
  exact truncated_cost hψ ring C T

/-- Indicator of an actual endpoint still containing adjacent leaders. -/
def miss (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : Nat :=
  if Separated ring C then 0 else 1

/-- Indicator of an actual separated endpoint, on the original carrier. -/
def hit (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : Nat :=
  if Separated ring C then 1 else 0

private theorem miss_mono (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) :
    miss ring (AdjacentLeaderElimination.step hψ ring C e) ≤ miss ring C := by
  classical
  by_cases hs : Separated ring C
  · simp [miss, hs, AdjacentLeaderElimination.separated_step hψ ring C hs e]
  · unfold miss
    rw [if_neg hs]
    split <;> decide

private theorem raw_miss_zero (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hs : Separated ring C) (T : Nat) :
    LeaderCountDyadicTail.wordSum (AdjacentLeaderElimination.step hψ ring) (miss ring) C T = 0 := by
  have h := LeaderCountDyadicTail.wordSum_le_initial
    (AdjacentLeaderElimination.step hψ ring) (miss ring) (miss_mono hψ ring) C T
  classical
  simpa only [miss, if_pos hs, Nat.mul_zero, Nat.le_zero] using h

/-- The active stopped leaves count precisely the original words whose
actual physical endpoint is still nonseparated. Closure justifies padding. -/
theorem active_count_eq_raw (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (T : Nat) :
    activeCount (entryStep hψ ring) (start ring C) T =
      LeaderCountDyadicTail.wordSum (AdjacentLeaderElimination.step hψ ring) (miss ring) C T := by
  classical
  induction T generalizing C with
  | zero => unfold start; split <;> simp_all [activeCount, treeWeight, activeWeight, miss]
  | succ T ih =>
    by_cases hs : Separated ring C
    · rw [raw_miss_zero hψ ring C hs]
      simp only [start, dif_pos hs, activeCount, treeWeight_success, activeWeight, Nat.mul_zero]
    · simp only [start, dif_neg hs, activeCount, treeWeight, stepNode,
        LeaderCountDyadicTail.wordSum_succ, entryStep]
      exact ofFn_sum_eq _ _ (fun e => ih (AdjacentLeaderElimination.step hψ ring C e))

/-- Half of the original words have physically reached separation by 2n². -/
theorem separation_half (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) :
    n ^ (2 * n * n) ≤ 2 * LeaderCountDyadicTail.wordSum
      (AdjacentLeaderElimination.step hψ ring) (hit ring) C (2 * n * n) := by
  have hactive := two_mul_activeCount_le_pow_of_scaled_cost
    (entryStep hψ ring) (start ring C)
    (Nat.mul_pos (Nat.mul_pos (by decide : 0 < (2 : Nat)) ring.hn) ring.hn) (by decide : 0 < 1)
    (num := n * n)
    (by simpa only [Nat.one_mul, Nat.mul_comm] using truncated_cost hψ ring C (2 * n * n))
    (by simp only [Nat.mul_one, Nat.mul_assoc, Nat.le_refl])
  rw [active_count_eq_raw] at hactive
  have he : (fun D : Fin n → UCell ψ κ => hit ring D + miss ring D) = (fun _ => 1) := by
    classical
    funext D
    unfold hit miss
    split <;> rfl
  have hp := LeaderCountDyadicTail.wordSum_add
    (AdjacentLeaderElimination.step hψ ring) (hit ring) (miss ring) C (2 * n * n)
  rw [he, LeaderCountDyadicTail.wordSum_const, Nat.mul_one] at hp
  omega

/-- The same uniform half-tail at every actual adaptive starting state. -/
theorem half_miss (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) :
    2 * LeaderCountDyadicTail.wordSum (AdjacentLeaderElimination.step hψ ring)
      (miss ring) C (2 * n * n) ≤ n ^ (2 * n * n) := by
  have h := two_mul_activeCount_le_pow_of_scaled_cost
    (entryStep hψ ring) (start ring C)
    (Nat.mul_pos (Nat.mul_pos (by decide : 0 < (2 : Nat)) ring.hn) ring.hn) (by decide : 0 < 1)
    (num := n * n)
    (by simpa only [Nat.one_mul, Nat.mul_comm] using truncated_cost hψ ring C (2 * n * n))
    (by simp only [Nat.mul_one, Nat.mul_assoc, Nat.le_refl])
  rwa [active_count_eq_raw] at h

/-- State-uniform amplification along original physical endpoints. There
are no independent episodes or assumed geometric waiting times. -/
theorem separation_tail (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (J : Nat) :
    2 ^ J * LeaderCountDyadicTail.wordSum (AdjacentLeaderElimination.step hψ ring)
      (miss ring) C (J * (2 * n * n)) ≤ n ^ (J * (2 * n * n)) := by
  classical
  have hb : ∀ D : Fin n → UCell ψ κ, True →
      2 * LeaderCountDyadicTail.wordSum (AdjacentLeaderElimination.step hψ ring)
        (miss ring) D (2 * n * n) ≤ 1 * n ^ (2 * n * n) * miss ring D := by
    intro D _
    by_cases hs : Separated ring D
    · rw [raw_miss_zero hψ ring D hs]
      simp only [Nat.mul_zero, Nat.zero_le]
    · simpa only [miss, if_neg hs, Nat.one_mul, Nat.mul_one] using half_miss hψ ring D
  have ht := LeaderCountDyadicTail.iterate_contraction
    (AdjacentLeaderElimination.step hψ ring) (fun _ => True)
    (fun _ _ _ => True.intro) (miss ring) (2 * n * n) 2 1 hb J C True.intro
  have hm : miss ring C ≤ 1 := by unfold miss; split <;> decide
  have hlast := Nat.mul_le_mul_left ((1 * n ^ (2 * n * n)) ^ J) hm
  have he : (1 * n ^ (2 * n * n)) ^ J * 1 = n ^ (J * (2 * n * n)) := by
    rw [Nat.one_mul, Nat.mul_one, ← Nat.pow_mul, Nat.mul_comm (2 * n * n) J]
  rw [he] at hlast
  exact Nat.le_trans ht hlast

/-- The original-clock probability of remaining nonseparated is at most
1/n after 2n²(log2 n + 1) interactions. This is the preceding physical-word
tail specialized to a concrete logarithmic number of blocks. -/
theorem separation_whp (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) :
    let T := (Nat.log2 n + 1) * (2 * n * n)
    n * LeaderCountDyadicTail.wordSum (AdjacentLeaderElimination.step hψ ring)
      (miss ring) C T ≤ n ^ T := by
  have hn : n ≤ 2 ^ (Nat.log2 n + 1) :=
    Nat.le_of_lt ((Nat.log2_lt (Nat.ne_of_gt ring.hn)).1 (by omega))
  exact Nat.le_trans (Nat.mul_le_mul_right _ hn)
    (separation_tail hψ ring C (Nat.log2 n + 1))

/-- Every physical word from the stated current peaceful class retains
positive count; a count-one endpoint is semantically safe for this protocol. -/
theorem peaceful_word_post (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : PeacefulGlobal ring C) (es : List (Fin n)) :
    let D := run (AdjacentLeaderElimination.step hψ ring) C es
    PeacefulGlobal ring D ∧ 0 < count D ∧
      (count D = 1 → PopulationProtocol.IsSafe (AdjacentLeaderElimination.protocol hψ κ) ring D id) := by
  have hd := AdjacentLeaderPeaceful.peacefulGlobal_run hψ hn ring C hC es
  exact ⟨hd, K2PeacefulGlobal.peacefulGlobal_count_pos ring _ hd,
    AdjacentLeaderPeaceful.count_one_isSafe hψ hn ring _ hd⟩

/-- The actual three-adjacent-leader example is initially unfinished and
remains unfinished after its first collision. Its second collision separates
the unique remaining leader and enters semantic output safety. -/
theorem repeated_collision_example :
    let ring := AdjacentLeaderPeaceful.RepeatedCollision.ring5
    let C := AdjacentLeaderPeaceful.RepeatedCollision.seed
    ¬ Separated ring C ∧
      ¬ Separated ring (AdjacentLeaderElimination.step (by decide) ring C 0) ∧
      Separated ring (run (AdjacentLeaderElimination.step (by decide) ring) C [0, 1]) ∧
      PopulationProtocol.IsSafe (AdjacentLeaderElimination.protocol (by decide) 1) ring
        (run (AdjacentLeaderElimination.step (by decide) ring) C [0, 1]) id := by
  refine ⟨by decide, by decide, by decide, AdjacentLeaderPeaceful.RepeatedCollision.after_two_isSafe⟩

end
end AdjacentSeparationEntry

#print axioms AdjacentSeparationEntry.old_adjacent_service
#print axioms AdjacentSeparationEntry.entry_bellman
#print axioms AdjacentSeparationEntry.physical_cost_eq
#print axioms AdjacentSeparationEntry.physical_truncated_cost
#print axioms AdjacentSeparationEntry.active_count_eq_raw
#print axioms AdjacentSeparationEntry.separation_half
#print axioms AdjacentSeparationEntry.separation_tail
#print axioms AdjacentSeparationEntry.separation_whp
#print axioms AdjacentSeparationEntry.peaceful_word_post
#print axioms AdjacentSeparationEntry.repeated_collision_example
