import Leader.Wu.ShortGap.CyclicIncidenceChoice
import Leader.Core.PredictableTwoTargetFiniteTree
import Leader.Core.BalancedFailureRestart

/-!
# Uniform-scheduler stopping certificates for short-gap choice

The primary certificate stops one bare-incidence round at its first persistent
`10` candidate or candidate-free uniform word.  A local good/bad physical-edge
injection lifts through the complete finite scheduler tree: from the all-Race
entry, the round costs at most `n*m` in normalized truncated expectation and
has candidate mass at least `1/4` by horizon `2*n*m`.

The older oriented-retry certificates remain as quotient-level comparison
lemmas.  They are state-uniform in the selected logical retry edge and permit
adjacent logical roots on adjacent physical cells, but a positive-length gap
cannot perform that logical retry in one radius-one interaction.  The direct
round certificate avoids that atomicity.  Neither route proves that arbitrary
literal dispatcher rows expose the bare incidence actions or implement the
stop-and-wait declaration/rearm carrier.
-/

namespace ShortGapChoiceStopping

set_option autoImplicit false

open FiniteUniformStoppingTree
open PeriodHIncidenceChoice
open PredictableTwoTargetFiniteTree

/-! ## Initial incidence drain -/

/-- An active bare-incidence state retains the witness needed to choose a
strictly decreasing Race port. -/
structure RaceDrainState (m : Nat) where
  configuration : Configuration m
  hasRace : HasRace configuration

/-- Stop exactly when the last unresolved incidence root disappears. -/
noncomputable def raceDrainStep {n m : Nat} (P : Placement n m)
    (state : RaceDrainState m) (edge : Fin n) :
    StopNode (RaceDrainState m) := by
  classical
  let next := incidenceStep P state.configuration edge
  exact if h : HasRace next then .active ⟨next, h⟩ else .success

private def raceDrainPotential {m : Nat} (n : Nat) :
    StopNode (RaceDrainState m) → Nat
  | .active state => n * choiceRaceReserve state.configuration
  | .success => 0
  | .failure => 0

private theorem choiceRaceReserve_eq_zero_of_not_hasRace
    {m : Nat} (C : Configuration m) (h : ¬ HasRace C) :
    choiceRaceReserve C = 0 := by
  unfold choiceRaceReserve
  calc
    (List.ofFn (fun i : Fin m => if C i = .race then 1 else 0)).sum =
        (List.ofFn (fun _ : Fin m => 0)).sum := by
          apply ofFn_sum_eq
          intro i
          have hi : C i ≠ .race := by
            intro hirace
            exact h ⟨i, hirace⟩
          simp [hi]
    _ = 0 := by rw [ofFn_sum_const]; simp

/-- A Race witness makes the unresolved-root reserve positive. -/
theorem choiceRaceReserve_pos_of_hasRace
    {n m : Nat} (P : Placement n m) (C : Configuration m)
    (h : HasRace C) : 0 < choiceRaceReserve C := by
  obtain ⟨i, hi⟩ := h
  have hdrop := choiceRaceReserve_incidenceStep_outgoing_lt P C i hi
  omega

/-- No configuration has more unresolved roots than logical root sites. -/
theorem choiceRaceReserve_le {m : Nat} (C : Configuration m) :
    choiceRaceReserve C ≤ m := by
  unfold choiceRaceReserve
  calc
    (List.ofFn (fun i : Fin m => if C i = .race then 1 else 0)).sum ≤
        (List.ofFn (fun _ : Fin m => 1)).sum := by
          apply ofFn_sum_le
          intro i
          split <;> simp
    _ = m := by rw [ofFn_sum_const]; simp

/-- The cyclic short-gap entry configuration before any incidence choice. -/
def allRaceConfiguration (m : Nat) : Configuration m := fun _ => .race

@[simp] theorem choiceRaceReserve_allRace (m : Nat) :
    choiceRaceReserve (allRaceConfiguration m) = m := by
  unfold choiceRaceReserve allRaceConfiguration
  simp only [ite_true]
  rw [ofFn_sum_const]
  simp

theorem allRaceConfiguration_hasRace {m : Nat} (hm : 0 < m) :
    HasRace (allRaceConfiguration m) := by
  exact ⟨⟨0, hm⟩, rfl⟩

/-- The two resolved constant words admitted by the retry interface. -/
def UniformFrozenBase {m : Nat} (C : Configuration m) : Prop :=
  (∀ i, C i = .in0) ∨ (∀ i, C i = .out1)

theorem not_hasRace_iff_frozen {m : Nat} (C : Configuration m) :
    ¬ HasRace C ↔ Frozen C := by
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · intro h ⟨i, hi⟩
    exact h i hi

/-- A completely resolved cyclic incidence word either already contains a
capture candidate or is one of the two uniform bases eligible for retry. -/
theorem frozen_candidate_or_uniform
    {m : Nat} (ring : DirectedRing m) (C : Configuration m)
    (h : Frozen C) :
    (∃ edge, Candidate10 ring C edge) ∨ UniformFrozenBase C := by
  classical
  by_cases hcandidate : ∃ edge, Candidate10 ring C edge
  · exact Or.inl hcandidate
  · right
    obtain ⟨value, hvalue⟩ := frozen_noCandidate_constant ring C h
      (fun edge hedge => hcandidate ⟨edge, hedge⟩)
    cases value with
    | race =>
        let i : Fin m := ⟨0, ring.hn⟩
        exact False.elim (h i (hvalue i))
    | in0 => exact Or.inl hvalue
    | out1 => exact Or.inr hvalue

/-- Starting with every logical root unresolved, one bare incidence edge
cannot finish in a candidate-free frozen word.  If its frozen result were
uniform, two distinct logical roots would have to occupy the same physical
port. -/
theorem allRace_incidence_frozen_hasCandidate
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (C : Configuration m)
    (hallRace : ∀ i, C i = .race) (edge : Fin n)
    (hfrozen : Frozen (incidenceStep P C edge)) :
    ∃ candidate, Candidate10 ring (incidenceStep P C edge) candidate := by
  rcases frozen_candidate_or_uniform ring _ hfrozen with hcandidate | huniform
  · exact hcandidate
  · let i : Fin m := ⟨0, ring.hn⟩
    let j := ring.rightNeighbor i
    have hji : j ≠ i := by
      simpa [j] using rightNeighbor_ne ring hm i
    rcases huniform with hin0 | hout1
    · have hrootI : P.root i = P.physicalRing.rightNeighbor edge := by
        have hi := hin0 i
        grind [incidenceStep, hallRace i]
      have hrootJ : P.root j = P.physicalRing.rightNeighbor edge := by
        have hj := hin0 j
        grind [incidenceStep, hallRace j]
      exact (hji (P.root_injective (hrootJ.trans hrootI.symm))).elim
    · have hrootI : P.root i = edge := by
        have hi := hout1 i
        grind [incidenceStep, hallRace i]
      have hrootJ : P.root j = edge := by
        have hj := hout1 j
        grind [incidenceStep, hallRace j]
      exact (hji (P.root_injective (hrootJ.trans hrootI.symm))).elim

/-- The stopped quotient classifies success by the actual post-interaction
absence of Race roots, not by a fixed service counter. -/
theorem raceDrainStep_eq_success_iff
    {n m : Nat} (P : Placement n m) (state : RaceDrainState m)
    (edge : Fin n) :
    raceDrainStep P state edge = .success ↔
      ¬ HasRace (incidenceStep P state.configuration edge) := by
  classical
  simp [raceDrainStep]

theorem raceDrainStep_eq_success_iff_frozen
    {n m : Nat} (P : Placement n m) (state : RaceDrainState m)
    (edge : Fin n) :
    raceDrainStep P state edge = .success ↔
      Frozen (incidenceStep P state.configuration edge) := by
  rw [raceDrainStep_eq_success_iff, not_hasRace_iff_frozen]

private theorem raceDrainPotential_step
    {n m : Nat} (P : Placement n m) (state : RaceDrainState m)
    (edge : Fin n) :
    raceDrainPotential n (raceDrainStep P state edge) =
      n * choiceRaceReserve
        (incidenceStep P state.configuration edge) := by
  classical
  simp only [raceDrainStep]
  split
  next => rfl
  next h =>
    rw [choiceRaceReserve_eq_zero_of_not_hasRace _ h]
    rfl

/-- The physical-ring-scaled Race reserve pays one complete raw scheduler
interaction at every active state.  Shared incident edges may resolve two
roots, so the estimate does not assume independent logical choices. -/
theorem raceDrain_natBellmanSuperSolution
    {n m : Nat} (P : Placement n m) :
    NatBellmanSuperSolution (raceDrainStep P) 1
      (raceDrainPotential n) := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  have hscaled := Nat.mul_le_mul_left n
    (choiceRaceReserve_incidence_childSum
      P state.configuration state.hasRace)
  have hchildren :
      (List.ofFn (fun edge : Fin n =>
        raceDrainPotential n (raceDrainStep P state edge))).sum =
        n * (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve
            (incidenceStep P state.configuration edge))).sum := by
    calc
      (List.ofFn (fun edge : Fin n =>
          raceDrainPotential n (raceDrainStep P state edge))).sum =
          (List.ofFn (fun edge : Fin n =>
            n * choiceRaceReserve
              (incidenceStep P state.configuration edge))).sum := by
            apply ofFn_sum_eq
            intro edge
            exact raceDrainPotential_step P state edge
      _ = n * (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve
            (incidenceStep P state.configuration edge))).sum :=
        ofFn_sum_mul_left n _
  rw [hchildren]
  simpa [raceDrainPotential, Nat.mul_add, Nat.mul_assoc] using hscaled

/-- Exact finite-horizon expected-work certificate for initial choice
resolution.  Its normalized truncated cost is at most `n` times the initial
number of Race roots. -/
theorem raceDrain_truncatedCost_le
    {n m : Nat} (P : Placement n m) (C : Configuration m)
    (h : HasRace C) (T : Nat) :
    truncatedActiveCostNumerator (raceDrainStep P)
        (.active ⟨C, h⟩) T ≤
      n ^ T * (n * choiceRaceReserve C) := by
  simpa [raceDrainPotential] using
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (raceDrainStep P) 1 (raceDrainPotential n)
      (raceDrain_natBellmanSuperSolution P) (.active ⟨C, h⟩) T

/-- Bare incidence has no failure outcome. -/
theorem raceDrain_failureCount_eq_zero
    {n m : Nat} (P : Placement n m) : ∀ state T,
    failureCount (raceDrainStep P) (.active state) T = 0 := by
  classical
  intro state T
  induction T generalizing state with
  | zero => rfl
  | succ T ih =>
      simp only [failureCount, treeWeight, stepNode]
      calc
        (List.ofFn (fun edge : Fin n => treeWeight
            (raceDrainStep P) failureWeight
            (raceDrainStep P state edge) T)).sum =
            (List.ofFn (fun _ : Fin n => 0)).sum := by
              apply ofFn_sum_eq
              intro edge
              simp only [raceDrainStep]
              split
              next hnext =>
                simpa [failureCount] using ih ⟨_, hnext⟩
              next => simp [treeWeight_success, failureWeight]
        _ = 0 := by rw [ofFn_sum_const]; simp

/-- By horizon `2*n*r`, where `r` is the initial Race reserve, at least half
of all scheduler words have completely frozen the incidence word. -/
theorem raceDrain_success_half_by_two_mul
    {n m : Nat} (P : Placement n m) (C : Configuration m)
    (h : HasRace C) :
    n ^ (2 * n * choiceRaceReserve C) ≤
      2 * successCount (raceDrainStep P) (.active ⟨C, h⟩)
        (2 * n * choiceRaceReserve C) := by
  let r := choiceRaceReserve C
  let T := 2 * n * r
  let start : RaceDrainState m := ⟨C, h⟩
  have hn : 0 < n := P.physicalRing.hn
  have hr : 0 < r := choiceRaceReserve_pos_of_hasRace P C h
  have hcost := raceDrain_truncatedCost_le P C h T
  have hactive :
      2 * activeCount (raceDrainStep P) (.active start) T ≤ n ^ T := by
    apply two_mul_activeCount_le_pow_of_scaled_cost
        (raceDrainStep P) (.active start) (L := T)
        (den := 1) (num := n * r)
    · dsimp [T]
      exact Nat.mul_pos (Nat.mul_pos (by decide) hn) hr
    · omega
    · simpa [start, r, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using hcost
    · dsimp [T]
      simp [Nat.mul_assoc]
  have hpartition := node_count_partition
    (raceDrainStep P) (.active start) T
  have hfailure := raceDrain_failureCount_eq_zero P start T
  rw [hfailure] at hpartition
  have hresult :
      n ^ T ≤
        2 * successCount (raceDrainStep P) (.active start) T := by
    omega
  simpa [T, start, r] using hresult

/-- On the actual all-short cyclic entry word, initial incidence resolution
has truncated expected cost at most `n*m`. -/
theorem allRace_truncatedCost_le
    {n m : Nat} (P : Placement n m) (hm : 0 < m) (T : Nat) :
    truncatedActiveCostNumerator (raceDrainStep P)
        (.active
          ⟨allRaceConfiguration m, allRaceConfiguration_hasRace hm⟩) T ≤
      n ^ T * (n * m) := by
  simpa using raceDrain_truncatedCost_le P (allRaceConfiguration m)
    (allRaceConfiguration_hasRace hm) T

/-- Consequently at least half of all length-`2*n*m` scheduler words have
resolved every initial all-short cyclic choice. -/
theorem allRace_success_half_by_two_mul
    {n m : Nat} (P : Placement n m) (hm : 0 < m) :
    n ^ (2 * n * m) ≤
      2 * successCount (raceDrainStep P)
        (.active
          ⟨allRaceConfiguration m, allRaceConfiguration_hasRace hm⟩)
        (2 * n * m) := by
  simpa using raceDrain_success_half_by_two_mul P (allRaceConfiguration m)
    (allRaceConfiguration_hasRace hm)

/-! ## Candidate-classifying incidence drain -/

/-- An active round has at least one unresolved root and has not yet created a
persistent oriented candidate. -/
structure CandidateDrainState {m : Nat} (ring : DirectedRing m) where
  configuration : Configuration m
  hasRace : HasRace configuration
  noCandidate : ∀ i, ¬ Candidate10 ring configuration i

/-- Stop a bare-incidence round at its first persistent candidate (success) or
at complete candidate-free resolution (failure). -/
noncomputable def candidateDrainStep
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (state : CandidateDrainState ring) (edge : Fin n) :
    StopNode (CandidateDrainState ring) := by
  classical
  let next := incidenceStep P state.configuration edge
  exact if hcandidate : ∃ i, Candidate10 ring next i then .success
    else if hrace : HasRace next then
      .active ⟨next, hrace, fun i hi => hcandidate ⟨i, hi⟩⟩
    else .failure

theorem candidateDrainStep_eq_success_iff
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (state : CandidateDrainState ring) (edge : Fin n) :
    candidateDrainStep ring P state edge = .success ↔
      CreatesCandidate ring P state.configuration edge := by
  classical
  by_cases hcandidate : ∃ i, Candidate10 ring
      (incidenceStep P state.configuration edge) i
  · simp [candidateDrainStep, CreatesCandidate, hcandidate]
  · constructor
    · intro hstep
      by_cases hrace : HasRace
          (incidenceStep P state.configuration edge)
      · simp [candidateDrainStep, hcandidate, hrace] at hstep
      · simp [candidateDrainStep, hcandidate, hrace] at hstep
    · intro hcreates
      exact (hcandidate hcreates).elim

theorem candidateDrainStep_eq_failure_iff
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (state : CandidateDrainState ring) (edge : Fin n) :
    candidateDrainStep ring P state edge = .failure ↔
      (∀ i, ¬ Candidate10 ring
        (incidenceStep P state.configuration edge) i) ∧
      Frozen (incidenceStep P state.configuration edge) := by
  classical
  rw [← not_hasRace_iff_frozen]
  by_cases hcandidate : ∃ i, Candidate10 ring
      (incidenceStep P state.configuration edge) i
  · constructor
    · intro hstep
      simp [candidateDrainStep, hcandidate] at hstep
    · intro hright
      obtain ⟨i, hi⟩ := hcandidate
      exact (hright.1 i hi).elim
  · by_cases hrace : HasRace
        (incidenceStep P state.configuration edge)
    · simp [candidateDrainStep, hcandidate, hrace]
    · have hnoCandidate : ∀ i, ¬ Candidate10 ring
          (incidenceStep P state.configuration edge) i := by
          intro i hi
          exact hcandidate ⟨i, hi⟩
      simp [candidateDrainStep, hrace, hnoCandidate]

def candidateDrainPotential {n m : Nat}
    (ring : DirectedRing m) : StopNode (CandidateDrainState ring) → Nat
  | .active state => n * choiceRaceReserve state.configuration
  | .success => 0
  | .failure => 0

/-- Every failed round ends in one of the two uniform frozen words. -/
theorem candidateDrain_failure_uniform
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (state : CandidateDrainState ring) (edge : Fin n)
    (hfailure : candidateDrainStep ring P state edge = .failure) :
    UniformFrozenBase
      (incidenceStep P state.configuration edge) := by
  have hterminal :=
    (candidateDrainStep_eq_failure_iff ring P state edge).mp hfailure
  rcases frozen_candidate_or_uniform ring _ hterminal.2 with
      hcandidate | huniform
  · obtain ⟨candidate, hcandidate⟩ := hcandidate
    exact (hterminal.1 candidate hcandidate).elim
  · exact huniform

/-- A previously resolved root fixes the value of every failed round. -/
theorem candidateDrain_failure_restores_fixed
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (state : CandidateDrainState ring) (b : FrozenValue)
    (fixed : Fin m)
    (hfixed : state.configuration fixed = b.toChoice)
    (edge : Fin n)
    (hfailure : candidateDrainStep ring P state edge = .failure) :
    RestoresBase b P state.configuration edge := by
  have hfixedNonRace : state.configuration fixed ≠ .race := by
    cases b <;> simp [hfixed, FrozenValue.toChoice]
  have hpreserved :
      incidenceStep P state.configuration edge fixed =
        state.configuration fixed := by
    simp [incidenceStep, hfixedNonRace]
  have huniform := candidateDrain_failure_uniform
    ring P state edge hfailure
  cases b with
  | in0 =>
      rcases huniform with hin0 | hout1
      · simpa [RestoresBase, FrozenValue.toChoice] using hin0
      · have hcontra := hout1 fixed
        rw [hpreserved, hfixed] at hcontra
        exact Choice.noConfusion hcontra
  | out1 =>
      rcases huniform with hin0 | hout1
      · have hcontra := hin0 fixed
        rw [hpreserved, hfixed] at hcontra
        exact Choice.noConfusion hcontra
      · simpa [RestoresBase, FrozenValue.toChoice] using hout1

private theorem candidateDrain_baseOrRace_of_failure
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (state : CandidateDrainState ring) (b : FrozenValue)
    (fixed : Fin m)
    (hfixed : state.configuration fixed = b.toChoice)
    (edge : Fin n)
    (hfailure : candidateDrainStep ring P state edge = .failure) :
    BaseOrRace b state.configuration := by
  have hrestore := candidateDrain_failure_restores_fixed
    ring P state b fixed hfixed edge hfailure
  intro i
  by_cases hi : state.configuration i = .race
  · exact Or.inl hi
  · right
    have hpreserved :
        incidenceStep P state.configuration edge i =
          state.configuration i := by
      simp [incidenceStep, hi]
    exact hpreserved.symm.trans (hrestore i)

private theorem candidateDrain_successSum_eq_goodEdgeCount
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (state : CandidateDrainState ring) :
    (List.ofFn (fun edge : Fin n =>
      successWeight (candidateDrainStep ring P state edge))).sum =
        goodEdgeCount ring P state.configuration := by
  classical
  unfold goodEdgeCount
  apply ofFn_sum_eq
  intro edge
  by_cases hgood : CreatesCandidate ring P state.configuration edge
  · have hsuccess :=
      (candidateDrainStep_eq_success_iff ring P state edge).mpr hgood
    simp [successWeight, hsuccess, goodEdge, hgood]
  · have hnotSuccess : candidateDrainStep ring P state edge ≠ .success :=
      fun h => hgood
        ((candidateDrainStep_eq_success_iff ring P state edge).mp h)
    cases hstep : candidateDrainStep ring P state edge <;>
      simp_all [successWeight, goodEdge]

private theorem candidateDrain_failureSum_eq_zero_of_noFailure
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (state : CandidateDrainState ring)
    (hnoFailure : ∀ edge, candidateDrainStep ring P state edge ≠ .failure) :
    (List.ofFn (fun edge : Fin n =>
      failureWeight (candidateDrainStep ring P state edge))).sum = 0 := by
  calc
    (List.ofFn (fun edge : Fin n =>
        failureWeight (candidateDrainStep ring P state edge))).sum =
        (List.ofFn (fun _ : Fin n => 0)).sum := by
          apply ofFn_sum_eq
          intro edge
          cases hstep : candidateDrainStep ring P state edge <;>
            simp_all [failureWeight]
    _ = 0 := by rw [ofFn_sum_const]; simp

private theorem candidateDrain_localBalance_of_fixed
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n)
    (state : CandidateDrainState ring) (b : FrozenValue)
    (fixed : Fin m)
    (hfixed : state.configuration fixed = b.toChoice)
    (failedEdge : Fin n)
    (hfailed : candidateDrainStep ring P state failedEdge = .failure) :
    (List.ofFn (fun edge : Fin n =>
      failureWeight (candidateDrainStep ring P state edge))).sum ≤
        (List.ofFn (fun edge : Fin n =>
          successWeight (candidateDrainStep ring P state edge))).sum := by
  classical
  have hbase := candidateDrain_baseOrRace_of_failure
    ring P state b fixed hfixed failedEdge hfailed
  calc
    (List.ofFn (fun edge : Fin n =>
        failureWeight (candidateDrainStep ring P state edge))).sum ≤
        badEdgeCount b P state.configuration := by
          unfold badEdgeCount
          apply ofFn_sum_le
          intro edge
          cases hstep : candidateDrainStep ring P state edge with
          | active child => simp [failureWeight]
          | success => simp [failureWeight]
          | failure =>
              have hrestore := candidateDrain_failure_restores_fixed
                ring P state b fixed hfixed edge hstep
              simp [failureWeight, badEdge, hrestore]
    _ ≤ goodEdgeCount ring P state.configuration :=
      goodEdgeCount_ge_badEdgeCount ring hm P hn b state.configuration
        hbase state.hasRace
    _ = (List.ofFn (fun edge : Fin n =>
        successWeight (candidateDrainStep ring P state edge))).sum :=
      (candidateDrain_successSum_eq_goodEdgeCount ring P state).symm

/-- At every active candidate-free incidence state, immediate uniform failure
mass is no larger than immediate candidate-creation mass.  Mixed states use a
resolved root to pin the only possible uniform base; an all-Race state cannot
freeze without creating a candidate. -/
theorem candidateDrain_localBalance
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n)
    (state : CandidateDrainState ring) :
    (List.ofFn (fun edge : Fin n =>
      failureWeight (candidateDrainStep ring P state edge))).sum ≤
        (List.ofFn (fun edge : Fin n =>
          successWeight (candidateDrainStep ring P state edge))).sum := by
  classical
  by_cases hnonRace : HasNonRace state.configuration
  · obtain ⟨fixed, hfixed⟩ := hnonRace
    by_cases hfailure : ∃ edge,
        candidateDrainStep ring P state edge = .failure
    · obtain ⟨failedEdge, hfailed⟩ := hfailure
      cases hvalue : state.configuration fixed with
      | race => exact (hfixed hvalue).elim
      | in0 =>
          exact candidateDrain_localBalance_of_fixed ring hm P hn state
            .in0 fixed (by simpa [FrozenValue.toChoice] using hvalue)
            failedEdge hfailed
      | out1 =>
          exact candidateDrain_localBalance_of_fixed ring hm P hn state
            .out1 fixed (by simpa [FrozenValue.toChoice] using hvalue)
            failedEdge hfailed
    · rw [candidateDrain_failureSum_eq_zero_of_noFailure ring P state
          (fun edge h => hfailure ⟨edge, h⟩)]
      exact Nat.zero_le _
  · have hallRace : ∀ i, state.configuration i = .race := by
      intro i
      cases hvalue : state.configuration i with
      | race => rfl
      | in0 =>
          exact (hnonRace ⟨i, by simp [hvalue]⟩).elim
      | out1 =>
          exact (hnonRace ⟨i, by simp [hvalue]⟩).elim
    have hnoFailure : ∀ edge,
        candidateDrainStep ring P state edge ≠ .failure := by
      intro edge hfailure
      have hterminal :=
        (candidateDrainStep_eq_failure_iff ring P state edge).mp hfailure
      obtain ⟨candidate, hcandidate⟩ :=
        allRace_incidence_frozen_hasCandidate ring hm P
          state.configuration hallRace edge hterminal.2
      exact hterminal.1 candidate hcandidate
    rw [candidateDrain_failureSum_eq_zero_of_noFailure
      ring P state hnoFailure]
    exact Nat.zero_le _

private theorem candidateDrainPotential_step_le
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (state : CandidateDrainState ring) (edge : Fin n) :
    candidateDrainPotential (n := n) ring
        (candidateDrainStep ring P state edge) ≤
      n * choiceRaceReserve
        (incidenceStep P state.configuration edge) := by
  classical
  simp only [candidateDrainStep]
  split
  · simp [candidateDrainPotential]
  · split
    · simp [candidateDrainPotential]
    · simp [candidateDrainPotential]

/-- The same Race reserve that pays for complete incidence resolution also
pays for the earlier candidate-or-uniform stopping time. -/
theorem candidateDrain_natBellmanSuperSolution
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m) :
    NatBellmanSuperSolution (candidateDrainStep ring P) 1
      (candidateDrainPotential (n := n) ring) := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  have hreserve := choiceRaceReserve_incidence_childSum
    P state.configuration state.hasRace
  have hscaled := Nat.mul_le_mul_left n hreserve
  have hchildren :
      (List.ofFn (fun edge : Fin n =>
        candidateDrainPotential (n := n) ring
          (candidateDrainStep ring P state edge))).sum ≤
        n * (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve
            (incidenceStep P state.configuration edge))).sum := by
    calc
      (List.ofFn (fun edge : Fin n =>
          candidateDrainPotential (n := n) ring
            (candidateDrainStep ring P state edge))).sum ≤
          (List.ofFn (fun edge : Fin n =>
            n * choiceRaceReserve
              (incidenceStep P state.configuration edge))).sum := by
            apply ofFn_sum_le
            intro edge
            exact candidateDrainPotential_step_le ring P state edge
      _ = n * (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve
            (incidenceStep P state.configuration edge))).sum :=
        ofFn_sum_mul_left n _
  calc
    1 * n + (List.ofFn (fun edge : Fin n =>
        candidateDrainPotential (n := n) ring
          (candidateDrainStep ring P state edge))).sum ≤
        n + n * (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve
            (incidenceStep P state.configuration edge))).sum := by
          simpa using Nat.add_le_add_left hchildren n
    _ = n * (1 + (List.ofFn (fun edge : Fin n =>
          choiceRaceReserve
            (incidenceStep P state.configuration edge))).sum) := by
        rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * choiceRaceReserve state.configuration) := hscaled
    _ = n * candidateDrainPotential (n := n) ring (.active state) := by
      rfl

/-- Exact finite-horizon work bound for one candidate-classifying round. -/
theorem candidateDrain_truncatedCost_le
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (state : CandidateDrainState ring) (T : Nat) :
    truncatedActiveCostNumerator (candidateDrainStep ring P)
        (.active state) T ≤
      n ^ T * (n * choiceRaceReserve state.configuration) := by
  simpa [candidateDrainPotential] using
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (candidateDrainStep ring P) 1
      (candidateDrainPotential (n := n) ring)
      (candidateDrain_natBellmanSuperSolution ring P)
      (.active state) T

/-- The immediate good/bad injection lifts through every finite stopped-tree
horizon. -/
theorem candidateDrain_failureCount_le_successCount
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n)
    (state : CandidateDrainState ring) (T : Nat) :
    failureCount (candidateDrainStep ring P) (.active state) T ≤
      successCount (candidateDrainStep ring P) (.active state) T := by
  exact failureCount_le_successCount_of_local_balance
    (candidateDrainStep ring P)
    (fun next => candidateDrain_localBalance ring hm P hn next)
    state T

/-- By the Race-reserve horizon, at least half of scheduler mass has reached
one of the two terminal outcomes. -/
theorem candidateDrain_active_half_by_two_mul
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (state : CandidateDrainState ring) :
    2 * activeCount (candidateDrainStep ring P) (.active state)
        (2 * n * choiceRaceReserve state.configuration) ≤
      n ^ (2 * n * choiceRaceReserve state.configuration) := by
  let r := choiceRaceReserve state.configuration
  let T := 2 * n * r
  have hn : 0 < n := P.physicalRing.hn
  have hr : 0 < r :=
    choiceRaceReserve_pos_of_hasRace P state.configuration state.hasRace
  have hcost := candidateDrain_truncatedCost_le ring P state T
  have hactive :
      2 * activeCount (candidateDrainStep ring P) (.active state) T ≤
        n ^ T := by
    apply two_mul_activeCount_le_pow_of_scaled_cost
        (candidateDrainStep ring P) (.active state) (L := T)
        (den := 1) (num := n * r)
    · dsimp [T]
      exact Nat.mul_pos (Nat.mul_pos (by decide) hn) hr
    · omega
    · simpa [r, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using hcost
    · dsimp [T]
      simp [Nat.mul_assoc]
  simpa [T, r] using hactive

/-- One bare-incidence round creates a persistent candidate with at least one
quarter of scheduler mass by horizon `2*n*r`. -/
theorem candidateDrain_success_quarter_by_two_mul
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n)
    (state : CandidateDrainState ring) :
    n ^ (2 * n * choiceRaceReserve state.configuration) ≤
      4 * successCount (candidateDrainStep ring P) (.active state)
        (2 * n * choiceRaceReserve state.configuration) := by
  let T := 2 * n * choiceRaceReserve state.configuration
  have hactive := candidateDrain_active_half_by_two_mul ring P state
  have hactiveT :
      2 * activeCount (candidateDrainStep ring P) (.active state) T ≤
        n ^ T := by
    simpa [T] using hactive
  have hfailure := candidateDrain_failureCount_le_successCount
    ring hm P hn state T
  have hpartition := node_count_partition
    (candidateDrainStep ring P) (.active state) T
  have hresult : n ^ T ≤
      4 * successCount (candidateDrainStep ring P) (.active state) T := by
    omega
  simpa [T] using hresult

theorem allRaceConfiguration_noCandidate
    {m : Nat} (ring : DirectedRing m) :
    ∀ i, ¬ Candidate10 ring (allRaceConfiguration m) i := by
  intro i
  simp [Candidate10, allRaceConfiguration]

/-- On the cyclic all-short entry word, one round has truncated expected work
at most `n*m`. -/
theorem allRace_candidateDrain_truncatedCost_le
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (hm : 0 < m) (T : Nat) :
    truncatedActiveCostNumerator (candidateDrainStep ring P)
        (.active ⟨allRaceConfiguration m,
          allRaceConfiguration_hasRace hm,
          allRaceConfiguration_noCandidate ring⟩) T ≤
      n ^ T * (n * m) := by
  simpa using candidateDrain_truncatedCost_le ring P
    ⟨allRaceConfiguration m, allRaceConfiguration_hasRace hm,
      allRaceConfiguration_noCandidate ring⟩ T

/-- Consequently at least one quarter of all length-`2*n*m` scheduler words
have already created a persistent candidate. -/
theorem allRace_candidateDrain_success_quarter_by_two_mul
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) :
    n ^ (2 * n * m) ≤
      4 * successCount (candidateDrainStep ring P)
        (.active ⟨allRaceConfiguration m,
          allRaceConfiguration_hasRace (by omega),
          allRaceConfiguration_noCandidate ring⟩)
        (2 * n * m) := by
  simpa using candidateDrain_success_quarter_by_two_mul ring hm P hn
    ⟨allRaceConfiguration m,
      allRaceConfiguration_hasRace (by omega),
      allRaceConfiguration_noCandidate ring⟩

/-! ## Candidate rounds with explicitly charged rearm -/

/-- Physical obligation left after a candidate-free uniform round.  The
service starts at `start`, never stops at a bad terminal, and has its own
finite Bellman potential.  Its successful terminal means that all current
declarations/denials have been discharged and every root has safely returned
to the all-Race entry state.

This is the exact remaining carrier interface.  In particular, `potential`
must charge message currentness, shared-root serialization, and rearm debt;
those costs cannot be hidden in the logical candidate round. -/
structure CandidateRearmSpec (n : Nat) where
  State : Type
  step : State → Fin n → StopNode State
  start : State
  potential : StopNode State → Nat
  bellman : NatBellmanSuperSolution step 1 potential
  noFailure : ∀ state edge, step state edge ≠ .failure

/-- Canonical all-Race entry state of a fresh candidate round. -/
def allRaceCandidateDrainState {m : Nat} (ring : DirectedRing m)
    (hm : 0 < m) : CandidateDrainState ring :=
  ⟨allRaceConfiguration m, allRaceConfiguration_hasRace hm,
    allRaceConfiguration_noCandidate ring⟩

abbrev CandidateRearmSpec.RestartState
    {n m : Nat} (spec : CandidateRearmSpec n) (ring : DirectedRing m) :=
  BalancedFailureRestart.RestartState (CandidateDrainState ring) spec.State

/-- A logical candidate round whose uniform failure enters the physical rearm
service.  Rearm completion begins a fresh all-Race round. -/
noncomputable def CandidateRearmSpec.restartStep
    {n m : Nat} (spec : CandidateRearmSpec n) (ring : DirectedRing m)
    (P : Placement n m) (hm : 0 < m) :
    spec.RestartState ring → Fin n → StopNode (spec.RestartState ring) :=
  BalancedFailureRestart.restartStep
    (candidateDrainStep ring P) spec.step
    (allRaceCandidateDrainState ring hm) spec.start

/-- Combined selection-plus-rearm potential. -/
def CandidateRearmSpec.restartPotential
    {n m : Nat} (spec : CandidateRearmSpec n) (ring : DirectedRing m)
    (hm : 0 < m) : StopNode (spec.RestartState ring) → Nat :=
  BalancedFailureRestart.restartPotential
    (candidateDrainPotential (n := n) ring) spec.potential
    (allRaceCandidateDrainState ring hm) spec.start

/-- Local candidate good/bad balance pays the insurance needed to enter the
rearm service.  This is a single Bellman certificate for arbitrarily many
failed candidate rounds; it does not assume independent retries. -/
theorem CandidateRearmSpec.restart_natBellmanSuperSolution
    {n m : Nat} (spec : CandidateRearmSpec n) (ring : DirectedRing m)
    (hm : 1 < m) (P : Placement n m) (hn : 1 < n) :
    NatBellmanSuperSolution (spec.restartStep ring P (by omega)) 1
      (spec.restartPotential ring (by omega)) := by
  exact BalancedFailureRestart.restart_natBellmanSuperSolution
    (candidateDrainStep ring P) spec.step
    (allRaceCandidateDrainState ring (by omega)) spec.start
    (candidateDrainPotential (n := n) ring) spec.potential
    (candidateDrain_natBellmanSuperSolution ring P) spec.bellman
    (fun state => candidateDrain_localBalance ring hm P hn state)
    spec.noFailure

/-- No scheduler edge of the composed process exposes a bad terminal: logical
uniformity starts rearm, and only a persistent candidate is terminal. -/
theorem CandidateRearmSpec.restartStep_ne_failure
    {n m : Nat} (spec : CandidateRearmSpec n) (ring : DirectedRing m)
    (P : Placement n m) (hm : 0 < m) :
    ∀ state edge, spec.restartStep ring P hm state edge ≠ .failure := by
  exact BalancedFailureRestart.restartStep_ne_failure
    (candidateDrainStep ring P) spec.step
    (allRaceCandidateDrainState ring hm) spec.start spec.noFailure

/-- Exact expected-work numerator from a fresh all-Race round.  If the rearm
start has potential `R`, repeated candidate rounds cost at most `2*n*m + R`;
the reset cost is charged once in expectation because failed round mass is
locally dominated by successful round mass. -/
theorem CandidateRearmSpec.allRace_truncatedCost_le
    {n m : Nat} (spec : CandidateRearmSpec n) (ring : DirectedRing m)
    (hm : 1 < m) (P : Placement n m) (hn : 1 < n) (T : Nat) :
    truncatedActiveCostNumerator (spec.restartStep ring P (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (2 * (n * m) + spec.potential (.active spec.start)) := by
  have hsuper := spec.restart_natBellmanSuperSolution ring hm P hn
  have hcost :=
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (spec.restartStep ring P (by omega)) 1
      (spec.restartPotential ring (by omega)) hsuper
      (.active (.round (allRaceCandidateDrainState ring (by omega)))) T
  simpa [CandidateRearmSpec.restartPotential, candidateDrainPotential,
    allRaceCandidateDrainState, choiceRaceReserve_allRace] using hcost

/-- At every finite horizon the composed tree has zero bad-terminal mass. -/
theorem CandidateRearmSpec.allRace_failureCount_eq_zero
    {n m : Nat} (spec : CandidateRearmSpec n) (ring : DirectedRing m)
    (P : Placement n m) (hm : 0 < m) : ∀ T,
    failureCount (spec.restartStep ring P hm)
      (.active (.round (allRaceCandidateDrainState ring hm))) T = 0 := by
  exact BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
    (spec.restartStep ring P hm)
    (spec.restartStep_ne_failure ring P hm)
    (.round (allRaceCandidateDrainState ring hm))

/-- Reciprocal finite-horizon tail for the complete selection-plus-rearm
process.  Taking `factor = n` gives bad mass at most `1/n` after
`n * (2*n*m + R)` interactions. -/
theorem CandidateRearmSpec.allRace_factor_mul_activeCount_le_pow
    {n m factor : Nat} (spec : CandidateRearmSpec n)
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m)
    (hn : 1 < n) :
    factor * activeCount (spec.restartStep ring P (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega))))
        (factor * (2 * (n * m) + spec.potential (.active spec.start))) ≤
      n ^ (factor * (2 * (n * m) +
        spec.potential (.active spec.start))) := by
  let initial : StopNode (spec.RestartState ring) :=
    .active (.round (allRaceCandidateDrainState ring (by omega)))
  have hsuper := spec.restart_natBellmanSuperSolution ring hm P hn
  have hnm : 0 < n * m := Nat.mul_pos (by omega) (by omega)
  have hpositive : 0 < spec.restartPotential ring (by omega) initial := by
    simp [initial, CandidateRearmSpec.restartPotential,
      candidateDrainPotential, allRaceCandidateDrainState,
      choiceRaceReserve_allRace]
    omega
  have htail :=
    BalancedFailureRestart.factor_mul_activeCount_le_pow_of_natSuperSolution
      (spec.restartStep ring P (by omega))
      (spec.restartPotential ring (by omega)) hsuper initial hpositive
      (factor := factor)
  simpa [initial, CandidateRearmSpec.restartPotential,
    candidateDrainPotential, allRaceCandidateDrainState,
    choiceRaceReserve_allRace] using htail

/-- Division-free success form of the same tail bound.  With `factor = n`,
at least a `1 - 1/n` fraction of length-`n * (2*n*m + R)` scheduler words
have already produced a persistent candidate. -/
theorem CandidateRearmSpec.allRace_success_one_minus_inv_factor
    {n m factor : Nat} (spec : CandidateRearmSpec n)
    (ring : DirectedRing m) (hm : 1 < m) (P : Placement n m)
    (hn : 1 < n) :
    (factor - 1) *
        n ^ (factor * (2 * (n * m) +
          spec.potential (.active spec.start))) ≤
      factor * successCount (spec.restartStep ring P (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega))))
        (factor * (2 * (n * m) +
          spec.potential (.active spec.start))) := by
  let initialState : spec.RestartState ring :=
    .round (allRaceCandidateDrainState ring (by omega))
  have hsuper := spec.restart_natBellmanSuperSolution ring hm P hn
  have hnm : 0 < n * m := Nat.mul_pos (by omega) (by omega)
  have hpositive :
      0 < spec.restartPotential ring (by omega) (.active initialState) := by
    simp [initialState, CandidateRearmSpec.restartPotential,
      candidateDrainPotential, allRaceCandidateDrainState,
      choiceRaceReserve_allRace]
    omega
  have hsuccess :=
    BalancedFailureRestart.pred_mul_pow_le_factor_mul_successCount
      (spec.restartStep ring P (by omega))
      (spec.restartPotential ring (by omega)) hsuper
      (spec.restartStep_ne_failure ring P (by omega))
      initialState hpositive (factor := factor)
  simpa [initialState, CandidateRearmSpec.restartPotential,
    candidateDrainPotential, allRaceCandidateDrainState,
    choiceRaceReserve_allRace] using hsuccess

/-! ## Persistent retry-launch renewal -/

/-- Control phase of one uniform-base retry renewal. -/
inductive RetryRenewalState (S : Type) where
  | base (payload : S)
  | opened (payload : S)

/-- A state-uniform retry service.  The launch, good, and restore ports may
depend on the complete current payload.  All payload updates are unrestricted;
only the two control phases and good/restore distinctness matter below. -/
structure RetryRenewalSpec (S : Type) (n : Nat) where
  launch : S → Fin n
  good : S → Fin n
  restore : S → Fin n
  good_ne_restore : ∀ payload, good payload ≠ restore payload
  nextBase : S → Fin n → S
  nextOpened : S → Fin n → S

/-- From a uniform base, wait for the predictable launch port.  From an
opened retry, good absorbs, restore returns to the base phase, and all other
ports retain the opened phase. -/
def RetryRenewalSpec.stoppedStep
    {S : Type} {n : Nat} (spec : RetryRenewalSpec S n) :
    RetryRenewalState S → Fin n → StopNode (RetryRenewalState S)
  | .base payload, edge =>
      if edge = spec.launch payload then
        .active (.opened (spec.nextBase payload edge))
      else .active (.base (spec.nextBase payload edge))
  | .opened payload, edge =>
      if edge = spec.good payload then .success
      else if edge = spec.restore payload then
        .active (.base (spec.nextOpened payload edge))
      else .active (.opened (spec.nextOpened payload edge))

private def retryRenewalPotential {S : Type} (n : Nat) :
    StopNode (RetryRenewalState S) → Nat
  | .active (.base _) => 3 * n
  | .active (.opened _) => 2 * n
  | .success => 0
  | .failure => 0

/-- Exact Bellman certificate for repeated launch/two-port retries.  The
uniform base costs at most `3n`; an already-opened retry costs at most `2n`.
The proof permits every distinguished port to move after every prior draw. -/
theorem RetryRenewalSpec.natBellmanSuperSolution
    {S : Type} {n : Nat} (spec : RetryRenewalSpec S n) :
    NatBellmanSuperSolution spec.stoppedStep 1
      (retryRenewalPotential n) := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  cases state with
  | base payload =>
      have htarget :
          retryRenewalPotential n
              (spec.stoppedStep (.base payload) (spec.launch payload)) =
            2 * n := by
        simp [RetryRenewalSpec.stoppedStep, retryRenewalPotential]
      have hsum := ofFn_sum_one_value_else_const
        (spec.launch payload)
        (fun edge : Fin n => retryRenewalPotential n
          (spec.stoppedStep (.base payload) edge))
        (3 * n) (by
          intro edge hedge
          simp [RetryRenewalSpec.stoppedStep, retryRenewalPotential, hedge])
      rw [htarget] at hsum
      have hn : 0 < n := by
        have := (spec.launch payload).isLt
        omega
      have hpred : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
      rw [hsum]
      simp only [retryRenewalPotential]
      calc
        1 * n + (2 * n + (n - 1) * (3 * n)) =
            (n - 1) * (3 * n) + 1 * (3 * n) := by omega
        _ = (n - 1 + 1) * (3 * n) := by rw [Nat.add_mul]
        _ ≤ n * (3 * n) := by
          rw [hpred]
          exact Nat.le_refl _
  | opened payload =>
      have hdistinct := spec.good_ne_restore payload
      have hgood :
          retryRenewalPotential n
              (spec.stoppedStep (.opened payload) (spec.good payload)) =
            0 := by
        simp [RetryRenewalSpec.stoppedStep, retryRenewalPotential]
      have hrestore :
          retryRenewalPotential n
              (spec.stoppedStep (.opened payload) (spec.restore payload)) =
            3 * n := by
        simp [RetryRenewalSpec.stoppedStep, retryRenewalPotential,
          hdistinct.symm]
      have hsum := ofFn_sum_two_values_else_const
        (spec.good payload) (spec.restore payload)
        (fun edge : Fin n => retryRenewalPotential n
          (spec.stoppedStep (.opened payload) edge))
        (2 * n) hdistinct (by
          intro edge notGood notRestore
          simp [RetryRenewalSpec.stoppedStep, retryRenewalPotential,
            notGood, notRestore])
      rw [hgood, hrestore] at hsum
      have hn2 : 2 ≤ n := by
        have hgoodLt := (spec.good payload).isLt
        have hrestoreLt := (spec.restore payload).isLt
        have hvalne : (spec.good payload).val ≠
            (spec.restore payload).val := by
          intro hval
          exact hdistinct (Fin.ext hval)
        omega
      have hpred : n - 2 + 2 = n := Nat.sub_add_cancel hn2
      rw [hsum]
      simp only [retryRenewalPotential]
      calc
        1 * n + (0 + 3 * n + (n - 2) * (2 * n)) =
            (n - 2) * (2 * n) + 2 * (2 * n) := by omega
        _ = (n - 2 + 2) * (2 * n) := by rw [Nat.add_mul]
        _ ≤ n * (2 * n) := by
          rw [hpred]
          exact Nat.le_refl _

/-- Finite-horizon normalized truncated work from any uniform base is at most
`3n`, including every failed restore and subsequent relaunch. -/
theorem RetryRenewalSpec.base_truncatedCost_le
    {S : Type} {n : Nat} (spec : RetryRenewalSpec S n)
    (payload : S) (T : Nat) :
    truncatedActiveCostNumerator spec.stoppedStep
        (.active (.base payload)) T ≤ n ^ T * (3 * n) := by
  simpa [retryRenewalPotential] using
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      spec.stoppedStep 1 (retryRenewalPotential n)
      spec.natBellmanSuperSolution (.active (.base payload)) T

theorem RetryRenewalSpec.failureCount_eq_zero
    {S : Type} {n : Nat} (spec : RetryRenewalSpec S n) :
    ∀ state T, failureCount spec.stoppedStep (.active state) T = 0 := by
  intro state T
  induction T generalizing state with
  | zero => rfl
  | succ T ih =>
      simp only [failureCount, treeWeight, stepNode]
      calc
        (List.ofFn (fun edge : Fin n => treeWeight spec.stoppedStep
            failureWeight (spec.stoppedStep state edge) T)).sum =
            (List.ofFn (fun _ : Fin n => 0)).sum := by
              apply ofFn_sum_eq
              intro edge
              cases state with
              | base payload =>
                  by_cases hlaunch : edge = spec.launch payload
                  · simpa [RetryRenewalSpec.stoppedStep, hlaunch,
                      failureCount] using
                      ih (.opened (spec.nextBase payload edge))
                  · simpa [RetryRenewalSpec.stoppedStep, hlaunch,
                      failureCount] using
                      ih (.base (spec.nextBase payload edge))
              | opened payload =>
                  by_cases hgood : edge = spec.good payload
                  · simp [RetryRenewalSpec.stoppedStep, hgood,
                      treeWeight_success, failureWeight]
                  · by_cases hrestore : edge = spec.restore payload
                    · simpa [RetryRenewalSpec.stoppedStep, hgood, hrestore,
                        (spec.good_ne_restore payload).symm,
                        failureCount] using
                        ih (.base (spec.nextOpened payload edge))
                    · simpa [RetryRenewalSpec.stoppedStep, hgood, hrestore,
                        failureCount] using
                        ih (.opened (spec.nextOpened payload edge))
        _ = 0 := by rw [ofFn_sum_const]; simp

/-- State-uniform half-tail for the complete renewal: by `6n` raw draws at
least half of all scheduler words have selected a good retry port. -/
theorem RetryRenewalSpec.base_success_half_by_six_mul
    {S : Type} {n : Nat} (spec : RetryRenewalSpec S n) (payload : S) :
    n ^ (6 * n) ≤
      2 * successCount spec.stoppedStep (.active (.base payload)) (6 * n) := by
  have hn : 0 < n := by
    have := (spec.launch payload).isLt
    omega
  have hcost := spec.base_truncatedCost_le payload (6 * n)
  have hactive :
      2 * activeCount spec.stoppedStep (.active (.base payload)) (6 * n) ≤
        n ^ (6 * n) := by
    apply two_mul_activeCount_le_pow_of_scaled_cost
      spec.stoppedStep (.active (.base payload)) (L := 6 * n)
      (den := 1) (num := 3 * n)
    · exact Nat.mul_pos (by decide) hn
    · omega
    · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcost
    · omega
  have hpartition := node_count_partition spec.stoppedStep
    (.active (.base payload)) (6 * n)
  have hfailure := spec.failureCount_eq_zero (.base payload) (6 * n)
  rw [hfailure] at hpartition
  omega

/-! ## Concurrent-launch retry envelope -/

/-- Phase-indexed state for a concurrent retry service.  Base and opened
payloads may carry different invariants. -/
inductive ConcurrentRetryState (B O : Type) where
  | base (payload : B)
  | opened (payload : O)

/-- A retry service need not have a unique enabled launcher.  This envelope
names only one progress launcher in a base state, one good port in an opened
state, and the only port that is allowed to return an opened state to a base.
Every other base port may stutter, open another retry, or succeed; every other
opened port may remain opened or succeed.  Thus concurrent launches and extra
good ports are admitted explicitly. -/
structure ConcurrentRetrySpec (B O : Type) (n : Nat) where
  step : ConcurrentRetryState B O → Fin n →
    StopNode (ConcurrentRetryState B O)
  launch : B → Fin n
  good : O → Fin n
  restore : O → Fin n
  good_ne_restore : ∀ payload, good payload ≠ restore payload
  launch_opens : ∀ payload, ∃ nextPayload,
    step (.base payload) (launch payload) = .active (.opened nextPayload)
  good_succeeds : ∀ payload,
    step (.opened payload) (good payload) = .success
  other_opened : ∀ payload edge,
    edge ≠ good payload → edge ≠ restore payload →
      step (.opened payload) edge = .success ∨
        ∃ nextPayload,
          step (.opened payload) edge = .active (.opened nextPayload)
  never_fails : ∀ state edge, step state edge ≠ .failure

private def concurrentRetryPotential {B O : Type} (n : Nat) :
    StopNode (ConcurrentRetryState B O) → Nat
  | .active (.base _) => 3 * n
  | .active (.opened _) => 2 * n
  | .success => 0
  | .failure => 0

private theorem concurrentRetryPotential_le_three_mul
    {B O : Type} (n : Nat) (node : StopNode (ConcurrentRetryState B O)) :
    concurrentRetryPotential n node ≤ 3 * n := by
  cases node with
  | active state => cases state <;> simp [concurrentRetryPotential] <;> omega
  | success => simp [concurrentRetryPotential]
  | failure => simp [concurrentRetryPotential]

private theorem ConcurrentRetrySpec.other_opened_potential_le
    {B O : Type} {n : Nat} (spec : ConcurrentRetrySpec B O n)
    (payload : O) (edge : Fin n)
    (hgood : edge ≠ spec.good payload)
    (hrestore : edge ≠ spec.restore payload) :
    concurrentRetryPotential n (spec.step (.opened payload) edge) ≤ 2 * n := by
  rcases spec.other_opened payload edge hgood hrestore with hsuccess | hopened
  · rw [hsuccess]
    simp [concurrentRetryPotential]
  · obtain ⟨nextPayload, hnext⟩ := hopened
    rw [hnext]
    simp [concurrentRetryPotential]

/-- The `3n/2n` Bellman certificate survives arbitrary concurrent launches,
extra good ports, and history-dependent payload changes.  The only forbidden
opened transition is an additional return to the base outside the named
restore port. -/
theorem ConcurrentRetrySpec.natBellmanSuperSolution
    {B O : Type} {n : Nat} (spec : ConcurrentRetrySpec B O n) :
    NatBellmanSuperSolution spec.step 1
      (concurrentRetryPotential n) := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  cases state with
  | base payload =>
      let bound : Fin n → Nat := fun edge =>
        if edge = spec.launch payload then 2 * n else 3 * n
      have hpoint : ∀ edge,
          concurrentRetryPotential n (spec.step (.base payload) edge) ≤
            bound edge := by
        intro edge
        by_cases hedge : edge = spec.launch payload
        · subst edge
          obtain ⟨nextPayload, hnext⟩ := spec.launch_opens payload
          rw [hnext]
          simp [bound, concurrentRetryPotential]
        · simpa [bound, hedge] using
            concurrentRetryPotential_le_three_mul n
              (spec.step (.base payload) edge)
      have hsumle := ofFn_sum_le
        (fun edge : Fin n =>
          concurrentRetryPotential n (spec.step (.base payload) edge))
        bound hpoint
      have hsumbound := ofFn_sum_one_value_else_const
        (spec.launch payload) bound (3 * n) (by
          intro edge hedge
          simp [bound, hedge])
      have hlaunchValue : bound (spec.launch payload) = 2 * n := by
        simp [bound]
      rw [hlaunchValue] at hsumbound
      rw [hsumbound] at hsumle
      have hn : 0 < n := by
        have := (spec.launch payload).isLt
        omega
      have hpred : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
      simp only [concurrentRetryPotential]
      calc
        1 * n + (List.ofFn (fun edge : Fin n =>
            concurrentRetryPotential n
              (spec.step (.base payload) edge))).sum ≤
            1 * n + (2 * n + (n - 1) * (3 * n)) :=
          Nat.add_le_add_left hsumle _
        _ = (n - 1) * (3 * n) + 1 * (3 * n) := by omega
        _ = (n - 1 + 1) * (3 * n) := by rw [Nat.add_mul]
        _ = n * (3 * n) := by rw [hpred]
  | opened payload =>
      let bound : Fin n → Nat := fun edge =>
        if edge = spec.good payload then 0
        else if edge = spec.restore payload then 3 * n
        else 2 * n
      have hdistinct := spec.good_ne_restore payload
      have hpoint : ∀ edge,
          concurrentRetryPotential n (spec.step (.opened payload) edge) ≤
            bound edge := by
        intro edge
        by_cases hgood : edge = spec.good payload
        · subst edge
          rw [spec.good_succeeds]
          simp [bound, concurrentRetryPotential]
        · by_cases hrestore : edge = spec.restore payload
          · simpa [bound, hgood, hrestore, hdistinct.symm] using
              concurrentRetryPotential_le_three_mul n
                (spec.step (.opened payload) edge)
          · simpa [bound, hgood, hrestore] using
              spec.other_opened_potential_le payload edge hgood hrestore
      have hsumle := ofFn_sum_le
        (fun edge : Fin n =>
          concurrentRetryPotential n (spec.step (.opened payload) edge))
        bound hpoint
      have hsumbound := ofFn_sum_two_values_else_const
        (spec.good payload) (spec.restore payload) bound (2 * n)
        hdistinct (by
          intro edge hgood hrestore
          simp [bound, hgood, hrestore])
      have hgoodValue : bound (spec.good payload) = 0 := by
        simp [bound]
      have hrestoreValue : bound (spec.restore payload) = 3 * n := by
        simp [bound, hdistinct.symm]
      rw [hgoodValue, hrestoreValue] at hsumbound
      rw [hsumbound] at hsumle
      have hn2 : 2 ≤ n := by
        have hgoodLt := (spec.good payload).isLt
        have hrestoreLt := (spec.restore payload).isLt
        have hvalne : (spec.good payload).val ≠
            (spec.restore payload).val := by
          intro hval
          exact hdistinct (Fin.ext hval)
        omega
      have hpred : n - 2 + 2 = n := Nat.sub_add_cancel hn2
      simp only [concurrentRetryPotential]
      calc
        1 * n + (List.ofFn (fun edge : Fin n =>
            concurrentRetryPotential n
              (spec.step (.opened payload) edge))).sum ≤
            1 * n + (0 + 3 * n + (n - 2) * (2 * n)) :=
          Nat.add_le_add_left hsumle _
        _ = (n - 2) * (2 * n) + 2 * (2 * n) := by omega
        _ = (n - 2 + 2) * (2 * n) := by rw [Nat.add_mul]
        _ = n * (2 * n) := by rw [hpred]

/-- Finite-horizon normalized work from a concurrent-launch base is at most
`3n`. -/
theorem ConcurrentRetrySpec.base_truncatedCost_le
    {B O : Type} {n : Nat} (spec : ConcurrentRetrySpec B O n)
    (payload : B) (T : Nat) :
    truncatedActiveCostNumerator spec.step
        (.active (.base payload)) T ≤ n ^ T * (3 * n) := by
  simpa [concurrentRetryPotential] using
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      spec.step 1 (concurrentRetryPotential n)
      spec.natBellmanSuperSolution (.active (.base payload)) T

theorem ConcurrentRetrySpec.failureCount_eq_zero
    {B O : Type} {n : Nat} (spec : ConcurrentRetrySpec B O n) :
    ∀ state T, failureCount spec.step (.active state) T = 0 := by
  intro state T
  induction T generalizing state with
  | zero => rfl
  | succ T ih =>
      simp only [failureCount, treeWeight, stepNode]
      calc
        (List.ofFn (fun edge : Fin n => treeWeight spec.step
            failureWeight (spec.step state edge) T)).sum =
            (List.ofFn (fun _ : Fin n => 0)).sum := by
              apply ofFn_sum_eq
              intro edge
              cases hnext : spec.step state edge with
              | active nextState =>
                  simpa [hnext, failureCount] using ih nextState
              | success => simp [treeWeight_success, failureWeight]
              | failure =>
                  exact (spec.never_fails state edge hnext).elim
        _ = 0 := by rw [ofFn_sum_const]; simp

/-- By `6n` raw draws, at least half of all scheduler words from a concurrent
retry base have succeeded. -/
theorem ConcurrentRetrySpec.base_success_half_by_six_mul
    {B O : Type} {n : Nat} (spec : ConcurrentRetrySpec B O n)
    (payload : B) :
    n ^ (6 * n) ≤
      2 * successCount spec.step (.active (.base payload)) (6 * n) := by
  have hn : 0 < n := by
    have := (spec.launch payload).isLt
    omega
  have hcost := spec.base_truncatedCost_le payload (6 * n)
  have hactive :
      2 * activeCount spec.step (.active (.base payload)) (6 * n) ≤
        n ^ (6 * n) := by
    apply two_mul_activeCount_le_pow_of_scaled_cost
      spec.step (.active (.base payload)) (L := 6 * n)
      (den := 1) (num := 3 * n)
    · exact Nat.mul_pos (by decide) hn
    · omega
    · simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcost
    · omega
  have hpartition := node_count_partition spec.step
    (.active (.base payload)) (6 * n)
  have hfailure := spec.failureCount_eq_zero (.base payload) (6 * n)
  rw [hfailure] at hpartition
  omega

/-! ## Ranked multi-step launch service

The one-step concurrent envelope above is the `d = 1` timing abstraction.  A
literal short-gap carrier generally has to protect and forward a request across
several radius-one services before a logical retry is opened.  The next
envelope makes that preparation debt explicit.  It still permits concurrent
launches: only one predictable service edge is named, and every other base
edge may finish, open another retry, or preserve the named service rank.

This is a scheduler theorem, not a construction of the carrier.  An
instantiation must separately prove that unrelated literal rows cannot revoke
the tracked current request or increase its remaining rank.
-/

/-- Concurrent retry with a positive, bounded preparation rank.  Selecting the
predictable service edge strictly lowers the rank unless it already opens a
retry or succeeds.  Other base edges need only avoid increasing the tracked
rank. -/
structure RankedConcurrentRetrySpec (B O : Type) (n d : Nat) where
  step : ConcurrentRetryState B O → Fin n →
    StopNode (ConcurrentRetryState B O)
  rank : B → Nat
  rank_pos : ∀ payload, 0 < rank payload
  rank_le : ∀ payload, rank payload ≤ d
  service : B → Fin n
  good : O → Fin n
  restore : O → Fin n
  good_ne_restore : ∀ payload, good payload ≠ restore payload
  service_progress : ∀ payload,
    step (.base payload) (service payload) = .success ∨
      (∃ nextPayload,
        step (.base payload) (service payload) =
          .active (.opened nextPayload)) ∨
      ∃ nextPayload,
        step (.base payload) (service payload) =
          .active (.base nextPayload) ∧
        rank nextPayload < rank payload
  other_base : ∀ payload edge,
    edge ≠ service payload →
      step (.base payload) edge = .success ∨
        (∃ nextPayload,
          step (.base payload) edge = .active (.opened nextPayload)) ∨
        ∃ nextPayload,
          step (.base payload) edge = .active (.base nextPayload) ∧
          rank nextPayload ≤ rank payload
  good_succeeds : ∀ payload,
    step (.opened payload) (good payload) = .success
  other_opened : ∀ payload edge,
    edge ≠ good payload → edge ≠ restore payload →
      step (.opened payload) edge = .success ∨
        ∃ nextPayload,
          step (.opened payload) edge = .active (.opened nextPayload)
  never_fails : ∀ state edge, step state edge ≠ .failure

private def rankedConcurrentRetryPotential
    {B O : Type} {n d : Nat} (spec : RankedConcurrentRetrySpec B O n d) :
    StopNode (ConcurrentRetryState B O) → Nat
  | .active (.base payload) => n * spec.rank payload + n * (d + 1)
  | .active (.opened _) => n * (d + 1)
  | .success => 0
  | .failure => 0

private theorem RankedConcurrentRetrySpec.potential_le_cap
    {B O : Type} {n d : Nat} (spec : RankedConcurrentRetrySpec B O n d)
    (node : StopNode (ConcurrentRetryState B O)) :
    rankedConcurrentRetryPotential spec node ≤ n * (2 * d + 1) := by
  cases node with
  | active state =>
      cases state with
      | base payload =>
          simp only [rankedConcurrentRetryPotential]
          calc
            n * spec.rank payload + n * (d + 1) ≤
                n * d + n * (d + 1) :=
              Nat.add_le_add_right
                (Nat.mul_le_mul_left n (spec.rank_le payload)) _
            _ = n * (2 * d + 1) := by
              simp only [Nat.mul_add, Nat.mul_one, Nat.two_mul]
              omega
      | opened payload =>
          simp only [rankedConcurrentRetryPotential]
          calc
            n * (d + 1) ≤ n * d + n * (d + 1) :=
              Nat.le_add_left _ _
            _ = n * (2 * d + 1) := by
              simp only [Nat.mul_add, Nat.mul_one, Nat.two_mul]
              omega
  | success => simp [rankedConcurrentRetryPotential]
  | failure => simp [rankedConcurrentRetryPotential]

private theorem RankedConcurrentRetrySpec.service_pays_one
    {B O : Type} {n d : Nat} (spec : RankedConcurrentRetrySpec B O n d)
    (payload : B) :
    n + rankedConcurrentRetryPotential spec
        (spec.step (.base payload) (spec.service payload)) ≤
      rankedConcurrentRetryPotential spec (.active (.base payload)) := by
  have hrank : 1 ≤ spec.rank payload := spec.rank_pos payload
  have hnrank := Nat.mul_le_mul_left n hrank
  rcases spec.service_progress payload with hsuccess | hopened | hbase
  · rw [hsuccess]
    simp only [rankedConcurrentRetryPotential]
    omega
  · obtain ⟨nextPayload, hnext⟩ := hopened
    rw [hnext]
    simp only [rankedConcurrentRetryPotential]
    omega
  · obtain ⟨nextPayload, hnext, hrankLt⟩ := hbase
    rw [hnext]
    simp only [rankedConcurrentRetryPotential]
    have hrankSucc : spec.rank nextPayload + 1 ≤ spec.rank payload := by
      omega
    have hmul := Nat.mul_le_mul_left n hrankSucc
    simp only [Nat.mul_add] at hmul
    omega

private theorem RankedConcurrentRetrySpec.other_base_potential_le
    {B O : Type} {n d : Nat} (spec : RankedConcurrentRetrySpec B O n d)
    (payload : B) (edge : Fin n) (hedge : edge ≠ spec.service payload) :
    rankedConcurrentRetryPotential spec (spec.step (.base payload) edge) ≤
      rankedConcurrentRetryPotential spec (.active (.base payload)) := by
  rcases spec.other_base payload edge hedge with hsuccess | hopened | hbase
  · rw [hsuccess]
    simp [rankedConcurrentRetryPotential]
  · obtain ⟨nextPayload, hnext⟩ := hopened
    rw [hnext]
    simp only [rankedConcurrentRetryPotential]
    exact Nat.le_add_left _ _
  · obtain ⟨nextPayload, hnext, hrank⟩ := hbase
    rw [hnext]
    simp only [rankedConcurrentRetryPotential]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left n hrank) _

private theorem RankedConcurrentRetrySpec.other_opened_potential_le
    {B O : Type} {n d : Nat} (spec : RankedConcurrentRetrySpec B O n d)
    (payload : O) (edge : Fin n)
    (hgood : edge ≠ spec.good payload)
    (hrestore : edge ≠ spec.restore payload) :
    rankedConcurrentRetryPotential spec (spec.step (.opened payload) edge) ≤
      n * (d + 1) := by
  rcases spec.other_opened payload edge hgood hrestore with hsuccess | hopened
  · rw [hsuccess]
    simp [rankedConcurrentRetryPotential]
  · obtain ⟨nextPayload, hnext⟩ := hopened
    rw [hnext]
    simp [rankedConcurrentRetryPotential]

/-- A bounded `d`-service preparation followed by a good/restore retry has
normalized truncated cost at most `n * (2*d+1)`.  The proof is uniform in all
history-dependent payload and target changes. -/
theorem RankedConcurrentRetrySpec.natBellmanSuperSolution
    {B O : Type} {n d : Nat} (spec : RankedConcurrentRetrySpec B O n d) :
    NatBellmanSuperSolution spec.step 1
      (rankedConcurrentRetryPotential spec) := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  cases state with
  | base payload =>
      let c := rankedConcurrentRetryPotential spec (.active (.base payload))
      let a := rankedConcurrentRetryPotential spec
        (spec.step (.base payload) (spec.service payload))
      let bound : Fin n → Nat := fun edge =>
        if edge = spec.service payload then a else c
      have hpoint : ∀ edge,
          rankedConcurrentRetryPotential spec
              (spec.step (.base payload) edge) ≤ bound edge := by
        intro edge
        by_cases hedge : edge = spec.service payload
        · subst edge
          simp [bound, a]
        · simpa [bound, hedge, c] using
            spec.other_base_potential_le payload edge hedge
      have hsumle := ofFn_sum_le
        (fun edge : Fin n => rankedConcurrentRetryPotential spec
          (spec.step (.base payload) edge)) bound hpoint
      have hsumbound := ofFn_sum_one_value_else_const
        (spec.service payload) bound c (by
          intro edge hedge
          simp [bound, hedge])
      have hserviceValue : bound (spec.service payload) = a := by
        simp [bound]
      rw [hserviceValue] at hsumbound
      rw [hsumbound] at hsumle
      have hn : 0 < n := by
        have := (spec.service payload).isLt
        omega
      have hpred : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
      have hpay : n + a ≤ c := by
        simpa [a, c] using spec.service_pays_one payload
      calc
        1 * n + (List.ofFn (fun edge : Fin n =>
            rankedConcurrentRetryPotential spec
              (spec.step (.base payload) edge))).sum ≤
            n + (a + (n - 1) * c) := by
              simpa [Nat.one_mul] using Nat.add_le_add_left hsumle n
        _ = (n + a) + (n - 1) * c := by omega
        _ ≤ c + (n - 1) * c := Nat.add_le_add_right hpay _
        _ = (n - 1 + 1) * c := by
          rw [Nat.add_mul]
          omega
        _ = n * c := by rw [hpred]
  | opened payload =>
      let openedCap := n * (d + 1)
      let baseCap := n * (2 * d + 1)
      let bound : Fin n → Nat := fun edge =>
        if edge = spec.good payload then 0
        else if edge = spec.restore payload then baseCap
        else openedCap
      have hdistinct := spec.good_ne_restore payload
      have hpoint : ∀ edge,
          rankedConcurrentRetryPotential spec
              (spec.step (.opened payload) edge) ≤ bound edge := by
        intro edge
        by_cases hgood : edge = spec.good payload
        · subst edge
          rw [spec.good_succeeds]
          simp [bound, rankedConcurrentRetryPotential]
        · by_cases hrestore : edge = spec.restore payload
          · simpa [bound, hgood, hrestore, hdistinct.symm, baseCap] using
              spec.potential_le_cap
                (spec.step (.opened payload) edge)
          · simpa [bound, hgood, hrestore, openedCap] using
              spec.other_opened_potential_le payload edge hgood hrestore
      have hsumle := ofFn_sum_le
        (fun edge : Fin n => rankedConcurrentRetryPotential spec
          (spec.step (.opened payload) edge)) bound hpoint
      have hsumbound := ofFn_sum_two_values_else_const
        (spec.good payload) (spec.restore payload) bound openedCap
        hdistinct (by
          intro edge hgood hrestore
          simp [bound, hgood, hrestore])
      have hgoodValue : bound (spec.good payload) = 0 := by
        simp [bound]
      have hrestoreValue : bound (spec.restore payload) = baseCap := by
        simp [bound, hdistinct.symm]
      rw [hgoodValue, hrestoreValue] at hsumbound
      rw [hsumbound] at hsumle
      have hn2 : 2 ≤ n := by
        have hgoodLt := (spec.good payload).isLt
        have hrestoreLt := (spec.restore payload).isLt
        have hvalne : (spec.good payload).val ≠
            (spec.restore payload).val := by
          intro hval
          exact hdistinct (Fin.ext hval)
        omega
      have hpred : n - 2 + 2 = n := Nat.sub_add_cancel hn2
      simp only [rankedConcurrentRetryPotential]
      calc
        1 * n + (List.ofFn (fun edge : Fin n =>
            rankedConcurrentRetryPotential spec
              (spec.step (.opened payload) edge))).sum ≤
            n + (0 + baseCap + (n - 2) * openedCap) := by
          simpa only [Nat.one_mul] using Nat.add_le_add_left hsumle n
        _ = n * openedCap := by
          have hbase : n + baseCap = 2 * openedCap := by
            dsimp [baseCap, openedCap]
            simp only [Nat.mul_add, Nat.mul_one, Nat.two_mul]
            omega
          rw [Nat.zero_add]
          calc
            n + (baseCap + (n - 2) * openedCap) =
                (n + baseCap) + (n - 2) * openedCap := by omega
            _ = 2 * openedCap + (n - 2) * openedCap := by rw [hbase]
            _ = (2 + (n - 2)) * openedCap := by rw [Nat.add_mul]
            _ = n * openedCap := by rw [show 2 + (n - 2) = n by omega]
        _ = n * (n * (d + 1)) := by rfl

/-- Finite-horizon work bound from any ranked base payload. -/
theorem RankedConcurrentRetrySpec.base_truncatedCost_le
    {B O : Type} {n d : Nat} (spec : RankedConcurrentRetrySpec B O n d)
    (payload : B) (T : Nat) :
    truncatedActiveCostNumerator spec.step (.active (.base payload)) T ≤
      n ^ T * (n * (2 * d + 1)) := by
  have hcost := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    spec.step 1 (rankedConcurrentRetryPotential spec)
    spec.natBellmanSuperSolution (.active (.base payload)) T
  have hcap := spec.potential_le_cap (.active (.base payload))
  have hcost' :
      truncatedActiveCostNumerator spec.step (.active (.base payload)) T ≤
        n ^ T * rankedConcurrentRetryPotential spec
          (.active (.base payload)) := by
    simpa using hcost
  exact Nat.le_trans hcost' (Nat.mul_le_mul_left (n ^ T) hcap)

theorem RankedConcurrentRetrySpec.failureCount_eq_zero
    {B O : Type} {n d : Nat} (spec : RankedConcurrentRetrySpec B O n d) :
    ∀ state T, failureCount spec.step (.active state) T = 0 := by
  intro state T
  induction T generalizing state with
  | zero => rfl
  | succ T ih =>
      simp only [failureCount, treeWeight, stepNode]
      calc
        (List.ofFn (fun edge : Fin n => treeWeight spec.step
            failureWeight (spec.step state edge) T)).sum =
            (List.ofFn (fun _ : Fin n => 0)).sum := by
              apply ofFn_sum_eq
              intro edge
              cases hnext : spec.step state edge with
              | active nextState =>
                  simpa [hnext, failureCount] using ih nextState
              | success => simp [treeWeight_success, failureWeight]
              | failure => exact (spec.never_fails state edge hnext).elim
        _ = 0 := by rw [ofFn_sum_const]; simp

/-- Markov at twice the ranked work budget: at least half of all scheduler
words have reached success by `2*n*(2*d+1)` raw draws. -/
theorem RankedConcurrentRetrySpec.base_success_half_by_two_mul
    {B O : Type} {n d : Nat} (spec : RankedConcurrentRetrySpec B O n d)
    (payload : B) :
    n ^ (2 * n * (2 * d + 1)) ≤
      2 * successCount spec.step (.active (.base payload))
        (2 * n * (2 * d + 1)) := by
  let budget := n * (2 * d + 1)
  let horizon := 2 * n * (2 * d + 1)
  have hn : 0 < n := by
    have := (spec.service payload).isLt
    omega
  have hbudget : 0 < budget := by
    dsimp [budget]
    exact Nat.mul_pos hn (by omega)
  have hcost := spec.base_truncatedCost_le payload horizon
  have hactive :
      2 * activeCount spec.step (.active (.base payload)) horizon ≤
        n ^ horizon := by
    apply two_mul_activeCount_le_pow_of_scaled_cost
      spec.step (.active (.base payload)) (L := horizon)
      (den := 1) (num := budget)
    · dsimp [horizon]
      exact Nat.mul_pos (Nat.mul_pos (by decide) hn) (by omega)
    · omega
    · simpa [budget, Nat.mul_comm] using hcost
    · dsimp [horizon, budget]
      simp only [Nat.mul_one]
      exact Nat.le_of_eq (by ac_rfl)
  have hpartition := node_count_partition spec.step
    (.active (.base payload)) horizon
  have hfailure := spec.failureCount_eq_zero (.base payload) horizon
  rw [hfailure] at hpartition
  dsimp [horizon] at hactive hpartition hfailure ⊢
  omega

/-! ## Concurrent choice-retry refinement interface -/

theorem Frozen.hasNonRace {m : Nat} {C : Configuration m}
    (hm : 0 < m) (h : Frozen C) : HasNonRace C := by
  let i : Fin m := ⟨0, hm⟩
  exact ⟨i, h i⟩

theorem Constant.frozen_of_hasNonRace
    {m : Nat} {C : Configuration m}
    (hconstant : Constant C) (hnonRace : HasNonRace C) : Frozen C := by
  obtain ⟨value, hvalue⟩ := hconstant
  obtain ⟨fixed, hfixed⟩ := hnonRace
  intro i hi
  have hvalueRace : value = .race := by
    rw [← hvalue i]
    exact hi
  apply hfixed
  rw [hvalue fixed, hvalueRace]

/-- Candidate-free constant payload after the initial all-Race drain. -/
structure ConcurrentRetryBase {m : Nat} (ring : DirectedRing m) where
  configuration : Configuration m
  frozen : Frozen configuration
  constant : Constant configuration
  noCandidate : ∀ i, ¬ Candidate10 ring configuration i

/-- Candidate-free nonconstant payload during any number of concurrent
oriented retries.  A retained non-Race root excludes return to all-Race. -/
structure ConcurrentRetryOpened {m : Nat} (ring : DirectedRing m) where
  configuration : Configuration m
  hasNonRace : HasNonRace configuration
  notConstant : ¬ Constant configuration
  noCandidate : ∀ i, ¬ Candidate10 ring configuration i

theorem ConcurrentRetryBase.hasNonRace
    {m : Nat} {ring : DirectedRing m}
    (payload : ConcurrentRetryBase ring) :
    HasNonRace payload.configuration :=
  Frozen.hasNonRace ring.hn payload.frozen

/-- Choice-quotient boundary for the concurrent-launch route.  A child in this
interface may contain arbitrarily many enabled logical launch and good actions.
The proof
needs only one base progress edge, one unmasked good edge in every opened
state, preservation of a non-Race root, and uniqueness of a child that returns
the whole choice word to a constant.  A literal radius-one refinement is a
separate obligation. -/
structure ConcurrentChoiceRetryCertificate
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m) where
  step : Configuration m → Fin n → Configuration m
  preservesNonRace : ∀ C edge, HasNonRace C → HasNonRace (step C edge)
  launch : ConcurrentRetryBase ring → Fin n
  launchNoCandidate : ∀ (payload : ConcurrentRetryBase ring) (i : Fin m),
    ¬ Candidate10 ring
      (step payload.configuration (launch payload)) i
  launchNotConstant : ∀ payload : ConcurrentRetryBase ring,
    ¬ Constant (step payload.configuration (launch payload))
  good : ConcurrentRetryOpened ring → Fin n
  goodCreates : ∀ payload : ConcurrentRetryOpened ring,
    ∃ i, Candidate10 ring
      (step payload.configuration (good payload)) i
  constantChildrenUnique : ∀ (payload : ConcurrentRetryOpened ring)
      (first second : Fin n),
    Constant (step payload.configuration first) →
    Constant (step payload.configuration second) → first = second

/-- The positive obligations for an atomic incidence-or-retry quotient: one
logical launch child from every uniform base and one unmasked good child from
every candidate-free nonconstant word.  No uniqueness is imposed on either set
of children.  For a positive-length physical gap, a ranked carrier must refine
the first obligation across several raw interactions. -/
structure ConcurrentDispatcherProgress
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (dispatcher : ConcurrentDispatcher n m) where
  launch : ConcurrentRetryBase ring → Fin n
  launchNoCandidate : ∀ (payload : ConcurrentRetryBase ring) (i : Fin m),
    ¬ Candidate10 ring
      (dispatcher.dispatchStep ring P payload.configuration
        (launch payload)) i
  launchNotConstant : ∀ payload : ConcurrentRetryBase ring,
    ¬ Constant (dispatcher.dispatchStep ring P payload.configuration
      (launch payload))
  good : ConcurrentRetryOpened ring → Fin n
  goodCreates : ∀ payload : ConcurrentRetryOpened ring,
    ∃ i, Candidate10 ring
      (dispatcher.dispatchStep ring P payload.configuration
        (good payload)) i

/-- The general constant-child and non-Race obligations follow from the
incidence-or-retry quotient itself; they are not extra protocol axioms. -/
def ConcurrentDispatcherProgress.choiceCertificate
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    {dispatcher : ConcurrentDispatcher n m}
    (progress : ConcurrentDispatcherProgress ring P dispatcher)
    (hm : 1 < m) : ConcurrentChoiceRetryCertificate ring P where
  step := dispatcher.dispatchStep ring P
  preservesNonRace := by
    intro C edge h
    exact dispatcher.dispatchStep_hasNonRace ring hm P C edge h
  launch := progress.launch
  launchNoCandidate := progress.launchNoCandidate
  launchNotConstant := progress.launchNotConstant
  good := progress.good
  goodCreates := progress.goodCreates
  constantChildrenUnique := by
    intro payload first second hfirst hsecond
    have hRace := hasRace_of_noCandidate_not_constant ring
      payload.configuration payload.noCandidate payload.notConstant
    exact dispatcher.constant_children_unique ring hm P payload.configuration
      hRace payload.hasNonRace payload.notConstant first second hfirst hsecond

noncomputable def classifyConcurrentChoice
    {m : Nat} (ring : DirectedRing m) (C : Configuration m)
    (hnonRace : HasNonRace C) :
    StopNode (ConcurrentRetryState
      (ConcurrentRetryBase ring) (ConcurrentRetryOpened ring)) := by
  classical
  by_cases hCandidate : ∃ i, Candidate10 ring C i
  · exact .success
  · have hnoCandidate : ∀ i, ¬ Candidate10 ring C i := by
      intro i hi
      exact hCandidate ⟨i, hi⟩
    by_cases hConstant : Constant C
    · exact .active (.base
        { configuration := C
          frozen := Constant.frozen_of_hasNonRace hConstant hnonRace
          constant := hConstant
          noCandidate := hnoCandidate })
    · exact .active (.opened
        { configuration := C
          hasNonRace := hnonRace
          notConstant := hConstant
          noCandidate := hnoCandidate })

theorem classifyConcurrentChoice_eq_success
    {m : Nat} (ring : DirectedRing m) (C : Configuration m)
    (hnonRace : HasNonRace C)
    (hCandidate : ∃ i, Candidate10 ring C i) :
    classifyConcurrentChoice ring C hnonRace = .success := by
  simp [classifyConcurrentChoice, hCandidate]

theorem classifyConcurrentChoice_eq_opened
    {m : Nat} (ring : DirectedRing m) (C : Configuration m)
    (hnonRace : HasNonRace C)
    (hnoCandidate : ∀ i, ¬ Candidate10 ring C i)
    (hnotConstant : ¬ Constant C) :
    ∃ payload : ConcurrentRetryOpened ring,
      classifyConcurrentChoice ring C hnonRace = .active (.opened payload) := by
  have hnone : ¬ ∃ i, Candidate10 ring C i := by
    intro h
    obtain ⟨i, hi⟩ := h
    exact hnoCandidate i hi
  simp only [classifyConcurrentChoice, hnone, hnotConstant, ↓reduceDIte]
  exact ⟨_, rfl⟩

theorem classifyConcurrentChoice_ne_failure
    {m : Nat} (ring : DirectedRing m) (C : Configuration m)
    (hnonRace : HasNonRace C) :
    classifyConcurrentChoice ring C hnonRace ≠ .failure := by
  classical
  unfold classifyConcurrentChoice
  split <;> simp
  split <;> simp

noncomputable def ConcurrentChoiceRetryCertificate.stoppedStep
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    (certificate : ConcurrentChoiceRetryCertificate ring P) :
    ConcurrentRetryState
        (ConcurrentRetryBase ring) (ConcurrentRetryOpened ring) →
      Fin n →
        StopNode (ConcurrentRetryState
          (ConcurrentRetryBase ring) (ConcurrentRetryOpened ring))
  | .base payload, edge =>
      classifyConcurrentChoice ring
        (certificate.step payload.configuration edge)
        (certificate.preservesNonRace payload.configuration edge
          payload.hasNonRace)
  | .opened payload, edge =>
      classifyConcurrentChoice ring
        (certificate.step payload.configuration edge)
        (certificate.preservesNonRace payload.configuration edge
          payload.hasNonRace)

theorem ConcurrentChoiceRetryCertificate.good_not_constant
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    (certificate : ConcurrentChoiceRetryCertificate ring P)
    (payload : ConcurrentRetryOpened ring) :
    ¬ Constant
      (certificate.step payload.configuration (certificate.good payload)) := by
  obtain ⟨i, hi⟩ := certificate.goodCreates payload
  exact hi.not_constant ring

/-- If a constant-return child exists, use it as the sole restore port.
Otherwise choose the clockwise neighbor of the good port as a harmless
placeholder. -/
noncomputable def ConcurrentChoiceRetryCertificate.restore
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    (certificate : ConcurrentChoiceRetryCertificate ring P)
    (payload : ConcurrentRetryOpened ring) : Fin n := by
  classical
  exact if h : ∃ edge,
      Constant (certificate.step payload.configuration edge) then
    Classical.choose h
  else P.physicalRing.rightNeighbor (certificate.good payload)

theorem ConcurrentChoiceRetryCertificate.good_ne_restore
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    (certificate : ConcurrentChoiceRetryCertificate ring P) (hn : 1 < n)
    (payload : ConcurrentRetryOpened ring) :
    certificate.good payload ≠ certificate.restore payload := by
  classical
  by_cases hConstantChild : ∃ edge,
      Constant (certificate.step payload.configuration edge)
  · have hrestoreEq : certificate.restore payload =
        Classical.choose hConstantChild := by
      simp [ConcurrentChoiceRetryCertificate.restore, hConstantChild]
    rw [hrestoreEq]
    intro heq
    apply certificate.good_not_constant payload
    rw [heq]
    exact Classical.choose_spec hConstantChild
  · have hrestoreEq : certificate.restore payload =
        P.physicalRing.rightNeighbor (certificate.good payload) := by
      simp [ConcurrentChoiceRetryCertificate.restore, hConstantChild]
    rw [hrestoreEq]
    exact (rightNeighbor_ne P.physicalRing hn
      (certificate.good payload)).symm

theorem ConcurrentChoiceRetryCertificate.other_not_constant
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    (certificate : ConcurrentChoiceRetryCertificate ring P)
    (payload : ConcurrentRetryOpened ring) (edge : Fin n)
    (hrestore : edge ≠ certificate.restore payload) :
    ¬ Constant (certificate.step payload.configuration edge) := by
  classical
  by_cases hConstantChild : ∃ candidateEdge,
      Constant (certificate.step payload.configuration candidateEdge)
  · intro hedgeConstant
    have hchosen := Classical.choose_spec hConstantChild
    have hedge := certificate.constantChildrenUnique payload edge
      (Classical.choose hConstantChild) hedgeConstant hchosen
    have hrestoreEq : certificate.restore payload =
        Classical.choose hConstantChild := by
      simp [ConcurrentChoiceRetryCertificate.restore, hConstantChild]
    apply hrestore
    exact hedge.trans hrestoreEq.symm
  · intro hedgeConstant
    exact hConstantChild ⟨edge, hedgeConstant⟩

/-- The atomic choice certificate induces the concurrent Bellman envelope. -/
noncomputable def ConcurrentChoiceRetryCertificate.concurrentSpec
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    (certificate : ConcurrentChoiceRetryCertificate ring P) (hn : 1 < n) :
    ConcurrentRetrySpec
      (ConcurrentRetryBase ring) (ConcurrentRetryOpened ring) n where
  step := certificate.stoppedStep
  launch := certificate.launch
  good := certificate.good
  restore := certificate.restore
  good_ne_restore := certificate.good_ne_restore hn
  launch_opens := by
    intro payload
    apply classifyConcurrentChoice_eq_opened
    · exact certificate.launchNoCandidate payload
    · exact certificate.launchNotConstant payload
  good_succeeds := by
    intro payload
    apply classifyConcurrentChoice_eq_success
    exact certificate.goodCreates payload
  other_opened := by
    intro payload edge hgood hrestore
    let next := certificate.step payload.configuration edge
    have hnonRace := certificate.preservesNonRace
      payload.configuration edge payload.hasNonRace
    by_cases hCandidate : ∃ i, Candidate10 ring next i
    · left
      exact classifyConcurrentChoice_eq_success ring next hnonRace hCandidate
    · right
      have hnoCandidate : ∀ i, ¬ Candidate10 ring next i := by
        intro i hi
        exact hCandidate ⟨i, hi⟩
      exact classifyConcurrentChoice_eq_opened ring next hnonRace
        hnoCandidate (certificate.other_not_constant payload edge hrestore)
  never_fails := by
    intro state edge
    cases state with
    | base payload =>
        exact classifyConcurrentChoice_ne_failure ring
          (certificate.step payload.configuration edge)
          (certificate.preservesNonRace payload.configuration edge
            payload.hasNonRace)
    | opened payload =>
        exact classifyConcurrentChoice_ne_failure ring
          (certificate.step payload.configuration edge)
          (certificate.preservesNonRace payload.configuration edge
            payload.hasNonRace)

theorem ConcurrentChoiceRetryCertificate.base_truncatedCost_le
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    (certificate : ConcurrentChoiceRetryCertificate ring P) (hn : 1 < n)
    (payload : ConcurrentRetryBase ring) (T : Nat) :
    truncatedActiveCostNumerator certificate.stoppedStep
        (.active (.base payload)) T ≤ n ^ T * (3 * n) :=
  (certificate.concurrentSpec hn).base_truncatedCost_le payload T

theorem ConcurrentChoiceRetryCertificate.base_success_half_by_six_mul
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    (certificate : ConcurrentChoiceRetryCertificate ring P) (hn : 1 < n)
    (payload : ConcurrentRetryBase ring) :
    n ^ (6 * n) ≤
      2 * successCount certificate.stoppedStep
        (.active (.base payload)) (6 * n) :=
  (certificate.concurrentSpec hn).base_success_half_by_six_mul payload

theorem ConcurrentDispatcherProgress.base_truncatedCost_le
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    {dispatcher : ConcurrentDispatcher n m}
    (progress : ConcurrentDispatcherProgress ring P dispatcher)
    (hm : 1 < m) (hn : 1 < n)
    (payload : ConcurrentRetryBase ring) (T : Nat) :
    truncatedActiveCostNumerator
        (progress.choiceCertificate hm).stoppedStep
        (.active (.base payload)) T ≤ n ^ T * (3 * n) :=
  (progress.choiceCertificate hm).base_truncatedCost_le hn payload T

theorem ConcurrentDispatcherProgress.base_success_half_by_six_mul
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    {dispatcher : ConcurrentDispatcher n m}
    (progress : ConcurrentDispatcherProgress ring P dispatcher)
    (hm : 1 < m) (hn : 1 < n)
    (payload : ConcurrentRetryBase ring) :
    n ^ (6 * n) ≤
      2 * successCount (progress.choiceCertificate hm).stoppedStep
        (.active (.base payload)) (6 * n) :=
  (progress.choiceCertificate hm).base_success_half_by_six_mul hn payload

/-! ## Uniform retry after a constant frozen word -/

/-- Exact physical classification of one opened uniform retry. -/
structure RetryPortCertificate {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (base : FrozenValue) where
  configuration : Configuration m
  goodPort : Fin n
  restorePort : Fin n
  ports_ne : goodPort ≠ restorePort
  good_creates : CreatesCandidate ring P configuration goodPort
  restore_restores : RestoresBase base P configuration restorePort
  other_stutters : ∀ edge, edge ≠ goodPort → edge ≠ restorePort →
    incidenceStep P configuration edge = configuration

/-- Uniform scheduler skeleton obtained once a literal carrier supplies one
persistent launch port for this retry certificate. -/
def RetryPortCertificate.renewalSpec
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    {base : FrozenValue} (certificate : RetryPortCertificate ring P base)
    (launchPort : Fin n) : RetryRenewalSpec Unit n where
  launch := fun _ => launchPort
  good := fun _ => certificate.goodPort
  restore := fun _ => certificate.restorePort
  good_ne_restore := fun _ => certificate.ports_ne
  nextBase := fun _ _ => ()
  nextOpened := fun _ _ => ()

theorem RetryPortCertificate.renewal_truncatedCost_le
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    {base : FrozenValue} (certificate : RetryPortCertificate ring P base)
    (launchPort : Fin n) (T : Nat) :
    truncatedActiveCostNumerator
        (certificate.renewalSpec launchPort).stoppedStep
        (.active (.base ())) T ≤ n ^ T * (3 * n) :=
  (certificate.renewalSpec launchPort).base_truncatedCost_le () T

theorem RetryPortCertificate.renewal_success_half_by_six_mul
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    {base : FrozenValue} (certificate : RetryPortCertificate ring P base)
    (launchPort : Fin n) :
    n ^ (6 * n) ≤ 2 * successCount
      (certificate.renewalSpec launchPort).stoppedStep
      (.active (.base ())) (6 * n) :=
  (certificate.renewalSpec launchPort).base_success_half_by_six_mul ()

/-- Uniform `00`: reopen the clockwise endpoint.  Its outgoing port is good
and its incoming port restores `00`. -/
def uniformIn0RetryCertificate
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (selected : Fin m) :
    RetryPortCertificate ring P .in0 := by
  let target := ring.rightNeighbor selected
  refine
    { configuration := retryStep ring (fun _ => .in0) selected
      goodPort := P.root target
      restorePort := P.physicalRing.leftNeighbor (P.root target)
      ports_ne := P.root_ne_incomingEdge hn target
      good_creates := ?_
      restore_restores := ?_
      other_stutters := ?_ }
  · simpa [target] using
      uniform_in0_retry_outgoing_createsCandidate ring hm P selected
  · simpa [target] using
      uniform_in0_retry_incoming_restoresBase ring P hn selected
  · intro edge notGood notRestore
    apply incidenceStep_eq_self_of_uniqueRace_off_ports P _ target
    · simp [retryStep, target]
    · intro i hi
      simp [retryStep, target, hi]
    · exact notGood
    · exact notRestore

/-- Uniform `11`: reopen the counterclockwise endpoint.  Its incoming port is
good and its outgoing port restores `11`. -/
def uniformOut1RetryCertificate
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (selected : Fin m) :
    RetryPortCertificate ring P .out1 := by
  refine
    { configuration := retryStep ring (fun _ => .out1) selected
      goodPort := P.physicalRing.leftNeighbor (P.root selected)
      restorePort := P.root selected
      ports_ne := (P.root_ne_incomingEdge hn selected).symm
      good_creates :=
        uniform_out1_retry_incoming_createsCandidate ring hm P hn selected
      restore_restores :=
        uniform_out1_retry_outgoing_restoresBase ring P selected
      other_stutters := ?_ }
  intro edge notGood notRestore
  apply incidenceStep_eq_self_of_uniqueRace_off_ports P _ selected
  · simp [retryStep]
  · intro i hi
    simp [retryStep, hi]
  · exact notRestore
  · exact notGood

/-- Stop at the first classified port.  Good is success, uniform restoration
is failure, and all other physical edges retain the same retry state. -/
def RetryPortCertificate.stoppedStep
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    {base : FrozenValue} (_certificate : RetryPortCertificate ring P base) :
    Unit → Fin n → StopNode Unit :=
  twoTargetStep
    (fun _ => _certificate.goodPort)
    (fun _ => _certificate.restorePort)
    (fun _ _ => ())

/-- The two possible first-hit outcomes have equal exact scheduler-word count
at every finite horizon. -/
theorem RetryPortCertificate.firstGood_eq_firstRestore
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    {base : FrozenValue} (certificate : RetryPortCertificate ring P base)
    (T : Nat) :
    successCount certificate.stoppedStep (.active ()) T =
      failureCount certificate.stoppedStep (.active ()) T := by
  simpa [RetryPortCertificate.stoppedStep] using
    (twoTarget_successCount_eq_failureCount
      (fun _ : Unit => certificate.goodPort)
      (fun _ : Unit => certificate.restorePort)
      (fun _ _ => ()) (fun _ => certificate.ports_ne) () T)

/-- Division-free truncated expectation statement: twice the active-cost
numerator is at most `n` times the scheduler-space denominator. -/
theorem RetryPortCertificate.two_mul_truncatedCost_le
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    {base : FrozenValue} (certificate : RetryPortCertificate ring P base)
    (T : Nat) :
    2 * truncatedActiveCostNumerator certificate.stoppedStep
        (.active ()) T <= n ^ T * n := by
  simpa [RetryPortCertificate.stoppedStep] using
    (twoTarget_two_mul_truncatedCost_le
      (fun _ : Unit => certificate.goodPort)
      (fun _ : Unit => certificate.restorePort)
      (fun _ _ => ()) (fun _ => certificate.ports_ne) () T)

/-- By `2n` raw scheduler interactions, at least three eighths of all words
have created the persistent candidate before restoring the uniform base. -/
theorem RetryPortCertificate.firstGood_three_eighths_by_two_mul
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    {base : FrozenValue} (certificate : RetryPortCertificate ring P base) :
    3 * n ^ (2 * n) <=
      8 * successCount certificate.stoppedStep (.active ()) (2 * n) := by
  simpa [RetryPortCertificate.stoppedStep] using
    (twoTarget_first_success_three_eighths_by_two_mul
      (fun _ : Unit => certificate.goodPort)
      (fun _ : Unit => certificate.restorePort)
      (fun _ _ => ()) (fun _ => certificate.ports_ne) ())

/-- Quarter-strength interface convenient for state-uniform block
composition. -/
theorem RetryPortCertificate.firstGood_quarter_by_two_mul
    {n m : Nat} {ring : DirectedRing m} {P : Placement n m}
    {base : FrozenValue} (certificate : RetryPortCertificate ring P base) :
    n ^ (2 * n) <=
      4 * successCount certificate.stoppedStep (.active ()) (2 * n) := by
  simpa [RetryPortCertificate.stoppedStep] using
    (twoTarget_first_success_quarter_by_two_mul
      (fun _ : Unit => certificate.goodPort)
      (fun _ : Unit => certificate.restorePort)
      (fun _ _ => ()) (fun _ => certificate.ports_ne) ())

end ShortGapChoiceStopping

#print axioms ShortGapChoiceStopping.uniformIn0RetryCertificate
#print axioms ShortGapChoiceStopping.uniformOut1RetryCertificate
#print axioms ShortGapChoiceStopping.raceDrainStep_eq_success_iff
#print axioms ShortGapChoiceStopping.raceDrainStep_eq_success_iff_frozen
#print axioms ShortGapChoiceStopping.frozen_candidate_or_uniform
#print axioms ShortGapChoiceStopping.raceDrain_natBellmanSuperSolution
#print axioms ShortGapChoiceStopping.raceDrain_truncatedCost_le
#print axioms ShortGapChoiceStopping.raceDrain_success_half_by_two_mul
#print axioms ShortGapChoiceStopping.allRace_truncatedCost_le
#print axioms ShortGapChoiceStopping.allRace_success_half_by_two_mul
#print axioms ShortGapChoiceStopping.allRace_incidence_frozen_hasCandidate
#print axioms ShortGapChoiceStopping.candidateDrain_localBalance
#print axioms ShortGapChoiceStopping.candidateDrain_natBellmanSuperSolution
#print axioms ShortGapChoiceStopping.candidateDrain_failureCount_le_successCount
#print axioms ShortGapChoiceStopping.allRace_candidateDrain_truncatedCost_le
#print axioms ShortGapChoiceStopping.allRace_candidateDrain_success_quarter_by_two_mul
#print axioms ShortGapChoiceStopping.CandidateRearmSpec.restart_natBellmanSuperSolution
#print axioms ShortGapChoiceStopping.CandidateRearmSpec.allRace_truncatedCost_le
#print axioms ShortGapChoiceStopping.CandidateRearmSpec.allRace_failureCount_eq_zero
#print axioms ShortGapChoiceStopping.CandidateRearmSpec.allRace_factor_mul_activeCount_le_pow
#print axioms ShortGapChoiceStopping.CandidateRearmSpec.allRace_success_one_minus_inv_factor
#print axioms ShortGapChoiceStopping.RetryRenewalSpec.natBellmanSuperSolution
#print axioms ShortGapChoiceStopping.RetryRenewalSpec.base_truncatedCost_le
#print axioms ShortGapChoiceStopping.RetryRenewalSpec.base_success_half_by_six_mul
#print axioms ShortGapChoiceStopping.ConcurrentRetrySpec.natBellmanSuperSolution
#print axioms ShortGapChoiceStopping.ConcurrentRetrySpec.base_truncatedCost_le
#print axioms ShortGapChoiceStopping.ConcurrentRetrySpec.base_success_half_by_six_mul
#print axioms ShortGapChoiceStopping.RankedConcurrentRetrySpec.natBellmanSuperSolution
#print axioms ShortGapChoiceStopping.RankedConcurrentRetrySpec.base_truncatedCost_le
#print axioms ShortGapChoiceStopping.RankedConcurrentRetrySpec.base_success_half_by_two_mul
#print axioms ShortGapChoiceStopping.ConcurrentDispatcherProgress.choiceCertificate
#print axioms ShortGapChoiceStopping.ConcurrentDispatcherProgress.base_truncatedCost_le
#print axioms ShortGapChoiceStopping.ConcurrentDispatcherProgress.base_success_half_by_six_mul
#print axioms ShortGapChoiceStopping.RetryPortCertificate.renewal_truncatedCost_le
#print axioms ShortGapChoiceStopping.RetryPortCertificate.renewal_success_half_by_six_mul
#print axioms ShortGapChoiceStopping.RetryPortCertificate.firstGood_eq_firstRestore
#print axioms ShortGapChoiceStopping.RetryPortCertificate.two_mul_truncatedCost_le
#print axioms ShortGapChoiceStopping.RetryPortCertificate.firstGood_three_eighths_by_two_mul
#print axioms ShortGapChoiceStopping.RetryPortCertificate.firstGood_quarter_by_two_mul
