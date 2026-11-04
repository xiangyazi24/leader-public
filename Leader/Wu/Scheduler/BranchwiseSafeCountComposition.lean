import Leader.Wu.Scheduler.RepeatedBlocks

/-!
# Branchwise scheduler-count composition

An arbitrary-state repair need not enter a phase that simulates its consumer
on every later scheduler word.  For finite-horizon stabilization it is enough
that many entry prefixes each admit many successful continuations.  This file
states that weaker interface directly for Definition-1 safety and proves the
exact product lower bound on scheduler words.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace BranchwiseSafeCountCompositionSol

open PPLLResearchFormulation PPLLTraceConvergence PPLLSchedulerBlocks

set_option autoImplicit false

variable {n : Nat}

private theorem runSchedule_append
    (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (pre tail : DetSchedule n) :
    runSchedule P ring C (pre ++ tail) =
      runSchedule P ring (runSchedule P ring C pre) tail := by
  induction pre generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runSchedule]
      exact ih _

/-- A continuation that reaches Definition-1 safety after an entry prefix is
also successful as one concatenated scheduler word. -/
theorem reachesSafeWithinSchedule_append_of_tail
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (C : P.Configuration n)
    (pre tail : DetSchedule n)
    (h : ReachesSafeWithinSchedule P ring isLeader
      (runSchedule P ring C pre) tail) :
    ReachesSafeWithinSchedule P ring isLeader C (pre ++ tail) := by
  obtain ⟨k, hk, hsafe⟩ := h
  refine ⟨pre.length + k, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · have htake : (pre ++ tail).take (pre.length + k) =
        pre ++ tail.take k := by
      rw [List.take_append]
      rw [List.take_of_length_le (by omega : pre.length ≤ pre.length + k)]
      congr
      omega
    rw [htake, runSchedule_append]
    exact hsafe

private theorem countP_le_countP_of_true_imp
    {α : Type} (p q : α → Bool) (xs : List α)
    (himp : ∀ x, x ∈ xs → p x = true → q x = true) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : ∀ y, y ∈ xs → p y = true → q y = true := by
        intro y hy
        exact himp y (by simp [hy])
      have hi := ih htail
      rw [List.countP_cons, List.countP_cons]
      cases hp : p x with
      | false =>
          cases q x <;> simp_all <;> omega
      | true =>
          have hq : q x = true := himp x (by simp) hp
          simpa [hp, hq] using hi

private theorem weighted_countP_le_sum
    {α : Type} (selected : α → Bool) (weight : α → Nat)
    (xs : List α) (B : Nat)
    (hweight : ∀ x, x ∈ xs → selected x = true → B ≤ weight x) :
    B * xs.countP selected ≤ (xs.map weight).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : ∀ y, y ∈ xs → selected y = true → B ≤ weight y := by
        intro y hy
        exact hweight y (by simp [hy])
      have hi := ih htail
      rw [List.countP_cons, List.map_cons, List.sum_cons]
      cases hx : selected x with
      | false =>
          exact Nat.le_add_left_of_le hi
      | true =>
          have hxWeight : B ≤ weight x := hweight x (by simp) hx
          simp only [if_pos True.intro]
          rw [Nat.mul_add]
          rw [Nat.mul_one]
          calc
            B * List.countP selected xs + B ≤
                (xs.map weight).sum + weight x :=
              Nat.add_le_add hi hxWeight
            _ = weight x + (xs.map weight).sum := Nat.add_comm _ _

/-- Exact branchwise composition.  If at least `A` length-`a` entry words are
selected and every selected endpoint has at least `B` successful length-`b`
continuations, then at least `A*B` length-`a+b` words reach genuine semantic
safety.  No entry-domain closure or all-word simulation premise is used. -/
theorem stabilizingScheduleCount_add_lower_of_branchwise
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (C : P.Configuration n)
    (entryTest : DetSchedule n → Bool)
    (a b A B : Nat)
    (hentry : A ≤ (allSchedules n a).countP entryTest)
    (hcontinuation : ∀ pre, pre ∈ allSchedules n a →
      entryTest pre = true →
      B ≤ stabilizingScheduleCount P ring isLeader
        (runSchedule P ring C pre) b) :
    A * B ≤ stabilizingScheduleCount P ring isLeader C (a + b) := by
  classical
  unfold stabilizingScheduleCount
  rw [allSchedules_add, List.countP_flatMap]
  let success : DetSchedule n → Bool := fun word =>
    if ReachesSafeWithinSchedule P ring isLeader C word then true else false
  let continuation : DetSchedule n → DetSchedule n → Bool := fun pre tail =>
    if ReachesSafeWithinSchedule P ring isLeader
      (runSchedule P ring C pre) tail then true else false
  let chunkCount : DetSchedule n → Nat := fun pre =>
    ((allSchedules n b).map (fun tail => pre ++ tail)).countP success
  have hchunk : ∀ pre, pre ∈ allSchedules n a → entryTest pre = true →
      B ≤ chunkCount pre := by
    intro pre hpre hselected
    have htailCount : B ≤ (allSchedules n b).countP (continuation pre) := by
      simpa [continuation, stabilizingScheduleCount] using
        hcontinuation pre hpre hselected
    have hmap : (allSchedules n b).countP (continuation pre) ≤
        chunkCount pre := by
      unfold chunkCount
      rw [List.countP_map]
      apply countP_le_countP_of_true_imp
      intro tail htail hsuccess
      simp only [Function.comp_apply]
      have hreachTail : ReachesSafeWithinSchedule P ring isLeader
          (runSchedule P ring C pre) tail := by
        simpa [continuation] using hsuccess
      have hreach := reachesSafeWithinSchedule_append_of_tail
        P ring isLeader C pre tail hreachTail
      simp [success, hreach]
    exact Nat.le_trans htailCount hmap
  have hweighted :
      B * (allSchedules n a).countP entryTest ≤
        ((allSchedules n a).map chunkCount).sum :=
    weighted_countP_le_sum entryTest chunkCount
      (allSchedules n a) B hchunk
  have hAB : A * B ≤ B * (allSchedules n a).countP entryTest := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left B hentry
  exact Nat.le_trans hAB hweighted

#print axioms reachesSafeWithinSchedule_append_of_tail
#print axioms stabilizingScheduleCount_add_lower_of_branchwise

end BranchwiseSafeCountCompositionSol
end PPLLCompleteMultiLeaderCleanup
