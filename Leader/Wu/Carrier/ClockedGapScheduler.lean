import Leader.Core.SymmetricKilledWalkFiniteTree

/-!
# Clocked current-certificate scheduler interface

Successive commits of the current multi-corridor table are not iid.  This file
states the smaller physical fact needed for a symmetric tagged-gap Bellman
argument.  A state carries one fixed proof-side tagged rear/front pair and its
current certificates.  Before adjacency or support drop, the rear certificate
has one current physical target, the front certificate has a distinct current
target, and every other raw edge either preserves the tagged gap or terminates
successfully because support already dropped.

The interface includes every `Fin n` child.  Thus a physical producer must
check internal corridor edges, the predecessor/source boundary, and the
target/successor boundary under one fixed cut; it may not choose a new owner or
cut after seeing the child.  The current repository does not yet supply the
literal clock-padding, target-distinctness, or collision-hold transition
lemmas.  They are fields below, not conclusions inferred from QMAT rank.
-/

namespace PPLLClockedBarrierScheduler

open FiniteUniformStoppingTree
open SymmetricKilledWalkFiniteTree

set_option autoImplicit false
set_option warningAsError true

/-- Required number of current-target services in the proposed padded barrier
program.  The coordinate is proof data; no `Fin (barrierClockLen h)` field is
added to the packed cell. -/
def barrierClockLen (h : Nat) : Nat := 8 * (h + 1)

/-- A literal physical tagged-gap kernel.  The three shape fields are the
transition-table obligations.  Terminal success means an earlier support drop;
terminal failure is permitted only on the front target at the upper trial
endpoint. -/
structure ClockedGapInterface (Physical : Type) (n L : Nat) where
  step : Physical → Fin n → StopNode Physical
  gap : Physical → Nat
  rearTarget : Physical → Fin n
  frontTarget : Physical → Fin n
  edge_count : 2 ≤ n
  gap_pos : ∀ state, 1 ≤ gap state
  gap_lt : ∀ state, gap state < L
  targets_ne : ∀ state, rearTarget state ≠ frontTarget state
  rear_shape : ∀ state,
    step state (rearTarget state) = .success ∨
      ∃ next, step state (rearTarget state) = .active next ∧
        gap next = gap state - 1
  front_shape : ∀ state,
    step state (frontTarget state) = .success ∨
      (step state (frontTarget state) = .failure ∧
        gap state + 1 = L) ∨
      ∃ next, step state (frontTarget state) = .active next ∧
        gap next = gap state + 1
  other_shape : ∀ state raw,
    raw ≠ rearTarget state → raw ≠ frontTarget state →
      step state raw = .success ∨
        ∃ next, step state raw = .active next ∧ gap next = gap state

/-- The current-certificate shape is exactly the existing symmetric killed
walk interface on the raw `n`-ary physical scheduler tree. -/
def ClockedGapInterface.toKilledWalkSpec
    {Physical : Type} {n L : Nat}
    (clock : ClockedGapInterface Physical n L) :
    SymmetricKilledWalkFiniteTree.Spec Physical n L where
  step := clock.step
  coord := clock.gap
  downEdge := clock.rearTarget
  upEdge := clock.frontTarget
  edge_count := clock.edge_count
  coord_pos := clock.gap_pos
  coord_lt := clock.gap_lt
  edges_ne := clock.targets_ne
  down_coord := by
    intro state
    rcases clock.rear_shape state with hsuccess | ⟨next, hnext, hgap⟩
    · simp [endpointCoord, hsuccess]
    · simp [endpointCoord, hnext, hgap]
  up_coord := by
    intro state
    rcases clock.front_shape state with hsuccess |
        ⟨hfailure, hend⟩ | ⟨next, hnext, hgap⟩
    · simp [endpointCoord, hsuccess]
    · simp [endpointCoord, hfailure, hend]
    · simp [endpointCoord, hnext, hgap]
  frame_coord := by
    intro state raw hrear hfront
    rcases clock.other_shape state raw hrear hfront with
      hsuccess | ⟨next, hnext, hgap⟩
    · simp [endpointCoord, hsuccess]
    · simp [endpointCoord, hnext, hgap]
  down_concave := by
    intro state
    rcases clock.rear_shape state with hsuccess | ⟨next, hnext, hgap⟩
    · simp [endpointConcave, hsuccess]
    · simp [endpointConcave, hnext, hgap]
  up_concave := by
    intro state
    rcases clock.front_shape state with hsuccess |
        ⟨hfailure, _⟩ | ⟨next, hnext, hgap⟩
    · simp [endpointConcave, hsuccess]
    · simp [endpointConcave, hfailure]
    · simp [endpointConcave, hnext, hgap]
  frame_concave := by
    intro state raw hrear hfront
    rcases clock.other_shape state raw hrear hfront with
      hsuccess | ⟨next, hnext, hgap⟩
    · simp [endpointConcave, hsuccess]
    · simp [endpointConcave, hnext, hgap]

/-- Exact raw child-sum Bellman inequality.  Nominally there is one `q-1`
child, one `q+1` child, and `n-2` stutters; early support-drop children only
decrease the left side. -/
theorem clockedGap_child_sum
    {Physical : Type} {n L : Nat}
    (clock : ClockedGapInterface Physical n L) (state : Physical) :
    2 + (List.ofFn (fun raw : Fin n ↦
      endpointConcave clock.gap L (clock.step state raw))).sum ≤
        n * concave L (clock.gap state) :=
  concave_child_sum_add_two_le clock.toKilledWalkSpec state

/-- Every-horizon raw physical duration for one tagged-gap trial. -/
theorem clockedGap_truncatedCost_mul_two_le
    {Physical : Type} {n L : Nat}
    (clock : ClockedGapInterface Physical n L)
    (state : Physical) (T : Nat) :
    2 * truncatedActiveCostNumerator clock.step (.active state) T ≤
      n ^ T * (n * concave L (clock.gap state)) :=
  duration_mul_two_le clock.toKilledWalkSpec state T

/-- Public proof-side coalescence budget proposed after the endpoint-retaining
restart/collision-hold composition.  This definition does not assert that the
current physical table supplies that composition. -/
def clockedCoalescenceBudget (n h m : Nat) : Nat :=
  4 * n * barrierClockLen h ^ 2 * m ^ 2

theorem clockedCoalescenceBudget_eq (n h m : Nat) :
    clockedCoalescenceBudget n h m =
      256 * n * (h + 1) ^ 2 * m ^ 2 := by
  simp only [clockedCoalescenceBudget, barrierClockLen, Nat.pow_two]
  rw [show 4 * n * (8 * (h + 1) * (8 * (h + 1))) * (m * m) =
      256 * n * ((h + 1) * (h + 1)) * (m * m) by
    rw [show 256 = 4 * 8 * 8 by decide]
    ac_rfl]

/-- Exact cubic envelope under `n = h*m`. -/
theorem clockedCoalescenceBudget_le_cube
    {n h m : Nat} (hh : 0 < h) (hfactor : h * m = n) :
    clockedCoalescenceBudget n h m ≤ 1024 * n ^ 3 := by
  have hlinear : h + 1 ≤ 2 * h := by omega
  have hsquare : (h + 1) ^ 2 ≤ (2 * h) ^ 2 :=
    Nat.pow_le_pow_left hlinear 2
  rw [clockedCoalescenceBudget_eq]
  calc
    256 * n * (h + 1) ^ 2 * m ^ 2 ≤
        256 * n * (2 * h) ^ 2 * m ^ 2 :=
      Nat.mul_le_mul_right (m ^ 2)
        (Nat.mul_le_mul_left (256 * n) hsquare)
    _ = 1024 * n * (h * m) ^ 2 := by
      simp only [Nat.pow_two]
      rw [show 1024 = 256 * 4 by decide]
      ac_rfl
    _ = 1024 * n ^ 3 := by
      rw [hfactor]
      simp only [Nat.pow_succ]
      ac_rfl

#print axioms ClockedGapInterface.toKilledWalkSpec
#print axioms clockedGap_child_sum
#print axioms clockedGap_truncatedCost_mul_two_le
#print axioms clockedCoalescenceBudget_le_cube

end PPLLClockedBarrierScheduler
