import Leader.AAFJ.TwoBarrier.FiveServiceClock

/-!
# A two-endpoint physical service race

This module runs the accepted five-service clock at two fixed charged tags at
once.  The race stops as soon as either tag advances or first contacts a
charged neighbour.  Before that stopping time both endpoint debts remain in
their literal pre-contact carriers.  Adding the two one-endpoint Bellman rows
gives scale two: the expected truncated duration is at most `5*n`, and at
horizon `10*n` at least half of the scheduler words have stopped.

This is the clock component of the transported-gap walk.  It deliberately
stops at an endpoint advance; `ConsecutiveTransport` must update the physical
tag before a fresh race is started.
-/

set_option autoImplicit false

namespace AAFJPK.TwoEndpointServiceClock

open BarrierAlgebra
open PersistentBarrierService
open FiniteUniformStoppingTree

/-- Two distinct fixed charged tags, both strictly before contact. -/
structure ActivePair {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) where
  config : Fin n → State k
  rear : Fin n
  front : Fin n
  ne : rear ≠ front
  rearPre : PreContact hk ring config rear
  frontPre : PreContact hk ring config front

private def rearState {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (st : ActivePair hk ring) : PersistentBarrierClock.ActiveService hk ring :=
  { config := st.config, tag := st.rear, preContact := st.rearPre }

private def frontState {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (st : ActivePair hk ring) : PersistentBarrierClock.ActiveService hk ring :=
  { config := st.config, tag := st.front, preContact := st.frontPre }

/-- One literal scheduler interaction, stopped when either fixed tag leaves
its pre-contact carrier. -/
noncomputable def step {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (st : ActivePair hk ring) (e : Fin n) : StopNode (ActivePair hk ring) := by
  classical
  let D := (protocol k hk).step ring st.config e
  exact if hr : PreContact hk ring D st.rear then
    if hf : PreContact hk ring D st.front then
      .active
        { config := D
          rear := st.rear
          front := st.front
          ne := st.ne
          rearPre := hr
          frontPre := hf }
    else .success
  else .success

/-- A stopped child is a literal advance-or-contact event at one of the two
fixed endpoint tags. -/
theorem terminal_of_step_eq_success
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} (hn3 : 2 < n)
    (st : ActivePair hk ring) (e : Fin n) (hs : step st e = .success) :
    PersistentBarrierClock.ServiceTerminal hk ring st.config
        ((protocol k hk).step ring st.config e) st.rear e ∨
      PersistentBarrierClock.ServiceTerminal hk ring st.config
        ((protocol k hk).step ring st.config e) st.front e := by
  classical
  let D := (protocol k hk).step ring st.config e
  by_cases hr : PreContact hk ring D st.rear
  · by_cases hf : PreContact hk ring D st.front
    · have ha : step st e = .active
          { config := D
            rear := st.rear
            front := st.front
            ne := st.ne
            rearPre := hr
            frontPre := hf } := by
        simp [step, D, hr, hf]
      rw [ha] at hs
      contradiction
    · right
      exact PersistentBarrierClock.not_preContact_child_terminal
        hk ring hn3 st.config st.front e st.frontPre (by simpa [D] using hf)
  · left
    exact PersistentBarrierClock.not_preContact_child_terminal
      hk ring hn3 st.config st.rear e st.rearPre (by simpa [D] using hr)

/-- Sum of the two accepted physical service potentials. -/
def potential {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) :
    StopNode (ActivePair hk ring) → Nat
  | .active st =>
      PersistentBarrierClock.potential hk ring (.active (rearState st)) +
        PersistentBarrierClock.potential hk ring (.active (frontState st))
  | .success => 0
  | .failure => 0

private theorem child_potential_le_single_sum
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (st : ActivePair hk ring) (e : Fin n) :
    potential hk ring (step st e) ≤
      PersistentBarrierClock.potential hk ring (PersistentBarrierClock.step (rearState st) e) +
        PersistentBarrierClock.potential hk ring (PersistentBarrierClock.step (frontState st) e) := by
  classical
  let D := (protocol k hk).step ring st.config e
  by_cases hr : PreContact hk ring D st.rear
  · by_cases hf : PreContact hk ring D st.front
    · have hp : step st e = .active
          { config := D
            rear := st.rear
            front := st.front
            ne := st.ne
            rearPre := hr
            frontPre := hf } := by
        simp [step, D, hr, hf]
      have hrear : PersistentBarrierClock.step (rearState st) e = .active
          { config := D, tag := st.rear, preContact := hr } := by
        simp [PersistentBarrierClock.step, rearState, D, hr]
      have hfront : PersistentBarrierClock.step (frontState st) e = .active
          { config := D, tag := st.front, preContact := hf } := by
        simp [PersistentBarrierClock.step, frontState, D, hf]
      rw [hp, hrear, hfront]
      exact Nat.le_refl _
    · have hp : step st e = .success := by simp [step, D, hr, hf]
      rw [hp]
      simp [potential]
  · have hp : step st e = .success := by simp [step, D, hr]
    rw [hp]
    simp [potential]

/-- Adding the two endpoint rows yields two units of Bellman service per raw
interaction, even when the two predictable targets coincide. -/
theorem pair_natBellmanSuperSolution
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} (hn3 : 2 < n) :
    NatBellmanSuperSolution (step (hk := hk) (ring := ring)) 2
      (potential hk ring) := by
  refine ⟨rfl, rfl, ?_⟩
  intro st
  have hr := (PersistentBarrierClock.service_natBellmanSuperSolution
    (hk := hk) (ring := ring) hn3).2.2 (rearState st)
  have hf := (PersistentBarrierClock.service_natBellmanSuperSolution
    (hk := hk) (ring := ring) hn3).2.2 (frontState st)
  have hr' : n + (List.ofFn (fun e : Fin n =>
      PersistentBarrierClock.potential hk ring
        (PersistentBarrierClock.step (rearState st) e))).sum ≤
      n * PersistentBarrierClock.potential hk ring (.active (rearState st)) := by
    simpa using hr
  have hf' : n + (List.ofFn (fun e : Fin n =>
      PersistentBarrierClock.potential hk ring
        (PersistentBarrierClock.step (frontState st) e))).sum ≤
      n * PersistentBarrierClock.potential hk ring (.active (frontState st)) := by
    simpa using hf
  have hchildren :
      (List.ofFn (fun e : Fin n => potential hk ring (step st e))).sum ≤
        (List.ofFn (fun e : Fin n =>
          PersistentBarrierClock.potential hk ring (PersistentBarrierClock.step (rearState st) e) +
            PersistentBarrierClock.potential hk ring (PersistentBarrierClock.step (frontState st) e))).sum := by
    apply ofFn_sum_le
    intro e
    exact child_potential_le_single_sum st e
  rw [ofFn_sum_add] at hchildren
  change 2 * n +
      (List.ofFn (fun e : Fin n => potential hk ring (step st e))).sum ≤
    n * (PersistentBarrierClock.potential hk ring (.active (rearState st)) +
      PersistentBarrierClock.potential hk ring (.active (frontState st)))
  calc
    2 * n + (List.ofFn (fun e : Fin n =>
        potential hk ring (step st e))).sum ≤
        (n + (List.ofFn (fun e : Fin n =>
          PersistentBarrierClock.potential hk ring
            (PersistentBarrierClock.step (rearState st) e))).sum) +
        (n + (List.ofFn (fun e : Fin n =>
          PersistentBarrierClock.potential hk ring
            (PersistentBarrierClock.step (frontState st) e))).sum) := by
      omega
    _ ≤ n * PersistentBarrierClock.potential hk ring (.active (rearState st)) +
        n * PersistentBarrierClock.potential hk ring (.active (frontState st)) :=
      Nat.add_le_add hr' hf'
    _ = n * (PersistentBarrierClock.potential hk ring (.active (rearState st)) +
        PersistentBarrierClock.potential hk ring (.active (frontState st))) := by
      rw [Nat.mul_add]

/-- The two endpoint race potential is at most `10*n`. -/
theorem potential_le_ten_mul
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (st : ActivePair hk ring) : potential hk ring (.active st) ≤ 10 * n := by
  have hr := serviceDebt_le_five hk ring st.config st.rear
  have hf := serviceDebt_le_five hk ring st.config st.front
  simp only [potential, PersistentBarrierClock.potential, rearState, frontState]
  calc
    n * serviceDebt hk ring st.config st.rear +
          n * serviceDebt hk ring st.config st.front ≤ n * 5 + n * 5 :=
      Nat.add_le_add (Nat.mul_le_mul_left n hr) (Nat.mul_le_mul_left n hf)
    _ = 10 * n := by omega

/-- Every finite truncation has twice its active-duration numerator bounded
by `10*n` times the scheduler-space denominator. -/
theorem two_mul_truncatedCost_le_ten_mul
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} (hn3 : 2 < n)
    (st : ActivePair hk ring) (T : Nat) :
    2 * truncatedActiveCostNumerator step (.active st) T ≤
      n ^ T * (10 * n) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    step 2 (potential hk ring) (pair_natBellmanSuperSolution hn3)
    (.active st) T
  exact Nat.le_trans h
    (Nat.mul_le_mul_left _ (potential_le_ten_mul st))

/-- The two-endpoint stopped tree contains no failure leaves. -/
theorem failureCount_eq_zero
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} :
    ∀ (st : ActivePair hk ring) (T : Nat),
      failureCount step (.active st) T = 0 := by
  intro st T
  induction T generalizing st with
  | zero => rfl
  | succ T ih =>
      simp only [failureCount, treeWeight, stepNode]
      calc
        (List.ofFn (fun e : Fin n =>
            treeWeight step failureWeight (step st e) T)).sum =
            (List.ofFn (fun _ : Fin n => 0)).sum := by
              apply ofFn_sum_eq
              intro e
              cases hchild : step st e with
              | active next => simpa [failureCount] using ih next
              | success => simp [treeWeight_success, failureWeight]
              | failure =>
                  classical
                  have hne : step st e ≠ .failure := by
                    by_cases hr : PreContact hk ring
                        ((protocol k hk).step ring st.config e) st.rear
                    · by_cases hf : PreContact hk ring
                          ((protocol k hk).step ring st.config e) st.front
                      · simp [step, hr, hf]
                      · simp [step, hr, hf]
                    · simp [step, hr]
                  exact False.elim (hne hchild)
        _ = 0 := by rw [ofFn_sum_const]; simp

/-- By `10*n` raw interactions, at least half of the scheduler words have
served one endpoint to an actual advance-or-contact event. -/
theorem success_half_by_ten_mul
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} (hn3 : 2 < n)
    (st : ActivePair hk ring) :
    n ^ (10 * n) ≤ 2 * successCount step (.active st) (10 * n) := by
  let T := 10 * n
  let N := n ^ T
  let A := activeCount step (.active st) T
  have hcost := two_mul_truncatedCost_le_ten_mul hn3 st T
  have hlive := horizon_mul_activeCount_le_truncatedActiveCostNumerator
    step (.active st) T
  have hactive : 2 * A ≤ N := by
    have hscaled : (10 * n) * (2 * A) ≤ (10 * n) * N := by
      calc
        (10 * n) * (2 * A) = 2 * (T * A) := by dsimp [T]; ac_rfl
        _ ≤ 2 * truncatedActiveCostNumerator step (.active st) T :=
          Nat.mul_le_mul_left 2 hlive
        _ ≤ N * (10 * n) := by simpa [N] using hcost
        _ = (10 * n) * N := by ac_rfl
    exact Nat.le_of_mul_le_mul_left hscaled (by omega)
  have hpartition := node_count_partition step (.active st) T
  have hfailure := failureCount_eq_zero st T
  dsimp [A, N, T] at hactive hpartition hfailure ⊢
  rw [hfailure] at hpartition
  omega

#print axioms pair_natBellmanSuperSolution
#print axioms terminal_of_step_eq_success
#print axioms success_half_by_ten_mul

end AAFJPK.TwoEndpointServiceClock
