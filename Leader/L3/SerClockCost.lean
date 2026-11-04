import Leader.L3.SerClock
import Leader.L3.ProbStages

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-!
Finite-horizon and expectation bridge for the physical
serializer S1-or-lost-root stopping kernel.

The original SerClock.lean is not modified. All edges remain
the actual uniform Fin n scheduler edges.
-/

/-- The scaled finite-horizon estimate at every stopped node.
    The nonterminal Bellman premise was proved in SerClock.lean. -/
theorem clockSerializerStoppedCostAtRank {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 4 ≤ n) (x : ClockSerializerStopNode n c) (T : Nat) :
    costNumerator (clockSerializerStoppedNext ring root)
      clockSerializerIsStopped x T ≤
      n ^ T * (n * clockSerializerStoppedRank ring root x) := by
  exact Prob.costNumerator_le_of_potential
    (clockSerializerStoppedNext ring root)
    clockSerializerIsStopped
    (fun y : ClockSerializerStopNode n c =>
      n * clockSerializerStoppedRank ring root y)
    (fun y hnot =>
      clockSerializerStoppedNonterminalDrift ring root hn y hnot)
    x T

/-- Uniform n(5n-4) first-hit cost for every stopped node.
    This stronger statement also covers every WFixedRoot entrance. -/
theorem clockSerializerStoppedCostBound {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 4 ≤ n) (x : ClockSerializerStopNode n c) (T : Nat) :
    costNumerator (clockSerializerStoppedNext ring root)
      clockSerializerIsStopped x T ≤
      n ^ T * (n * (5 * n - 4)) := by
  calc
    costNumerator (clockSerializerStoppedNext ring root)
        clockSerializerIsStopped x T ≤
      n ^ T * (n * clockSerializerStoppedRank ring root x) :=
        clockSerializerStoppedCostAtRank ring root hn x T
    _ ≤ n ^ T * (n * (5 * n - 4)) :=
      Nat.mul_le_mul_left (n ^ T)
        (Nat.mul_le_mul_left n
          (clockSerializerStoppedRankCap ring root hn x))

/-- Requested fixed-root entry form of the finite-horizon bound. -/
theorem clockSerializerStoppedCostFromFixedRoot
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (hn : 4 ≤ n)
    (hfixed : WFixedRoot ring root s) :
    ∀ T : Nat,
      costNumerator (clockSerializerStoppedNext ring root)
        clockSerializerIsStopped
        (.active s : ClockSerializerStopNode n c) T ≤
      n ^ T * (n * (5 * n - 4)) := by
  have hdomain : clockSerializerStoppedDomain ring root
      (.active s : ClockSerializerStopNode n c) := hfixed
  intro T
  exact clockSerializerStoppedCostBound ring root hn (.active s) T

/-- Exact uniform IID expected first-hit bound for the absorbing
    physical S1-or-lost-root stopped kernel. -/
theorem clockSerializerStoppedExpected {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (hn : 4 ≤ n)
    (hfixed : WFixedRoot ring root s) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (clockSerializerStoppedNext ring root)
      clockSerializerIsStopped
      (.active s : ClockSerializerStopNode n c)
      ((n * (5 * n - 4) : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (clockSerializerStoppedNext ring root)
    clockSerializerIsStopped (by omega : 0 < n)
    (.active s : ClockSerializerStopNode n c)
    (n * (5 * n - 4))).2
  exact clockSerializerStoppedCostFromFixedRoot
    ring root s hn hfixed

/-!
The S1-only comparison uses a genuinely distinct stopped kernel:
unlike clockSerializerStoppedNext, it continues after a would-be
lost-root event. The named G closure eliminates that difference
along all trajectories starting in G.
-/

/-- Stop exactly on a physical S1 service, not on a lost-root exit. -/
noncomputable def clockSerializerSOneOnlyNext
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (x : ClockSerializerStopNode n c) (e : Fin n) :
    ClockSerializerStopNode n c := by
  classical
  cases x with
  | stopped =>
    exact .stopped
  | active s =>
    exact if clockSerializerSOneService ring root s e
      then .stopped
      else .active (phiW ring s e)

/-- The new kernel reaches its stop on a live edge iff that edge
    executes the S1 row, with no additional lost-root discriminator. -/
theorem clockSerializerSOneOnlyStopIff {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n) :
    clockSerializerIsStopped
      (clockSerializerSOneOnlyNext ring root
        (.active s : ClockSerializerStopNode n c) e) ↔
      clockSerializerSOneService ring root s e := by
  classical
  by_cases hs : clockSerializerSOneService ring root s e
  · simp [clockSerializerSOneOnlyNext,
      clockSerializerIsStopped, hs]
  · simp [clockSerializerSOneOnlyNext,
      clockSerializerIsStopped, hs]

/-- Lift the closure invariant to the common stopped state space. -/
def clockSerializerGLifted {n : Nat} {c : Compiled}
    (G : (Fin n → ProjW c) → Prop) :
    ClockSerializerStopNode n c → Prop
  | .stopped => True
  | .active s => G s

/-- On the named closure domain, stopping only for S1 and stopping
    for S1-or-lost-root are exactly the same physical update. -/
theorem clockSerializerSOneNextEqOnG {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (G : (Fin n → ProjW c) → Prop)
    (hG : ClockSerializerNoRootLossFromG ring root G)
    (x : ClockSerializerStopNode n c)
    (hx : clockSerializerGLifted G x) (e : Fin n) :
    clockSerializerSOneOnlyNext ring root x e =
      clockSerializerStoppedNext ring root x e := by
  classical
  cases x with
  | stopped =>
    rfl
  | active s =>
    have hs : G s := hx
    have heq := clockSerializerStopEventAtG
      ring root G hG s hs e
    by_cases hSOne : clockSerializerSOneService ring root s e
    · have hExit : clockSerializerExitService ring root s e :=
        heq.mpr hSOne
      simp [clockSerializerSOneOnlyNext,
        clockSerializerStoppedNext, hSOne, hExit]
    · have hNoExit : ¬ clockSerializerExitService ring root s e := by
        intro he
        exact hSOne (heq.mp he)
      simp [clockSerializerSOneOnlyNext,
        clockSerializerStoppedNext, hSOne, hNoExit]

/-- The common stopped kernel preserves the lifted G domain. -/
theorem clockSerializerGLiftedNext {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (G : (Fin n → ProjW c) → Prop)
    (hG : ClockSerializerNoRootLossFromG ring root G)
    (x : ClockSerializerStopNode n c)
    (hx : clockSerializerGLifted G x) (e : Fin n) :
    clockSerializerGLifted G
      (clockSerializerStoppedNext ring root x e) := by
  classical
  cases x with
  | stopped =>
    simp [clockSerializerStoppedNext, clockSerializerGLifted]
  | active s =>
    have hs : G s := hx
    by_cases he : clockSerializerExitService ring root s e
    · simp [clockSerializerStoppedNext,
        clockSerializerGLifted, he]
    · have hnext : G (phiW ring s e) := (hG.2 s hs e).1
      simpa [clockSerializerStoppedNext,
        clockSerializerGLifted, he] using hnext

/-- The finite-horizon first-hit cost is identical for the S1-only
    and S1-or-lost-root kernels at every G-reachable stopped state. -/
theorem clockSerializerSOneCostEqOnG {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (G : (Fin n → ProjW c) → Prop)
    (hG : ClockSerializerNoRootLossFromG ring root G)
    (x : ClockSerializerStopNode n c)
    (hx : clockSerializerGLifted G x) (T : Nat) :
    costNumerator (clockSerializerSOneOnlyNext ring root)
      clockSerializerIsStopped x T =
    costNumerator (clockSerializerStoppedNext ring root)
      clockSerializerIsStopped x T := by
  classical
  have hmain : ∀ (t : Nat) (y : ClockSerializerStopNode n c),
      clockSerializerGLifted G y →
      costNumerator (clockSerializerSOneOnlyNext ring root)
        clockSerializerIsStopped y t =
      costNumerator (clockSerializerStoppedNext ring root)
        clockSerializerIsStopped y t := by
    intro t
    induction t with
    | zero =>
      intro y _
      simp only [costNumerator_zero]
    | succ t ih =>
      intro y hy
      by_cases hterminal : clockSerializerIsStopped y
      · rw [costNumerator_terminal
          (clockSerializerSOneOnlyNext ring root)
          clockSerializerIsStopped y hterminal (t + 1),
        costNumerator_terminal
          (clockSerializerStoppedNext ring root)
          clockSerializerIsStopped y hterminal (t + 1)]
      · rw [costNumerator_succ
          (clockSerializerSOneOnlyNext ring root)
          clockSerializerIsStopped y hterminal t,
        costNumerator_succ
          (clockSerializerStoppedNext ring root)
          clockSerializerIsStopped y hterminal t]
        have hsum :
            (List.ofFn (fun e : Fin n =>
              costNumerator (clockSerializerSOneOnlyNext ring root)
                clockSerializerIsStopped
                (clockSerializerSOneOnlyNext ring root y e) t)).sum =
            (List.ofFn (fun e : Fin n =>
              costNumerator (clockSerializerStoppedNext ring root)
                clockSerializerIsStopped
                (clockSerializerStoppedNext ring root y e) t)).sum := by
          apply ofFn_sum_eq
          intro e
          rw [clockSerializerSOneNextEqOnG
            ring root G hG y hy e]
          exact ih (clockSerializerStoppedNext ring root y e)
            (clockSerializerGLiftedNext ring root G hG y hy e)
        exact congrArg (fun z : Nat => n ^ (t + 1) + z) hsum
  exact hmain T x hx

/-- Under the named G closure, the S1-only process has the same
    finite-horizon n(5n-4) bound, not merely an exit-time bound. -/
theorem clockSerializerSOneCostFromG {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (G : (Fin n → ProjW c) → Prop)
    (hG : ClockSerializerNoRootLossFromG ring root G)
    (s : Fin n → ProjW c) (hs : G s) (hn : 4 ≤ n) :
    ∀ T : Nat,
      costNumerator (clockSerializerSOneOnlyNext ring root)
        clockSerializerIsStopped
        (.active s : ClockSerializerStopNode n c) T ≤
      n ^ T * (n * (5 * n - 4)) := by
  intro T
  calc
    costNumerator (clockSerializerSOneOnlyNext ring root)
        clockSerializerIsStopped
        (.active s : ClockSerializerStopNode n c) T =
      costNumerator (clockSerializerStoppedNext ring root)
        clockSerializerIsStopped
        (.active s : ClockSerializerStopNode n c) T :=
      clockSerializerSOneCostEqOnG ring root G hG
        (.active s) hs T
    _ ≤ n ^ T * (n * (5 * n - 4)) :=
      clockSerializerStoppedCostFromFixedRoot
        ring root s hn (hG.1 s hs) T

/-- S1 alone: the same true uniform IID expected hitting-time bound
    under the separately named, externally supplied G closure. -/
theorem clockSerializerSOneExpectedFromG {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (G : (Fin n → ProjW c) → Prop)
    (hG : ClockSerializerNoRootLossFromG ring root G)
    (s : Fin n → ProjW c) (hs : G s) (hn : 4 ≤ n) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (clockSerializerSOneOnlyNext ring root)
      clockSerializerIsStopped
      (.active s : ClockSerializerStopNode n c)
      ((n * (5 * n - 4) : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (clockSerializerSOneOnlyNext ring root)
    clockSerializerIsStopped (by omega : 0 < n)
    (.active s : ClockSerializerStopNode n c)
    (n * (5 * n - 4))).2
  exact clockSerializerSOneCostFromG ring root G hG s hs hn

end L3
