import Leader.AAFJ.Centered.CoalescenceTrial
import Leader.Core.RestartingKilledWalkFiniteTree
import Leader.Core.InverseSquareLevelSum

/-!
# Fixed-level restart for centered AAFJ coalescence

`AAFJCenteredCoalescenceTrial` exposes the exact physical configuration at an
upper killed-walk exit.  This module performs the zero-time proof-local reseed
at the same support level and then feeds the resulting process to the generic
restart Bellman potential.

The common scale at support level `m` is

`Q = floor (2*n/m)`, `L = 2*Q`, `R = n*Q^2`.

Every retry chooses a minimum phase-corrected doubled gap in the unchanged
physical configuration.  Its coordinate is at most `Q`; hence one natural
Bellman certificate absorbs all failed trials without an infinite stopping
time or a geometric-series limit.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace CoalescenceRestart

open CoalescenceTrial
open FiniteUniformStoppingTree
open RestartingKilledWalkFiniteTree

set_option autoImplicit false

/-- Common half-width shared by all retries at support level `m`. -/
def commonScale (n m : Nat) : Nat := (2 * n) / m

/-- Restart account at one support level. -/
def levelBudget (n m : Nat) : Nat :=
  n * commonScale n m * commonScale n m

/-- The coordinate of the active state produced by a fixed-level seed is the
selected phase-corrected doubled cycle gap. -/
theorem fixedLevelSeed_active_coord {n k m Q : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {C : Config n k}
    (seed : FixedLevelSeed (m := m) hk ring C Q) (hm2 : 2 <= m) :
    Active.coord (seed.active hm2) = seed.cycle.doubledGap seed.index := by
  exact cycleGapAligned seed.cycle hm2 seed.index

/-- Convert the enriched killed-trial node into the global fixed-level node.
An upper failure becomes a fresh active proof state; its physical configuration
is not changed. -/
noncomputable def restartNode {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m) :
    KilledTrialNode hk ring hn2 m (2 * commonScale n m) ->
      StopNode (Active hk ring m (2 * commonScale n m))
  | .active state => .active state
  | .success => .success
  | .failure endpoint => .active (endpoint.restartedActive hm2)

/-- One literal physical interaction followed, only on an upper trial exit,
by a zero-time minimum-gap reseed in the same configuration. -/
noncomputable def restartedStep {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m)
    (state : Active hk ring m (2 * commonScale n m)) (selected : Fin n) :
    StopNode (Active hk ring m (2 * commonScale n m)) :=
  restartNode hk ring hn2 hm2
    (killedStepWithFailure hk ring hn2 state selected)

/-- Canonical initial proof state for an arbitrary physical configuration at
support level `m`. -/
noncomputable def initialActive {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hm2 : 2 <= m) (C : Config n k)
    (hcount : supportCount hk ring C = m) :
    Active hk ring m (2 * commonScale n m) :=
  (fixedLevelSeed hk ring C hm2 hcount).active hm2

@[simp] theorem initialActive_config {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hm2 : 2 <= m) (C : Config n k)
    (hcount : supportCount hk ring C = m) :
    (initialActive hk ring hm2 C hcount).config = C := rfl

/-- Every canonical initial or retry coordinate lies in the lower half of the
common interval. -/
theorem initialActive_coord_le {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hm2 : 2 <= m) (C : Config n k)
    (hcount : supportCount hk ring C = m) :
    Active.coord (initialActive hk ring hm2 C hcount) <= commonScale n m := by
  let seed := fixedLevelSeed hk ring C hm2 hcount
  change Active.coord (seed.active hm2) <= commonScale n m
  rw [fixedLevelSeed_active_coord seed hm2]
  exact seed.gap_le

/-- `restartNode` has no new terminal-success branch. -/
theorem restartNode_eq_success_iff {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m)
    (node : KilledTrialNode hk ring hn2 m (2 * commonScale n m)) :
    restartNode hk ring hn2 hm2 node = .success <-> node = .success := by
  cases node <;> simp [restartNode]

/-- Global fixed-level success is exactly a literal charged-support drop.  In
particular, the killed walk's syntactic zero-coordinate branch is not counted
as semantic success. -/
theorem restartedStep_eq_success_iff_drops {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m)
    (state : Active hk ring m (2 * commonScale n m)) (selected : Fin n) :
    restartedStep hk ring hn2 hm2 state selected = .success <->
      Drops hk ring state.config selected := by
  rw [restartedStep, restartNode_eq_success_iff]
  exact killedStepWithFailure_eq_success_iff_drops hk ring hn2 state selected

/-- An upper trial failure is spliced to the canonical minimum-gap retry, and
that retry retains the literal raw successor configuration. -/
theorem failure_splice_same_config {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m)
    (state : Active hk ring m (2 * commonScale n m)) (selected : Fin n)
    (endpoint : FailureEndpoint hk ring hn2 m (2 * commonScale n m))
    (hfailure : killedStepWithFailure hk ring hn2 state selected =
      .failure endpoint) :
    restartedStep hk ring hn2 hm2 state selected =
        .active (endpoint.restartedActive hm2) /\
      (endpoint.restartedActive hm2).config =
        rawStep hk ring state.config selected := by
  constructor
  · simp [restartedStep, hfailure, restartNode]
  · change endpoint.config = rawStep hk ring state.config selected
    exact (killedStepWithFailure_failure_payload hk ring hn2 state selected
      endpoint hfailure).2.2.2.1

/-- The rear distinguished child satisfies the restarted potential law. -/
theorem restartedStep_down_potential {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m)
    (state : Active hk ring m (2 * commonScale n m)) :
    nodePotential n (2 * commonScale n m) (levelBudget n m) Active.coord
        (restartedStep hk ring hn2 hm2 state state.tags.rear) <=
      restartPotential n (2 * commonScale n m) (levelBudget n m)
        (Active.coord state - 1) := by
  unfold restartedStep killedStepWithFailure
  split
  · simp [restartNode, nodePotential]
  · rename_i hnodrop
    have hlaw := (coordinateTransportLaw hk ring hn2).rear state.config
      state.tags state.rear_charged state.front_charged hnodrop
    dsimp only at hlaw
    dsimp only
    split
    · simp [restartNode, nodePotential]
    · split
      · rename_i hupper
        have hlt := state.coord_lt
        change correctedTagGap ring state.config state.tags <
          2 * commonScale n m at hlt
        omega
      · simp [restartNode, nodePotential, Active.coord]
        rw [hlaw]
        exact Nat.le_refl _

/-- The front distinguished child satisfies the restarted potential law.  At
the upper endpoint the fresh minimum gap is paid by the linear restart
account. -/
theorem restartedStep_up_potential {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m)
    (state : Active hk ring m (2 * commonScale n m)) :
    nodePotential n (2 * commonScale n m) (levelBudget n m) Active.coord
        (restartedStep hk ring hn2 hm2 state state.tags.front) <=
      restartPotential n (2 * commonScale n m) (levelBudget n m)
        (Active.coord state + 1) := by
  unfold restartedStep killedStepWithFailure
  split
  · simp [restartNode, nodePotential]
  · rename_i hnodrop
    have hlaw := (coordinateTransportLaw hk ring hn2).front state.config
      state.tags state.rear_charged state.front_charged hnodrop
    dsimp only at hlaw
    dsimp only
    split
    · simp [restartNode, nodePotential]
    · split
      · rename_i hupper
        let endpoint : FailureEndpoint hk ring hn2 m
            (2 * commonScale n m) := {
          source := state
          selected := state.tags.front
          no_drop := hnodrop
          coord_eq := by
            have hle := transported_coord_le_upper hk ring hn2 state
              state.tags.front hnodrop
            dsimp only at hle
            exact Nat.le_antisymm hle hupper }
        have hcoord : Active.coord (endpoint.restartedActive hm2) <=
            commonScale n m := by
          unfold FailureEndpoint.restartedActive
          rw [fixedLevelSeed_active_coord (endpoint.reseed hm2) hm2]
          exact (endpoint.reseed hm2).gap_le
        have hseed := restartPotential_le_midpoint_budget n
          (commonScale n m) (Active.coord (endpoint.restartedActive hm2))
          hcoord
        have hlt := state.coord_lt
        change correctedTagGap ring state.config state.tags <
          2 * commonScale n m at hlt
        have heq : Active.coord state + 1 = 2 * commonScale n m := by
          change correctedTagGap ring state.config state.tags + 1 =
            2 * commonScale n m
          omega
        change restartPotential n (2 * commonScale n m) (levelBudget n m)
            (Active.coord (endpoint.restartedActive hm2)) <=
          restartPotential n (2 * commonScale n m) (levelBudget n m)
            (Active.coord state + 1)
        calc
          restartPotential n (2 * commonScale n m) (levelBudget n m)
              (Active.coord (endpoint.restartedActive hm2)) <=
              (2 * (2 * commonScale n m)) * levelBudget n m := by
                simpa [levelBudget] using hseed
          _ = restartPotential n (2 * commonScale n m) (levelBudget n m)
              (2 * commonScale n m) := by
                simp [restartPotential,
                  SymmetricKilledWalkFiniteTree.concave]
          _ = restartPotential n (2 * commonScale n m) (levelBudget n m)
              (Active.coord state + 1) := by rw [heq]
      · simp [restartNode, nodePotential, Active.coord]
        rw [hlaw]
        exact Nat.le_refl _

/-- Every nondistinguished no-drop child satisfies the restarted frame law. -/
theorem restartedStep_frame_potential {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m)
    (state : Active hk ring m (2 * commonScale n m))
    (selected : Fin n) (hrear : selected ≠ state.tags.rear)
    (hfront : selected ≠ state.tags.front) :
    nodePotential n (2 * commonScale n m) (levelBudget n m) Active.coord
        (restartedStep hk ring hn2 hm2 state selected) <=
      restartPotential n (2 * commonScale n m) (levelBudget n m)
        (Active.coord state) := by
  unfold restartedStep killedStepWithFailure
  split
  · simp [restartNode, nodePotential]
  · rename_i hnodrop
    have hlaw := (coordinateTransportLaw hk ring hn2).frame state.config
      state.tags selected state.rear_charged state.front_charged hrear hfront
      hnodrop
    dsimp only at hlaw
    dsimp only
    split
    · simp [restartNode, nodePotential]
    · split
      · rename_i hupper
        have hlt := state.coord_lt
        change correctedTagGap ring state.config state.tags <
          2 * commonScale n m at hlt
        omega
      · simp [restartNode, nodePotential, Active.coord]
        rw [hlaw]
        exact Nat.le_refl _

/-- The literal fixed-level restarted process instantiates the generic
restart Bellman interface. -/
noncomputable def restartingSpec {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m) :
    RestartingKilledWalkFiniteTree.Spec
      (Active hk ring m (2 * commonScale n m)) n (2 * commonScale n m)
        (levelBudget n m) where
  step := restartedStep hk ring hn2 hm2
  coord := Active.coord
  downEdge := Active.downEdge
  upEdge := Active.upEdge
  edge_count := hn2
  coord_pos := fun state => state.coord_pos
  coord_lt := fun state => state.coord_lt
  edges_ne := fun state => state.tags.ne
  down_potential := restartedStep_down_potential hk ring hn2 hm2
  up_potential := restartedStep_up_potential hk ring hn2 hm2
  frame_potential := restartedStep_frame_potential hk ring hn2 hm2

/-- Uniform finite-horizon residence cost at one fixed support level.  Every
upper failure and every later retry is already included in the left-hand tree
cost. -/
theorem fixedLevel_duration_le {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m)
    (state : Active hk ring m (2 * commonScale n m))
    (hcoord : Active.coord state <= commonScale n m) (T : Nat) :
    truncatedActiveCostNumerator (restartedStep hk ring hn2 hm2)
        (.active state) T <= n ^ T * levelBudget n m := by
  have hQ : 0 < commonScale n m := by
    have hpos := state.coord_pos
    have hlt := state.coord_lt
    omega
  exact lowerHalf_duration_le (restartingSpec hk ring hn2 hm2) state T
    (commonScale n m) hQ hcoord rfl rfl

/-- State-uniform canonical residence bound at support level `m`. -/
theorem canonical_fixedLevel_duration_le {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m)
    (C : Config n k) (hcount : supportCount hk ring C = m) (T : Nat) :
    truncatedActiveCostNumerator (restartedStep hk ring hn2 hm2)
        (.active (initialActive hk ring hm2 C hcount)) T <=
      n ^ T * levelBudget n m :=
  fixedLevel_duration_le hk ring hn2 hm2
    (initialActive hk ring hm2 C hcount)
    (initialActive_coord_le hk ring hm2 C hcount) T

/-- Division-free cubic form of the state-uniform fixed-level residence
bound. -/
theorem canonical_fixedLevel_scaled_duration_le {n k m : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (hm2 : 2 <= m) (C : Config n k)
    (hcount : supportCount hk ring C = m) (T : Nat) :
    m ^ 2 * truncatedActiveCostNumerator
        (restartedStep hk ring hn2 hm2)
        (.active (initialActive hk ring hm2 C hcount)) T <=
      4 * n ^ 3 * n ^ T := by
  let D := truncatedActiveCostNumerator (restartedStep hk ring hn2 hm2)
    (.active (initialActive hk ring hm2 C hcount)) T
  have hD : D <= n ^ T * levelBudget n m :=
    canonical_fixedLevel_duration_le hk ring hn2 hm2 C hcount T
  have hbudget : m ^ 2 * levelBudget n m <= 4 * n ^ 3 := by
    have hmul := CoalescenceLevelSum.common_scale_mul_le m n
    simpa [levelBudget, commonScale, Nat.pow_two, Nat.mul_assoc] using
      CoalescenceLevelSum.common_scale_cubic hmul
  calc
    m ^ 2 * D <= m ^ 2 * (n ^ T * levelBudget n m) :=
      Nat.mul_le_mul_left _ hD
    _ = n ^ T * (m ^ 2 * levelBudget n m) := by ac_rfl
    _ <= n ^ T * (4 * n ^ 3) := Nat.mul_le_mul_left _ hbudget
    _ = 4 * n ^ 3 * n ^ T := by ac_rfl

/-- Arithmetic-only final summation.  A later physical across-level consumer
must supply `levelCost`; this theorem does not itself partition one global
protocol tree into level residence costs. -/
theorem summed_uniform_level_budgets_le_three_cubic (n T : Nat)
    (hn2 : 2 <= n) (levelCost : Nat -> Nat)
    (hlevel : forall m, 2 <= m -> m <= n ->
      m ^ 2 * levelCost m <= 4 * n ^ 3 * n ^ T) :
    CoalescenceLevelSum.intervalSum levelCost 2 (n - 1) <=
      3 * n ^ 3 * n ^ T := by
  have h := CoalescenceLevelSum.sum_levels_le_three_of_sq_scaled
    levelCost (n ^ 3 * n ^ T) n hn2 (by
      intro m hm2 hmn
      simpa [Nat.mul_assoc] using hlevel m hm2 hmn)
  simpa [Nat.mul_assoc] using h

end CoalescenceRestart
end CenteredRenewal
end AAFJPK
