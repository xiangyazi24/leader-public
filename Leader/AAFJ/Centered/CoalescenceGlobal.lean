import Leader.AAFJ.Centered.CoalescenceRestart

/-!
# Physical across-level composition for centered AAFJ coalescence

The fixed-level process stops exactly when the literal charged support drops.
This file retains that raw successor, either canonically reseeds it at its new
support level, or records the resulting one-barrier configuration.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace CoalescenceGlobal

open BarrierAlgebra
open CoalescenceTrial
open CoalescenceRestart
open FiniteUniformStoppingTree
open RestartingKilledWalkFiniteTree

set_option autoImplicit false

/-- A proof state whose scale is chosen canonically from its current physical
charged-support level. -/
structure GlobalActive {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) where
  level : Nat
  level_two : 2 <= level
  trial : Active hk ring level (2 * commonScale n level)

namespace GlobalActive

variable {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} {hn2 : 1 < n}

/-- The literal physical configuration carried by a global proof state. -/
def config (state : GlobalActive hk ring hn2) : Config n k :=
  state.trial.config

@[simp] theorem local_count_eq (state : GlobalActive hk ring hn2) :
    supportCount hk ring state.config = state.level :=
  state.trial.count_eq

/-- Canonical reseeding of any physical configuration with at least two
charged barriers. -/
noncomputable def seed (C : Config n k) (m : Nat) (hm2 : 2 <= m)
    (hcount : supportCount hk ring C = m) : GlobalActive hk ring hn2 where
  level := m
  level_two := hm2
  trial := initialActive hk ring hm2 C hcount

@[simp] theorem seed_config (C : Config n k) (m : Nat) (hm2 : 2 <= m)
    (hcount : supportCount hk ring C = m) :
    (seed (hk := hk) (ring := ring) (hn2 := hn2) C m hm2 hcount).config = C :=
  rfl

end GlobalActive

/-- A literal support-drop interaction, before deciding whether its successor
still has at least two charged barriers. -/
structure SupportDropEndpoint {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) where
  source : GlobalActive hk ring hn2
  selected : Fin n
  drops : Drops hk ring source.config selected

namespace SupportDropEndpoint

variable {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} {hn2 : 1 < n}

/-- The endpoint is the literal protocol successor, not a proof-only state. -/
def config (endpoint : SupportDropEndpoint hk ring hn2) : Config n k :=
  rawStep hk ring endpoint.source.config endpoint.selected

/-- Its exact charged-support level. -/
def level (endpoint : SupportDropEndpoint hk ring hn2) : Nat :=
  supportCount hk ring endpoint.config

theorem level_lt (endpoint : SupportDropEndpoint hk ring hn2) :
    endpoint.level < endpoint.source.level := by
  rw [← endpoint.source.local_count_eq]
  exact endpoint.drops

theorem level_pos (endpoint : SupportDropEndpoint hk ring hn2)
    (hndvd : ¬ k ∣ n) : 0 < endpoint.level := by
  exact barrierCount_pos_of_not_dvd hk ring endpoint.config hndvd

/-- A genuine lower level is reseeded without changing the physical endpoint. -/
noncomputable def reseed (endpoint : SupportDropEndpoint hk ring hn2)
    (hm2 : 2 <= endpoint.level) : GlobalActive hk ring hn2 :=
  GlobalActive.seed endpoint.config endpoint.level hm2 rfl

@[simp] theorem reseed_config (endpoint : SupportDropEndpoint hk ring hn2)
    (hm2 : 2 <= endpoint.level) :
    (endpoint.reseed hm2).config = endpoint.config := rfl

end SupportDropEndpoint

/-- Terminal physical payload at support level one. -/
structure OneBarrierEndpoint {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) where
  drop : SupportDropEndpoint hk ring hn2
  count_eq_one : drop.level = 1

/-- One global interaction either leaves another canonically scaled active
state or reaches a retained one-barrier physical endpoint. -/
inductive GlobalNode {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) where
  | active : GlobalActive hk ring hn2 -> GlobalNode hk ring hn2
  | oneBarrier : OneBarrierEndpoint hk ring hn2 -> GlobalNode hk ring hn2

namespace GlobalNode

variable {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} {hn2 : 1 < n}

/-- Forget the terminal physical payload only when entering a generic stopping
tree. -/
def erase : GlobalNode hk ring hn2 -> StopNode (GlobalActive hk ring hn2)
  | .active state => .active state
  | .oneBarrier _ => .success

/-- Physical configuration of either kind of global child. -/
def config : GlobalNode hk ring hn2 -> Config n k
  | .active state => state.config
  | .oneBarrier endpoint => endpoint.drop.config

end GlobalNode

/-- The restarted fixed-level step has no generic failure outcome. -/
theorem restartedStep_ne_failure {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m)
    (state : Active hk ring m (2 * commonScale n m)) (selected : Fin n) :
    restartedStep hk ring hn2 hm2 state selected ≠ .failure := by
  unfold restartedStep restartNode
  cases killedStepWithFailure hk ring hn2 state selected <;> simp

/-- Every active fixed-level successor carries the literal raw configuration,
including the upper-exit/reseed branch. -/
theorem restartedStep_active_config {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m)
    (state : Active hk ring m (2 * commonScale n m)) (selected : Fin n)
    (next : Active hk ring m (2 * commonScale n m))
    (hnext : restartedStep hk ring hn2 hm2 state selected = .active next) :
    next.config = rawStep hk ring state.config selected := by
  unfold restartedStep restartNode at hnext
  cases hnode : killedStepWithFailure hk ring hn2 state selected with
  | active continued =>
      simp [hnode] at hnext
      subst next
      unfold killedStepWithFailure at hnode
      split at hnode
      · contradiction
      · dsimp at hnode
        split at hnode
        · contradiction
        · split at hnode
          · contradiction
          · simp only [KilledTrialNode.active.injEq] at hnode
            subst continued
            rfl
  | success => simp [hnode] at hnext
  | failure endpoint =>
      simp [hnode] at hnext
      have heq : endpoint.restartedActive hm2 = next := by
        exact StopNode.active.inj hnext
      subst next
      exact (failure_splice_same_config hk ring hn2 hm2 state selected
        endpoint hnode).2

/-- A no-drop fixed-level step has an active successor. -/
theorem exists_restarted_active_of_not_drops {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m)
    (state : Active hk ring m (2 * commonScale n m)) (selected : Fin n)
    (hnodrop : ¬ Drops hk ring state.config selected) :
    ∃ next, restartedStep hk ring hn2 hm2 state selected = .active next := by
  cases hnode : restartedStep hk ring hn2 hm2 state selected with
  | active next => exact ⟨next, rfl⟩
  | success =>
      exact False.elim (hnodrop
        ((restartedStep_eq_success_iff_drops hk ring hn2 hm2 state selected).mp
          hnode))
  | failure =>
      exact False.elim ((restartedStep_ne_failure hk ring hn2 hm2 state
        selected) hnode)

/-- Continue a no-drop interaction inside the same global support level. -/
noncomputable def continueNoDrop {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : GlobalActive hk ring hn2) (selected : Fin n)
    (hnodrop : ¬ Drops hk ring state.config selected) :
    GlobalActive hk ring hn2 where
  level := state.level
  level_two := state.level_two
  trial := Classical.choose (exists_restarted_active_of_not_drops hk ring hn2
    state.level_two state.trial selected hnodrop)

theorem continueNoDrop_step {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : GlobalActive hk ring hn2) (selected : Fin n)
    (hnodrop : ¬ Drops hk ring state.config selected) :
    restartedStep hk ring hn2 state.level_two state.trial selected =
      .active (continueNoDrop hk ring hn2 state selected hnodrop).trial := by
  exact Classical.choose_spec (exists_restarted_active_of_not_drops hk ring
    hn2 state.level_two state.trial selected hnodrop)

@[simp] theorem continueNoDrop_level {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : GlobalActive hk ring hn2) (selected : Fin n)
    (hnodrop : ¬ Drops hk ring state.config selected) :
    (continueNoDrop hk ring hn2 state selected hnodrop).level = state.level :=
  rfl

theorem continueNoDrop_config {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (state : GlobalActive hk ring hn2) (selected : Fin n)
    (hnodrop : ¬ Drops hk ring state.config selected) :
    (continueNoDrop hk ring hn2 state selected hnodrop).config =
      rawStep hk ring state.config selected := by
  exact restartedStep_active_config hk ring hn2 state.level_two state.trial
    selected _ (continueNoDrop_step hk ring hn2 state selected hnodrop)

/-- A literal interaction, with same-level restart on no drop and canonical
lower-level reseeding on a drop. -/
noncomputable def globalStep {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n)
    (state : GlobalActive hk ring hn2) (selected : Fin n) :
    GlobalNode hk ring hn2 :=
  if hdrop : Drops hk ring state.config selected then
    let endpoint : SupportDropEndpoint hk ring hn2 := {
      source := state
      selected := selected
      drops := hdrop }
    if hm2 : 2 <= endpoint.level then
      .active (endpoint.reseed hm2)
    else
      .oneBarrier {
        drop := endpoint
        count_eq_one := by
          have hpos := endpoint.level_pos hndvd
          omega }
  else
    .active (continueNoDrop hk ring hn2 state selected hdrop)

/-- Generic stopped-tree view of the physical global interaction. -/
noncomputable def globalErasedStep {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n) :
    GlobalActive hk ring hn2 -> Fin n -> StopNode (GlobalActive hk ring hn2) :=
  fun state selected => (globalStep hk ring hn2 hndvd state selected).erase

/-- Exact physical projection: every global child, including a fixed-level
upper-exit reseed and a cross-level reseed, is the literal raw successor. -/
theorem globalStep_config {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n)
    (state : GlobalActive hk ring hn2) (selected : Fin n) :
    (globalStep hk ring hn2 hndvd state selected).config =
      rawStep hk ring state.config selected := by
  unfold globalStep
  split
  · rename_i hdrop
    dsimp only
    split
    · exact SupportDropEndpoint.reseed_config _ _
    · rfl
  · rename_i hnodrop
    exact continueNoDrop_config hk ring hn2 state selected hnodrop

/-- A global terminal child retains exactly one charged barrier. -/
theorem globalStep_oneBarrier_count {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n)
    (state : GlobalActive hk ring hn2) (selected : Fin n)
    (endpoint : OneBarrierEndpoint hk ring hn2)
    (hstep : globalStep hk ring hn2 hndvd state selected =
      .oneBarrier endpoint) :
    supportCount hk ring (rawStep hk ring state.config selected) = 1 := by
  have hconfig := globalStep_config hk ring hn2 hndvd state selected
  rw [hstep] at hconfig
  change endpoint.drop.config = rawStep hk ring state.config selected at hconfig
  rw [← hconfig]
  exact endpoint.count_eq_one

/-- An active global child never raises the physical support level, and every
cross-level transition is a strict support drop. -/
theorem globalStep_active_level_le {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n)
    (state next : GlobalActive hk ring hn2) (selected : Fin n)
    (hstep : globalStep hk ring hn2 hndvd state selected = .active next) :
    next.level <= state.level := by
  unfold globalStep at hstep
  split at hstep
  · rename_i hdrop
    dsimp only at hstep
    split at hstep
    · simp only [GlobalNode.active.injEq] at hstep
      subst next
      exact Nat.le_of_lt (SupportDropEndpoint.level_lt _)
    · contradiction
  · simp only [GlobalNode.active.injEq] at hstep
    subst next
    exact Nat.le_refl _

/-! ## Exact residence partition of the physical global tree -/

/-- Every charged support is a filtered list of the `n` ring edges. -/
theorem supportCount_le_ringSize {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Config n k) :
    supportCount hk ring C <= n := by
  unfold supportCount barrierCount barrierSupport
  exact Nat.le_trans (List.length_filter_le _ _) (by
    simp [ExhaustiveList.fin])

theorem GlobalActive.level_le_ringSize {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {hn2 : 1 < n}
    (state : GlobalActive hk ring hn2) : state.level <= n := by
  rw [← state.local_count_eq]
  exact supportCount_le_ringSize hk ring state.config

/-- Exact scheduler-word numerator for a state-dependent interaction toll. -/
def weightedActiveCostNumerator {S : Type} {n : Nat}
    (step : S -> Fin n -> StopNode S) (toll : S -> Nat) :
    StopNode S -> Nat -> Nat
  | _, 0 => 0
  | .success, _ + 1 => 0
  | .failure, _ + 1 => 0
  | .active state, T + 1 =>
      toll state * n ^ (T + 1) +
        (List.ofFn (fun edge : Fin n =>
          weightedActiveCostNumerator step toll (step state edge) T)).sum

theorem weightedActiveCostNumerator_congr {S : Type} {n : Nat}
    (step : S -> Fin n -> StopNode S) (a b : S -> Nat)
    (hab : ∀ state, a state = b state) :
    ∀ node T, weightedActiveCostNumerator step a node T =
      weightedActiveCostNumerator step b node T := by
  intro node T
  induction T generalizing node with
  | zero => rfl
  | succ T ih =>
      cases node with
      | success => rfl
      | failure => rfl
      | active state =>
          simp only [weightedActiveCostNumerator, hab state]
          congr 1
          apply ofFn_sum_eq
          intro edge
          exact ih (step state edge)

theorem weightedActiveCostNumerator_add {S : Type} {n : Nat}
    (step : S -> Fin n -> StopNode S) (a b : S -> Nat) :
    ∀ node T,
      weightedActiveCostNumerator step (fun state => a state + b state)
          node T =
        weightedActiveCostNumerator step a node T +
          weightedActiveCostNumerator step b node T := by
  intro node T
  induction T generalizing node with
  | zero => rfl
  | succ T ih =>
      cases node with
      | success => rfl
      | failure => rfl
      | active state =>
          simp only [weightedActiveCostNumerator, Nat.add_mul]
          rw [show (List.ofFn (fun edge : Fin n =>
              weightedActiveCostNumerator step (fun state =>
                a state + b state) (step state edge) T)).sum =
              (List.ofFn (fun edge : Fin n =>
                weightedActiveCostNumerator step a (step state edge) T +
                  weightedActiveCostNumerator step b
                    (step state edge) T)).sum by
            apply ofFn_sum_eq
            intro edge
            exact ih (step state edge)]
          rw [ofFn_sum_add]
          omega

theorem weightedActiveCostNumerator_zero {S : Type} {n : Nat}
    (step : S -> Fin n -> StopNode S) :
    ∀ node T,
      weightedActiveCostNumerator step (fun _ => 0) node T = 0 := by
  intro node T
  induction T generalizing node with
  | zero => rfl
  | succ T ih =>
      cases node with
      | success => rfl
      | failure => rfl
      | active state =>
          simp only [weightedActiveCostNumerator, Nat.zero_mul,
            Nat.zero_add]
          rw [show (List.ofFn (fun edge : Fin n =>
              weightedActiveCostNumerator step (fun _ => 0)
                (step state edge) T)).sum =
              (List.ofFn (fun _ : Fin n => 0)).sum by
            apply ofFn_sum_eq
            intro edge
            exact ih (step state edge)]
          rw [ofFn_sum_const, Nat.mul_zero]

theorem weightedActiveCostNumerator_one_eq {S : Type} {n : Nat}
    (step : S -> Fin n -> StopNode S) :
    ∀ node T,
      weightedActiveCostNumerator step (fun _ => 1) node T =
        truncatedActiveCostNumerator step node T := by
  intro node T
  induction T generalizing node with
  | zero => rfl
  | succ T ih =>
      cases node with
      | success => rfl
      | failure => rfl
      | active state =>
          simp only [weightedActiveCostNumerator,
            truncatedActiveCostNumerator, Nat.one_mul]
          congr 1
          apply ofFn_sum_eq
          intro edge
          exact ih (step state edge)

/-- State-dependent-toll version of the natural Bellman interface. -/
def WeightedNatBellmanSuperSolution {S : Type} {n : Nat}
    (step : S -> Fin n -> StopNode S) (toll : S -> Nat) (scale : Nat)
    (potential : StopNode S -> Nat) : Prop :=
  potential .success = 0 ∧ potential .failure = 0 ∧
    ∀ state, scale * toll state * n +
      (List.ofFn (fun edge : Fin n => potential (step state edge))).sum <=
        n * potential (.active state)

/-- Finite-horizon Bellman induction for an exact state-dependent toll. -/
theorem weightedActiveCostNumerator_mul_le_of_superSolution
    {S : Type} {n : Nat} (step : S -> Fin n -> StopNode S)
    (toll : S -> Nat) (scale : Nat) (potential : StopNode S -> Nat)
    (hsuper : WeightedNatBellmanSuperSolution step toll scale potential) :
    ∀ node T,
      scale * weightedActiveCostNumerator step toll node T +
          treeWeight step potential node T <=
        n ^ T * potential node := by
  intro node T
  induction T generalizing node with
  | zero => simp [weightedActiveCostNumerator, treeWeight]
  | succ T ih =>
      rcases hsuper with ⟨hsuccess, hfailure, hstep⟩
      cases node with
      | success => simp [weightedActiveCostNumerator,
          treeWeight_success, hsuccess]
      | failure => simp [weightedActiveCostNumerator,
          treeWeight_failure, hfailure]
      | active state =>
          have hchildren := ofFn_sum_le
            (fun edge : Fin n =>
              scale * weightedActiveCostNumerator step toll
                  (step state edge) T +
                treeWeight step potential (step state edge) T)
            (fun edge : Fin n => n ^ T * potential (step state edge))
            (fun edge => ih (step state edge))
          simp only [weightedActiveCostNumerator, treeWeight]
          calc
            scale * (toll state * n ^ (T + 1) +
                (List.ofFn (fun edge : Fin n =>
                  weightedActiveCostNumerator step toll
                    (step state edge) T)).sum) +
                (List.ofFn (fun edge : Fin n =>
                  treeWeight step potential (step state edge) T)).sum =
              n ^ T * (scale * toll state * n) +
                (List.ofFn (fun edge : Fin n =>
                  scale * weightedActiveCostNumerator step toll
                      (step state edge) T +
                    treeWeight step potential (step state edge) T)).sum := by
                      rw [Nat.mul_add, ofFn_sum_add,
                        ofFn_sum_mul_left]
                      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
                        Nat.mul_assoc, Nat.add_assoc]
            _ <= n ^ T * (scale * toll state * n) +
                (List.ofFn (fun edge : Fin n =>
                  n ^ T * potential (step state edge))).sum :=
              Nat.add_le_add_left hchildren _
            _ = n ^ T * (scale * toll state * n +
                (List.ofFn (fun edge : Fin n =>
                  potential (step state edge))).sum) := by
              rw [ofFn_sum_mul_left, Nat.mul_add]
            _ <= n ^ T * (n * potential (.active state)) :=
              Nat.mul_le_mul_left _ (hstep state)
            _ = n ^ (T + 1) * potential (.active state) := by
              simp [Nat.pow_succ, Nat.mul_assoc]

theorem weightedActiveCostNumerator_mul_le {S : Type} {n : Nat}
    (step : S -> Fin n -> StopNode S) (toll : S -> Nat) (scale : Nat)
    (potential : StopNode S -> Nat)
    (hsuper : WeightedNatBellmanSuperSolution step toll scale potential)
    (node : StopNode S) (T : Nat) :
    scale * weightedActiveCostNumerator step toll node T <=
      n ^ T * potential node := by
  have h := weightedActiveCostNumerator_mul_le_of_superSolution step toll
    scale potential hsuper node T
  omega

/-- A finite interval sum commutes with the exact weighted tree cost. -/
theorem weightedActiveCostNumerator_intervalSum {S : Type} {n : Nat}
    (step : S -> Fin n -> StopNode S) (toll : Nat -> S -> Nat)
    (lo fuel : Nat) (node : StopNode S) (T : Nat) :
    weightedActiveCostNumerator step
        (fun state => CoalescenceLevelSum.intervalSum
          (fun m => toll m state) lo fuel) node T =
      CoalescenceLevelSum.intervalSum
        (fun m => weightedActiveCostNumerator step (toll m) node T)
        lo fuel := by
  induction fuel generalizing lo with
  | zero =>
      change weightedActiveCostNumerator step (fun _ => 0) node T = 0
      exact weightedActiveCostNumerator_zero step node T
  | succ fuel ih =>
      change weightedActiveCostNumerator step
          (fun state => toll lo state +
            CoalescenceLevelSum.intervalSum (fun m => toll m state)
              (lo + 1) fuel) node T =
        weightedActiveCostNumerator step (toll lo) node T +
          CoalescenceLevelSum.intervalSum
            (fun m => weightedActiveCostNumerator step (toll m) node T)
            (lo + 1) fuel
      rw [weightedActiveCostNumerator_add, ih]

/-- An interval beginning strictly after the marked index contains no marked
term. -/
theorem intervalSum_indicator_zero_of_lt (x lo fuel : Nat) (hx : x < lo) :
    CoalescenceLevelSum.intervalSum (fun m => if m = x then 1 else 0)
      lo fuel = 0 := by
  induction fuel generalizing lo with
  | zero => rfl
  | succ fuel ih =>
      rw [CoalescenceLevelSum.intervalSum_succ]
      have hne : lo ≠ x := by omega
      rw [if_neg hne, Nat.zero_add]
      exact ih (lo + 1) (by omega)

/-- A finite interval containing the marked index has indicator sum one. -/
theorem intervalSum_indicator_eq_one (x lo fuel : Nat)
    (hlo : lo <= x) (hhi : x < lo + fuel) :
    CoalescenceLevelSum.intervalSum (fun m => if m = x then 1 else 0)
      lo fuel = 1 := by
  induction fuel generalizing lo with
  | zero => omega
  | succ fuel ih =>
      rw [CoalescenceLevelSum.intervalSum_succ]
      by_cases hx : lo = x
      · subst x
        rw [if_pos rfl,
          intervalSum_indicator_zero_of_lt lo (lo + 1) fuel (by omega)]
      · rw [if_neg hx, Nat.zero_add]
        exact ih (lo + 1) (by omega) (by omega)

/-- Indicator toll for interactions occurring at one literal support level. -/
def levelToll {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    {hn2 : 1 < n} (m : Nat) (state : GlobalActive hk ring hn2) : Nat :=
  if m = state.level then 1 else 0

/-- Fixed-level Bellman scale used while accounting for support level `m`. -/
def residenceScale (n m : Nat) : Nat := 2 * (2 * commonScale n m)

/-- Potential for residence at one target support level.  Above the target it
holds a constant entrance reserve; at the target it is the exact restarted
killed-walk potential; below the target it vanishes. -/
def levelResidencePotential {n k : Nat} {hk : 0 < k}
    {ring : DirectedRing n} {hn2 : 1 < n} (m : Nat) :
    StopNode (GlobalActive hk ring hn2) -> Nat
  | .success => 0
  | .failure => 0
  | .active state =>
      if m < state.level then
        residenceScale n m * levelBudget n m
      else if m = state.level then
        restartPotential n (2 * commonScale n m) (levelBudget n m)
          (Active.coord state.trial)
      else 0

/-- At the target level, the physical global child has exactly the potential
of the corresponding fixed-level restarted child. -/
theorem levelResidencePotential_step_eq_fixed {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n)
    (state : GlobalActive hk ring hn2) (hlevel : state.level = m)
    (selected : Fin n) :
    levelResidencePotential m
        (globalErasedStep hk ring hn2 hndvd state selected) =
      nodePotential n (2 * commonScale n m) (levelBudget n m) Active.coord
        (restartedStep hk ring hn2 (hlevel ▸ state.level_two)
          (hlevel ▸ state.trial) selected) := by
  subst m
  unfold globalErasedStep globalStep
  split
  · rename_i hdrop
    have hfixed := (restartedStep_eq_success_iff_drops hk ring hn2
      state.level_two state.trial selected).mpr hdrop
    dsimp only
    split
    · rename_i hm2
      let endpoint : SupportDropEndpoint hk ring hn2 :=
        { source := state, selected := selected, drops := hdrop }
      have hlt : endpoint.level < state.level := endpoint.level_lt
      have hreseed : (endpoint.reseed hm2).level = endpoint.level := rfl
      have hnlt : ¬ state.level < (endpoint.reseed hm2).level := by omega
      have hne : state.level ≠ (endpoint.reseed hm2).level := by omega
      rw [hfixed]
      change levelResidencePotential state.level (.active (endpoint.reseed hm2)) = 0
      simp [levelResidencePotential, hnlt, hne]
    · rw [hfixed]
      simp [GlobalNode.erase, levelResidencePotential, nodePotential]
  · rename_i hnodrop
    have hfixed := continueNoDrop_step hk ring hn2 state selected hnodrop
    rw [hfixed]
    simp [GlobalNode.erase, levelResidencePotential, nodePotential,
      continueNoDrop_level]

/-- A canonical level seed fits inside its target-level entrance reserve. -/
theorem seed_potential_le_reserve {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hm2 : 2 <= m)
    (C : Config n k) (hcount : supportCount hk ring C = m) :
    restartPotential n (2 * commonScale n m) (levelBudget n m)
        (Active.coord
          (GlobalActive.seed (hk := hk) (ring := ring) (hn2 := hn2)
            C m hm2 hcount).trial) <=
      residenceScale n m * levelBudget n m := by
  have hcoord := initialActive_coord_le hk ring hm2 C hcount
  have hbound := restartPotential_le_midpoint_budget n (commonScale n m)
    (Active.coord (initialActive hk ring hm2 C hcount)) hcoord
  simpa [GlobalActive.seed, residenceScale, levelBudget] using hbound

/-- Before the target level is first reached, every physical child fits below
the same constant entrance reserve. -/
theorem levelResidencePotential_child_le_reserve {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n)
    (state : GlobalActive hk ring hn2) (habove : m < state.level)
    (selected : Fin n) :
    levelResidencePotential m
        (globalErasedStep hk ring hn2 hndvd state selected) <=
      residenceScale n m * levelBudget n m := by
  unfold globalErasedStep globalStep
  split
  · rename_i hdrop
    dsimp only
    split
    · rename_i hm2
      let endpoint : SupportDropEndpoint hk ring hn2 :=
        { source := state, selected := selected, drops := hdrop }
      change levelResidencePotential m (.active (endpoint.reseed hm2)) <= _
      simp only [levelResidencePotential]
      have hreseed : (endpoint.reseed hm2).level = endpoint.level := rfl
      by_cases hstill : m < endpoint.level
      · have hstill' : m < (endpoint.reseed hm2).level := by
          rw [hreseed]
          exact hstill
        rw [if_pos hstill']
        exact Nat.le_refl _
      · have hstill' : ¬ m < (endpoint.reseed hm2).level := by
          rw [hreseed]
          exact hstill
        rw [if_neg hstill']
        by_cases heq : m = endpoint.level
        · have heq' : m = (endpoint.reseed hm2).level := by
            rw [hreseed]
            exact heq
          rw [if_pos heq']
          subst m
          exact seed_potential_le_reserve hk ring hn2 hm2 endpoint.config rfl
        · have heq' : m ≠ (endpoint.reseed hm2).level := by
            rw [hreseed]
            exact heq
          rw [if_neg heq']
          exact Nat.zero_le _
    · simp [GlobalNode.erase, levelResidencePotential]
  · rename_i hnodrop
    simp [GlobalNode.erase, levelResidencePotential, continueNoDrop_level,
      habove]

/-- After the physical support has passed below the target, the target-level
potential remains zero. -/
theorem levelResidencePotential_child_eq_zero_of_below {n k m : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (hndvd : ¬ k ∣ n) (state : GlobalActive hk ring hn2)
    (hbelow : state.level < m) (selected : Fin n) :
    levelResidencePotential m
        (globalErasedStep hk ring hn2 hndvd state selected) = 0 := by
  cases hnode : globalStep hk ring hn2 hndvd state selected with
  | oneBarrier endpoint =>
      simp [globalErasedStep, hnode, GlobalNode.erase,
        levelResidencePotential]
  | active next =>
      have hle := globalStep_active_level_le hk ring hn2 hndvd state next
        selected hnode
      have hnlt : ¬ m < next.level := by omega
      have hne : m ≠ next.level := by omega
      simp [globalErasedStep, hnode, GlobalNode.erase,
        levelResidencePotential, hnlt, hne]

/-- The target-level entrance reserve and exact fixed-level potential form a
weighted Bellman certificate for the literal across-level process. -/
theorem levelResidenceSuperSolution {n k m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n)
    (hm2 : 2 <= m) :
    WeightedNatBellmanSuperSolution
      (globalErasedStep hk ring hn2 hndvd) (levelToll m)
      (residenceScale n m) (levelResidencePotential m) := by
  constructor
  · rfl
  constructor
  · rfl
  intro state
  by_cases habove : m < state.level
  · have hchildren := ofFn_sum_le
      (fun selected : Fin n => levelResidencePotential m
        (globalErasedStep hk ring hn2 hndvd state selected))
      (fun _ : Fin n => residenceScale n m * levelBudget n m)
      (fun selected => levelResidencePotential_child_le_reserve hk ring hn2
        hndvd state habove selected)
    have hne : m ≠ state.level := by omega
    simp only [levelToll, if_neg hne, residenceScale, Nat.mul_zero,
      Nat.zero_mul, Nat.zero_add, levelResidencePotential, if_pos habove]
    rw [ofFn_sum_const] at hchildren
    exact hchildren
  · by_cases heq : m = state.level
    · have hm2state : 2 <= state.level := state.level_two
      have hfixed := (natSuperSolution
        (restartingSpec hk ring hn2 hm2state)).2.2 state.trial
      change 2 * (2 * commonScale n state.level) * n +
          (List.ofFn (fun selected : Fin n =>
            nodePotential n (2 * commonScale n state.level)
              (levelBudget n state.level) Active.coord
              (restartedStep hk ring hn2 state.level_two state.trial
                selected))).sum <=
          n * restartPotential n (2 * commonScale n state.level)
            (levelBudget n state.level) (Active.coord state.trial) at hfixed
      have hchildren :
          (List.ofFn (fun selected : Fin n => levelResidencePotential m
            (globalErasedStep hk ring hn2 hndvd state selected))).sum =
          (List.ofFn (fun selected : Fin n =>
            nodePotential n (2 * commonScale n state.level)
              (levelBudget n state.level) Active.coord
              (restartedStep hk ring hn2 state.level_two state.trial
                selected))).sum := by
        apply ofFn_sum_eq
        intro selected
        subst m
        exact levelResidencePotential_step_eq_fixed hk ring hn2 hndvd state
          rfl selected
      rw [hchildren]
      subst m
      simpa [levelToll, levelResidencePotential, residenceScale] using hfixed
    · have hbelow : state.level < m := by omega
      have hchildren :
          (List.ofFn (fun selected : Fin n => levelResidencePotential m
            (globalErasedStep hk ring hn2 hndvd state selected))).sum = 0 := by
        rw [show (List.ofFn (fun selected : Fin n => levelResidencePotential m
            (globalErasedStep hk ring hn2 hndvd state selected))).sum =
            (List.ofFn (fun _ : Fin n => 0)).sum by
          apply ofFn_sum_eq
          intro selected
          exact levelResidencePotential_child_eq_zero_of_below hk ring hn2
            hndvd state hbelow selected]
        rw [ofFn_sum_const, Nat.mul_zero]
      rw [hchildren]
      simp [levelToll, levelResidencePotential, habove, heq]

/-- Actual residence numerator of the physical across-level tree at level
`m`; this is not an arbitrary accounting function. -/
noncomputable def globalLevelResidenceNumerator {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n)
    (initial : GlobalActive hk ring hn2) (T m : Nat) : Nat :=
  weightedActiveCostNumerator (globalErasedStep hk ring hn2 hndvd)
    (levelToll m) (.active initial) T

/-- At every target level, a canonical global root fits below the constant
first-entry reserve. -/
theorem canonical_root_potential_le_reserve {n k M m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hM2 : 2 <= M)
    (C : Config n k) (hcount : supportCount hk ring C = M) :
    levelResidencePotential m
        (.active (GlobalActive.seed (hk := hk) (ring := ring) (hn2 := hn2)
          C M hM2 hcount)) <=
      residenceScale n m * levelBudget n m := by
  let initial := GlobalActive.seed (hk := hk) (ring := ring) (hn2 := hn2)
    C M hM2 hcount
  have hlevel : initial.level = M := rfl
  by_cases habove : m < M
  · change (if m < M then residenceScale n m * levelBudget n m
        else if m = M then _ else 0) <= _
    rw [if_pos habove]
    exact Nat.le_refl _
  · by_cases heq : m = M
    · subst m
      have hnlt : ¬ M < initial.level := by simp [hlevel]
      have heq' : M = initial.level := by exact hlevel.symm
      rw [show levelResidencePotential M (.active initial) =
          restartPotential n (2 * commonScale n M) (levelBudget n M)
            (Active.coord initial.trial) by
        simp [levelResidencePotential, heq']]
      exact seed_potential_le_reserve hk ring hn2 hM2 C hcount
    · change (if m < M then residenceScale n m * levelBudget n m
        else if m = M then _ else 0) <= _
      rw [if_neg habove, if_neg heq]
      exact Nat.zero_le _

/-- Actual physical global residence at one target level satisfies the same
uniform budget as a fresh fixed-level run.  The constant potential above the
target accounts for all possible first-entry prefixes. -/
theorem canonical_global_level_residence_le {n k M m : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n)
    (hM2 : 2 <= M) (hm2 : 2 <= m) (hmn : m <= n)
    (C : Config n k) (hcount : supportCount hk ring C = M) (T : Nat) :
    globalLevelResidenceNumerator hk ring hn2 hndvd
        (GlobalActive.seed (hk := hk) (ring := ring) (hn2 := hn2)
          C M hM2 hcount) T m <=
      n ^ T * levelBudget n m := by
  let initial := GlobalActive.seed (hk := hk) (ring := ring) (hn2 := hn2)
    C M hM2 hcount
  let D := globalLevelResidenceNumerator hk ring hn2 hndvd initial T m
  have hbellman := weightedActiveCostNumerator_mul_le
    (globalErasedStep hk ring hn2 hndvd) (levelToll m)
    (residenceScale n m) (levelResidencePotential m)
    (levelResidenceSuperSolution hk ring hn2 hndvd hm2)
    (.active initial) T
  have hroot := canonical_root_potential_le_reserve hk ring hn2 hM2 C hcount
    (m := m)
  have hscaled : residenceScale n m * D <=
      residenceScale n m * (n ^ T * levelBudget n m) := by
    calc
      residenceScale n m * D <=
          n ^ T * levelResidencePotential m (.active initial) := hbellman
      _ <= n ^ T * (residenceScale n m * levelBudget n m) :=
        Nat.mul_le_mul_left _ hroot
      _ = residenceScale n m * (n ^ T * levelBudget n m) := by ac_rfl
  have hmpos : 0 < m := by omega
  have hQ2 : 2 <= commonScale n m := by
    apply (Nat.le_div_iff_mul_le hmpos).2
    omega
  have hscale : 0 < residenceScale n m := by
    unfold residenceScale
    omega
  exact Nat.le_of_mul_le_mul_left hscaled hscale

/-- Division-free cubic form of the physically connected per-level residence
bound. -/
theorem canonical_global_level_scaled_residence_le {n k M m : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (hndvd : ¬ k ∣ n) (hM2 : 2 <= M) (hm2 : 2 <= m) (hmn : m <= n)
    (C : Config n k) (hcount : supportCount hk ring C = M) (T : Nat) :
    m ^ 2 * globalLevelResidenceNumerator hk ring hn2 hndvd
        (GlobalActive.seed (hk := hk) (ring := ring) (hn2 := hn2)
          C M hM2 hcount) T m <=
      4 * n ^ 3 * n ^ T := by
  let D := globalLevelResidenceNumerator hk ring hn2 hndvd
    (GlobalActive.seed (hk := hk) (ring := ring) (hn2 := hn2)
      C M hM2 hcount) T m
  have hD : D <= n ^ T * levelBudget n m :=
    canonical_global_level_residence_le hk ring hn2 hndvd hM2 hm2 hmn
      C hcount T
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

/-- Exact partition of all physical global interactions into the possible
support levels `2,...,n`. -/
theorem global_residence_partition {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n)
    (initial : GlobalActive hk ring hn2) (T : Nat) :
    truncatedActiveCostNumerator (globalErasedStep hk ring hn2 hndvd)
        (.active initial) T =
      CoalescenceLevelSum.intervalSum
        (globalLevelResidenceNumerator hk ring hn2 hndvd initial T)
        2 (n - 1) := by
  rw [← weightedActiveCostNumerator_one_eq]
  unfold globalLevelResidenceNumerator
  rw [← weightedActiveCostNumerator_intervalSum]
  apply weightedActiveCostNumerator_congr
  intro state
  unfold levelToll
  exact (intervalSum_indicator_eq_one state.level 2 (n - 1)
    state.level_two (by
      have hle := state.level_le_ringSize
      omega)).symm

/-- Once a bound is proved for the actual residence of each physical support
level, the exact partition and the division-free level sum give the desired
global normalized cubic bound. -/
theorem global_duration_le_three_cubic_of_level_residence {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (hndvd : ¬ k ∣ n) (initial : GlobalActive hk ring hn2) (T : Nat)
    (hlevel : ∀ m, 2 <= m -> m <= n ->
      m ^ 2 * globalLevelResidenceNumerator hk ring hn2 hndvd initial T m <=
        4 * n ^ 3 * n ^ T) :
    truncatedActiveCostNumerator (globalErasedStep hk ring hn2 hndvd)
        (.active initial) T <= 3 * n ^ 3 * n ^ T := by
  rw [global_residence_partition]
  exact summed_uniform_level_budgets_le_three_cubic n T (by omega)
    (globalLevelResidenceNumerator hk ring hn2 hndvd initial T) hlevel

/-- Complete finite-horizon physical coalescence bound from an arbitrary
configuration with at least two charged barriers.  The left side is the exact
number of active interactions over all depth-`T` scheduler words; dividing by
`n^T` gives the normalized residence bound `3*n^3`. -/
theorem canonical_global_duration_le_three_cubic {n k M : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (hndvd : ¬ k ∣ n) (hM2 : 2 <= M)
    (C : Config n k) (hcount : supportCount hk ring C = M) (T : Nat) :
    truncatedActiveCostNumerator (globalErasedStep hk ring hn2 hndvd)
        (.active (GlobalActive.seed (hk := hk) (ring := ring) (hn2 := hn2)
          C M hM2 hcount)) T <=
      3 * n ^ 3 * n ^ T := by
  apply global_duration_le_three_cubic_of_level_residence hk ring hn2 hndvd
  intro m hm2 hmn
  exact canonical_global_level_scaled_residence_le hk ring hn2 hndvd hM2
    hm2 hmn C hcount T

end CoalescenceGlobal
end CenteredRenewal
end AAFJPK
