import Leader.AAFJ.Centered.EndToEndBind
import Leader.AAFJ.Centered.Sanitation

/-!
# Physical terminal seam for the centered AAFJ protocol

This module turns the canonical rank-one stopping certificate into statements
about the literal physical endpoint.  It also instantiates the end-to-end
numerical theorem with the concrete four-mode terminal process.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace TerminalPhysical

open SingleBarrierSanitation
open CoalescenceTrial
open CenteredFixedBlockDescent
open ComplexityConstants
open EndToEndBind
open FiniteUniformStoppingTree
open TerminalRankOne

set_option autoImplicit false

/-! ## Generic domination by a sound stopping strategy -/

/-- Stop a raw process on the first child satisfying `done`. -/
def predicateStopStep {P : Type} {n : Nat}
    (physicalStep : P -> Fin n -> P) (done : P -> Prop)
    [DecidablePred done] : P -> Fin n -> StopNode P :=
  fun state edge =>
    let child := physicalStep state edge
    if done child then .success else .active child

/-- Stop already at time zero when the initial raw state satisfies `done`. -/
def predicateInitialNode {P : Type} (done : P -> Prop)
    [DecidablePred done] (state : P) : StopNode P :=
  if done state then .success else .active state

/-- A strategy that never fails and stops only on a `done` physical child
upper-bounds the raw first-`done` active cost.  It may stop later than the raw
process, which is why only soundness of success is required. -/
theorem predicateCost_le_soundStrategy
    {P R : Type} {n : Nat}
    (physicalStep : P -> Fin n -> P) (done : P -> Prop)
    [DecidablePred done]
    (strategyStep : R -> Fin n -> StopNode R) (physical : R -> P)
    (hactive : forall state edge child,
      strategyStep state edge = .active child ->
        physical child = physicalStep (physical state) edge)
    (hsuccess : forall state edge,
      strategyStep state edge = .success ->
        done (physicalStep (physical state) edge))
    (hfailure : forall state edge,
      strategyStep state edge ≠ .failure) :
    forall state T,
      truncatedActiveCostNumerator (predicateStopStep physicalStep done)
          (predicateInitialNode done (physical state)) T <=
        truncatedActiveCostNumerator strategyStep (.active state) T := by
  intro state T
  induction T generalizing state with
  | zero => simp [truncatedActiveCostNumerator]
  | succ T ih =>
      by_cases hdone : done (physical state)
      · simp [predicateInitialNode, hdone,
          truncatedActiveCostNumerator]
      · simp only [predicateInitialNode, hdone, if_false,
          truncatedActiveCostNumerator]
        apply Nat.add_le_add_left
        apply ofFn_sum_le
        intro edge
        generalize hnode : strategyStep state edge = node
        cases node with
        | success =>
            have hchildDone := hsuccess state edge hnode
            have hraw : predicateStopStep physicalStep done
                (physical state) edge = .success := by
              simp [predicateStopStep, hchildDone]
            rw [hraw]
            cases T <;> simp [truncatedActiveCostNumerator]
        | failure =>
            exact False.elim (hfailure state edge hnode)
        | active child =>
            have hphysical := hactive state edge child hnode
            by_cases hchildDone : done (physicalStep (physical state) edge)
            · have hraw : predicateStopStep physicalStep done
                  (physical state) edge = .success := by
                simp [predicateStopStep, hchildDone]
              rw [hraw]
              cases T <;> simp [truncatedActiveCostNumerator]
            · have hchildNotDone : ¬ done (physical child) := by
                simpa [hphysical] using hchildDone
              simpa [predicateStopStep, hchildDone, hphysical,
                predicateInitialNode, hchildNotDone] using ih child

/-- A clean canonical cut, together with the physical unique-barrier witness
used to form that cut, is an actual physical clean configuration. -/
theorem clean_of_canonicalClean_cutView
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (C : Fin n -> State k) (barrier ell : Fin n)
    (hone : OneBarrierAt hk ring C barrier)
    (hclean : CanonicalClean hk ring (cutView ring barrier C) ell) :
    Clean hk ring C := by
  refine ⟨cutPos ring barrier ell, barrier, hone, ?_⟩
  simpa [CleanData] using hclean.2

/-- Canonical cleanliness of the exact reindexed terminal child implies
physical cleanliness of the actual raw child. -/
theorem clean_literalStep_of_canonicalCutSuccessor
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring) (rawEdge ell : Fin n)
    (hclean : CanonicalClean hk ring
      (Rank.cutSuccessor hk ring
        (cutView ring state.barrier state.config)
        (cutCoord ring state.barrier rawEdge)) ell) :
    Clean hk ring (literalStep hn3 hndvd state rawEdge).config := by
  apply clean_of_canonicalClean_cutView
    (literalStep hn3 hndvd state rawEdge).config
    (literalStep hn3 hndvd state rawEdge).barrier ell
    (literalStep hn3 hndvd state rawEdge).oneBarrier
  rw [literalStep_cutView_eq_cutSuccessor]
  exact hclean

/-- Physical `Clean` is closed under the exact literal transition carried by
the one-barrier state. -/
theorem clean_literalStep
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring)
    (hclean : Clean hk ring state.config) (rawEdge : Fin n) :
    Clean hk ring (literalStep hn3 hndvd state rawEdge).config := by
  exact Sanitation.clean_step hk ring hn3 hndvd
    state.config hclean rawEdge

/-- Every success branch of the concrete terminal machine lands on a physical
clean raw successor; the state-dependent edge view is the literal cut
coordinate of the selected physical edge. -/
theorem terminalSuccess_implies_literalStep_clean
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (physical : LiteralState hk ring) (canonical : TerminalState hk ring)
    (hrelated : canonical.configuration =
      cutView ring physical.barrier physical.config)
    (rawEdge : Fin n)
    (hsuccess : terminalStep hn3 hndvd canonical
      (cutCoord ring physical.barrier rawEdge) = .success) :
    Clean hk ring (literalStep hn3 hndvd physical rawEdge).config := by
  obtain ⟨ell, hell⟩ :=
    (terminalStep_eq_success_iff hn3 hndvd canonical
      (cutCoord ring physical.barrier rawEdge)).mp hsuccess
  apply clean_literalStep_of_canonicalCutSuccessor
    hn3 hndvd physical rawEdge ell
  simpa [hrelated] using hell

/-! ## Exact raw-edge refinement of the terminal process -/

/-- The canonical terminal state is the current physical state viewed from
its moving unique barrier. -/
def TerminalRelated {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (physical : LiteralState hk ring) (canonical : TerminalState hk ring) :
    Prop :=
  canonical.configuration =
    cutView ring physical.barrier physical.config

theorem terminalRelated_active
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (physical : LiteralState hk ring) (canonical : TerminalState hk ring)
    (hrelated : TerminalRelated physical canonical) (rawEdge : Fin n)
    (next : TerminalState hk ring)
    (hactive : terminalStep hn3 hndvd canonical
      (cutCoord ring physical.barrier rawEdge) = .active next) :
    TerminalRelated (literalStep hn3 hndvd physical rawEdge) next := by
  unfold TerminalRelated at hrelated ⊢
  calc
    next.configuration =
        Rank.cutSuccessor hk ring canonical.configuration
          (cutCoord ring physical.barrier rawEdge) :=
      terminalStep_active_configuration hn3 hndvd canonical next
        (cutCoord ring physical.barrier rawEdge) hactive
    _ = Rank.cutSuccessor hk ring
          (cutView ring physical.barrier physical.config)
          (cutCoord ring physical.barrier rawEdge) := by rw [hrelated]
    _ = cutView ring (literalStep hn3 hndvd physical rawEdge).barrier
          (literalStep hn3 hndvd physical rawEdge).config :=
      (literalStep_cutView_eq_cutSuccessor
        hn3 hndvd physical rawEdge).symm

/-- The concrete terminal strategy driven by literal raw physical edges. -/
noncomputable def terminalPhysicalStrategyStep
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) :
    ReindexedStopState (LiteralState hk ring) (TerminalState hk ring)
        TerminalRelated -> Fin n ->
      StopNode (ReindexedStopState (LiteralState hk ring)
        (TerminalState hk ring) TerminalRelated) :=
  reindexedStopStep (literalStep hn3 hndvd) (terminalStep hn3 hndvd)
    (fun physical rawEdge => cutCoord ring physical.barrier rawEdge)
    TerminalRelated (terminalRelated_active hn3 hndvd)

theorem terminalPhysicalStrategyStep_active_physical
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state child : ReindexedStopState (LiteralState hk ring)
      (TerminalState hk ring) TerminalRelated)
    (rawEdge : Fin n)
    (hactive : terminalPhysicalStrategyStep hn3 hndvd state rawEdge =
      .active child) :
    child.physical = literalStep hn3 hndvd state.physical rawEdge := by
  rcases state with ⟨physical, canonical, hrelated⟩
  simp only [terminalPhysicalStrategyStep, reindexedStopStep] at hactive
  split at hactive
  · injection hactive with hchild
    subst child
    rfl
  · contradiction
  · contradiction

theorem terminalPhysicalStrategyStep_success_clean
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : ReindexedStopState (LiteralState hk ring)
      (TerminalState hk ring) TerminalRelated)
    (rawEdge : Fin n)
    (hsuccess : terminalPhysicalStrategyStep hn3 hndvd state rawEdge =
      .success) :
    Clean hk ring
      (literalStep hn3 hndvd state.physical rawEdge).config := by
  rcases state with ⟨physical, canonical, hrelated⟩
  simp only [terminalPhysicalStrategyStep, reindexedStopStep] at hsuccess
  split at hsuccess
  · contradiction
  · exact terminalSuccess_implies_literalStep_clean
      hn3 hndvd physical canonical hrelated rawEdge (by assumption)
  · contradiction

theorem terminalPhysicalStrategyStep_ne_failure
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : ReindexedStopState (LiteralState hk ring)
      (TerminalState hk ring) TerminalRelated)
    (rawEdge : Fin n) :
    terminalPhysicalStrategyStep hn3 hndvd state rawEdge ≠ .failure := by
  rcases state with ⟨physical, canonical, hrelated⟩
  simp only [terminalPhysicalStrategyStep, reindexedStopStep]
  split
  · simp
  · simp
  · rename_i hfailure
    exact False.elim
      (terminalStep_ne_failure hn3 hndvd canonical
        (cutCoord ring physical.barrier rawEdge) hfailure)

/-- Reindexing by the moving physical cut preserves the exact complete
scheduler-tree numerator at every finite horizon. -/
theorem terminalPhysicalStrategyCost_eq_canonical
    {n k T : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : ReindexedStopState (LiteralState hk ring)
      (TerminalState hk ring) TerminalRelated) :
    truncatedActiveCostNumerator
        (terminalPhysicalStrategyStep hn3 hndvd) (.active state) T =
      truncatedActiveCostNumerator (terminalStep hn3 hndvd)
        (.active state.canonical) T := by
  exact truncatedActiveCostNumerator_reindexedStopStep_eq
    (literalStep hn3 hndvd) (terminalStep hn3 hndvd)
    (fun physical rawEdge => cutCoord ring physical.barrier rawEdge)
    (fun physical canonicalEdge =>
      cutPos ring physical.barrier canonicalEdge)
    (fun physical edge => cutPos_cutCoord ring physical.barrier edge)
    (fun physical edge => cutCoord_cutPos ring physical.barrier edge)
    TerminalRelated (terminalRelated_active hn3 hndvd) (.active state) T

/-- Exact raw first-physical-`Clean` truncated numerator from a rank-one
literal endpoint. -/
noncomputable def literalTerminalRawCleanCostNumerator
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring) (T : Nat) : Nat := by
  classical
  exact truncatedActiveCostNumerator
    (predicateStopStep (literalStep hn3 hndvd)
      (fun endpoint => Clean hk ring endpoint.config))
    (predicateInitialNode
      (fun endpoint => Clean hk ring endpoint.config) state) T

/-- A nonclean rank-zero physical endpoint gives the live canonical terminal
state used by both the reindexed and canonical stopping trees. -/
noncomputable def terminalStateOfNotClean
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (state : LiteralState hk ring)
    (hzero : literalExcessRank state = 0)
    (hnotClean : ¬ Clean hk ring state.config) : TerminalState hk ring :=
  { configuration := cutView ring state.barrier state.config
    rankOne := literalRankOneCut state hzero
    notClean := by
      rintro ⟨ell, hell⟩
      exact hnotClean (clean_of_canonicalClean_cutView
        state.config state.barrier ell state.oneBarrier hell) }

/-- The paired physical/canonical initial state for the nonclean terminal
lane. -/
noncomputable def terminalReindexedStateOfNotClean
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (state : LiteralState hk ring)
    (hzero : literalExcessRank state = 0)
    (hnotClean : ¬ Clean hk ring state.config) :
    ReindexedStopState (LiteralState hk ring) (TerminalState hk ring)
      TerminalRelated :=
  ⟨state, terminalStateOfNotClean state hzero hnotClean, rfl⟩

/-- The exact raw first-`Clean` cost on the terminal lane is dominated by the
canonical four-mode stopping tree. -/
theorem literalTerminalRawCleanCostNumerator_le_canonical
    {n k T : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring)
    (hzero : literalExcessRank state = 0) :
    literalTerminalRawCleanCostNumerator hn3 hndvd state T <=
      literalTerminalCanonicalCostNumerator
        (terminalStep hn3 hndvd) state T := by
  classical
  by_cases hclean : Clean hk ring state.config
  · have hraw : literalTerminalRawCleanCostNumerator
        hn3 hndvd state T = 0 := by
      unfold literalTerminalRawCleanCostNumerator
      simp only [predicateInitialNode, hclean, if_true]
      cases T <;> rfl
    rw [hraw]
    exact Nat.zero_le _
  · let canonical := terminalStateOfNotClean state hzero hclean
    let paired := terminalReindexedStateOfNotClean state hzero hclean
    have hdom := predicateCost_le_soundStrategy
      (literalStep hn3 hndvd)
      (fun endpoint => Clean hk ring endpoint.config)
      (terminalPhysicalStrategyStep hn3 hndvd)
      (fun paired => paired.physical)
      (fun paired edge child hactive =>
        terminalPhysicalStrategyStep_active_physical
          hn3 hndvd paired child edge hactive)
      (terminalPhysicalStrategyStep_success_clean hn3 hndvd)
      (terminalPhysicalStrategyStep_ne_failure hn3 hndvd)
      paired T
    have hreindex := terminalPhysicalStrategyCost_eq_canonical
      (T := T) hn3 hndvd paired
    calc
      literalTerminalRawCleanCostNumerator hn3 hndvd state T <=
          truncatedActiveCostNumerator
            (terminalPhysicalStrategyStep hn3 hndvd) (.active paired) T := by
        simpa [literalTerminalRawCleanCostNumerator, paired,
          terminalReindexedStateOfNotClean] using hdom
      _ = truncatedActiveCostNumerator (terminalStep hn3 hndvd)
          (.active canonical) T := by
        simpa [paired, terminalReindexedStateOfNotClean, canonical] using
          hreindex
      _ = literalTerminalCanonicalCostNumerator
          (terminalStep hn3 hndvd) state T := by
        simp only [literalTerminalCanonicalCostNumerator, hzero, dite_true]
        unfold literalTerminalInitialNode initialNode
        split
        · rename_i hcanonicalClean
          exact False.elim ((terminalStateOfNotClean state hzero hclean).notClean
            hcanonicalClean)
        · rfl

/-- Published terminal budget for the actual raw first-physical-`Clean`
numerator. -/
theorem literalTerminalRawCleanCostNumerator_le_terminalBudget
    {n k T : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring)
    (hzero : literalExcessRank state = 0) :
    literalTerminalRawCleanCostNumerator hn3 hndvd state T <=
      n ^ T * terminalBudget n := by
  exact Nat.le_trans
    (literalTerminalRawCleanCostNumerator_le_canonical
      hn3 hndvd state hzero)
    (literalTerminalCanonicalCostNumerator_le hn3
      (terminalStep hn3 hndvd)
      (terminalNatBellmanSuperSolution hn3 hndvd) state hzero)

/-- Endpoint-retaining all-state composition whose final continuation is the
actual raw first-physical-`Clean` numerator, rather than a canonical proxy. -/
noncomputable def allStateEndToEndRawTerminalCostNumerator
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Config n k) (T J U : Nat) : Nat :=
  allStateSequentialCostNumerator hk ring hn3 hndvd C
    (fun state => centeredRankThenTerminalCostNumerator hn3 hndvd
      (fun endpoint =>
        literalTerminalRawCleanCostNumerator hn3 hndvd endpoint U)
      state J U)
    T (rankBlockHorizon n * J + U)

/-- Coalescence and strict-rank descent compose with the actual raw terminal
first-`Clean` cost within the published cubic budget. -/
theorem allStateEndToEndRawTerminalCostNumerator_le_540_cube
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Config n k) (T J U : Nat) :
    allStateEndToEndRawTerminalCostNumerator
        hk ring hn3 hndvd C T J U <=
      n ^ (T + (rankBlockHorizon n * J + U)) * (540 * n ^ 3) := by
  unfold allStateEndToEndRawTerminalCostNumerator
  apply allStateEndToEndCostNumerator_le_540_cube_of_terminalCost
    hk ring hn3 hndvd C
  intro state hzero
  exact literalTerminalRawCleanCostNumerator_le_terminalBudget
    hn3 hndvd state hzero

/-- The concrete terminal producer removes the final `hsuper` parameter from
the all-state numerical composition. -/
theorem allStateEndToEndConcreteCostNumerator_le_540_cube
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Config n k) (T J U : Nat) :
    allStateEndToEndCanonicalCostNumerator hk ring hn3 hndvd C
        (terminalStep hn3 hndvd) T J U <=
      n ^ (T + (rankBlockHorizon n * J + U)) * (540 * n ^ 3) := by
  exact allStateEndToEndCanonicalCostNumerator_le_540_cube
    hk ring hn3 hndvd C (terminalStep hn3 hndvd)
    (terminalNatBellmanSuperSolution hn3 hndvd) T J U

end TerminalPhysical
end CenteredRenewal
end AAFJPK
