import Leader.AAFJ.Centered.TerminalPhysical

/-!
# Raw first-Clean finite-horizon composition for centered AAFJ

The fixed-horizon numerators in `AAFJCenteredEndToEndBind` pad a continuation
after a *fixed* first-stage horizon.  They are useful budget certificates, but
they do not themselves describe the raw first-`Clean` process when the first
stage is still active at that horizon.

This module supplies the complementary same-total-horizon bind.  A successful
first stage starts its endpoint-dependent continuation with exactly the
remaining raw scheduler coordinates.  The generic domination theorem permits
the raw predicate to become true during an earlier stage: the staged strategy
may stop later, never earlier.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace RawFirstClean

open FiniteUniformStoppingTree
open PayloadFiniteStoppingTree
open FixedBlockStrongRankDescent
open CenteredFixedBlockDescent
open CoalescenceGlobal
open EndToEndBind
open TerminalPhysical
open ComplexityConstants
open SingleBarrierSanitation
open CoalescenceTrial

set_option autoImplicit false

/-! ## Physical domination through an endpoint-retaining stage -/

/-- If every active or successful first-stage child is the literal physical
child, failures are impossible, and the endpoint continuation dominates the
raw predicate cost from that endpoint, then the same-total-horizon staged cost
dominates raw first-predicate cost.  No premise says that `done` stays false
during the first stage. -/
theorem predicateCost_le_remainingHorizonSequential
    {P A S F : Type} {n : Nat}
    (physicalStep : P -> Fin n -> P) (done : P -> Prop)
    [DecidablePred done]
    (stageStep : A -> Fin n -> PayloadNode A S F)
    (activePhysical : A -> P) (successPhysical : S -> P)
    (continuationCost : S -> Nat -> Nat)
    (hactive : forall state edge child,
      stageStep state edge = .active child ->
        activePhysical child = physicalStep (activePhysical state) edge)
    (hsuccess : forall state edge endpoint,
      stageStep state edge = .success endpoint ->
        successPhysical endpoint = physicalStep (activePhysical state) edge)
    (hfailure : forall state edge endpoint,
      stageStep state edge ≠ .failure endpoint)
    (hcontinuation : forall endpoint T,
      truncatedActiveCostNumerator (predicateStopStep physicalStep done)
          (predicateInitialNode done (successPhysical endpoint)) T <=
        continuationCost endpoint T) :
    forall state T,
      truncatedActiveCostNumerator (predicateStopStep physicalStep done)
          (predicateInitialNode done (activePhysical state)) T <=
        remainingHorizonSequentialCostNumerator stageStep continuationCost
          (.active state) T := by
  intro state T
  induction T generalizing state with
  | zero => simp [truncatedActiveCostNumerator,
      remainingHorizonSequentialCostNumerator]
  | succ T ih =>
      by_cases hdone : done (activePhysical state)
      · simp [predicateInitialNode, hdone, truncatedActiveCostNumerator,
          remainingHorizonSequentialCostNumerator]
      · simp only [predicateInitialNode, hdone, if_false,
          truncatedActiveCostNumerator,
          remainingHorizonSequentialCostNumerator, PayloadNode.erase,
          remainingHorizonTerminalBindMass]
        rw [Nat.add_assoc]
        apply Nat.add_le_add_left
        calc
          (List.ofFn (fun edge : Fin n =>
              truncatedActiveCostNumerator
                (predicateStopStep physicalStep done)
                (predicateStopStep physicalStep done
                  (activePhysical state) edge) T)).sum <=
              (List.ofFn (fun edge : Fin n =>
                truncatedActiveCostNumerator (eraseStep stageStep)
                    (stageStep state edge).erase T +
                  remainingHorizonTerminalBindMass stageStep
                    continuationCost (stageStep state edge) T)).sum := by
            apply ofFn_sum_le
            intro edge
            generalize hnode : stageStep state edge = node
            cases node with
            | active child =>
                have hphysical := hactive state edge child hnode
                simpa [predicateStopStep, predicateInitialNode, hphysical,
                  remainingHorizonSequentialCostNumerator] using ih child
            | success endpoint =>
                have hphysical := hsuccess state edge endpoint hnode
                cases T with
                | zero => simp [truncatedActiveCostNumerator]
                | succ T =>
                    simpa [predicateStopStep, predicateInitialNode, hphysical,
                      eraseStep, PayloadNode.erase,
                      remainingHorizonTerminalBindMass,
                      truncatedActiveCostNumerator] using
                        hcontinuation endpoint (T + 1)
            | failure endpoint =>
                exact False.elim (hfailure state edge endpoint hnode)
          _ = (List.ofFn (fun edge : Fin n =>
                truncatedActiveCostNumerator (eraseStep stageStep)
                  (stageStep state edge).erase T)).sum +
              (List.ofFn (fun edge : Fin n =>
                remainingHorizonTerminalBindMass stageStep continuationCost
                  (stageStep state edge) T)).sum :=
            ofFn_sum_add _ _

/-! ## Why the old fixed split is not a raw hitting-time numerator -/

private def fixedSplitCounterPhysicalStep (_ : Bool) (_ : Fin 1) : Bool :=
  true

private def fixedSplitCounterStageStep (_ : Unit) (_ : Fin 1) :
    PayloadNode Unit Unit PEmpty := .active ()

/-- With zero first-stage horizon the fixed-split fold discards an active
first stage, even though the next raw interaction hits the predicate.  Thus a
direct raw-cost domination theorem for `sequentialStageCostNumerator` is false
without a successful-first-stage or tail term. -/
theorem fixedSplitNumerator_does_not_dominate_raw :
    truncatedActiveCostNumerator
        (predicateStopStep fixedSplitCounterPhysicalStep (fun b => b = true))
        (predicateInitialNode (fun b => b = true) false) 1 = 1 ∧
      sequentialStageCostNumerator fixedSplitCounterStageStep
        (fun _ => 0) (.active ()) 0 1 = 0 := by
  decide

/-! ## Raw first-zero cost versus block-rounded cost -/

/-- Literal raw first-rank-zero cost, including a zero-time stop. -/
def firstZeroCostNumerator {S : Type} {n : Nat}
    (step : S -> Fin n -> S) (rank : S -> Nat)
    (state : S) (T : Nat) : Nat :=
  truncatedActiveCostNumerator
    (predicateStopStep step (fun endpoint => rank endpoint = 0))
    (predicateInitialNode (fun endpoint => rank endpoint = 0) state) T

private theorem truncatedActiveCostNumerator_zero
    {S : Type} {n : Nat} (step : S -> Fin n -> StopNode S)
    (node : StopNode S) :
    truncatedActiveCostNumerator step node 0 = 0 := rfl

private theorem truncatedActiveCostNumerator_success_zero
    {S : Type} {n : Nat} (step : S -> Fin n -> StopNode S) :
    forall T, truncatedActiveCostNumerator step .success T = 0 := by
  intro T
  cases T <;> rfl

private theorem sum_flatMap_nat {A : Type} (xs : List A)
    (f : A -> List Nat) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, List.sum_append]

private theorem sum_map_le_sum_map {A : Type} (xs : List A)
    (f g : A -> Nat) (hfg : forall x, x ∈ xs -> f x <= g x) :
    (xs.map f).sum <= (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      apply Nat.add_le_add
      · exact hfg x (by simp)
      · exact ih (fun y hy => hfg y (by simp [hy]))

theorem runWord_append {S : Type} {n : Nat}
    (step : S -> Fin n -> S) (state : S)
    (pre suffix : List (Fin n)) :
    runWord step state (pre ++ suffix) =
      runWord step (runWord step state pre) suffix := by
  induction pre generalizing state with
  | nil => rfl
  | cons edge tail ih =>
      simp only [List.cons_append, runWord_cons]
      exact ih (step state edge)

/-- Rebracket the exhaustive schedule sum at its first raw edge. -/
private theorem sum_allSchedules_runWord_succ {S : Type} {n : Nat}
    (step : S -> Fin n -> S) (value : S -> Nat)
    (state : S) (T : Nat) :
    ((allSchedules n (T + 1)).map (fun word =>
        value (runWord step state word))).sum =
      (List.ofFn (fun edge : Fin n =>
        ((allSchedules n T).map (fun word =>
          value (runWord step (step state edge) word))).sum)).sum := by
  rw [show T + 1 = 1 + T by omega,
    PPLLSchedulerBlocks.allSchedules_add]
  simp only [allSchedules, List.flatMap_singleton, List.nil_append,
    List.map_flatMap, sum_flatMap_nat, List.map_map,
    List.map_ofFn]
  apply ofFn_sum_eq
  intro edge
  apply congrArg List.sum
  apply List.map_congr_left
  intro word hword
  rfl

/-- Over a block prefix, raw first-zero cost is at most the full cost of all
`H` prefix interactions plus the exact continuation cost from every literal
block endpoint.  This deliberately overcharges words that hit zero inside the
block. -/
theorem firstZeroCostNumerator_add_le_blockPrefix
    {S : Type} {n : Nat}
    (step : S -> Fin n -> S) (rank : S -> Nat) :
    forall state H R,
      firstZeroCostNumerator step rank state (H + R) <=
        H * n ^ (H + R) +
          ((allSchedules n H).map (fun word =>
            firstZeroCostNumerator step rank
              (runWord step state word) R)).sum := by
  intro state H
  induction H generalizing state with
  | zero =>
      intro R
      simp [firstZeroCostNumerator, allSchedules]
  | succ H ih =>
      intro R
      by_cases hzero : rank state = 0
      · rw [show H + 1 + R = (H + R) + 1 by omega]
        simp [firstZeroCostNumerator, predicateInitialNode, hzero,
          truncatedActiveCostNumerator]
      · have hchildren :
            (List.ofFn (fun edge : Fin n =>
              firstZeroCostNumerator step rank (step state edge)
                (H + R))).sum <=
              (List.ofFn (fun edge : Fin n =>
                H * n ^ (H + R) +
                  ((allSchedules n H).map (fun word =>
                    firstZeroCostNumerator step rank
                      (runWord step (step state edge) word) R)).sum)).sum := by
          exact ofFn_sum_le _ _ (fun edge => ih (step state edge) R)
        have hschedules := sum_allSchedules_runWord_succ step
          (fun endpoint => firstZeroCostNumerator step rank endpoint R)
          state H
        rw [show H + 1 + R = (H + R) + 1 by omega]
        simp only [firstZeroCostNumerator, predicateInitialNode, hzero,
          if_false, truncatedActiveCostNumerator]
        change n ^ (H + R + 1) +
            (List.ofFn (fun edge : Fin n =>
              firstZeroCostNumerator step rank (step state edge)
                (H + R))).sum <=
          (H + 1) * n ^ (H + R + 1) +
            ((allSchedules n (H + 1)).map (fun word =>
              firstZeroCostNumerator step rank
                (runWord step state word) R)).sum
        calc
          n ^ (H + R + 1) +
              (List.ofFn (fun edge : Fin n =>
                firstZeroCostNumerator step rank (step state edge)
                  (H + R))).sum <=
            n ^ (H + R + 1) +
              (List.ofFn (fun edge : Fin n =>
                H * n ^ (H + R) +
                  ((allSchedules n H).map (fun word =>
                    firstZeroCostNumerator step rank
                      (runWord step (step state edge) word) R)).sum)).sum :=
            Nat.add_le_add_left hchildren _
          _ = (H + 1) * n ^ (H + R + 1) +
              (List.ofFn (fun edge : Fin n =>
                ((allSchedules n H).map (fun word =>
                  firstZeroCostNumerator step rank
                    (runWord step (step state edge) word) R)).sum)).sum := by
            rw [ofFn_sum_add, ofFn_sum_const]
            rw [Nat.pow_succ]
            simp only [Nat.add_mul, Nat.one_mul]
            ac_rfl
          _ = (H + 1) * n ^ (H + R + 1) +
              ((allSchedules n (H + 1)).map (fun word =>
                firstZeroCostNumerator step rank
                  (runWord step state word) R)).sum := by
            rw [hschedules]

/-- Checking zero after every raw interaction can only stop earlier than the
block-rounded process that checks at boundaries and charges each live block in
full. -/
theorem firstZeroCostNumerator_aligned_le_rounded
    {S : Type} {n : Nat}
    (step : S -> Fin n -> S) (rank : S -> Nat) (H : Nat) :
    forall state J,
      firstZeroCostNumerator step rank state (H * J) <=
        truncatedRoundedCostNumerator step rank H state J := by
  intro state J
  induction J generalizing state with
  | zero =>
      rw [firstZeroCostNumerator, truncatedRoundedCostNumerator]
      simpa using Nat.le_of_eq (truncatedActiveCostNumerator_zero
        (predicateStopStep step (fun endpoint => rank endpoint = 0))
        (predicateInitialNode (fun endpoint => rank endpoint = 0) state))
  | succ J ih =>
      by_cases hzero : rank state = 0
      · rw [firstZeroCostNumerator, predicateInitialNode]
        simp only [hzero, if_pos, truncatedRoundedCostNumerator]
        exact Nat.le_of_eq (truncatedActiveCostNumerator_success_zero
          (predicateStopStep step (fun endpoint => rank endpoint = 0)) _)
      · have hprefix := firstZeroCostNumerator_add_le_blockPrefix
          step rank state H (H * J)
        have hsum :
            ((allSchedules n H).map (fun word =>
              firstZeroCostNumerator step rank
                (runWord step state word) (H * J))).sum <=
              ((allSchedules n H).map (fun word =>
                truncatedRoundedCostNumerator step rank H
                  (runWord step state word) J)).sum := by
          apply sum_map_le_sum_map
          intro word hword
          exact ih (runWord step state word)
        rw [truncatedRoundedCostNumerator, if_neg hzero]
        calc
          firstZeroCostNumerator step rank state (H * (J + 1)) =
              firstZeroCostNumerator step rank state (H + H * J) := by
            rw [Nat.mul_succ, Nat.add_comm]
          _ <= H * n ^ (H + H * J) +
              ((allSchedules n H).map (fun word =>
                firstZeroCostNumerator step rank
                  (runWord step state word) (H * J))).sum := hprefix
          _ <= H * n ^ (H + H * J) +
              ((allSchedules n H).map (fun word =>
                truncatedRoundedCostNumerator step rank H
                  (runWord step state word) J)).sum :=
            Nat.add_le_add_left hsum _
          _ = H * (n ^ H) ^ (J + 1) +
              ((allSchedules n H).map (fun word =>
                truncatedRoundedCostNumerator step rank H
                  (runWord step state word) J)).sum := by
            congr 2
            have hexponent : H + H * J = H * (J + 1) := by
              rw [Nat.mul_succ, Nat.add_comm]
            rw [hexponent, Nat.pow_mul]

/-- A uniform block-rounded estimate implies the corresponding normalized
bound at every raw horizon.  We pad horizon `R` to `H * R`; positivity of `H`
makes this a genuine extension, and positivity of `n` cancels the padding
denominator. -/
theorem firstZeroCostNumerator_le_of_rounded
    {S : Type} {n H budget : Nat}
    (step : S -> Fin n -> S) (rank : S -> Nat)
    (hn : 0 < n) (hH : 0 < H)
    (hrounded : forall state J,
      truncatedRoundedCostNumerator step rank H state J <=
        (n ^ H) ^ J * budget) :
    forall state R,
      firstZeroCostNumerator step rank state R <= n ^ R * budget := by
  intro state R
  let K := H * R - R
  have hR : R <= H * R := by
    have h1 : 1 <= H := hH
    exact Nat.le_mul_of_pos_left R hH
  have hRK : R + K = H * R := by
    dsimp [K]
    omega
  have hpad := pow_mul_truncatedActiveCostNumerator_le_add
    (predicateStopStep step (fun endpoint => rank endpoint = 0))
    (predicateInitialNode (fun endpoint => rank endpoint = 0) state) R K
  have haligned := firstZeroCostNumerator_aligned_le_rounded
    step rank H state R
  have hround := hrounded state R
  have hchain : n ^ K * firstZeroCostNumerator step rank state R <=
      n ^ K * (n ^ R * budget) := by
    calc
      n ^ K * firstZeroCostNumerator step rank state R <=
          firstZeroCostNumerator step rank state (R + K) := hpad
      _ = firstZeroCostNumerator step rank state (H * R) := by rw [hRK]
      _ <= truncatedRoundedCostNumerator step rank H state R := haligned
      _ <= (n ^ H) ^ R * budget := hround
      _ = n ^ K * (n ^ R * budget) := by
        rw [← Nat.pow_mul]
        rw [← hRK, Nat.pow_add]
        ac_rfl
  exact Nat.le_of_mul_le_mul_left hchain (Nat.pow_pos hn)

/-! ## Endpoint-retaining centered rank descent -/

/-- The block-rounded centered certificate yields an exact raw-horizon bound
for first literal excess-rank zero. -/
theorem literalFirstRankZeroCostNumerator_le
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring) (R : Nat) :
    firstZeroCostNumerator (literalStep hn3 hndvd) literalExcessRank
        state R <=
      n ^ R * rankDescentBudget n := by
  apply firstZeroCostNumerator_le_of_rounded
    (H := rankBlockHorizon n) (budget := rankDescentBudget n)
    (literalStep hn3 hndvd) literalExcessRank
  · omega
  · unfold rankBlockHorizon
    omega
  · intro endpoint J
    exact centeredPaddedRankDescent_truncatedCost_le_publishedBudget
      hk ring hn3 hndvd endpoint J

/-- A literal rank-zero endpoint retained as physical continuation payload. -/
structure LiteralRankZeroEndpoint
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) where
  state : LiteralState hk ring
  rank_zero : literalExcessRank state = 0

/-- One literal interaction of the raw rank stage. -/
noncomputable def literalRankPayloadStep
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) :
    LiteralState hk ring -> Fin n ->
      PayloadNode (LiteralState hk ring)
        (LiteralRankZeroEndpoint hk ring) PEmpty :=
  fun state edge =>
    let child := literalStep hn3 hndvd state edge
    if hzero : literalExcessRank child = 0 then
      .success ⟨child, hzero⟩
    else .active child

/-- Stop at zero time if the supplied literal state already has zero excess
rank. -/
noncomputable def literalRankInitialNode
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (state : LiteralState hk ring) :
    PayloadNode (LiteralState hk ring)
      (LiteralRankZeroEndpoint hk ring) PEmpty :=
  if hzero : literalExcessRank state = 0 then
    .success ⟨state, hzero⟩
  else .active state

theorem erase_literalRankPayloadStep
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) :
    (eraseStep (literalRankPayloadStep hn3 hndvd) :
      LiteralState hk ring -> Fin n -> StopNode (LiteralState hk ring)) =
      predicateStopStep (literalStep hn3 hndvd)
        (fun state : LiteralState hk ring => literalExcessRank state = 0) := by
  funext state edge
  simp only [eraseStep, literalRankPayloadStep, predicateStopStep]
  split <;> rfl

theorem erase_literalRankInitialNode
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (state : LiteralState hk ring) :
    (literalRankInitialNode state).erase =
      predicateInitialNode (fun endpoint => literalExcessRank endpoint = 0)
        state := by
  simp only [literalRankInitialNode, predicateInitialNode]
  split <;> rfl

theorem literalRankPayloadStep_active_state
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state child : LiteralState hk ring) (edge : Fin n)
    (hactive : literalRankPayloadStep hn3 hndvd state edge = .active child) :
    child = literalStep hn3 hndvd state edge := by
  simp only [literalRankPayloadStep] at hactive
  split at hactive
  · contradiction
  · exact (PayloadNode.active.inj hactive).symm

theorem literalRankPayloadStep_success_state
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring) (edge : Fin n)
    (endpoint : LiteralRankZeroEndpoint hk ring)
    (hsuccess : literalRankPayloadStep hn3 hndvd state edge =
      .success endpoint) :
    endpoint.state = literalStep hn3 hndvd state edge := by
  simp only [literalRankPayloadStep] at hsuccess
  split at hsuccess
  · exact (congrArg LiteralRankZeroEndpoint.state
      (PayloadNode.success.inj hsuccess)).symm
  · contradiction

theorem literalRankPayloadStep_ne_failure
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring) (edge : Fin n)
    (failure : PEmpty) :
    literalRankPayloadStep hn3 hndvd state edge ≠ .failure failure := by
  simp only [literalRankPayloadStep]
  split <;> intro h <;> contradiction

/-- Same-total-horizon rank descent followed by raw physical terminal cleanup,
started from the supplied literal one-barrier state. -/
noncomputable def literalRankThenTerminalRawCostNumerator
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring) (R : Nat) : Nat :=
  remainingHorizonSequentialCostNumerator
    (literalRankPayloadStep hn3 hndvd)
    (fun endpoint T =>
      literalTerminalRawCleanCostNumerator hn3 hndvd endpoint.state T)
    (literalRankInitialNode state) R

/-- Uniform same-total-horizon one-barrier budget on actual physical
endpoints. -/
theorem literalRankThenTerminalRawCostNumerator_le
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring) (R : Nat) :
    literalRankThenTerminalRawCostNumerator hn3 hndvd state R <=
      n ^ R * oneBarrierBudget n := by
  unfold literalRankThenTerminalRawCostNumerator
  have hbound := remainingHorizonSequentialCostNumerator_le
    (literalRankPayloadStep hn3 hndvd)
    (fun endpoint T =>
      literalTerminalRawCleanCostNumerator hn3 hndvd endpoint.state T)
    (literalRankInitialNode state)
    (firstBudget := rankDescentBudget n)
    (continuationBudget := terminalBudget n)
    (fun T => by
      rw [erase_literalRankPayloadStep, erase_literalRankInitialNode]
      exact literalFirstRankZeroCostNumerator_le hn3 hndvd state T)
    (fun endpoint T =>
      literalTerminalRawCleanCostNumerator_le_terminalBudget
        (T := T) hn3 hndvd endpoint.state endpoint.rank_zero) R
  simpa [oneBarrierBudget_eq_rankDescent_add_terminal] using hbound

/-- The raw first-physical-`Clean` process may stop during rank descent.  The
endpoint-retaining staged process ignores such an early hit, so it is a
pathwise upper bound and requires no claim that `Clean` first appears at
`Phi = 1`. -/
theorem literalRawCleanCostNumerator_le_rankThenTerminal
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring) (R : Nat) :
    literalTerminalRawCleanCostNumerator hn3 hndvd state R <=
      literalRankThenTerminalRawCostNumerator hn3 hndvd state R := by
  classical
  by_cases hzero : literalExcessRank state = 0
  · cases R with
    | zero =>
        simp [literalTerminalRawCleanCostNumerator,
          literalRankThenTerminalRawCostNumerator,
          remainingHorizonSequentialCostNumerator,
          truncatedActiveCostNumerator]
    | succ R =>
        simp [literalRankThenTerminalRawCostNumerator,
          literalRankInitialNode, hzero,
          remainingHorizonSequentialCostNumerator,
          remainingHorizonTerminalBindMass]
  · have hdom := predicateCost_le_remainingHorizonSequential
      (literalStep hn3 hndvd)
      (fun endpoint : LiteralState hk ring => Clean hk ring endpoint.config)
      (literalRankPayloadStep hn3 hndvd)
      (fun endpoint : LiteralState hk ring => endpoint)
      (fun endpoint : LiteralRankZeroEndpoint hk ring => endpoint.state)
      (fun endpoint T =>
        literalTerminalRawCleanCostNumerator hn3 hndvd endpoint.state T)
      (fun source edge child hactive =>
        literalRankPayloadStep_active_state
          hn3 hndvd source child edge hactive)
      (fun source edge endpoint hsuccess =>
        literalRankPayloadStep_success_state
          hn3 hndvd source edge endpoint hsuccess)
      (fun source edge failure =>
        literalRankPayloadStep_ne_failure
          hn3 hndvd source edge failure)
      (fun endpoint T => Nat.le_refl _)
      state R
    simpa [literalTerminalRawCleanCostNumerator,
      literalRankThenTerminalRawCostNumerator,
      literalRankInitialNode, hzero] using hdom

/-! ## Physical configuration projection -/

theorem literalStep_config
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring) (edge : Fin n) :
    (literalStep hn3 hndvd state edge).config =
      rawStep hk ring state.config edge := rfl

/-- Exact raw first-physical-`Clean` truncated numerator on configurations. -/
noncomputable def physicalRawCleanCostNumerator
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Config n k) (R : Nat) : Nat := by
  classical
  exact truncatedActiveCostNumerator
    (predicateStopStep (rawStep hk ring) (Clean hk ring))
    (predicateInitialNode (Clean hk ring) C) R

/-- The literal one-barrier carrier is a conservative exact-configuration
lift of the raw process. -/
theorem physicalRawCleanCostNumerator_le_literal
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring) (R : Nat) :
    physicalRawCleanCostNumerator hk ring state.config R <=
      literalTerminalRawCleanCostNumerator hn3 hndvd state R := by
  classical
  by_cases hclean : Clean hk ring state.config
  · unfold physicalRawCleanCostNumerator
    unfold literalTerminalRawCleanCostNumerator
    simp only [predicateInitialNode, hclean, if_pos]
    rw [truncatedActiveCostNumerator_success_zero,
      truncatedActiveCostNumerator_success_zero]
    exact Nat.le_refl 0
  · have hdom := predicateCost_le_soundStrategy
      (rawStep hk ring) (Clean hk ring)
      (predicateStopStep (literalStep hn3 hndvd)
        (fun endpoint : LiteralState hk ring => Clean hk ring endpoint.config))
      (fun endpoint : LiteralState hk ring => endpoint.config)
      (fun source edge child hactive => by
        simp only [predicateStopStep] at hactive
        split at hactive
        · contradiction
        · have hchild := StopNode.active.inj hactive
          subst child
          exact literalStep_config hn3 hndvd source edge)
      (fun source edge hsuccess => by
        simp only [predicateStopStep] at hsuccess
        split at hsuccess
        · assumption
        · contradiction)
      (fun source edge => by
        simp only [predicateStopStep]
        split <;> intro h <;> contradiction) state R
    simpa [physicalRawCleanCostNumerator,
      literalTerminalRawCleanCostNumerator,
      predicateInitialNode, hclean] using hdom

theorem globalPayloadStep_active_config
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (hndvd : ¬ k ∣ n)
    (state child : GlobalActive hk ring hn2) (edge : Fin n)
    (hactive : globalPayloadStep hk ring hn2 hndvd state edge =
      .active child) :
    child.config = rawStep hk ring state.config edge := by
  have hconfig := globalStep_config hk ring hn2 hndvd state edge
  unfold globalPayloadStep at hactive
  cases hnode : globalStep hk ring hn2 hndvd state edge with
  | active next =>
      rw [hnode] at hconfig
      simp only [hnode] at hactive
      have hchild : next = child := PayloadNode.active.inj hactive
      subst child
      exact hconfig
  | oneBarrier endpoint => simp [hnode] at hactive

theorem globalPayloadStep_ne_failure
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (hndvd : ¬ k ∣ n)
    (state : GlobalActive hk ring hn2) (edge : Fin n)
    (failure : PEmpty) :
    globalPayloadStep hk ring hn2 hndvd state edge ≠ .failure failure := by
  unfold globalPayloadStep
  split <;> intro h <;> contradiction

/-! ## Arbitrary physical initialization -/

/-- Actual endpoint-retaining coalescence, rank descent, and terminal cleanup
on one common raw horizon.  A support-one configuration skips coalescence at
zero time. -/
noncomputable def allStateRemainingHorizonCostNumerator
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Config n k) (R : Nat) : Nat :=
  let M := supportCount hk ring C
  if hM1 : M = 1 then
    literalRankThenTerminalRawCostNumerator hn3 hndvd
      (literalStateOfSupportCountOne hk ring C hM1) R
  else
    have hMpos : 0 < M := supportCount_pos_of_not_dvd hk ring hndvd C
    have hM2 : 2 <= M := by omega
    remainingHorizonSequentialCostNumerator
      (globalPayloadStep hk ring (by omega) hndvd)
      (fun endpoint T => literalRankThenTerminalRawCostNumerator
        hn3 hndvd (oneBarrierEndpointToLiteralState endpoint) T)
      (.active (GlobalActive.seed (hk := hk) (ring := ring)
        (hn2 := by omega) C M hM2 rfl)) R

/-- The actual same-total-horizon staged cost has the published all-state
budget. -/
theorem allStateRemainingHorizonCostNumerator_le
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Config n k) (R : Nat) :
    allStateRemainingHorizonCostNumerator hk ring hn3 hndvd C R <=
      n ^ R * allStateBudget n := by
  let M := supportCount hk ring C
  by_cases hM1 : M = 1
  · have hone := literalRankThenTerminalRawCostNumerator_le
      hn3 hndvd (literalStateOfSupportCountOne hk ring C hM1) R
    calc
      allStateRemainingHorizonCostNumerator hk ring hn3 hndvd C R =
          literalRankThenTerminalRawCostNumerator hn3 hndvd
            (literalStateOfSupportCountOne hk ring C hM1) R := by
        simp [allStateRemainingHorizonCostNumerator, M, hM1]
      _ <= n ^ R * oneBarrierBudget n := hone
      _ <= n ^ R * allStateBudget n :=
        Nat.mul_le_mul_left _ (by simp [allStateBudget])
  · have hMpos : 0 < M := supportCount_pos_of_not_dvd hk ring hndvd C
    have hM2 : 2 <= M := by omega
    rw [show allStateRemainingHorizonCostNumerator hk ring hn3 hndvd C R =
        remainingHorizonSequentialCostNumerator
          (globalPayloadStep hk ring (by omega) hndvd)
          (fun endpoint T => literalRankThenTerminalRawCostNumerator
            hn3 hndvd (oneBarrierEndpointToLiteralState endpoint) T)
          (.active (GlobalActive.seed (hk := hk) (ring := ring)
            (hn2 := by omega) C M hM2 rfl)) R by
      simp [allStateRemainingHorizonCostNumerator, M, hM1]]
    have hbound := remainingHorizonSequentialCostNumerator_le
      (globalPayloadStep hk ring (by omega) hndvd)
      (fun endpoint T => literalRankThenTerminalRawCostNumerator
        hn3 hndvd (oneBarrierEndpointToLiteralState endpoint) T)
      (.active (GlobalActive.seed (hk := hk) (ring := ring)
        (hn2 := by omega) C M hM2 rfl))
      (firstBudget := 3 * n ^ 3)
      (continuationBudget := oneBarrierBudget n)
      (canonical_global_payload_duration_le_three_cubic
        hk ring (by omega) hndvd hM2 C rfl)
      (fun endpoint T => literalRankThenTerminalRawCostNumerator_le
        hn3 hndvd (oneBarrierEndpointToLiteralState endpoint) T) R
    simpa [allStateBudget] using hbound

/-- Raw first physical `Clean` from an arbitrary configuration is dominated
by the endpoint-retaining same-horizon staged process.  In particular, an
early `Clean` hit during coalescence or rank descent is accepted immediately by
the left process and can only reduce its cost. -/
theorem physicalRawCleanCostNumerator_le_allStateRemaining
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Config n k) (R : Nat) :
    physicalRawCleanCostNumerator hk ring C R <=
      allStateRemainingHorizonCostNumerator hk ring hn3 hndvd C R := by
  classical
  let M := supportCount hk ring C
  by_cases hM1 : M = 1
  · let state := literalStateOfSupportCountOne hk ring C hM1
    have hphysical := physicalRawCleanCostNumerator_le_literal
      hn3 hndvd state R
    have hrank := literalRawCleanCostNumerator_le_rankThenTerminal
      hn3 hndvd state R
    calc
      physicalRawCleanCostNumerator hk ring C R =
          physicalRawCleanCostNumerator hk ring state.config R := rfl
      _ <= literalTerminalRawCleanCostNumerator hn3 hndvd state R := hphysical
      _ <= literalRankThenTerminalRawCostNumerator hn3 hndvd state R := hrank
      _ = allStateRemainingHorizonCostNumerator
          hk ring hn3 hndvd C R := by
        simp [allStateRemainingHorizonCostNumerator, M, hM1, state]
  · have hMpos : 0 < M := supportCount_pos_of_not_dvd hk ring hndvd C
    have hM2 : 2 <= M := by omega
    let initial := GlobalActive.seed (hk := hk) (ring := ring)
      (hn2 := by omega) C M hM2 rfl
    have hdom := predicateCost_le_remainingHorizonSequential
      (rawStep hk ring) (Clean hk ring)
      (globalPayloadStep hk ring (by omega) hndvd)
      (fun state : GlobalActive hk ring (by omega) => state.config)
      (fun endpoint : OneBarrierEndpoint hk ring (by omega) =>
        endpoint.drop.config)
      (fun endpoint T => literalRankThenTerminalRawCostNumerator
        hn3 hndvd (oneBarrierEndpointToLiteralState endpoint) T)
      (fun source edge child hactive =>
        globalPayloadStep_active_config
          hk ring (by omega) hndvd source child edge hactive)
      (fun source edge endpoint hsuccess =>
        globalPayloadStep_success_config
          hk ring (by omega) hndvd source edge endpoint hsuccess)
      (fun source edge failure =>
        globalPayloadStep_ne_failure
          hk ring (by omega) hndvd source edge failure)
      (fun endpoint T => Nat.le_trans
        (by
          change physicalRawCleanCostNumerator hk ring
              endpoint.drop.config T <=
            literalTerminalRawCleanCostNumerator hn3 hndvd
              (oneBarrierEndpointToLiteralState endpoint) T
          exact physicalRawCleanCostNumerator_le_literal
            hn3 hndvd (oneBarrierEndpointToLiteralState endpoint) T)
        (literalRawCleanCostNumerator_le_rankThenTerminal
          hn3 hndvd (oneBarrierEndpointToLiteralState endpoint) T))
      initial R
    calc
      physicalRawCleanCostNumerator hk ring C R =
          physicalRawCleanCostNumerator hk ring initial.config R := rfl
      _ <= remainingHorizonSequentialCostNumerator
          (globalPayloadStep hk ring (by omega) hndvd)
          (fun endpoint T => literalRankThenTerminalRawCostNumerator
            hn3 hndvd (oneBarrierEndpointToLiteralState endpoint) T)
          (.active initial) R := by
        simpa [physicalRawCleanCostNumerator] using hdom
      _ = allStateRemainingHorizonCostNumerator
          hk ring hn3 hndvd C R := by
        simp [allStateRemainingHorizonCostNumerator, M, hM1, initial]

/-- Direct finite-horizon capstone for the literal raw scheduler from every
physical configuration. -/
theorem physicalRawCleanCostNumerator_le_540_cube
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (C : Config n k) (R : Nat) :
    physicalRawCleanCostNumerator hk ring C R <=
      n ^ R * (540 * n ^ 3) := by
  exact Nat.le_trans
    (physicalRawCleanCostNumerator_le_allStateRemaining
      hk ring hn3 hndvd C R)
    (Nat.le_trans
      (allStateRemainingHorizonCostNumerator_le
        hk ring hn3 hndvd C R)
      (Nat.mul_le_mul_left (n ^ R)
        (allStateBudget_le_540_cube n hn3)))

end RawFirstClean
end CenteredRenewal
end AAFJPK
