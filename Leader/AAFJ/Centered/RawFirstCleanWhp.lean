import Leader.AAFJ.Centered.RawFirstClean

/-!
# Finite-count tail for raw first-Clean centered AAFJ

This module turns the state-uniform raw first-`Clean` interaction-cost bound
into exact natural-number miss bounds.  The stopped tree tests `Clean` at time
zero, applies one literal `rawStep` at every active node, and tests the child
before retaining it as the endpoint of the next block.

The repeated-block theorem is an exact finite-tree calculation.  Every live
prefix retains its literal physical endpoint, to which the same one-block
bound applies.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace RawFirstCleanWhp

open FiniteUniformStoppingTree
open ComplexityConstants
open SingleBarrierSanitation
open CoalescenceTrial
open TerminalPhysical
open RawFirstClean

set_option autoImplicit false

/-! ## Endpoint-retaining finite-tree composition -/

/-- A state-uniform scaled miss bound composes after an arbitrary prefix of a
first-predicate stopped tree.  A live prefix child is the literal physical
child and is known not to satisfy `done`, so the suffix starts from exactly
that child. -/
theorem predicateActiveCount_add_le_mul_scaled
    {P : Type} {n : Nat}
    (physicalStep : P -> Fin n -> P) (done : P -> Prop)
    [DecidablePred done] (a b d B : Nat)
    (hB : forall state,
      d * activeCount (predicateStopStep physicalStep done)
          (predicateInitialNode done state) b <= B) :
    forall state,
      d * activeCount (predicateStopStep physicalStep done)
          (predicateInitialNode done state) (a + b) <=
        activeCount (predicateStopStep physicalStep done)
          (predicateInitialNode done state) a * B := by
  intro state
  induction a generalizing state with
  | zero =>
      by_cases hdone : done state
      · simp [predicateInitialNode, hdone, activeCount,
          treeWeight_success, activeWeight]
      · simpa [predicateInitialNode, hdone, activeCount, treeWeight,
          activeWeight] using hB state
  | succ a ih =>
      by_cases hdone : done state
      · simp [predicateInitialNode, hdone, activeCount,
          treeWeight_success, activeWeight]
      · have hchild : forall edge : Fin n,
            d * activeCount (predicateStopStep physicalStep done)
                (predicateStopStep physicalStep done state edge) (a + b) <=
              B * activeCount (predicateStopStep physicalStep done)
                (predicateStopStep physicalStep done state edge) a := by
          intro edge
          by_cases hdoneChild : done (physicalStep state edge)
          · simp [predicateStopStep, hdoneChild, activeCount,
              treeWeight_success, activeWeight]
          · have hi := ih (physicalStep state edge)
            simpa [predicateStopStep, predicateInitialNode, hdoneChild,
              Nat.mul_comm] using hi
        simp only [Nat.succ_add, predicateInitialNode, hdone, if_false,
          activeCount, treeWeight, stepNode]
        calc
          d * (List.ofFn (fun edge : Fin n =>
                treeWeight (predicateStopStep physicalStep done) activeWeight
                  (predicateStopStep physicalStep done state edge)
                  (a + b))).sum =
              (List.ofFn (fun edge : Fin n =>
                d * treeWeight (predicateStopStep physicalStep done)
                  activeWeight
                  (predicateStopStep physicalStep done state edge)
                  (a + b))).sum :=
            (ofFn_sum_mul_left d _).symm
          _ <= (List.ofFn (fun edge : Fin n =>
                B * treeWeight (predicateStopStep physicalStep done)
                  activeWeight
                  (predicateStopStep physicalStep done state edge) a)).sum :=
            ofFn_sum_le _ _ hchild
          _ = B * (List.ofFn (fun edge : Fin n =>
                treeWeight (predicateStopStep physicalStep done) activeWeight
                  (predicateStopStep physicalStep done state edge) a)).sum :=
            ofFn_sum_mul_left B _
          _ = (List.ofFn (fun edge : Fin n =>
                treeWeight (predicateStopStep physicalStep done) activeWeight
                  (predicateStopStep physicalStep done state edge) a)).sum * B :=
            Nat.mul_comm _ _

/-! ## Physical raw first-Clean miss counts -/

/-- Exact number of length-`R` raw scheduler words that have not visited
physical `Clean` at any time from `0` through `R`. -/
noncomputable def physicalRawCleanMissCount
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Config n k) (R : Nat) : Nat := by
  classical
  exact activeCount
    (predicateStopStep (rawStep hk ring) (Clean hk ring))
    (predicateInitialNode (Clean hk ring) C) R

/-- The common physical block horizon used for the half-tail estimate. -/
def physicalRawCleanBlockHorizon (n : Nat) : Nat :=
  1080 * n ^ 3

/-- Finite Markov at the physical block horizon: at most half of the exact
`n^H` scheduler words remain non-`Clean` through time `H`. -/
theorem two_mul_physicalRawCleanMissCount_le_pow
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) (C : Config n k) :
    2 * physicalRawCleanMissCount hk ring C
          (physicalRawCleanBlockHorizon n) <=
      n ^ physicalRawCleanBlockHorizon n := by
  classical
  let H := physicalRawCleanBlockHorizon n
  have hH : 0 < H := by
    dsimp [H, physicalRawCleanBlockHorizon]
    exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have hcostRaw := physicalRawCleanCostNumerator_le_540_cube
    hk ring hn3 hndvd C H
  have hcost :
      1 * truncatedActiveCostNumerator
          (predicateStopStep (rawStep hk ring) (Clean hk ring))
          (predicateInitialNode (Clean hk ring) C) H <=
        (540 * n ^ 3) * n ^ H := by
    simpa [physicalRawCleanCostNumerator, Nat.mul_comm] using hcostRaw
  have hscale : 2 * (540 * n ^ 3) <= H * 1 := by
    simp [H, physicalRawCleanBlockHorizon]
    omega
  have htail := two_mul_activeCount_le_pow_of_scaled_cost
    (predicateStopStep (rawStep hk ring) (Clean hk ring))
    (predicateInitialNode (Clean hk ring) C)
    hH (by omega) hcost hscale
  simpa [physicalRawCleanMissCount, H] using htail

/-- Exact state-uniform block amplification.  After `m` consecutive physical
blocks, every live prefix continues from its retained raw configuration and
the miss numerator gains one factor of `2` per block. -/
theorem pow_two_mul_physicalRawCleanMissCount_le_pow
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n) (m : Nat) (C : Config n k) :
    2 ^ m * physicalRawCleanMissCount hk ring C
          (m * physicalRawCleanBlockHorizon n) <=
      n ^ (m * physicalRawCleanBlockHorizon n) := by
  classical
  induction m with
  | zero =>
      by_cases hclean : Clean hk ring C
      · simp [physicalRawCleanMissCount, predicateInitialNode, hclean,
          activeCount, treeWeight, activeWeight]
      · simp [physicalRawCleanMissCount, predicateInitialNode, hclean,
          activeCount, treeWeight, activeWeight]
  | succ m ih =>
      have hblock : forall D : Config n k,
          2 * activeCount
              (predicateStopStep (rawStep hk ring) (Clean hk ring))
              (predicateInitialNode (Clean hk ring) D)
              (physicalRawCleanBlockHorizon n) <=
            n ^ physicalRawCleanBlockHorizon n := by
        intro D
        simpa [physicalRawCleanMissCount] using
          two_mul_physicalRawCleanMissCount_le_pow
            hk ring hn3 hndvd D
      have hcompose := predicateActiveCount_add_le_mul_scaled
        (rawStep hk ring) (Clean hk ring)
        (m * physicalRawCleanBlockHorizon n)
        (physicalRawCleanBlockHorizon n) 2
        (n ^ physicalRawCleanBlockHorizon n) hblock C
      have hscaled := Nat.mul_le_mul_left (2 ^ m) hcompose
      have hi := Nat.mul_le_mul_right
        (n ^ physicalRawCleanBlockHorizon n) ih
      calc
        2 ^ (m + 1) * physicalRawCleanMissCount hk ring C
            ((m + 1) * physicalRawCleanBlockHorizon n) =
            2 ^ m * (2 * physicalRawCleanMissCount hk ring C
              (m * physicalRawCleanBlockHorizon n +
                physicalRawCleanBlockHorizon n)) := by
              rw [Nat.pow_succ, Nat.succ_mul]
              ac_rfl
        _ <= (2 ^ m * physicalRawCleanMissCount hk ring C
              (m * physicalRawCleanBlockHorizon n)) *
            n ^ physicalRawCleanBlockHorizon n := by
              simpa [physicalRawCleanMissCount, Nat.mul_assoc] using hscaled
        _ <= n ^ (m * physicalRawCleanBlockHorizon n) *
            n ^ physicalRawCleanBlockHorizon n := hi
        _ = n ^ ((m + 1) * physicalRawCleanBlockHorizon n) := by
          rw [← Nat.pow_add]
          congr 1
          rw [Nat.succ_mul]

end RawFirstCleanWhp
end CenteredRenewal
end AAFJPK
