import Leader.Wu.Epoch.FilterProtectedPotential

/-!
# Protected-state action tree for the filtered epoch protocol

This is one layer of the mechanically split polynomial iid upper-bound proof.
Public declarations remain in the historical epoch-voter namespace.
-/

namespace PPLLEpochVoterPolynomialUpper

open PPLLEpochVoterReduction PPLLEpochVoterTwoDomain
  PPLLEpochVoterFiniteTree PPLLResearchFormulation
  PPLLProtectedEpochProtocol PPLLDerivedEpochRepair
  PPLLDerivedEpochRuntimeNoGo
open PPLLEpochVoterSumTools

/-! ## Full protected-state action tree -/

/-- Total full-state potential at depth `t` over all exact scheduler words. -/
noncomputable def filteredProtectedPotentialTreeTotal
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) :
    (Fin n → EpochAgentState n ψ κ) → Nat → Nat
  | C, 0 => filteredProtectedPotential C
  | C, t + 1 =>
      (List.ofFn (fun e => filteredProtectedPotentialTreeTotal hψ κ ring
        (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e) t)).sum

/-- The complete depth-`t` potential is bounded by `n^t (n^2+n)`. -/
theorem filteredProtectedPotentialTreeTotal_le
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat) :
    filteredProtectedPotentialTreeTotal hψ κ ring C t ≤
      n ^ t * (n ^ 2 + n) := by
  induction t generalizing C with
  | zero =>
      simpa [filteredProtectedPotentialTreeTotal] using
        filteredProtectedPotential_le C
  | succ t ih =>
      rw [filteredProtectedPotentialTreeTotal]
      calc
        (List.ofFn (fun e => filteredProtectedPotentialTreeTotal hψ κ ring
            (localStep ring
              (ppllEpochFilterTransition hψ κ ring.hn) C e) t)).sum ≤
            (List.ofFn (fun _ : Fin n => n ^ t * (n ^ 2 + n))).sum := by
              apply sum_ofFn_le
              intro e
              exact ih (localStep ring
                (ppllEpochFilterTransition hψ κ ring.hn) C e)
        _ = n * (n ^ t * (n ^ 2 + n)) := sum_ofFn_const n _
        _ = n ^ (t + 1) * (n ^ 2 + n) := by
          rw [Nat.pow_succ]
          grind

/-- Across one generation of the full action tree, every still-unprotected
prefix pays at least two units of potential drift. -/
theorem filteredProtectedPotentialTreeTotal_drift
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat) :
    n * filteredProtectedPotentialTreeTotal hψ κ ring C t +
        2 * filteredProtectedMissTree hψ κ ring C t ≤
      filteredProtectedPotentialTreeTotal hψ κ ring C (t + 1) := by
  induction t generalizing C with
  | zero =>
      simp only [filteredProtectedPotentialTreeTotal,
        filteredProtectedMissTree]
      by_cases hC : ProtectedEpoch ring.hn ring C
      · rw [if_pos hC,
          filteredProtectedPotential_step_sum hn2 hψ κ ring C]
        omega
      · rw [if_neg hC]
        exact filteredProtectedPotential_step_sum_live
          hn2 hψ κ ring C hC
  | succ t ih =>
      change n * (List.ofFn (fun e =>
          filteredProtectedPotentialTreeTotal hψ κ ring
            (localStep ring
              (ppllEpochFilterTransition hψ κ ring.hn) C e) t)).sum +
          2 * filteredProtectedMissTree hψ κ ring C (t + 1) ≤
        (List.ofFn (fun e =>
          filteredProtectedPotentialTreeTotal hψ κ ring
            (localStep ring
              (ppllEpochFilterTransition hψ κ ring.hn) C e) (t + 1))).sum
      have hchildren := sum_ofFn_le
        (fun e => n * filteredProtectedPotentialTreeTotal hψ κ ring
            (localStep ring
              (ppllEpochFilterTransition hψ κ ring.hn) C e) t +
          2 * filteredProtectedMissTree hψ κ ring
            (localStep ring
              (ppllEpochFilterTransition hψ κ ring.hn) C e) t)
        (fun e => filteredProtectedPotentialTreeTotal hψ κ ring
          (localStep ring
            (ppllEpochFilterTransition hψ κ ring.hn) C e) (t + 1))
        (fun e => ih (localStep ring
          (ppllEpochFilterTransition hψ κ ring.hn) C e))
      rw [sum_ofFn_add, sum_ofFn_mul_left,
        sum_ofFn_mul_left] at hchildren
      rw [filteredProtectedMissTree]
      by_cases hC : ProtectedEpoch ring.hn ring C
      · rw [if_pos hC]
        omega
      · rw [if_neg hC]
        exact hchildren

/-- Weighted survival sum for the full protected predicate. -/
noncomputable def filteredProtectedWeightedMissTotal
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) : Nat → Nat
  | 0 => 0
  | t + 1 => n * filteredProtectedWeightedMissTotal hψ κ ring C t +
      filteredProtectedMissTree hψ κ ring C t

/-- The physical potential telescope pays for the complete weighted protected
survival sum. -/
theorem filteredProtectedPotentialTree_telescope
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat) :
    n ^ t * filteredProtectedPotential C +
        2 * filteredProtectedWeightedMissTotal hψ κ ring C t ≤
      filteredProtectedPotentialTreeTotal hψ κ ring C t := by
  induction t with
  | zero => simp [filteredProtectedWeightedMissTotal,
      filteredProtectedPotentialTreeTotal]
  | succ t ih =>
      have hscaled := Nat.mul_le_mul_left n ih
      have hdrift := filteredProtectedPotentialTreeTotal_drift
        hn2 hψ κ ring C t
      rw [filteredProtectedWeightedMissTotal, Nat.pow_succ]
      calc
        n ^ t * n * filteredProtectedPotential C +
            2 * (n * filteredProtectedWeightedMissTotal hψ κ ring C t +
              filteredProtectedMissTree hψ κ ring C t) =
            n * (n ^ t * filteredProtectedPotential C +
              2 * filteredProtectedWeightedMissTotal hψ κ ring C t) +
              2 * filteredProtectedMissTree hψ κ ring C t := by grind
        _ ≤ n * filteredProtectedPotentialTreeTotal hψ κ ring C t +
              2 * filteredProtectedMissTree hψ κ ring C t := by
            exact Nat.add_le_add_right hscaled _
        _ ≤ filteredProtectedPotentialTreeTotal hψ κ ring C (t + 1) :=
          hdrift

theorem filteredProtectedWeightedMissTotal_budget
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat) :
    2 * filteredProtectedWeightedMissTotal hψ κ ring C t ≤
      n ^ t * (n ^ 2 + n) := by
  have htelescope := filteredProtectedPotentialTree_telescope
    hn2 hψ κ ring C t
  have hupper := filteredProtectedPotentialTreeTotal_le hψ κ ring C t
  omega

theorem filteredProtectedMissTree_succ_le_mul
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat) :
    filteredProtectedMissTree hψ κ ring C (t + 1) ≤
      n * filteredProtectedMissTree hψ κ ring C t := by
  induction t generalizing C with
  | zero =>
      simp only [filteredProtectedMissTree]
      by_cases hC : ProtectedEpoch ring.hn ring C
      · rw [if_pos hC, if_pos hC]
        exact Nat.zero_le _
      · rw [if_neg hC, if_neg hC]
        have hchildren := sum_ofFn_le
          (fun e => @ite Nat
            (ProtectedEpoch ring.hn ring
              (localStep ring
                (ppllEpochFilterTransition hψ κ ring.hn) C e))
            (Classical.propDecidable _) 0 1)
          (fun _ : Fin n => 1) (by
            intro e
            split <;> omega)
        rw [sum_ofFn_const] at hchildren
        simpa using hchildren
  | succ t ih =>
      simp only [filteredProtectedMissTree]
      by_cases hC : ProtectedEpoch ring.hn ring C
      · rw [if_pos hC, if_pos hC]
        exact Nat.zero_le _
      · rw [if_neg hC, if_neg hC]
        have hchildren := sum_ofFn_le
          (fun e => filteredProtectedMissTree hψ κ ring
            (localStep ring
              (ppllEpochFilterTransition hψ κ ring.hn) C e) (t + 1))
          (fun e => n * filteredProtectedMissTree hψ κ ring
            (localStep ring
              (ppllEpochFilterTransition hψ κ ring.hn) C e) t)
          (fun e => ih (localStep ring
            (ppllEpochFilterTransition hψ κ ring.hn) C e))
        rw [sum_ofFn_mul_left] at hchildren
        exact hchildren

theorem filteredProtectedMissTree_mul_time_le_weighted
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat) :
    (t + 1) * filteredProtectedMissTree hψ κ ring C t ≤
      filteredProtectedWeightedMissTotal hψ κ ring C (t + 1) := by
  induction t with
  | zero => simp [filteredProtectedWeightedMissTotal]
  | succ t ih =>
      have hmono := filteredProtectedMissTree_succ_le_mul hψ κ ring C t
      have hmonoScaled := Nat.mul_le_mul_left (t + 1) hmono
      have hihScaled := Nat.mul_le_mul_left n ih
      rw [filteredProtectedWeightedMissTotal]
      grind

/-- Exact finite-horizon moment inequality for the full protected predicate. -/
theorem filteredProtectedMissTree_tail_moment
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat) :
    2 * (t + 1) * filteredProtectedMissTree hψ κ ring C t ≤
      n ^ t * (n ^ 3 + n ^ 2) := by
  have hlower := filteredProtectedMissTree_mul_time_le_weighted
    hψ κ ring C t
  have hbudget := filteredProtectedWeightedMissTotal_budget
    hn2 hψ κ ring C (t + 1)
  have hchain :
      2 * ((t + 1) * filteredProtectedMissTree hψ κ ring C t) ≤
        2 * filteredProtectedWeightedMissTotal hψ κ ring C (t + 1) :=
    Nat.mul_le_mul_left 2 hlower
  have h := Nat.le_trans hchain hbudget
  have hscale : n ^ (t + 1) * (n ^ 2 + n) =
      n ^ t * (n ^ 3 + n ^ 2) := by
    simp only [Nat.pow_succ]
    grind
  rw [hscale] at h
  calc
    2 * (t + 1) * filteredProtectedMissTree hψ κ ring C t =
        2 * ((t + 1) * filteredProtectedMissTree hψ κ ring C t) := by
          rw [Nat.mul_assoc]
    _ ≤ n ^ t * (n ^ 3 + n ^ 2) := h

/-- Polynomial iid protected-state tail from every physical initialization. -/
theorem filteredProtectedMissTree_polynomial_tail
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (q t : Nat)
    (horizon : q * (n ^ 3 + n ^ 2) ≤ 2 * (t + 1)) :
    q * filteredProtectedMissTree hψ κ ring C t ≤ n ^ t := by
  have hmoment := filteredProtectedMissTree_tail_moment
    hn2 hψ κ ring C t
  have hscaled := Nat.mul_le_mul_right
    (filteredProtectedMissTree hψ κ ring C t) horizon
  have hchain := Nat.le_trans hscaled hmoment
  have hcommon :
      (n ^ 3 + n ^ 2) *
          (q * filteredProtectedMissTree hψ κ ring C t) ≤
        (n ^ 3 + n ^ 2) * n ^ t := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hchain
  have hpositive : 0 < n ^ 3 + n ^ 2 := by
    have hn3 := Nat.pow_pos ring.hn (n := 3)
    omega
  exact Nat.le_of_mul_le_mul_left hcommon hpositive

/-- Concrete one-eighth protected-state failure bound at the exact cubic
horizon furnished by the potential proof. -/
theorem filteredProtected_failure_eighth_at_cubic
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat)
    (horizon : 4 * (n ^ 3 + n ^ 2) ≤ t + 1) :
    8 * filteredProtectedMissTree hψ κ ring C t ≤ n ^ t := by
  apply filteredProtectedMissTree_polynomial_tail
    hn2 hψ κ ring C 8 t
  omega


end PPLLEpochVoterPolynomialUpper

