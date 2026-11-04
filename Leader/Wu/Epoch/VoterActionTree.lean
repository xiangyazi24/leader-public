import Leader.Wu.Epoch.VoterColorDrift

/-!
# Finite action-tree telescope for the directed epoch voter process

This is one layer of the mechanically split polynomial iid upper-bound proof.
Public declarations remain in the historical epoch-voter namespace.
-/

namespace PPLLEpochVoterPolynomialUpper

open PPLLEpochVoterReduction PPLLEpochVoterTwoDomain
  PPLLEpochVoterFiniteTree PPLLResearchFormulation
  PPLLProtectedEpochProtocol PPLLDerivedEpochRepair
  PPLLDerivedEpochRuntimeNoGo
open PPLLEpochVoterSumTools

/-! ## Finite action-tree telescope -/

/-- Total agreement potential at depth `t`, summed over all exact scheduler
words.  Consensus states remain in the tree; they are fixed points and simply
carry maximal potential. -/
def voterPotentialTreeTotal (ring : DirectedRing n) :
    (Fin n → Fin n) → Nat → Nat
  | D, 0 => voterAgreementPotential D
  | D, t + 1 =>
      (List.ofFn (fun e => voterPotentialTreeTotal ring
        (directedVoterStep ring D e) t)).sum

/-- A consensus word is a fixed point of every directed voter action. -/
theorem directedVoterStep_eq_self_of_consensus
    (ring : DirectedRing n) (D : Fin n → Fin n)
    (hD : VoterConsensus D) (e : Fin n) :
    directedVoterStep ring D e = D := by
  apply directedVoterStep_eq_of_edge_eq
  obtain ⟨c, hc⟩ := hD
  rw [hc e, hc (ring.rightNeighbor e)]

/-- Consequently, one complete scheduler generation multiplies the total
potential of a consensus word by exactly `n`. -/
theorem voterPotentialTreeTotal_succ_of_consensus
    (ring : DirectedRing n) (D : Fin n → Fin n)
    (hD : VoterConsensus D) (t : Nat) :
    voterPotentialTreeTotal ring D (t + 1) =
      n * voterPotentialTreeTotal ring D t := by
  rw [voterPotentialTreeTotal]
  calc
    (List.ofFn (fun e => voterPotentialTreeTotal ring
        (directedVoterStep ring D e) t)).sum =
        (List.ofFn (fun _ : Fin n =>
          voterPotentialTreeTotal ring D t)).sum := by
            apply sum_ofFn_eq
            intro e
            rw [directedVoterStep_eq_self_of_consensus ring D hD e]
    _ = n * voterPotentialTreeTotal ring D t := sum_ofFn_const n _

/-- The total potential at depth `t` is at most `n^t * n^2`. -/
theorem voterPotentialTreeTotal_le
    (ring : DirectedRing n) (D : Fin n → Fin n) (t : Nat) :
    voterPotentialTreeTotal ring D t ≤ n ^ t * n ^ 2 := by
  induction t generalizing D with
  | zero =>
      simpa [voterPotentialTreeTotal] using
        voterAgreementPotential_le_square D
  | succ t ih =>
      rw [voterPotentialTreeTotal]
      calc
        (List.ofFn (fun e => voterPotentialTreeTotal ring
            (directedVoterStep ring D e) t)).sum ≤
            (List.ofFn (fun _ : Fin n => n ^ t * n ^ 2)).sum := by
              apply sum_ofFn_le
              intro e
              exact ih (directedVoterStep ring D e)
        _ = n * (n ^ t * n ^ 2) := sum_ofFn_const n _
        _ = n ^ (t + 1) * n ^ 2 := by
          rw [Nat.pow_succ]
          grind

/-- One generation of the complete action tree gains at least two units for
every scheduler prefix that is still outside consensus. -/
theorem voterPotentialTreeTotal_drift
    (hn2 : 1 < n) (ring : DirectedRing n)
    (D : Fin n → Fin n) (t : Nat) :
    n * voterPotentialTreeTotal ring D t +
        2 * voterMissTree ring D t ≤
      voterPotentialTreeTotal ring D (t + 1) := by
  induction t generalizing D with
  | zero =>
      simp only [voterPotentialTreeTotal, voterMissTree]
      by_cases hD : VoterConsensus D
      · rw [if_pos hD]
        rw [voterAgreementPotential_step_sum hn2 ring D]
        omega
      · rw [if_neg hD]
        exact voterAgreementPotential_step_sum_live hn2 ring D hD
  | succ t ih =>
      by_cases hD : VoterConsensus D
      · rw [voterMissTree, if_pos hD,
          voterPotentialTreeTotal_succ_of_consensus ring D hD (t + 1),
          voterPotentialTreeTotal_succ_of_consensus ring D hD t]
        omega
      · simp only [voterPotentialTreeTotal]
        have hchildren := sum_ofFn_le
          (fun e => n * voterPotentialTreeTotal ring
              (directedVoterStep ring D e) t +
            2 * voterMissTree ring (directedVoterStep ring D e) t)
          (fun e => voterPotentialTreeTotal ring
            (directedVoterStep ring D e) (t + 1))
          (fun e => ih (directedVoterStep ring D e))
        rw [sum_ofFn_add, sum_ofFn_mul_left,
          sum_ofFn_mul_left] at hchildren
        simp only [voterMissTree, if_neg hD]
        exact hchildren

/-- Weighted finite survival sum.  At depth `t`, this is
`sum_{k<t} n^(t-1-k) * missCount(k)` without division. -/
noncomputable def voterWeightedMissTotal (ring : DirectedRing n)
    (D : Fin n → Fin n) : Nat → Nat
  | 0 => 0
  | t + 1 => n * voterWeightedMissTotal ring D t + voterMissTree ring D t

/-- The potential telescope charges twice the complete weighted survival sum. -/
theorem voterPotentialTree_telescope
    (hn2 : 1 < n) (ring : DirectedRing n)
    (D : Fin n → Fin n) (t : Nat) :
    n ^ t * voterAgreementPotential D +
        2 * voterWeightedMissTotal ring D t ≤
      voterPotentialTreeTotal ring D t := by
  induction t with
  | zero => simp [voterWeightedMissTotal, voterPotentialTreeTotal]
  | succ t ih =>
      have hscaled := Nat.mul_le_mul_left n ih
      have hdrift := voterPotentialTreeTotal_drift hn2 ring D t
      rw [voterWeightedMissTotal, Nat.pow_succ]
      calc
        n ^ t * n * voterAgreementPotential D +
            2 * (n * voterWeightedMissTotal ring D t +
              voterMissTree ring D t) =
            n * (n ^ t * voterAgreementPotential D +
              2 * voterWeightedMissTotal ring D t) +
              2 * voterMissTree ring D t := by grind
        _ ≤ n * voterPotentialTreeTotal ring D t +
              2 * voterMissTree ring D t := by
            exact Nat.add_le_add_right hscaled _
        _ ≤ voterPotentialTreeTotal ring D (t + 1) := hdrift

/-- Exact finite analogue of the expected-time upper bound: after normalizing
by `n^t`, the sum of survival probabilities through depth `t-1` is at most
`n^2 / 2`. -/
theorem voterWeightedMissTotal_budget
    (hn2 : 1 < n) (ring : DirectedRing n)
    (D : Fin n → Fin n) (t : Nat) :
    2 * voterWeightedMissTotal ring D t ≤ n ^ t * n ^ 2 := by
  have htelescope := voterPotentialTree_telescope hn2 ring D t
  have hupper := voterPotentialTreeTotal_le ring D t
  omega

/-- Survival counts cannot grow faster than the `n` extensions of each live
prefix. -/
theorem voterMissTree_succ_le_mul
    (ring : DirectedRing n) (D : Fin n → Fin n) (t : Nat) :
    voterMissTree ring D (t + 1) ≤ n * voterMissTree ring D t := by
  induction t generalizing D with
  | zero =>
      simp only [voterMissTree]
      by_cases hD : VoterConsensus D
      · rw [if_pos hD, if_pos hD]
        exact Nat.zero_le _
      · rw [if_neg hD, if_neg hD]
        have hchildren := sum_ofFn_le
          (fun e => @ite Nat
            (VoterConsensus (directedVoterStep ring D e))
            (Classical.propDecidable _) 0 1)
          (fun _ : Fin n => 1) (by
            intro e
            split <;> omega)
        rw [sum_ofFn_const] at hchildren
        simpa using hchildren
  | succ t ih =>
      simp only [voterMissTree]
      by_cases hD : VoterConsensus D
      · rw [if_pos hD, if_pos hD]
        exact Nat.zero_le _
      · rw [if_neg hD, if_neg hD]
        have hchildren := sum_ofFn_le
          (fun e => voterMissTree ring
            (directedVoterStep ring D e) (t + 1))
          (fun e => n * voterMissTree ring
            (directedVoterStep ring D e) t)
          (fun e => ih (directedVoterStep ring D e))
        rw [sum_ofFn_mul_left] at hchildren
        exact hchildren

/-- The final survival count appears at least `t+1` times in the weighted
survival sum after extending every earlier live prefix. -/
theorem voterMissTree_mul_time_le_weighted
    (ring : DirectedRing n) (D : Fin n → Fin n) (t : Nat) :
    (t + 1) * voterMissTree ring D t ≤
      voterWeightedMissTotal ring D (t + 1) := by
  induction t with
  | zero => simp [voterWeightedMissTotal]
  | succ t ih =>
      have hmono := voterMissTree_succ_le_mul ring D t
      have hmonoScaled := Nat.mul_le_mul_left (t + 1) hmono
      have hihScaled := Nat.mul_le_mul_left n ih
      rw [voterWeightedMissTotal]
      grind

/-- Division-free finite-horizon tail inequality.  In probability notation it
is `Pr[T_consensus > t] ≤ n^3 / (2(t+1))`. -/
theorem voterMissTree_tail_moment
    (hn2 : 1 < n) (ring : DirectedRing n)
    (D : Fin n → Fin n) (t : Nat) :
    2 * (t + 1) * voterMissTree ring D t ≤ n ^ t * n ^ 3 := by
  have hlower := voterMissTree_mul_time_le_weighted ring D t
  have hbudget := voterWeightedMissTotal_budget hn2 ring D (t + 1)
  have hchain :
      2 * ((t + 1) * voterMissTree ring D t) ≤
        2 * voterWeightedMissTotal ring D (t + 1) :=
    Nat.mul_le_mul_left 2 hlower
  have h := Nat.le_trans hchain hbudget
  rw [Nat.pow_succ] at h
  simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    using h

/-- Polynomial iid consensus tail for every initial color word.  The premise
is the exact integer form of `q ≤ 2(t+1)/n^3`; the conclusion says that at
most a `1/q` fraction of the `n^t` scheduler words still miss consensus. -/
theorem voterMissTree_polynomial_tail
    (hn2 : 1 < n) (ring : DirectedRing n)
    (D : Fin n → Fin n) (q t : Nat)
    (horizon : q * n ^ 3 ≤ 2 * (t + 1)) :
    q * voterMissTree ring D t ≤ n ^ t := by
  have hmoment := voterMissTree_tail_moment hn2 ring D t
  have hscaled := Nat.mul_le_mul_right (voterMissTree ring D t) horizon
  have hchain := Nat.le_trans hscaled hmoment
  have hcommon : n ^ 3 * (q * voterMissTree ring D t) ≤
      n ^ 3 * n ^ t := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hchain
  exact Nat.le_of_mul_le_mul_left hcommon (Nat.pow_pos ring.hn)

/-- Concrete one-eighth failure bound at a cubic global-interaction horizon. -/
theorem voterMissTree_failure_eighth_at_cubic
    (hn2 : 1 < n) (ring : DirectedRing n)
    (D : Fin n → Fin n) (t : Nat)
    (horizon : 4 * n ^ 3 ≤ t + 1) :
    8 * voterMissTree ring D t ≤ n ^ t := by
  apply voterMissTree_polynomial_tail hn2 ring D 8 t
  omega


end PPLLEpochVoterPolynomialUpper

