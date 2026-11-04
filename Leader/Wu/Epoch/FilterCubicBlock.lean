import Leader.Wu.Epoch.FilterProtectedActionTree

/-!
# Definition-1 capstones for the filtered epoch protocol

This is one layer of the mechanically split polynomial iid upper-bound proof.
Public declarations remain in the historical epoch-voter namespace.
-/

namespace PPLLEpochVoterPolynomialUpper

open PPLLEpochVoterReduction PPLLEpochVoterTwoDomain
  PPLLEpochVoterFiniteTree PPLLResearchFormulation
  PPLLProtectedEpochProtocol PPLLDerivedEpochRepair
  PPLLDerivedEpochRuntimeNoGo
open PPLLEpochVoterSumTools

/-! ## Absorption and genuine final-state Definition-1 failure -/

/-- Direct one-step absorption of the protected physical predicate under the
same local transition used by the miss tree. -/
theorem filteredProtected_absorbing
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ)
    (hC : ProtectedEpoch ring.hn ring C) (e : Fin n) :
    ProtectedEpoch ring.hn ring
      (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e) := by
  apply ppllEpochFilter_closed hψ κ ring C hC
  exact ⟨e, rfl⟩

theorem filteredProtectedMissTree_zero_of_protected
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ)
    (hC : ProtectedEpoch ring.hn ring C) (t : Nat) :
    filteredProtectedMissTree hψ κ ring C t = 0 := by
  cases t <;> simp [filteredProtectedMissTree, hC]

/-- Unabsorbed action-tree count whose leaves are tested for `ProtectedEpoch`
exactly at time `t`. -/
noncomputable def filteredProtectedFinalMissTree
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) :
    (Fin n → EpochAgentState n ψ κ) → Nat → Nat
  | C, 0 => @ite Nat (ProtectedEpoch ring.hn ring C)
      (Classical.propDecidable _) 0 1
  | C, t + 1 =>
      (List.ofFn (fun e => filteredProtectedFinalMissTree hψ κ ring
        (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e) t)).sum

/-- Since `ProtectedEpoch` is absorbing, the first-hit miss tree is exactly the
leafwise final-state failure count, at every horizon. -/
theorem filteredProtectedMissTree_eq_final
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat) :
    filteredProtectedMissTree hψ κ ring C t =
      filteredProtectedFinalMissTree hψ κ ring C t := by
  induction t generalizing C with
  | zero => rfl
  | succ t ih =>
      rw [filteredProtectedMissTree, filteredProtectedFinalMissTree]
      by_cases hC : ProtectedEpoch ring.hn ring C
      · rw [if_pos hC]
        have hzero :
            (List.ofFn (fun e => filteredProtectedFinalMissTree hψ κ ring
              (localStep ring
                (ppllEpochFilterTransition hψ κ ring.hn) C e) t)).sum =
              (List.ofFn (fun _ : Fin n => 0)).sum := by
          apply sum_ofFn_eq
          intro e
          rw [← ih]
          exact filteredProtectedMissTree_zero_of_protected hψ κ ring _
            (filteredProtected_absorbing hψ κ ring C hC e) t
        rw [hzero, sum_ofFn_const]
        omega
      · rw [if_neg hC]
        apply sum_ofFn_eq
        intro e
        exact ih (localStep ring
          (ppllEpochFilterTransition hψ κ ring.hn) C e)

/-- Leafwise count of exact scheduler words whose time-`t` configuration is
not safe in the full sense of Wu's Definition 1. -/
noncomputable def filteredDefinitionOneFinalMissTree
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n) :
    (Fin n → EpochAgentState n ψ κ) → Nat → Nat
  | C, 0 => @ite Nat
      (PopulationProtocol.IsSafe
        (ppllEpochFilterProtocol hψ κ ring.hn) ring C isLeaderOutput)
      (Classical.propDecidable _) 0 1
  | C, t + 1 =>
      (List.ofFn (fun e => filteredDefinitionOneFinalMissTree hψ κ ring
        (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e) t)).sum

/-- Every leaf that is not Definition-1 safe is in particular not protected,
because protected physical states are proved semantically safe. -/
theorem filteredDefinitionOneFinalMissTree_le_protected
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat) :
    filteredDefinitionOneFinalMissTree hψ κ ring C t ≤
      filteredProtectedFinalMissTree hψ κ ring C t := by
  induction t generalizing C with
  | zero =>
      simp only [filteredDefinitionOneFinalMissTree,
        filteredProtectedFinalMissTree]
      by_cases hC : ProtectedEpoch ring.hn ring C
      · have hsafe := ppllEpochFilter_isSafe hψ κ ring hC
        rw [if_pos hC, if_pos hsafe]
        exact Nat.zero_le _
      · rw [if_neg hC]
        split <;> omega
  | succ t ih =>
      simp only [filteredDefinitionOneFinalMissTree,
        filteredProtectedFinalMissTree]
      exact sum_ofFn_le _ _ (fun e => ih
        (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e))

/-- Arbitrary-initial-state iid `1/8` bound for final protected membership.
The premise is the exact integer horizon supplied by the full-state potential. -/
theorem filteredProtectedFinal_failure_eighth_at_cubic
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat)
    (horizon : 4 * (n ^ 3 + n ^ 2) ≤ t + 1) :
    8 * filteredProtectedFinalMissTree hψ κ ring C t ≤ n ^ t := by
  rw [← filteredProtectedMissTree_eq_final]
  exact filteredProtected_failure_eighth_at_cubic
    hn2 hψ κ ring C t horizon

/-- Arbitrary-initial-state iid `1/8` bound for genuine Definition-1 safety at
the final horizon.  It counts every length-`t` scheduler word with its exact
multiplicity and uses no probabilistic postulate. -/
theorem filteredDefinitionOne_failure_eighth_at_cubic
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat)
    (horizon : 4 * (n ^ 3 + n ^ 2) ≤ t + 1) :
    8 * filteredDefinitionOneFinalMissTree hψ κ ring C t ≤ n ^ t := by
  have hsub := filteredDefinitionOneFinalMissTree_le_protected
    hψ κ ring C t
  have hprotected := filteredProtectedFinal_failure_eighth_at_cubic
    hn2 hψ κ ring C t horizon
  exact Nat.le_trans (Nat.mul_le_mul_left 8 hsub) hprotected

/-- Slightly looser but simpler pure-cubic formulation. -/
theorem filteredDefinitionOne_failure_eighth_at_eight_cubic
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (t : Nat)
    (horizon : 8 * n ^ 3 ≤ t + 1) :
    8 * filteredDefinitionOneFinalMissTree hψ κ ring C t ≤ n ^ t := by
  apply filteredDefinitionOne_failure_eighth_at_cubic
    hn2 hψ κ ring C t
  have hn2le : n ^ 2 ≤ n ^ 3 := by
    have hn1 : 1 ≤ n := by omega
    calc
      n ^ 2 = n ^ 2 * 1 := by omega
      _ ≤ n ^ 2 * n := Nat.mul_le_mul_left _ hn1
      _ = n ^ 3 := (Nat.pow_succ n 2).symm
  omega


end PPLLEpochVoterPolynomialUpper

