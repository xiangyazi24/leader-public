import Leader.Wu.Epoch.VoterColorDrift

/-!
# Protected-state potential for the filtered epoch protocol

This is one layer of the mechanically split polynomial iid upper-bound proof.
Public declarations remain in the historical epoch-voter namespace.
-/

namespace PPLLEpochVoterPolynomialUpper

open PPLLEpochVoterReduction PPLLEpochVoterTwoDomain
  PPLLEpochVoterFiniteTree PPLLResearchFormulation
  PPLLProtectedEpochProtocol PPLLDerivedEpochRepair
  PPLLDerivedEpochRuntimeNoGo
open PPLLEpochVoterSumTools

/-! ## Physical protected-state potential

The color potential alone does not recognize Definition-1 safety: arbitrary
transient core fields may remain after the slots have reached a rotation.  The
filter sanitizes both selected endpoints.  Adding the number of clean agents
to the color potential gives a single Lyapunov function for the full protected
predicate. -/

/-- Indicator that one physical epoch endpoint is already canonical. -/
noncomputable def epochCleanIndicator
    (u : EpochAgentState n ψ κ) : Nat :=
  @ite Nat (EpochClean u) (Classical.propDecidable _) 1 0

/-- Complementary indicator for a non-canonical endpoint. -/
noncomputable def epochDirtyIndicator
    (u : EpochAgentState n ψ κ) : Nat :=
  @ite Nat (EpochClean u) (Classical.propDecidable _) 0 1

/-- Number of canonical physical endpoints. -/
noncomputable def epochCleanMass
    (C : Fin n → EpochAgentState n ψ κ) : Nat :=
  (List.ofFn (fun i => epochCleanIndicator (C i))).sum

/-- Number of non-canonical physical endpoints. -/
noncomputable def epochDirtyMass
    (C : Fin n → EpochAgentState n ψ κ) : Nat :=
  (List.ofFn (fun i => epochDirtyIndicator (C i))).sum

theorem epochCleanIndicator_add_dirty
    (u : EpochAgentState n ψ κ) :
    epochCleanIndicator u + epochDirtyIndicator u = 1 := by
  by_cases hu : EpochClean u <;>
    simp [epochCleanIndicator, epochDirtyIndicator, hu]

/-- Clean and dirty endpoints partition the physical ring. -/
theorem epochCleanMass_add_dirty
    (C : Fin n → EpochAgentState n ψ κ) :
    epochCleanMass C + epochDirtyMass C = n := by
  unfold epochCleanMass epochDirtyMass
  rw [← sum_ofFn_add]
  calc
    (List.ofFn (fun i =>
        epochCleanIndicator (C i) + epochDirtyIndicator (C i))).sum =
        (List.ofFn (fun _ : Fin n => 1)).sum := by
          apply sum_ofFn_eq
          intro i
          exact epochCleanIndicator_add_dirty (C i)
    _ = n := by simpa using sum_ofFn_const n 1

theorem epochCleanMass_le
    (C : Fin n → EpochAgentState n ψ κ) :
    epochCleanMass C ≤ n := by
  have hpartition := epochCleanMass_add_dirty C
  omega

/-- If some endpoint is not canonical, the dirty mass is positive. -/
theorem epochDirtyMass_pos_of_not_all_clean
    (C : Fin n → EpochAgentState n ψ κ)
    (hC : ¬ ∀ i, EpochClean (C i)) :
    0 < epochDirtyMass C := by
  obtain ⟨i, hi⟩ := Classical.not_forall.mp hC
  have ht := term_le_sum_ofFn (fun i => epochDirtyIndicator (C i)) i
  unfold epochDirtyMass
  have hone : 1 ≤
      (List.ofFn (fun i => epochDirtyIndicator (C i))).sum := by
    simpa [epochDirtyIndicator, hi] using ht
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one hone

/-- Both endpoints selected by a filtered interaction are canonical afterward. -/
theorem filteredLocalStep_endpoints_clean
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (e : Fin n) :
    EpochClean
        (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e e) ∧
      EpochClean
        (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e
          (ring.rightNeighbor e)) := by
  let j := ring.rightNeighbor e
  let q := ppllEpochFilterTransition hψ κ ring.hn (C e) (C j)
  have hq := ppllEpochFilter_local_contract hψ κ ring.hn (C e) (C j)
  change q.1.slot = (C e).slot ∧
    q.2.slot = nextSlot ring.hn q.1.slot ∧
    EpochClean q.1 ∧ EpochClean q.2 at hq
  have hne : j ≠ e := rightNeighbor_ne hn2 ring e
  change EpochClean (if e = e then q.1 else if e = j then q.2 else C e) ∧
    EpochClean (if j = e then q.1 else if j = j then q.2 else C j)
  rw [if_pos rfl, if_neg hne, if_pos rfl]
  exact hq.2.2

/-- A filtered interaction frames every unselected endpoint. -/
theorem filteredLocalStep_eq_of_other
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (e i : Fin n)
    (hie : i ≠ e) (hij : i ≠ ring.rightNeighbor e) :
    localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e i = C i := by
  simp [localStep, hie, hij]

/-- Subtraction-free local balance for endpoint cleanliness. -/
theorem epochCleanMass_localStep_balance
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (e : Fin n) :
    epochCleanMass
        (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e) +
        epochCleanIndicator (C e) +
        epochCleanIndicator (C (ring.rightNeighbor e)) =
      epochCleanMass C + 2 := by
  let C' := localStep ring
    (ppllEpochFilterTransition hψ κ ring.hn) C e
  let j := ring.rightNeighbor e
  have hne : e ≠ j := Ne.symm (rightNeighbor_ne hn2 ring e)
  have hsum := sum_ofFn_balance_two
    (fun i => epochCleanIndicator (C' i))
    (fun i => epochCleanIndicator (C i)) e j hne (by
      intro i hie hij
      have hi : C' i = C i := by
        dsimp [C']
        apply filteredLocalStep_eq_of_other hψ κ ring C e i hie
        simpa [j] using hij
      rw [hi])
  have hend := filteredLocalStep_endpoints_clean hn2 hψ κ ring C e
  change epochCleanMass C' + epochCleanIndicator (C e) +
      epochCleanIndicator (C j) =
    epochCleanMass C + epochCleanIndicator (C' e) +
      epochCleanIndicator (C' j) at hsum
  have hende : EpochClean (C' e) := by
    simpa [C'] using hend.1
  have hendj : EpochClean (C' j) := by
    simpa [C', j] using hend.2
  have he : epochCleanIndicator (C' e) = 1 := by
    simp [epochCleanIndicator, hende]
  have hj : epochCleanIndicator (C' j) = 1 := by
    simp [epochCleanIndicator, hendj]
  rw [he, hj] at hsum
  simpa [C', j] using hsum

/-- Exact scheduler drift of the cleanliness mass.  Each dirty endpoint is
incident to two possible directed interactions. -/
theorem epochCleanMass_step_sum
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    (List.ofFn (fun e => epochCleanMass
      (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e))).sum =
      n * epochCleanMass C + 2 * epochDirtyMass C := by
  have hsum := sum_ofFn_eq
    (fun e => epochCleanMass
        (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e) +
      epochCleanIndicator (C e) +
      epochCleanIndicator (C (ring.rightNeighbor e)))
    (fun _ : Fin n => epochCleanMass C + 2)
    (fun e => epochCleanMass_localStep_balance hn2 hψ κ ring C e)
  rw [sum_ofFn_add, sum_ofFn_add, sum_ofFn_const] at hsum
  have hright :
      (List.ofFn (fun e =>
        epochCleanIndicator (C (ring.rightNeighbor e)))).sum =
        epochCleanMass C := by
    simpa [epochCleanMass] using sum_ofFn_rightNeighbor ring
      (fun i => epochCleanIndicator (C i))
  have hpartition := epochCleanMass_add_dirty C
  change (List.ofFn (fun e => epochCleanMass
      (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e))).sum +
      epochCleanMass C +
      (List.ofFn (fun e =>
        epochCleanIndicator (C (ring.rightNeighbor e)))).sum =
        n * (epochCleanMass C + 2) at hsum
  rw [hright] at hsum
  rw [Nat.mul_add] at hsum
  omega

/-- One physical Lyapunov function for both color consensus and endpoint
canonicality. -/
noncomputable def filteredProtectedPotential
    (C : Fin n → EpochAgentState n ψ κ) : Nat :=
  voterAgreementPotential (epochColorConfig C) + epochCleanMass C

/-- Exact full-state scheduler drift. -/
theorem filteredProtectedPotential_step_sum
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    (List.ofFn (fun e => filteredProtectedPotential
      (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e))).sum =
      n * filteredProtectedPotential C +
        2 * voterWallCount ring (epochColorConfig C) +
        2 * epochDirtyMass C := by
  have hcolor := voterAgreementPotential_step_sum hn2 ring
    (epochColorConfig C)
  have hclean := epochCleanMass_step_sum hn2 hψ κ ring C
  have hprojected :
      (List.ofFn (fun e => voterAgreementPotential
        (epochColorConfig
          (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e)))).sum =
      (List.ofFn (fun e => voterAgreementPotential
        (directedVoterStep ring (epochColorConfig C) e))).sum := by
    apply sum_ofFn_eq
    intro e
    rw [epochColorConfig_localStep]
  unfold filteredProtectedPotential
  rw [sum_ofFn_add]
  rw [hprojected, hcolor, hclean, Nat.mul_add]
  omega

/-- Every physical state outside the protected set has positive full-state
scheduler drift. -/
theorem filteredProtectedPotential_step_sum_live
    (hn2 : 1 < n) (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ)
    (hC : ¬ ProtectedEpoch ring.hn ring C) :
    n * filteredProtectedPotential C + 2 ≤
      (List.ofFn (fun e => filteredProtectedPotential
        (localStep ring (ppllEpochFilterTransition hψ κ ring.hn) C e))).sum := by
  rw [filteredProtectedPotential_step_sum hn2 hψ κ ring C]
  by_cases hcolor : VoterConsensus (epochColorConfig C)
  · have hnotclean : ¬ ∀ i, EpochClean (C i) := by
      intro hclean
      apply hC
      exact (protectedEpoch_iff_colorConsensus_clean ring C).2
        ⟨hcolor, hclean⟩
    have hdirty := epochDirtyMass_pos_of_not_all_clean C hnotclean
    omega
  · have hwalls := voterWallCount_pos_of_not_consensus ring
      (epochColorConfig C) hcolor
    omega

/-- The full-state potential is at most `n^2 + n`. -/
theorem filteredProtectedPotential_le
    (C : Fin n → EpochAgentState n ψ κ) :
    filteredProtectedPotential C ≤ n ^ 2 + n := by
  have hcolor := voterAgreementPotential_le_square (epochColorConfig C)
  have hclean := epochCleanMass_le C
  unfold filteredProtectedPotential
  omega


end PPLLEpochVoterPolynomialUpper

