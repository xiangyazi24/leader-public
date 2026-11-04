import Leader.Core.Basic

/-!
# Leader Count Preservation

A key building block for safe-config closedness: if a transition function
cannot create new leaders and cannot destroy existing leaders, then the
leader count is preserved.

We prove this for abstract predicates (isLeader : Q → Bool) over the
generic PopulationProtocol framework, independent of P_PLL details.
-/

/-! ## Leader set analysis for a single step -/

/-- After a single step at edge (i, j=i+1), only agents i and j can change.
All other agents keep their state. -/
theorem step_preserves_others (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (e : Fin n) (k : Fin n)
    (hki : k ≠ e) (hkj : k ≠ ring.rightNeighbor e) :
    P.step ring C e k = C k := by
  unfold PopulationProtocol.step
  simp only [if_neg hki, if_neg hkj]

/-- A step only modifies the states of the two interacting agents. -/
theorem step_eq_on_others (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (e : Fin n) :
    ∀ k : Fin n, k ≠ e → k ≠ ring.rightNeighbor e →
    P.step ring C e k = C k :=
  fun k hki hkj => step_preserves_others P ring C e k hki hkj

/-! ## Leader-creation/destruction conditions imply preservation -/

/-- In any configuration where `isLeader` holds for exactly one agent,
and the transition function neither creates new leaders nor destroys
existing ones, the unique-leader property is preserved.

This is the core of Lemma 4.1.1's condition-1 argument:
a purely combinatorial fact about how a local transition (affecting 2 agents)
interacts with a global uniqueness property (exactly 1 leader among n). -/
theorem unique_leader_of_no_create_no_destroy
    (P : PopulationProtocol) (ring : DirectedRing n) (isLdr : P.Q → Bool)
    (C : P.Configuration n) (e : Fin n)
    (hunique : ∃ i₀ : Fin n, isLdr (C i₀) = true ∧
      ∀ j, isLdr (C j) = true → j = i₀)
    (hno_create : ∀ k : Fin n,
      isLdr (P.step ring C e k) = true → isLdr (C k) = true)
    (hno_destroy : ∀ k : Fin n,
      isLdr (C k) = true → isLdr (P.step ring C e k) = true) :
    ∃ i₀ : Fin n, isLdr (P.step ring C e i₀) = true ∧
      ∀ j, isLdr (P.step ring C e j) = true → j = i₀ := by
  obtain ⟨i₀, hldr, huniq⟩ := hunique
  exact ⟨i₀, hno_destroy i₀ hldr, fun j hj => huniq j (hno_create j hj)⟩

/-! ## Deriving the no-create/no-destroy hypotheses from step structure -/

/-- For agents not involved in the interaction, their leader status is trivially
preserved (their state doesn't change). So the no-create and no-destroy
conditions only need to be checked for the two interacting agents. -/
theorem no_create_from_edge (P : PopulationProtocol) (ring : DirectedRing n)
    (isLdr : P.Q → Bool) (C : P.Configuration n) (e : Fin n)
    (hi : isLdr (P.step ring C e e) = true → isLdr (C e) = true)
    (hj : isLdr (P.step ring C e (ring.rightNeighbor e)) = true →
      isLdr (C (ring.rightNeighbor e)) = true) :
    ∀ k : Fin n, isLdr (P.step ring C e k) = true → isLdr (C k) = true := by
  intro k hk
  by_cases hki : k = e
  · subst hki; exact hi hk
  · by_cases hkj : k = ring.rightNeighbor e
    · subst hkj; exact hj hk
    · rwa [step_preserves_others P ring C e k hki hkj] at hk

theorem no_destroy_from_edge (P : PopulationProtocol) (ring : DirectedRing n)
    (isLdr : P.Q → Bool) (C : P.Configuration n) (e : Fin n)
    (hi : isLdr (C e) = true → isLdr (P.step ring C e e) = true)
    (hj : isLdr (C (ring.rightNeighbor e)) = true →
      isLdr (P.step ring C e (ring.rightNeighbor e)) = true) :
    ∀ k : Fin n, isLdr (C k) = true → isLdr (P.step ring C e k) = true := by
  intro k hk
  by_cases hki : k = e
  · subst hki; exact hi hk
  · by_cases hkj : k = ring.rightNeighbor e
    · subst hkj; exact hj hk
    · rwa [step_preserves_others P ring C e k hki hkj]
