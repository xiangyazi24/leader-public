import Leader.PPL.MainTheorem.GeneralTargets
import Leader.Wu.Protocol.FiniteState
import Leader.Wu.Safety.CorrectedFormulation

/-!
# P_PL Theorem 1, general finite maximum: pointwise hits to a uniform length

For the small-`n` expected-cost argument, a pointwise possible-convergence
statement (every configuration has some word that hits the target) becomes a
uniform one (one length bound for all configurations) by a finite maximum
over an exhaustive configuration list, and a prefix hit yields an endpoint
witness no longer than the word.  The `S_PL` versions
(`PPL.theorem1PossibleUniformBound_of_exhaustive`,
`PPL.theorem1ReachesSPL_endpoint_prefix`) and the safe-target versions in
`PPL.PsiAtLeastN` are special cases of the lemmas here.

P_PL Theorem 1 cleanup, phase 2, step 6e.
-/

namespace PPL.Theorem1General

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPLLResearchFormulation

/-- The explicit local run is the population run of `P_PL`. -/
theorem theorem1RunLocalSchedule_eq_runPPL
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (word : DetSchedule n) :
    runLocalSchedule ring (PPL.protocol psi kappa).transition C word =
      PPL.Probability.runPPL ring C word := by
  induction word generalizing C with
  | nil =>
      rfl
  | cons e rest ih =>
      simp only
        [runLocalSchedule,
          PPL.Probability.runPPL,
          PPL.Probability.runPopulationSchedule]
      rw [PPLLResearchFormulation.localStep_eq_protocol_step
          (PPL.protocol psi kappa) ring C e]
      simpa [PPL.Probability.runPPL] using
        ih (C := PopulationProtocol.step (PPL.protocol psi kappa) ring C e)

/-- A prefix hit of a Boolean target yields an endpoint witness no longer
than the word: cut the word at the first configuration in the target. -/
theorem theorem1ReachesB_endpoint_prefix
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (tgt : Config n psi kappa → Bool)
    (C : Config n psi kappa)
    (word : DetSchedule n)
    (hhit : theorem1ReachesB ring tgt C word = true) :
    ∃ pre : DetSchedule n,
      pre.length ≤ word.length ∧
      tgt (runLocalSchedule ring (PPL.protocol psi kappa).transition C pre) =
        true := by
  induction word generalizing C with
  | nil =>
      exact ⟨[], Nat.le_refl _, by simpa [theorem1ReachesB, runLocalSchedule] using hhit⟩
  | cons e rest ih =>
      cases hC : tgt C with
      | true =>
          exact ⟨[], Nat.zero_le _, by simpa [runLocalSchedule] using hC⟩
      | false =>
          have htail :
              theorem1ReachesB ring tgt
                (PopulationProtocol.step (PPL.protocol psi kappa) ring C e)
                rest = true := by
            simpa [theorem1ReachesB, hC] using hhit
          obtain ⟨pre, hlen, hsafe⟩ := ih _ htail
          refine ⟨e :: pre, Nat.succ_le_succ hlen, ?_⟩
          simp only [runLocalSchedule]
          rw [localStep_eq_protocol_step (PPL.protocol psi kappa) ring C e]
          exact hsafe

/-- Finite maximum: pointwise hits over an exhaustive list give one uniform
length bound. -/
theorem theorem1UniformBound_of_exhaustive
    {α : Type} {n : Nat}
    (e : ExhaustiveList α)
    (R : α → DetSchedule n → Bool)
    (hpoint : ∀ C : α, ∃ word : DetSchedule n, R C word = true) :
    ∃ L : Nat,
      ∀ C : α,
        ∃ word : DetSchedule n,
          word.length ≤ L ∧ R C word = true := by
  have hlist :
      ∀ xs : List α,
        ∃ L : Nat,
          ∀ C, C ∈ xs →
            ∃ word : DetSchedule n,
              word.length ≤ L ∧ R C word = true := by
    intro xs
    induction xs with
    | nil =>
        exact ⟨0, fun C hC => by cases hC⟩
    | cons C xs ih =>
        obtain ⟨Ltail, hLtail⟩ := ih
        obtain ⟨wC, hwC⟩ := hpoint C
        refine ⟨Nat.max wC.length Ltail, ?_⟩
        intro D hD
        cases List.mem_cons.mp hD with
        | inl hDC =>
            subst hDC
            exact ⟨wC, Nat.le_max_left _ _, hwC⟩
        | inr hDtail =>
            obtain ⟨wD, hwDlen, hwD⟩ := hLtail D hDtail
            exact ⟨wD, Nat.le_trans hwDlen (Nat.le_max_right _ _), hwD⟩
  obtain ⟨L, hL⟩ := hlist e.values
  exact ⟨L, fun C => hL C (e.complete C)⟩

end PPL.Theorem1General
