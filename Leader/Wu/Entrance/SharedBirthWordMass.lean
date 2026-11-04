import Leader.Wu.Entrance.JoinObligations


set_option autoImplicit false
set_option Elab.async false


namespace B6EntranceK2Mass2


open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C


variable {n psi : Nat}


private theorem aliveAlong_end
    {S : Type} {m : Nat}
    (step : S → Fin m → S) (Good : S → Prop)
    (x : S) (u : List (Fin m))
    (h : AliveAlong step Good x u) :
    Good (u.foldl step x) := by
  induction u generalizing x with
  | nil =>
      exact h
  | cons e rest ih =>
      simpa only [List.foldl_cons] using
        (ih (x := step x e) h.2)


/-- One shared C4/C5 currency: the final Q=8 first-leader mass on literal
`Fin n` words at the C-final leaf horizon.  This is the real remaining mass
argument; it is not implied by the current existential C4 `HostExit`. -/
def C4C5SharedBirthWordMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ C : FinalCandidateR2C.Config n psi psi (16 * psi),
    FinalLeaderless C →
    8 * avoidCount
        (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        (fun _ : FinalCandidateR2C.Config n psi psi (16 * psi) => True)
        HasLeader C (256 * n ^ 2) ≤
      (8 - 1) * n ^ (256 * n ^ 2)


/-- The shared final leaf immediately supplies C4's lineage-indexed mass
obligation: `AliveAlong` gives leaderlessness of the lineage endpoint. -/
theorem c4K2EnvelopeUniformMass_of_sharedBirthWordMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (hLeaf : C4C5SharedBirthWordMass hpsi h2 ring) :
    B6EntranceK2Gate.C4K2EnvelopeUniformMassObligation
      hpsi h2 ring := by
  unfold C4C5SharedBirthWordMass at hLeaf
  unfold B6EntranceK2Gate.C4K2EnvelopeUniformMassObligation
  intro C0 lineage _hA _hClear hAlive
  dsimp only
  apply hLeaf
  exact aliveAlong_end
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    FinalLeaderless C0 lineage hAlive


/-- The same shared leaf is already the exact final `B7ComposedMassObligation`
currency after unfolding `stepConcrete`. -/
theorem b7ComposedMass_of_sharedBirthWordMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (hLeaf : C4C5SharedBirthWordMass hpsi h2 ring) :
    B7ComposedMassObligation hpsi h2
      (concretePort (κ := psi) (τ := 16 * psi) hpsi h2) ring
      (fun _ : FinalCandidateR2C.Config n psi psi (16 * psi) => True)
      (256 * n ^ 2) 8 := by
  unfold C4C5SharedBirthWordMass at hLeaf
  unfold B7ComposedMassObligation
  constructor
  · decide
  · intro C hC
    have h := hLeaf C hC.2
    simpa only [stepConcrete] using h


/-- Revised J6: once the one shared birth leaf is available, neither the
carrier identity nor the existential C4 gate contributes any further mass
argument. -/
theorem j6_of_sharedBirthWordMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (hLeaf : C4C5SharedBirthWordMass hpsi h2 ring) :
    CFinalAssembly.J6C4WitnessToUniformMass hpsi h2 ring := by
  unfold CFinalAssembly.J6C4WitnessToUniformMass
  intro _hJ5 _hC4
  exact c4K2EnvelopeUniformMass_of_sharedBirthWordMass
    hpsi h2 ring hLeaf


/-- Revised J7 wiring: J7 still records the C5/B4 producer as its first
conjunct, but the final mass conclusion should consume the same shared leaf
instead of multiplying C2/C4/C5 denominators again. -/
theorem j7_of_b4_and_sharedBirthWordMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn4 : 4 ≤ n)
    (ring : DirectedRing n) (anchor : Fin n)
    (hB4 : ConcreteB4BlockProgressMassObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 hn4 ring anchor)
    (hLeaf : C4C5SharedBirthWordMass hpsi h2 ring) :
    CFinalAssembly.J7PassiveAdmissionComposition
      hpsi h2 hn4 ring anchor := by
  unfold CFinalAssembly.J7PassiveAdmissionComposition
  refine ⟨hB4, ?_⟩
  intro _hB4 _hClosed _hRecovery _hC4
  exact b7ComposedMass_of_sharedBirthWordMass
    hpsi h2 ring hLeaf


end B6EntranceK2Mass2
