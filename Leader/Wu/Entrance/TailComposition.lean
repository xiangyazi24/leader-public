import Leader.Wu.Entrance.RecoveryThenLeaf


set_option autoImplicit false
set_option Elab.async false


namespace CFinalTailComposition


open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open CFinalAssembly2


variable {n psi : Nat}


/-- Honest final tail: once the shared Q=8 birth leaf exists, no C1/C2/C4
or join/composition gate is needed to obtain the one-over-n bound. -/
theorem b7_bound_of_sharedBirthWordMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn2 : 2 <= n)
    (ring : DirectedRing n)
    (hLeaf : C4C5SharedBirthWordMassAt
      hpsi h2 ring (FinalLeafHV2 n psi)) :
    FinalB7OneOverN hpsi h2 ring (FinalLeafHV2 n psi) := by
  have hMass := b7ComposedMass_of_sharedBirthWordMassAt
    hpsi h2 ring (FinalLeafHV2 n psi) hLeaf
  have hUniform := uniformLeaf_of_b7ComposedMass_v2
    hpsi h2 ring (FinalLeafHV2 n psi) hMass
  unfold FinalB7OneOverN
  intro C hC
  exact
    BirthLeaderlessBirthMassB7Generic.firstLeader_failure_le_one_over_n_of_uniformBirthMass
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless (FinalLeafHV2 n psi) hUniform hn2 C hC


end CFinalTailComposition
