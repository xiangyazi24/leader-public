import Leader.Wu.Splice.RecoveryFinalStepMass
import Leader.Wu.Splice.RiskHoldRepairSelector
import Leader.Wu.Splice.RiskHostResidual


set_option autoImplicit false
set_option Elab.async false


namespace B9RecoveryGateInstance


variable {n psi kappa tau : Nat}


theorem c2RecoveryGate_of_installed
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hDomain : B9RiskRefinementPhys5.R1Row10gHostRiskViewResidual)
    (hJ4 : B9RecoveryGate.C2J4RecoveryToB7Mass
      (kappa := kappa) (tau := tau) hpsi h2 ring) :
    B9RecoveryGate.C2RecoveryGate
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  have hHold :
      B9RiskRefinement2C.HoldRepairControllerProjectionObligation
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2) hpsi :=
    B9RiskRefinement2D.r1Host_holdRepairControllerProjectionObligation
      (kappa := kappa) (tau := tau) hpsi h2
  have hCompletion :
      B9RiskRefinementPhys4.R1Row10gLeafRiskViewCompletionClause :=
    B9RiskRefinementPhys5.r1Row10gLeafRiskViewCompletion_of_residual hDomain
  have hJ3 : B9RecoveryGate.C2J3OldToFinalRecoveryMass
      (kappa := kappa) (tau := tau) hpsi h2 ring :=
    B9RecoveryJ3Direct.c2J3OldToFinalRecoveryMass_direct
      (κ := kappa) (τ := tau) hpsi h2 ring
  exact B9RecoveryGate.c2RecoveryGate_of_mass_and_refinement
    (kappa := kappa) (tau := tau) hpsi h2 ring
    hHold hCompletion ⟨hJ3, hJ4⟩


end B9RecoveryGateInstance
