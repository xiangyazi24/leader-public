import Leader.Wu.Splice.RiskLeafIdentification

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9RiskRefinementPhys5

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceV10cLiveness
open B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10j
open B9Host B9SpliceTableHost B9RiskAbstraction B9RiskRefinement
open B9HostRightLabelLaw B9RiskRefinementPhys2
open B9RiskRefinementPhys3 B9RiskRefinementPhys4

variable {psi kappa tau : Nat}

/-- First source-resistant row10g seam.

`row10gH_trichotomy` gives the concrete coarse class, but current public
facts do not yet identify its private abstract leaf.  On a HOST leaf the
completion clause additionally needs the prepared/open deletion domain,
which `RiskView` does not record. -/
def R1Row10gHostRiskViewResidual : Prop :=
  ∀ {psi kappa tau : Nat}
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Cell psi kappa tau),
    let host := r1Host (kappa := kappa) (tau := tau) hpsi h2
    let v := riskViewOf host hpsi l r
    let w := row10gH host hpsi l r
    ¬ ldc host l.carrier r.carrier →
      concreteOutPhys l r w.1 w.2 = (absRowB9 v).phys ∧
      (PhysRow host l r w →
        leader (base l) = false ∧
        leader (base r) = false ∧
        BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
          hpsi (base l) (base r))

/-- Everything after the resistant row10g seam is already closed by Phys3. -/
theorem r1Row10gLeafRiskViewCompletion_of_residual
    (hResidual : R1Row10gHostRiskViewResidual) :
    R1Row10gLeafRiskViewCompletionClause := by
  unfold R1Row10gLeafRiskViewCompletionClause
  intro psi kappa tau hpsi h2 l r
  let host : HostRow (Phys psi kappa tau) :=
    r1Host (kappa := kappa) (tau := tau) hpsi h2
  let v := riskViewOf host hpsi l r
  let w := row10gH host hpsi l r
  change
    SpliceProjectionFacts host →
    ¬ ldc host l.carrier r.carrier →
      (((base w.1 = base l ∧ base w.2 = base r) →
          inputPhysPublic v = (absRowB9 v).phys) ∧
       (PhysRow host l r w →
          leader (base l) = false ∧
          leader (base r) = false ∧
          BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
            hpsi (base l) (base r) ∧
          absHostPhys v = (absRowB9 v).phys) ∧
       ((base w.1 = base l ∧
           base w.2 = relabelCell hpsi (base l) (base r)) →
          relabelPhysPublic v = (absRowB9 v).phys))
  intro _hFacts hNotLdc
  have hR := hResidual (psi := psi) (kappa := kappa) (tau := tau)
    hpsi h2 l r
  dsimp only at hR
  have hP := hR hNotLdc
  refine ⟨?_, ?_, ?_⟩
  · intro hk
    have hc := concreteOutPhys_keep host hpsi l r w.1 w.2 hk.1 hk.2
    exact hc.symm.trans hP.1
  · intro hh
    have hd := hP.2 hh
    have hc := r1Host_host_leaf_phys_projection_from_five_fields
      (kappa := kappa) (tau := tau) hpsi h2 l r w.1 w.2
      hd.1 hd.2.1 hd.2.2
      (by simpa [host] using hh.1)
      (by simpa [host] using hh.2)
    have hc' : concreteOutPhys l r w.1 w.2 = absHostPhys v := by
      simpa [host, v] using hc
    exact ⟨hd.1, hd.2.1, hd.2.2, hc'.symm.trans hP.1⟩
  · intro hr
    have hc := concreteOutPhys_relabel host hpsi l r w.1 w.2 hr.1 hr.2
    exact hc.symm.trans hP.1

/-- Conditional completion of the Phys4 R1 projection gate. -/
theorem r1Host_concreteRowB9PhysicalProjection_of_residual
    (hResidual : R1Row10gHostRiskViewResidual) :
    R1ConcreteRowB9PhysicalProjectionObligation :=
  r1Host_concreteRowB9PhysicalProjection
    (r1Row10gLeafRiskViewCompletion_of_residual hResidual)

end B9RiskRefinementPhys5
