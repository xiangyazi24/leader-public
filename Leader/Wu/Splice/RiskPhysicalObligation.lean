import Leader.Wu.Splice.RiskBooleanSelectors

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9RiskRefinementPhys

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
  B9RiskRefinement2

/-- Physical projection obligation for the literal served pair. -/
def ConcreteRowB9PhysicalProjectionObligation : Prop :=
  ∀ {psi kappa tau : Nat}
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau),
    B9Host.SpliceLaws host →
      let v := B9RiskAbstraction.riskViewOf host hpsi l r
      let w := B9SpliceTableHost.rowB9 host hpsi l r
      B9RiskAbstraction.concreteOutPhys l r w.1 w.2 =
        (B9RiskAbstraction.absRowB9 v).phys

namespace B9RiskRefinementPhys

/-- First HOST fact needed by the requested law-driven proof but absent from
`B9Host.SpliceLaws`.  This is the public analogue of the private
`RightFollowerLabelLaw` in `B9RecoveryRiskLeaves`. -/
def RightFollowerLabelProjectionLaw
    {psi kappa tau : Nat}
    (host : HostRow (Phys psi kappa tau)) : Prop :=
  ∀ (l r : Phys psi kappa tau),
    B9Host.leader r = false →
      B9Host.label (host.row l r).2 = B9Host.label r

/-- What the existing `SpliceLaws` really gives on the left follower. -/
theorem spliceLaws_leftFollowerLabel
    {psi kappa tau : Nat}
    (host : HostRow (Phys psi kappa tau))
    (h : B9Host.SpliceLaws host)
    (l r : Phys psi kappa tau)
    (hl : B9Host.leader l = false) :
    B9Host.label (host.row l r).1 = B9Host.label l :=
  h.left_follower_label l r hl

/-- What the existing `SpliceLaws` really gives for an old right leader. -/
theorem spliceLaws_rightLeader
    {psi kappa tau : Nat}
    (host : HostRow (Phys psi kappa tau))
    (h : B9Host.SpliceLaws host)
    (l r : Phys psi kappa tau)
    (hr : B9Host.leader r = true) :
    B9Host.leader (host.row l r).2 = true :=
  h.right_leader l r hr

/-- Alignment is only a guarded one-way preservation fact, not an exact
characterization of the HOST `aligned` output bit. -/
theorem spliceLaws_alignedFollowers
    {psi kappa tau : Nat}
    (host : HostRow (Phys psi kappa tau))
    (h : B9Host.SpliceLaws host)
    (l r : Phys psi kappa tau)
    (hl : B9Host.leader l = false)
    (hr : B9Host.leader r = false)
    (hol : B9Host.leader (host.row l r).1 = false)
    (hor : B9Host.leader (host.row l r).2 = false)
    (ha : B9Host.Aligned l r) :
    B9Host.Aligned (host.row l r).1 (host.row l r).2 :=
  h.aligned_followers l r hl hr hol hor ha

-- Needed in the HOST branch when the right input is a follower:
/- MISSING HOST LAW (finding): the right follower label is not determined by SpliceLaws:
B9Host.label (host.row (B9SpliceTableHost.base l)
    (B9SpliceTableHost.base r)).2 =
  B9Host.label (B9SpliceTableHost.base r)
-/

-- This determines the concrete `labelEqR = true` case.
-- `B9Host.SpliceLaws host` has no field from which to derive it.
