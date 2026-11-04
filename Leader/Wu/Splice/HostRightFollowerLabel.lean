import Leader.Wu.Splice.PermitRepairHostLaws
import Leader.Wu.Splice.RiskPhysicalObligation

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9HostRightFollowerLabel

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open B9Host B9SpliceTableHost B9RiskAbstraction

variable {psi kappa tau : Nat}

/-- Exact right-end mirror of `B9Host.SpliceLaws.left_follower_label`.
Source: `Leader/Wu/Splice/HostRow.lean:132-134`.  The accepted left law has no
side condition besides the served initiator being a follower, so the mirror
has no side condition besides the served responder being a follower. -/
def RightFollowerLabelLaw
    (host : HostRow (Phys psi kappa tau)) : Prop :=
  ∀ l r : Phys psi kappa tau,
    leader r = false →
      label (host.row l r).2 = label r

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide

/-- Existing passive bounded/expiring cell: follower, label 0. -/
private def rfCell : Phys 3 3 1 :=
  B9AllPendingFixed.cleanPhys3 (0 : Fin 3)

/-- Literal width-two R1 host at the same carrier parameters. -/
private def rfHost : HostRow (Phys 3 3 1) :=
  r1Host (kappa := 3) (tau := 1) h3 h23

/-- Concrete non-birth responder relabel.
Both the input responder and the completed output responder are followers,
but the responder label changes 0 -> 1.  This is the P'_psi ruler-repair
branch (`Leader/Wu/Protocol/Algorithm.lean:30-44`), not K2 birth. -/
theorem r1Host_right_follower_relabel_witness :
    leader rfCell = false ∧
    leader (rfHost.row rfCell rfCell).2 = false ∧
    label rfCell = (0 : Fin 3) ∧
    label (rfHost.row rfCell rfCell).2 = (1 : Fin 3) := by
  decide +kernel

/-- Consequently the exact right-end mirror law is false for `r1Host`.
There is deliberately no theorem named `r1Host_right_follower_label`. -/
theorem r1Host_right_follower_label_false :
    ¬ RightFollowerLabelLaw rfHost := by
  intro hLaw
  have heq := hLaw rfCell rfCell
    r1Host_right_follower_relabel_witness.1
  have hin := r1Host_right_follower_relabel_witness.2.2.1
  have hout := r1Host_right_follower_relabel_witness.2.2.2
  rw [hout, hin] at heq
  exact (by decide : (1 : Fin 3) ≠ 0) heq

/-- Physical projection with the missing law supplied separately.
This shadows `B9RiskRefinementPhys.ConcreteRowB9PhysicalProjectionObligation`
without changing the accepted `B9Host.SpliceLaws` structure. -/
def ConcreteRowB9PhysicalProjectionObligation : Prop :=
  ∀ {psi kappa tau : Nat}
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau),
    B9Host.SpliceLaws host →
    RightFollowerLabelLaw host →
      let v := B9RiskAbstraction.riskViewOf host hpsi l r
      let w := B9SpliceTableHost.rowB9 host hpsi l r
      B9RiskAbstraction.concreteOutPhys l r w.1 w.2 =
        (B9RiskAbstraction.absRowB9 v).phys

/-- On a HOST leaf with a follower responder, the extra law makes the
abstractly observed HOST `labelEqR` bit true. -/
theorem riskView_hostLabelEqR_true_of_rightFollower
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r : B9SpliceTableHost.Cell psi kappa tau)
    (hRight : RightFollowerLabelLaw host)
    (hr : leader (base r) = false) :
    (B9RiskAbstraction.riskViewOf host hpsi l r).hostLabelEqR = true := by
  classical
  unfold B9RiskAbstraction.riskViewOf
  dsimp only
  simp [hRight (base l) (base r) hr]

/-- The same HOST law gives the concrete served output's `labelEqR` bit,
provided this branch has installed the selected host's right physical output. -/
theorem concrete_host_labelEqR_true_of_rightFollower
    (host : HostRow (Phys psi kappa tau))
    (l r wL wR : B9SpliceTableHost.Cell psi kappa tau)
    (hRight : RightFollowerLabelLaw host)
    (hr : leader (base r) = false)
    (hwR : base wR = (host.row (base l) (base r)).2) :
    (B9RiskAbstraction.concreteOutPhys l r wL wR).labelEqR = true := by
  classical
  unfold B9RiskAbstraction.concreteOutPhys
  dsimp only
  rw [hwR]
  simp [hRight (base l) (base r) hr]

/-- The requested HOST-leaf coordinate proof. `hwR` is the concrete HOST
physical-output equation; `hAbs` is the already-established branch fact that this
abstract leaf is a HOST leaf, hence its physical `labelEqR` field is
`v.hostLabelEqR`.  No other physical coordinate is claimed here. -/
theorem host_leaf_labelEqR_case
    (host : HostRow (Phys psi kappa tau)) (hpsi : 0 < psi)
    (l r wL wR : B9SpliceTableHost.Cell psi kappa tau)
    (hRight : RightFollowerLabelLaw host)
    (hr : leader (base r) = false)
    (hwR : base wR = (host.row (base l) (base r)).2)
    (hAbs :
      (B9RiskAbstraction.absRowB9
        (B9RiskAbstraction.riskViewOf host hpsi l r)).phys.labelEqR =
      (B9RiskAbstraction.riskViewOf host hpsi l r).hostLabelEqR) :
    (B9RiskAbstraction.concreteOutPhys l r wL wR).labelEqR =
      (B9RiskAbstraction.absRowB9
        (B9RiskAbstraction.riskViewOf host hpsi l r)).phys.labelEqR := by
  have hc := concrete_host_labelEqR_true_of_rightFollower
    host l r wL wR hRight hr hwR
  have hv := riskView_hostLabelEqR_true_of_rightFollower
    host hpsi l r hRight hr
  exact hc.trans (hAbs.trans hv).symm

end B9HostRightFollowerLabel


