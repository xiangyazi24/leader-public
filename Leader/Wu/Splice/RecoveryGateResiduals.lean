import Leader.Wu.Splice.RecoveryGateInstance
import Leader.Wu.Splice.RiskHostResidual
import Leader.Wu.Splice.RecoveryLeaderDrain


set_option autoImplicit false
set_option Elab.async false


namespace B9RecoveryGateResiduals


variable {n psi : Nat}


/-- Exact Phys5 residual consumed as `hDomain` by the installed gate. -/
abbrev Phys5HostDomainResidual : Prop :=
  B9RiskRefinementPhys5.R1Row10gHostRiskViewResidual


/-- Exact J4 residual consumed as `hJ4` after the C2 wiring specialization. -/
abbrev InternalJ4Residual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  B9RecoveryGate.C2J4RecoveryToB7Mass
    (kappa := psi) (tau := 16 * psi) hpsi h2 ring


/-- The sole physical host occurring in the C2 gate wiring. -/
abbrev C2R1Host
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) :
    B9Host.HostRow (B9Host.Phys psi psi (16 * psi)) :=
  B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2


@[simp] theorem c2R1Host_eq
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) :
    C2R1Host hpsi h2 =
      B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2 := by
  rfl


/-- `physicalHoldH` is an unconditional HOST-class physical row.This is exactly why fixing the host parameters does not prove the Phys5
`PhysRow -> follower/follower ∧ PreparedOrdinaryOpen` domain implication. -/
theorem c2_physicalHold_is_host_row
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : B9SpliceTableHost.Cell psi psi (16 * psi)) :
    B9SpliceTableHost.PhysRow (C2R1Host hpsi h2) l r
      (B9SpliceTableHost.physicalHoldH (C2R1Host hpsi h2) l r) := by
  exact B9SpliceTableHost.phys_hold (C2R1Host hpsi h2) l r

/-- The internal J4 content after removing the already-proved mass algebra. -/
abbrev C2InternalJ4Drain
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) : Prop :=
  B9RecoveryJ4Internal.RecoveryToLeaderDrain
    (kappa := psi) (tau := 16 * psi) hpsi h2 ring


/-- Wiring-only wrapper: the landed J4 theorem has exactly the instance target. -/
theorem internalJ4Residual_of_drain
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hDrain : C2InternalJ4Drain hpsi h2 ring) :
    InternalJ4Residual hpsi h2 ring := by
  exact B9RecoveryJ4Internal.c2J4RecoveryToB7Mass_of_drain
    (kappa := psi) (tau := 16 * psi) hpsi h2 ring hDrain


/-- Installed C2 gate with J4 reduced to its genuine internal drain residual.Phys5 stays explicit because the current gate consumes the global clause. -/
theorem c2RecoveryGate_of_phys5_and_internalDrain
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hDomain : Phys5HostDomainResidual)
    (hDrain : C2InternalJ4Drain hpsi h2 ring) :
    B9RecoveryGate.C2RecoveryGate
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring := by
  exact B9RecoveryGateInstance.c2RecoveryGate_of_installed
    (n := n) (psi := psi) (kappa := psi) (tau := 16 * psi)
    hpsi h2 ring hDomain
    (internalJ4Residual_of_drain hpsi h2 ring hDrain)




end B9RecoveryGateResiduals
