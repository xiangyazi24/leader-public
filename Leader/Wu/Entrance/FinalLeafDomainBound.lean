import Leader.Wu.Entrance.RecoveryThenLeaf

set_option autoImplicit false
set_option Elab.async false

namespace CFinalLeafDomain

variable {n psi : Nat}

/-- Domain-correct spelling of the calibrated C-final campaign bound.The additional hypotheses are exactly the domain of the only landed producer
of the shared birth leaf: the CHECK train needs at least three labels and a
non-wrapping psi-cell window. -/
theorem b7_bound_of_gates_v3_domain
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (_h3 : 2 < psi) (_hpsin : psi <= n) (hn4 : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (hC1 : R2CoherenceV31MissionGate.C1CoherenceGate
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring)
    (hC2 : CFinalAssembly3.C2RecoveryGateV3 hpsi h2 ring)
    (hC4 :
      B6EntranceK2Budget.B6EntranceK2Budget.B6EntranceK2Budget.FrozenC4GateBundle
        hpsi h2 ring)
    (hJ1 : CFinalAssembly.J1C1FinalCarrierJoin hpsi h2 ring)
    (hJ2 : CFinalAssembly.J2C1AdmissionLanding hpsi h2 ring)
    (hJ3 : CFinalAssembly.J3C2FinalCarrierJoin hpsi h2 ring)
    (hJ5 : CFinalAssembly.J5C4FinalCarrierJoin hpsi h2 ring)
    (hJ6 : CFinalAssembly2.J6C4WitnessToUniformMassV2 hpsi h2 ring)
    (hJ7 : CFinalAssembly3.J7PassiveAdmissionCompositionV3
      hpsi h2 hn4 ring anchor) :
    CFinalAssembly2.FinalB7OneOverN
      hpsi h2 ring (CFinalAssembly2.FinalLeafHV2 n psi) := by
  exact CFinalAssembly3.b7_bound_of_gates_v3
    hpsi h2 hn4 ring anchor
    hC1 hC2 hC4 hJ1 hJ2 hJ3 hJ5 hJ6 hJ7


end CFinalLeafDomain
