import Leader.Wu.Entrance.WriterProtectionWitness

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceLargeRingPackage

/-- The corrected C4 domain: psi is nontrivial and one full envelope fits strictly inside the ring. -/
def LargeRingDomain (psi n : Nat) : Prop :=
  2 < psi ∧ B6EntranceV2.envelopeWidth psi < n

/-- The fixed reverse K2 drain reaches the corrected K2 endpoint within one envelope sweep. -/
def K2DrainWithinEnvelopeSweep
    {n psi : Nat} (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (_hdom : LargeRingDomain psi n) : Prop :=
  B6EntranceV3.HostK2ClearableOrLeaderV3
    hpsi h2
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : B6EntranceV2.Phys psi psi (16 * psi) => q)
    ring (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceV2K2.k2DrainLength psi)

end B6EntranceLargeRingPackage
