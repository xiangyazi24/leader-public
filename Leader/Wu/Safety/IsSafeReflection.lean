import Leader.Wu.Scheduler.ClosedDomainAmplification

set_option autoImplicit false
set_option Elab.async false

namespace ZZIsSafeDecidable

/-- Exact Boolean reflection of Definition-1 safety.

This is intentionally noncomputable: `PopulationProtocol.IsSafe` quantifies
over the whole forward closure.  The amplification API requires only the
reflection theorem below, not an executable finite-search procedure. -/
noncomputable def isSafeBool
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (C : P.Configuration n) : Bool := by
  classical
  exact if PopulationProtocol.IsSafe P ring C isLeader then true else false

/-- The exact `hdec` argument required by
`boundedIsSafeProducer_repeatedBlockSSLEOn`. -/
theorem isSafeBool_hdec
    (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) (isLeader : P.Y → Bool) :
    ∀ C : P.Configuration n,
      isSafeBool P ring isLeader C = true ↔
        PopulationProtocol.IsSafe P ring C isLeader := by
  intro C
  classical
  simp [isSafeBool]

end ZZIsSafeDecidable

#print axioms ZZIsSafeDecidable.isSafeBool_hdec
