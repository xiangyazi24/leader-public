import Leader.Wu.Coherence.FreshCoverSoundness

set_option autoImplicit false

namespace ZZShadowC1Degeneracy

variable {n ψ κ τ : Nat}

/-- Decisive probe: does the C1 Fresh endpoint follow from the payload hypothesis
ALONE, with the other five hypotheses unused?  If this compiles, the endpoint is
degenerate and its real content sits entirely in `Cover3PayloadReachableV31`. -/
theorem endpoint_of_payload_only
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (r : DirectedRing n)
    (payload : R2CoherenceV31FootprintCover3.Cover3PayloadReachableV31
      (κ := κ) (τ := τ) hψ h2 r) :
    ∀ C : R2CoherenceV31.FC n ψ κ τ,
      R2CoherenceV31QuarantineReach.ReachableFromQuarantineV31 hψ h2 r C →
      R2CoherenceV31FreshnessClear.ReachablePhaseFactsFreshV31 r C :=
  fun C hC =>
    R2CoherenceV31FreshnessClear.reachablePhaseFactsFresh_of_oldStrong r C
      (payload C hC)

end ZZShadowC1Degeneracy
