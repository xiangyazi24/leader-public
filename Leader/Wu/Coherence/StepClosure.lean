import Leader.Wu.Coherence.OpenRCoherence

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31Step

open R2CoherenceV31
open R2CoherenceV31Closure

variable {n ψ κ τ : Nat}

/-- The sole unresolved branch of V3.1 CHECK/ID coherence closure. -/
def OpenNoHazardCoherenceV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  BranchCoherenceObligationV31 (κ := κ) (τ := τ)
    hψ h2 ring .openNoHazard

/-- One arbitrary V3.1 service preserves the full coherence-closed domain. -/
def CoherenceStepV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (C : FC n ψ κ τ) (e : Fin n),
    CoherenceClosedV31 hψ h2 ring C →
      CoherenceClosedV31 hψ h2 ring (stepV3 hψ h2 ring C e)

/-- Assemble all ten branch cases.  Nine are compiled theorems; the tenth is
exactly `OpenNoHazardCoherenceV31`. -/
theorem coherenceStepV31_of_openNoHazard
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hOpenNoHazard : OpenNoHazardCoherenceV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    CoherenceStepV31 (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hClosed
  have hOpen :
      BranchCoherenceObligationV31 (κ := κ) (τ := τ)
        hψ h2 ring .openNoHazard := by
    simpa [OpenNoHazardCoherenceV31] using hOpenNoHazard
  have hGeometry :
      ElectionGeometryV31 ring (stepV3 hψ h2 ring C e) :=
    (R2CoherenceV31Closure2.electionGeometryStepV31
      (κ := κ) (τ := τ) hψ h2 ring) C e hClosed.1
  have hCoherenceSound :
      CoherentPrefixesV3 ring (stepV3 hψ h2 ring C e) ∧
        ControllerSoundV3 hψ h2 ring (stepV3 hψ h2 ring C e) := by
    cases hb : branchAtV3 hψ h2
        (C e) (C (ring.rightNeighbor e)) with
    | seek =>
        exact (R2CoherenceV31Closure.seek_coherence
          (κ := κ) (τ := τ) hψ h2 ring) C e hClosed hb
    | sweep =>
        exact (R2CoherenceV31Closure.sweep_coherence
          (κ := κ) (τ := τ) hψ h2 ring) C e hClosed hb
    | commit =>
        exact (R2CoherenceV31Closure.commit_coherence
          (κ := κ) (τ := τ) hψ h2 ring) C e hClosed hb
    | release =>
        exact (R2CoherenceV31Closure.release_coherence
          (κ := κ) (τ := τ) hψ h2 ring) C e hClosed hb
    | scrubL =>
        exact (R2CoherenceV31Closure.scrubL_coherence
          (κ := κ) (τ := τ) hψ h2 ring) C e hClosed hb
    | openR =>
        exact (R2CoherenceV31OpenRProof.openR_coherence
          (κ := κ) (τ := τ) hψ h2 ring) C e hClosed hb
    | sealed =>
        exact (R2CoherenceV31Closure2.sealed_coherence
          (κ := κ) (τ := τ) hψ h2 ring) C e hClosed hb
    | openHazard =>
        exact (R2CoherenceV31Closure.openHazard_coherence
          (κ := κ) (τ := τ) hψ h2 ring) C e hClosed hb
    | openNoHazard =>
        exact hOpen C e hClosed hb
    | mixed =>
        exact (R2CoherenceV31Closure.mixed_coherence
          (κ := κ) (τ := τ) hψ h2 ring) C e hClosed hb
  exact ⟨hGeometry, hCoherenceSound.1, hCoherenceSound.2⟩

/-- From one coherent entrance configuration, every finite scheduler word stays
inside `CoherenceClosedV31`.  This is the service-word reachability form of the
invariant. -/
def CoherenceInvariantV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C₀ : FC n ψ κ τ,
    CoherenceClosedV31 hψ h2 ring C₀ →
      ∀ w : List (Fin n),
        CoherenceClosedV31 hψ h2 ring
          (w.foldl (stepV3 hψ h2 ring) C₀)

/-- Compose one-step closure along an arbitrary finite service word. -/
theorem coherenceInvariantV31_of_openNoHazard
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hOpenNoHazard : OpenNoHazardCoherenceV31
      (κ := κ) (τ := τ) hψ h2 ring) :
    CoherenceInvariantV31 (κ := κ) (τ := τ) hψ h2 ring := by
  intro C₀ hC₀ w
  induction w generalizing C₀ with
  | nil =>
      simpa using hC₀
  | cons e w ih =>
      simp only [List.foldl_cons]
      apply ih
      exact
        (coherenceStepV31_of_openNoHazard
          (κ := κ) (τ := τ) hψ h2 ring hOpenNoHazard) C₀ e hC₀

end R2CoherenceV31Step
