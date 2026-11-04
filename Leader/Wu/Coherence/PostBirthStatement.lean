import Leader.Wu.Coherence.StepClosure
import Leader.Wu.Coherence.OpenEntrance


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace R2CoherenceV31Mission


open R2CoherenceV31
open R2CoherenceV31Closure
open R2CoherenceV31Step


variable {n ψ κ τ : Nat}


/-- Immutable Prove2Me mission surface for post-birth CHECK/ID coherence. -/
def PostBirthCheckIdCoherenceMissionV1
    (BirthEntranceV1 : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C₀ : FC n ψ κ τ,
    BirthEntranceV1 C₀ →
      ∀ w : List (Fin n),
        ElectionGeometryV31 ring
            (w.foldl (stepV3 hψ h2 ring) C₀) ∧
          CoherentPrefixesV3 ring
            (w.foldl (stepV3 hψ h2 ring) C₀)


/-- Producer-facing empty-word entrance obligation for mission V1. -/
def BirthEntranceProducerV31V1
    (BirthEntranceV1 : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    BirthEntranceV1 C →
      ElectionGeometryV31 ring C ∧ CoherentPrefixesV3 ring C


/-- Implementation-side bridge into the current V3.1 closed domain. -/
def EntranceClosedBridgeV31V1
    (BirthEntranceV1 : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : FC n ψ κ τ,
    BirthEntranceV1 C →
      CoherenceClosedV31 hψ h2 ring C

theorem coherenceClosedV31_projects
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    {C : FC n ψ κ τ}
    (hClosed : CoherenceClosedV31 hψ h2 ring C) :
    ElectionGeometryV31 ring C ∧ CoherentPrefixesV3 ring C := by
  exact ⟨hClosed.1, hClosed.2.1⟩

theorem mission_of_bridge_and_openNoHazard
    (BirthEntranceV1 : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hOpenNoHazard : OpenNoHazardCoherenceV31
      (κ := κ) (τ := τ) hψ h2 ring)
    (hBridge : EntranceClosedBridgeV31V1
      (κ := κ) (τ := τ) BirthEntranceV1 hψ h2 ring) :
    PostBirthCheckIdCoherenceMissionV1
      (κ := κ) (τ := τ) BirthEntranceV1 hψ h2 ring := by
  intro C₀ hBirth w
  have hClosed :
      CoherenceClosedV31 hψ h2 ring
        (w.foldl (stepV3 hψ h2 ring) C₀) :=
    (coherenceInvariantV31_of_openNoHazard
      (κ := κ) (τ := τ) hψ h2 ring hOpenNoHazard)
      C₀ (hBridge C₀ hBirth) w
  exact coherenceClosedV31_projects hψ h2 ring hClosed

theorem mission_gives_producer
    (BirthEntranceV1 : FC n ψ κ τ → Prop)
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hMission : PostBirthCheckIdCoherenceMissionV1
      (κ := κ) (τ := τ) BirthEntranceV1 hψ h2 ring) :
    BirthEntranceProducerV31V1
      (κ := κ) (τ := τ) BirthEntranceV1 hψ ring := by
  intro C hBirth
  have hEmpty := hMission C hBirth ([] : List (Fin n))
  simpa using hEmpty


end R2CoherenceV31Mission
