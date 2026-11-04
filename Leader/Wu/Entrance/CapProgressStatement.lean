import Leader.Wu.Entrance.WidthTwoWaitTransfer
import Leader.Wu.Birth.IncreaseOrCapDirtySuccess
import Leader.Wu.Birth.IncreaseOrCapPrefireBellman
import Leader.Wu.Birth.IncreaseOrCapFourWayCoverage
import Leader.Wu.Entrance.PassiveAdmission

set_option autoImplicit false

namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthLeaderlessBirthMassRenewal

variable {n ψ κ τ : Nat}

/-- A scheduler letter is an actual concrete realization of the old width-two
cap row, not merely a base state on which `RowCap2` would have been true. -/
def ConcreteB4CapFireAt
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (D : Config n ψ κ τ) (e : Fin n) : Prop :=
  BirthShortDoneTerminalPassiveR4.RowCap2
      hψ h2 κ ring (finalBase D) e ∧
    finalBase
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring D e) =
      BirthPhaseWait2BlockProgress.currentStep2
        hψ h2 ring (finalBase D) e

/-- Prefix-existential first-cap event on the literal original concrete word. -/
def ConcreteB4FirstCapWithin
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (C : Config n ψ κ τ) (u : List (Fin n)) : Prop :=
  ∃ pre : List (Fin n), ∃ e : Fin n, ∃ post : List (Fin n),
    u = pre ++ (e :: post) ∧
      ConcreteB4CapFireAt hψ h2 ring
        (pre.foldl
          (stepConcrete (κ := κ) (τ := τ) hψ h2 ring) C) e

/-- Exact final-step analogue of the old `CapOrEndpointProgress`. -/
def ConcreteB4CapOrEndpointProgress
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : Config n ψ κ τ) (u : List (Fin n)) : Prop :=
  ConcreteB4FirstCapWithin hψ h2 ring C u ∨
    BirthPhaseWait2BlockProgress.shortCountAt
        ring anchor (finalBase C) <
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (finalBase
          (u.foldl
            (stepConcrete (κ := κ) (τ := τ) hψ h2 ring) C))

noncomputable def concreteB4ProgressBit
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : Config n ψ κ τ) (u : List (Fin n)) : Nat := by
  classical
  exact if ConcreteB4CapOrEndpointProgress hψ h2 ring anchor C u
    then 1 else 0

noncomputable def concreteB4ProgressNumerator
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : Config n ψ κ τ) : Nat :=
  FixedSpanRenewalPayload.wordSum n
    (BirthPhaseWait2BlockProgress.L n)
    (concreteB4ProgressBit hψ h2 ring anchor C)

/-- Final B4 gate: constant mass on literal original `Fin n` scheduler words.
The start class is the repaired writer-passive admission, not the refuted
`.none`-only writer-clear class. -/
def ConcreteB4BlockProgressMassObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (hn : 4 ≤ n)
    (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  ∀ C : Config n ψ κ τ,
    ConcreteB7AdmittedPassive hψ h2 ring C →
    FinalLeaderless C →
    BirthPhaseWait2BlockProgress.Carrier
      hψ h2 hn ring anchor (finalBase C) →
    n ^ BirthPhaseWait2BlockProgress.L n ≤
      BirthPhaseWait2BlockProgress.Q *
        concreteB4ProgressNumerator hψ h2 ring anchor C

end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
