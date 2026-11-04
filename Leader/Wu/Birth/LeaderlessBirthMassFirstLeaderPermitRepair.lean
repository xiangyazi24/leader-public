import Leader.Wu.Birth.LeaderlessBirthMassFirstLeaderGeneric
import Leader.Wu.Birth.CheckChainFirstLeaderTail

set_option autoImplicit false

/-!
# B7 first-leader failure bounds for the literal R1 step

This module gives R1 its own step-indexed failure numerator. It is exactly
`aliveCount` for `BirthCheckPermitRepairLeaf.step1`, NOT the consumer-specific
`BirthPhaseFirstLeaderComposition.firstLeaderFailureNumerator`.

The uniform and restricted R1 leaf aliases retain the existing leaf types.
The generic B7 theorem applies directly to each, with no consumer/R1
agreement assumption. The ready-window producer premise gives the uniform
leaf at `3 * (Q1 * Q2) * (B1 + 2 * n * (psi - 1))`.

The last theorem merely repackages the already existing
`BirthCheckChainR1FirstLeaderTail.first_leader_tail_of_ready_window_mass`
in this named R1 currency. It proves neither the producer premise nor a
numerical or asymptotic calibration of that horizon. No transition changes,
consumer-step equality, or B9 scheduler projection are asserted.
-/

namespace BirthLeaderlessBirthMassB7R1

-- Open the defining namespace of step1, rather than unfolding the row.
open BirthCheckPermitRepairLeaf BirthCheckChainR1PerBlock

variable {n ψ κ τ : Nat}

abbrev FC (n ψ κ τ : Nat) := BirthCheckPermitRepairLeaf.FC n ψ κ τ

/-- Failure to see a physical leader at any prefix under R1. -/
noncomputable def firstLeaderFailureNumerator
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (T : Nat) : Nat :=
  BirthLeaderlessBirthMassB7Generic.firstLeaderFailureNumerator
    (step1 hψ h2 ring) BirthShortDoneTerminalFirstHit.Leaderless C T

theorem firstLeaderFailureNumerator_eq_aliveCount
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : FC n ψ κ τ) (T : Nat) :
    firstLeaderFailureNumerator hψ h2 ring C T =
      BirthLeaderlessBirthMassRenewal.aliveCount (step1 hψ h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless C T :=
  rfl

/-- Existing R1 leaf, exposed with the B7 interface name. -/
abbrev UniformFirstHitBirthMass
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (L : Nat) : Prop :=
  BirthCheckPermitRepairLeaf.UniformR1BirthMass
    (kappa := κ) (tau := τ) hψ h2 ring L

/-- Existing restricted-class R1 leaf. -/
abbrev UniformFirstHitBirthMassOn
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (R : FC n ψ κ τ → Prop) (L : Nat) : Prop :=
  BirthCheckPermitRepairLeaf.UniformR1BirthMassOn hψ h2 ring R L

/-- R1 is a direct instance of the generic B7 tail. -/
theorem firstLeader_failure_le_one_over_n_of_uniformBirthMass
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (L : Nat)
    (hmass : UniformFirstHitBirthMass (κ := κ) (τ := τ) hψ h2 ring L)
    (hn : 2 ≤ n) (C : FC n ψ κ τ)
    (hC : BirthShortDoneTerminalFirstHit.Leaderless C) :
    n * firstLeaderFailureNumerator hψ h2 ring C
        (6 * (Nat.log2 n + 1) * L) ≤
      n ^ (6 * (Nat.log2 n + 1) * L) :=
  BirthLeaderlessBirthMassB7Generic.firstLeader_failure_le_one_over_n_of_uniformBirthMass
    (step1 hψ h2 ring) BirthShortDoneTerminalFirstHit.Leaderless
    L hmass hn C hC

/-- Restricted-class R1 instance, keeping the explicit step1 closure premise. -/
theorem firstLeader_failure_le_one_over_n_of_uniformBirthMassOn
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (R : FC n ψ κ τ → Prop)
    (hR : ∀ C e, R C → R (step1 hψ h2 ring C e)) (L : Nat)
    (hmass : UniformFirstHitBirthMassOn hψ h2 ring R L)
    (hn : 2 ≤ n) (C : FC n ψ κ τ) (hCR : R C)
    (hC : BirthShortDoneTerminalFirstHit.Leaderless C) :
    n * firstLeaderFailureNumerator hψ h2 ring C
        (6 * (Nat.log2 n + 1) * L) ≤
      n ^ (6 * (Nat.log2 n + 1) * L) :=
  BirthLeaderlessBirthMassB7Generic.firstLeader_failure_le_one_over_n_of_uniformBirthMassOn
    (step1 hψ h2 ring) BirthShortDoneTerminalFirstHit.Leaderless
    R hR L hmass hn C hCR hC

/-- The exact ready-window premise produces the R1 B7 leaf at its actual
horizon. In particular, the horizon is not silently replaced by 256*n^2. -/
theorem uniformBirthMass_of_ready_window_mass
    (hψ : 0 < ψ) (h3 : 2 < ψ) (ring : DirectedRing n) (hψn : ψ ≤ n)
    (B₁ Q₁ Q₂ : Nat) (hQ₁ : 1 ≤ Q₁)
    (hQ : (4 * (ψ + 1)) ^ (ψ - 1) ≤ 3 ^ (ψ - 1) * Q₂)
    (h1 : ∀ C : FC n ψ κ τ, BirthShortDoneTerminalFirstHit.Leaderless C →
      Q₁ * BirthTwoStageEscape.avoidCount (step1 hψ (by omega) ring)
        BirthShortDoneTerminalFirstHit.Leaderless (ReadyWindow ring) C B₁ ≤
          (Q₁ - 1) * n ^ B₁) :
    UniformFirstHitBirthMass (κ := κ) (τ := τ) hψ (by omega) ring
      (3 * (Q₁ * Q₂) * (B₁ + 2 * n * (ψ - 1))) :=
  BirthCheckChainR1PerBlock.leaf_of_ready_window_mass
    (κ := κ) (τ := τ) hψ h3 ring hψn B₁ Q₁ Q₂ hQ₁ hQ h1

/-- R1 B7 first-leader failure bound from h1. This is definitionally the
existing first_leader_tail_of_ready_window_mass conclusion, with a named
R1 numerator; the existing theorem supplies the entire proof. -/
theorem firstLeader_failure_le_one_over_n_of_ready_window_mass
    (hψ : 0 < ψ) (h3 : 2 < ψ) (ring : DirectedRing n) (hψn : ψ ≤ n)
    (B₁ Q₁ Q₂ : Nat) (hQ₁ : 1 ≤ Q₁)
    (hQ : (4 * (ψ + 1)) ^ (ψ - 1) ≤ 3 ^ (ψ - 1) * Q₂)
    (h1 : ∀ C : FC n ψ κ τ, BirthShortDoneTerminalFirstHit.Leaderless C →
      Q₁ * BirthTwoStageEscape.avoidCount (step1 hψ (by omega) ring)
        BirthShortDoneTerminalFirstHit.Leaderless (ReadyWindow ring) C B₁ ≤
          (Q₁ - 1) * n ^ B₁)
    (hn : 2 ≤ n) (C : FC n ψ κ τ)
    (hC : BirthShortDoneTerminalFirstHit.Leaderless C) :
    n * firstLeaderFailureNumerator hψ (by omega) ring C
        (6 * (Nat.log2 n + 1) *
          (3 * (Q₁ * Q₂) * (B₁ + 2 * n * (ψ - 1)))) ≤
      n ^ (6 * (Nat.log2 n + 1) *
        (3 * (Q₁ * Q₂) * (B₁ + 2 * n * (ψ - 1)))) :=
  BirthCheckChainR1FirstLeaderTail.first_leader_tail_of_ready_window_mass
    (κ := κ) (τ := τ) hψ h3 ring hψn B₁ Q₁ Q₂ hQ₁ hQ h1 hn C hC

end BirthLeaderlessBirthMassB7R1
