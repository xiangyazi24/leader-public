import Leader.Wu.Birth.CheckChainPerBlock

set_option autoImplicit false

/-! # R1 first-leader tail from the ready-window mass

The B7 currency on the R1 step: with the per-block premise of `BirthCheckChainR1PerBlock.leaf_of_ready_window_mass`
and `BirthLeaderlessBirthMassRenewal.tail_one_over_n`, from every leaderless configuration on `n ≥ 2` cells at most a
`1/n` fraction of the words of length `6 (log2 n + 1) * 3 Q₁ Q₂ (B₁ + 2 n (psi - 1))` stay leaderless under `step1`
(`first_leader_tail_of_ready_window_mass`).  This is the step1 counterpart of
`BirthLeaderlessBirthMassB7.firstLeader_failure_le_one_over_n_of_uniformBirthMass`, which is stated for the consumer
step `currentStep2`.
-/

namespace BirthCheckChainR1FirstLeaderTail

open BirthCheckPermitRepairLeaf BirthLeaderlessBirthMassRenewal BirthCheckChainR1PerBlock

variable {n ψ κ τ : Nat}

theorem first_leader_tail_of_ready_window_mass (hψ : 0 < ψ) (h3 : 2 < ψ) (ring : DirectedRing n) (hψn : ψ ≤ n)
    (B₁ Q₁ Q₂ : Nat) (hQ₁ : 1 ≤ Q₁) (hQ : (4 * (ψ + 1)) ^ (ψ - 1) ≤ 3 ^ (ψ - 1) * Q₂)
    (h1 : ∀ C : BirthCheckPermitRepairLeaf.FC n ψ κ τ, BirthShortDoneTerminalFirstHit.Leaderless C →
      Q₁ * BirthTwoStageEscape.avoidCount (step1 hψ (by omega) ring) BirthShortDoneTerminalFirstHit.Leaderless
        (ReadyWindow ring) C B₁ ≤ (Q₁ - 1) * n ^ B₁)
    (hn : 2 ≤ n) (C : BirthCheckPermitRepairLeaf.FC n ψ κ τ) (hC : BirthShortDoneTerminalFirstHit.Leaderless C) :
    n * aliveCount (step1 hψ (by omega) ring) BirthShortDoneTerminalFirstHit.Leaderless C
        (6 * (Nat.log2 n + 1) * (3 * (Q₁ * Q₂) * (B₁ + 2 * n * (ψ - 1)))) ≤
      n ^ (6 * (Nat.log2 n + 1) * (3 * (Q₁ * Q₂) * (B₁ + 2 * n * (ψ - 1)))) :=
  tail_one_over_n _ _ _ (leaf_of_ready_window_mass hψ h3 ring hψn B₁ Q₁ Q₂ hQ₁ hQ h1) hn C hC

end BirthCheckChainR1FirstLeaderTail
