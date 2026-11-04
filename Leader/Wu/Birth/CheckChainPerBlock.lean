import Leader.Wu.Birth.CheckChainWindowMass
import Leader.Wu.Birth.TwoStageEscape

set_option autoImplicit false

/-! # Per-block reduction of the R1 leaderless leaf to the ready-window mass

`ReadyWindow ring C`: some train window of `C` is ready (`ReadyCell k` at `cell ring s k` for `k < psi`).  The proved
window chain mass (`BirthCheckChainR1Mass.train_escape_mass_explicit`) is restated as a stage-two escape mass with
any `Q₂` such that `(4 (psi + 1))^(psi - 1) ≤ 3^(psi - 1) Q₂` (`ready_stage_two`).  With
`BirthTwoStageEscape.two_stage_escape` and `BirthLeafBoost.escape_boost`: if from every leaderless configuration at
most a `(Q₁ - 1)/Q₁` fraction of the words of length `B₁` stay leaderless without ever showing a ready window, then
the R1 step has the seven-eighths leaf at horizon `3 Q₁ Q₂ (B₁ + 2 n (psi - 1))` (`leaf_of_ready_window_mass`).
The premise is the open part of B6 (stages 1-3); nothing here asks the chain to succeed with constant probability.
-/

namespace BirthCheckChainR1PerBlock

open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring BirthCheckChainR1Mass BirthLeaderlessBirthMassRenewal

variable {n ψ κ τ : Nat}

/-- Some train window is ready. -/
def ReadyWindow (ring : DirectedRing n) (C : BirthCheckPermitRepairLeaf.FC n ψ κ τ) : Prop :=
  ∃ s : Fin n, ∀ k, k < ψ → ReadyCell k (C (cell ring s k))

theorem ready_stage_two (hψ : 0 < ψ) (h3 : 2 < ψ) (ring : DirectedRing n) (hψn : ψ ≤ n) (Q₂ : Nat)
    (hQ : (4 * (ψ + 1)) ^ (ψ - 1) ≤ 3 ^ (ψ - 1) * Q₂) (C : BirthCheckPermitRepairLeaf.FC n ψ κ τ) (hC : ReadyWindow ring C) :
    Q₂ * aliveCount (step1 hψ (by omega) ring) BirthShortDoneTerminalFirstHit.Leaderless C (2 * n * (ψ - 1)) ≤
      (Q₂ - 1) * n ^ (2 * n * (ψ - 1)) := by
  obtain ⟨s, hs⟩ := hC
  have hm := train_escape_mass_explicit (κ := κ) (τ := τ) hψ h3 ring hψn C s hs
  have hMpos : 0 < (4 * (ψ + 1)) ^ (ψ - 1) := Nat.pow_pos (by omega)
  generalize aliveCount (step1 hψ (by omega) ring) BirthShortDoneTerminalFirstHit.Leaderless C (2 * n * (ψ - 1)) = A
    at hm ⊢
  generalize n ^ (2 * n * (ψ - 1)) = N at hm ⊢
  generalize (4 * (ψ + 1)) ^ (ψ - 1) = M at hm hQ hMpos
  generalize 3 ^ (ψ - 1) = c at hm hQ
  -- hm : c * N + M * A ≤ M * N,  hQ : M ≤ c * Q₂
  have s1 : M * (Q₂ * A + N) ≤ Q₂ * (M * N) := by
    calc M * (Q₂ * A + N) = Q₂ * (M * A) + M * N := by
          rw [Nat.mul_add, Nat.mul_left_comm]
      _ ≤ Q₂ * (M * A) + (c * Q₂) * N := Nat.add_le_add_left (Nat.mul_le_mul_right _ hQ) _
      _ = Q₂ * (c * N + M * A) := by
          rw [Nat.mul_add, Nat.mul_comm c Q₂, Nat.mul_assoc, Nat.add_comm]
      _ ≤ Q₂ * (M * N) := Nat.mul_le_mul_left _ hm
  have s2 : M * (Q₂ * A + N) ≤ M * (Q₂ * N) := by
    rw [Nat.mul_left_comm] at s1; exact s1
  have s3 : Q₂ * A + N ≤ Q₂ * N := Nat.le_of_mul_le_mul_left s2 hMpos
  have e : (Q₂ - 1) * N = Q₂ * N - N := Nat.sub_one_mul Q₂ N
  rw [e]
  omega

theorem leaf_of_ready_window_mass (hψ : 0 < ψ) (h3 : 2 < ψ) (ring : DirectedRing n) (hψn : ψ ≤ n)
    (B₁ Q₁ Q₂ : Nat) (hQ₁ : 1 ≤ Q₁) (hQ : (4 * (ψ + 1)) ^ (ψ - 1) ≤ 3 ^ (ψ - 1) * Q₂)
    (h1 : ∀ C : BirthCheckPermitRepairLeaf.FC n ψ κ τ, BirthShortDoneTerminalFirstHit.Leaderless C →
      Q₁ * BirthTwoStageEscape.avoidCount (step1 hψ (by omega) ring) BirthShortDoneTerminalFirstHit.Leaderless
        (ReadyWindow ring) C B₁ ≤ (Q₁ - 1) * n ^ B₁) :
    UniformEscapeMass (step1 (kappa := κ) (tau := τ) hψ (by omega) ring) BirthShortDoneTerminalFirstHit.Leaderless
      (3 * (Q₁ * Q₂) * (B₁ + 2 * n * (ψ - 1))) 8 := by
  have hQ₂ : 1 ≤ Q₂ := by
    have hMpos : 0 < (4 * (ψ + 1)) ^ (ψ - 1) := Nat.pow_pos (by omega)
    rcases Nat.eq_zero_or_pos Q₂ with h | h
    · rw [h, Nat.mul_zero] at hQ; omega
    · exact h
  have two := BirthTwoStageEscape.two_stage_escape (step1 (kappa := κ) (tau := τ) hψ (by omega) ring)
    BirthShortDoneTerminalFirstHit.Leaderless (ReadyWindow ring) B₁ (2 * n * (ψ - 1)) Q₁ Q₂ hQ₁ hQ₂ h1
    (fun C _ hC => ready_stage_two hψ h3 ring hψn Q₂ hQ C hC)
  exact BirthLeafBoost.escape_boost _ _ (B₁ + 2 * n * (ψ - 1)) (Q₁ * Q₂) (Nat.mul_pos hQ₁ hQ₂) two

end BirthCheckChainR1PerBlock
