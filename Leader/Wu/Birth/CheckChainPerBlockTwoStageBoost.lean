import Leader.Wu.Birth.CheckChainPerBlock

set_option autoImplicit false
set_option Elab.async false

namespace BirthCheckChainR1PerBlockQ2Boost

open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring
open BirthLeaderlessBirthMassRenewal
open BirthCheckChainR1PerBlock

variable {n ψ κ τ : Nat}

/-- The pre-Q=8 two-stage block already amplifies to survival mass at most
one half after `Q₁*Q₂` consecutive blocks. -/
theorem leaf2_of_ready_window_mass
    (hψ : 0 < ψ) (h3 : 2 < ψ)
    (ring : DirectedRing n) (hψn : ψ ≤ n)
    (B₁ Q₁ Q₂ : Nat) (hQ₁ : 1 ≤ Q₁)
    (hQ :
      (4 * (ψ + 1)) ^ (ψ - 1) ≤
        3 ^ (ψ - 1) * Q₂)
    (h1 :
      ∀ C : BirthCheckPermitRepairLeaf.FC n ψ κ τ,
        BirthShortDoneTerminalFirstHit.Leaderless C →
        Q₁ * BirthTwoStageEscape.avoidCount
            (step1 hψ (by omega) ring)
            BirthShortDoneTerminalFirstHit.Leaderless
            (ReadyWindow ring) C B₁ ≤
          (Q₁ - 1) * n ^ B₁) :
    UniformEscapeMass
      (step1 (kappa := κ) (tau := τ) hψ (by omega) ring)
      BirthShortDoneTerminalFirstHit.Leaderless
      ((Q₁ * Q₂) * (B₁ + 2 * n * (ψ - 1))) 2 := by
  have hQ₂ : 1 ≤ Q₂ := by
    have hMpos : 0 < (4 * (ψ + 1)) ^ (ψ - 1) :=
      Nat.pow_pos (by omega)
    rcases Nat.eq_zero_or_pos Q₂ with h | h
    · rw [h, Nat.mul_zero] at hQ
      omega
    · exact h
  have hbase :
      UniformEscapeMass
        (step1 (kappa := κ) (tau := τ) hψ (by omega) ring)
        BirthShortDoneTerminalFirstHit.Leaderless
        (B₁ + 2 * n * (ψ - 1)) (Q₁ * Q₂) :=
    BirthTwoStageEscape.two_stage_escape
      (step1 (kappa := κ) (tau := τ) hψ (by omega) ring)
      BirthShortDoneTerminalFirstHit.Leaderless
      (ReadyWindow ring)
      B₁ (2 * n * (ψ - 1)) Q₁ Q₂ hQ₁ hQ₂ h1
      (fun C _ hC =>
        ready_stage_two hψ h3 ring hψn Q₂ hQ C hC)
  have hQpos : 0 < Q₁ * Q₂ :=
    Nat.mul_pos (by omega) (by omega)
  have hQone : 1 ≤ Q₁ * Q₂ := by
    omega
  intro C hC
  have ht :=
    alive_tail
      (step1 (kappa := κ) (tau := τ) hψ (by omega) ring)
      BirthShortDoneTerminalFirstHit.Leaderless
      (B₁ + 2 * n * (ψ - 1)) (Q₁ * Q₂) hbase
      (Q₁ * Q₂) C hC
  have hb :=
    B9OrderedWindowMatcher.two_mul_pow_le (Q₁ * Q₂) hQone
  have hpowpos : 0 < (Q₁ * Q₂) ^ (Q₁ * Q₂) :=
    Nat.pow_pos hQpos
  generalize
      aliveCount
        (step1 (kappa := κ) (tau := τ) hψ (by omega) ring)
        BirthShortDoneTerminalFirstHit.Leaderless C
        ((Q₁ * Q₂) * (B₁ + 2 * n * (ψ - 1))) = A
    at ht ⊢
  generalize
      n ^ ((Q₁ * Q₂) * (B₁ + 2 * n * (ψ - 1))) = N
    at ht ⊢
  generalize (Q₁ * Q₂) ^ (Q₁ * Q₂) = P
    at ht hb hpowpos
  generalize (Q₁ * Q₂ - 1) ^ (Q₁ * Q₂) = R
    at ht hb
  have hs : P * (2 * A) ≤ P * N := by
    calc
      P * (2 * A) = 2 * (P * A) := by ac_rfl
      _ ≤ 2 * (R * N) := Nat.mul_le_mul_left 2 ht
      _ = (2 * R) * N := by ac_rfl
      _ ≤ P * N := Nat.mul_le_mul_right N hb
  have hhalf : 2 * A ≤ N :=
    Nat.le_of_mul_le_mul_left hs hpowpos
  simpa using hhalf

end BirthCheckChainR1PerBlockQ2Boost

#print axioms BirthCheckChainR1PerBlockQ2Boost.leaf2_of_ready_window_mass
