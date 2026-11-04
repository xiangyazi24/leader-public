import Leader.Wu.Birth.LeaderlessBirthMassRenewal
import Leader.Wu.Splice.OrderedWindowMatcher

set_option autoImplicit false

/-! # Boosting a small per-block escape mass to the seven-eighths leaf

`BirthLeaderlessBirthMassRenewal.UniformEscapeMass step Good B Q` says that from every `Good` state at most a
`(Q-1)/Q` fraction of the words of length `B` stay `Good` along every prefix.  Concatenating `3 Q` blocks
(`alive_tail`) and `8 (Q-1)^(3Q) ≤ Q^(3Q)` (cube of `2 (Q-1)^Q ≤ Q^Q`) gives the leaf with `Q = 8` at horizon
`3 Q B` (`escape_boost`).  So the uniform birth-mass leaf of B7 at horizon `3 Q B` follows from a per-block escape mass
`1/Q` on blocks of length `B`: for a horizon `Theta(n^2)`, a block of `O(n polylog n)` letters may have escape
probability as small as `polylog n / n`.
-/

namespace BirthLeafBoost

open BirthLeaderlessBirthMassRenewal

variable {S : Type} {n : Nat}

theorem eight_mul_pow_le (Q : Nat) (hQ : 1 ≤ Q) : 8 * (Q - 1) ^ (3 * Q) ≤ Q ^ (3 * Q) := by
  have h := B9OrderedWindowMatcher.two_mul_pow_le Q hQ
  have h3 : (2 * (Q - 1) ^ Q) ^ 3 ≤ (Q ^ Q) ^ 3 := Nat.pow_le_pow_left h 3
  have e1 : (2 * (Q - 1) ^ Q) ^ 3 = 8 * (Q - 1) ^ (3 * Q) := by
    rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm Q 3]
  have e2 : (Q ^ Q) ^ 3 = Q ^ (3 * Q) := by
    rw [← Nat.pow_mul, Nat.mul_comm Q 3]
  rw [e1, e2] at h3
  exact h3

theorem escape_boost (step : S → Fin n → S) (Good : S → Prop) (B Q : Nat) (hQ : 1 ≤ Q)
    (hmass : UniformEscapeMass step Good B Q) : UniformEscapeMass step Good (3 * Q * B) 8 := by
  intro x hx
  have ht := alive_tail step Good B Q hmass (3 * Q) x hx
  have hb := eight_mul_pow_le Q hQ
  have hpos : 0 < Q ^ (3 * Q) := Nat.pow_pos (by omega)
  generalize aliveCount step Good x (3 * Q * B) = A at ht ⊢
  generalize n ^ (3 * Q * B) = N at ht ⊢
  generalize Q ^ (3 * Q) = P at ht hb hpos
  generalize (Q - 1) ^ (3 * Q) = R at ht hb
  -- ht : P * A ≤ R * N, hb : 8 * R ≤ P
  have s1 : P * (8 * A) ≤ P * N := by
    calc P * (8 * A) = 8 * (P * A) := by rw [Nat.mul_left_comm]
      _ ≤ 8 * (R * N) := Nat.mul_le_mul_left _ ht
      _ = (8 * R) * N := by rw [Nat.mul_assoc]
      _ ≤ P * N := Nat.mul_le_mul_right _ hb
  have s2 : 8 * A ≤ N := Nat.le_of_mul_le_mul_left s1 hpos
  show 8 * A ≤ (8 - 1) * N
  omega

end BirthLeafBoost
