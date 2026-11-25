import Leader.L3.ParamsFacts

/-!
# L3-PRIME signed-band parameter facts (`L3PRIME-TRANSFER.tex` (P2)-(P3))

On the signed band `s ≥ 40000`, with `A = 557 s + 119981`, `B = (s + 11)(s + 13)` and
`t = t_s = floor(log2 floor(B / (32 A)))`:
* `64 A ≤ B`, hence `t ≥ 1` (`signedB_ge`, `signedT_spec`);
* `32 A 2^t ≤ B < 64 A 2^t`, i.e. `32 A / B ≤ V < 64 A / B` for `V = 2^-t` (`signedT_spec`);
* `t < s` (`signedT_lt`), so `K = 2q - t > 2q - s`.
Core Lean only; no `sorry`, `axiom`, `native_decide`.
-/

namespace L3

set_option autoImplicit false

/-- `64 A_s ≤ B_s` for `s ≥ 40000` (`L3PRIME-TRANSFER.tex` (P2): `floor(B/(32A)) ≥ 2`). -/
theorem signedB_ge (s : Nat) (hs : 40000 ≤ s) : 64 * signedA s ≤ signedB s := by
  have h2 : 64 * signedA s ≤ 40000 * s := by
    have e : 64 * signedA s = 35648 * s + 7678784 := by
      show 64 * (557 * s + 119981) = 35648 * s + 7678784
      rw [Nat.mul_add, ← Nat.mul_assoc]
    have h4 : 7678784 ≤ 4352 * s :=
      Nat.le_trans (by decide : 7678784 ≤ 4352 * 40000) (Nat.mul_le_mul_left 4352 hs)
    rw [e, show 40000 * s = 35648 * s + 4352 * s by rw [← Nat.add_mul]]
    exact Nat.add_le_add_left h4 _
  have h1 : 40000 * s ≤ s * s := Nat.mul_le_mul_right s hs
  have h3 : s * s ≤ (s + 11) * (s + 13) :=
    Nat.mul_le_mul (Nat.le_add_right s 11) (Nat.le_add_right s 13)
  exact Nat.le_trans h2 (Nat.le_trans h1 h3)

/-- (P2)-(P3): `t_s ≥ 1` and `32 A 2^t ≤ B < 64 A 2^t` on the signed band. -/
theorem signedT_spec (s : Nat) (hs : 40000 ≤ s) :
    1 ≤ signedT s ∧
      32 * signedA s * 2 ^ signedT s ≤ signedB s ∧
      signedB s < 64 * signedA s * 2 ^ signedT s := by
  have hB := signedB_ge s hs
  have hApos : 0 < 32 * signedA s := by unfold signedA; omega
  have hm2 : 2 ≤ signedB s / (32 * signedA s) := by
    rw [Nat.le_div_iff_mul_le hApos]
    omega
  have hm0 : signedB s / (32 * signedA s) ≠ 0 := by omega
  have hlow : 2 ^ signedT s ≤ signedB s / (32 * signedA s) := by
    unfold signedT floorLogTwo
    exact Nat.log2_self_le hm0
  have hhigh : signedB s / (32 * signedA s) < 2 ^ (signedT s + 1) := by
    unfold signedT floorLogTwo
    exact Nat.lt_log2_self
  have hone : 1 ≤ signedT s := by
    unfold signedT floorLogTwo
    exact (Nat.le_log2 hm0).2 (by simpa using hm2)
  have hdiv : signedB s / (32 * signedA s) * (32 * signedA s) ≤ signedB s :=
    Nat.div_mul_le_self _ _
  have hmod := Nat.div_add_mod (signedB s) (32 * signedA s)
  have hmodlt := Nat.mod_lt (signedB s) hApos
  refine ⟨hone, ?_, ?_⟩
  · calc 32 * signedA s * 2 ^ signedT s
        ≤ 32 * signedA s * (signedB s / (32 * signedA s)) := Nat.mul_le_mul_left _ hlow
      _ = signedB s / (32 * signedA s) * (32 * signedA s) := Nat.mul_comm _ _
      _ ≤ signedB s := hdiv
  · have hsucc : signedB s / (32 * signedA s) + 1 ≤ 2 ^ (signedT s + 1) := hhigh
    have hpow : 2 ^ (signedT s + 1) = 2 * 2 ^ signedT s := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hstep : 32 * signedA s * (signedB s / (32 * signedA s) + 1) ≤
        32 * signedA s * (2 * 2 ^ signedT s) := by
      rw [← hpow]; exact Nat.mul_le_mul_left _ hsucc
    have heq : 64 * signedA s * 2 ^ signedT s = 32 * signedA s * (2 * 2 ^ signedT s) := by
      rw [show 64 * signedA s = 32 * signedA s * 2 by omega, Nat.mul_assoc]
    rw [heq]
    generalize signedB s / (32 * signedA s) = m at hstep hmod
    generalize signedB s % (32 * signedA s) = r at hmod hmodlt
    generalize 32 * signedA s * (2 * 2 ^ signedT s) = R at hstep ⊢
    generalize 32 * signedA s = a at hstep hmod hmodlt
    rw [Nat.mul_add, Nat.mul_one] at hstep
    omega

/-- `(s + 13)^2 ≤ 2^s` for `s ≥ 16`. -/
theorem signed_square_le_pow (s : Nat) (hs : 16 ≤ s) : (s + 13) * (s + 13) ≤ 2 ^ s := by
  have key : ∀ k : Nat, (k + 29) * (k + 29) ≤ 2 ^ (k + 16) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        have hpow : 2 ^ (k + 1 + 16) = 2 * 2 ^ (k + 16) := by
          rw [show k + 1 + 16 = (k + 16) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        have hsq : (k + 1 + 29) * (k + 1 + 29) = (k + 29) * (k + 29) + (2 * k + 59) := by
          rw [show k + 1 + 29 = (k + 29) + 1 by omega, Nat.add_mul, Nat.mul_add, Nat.mul_one,
            Nat.one_mul]
          omega
        have hge : 2 * k + 59 ≤ (k + 29) * (k + 29) := by
          have : 29 * (k + 29) ≤ (k + 29) * (k + 29) := Nat.mul_le_mul_right _ (by omega)
          omega
        rw [hpow, hsq]
        omega
  have h := key (s - 16)
  rw [show s - 16 + 29 = s + 13 by omega, show s - 16 + 16 = s by omega] at h
  exact h

/-- `t_s < s` on the signed band: `2^t ≤ B/(32A) ≤ B ≤ (s+13)^2 ≤ 2^s`, strictly. -/
theorem signedT_lt (s : Nat) (hs : 40000 ≤ s) : signedT s < s := by
  have hspec := signedT_spec s hs
  have hA : 1 ≤ signedA s := by unfold signedA; omega
  have hBle : signedB s ≤ (s + 13) * (s + 13) := by
    unfold signedB; exact Nat.mul_le_mul_right _ (by omega)
  have hsq := signed_square_le_pow s (by omega)
  have h32 : 2 ^ signedT s < 2 ^ s := by
    have h1 : 32 * 2 ^ signedT s ≤ 32 * signedA s * 2 ^ signedT s := by
      rw [Nat.mul_assoc 32]
      exact Nat.mul_le_mul_left 32 (Nat.le_mul_of_pos_left _ (by omega))
    have hp : 0 < 2 ^ signedT s := Nat.two_pow_pos _
    omega
  exact (Nat.pow_lt_pow_iff_right (by omega)).1 h32

/-- On the signed band, `signedT` is evaluated at the padded width `ceilLogTwo q`, and
`K = 2 q - t` with `t < ceilLogTwo q`. -/
theorem compileAdvice_K_signed_bounds (q : Nat) (h : signedBand q) :
    40000 ≤ ceilLogTwo q ∧
      (compileAdvice q).K = 2 * q - signedT (ceilLogTwo q) ∧
      1 ≤ signedT (ceilLogTwo q) ∧ signedT (ceilLogTwo q) < ceilLogTwo q := by
  have hs : 40000 ≤ max 2 (ceilLogTwo q) := (signedBand_iff q).1 h
  have hmax : max 2 (ceilLogTwo q) = ceilLogTwo q := by omega
  have hs' : 40000 ≤ ceilLogTwo q := by omega
  refine ⟨hs', ?_, (signedT_spec _ hs').1, signedT_lt _ hs'⟩
  rw [compileAdvice_K_signed q h, hmax]

/-- `0 < K` for every advice `q >= 1`, on both bands. -/
theorem compileAdvice_K_pos (q : Nat) (hq : 1 ≤ q) : 0 < (compileAdvice q).K := by
  by_cases hsb : signedBand q
  · obtain ⟨_, hK, _, hlt⟩ := compileAdvice_K_signed_bounds q hsb
    have hle := ceilLogTwo_le_self q
    rw [hK]
    omega
  · rw [compileAdvice_K_unsigned q hsb]
    omega

/-- `q ≤ K` for every advice `q`, on both bands (signed: `K = 2q - t_s`, `t_s < s ≤ q`). -/
theorem compileAdvice_K_ge_q (q : Nat) : q ≤ (compileAdvice q).K := by
  by_cases hsb : signedBand q
  · obtain ⟨_, hK, _, hlt⟩ := compileAdvice_K_signed_bounds q hsb
    have hle := ceilLogTwo_le_self q
    rw [hK]
    omega
  · rw [compileAdvice_K_unsigned q hsb]
    omega

/-- Every advice below `40000` is off the signed band. -/
theorem not_signedBand_of_small (q : Nat) (h : q < 40000) : ¬ signedBand q :=
  not_signedBand_of_lt q (by have := ceilLogTwo_le_self q; omega)

/-- Off the signed band `K = 2q + kappa` (`kdrop = 0`). -/
theorem compileAdvice_K_eq_add_kappa (q : Nat) (h : ¬ signedBand q) :
    (compileAdvice q).K = 2 * q + (compileAdvice q).kappa := by
  rw [compileAdvice_K_unsigned q h, compileAdvice_kappa_unsigned q h]

/-- The SMALL band (`q ≤ 79`) is off the signed band. -/
theorem not_signedBand_of_useSmall (q : Nat) (h : (compileAdvice q).useSmall = true) :
    ¬ signedBand q := by
  have hq : q ≤ qStar := of_decide_eq_true h
  have hstar : qStar = 79 := rfl
  exact not_signedBand_of_small q (by omega)

end L3
