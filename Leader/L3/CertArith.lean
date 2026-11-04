import Leader.L3.ParamsFacts

/-!
# Arithmetic of the installed certificate

For every ring size `n ≥ 5`, with `q = ceilLogTwo n` and `c = compileAdvice q`, the recurrence period
is `r = 2^c.t - 1` (`Compiled.rho`) and the identifier radix is `a = c.topA`.  This file proves the
numeric facts used by `research/paper/l3/appendices/certificate.tex` (Proposition `prop:certificate`,
lines 70-98), `repair.tex` (`n ≥ t + r`) and Lemma `lem:fresh-scan` (`n ≥ t + 3`):

* `cert_block_bound`: `n < r * a ^ r`, i.e. the block count `m = n / r` satisfies `m < a ^ r`;
* `cert_n_ge_t_add_r`: `t + r ≤ n`;
* `cert_n_ge_t_add_three`: `t + 3 ≤ n`;
* `cert_rho_pos`, `cert_rho_le_n`, `cert_m_pos`: `0 < r ≤ n`, hence `m ≥ 1`.

Bands `q = 3..32` are finite checks (`decide +kernel`); `q ≥ 33` (where `t = psi = ceilLogTwo q`,
`s = psi`, `a ≥ 4`) is structural: `n ≤ 2^q ≤ 2^(r+1) < 2^(2r) ≤ a^r`.
-/

namespace L3

set_option autoImplicit false

/-- The recurrence period `r = 2^t - 1`. -/
def Compiled.rho (c : Compiled) : Nat := 2 ^ c.t - 1

/-! ## Finite bands `3 ≤ q ≤ 32` -/

theorem cert_finite_block :
    ∀ q, q < 33 → 3 ≤ q →
      2 ^ q < (compileAdvice q).rho * (compileAdvice q).topA ^ (compileAdvice q).rho := by
  decide +kernel

theorem cert_finite_t_add_r :
    ∀ q, q < 33 → 3 ≤ q → (compileAdvice q).t + (compileAdvice q).rho ≤ 2 ^ (q - 1) + 1 := by
  decide +kernel

/-! ## Structural band `q ≥ 33` -/

/-- Pure arithmetic: `q ≤ R + 1`, `R ≥ 2`, `a ≥ 4` give `2^q < R * a^R`. -/
theorem large_arith (q R a : Nat) (hR : 2 ≤ R) (hq : q ≤ R + 1) (ha : 4 ≤ a) :
    2 ^ q < R * a ^ R := by
  have h1 : 2 ^ q ≤ 2 ^ (R + 1) := Nat.pow_le_pow_right (by omega) hq
  have h2 : 2 ^ (R + 1) < 2 ^ (2 * R) := Nat.pow_lt_pow_right (by omega) (by omega)
  have h4 : (2 : Nat) ^ 2 = 4 := by decide
  have h3 : 2 ^ (2 * R) = 4 ^ R := by rw [Nat.pow_mul, h4]
  have h5 : 4 ^ R ≤ a ^ R := Nat.pow_le_pow_left ha R
  have h6 : a ^ R ≤ R * a ^ R := by
    calc a ^ R = 1 * a ^ R := (Nat.one_mul _).symm
      _ ≤ R * a ^ R := Nat.mul_le_mul_right _ (by omega)
  omega

/-- `3 * y + 3 ≤ 2 ^ y` for `y ≥ 4`. -/
theorem three_mul_add_three_le_two_pow (y : Nat) (hy : 4 ≤ y) : 3 * y + 3 ≤ 2 ^ y := by
  have key : ∀ k : Nat, 3 * (k + 4) + 3 ≤ 2 ^ (k + 4) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hp : 0 < 2 ^ (k + 4) := Nat.two_pow_pos (k + 4)
      have h2 : 2 ^ (k + 1 + 4) = 2 ^ (k + 4) * 2 := by
        have : k + 1 + 4 = (k + 4) + 1 := by omega
        rw [this]
        exact Nat.pow_succ 2 (k + 4)
      omega
  have := key (y - 4)
  have e : y - 4 + 4 = y := by omega
  rw [e] at this
  exact this

/-- For `q ≥ 33`, the data of the compile: `t = psi`, `s = psi`, `psi ≥ 6`, `a ≥ 4`. -/
theorem large_data (q : Nat) (hq : 33 ≤ q) :
    (compileAdvice q).t = ceilLogTwo q ∧ (compileAdvice q).s = ceilLogTwo q ∧
      6 ≤ ceilLogTwo q ∧ 4 ≤ (compileAdvice q).topA := by
  have h6 := ceilLogTwo_ge_six q hq
  have ht := compileAdvice_t_large q hq
  have hs : (compileAdvice q).s = ceilLogTwo q := by
    rw [compileAdvice_s]; omega
  refine ⟨ht, hs, h6, ?_⟩
  have hl : 2 ≤ floorLogTwo (compileAdvice q).s := by
    show 2 ≤ Nat.log2 (compileAdvice q).s
    exact (Nat.le_log2 (by omega)).2 (by omega)
  have hp : 2 ^ 2 ≤ 2 ^ floorLogTwo (compileAdvice q).s := Nat.pow_le_pow_right (by omega) hl
  have h4 : (2 : Nat) ^ 2 = 4 := by decide
  show 4 ≤ 2 ^ floorLogTwo (compileAdvice q).s
  omega

theorem cert_large_block (q : Nat) (hq : 33 ≤ q) :
    2 ^ q < (compileAdvice q).rho * (compileAdvice q).topA ^ (compileAdvice q).rho := by
  obtain ⟨ht, _, h6, ha⟩ := large_data q hq
  have hqψ : q ≤ 2 ^ ceilLogTwo q := (ceilLogTwo_spec q (by omega)).2
  have hpow : 2 ^ 6 ≤ 2 ^ ceilLogTwo q := Nat.pow_le_pow_right (by omega) h6
  have h64 : (2 : Nat) ^ 6 = 64 := by decide
  have hr : (compileAdvice q).rho = 2 ^ ceilLogTwo q - 1 := by
    unfold Compiled.rho; rw [ht]
  exact large_arith q _ _ (by omega) (by omega) ha

/-- `2^psi - 1 < 2 q` when `2^(psi-1) < q`, `psi ≥ 1`. -/
theorem pow_pred_bound (ψ q : Nat) (h1 : 1 ≤ ψ) (h2 : 2 ^ (ψ - 1) < q) : 2 ^ ψ - 1 < 2 * q := by
  obtain ⟨j, rfl⟩ : ∃ j, ψ = j + 1 := ⟨ψ - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h2
  have := Nat.pow_succ 2 j
  omega

theorem cert_large_t_add_r (q : Nat) (hq : 33 ≤ q) :
    (compileAdvice q).t + (compileAdvice q).rho ≤ 2 ^ (q - 1) + 1 := by
  obtain ⟨ht, _, h6, _⟩ := large_data q hq
  have hle := ceilLogTwo_le_self q
  have hspec := (ceilLogTwo_spec q (by omega)).1
  have hb := pow_pred_bound (ceilLogTwo q) q (by omega) hspec
  have hr : (compileAdvice q).rho = 2 ^ ceilLogTwo q - 1 := by
    unfold Compiled.rho; rw [ht]
  have hL := three_mul_add_three_le_two_pow (q - 1) (by omega)
  have e : 3 * (q - 1) + 3 = 3 * q := by omega
  omega

/-! ## Statements for ring size `n ≥ 5` -/

/-- For `n ≥ 5`, `q = ceilLogTwo n` satisfies `3 ≤ q`, `2^(q-1) < n ≤ 2^q`. -/
theorem ringQ_facts (n : Nat) (hn : 5 ≤ n) :
    3 ≤ ceilLogTwo n ∧ 2 ^ (ceilLogTwo n - 1) < n ∧ n ≤ 2 ^ ceilLogTwo n := by
  have h := ceilLogTwo_spec n (by omega)
  refine ⟨?_, h.1, h.2⟩
  rcases Nat.lt_or_ge (ceilLogTwo n) 3 with hc | hc
  · have hk : ceilLogTwo n ≤ 2 := by omega
    have : 2 ^ ceilLogTwo n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hk
    have h4 : (2 : Nat) ^ 2 = 4 := by decide
    omega
  · exact hc

/-- Block bound (`certificate.tex:70-98`): `n < r * a ^ r`, i.e. `m = n / r < a ^ r`. -/
theorem cert_block_bound (n : Nat) (hn : 5 ≤ n) :
    n < (compileAdvice (ceilLogTwo n)).rho *
      (compileAdvice (ceilLogTwo n)).topA ^ (compileAdvice (ceilLogTwo n)).rho := by
  obtain ⟨h3, _, hle⟩ := ringQ_facts n hn
  by_cases hq : ceilLogTwo n < 33
  · have := cert_finite_block (ceilLogTwo n) hq h3
    omega
  · have := cert_large_block (ceilLogTwo n) (by omega)
    omega

/-- The number of complete blocks `m = n / r` is below `a ^ r`. -/
theorem cert_blocks_lt (n : Nat) (hn : 5 ≤ n) :
    n / (compileAdvice (ceilLogTwo n)).rho <
      (compileAdvice (ceilLogTwo n)).topA ^ (compileAdvice (ceilLogTwo n)).rho := by
  have hb := cert_block_bound n hn
  have hr : 0 < (compileAdvice (ceilLogTwo n)).rho := by
    have := compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
    unfold Compiled.rho
    have : 2 ^ 2 ≤ 2 ^ (compileAdvice (ceilLogTwo n)).t := Nat.pow_le_pow_right (by omega) this
    have h4 : (2 : Nat) ^ 2 = 4 := by decide
    omega
  exact (Nat.div_lt_iff_lt_mul hr).2 (by rw [Nat.mul_comm]; exact hb)

/-- `n ≥ t + r` (`repair.tex:41`). -/
theorem cert_n_ge_t_add_r (n : Nat) (hn : 5 ≤ n) :
    (compileAdvice (ceilLogTwo n)).t + (compileAdvice (ceilLogTwo n)).rho ≤ n := by
  obtain ⟨h3, hgt, _⟩ := ringQ_facts n hn
  by_cases hq : ceilLogTwo n < 33
  · have := cert_finite_t_add_r (ceilLogTwo n) hq h3
    omega
  · have := cert_large_t_add_r (ceilLogTwo n) (by omega)
    omega

/-- `r ≥ 3`, hence `0 < r`. -/
theorem cert_rho_ge_three (n : Nat) (hn : 5 ≤ n) : 3 ≤ (compileAdvice (ceilLogTwo n)).rho := by
  have := compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  unfold Compiled.rho
  have : 2 ^ 2 ≤ 2 ^ (compileAdvice (ceilLogTwo n)).t := Nat.pow_le_pow_right (by omega) this
  have h4 : (2 : Nat) ^ 2 = 4 := by decide
  omega

theorem cert_rho_pos (n : Nat) (hn : 5 ≤ n) : 0 < (compileAdvice (ceilLogTwo n)).rho := by
  have := cert_rho_ge_three n hn
  omega

/-- `n ≥ t + 3` (hypothesis of `lem:fresh-scan`, `certificate.tex:189`). -/
theorem cert_n_ge_t_add_three (n : Nat) (hn : 5 ≤ n) :
    (compileAdvice (ceilLogTwo n)).t + 3 ≤ n := by
  have h1 := cert_n_ge_t_add_r n hn
  have h2 := cert_rho_ge_three n hn
  omega

/-- `r ≤ n`. -/
theorem cert_rho_le_n (n : Nat) (hn : 5 ≤ n) : (compileAdvice (ceilLogTwo n)).rho ≤ n := by
  have h1 := cert_n_ge_t_add_r n hn
  omega

/-- At least one complete block: `0 < m = n / r`. -/
theorem cert_m_pos (n : Nat) (hn : 5 ≤ n) : 0 < n / (compileAdvice (ceilLogTwo n)).rho :=
  Nat.div_pos (cert_rho_le_n n hn) (cert_rho_pos n hn)

end L3
