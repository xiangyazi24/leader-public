import Leader.L3.Params

/-!
# Facts about the production compile `compileAdvice q`

Arithmetic properties of `Leader/L3/Params.lean` used by the Lean model:

1. `ceilLogTwo` specification and uniqueness;
2. band facts: certificate width `t`, padded width `s`;
3. the SMALL band bound `K ≤ 175 < kStar` (finite check, `decide +kernel`);
4. the compiler invariant `K + 1 < 2 ^ b` for all `q ≥ 3` (structural, not a finite check);
5. the LIVE-TOP radix `0 < topA ≤ s`.

Only core Lean (no Mathlib, no Batteries); no `sorry`, `axiom`, `native_decide`.
-/

namespace L3

set_option autoImplicit false

/-! ## 1. `ceilLogTwo` -/

/-- For `m ≥ 2`, `ceilLogTwo m = log2 (m-1) + 1` (the `else` branch of `ceilLogTwo`). -/
theorem ceilLogTwo_eq (m : Nat) (hm : 2 ≤ m) : ceilLogTwo m = Nat.log2 (m - 1) + 1 := by
  unfold ceilLogTwo
  have h : ¬ m ≤ 1 := by omega
  rw [if_neg h]

/-- `2^(k-1) < m ≤ 2^k` for `k = ceilLogTwo m`, `m ≥ 2` (`composed-full.mjs:47`). -/
theorem ceilLogTwo_spec (m : Nat) (hm : 2 ≤ m) :
    2 ^ (ceilLogTwo m - 1) < m ∧ m ≤ 2 ^ ceilLogTwo m := by
  rw [ceilLogTwo_eq m hm]
  have h1 : m - 1 ≠ 0 := by omega
  have h := (Nat.log2_eq_iff h1).1 rfl
  simp only [Nat.add_sub_cancel]
  omega

/-- Uniqueness: `2^(k-1) < m ≤ 2^k` and `k ≥ 1` force `ceilLogTwo m = k`. -/
theorem ceilLogTwo_unique (k m : Nat) (hk : 1 ≤ k) (h1 : 2 ^ (k - 1) < m) (h2 : m ≤ 2 ^ k) :
    ceilLogTwo m = k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1
  have hp : 0 < 2 ^ j := Nat.two_pow_pos j
  have hm : 2 ≤ m := by omega
  rw [ceilLogTwo_eq m hm]
  have : Nat.log2 (m - 1) = j := by
    rw [Nat.log2_eq_iff (by omega)]
    exact ⟨by omega, by omega⟩
  omega

/-- `ceilLogTwo m ≤ m`. -/
theorem ceilLogTwo_le_self (m : Nat) : ceilLogTwo m ≤ m := by
  by_cases hm : 2 ≤ m
  · have h := (ceilLogTwo_spec m hm).1
    have h2 : ceilLogTwo m - 1 < 2 ^ (ceilLogTwo m - 1) := Nat.lt_two_pow_self
    omega
  · unfold ceilLogTwo
    have h : m ≤ 1 := by omega
    rw [if_pos h]
    omega

/-- `ceilLogTwo q ≥ 2` for `q ≥ 3`. -/
theorem ceilLogTwo_ge_two (q : Nat) (hq : 3 ≤ q) : 2 ≤ ceilLogTwo q := by
  have h := (ceilLogTwo_spec q (by omega)).2
  rcases Nat.lt_or_ge (ceilLogTwo q) 2 with hc | hc
  · have hk : ceilLogTwo q ≤ 1 := by omega
    have : 2 ^ ceilLogTwo q ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) hk
    omega
  · exact hc

/-- `ceilLogTwo q ≥ 6` for `q ≥ 33`. -/
theorem ceilLogTwo_ge_six (q : Nat) (hq : 33 ≤ q) : 6 ≤ ceilLogTwo q := by
  have h := (ceilLogTwo_spec q (by omega)).2
  rcases Nat.lt_or_ge (ceilLogTwo q) 6 with hc | hc
  · have hk : ceilLogTwo q ≤ 5 := by omega
    have : 2 ^ ceilLogTwo q ≤ 2 ^ 5 := Nat.pow_le_pow_right (by omega) hk
    have h32 : (2 : Nat) ^ 5 = 32 := by decide
    omega
  · exact hc

/-! ## 2. Band facts -/

/-- `t = finiteCertWidth q` for `3 ≤ q ≤ 32`. -/
theorem compileAdvice_t_finite (q : Nat) (h3 : 3 ≤ q) (h32 : q ≤ 32) :
    (compileAdvice q).t = finiteCertWidth q := by
  have hne : sourceTOfQ q ≠ 1 := by
    have := ceilLogTwo_ge_two q h3
    unfold sourceTOfQ
    omega
  have : (compileAdvice q).t =
      (if sourceTOfQ q = 1 then 2 else if q ≤ 32 then finiteCertWidth q else sourceTOfQ q) := rfl
  rw [this, if_neg hne, if_pos h32]

/-- `t = ceilLogTwo q` for `q ≥ 33`. -/
theorem compileAdvice_t_large (q : Nat) (h33 : 33 ≤ q) :
    (compileAdvice q).t = ceilLogTwo q := by
  have hne : sourceTOfQ q ≠ 1 := by
    have := ceilLogTwo_ge_two q (by omega)
    unfold sourceTOfQ
    omega
  have : (compileAdvice q).t =
      (if sourceTOfQ q = 1 then 2 else if q ≤ 32 then finiteCertWidth q else ceilLogTwo q) := rfl
  have hn : ¬ q ≤ 32 := by omega
  rw [this, if_neg hne, if_neg hn]

/-- `s = max 2 (ceilLogTwo q)` for every `q`. -/
theorem compileAdvice_s (q : Nat) : (compileAdvice q).s = max 2 (ceilLogTwo q) := rfl

/-- `2 ≤ t` for `q ≥ 3`. -/
theorem compileAdvice_t_ge_two (q : Nat) (h3 : 3 ≤ q) : 2 ≤ (compileAdvice q).t := by
  by_cases h32 : q ≤ 32
  · rw [compileAdvice_t_finite q h3 h32]
    unfold finiteCertWidth
    split <;> (try split) <;> omega
  · rw [compileAdvice_t_large q (by omega)]
    exact ceilLogTwo_ge_two q h3

/-- For `q ≥ 33`: `t ≤ 17 ↔ ceilLogTwo q ≤ 17` (tap table coverage). -/
theorem compileAdvice_t_le_17_iff (q : Nat) (h33 : 33 ≤ q) :
    (compileAdvice q).t ≤ 17 ↔ ceilLogTwo q ≤ 17 := by
  rw [compileAdvice_t_large q h33]

/-- `q = 9..16`: `t = 3` and `s = 4`. -/
theorem compileAdvice_nine_to_sixteen (q : Nat) (h9 : 9 ≤ q) (h16 : q ≤ 16) :
    (compileAdvice q).t = 3 ∧ (compileAdvice q).s = 4 := by
  constructor
  · rw [compileAdvice_t_finite q (by omega) (by omega)]
    unfold finiteCertWidth
    have h4 : ¬ q ≤ 4 := by omega
    rw [if_neg h4, if_pos h16]
  · have h8 : (2 : Nat) ^ (4 - 1) = 8 := by decide
    have h16' : (2 : Nat) ^ 4 = 16 := by decide
    have := ceilLogTwo_unique 4 q (by omega) (by omega) (by omega)
    have hs := compileAdvice_s q
    rw [this] at hs
    omega

/-! ## 3. SMALL band -/

/-- `K ≤ 175` on `3 ≤ q ≤ 79`: finite check over the whole SMALL band. -/
theorem compileAdvice_K_le_smallCap_range :
    ∀ q, q < 80 → 3 ≤ q → (compileAdvice q).K ≤ 175 := by
  decide +kernel

/-- SMALL band: `useSmall = true`, `q ≥ 3` give `K ≤ 175`. -/
theorem compileAdvice_K_le_smallCap (q : Nat) (h3 : 3 ≤ q) (hs : (compileAdvice q).useSmall = true) :
    (compileAdvice q).K ≤ 175 := by
  have hq : q ≤ qStar := by
    have : (compileAdvice q).useSmall = decide (q ≤ qStar) := rfl
    rw [this] at hs
    exact of_decide_eq_true hs
  have : q < 80 := by
    have : qStar = 79 := rfl
    omega
  exact compileAdvice_K_le_smallCap_range q this h3

/-- SMALL band: `K < kStar = 199`. -/
theorem compileAdvice_K_lt_kStar (q : Nat) (h3 : 3 ≤ q) (hs : (compileAdvice q).useSmall = true) :
    (compileAdvice q).K < kStar := by
  have := compileAdvice_K_le_smallCap q h3 hs
  have : kStar = 199 := rfl
  omega

/-- Every `RUN (j+1)` built under `j + 1 < K` stays below `kStar` in the production SMALL band. -/
theorem small_run_succ_lt (q : Nat) (h3 : 3 ≤ q) (hs : (compileAdvice q).useSmall = true)
    (j : Nat) (hj : j + 1 < (compileAdvice q).K) : j + 1 < kStar :=
  Nat.lt_trans hj (compileAdvice_K_lt_kStar q h3 hs)

/-! ## 4. Compiler invariant `K + 1 < 2 ^ b` -/

/-- `finiteKappa q ≤ 15`. -/
theorem finiteKappa_le (q : Nat) : finiteKappa q ≤ 15 := by
  unfold finiteKappa
  split <;> (try split) <;> (try split) <;> (try split) <;> omega

/-- Growth lemma: `557 s + 119983 < 2046 * 2^s` for `s ≥ 6`. -/
theorem growth_bound (s : Nat) (hs : 6 ≤ s) : 557 * s + 119983 < 2046 * 2 ^ s := by
  have key : ∀ n : Nat, 557 * (n + 6) + 119983 < 2046 * 2 ^ (n + 6) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      have hp : 0 < 2 ^ (n + 6) := Nat.two_pow_pos (n + 6)
      have h2 : 2 ^ (n + 1 + 6) = 2 ^ (n + 6) * 2 := by
        have : n + 1 + 6 = (n + 6) + 1 := by omega
        rw [this]
        exact Nat.pow_succ 2 (n + 6)
      omega
  have := key (s - 6)
  have e : s - 6 + 6 = s := by omega
  rw [e] at this
  exact this

/-- `kappaDot s ≤ 557 s + 119982` for `s ≥ 6`. -/
theorem kappaDot_le (s : Nat) (hs : 6 ≤ s) : kappaDot s ≤ 557 * s + 119982 := by
  unfold kappaDot
  have n2 : ¬ s = 2 := by omega
  have n3 : ¬ s = 3 := by omega
  have n4 : ¬ s = 4 := by omega
  have n5 : ¬ s = 5 := by omega
  have n5' : ¬ s ≤ 5 := by omega
  rw [if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n5']
  by_cases h6 : s = 6
  · rw [if_pos h6]; omega
  · rw [if_neg h6]
    have := ceilLogTwo_le_self (557 * s + 119981 + 1)
    omega

/-- Compiler invariant `K < 2^b` (stronger: `K + 1 < 2^b`) for all `q ≥ 3`
(`composed-full.mjs:131`).  Structural: `b = s + 11`, `s ≥ ceilLogTwo q`, `2q ≤ 2^(s+1)`,
`kappa ≤ 15` below `33` and `kappa ≤ 557 s + 119982` above. -/
theorem compileAdvice_K_lt_two_pow_b (q : Nat) (h3 : 3 ≤ q) :
    (compileAdvice q).K + 1 < 2 ^ (compileAdvice q).b := by
  have hK : (compileAdvice q).K = 2 * q + productionKappa q := rfl
  have hb : (compileAdvice q).b = max 2 (ceilLogTwo q) + 11 := rfl
  rw [hK, hb]
  by_cases h32 : q ≤ 32
  · have hk : productionKappa q ≤ 15 := by
      unfold productionKappa
      rw [if_pos h32]
      exact finiteKappa_le q
    have h2 : 2 ^ 13 ≤ 2 ^ (max 2 (ceilLogTwo q) + 11) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h13 : (2 : Nat) ^ 13 = 8192 := by decide
    omega
  · have h6 := ceilLogTwo_ge_six q (by omega)
    have hq := (ceilLogTwo_spec q (by omega)).2
    have hmax : max 2 (ceilLogTwo q) = ceilLogTwo q := by omega
    have hk : productionKappa q = kappaDot (ceilLogTwo q) := by
      unfold productionKappa
      rw [if_neg h32]
      show kappaDot (max 2 (ceilLogTwo q)) = _
      rw [hmax]
    rw [hmax, hk]
    have hkd := kappaDot_le (ceilLogTwo q) h6
    have hg := growth_bound (ceilLogTwo q) h6
    have h11 : (2 : Nat) ^ 11 = 2048 := by decide
    have hpow : 2 ^ (ceilLogTwo q + 11) = 2 ^ ceilLogTwo q * 2048 := by
      rw [Nat.pow_add, h11]
    omega

/-! ## 5. LIVE-TOP radix -/

/-- `0 < topA`. -/
theorem compileAdvice_topA_pos (q : Nat) : 0 < (compileAdvice q).topA :=
  Compiled.topA_pos _

/-- `topA ≤ s`. -/
theorem compileAdvice_topA_le_s (q : Nat) : (compileAdvice q).topA ≤ (compileAdvice q).s := by
  have hs : (compileAdvice q).s = max 2 (ceilLogTwo q) := rfl
  have h0 : (compileAdvice q).s ≠ 0 := by omega
  show 2 ^ floorLogTwo (compileAdvice q).s ≤ (compileAdvice q).s
  exact (Nat.le_log2 h0).1 (Nat.le_refl _)

end L3
